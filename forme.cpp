#include <unistd.h>     // sbrk
#include <sys/mman.h>   // mmap, munmap
#include <cstring>      // memset, memmove
#include <iostream>     // std::cerr, std::cout
#include <cmath>        // pow

static const int    MAX_ORDER      = 10;          // Buddy max order (0..10)
static const size_t BLOCK_SIZE     = 128 * 1024;  // 128KB
static const int    NUM_INIT_BLOCKS= 32;          // total 32 blocks => 4MB
static bool         is_buddy_initialized = false;

// We store a pointer to the start of the entire 4MB buddy region
static char* BASE = nullptr;

// A cookie if you need a canary or ID
static int GlobalCookie = 0x12345678;

// ------------------------------------
// MallocMetadata
// ------------------------------------
struct MallocMetadata {
    int    cookie;
    size_t size;      // "usable" size of the block (excluding this metadata)
    bool   is_free;   // true if block is free
    bool   is_mmap;   // true if allocated by mmap
    int    order;     // buddy order (if is_mmap=false), -1 otherwise

    MallocMetadata* next;
    MallocMetadata* prev;
};

// ------------------------------------
// BlocksList: a minimal doubly-linked list
//             (NO STATS updates here)
// ------------------------------------
class BlocksList {
public:
    MallocMetadata* head;

    BlocksList() {
        head = nullptr;
    }

    // Add a block by address
    void addBlock(MallocMetadata* block) {
        if (!block) return;
        if (!head) {
            head = block;
            block->prev = nullptr;
            block->next = nullptr;
            return;
        }
        if (block < head) {
            block->next = head;
            block->prev = nullptr;
            head->prev = block;
            head = block;
            return;
        }
        // Otherwise, find correct position
        MallocMetadata* curr = head;
        while (curr->next && (curr->next < block)) {
            curr = curr->next;
        }
        block->next = curr->next;
        block->prev = curr;
        if (curr->next) {
            curr->next->prev = block;
        }
        curr->next = block;
    }

    // Remove a block from the list
    void removeBlock(MallocMetadata* block) {
        if (!block) return;
        if (block->prev) {
            block->prev->next = block->next;
        } else {
            if (head == block) {
                head = block->next;
            }
        }
        if (block->next) {
            block->next->prev = block->prev;
        }
        block->next = nullptr;
        block->prev = nullptr;
    }

    // Find first free block with size >= neededSize
    MallocMetadata* findFirstFreeBlock(size_t neededSize) {
        MallocMetadata* curr = head;
        while (curr) {
            if (curr->is_free && curr->size >= neededSize) {
                return curr;
            }
            curr = curr->next;
        }
        return nullptr;
    }
};

// ------------------------------------
// We keep stats for each order in a separate struct
// plus one for mmap
// ------------------------------------
struct BuddyStats {
    size_t num_free_blocks;
    size_t num_free_bytes;
    size_t num_allocated_blocks;
    size_t num_allocated_bytes;
    size_t num_meta_data_bytes;
};

static BuddyStats buddyStats[MAX_ORDER + 1]; // one for each order
static BuddyStats mmapStats;                 // separate stats for mmap

// For convenience, we define a function to get the
// total across all buddyStats + mmapStats:
static size_t sumFreeBlocks() {
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++)
        total += buddyStats[i].num_free_blocks;
    total += mmapStats.num_free_blocks;
    return total;
}

static size_t sumFreeBytes() {
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++)
        total += buddyStats[i].num_free_bytes;
    total += mmapStats.num_free_bytes;
    return total;
}

static size_t sumAllocatedBlocks() {
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++)
        total += buddyStats[i].num_allocated_blocks;
    total += mmapStats.num_allocated_blocks;
    return total;
}

static size_t sumAllocatedBytes() {
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++)
        total += buddyStats[i].num_allocated_bytes;
    total += mmapStats.num_allocated_bytes;
    return total;
}

static size_t sumMetaDataBytes() {
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++)
        total += buddyStats[i].num_meta_data_bytes;
    total += mmapStats.num_meta_data_bytes;
    return total;
}

// We'll keep an array of buddy lists for [0..MAX_ORDER]
static BlocksList buddyArray[MAX_ORDER + 1];
// We'll keep a separate list for mmap blocks
static BlocksList mmapList;

// ------------------------------------
// Helper to update stats when we add a block
// to a specific order or to mmapStats
// ------------------------------------
static void incrementStats(int order, MallocMetadata* block) {
    if (!block) return;
    size_t blockSize = block->size;
    // If it's an mmap block
    if (order < 0) {
        mmapStats.num_allocated_blocks++;
        mmapStats.num_allocated_bytes += blockSize;
        mmapStats.num_meta_data_bytes += sizeof(MallocMetadata);
        if (block->is_free) {
            mmapStats.num_free_blocks++;
            mmapStats.num_free_bytes += blockSize;
        }
    } else {
        buddyStats[order].num_allocated_blocks++;
        buddyStats[order].num_allocated_bytes += blockSize;
        buddyStats[order].num_meta_data_bytes += sizeof(MallocMetadata);
        if (block->is_free) {
            buddyStats[order].num_free_blocks++;
            buddyStats[order].num_free_bytes += blockSize;
        }
    }
}

// ------------------------------------
// Helper to update stats when we remove a block
// from a specific order or from mmapStats
// ------------------------------------
static void decrementStats(int order, MallocMetadata* block) {
    if (!block) return;
    size_t blockSize = block->size;

    if (order < 0) {
        mmapStats.num_allocated_blocks--;
        mmapStats.num_allocated_bytes -= blockSize;
        mmapStats.num_meta_data_bytes -= sizeof(MallocMetadata);
        if (block->is_free) {
            mmapStats.num_free_blocks--;
            mmapStats.num_free_bytes -= blockSize;
        }
    } else {
        buddyStats[order].num_allocated_blocks--;
        buddyStats[order].num_allocated_bytes -= blockSize;
        buddyStats[order].num_meta_data_bytes -= sizeof(MallocMetadata);
        if (block->is_free) {
            buddyStats[order].num_free_blocks--;
            buddyStats[order].num_free_bytes -= blockSize;
        }
    }
}

// ------------------------------------
// Some forward declarations
// ------------------------------------
static bool initialize_buddy_allocator();
static MallocMetadata* allocate_with_mmap(size_t userSize);
static void free_mmap_block(MallocMetadata* block);
static MallocMetadata* getBuddy(MallocMetadata* block);
static MallocMetadata* split_block(MallocMetadata* block);
static MallocMetadata* merge_blocks(MallocMetadata* b1, MallocMetadata* b2);

// ------------------------------------
// mmap-related helpers
// ------------------------------------
static MallocMetadata* allocate_with_mmap(size_t userSize)
{
    size_t totalSize = userSize + sizeof(MallocMetadata);
    void* addr = mmap(nullptr, totalSize,
                      PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (addr == MAP_FAILED) {
        return nullptr;
    }

    MallocMetadata* block = (MallocMetadata*)addr;
    block->cookie  = GlobalCookie;
    block->size    = userSize;
    block->is_free = false;
    block->is_mmap = true;
    block->order   = -1;
    block->next    = nullptr;
    block->prev    = nullptr;

    // Insert into the mmapList
    mmapList.addBlock(block);
    // Now update stats for "order = -1"
    incrementStats(-1, block);

    return block;
}

static void free_mmap_block(MallocMetadata* block)
{
    if (!block) return;
    // first, we remove from the list
    mmapList.removeBlock(block);
    // then, update stats
    decrementStats(-1, block);

    // now unmap the memory
    munmap(block, block->size + sizeof(MallocMetadata));
}

// ------------------------------------
// initialize_buddy_allocator()
// ------------------------------------
static bool initialize_buddy_allocator()
{
    if (is_buddy_initialized) return true;
    is_buddy_initialized = true;

    // 1) Alignment
    void* currBrk   = sbrk(0);
    size_t alignment = ((uintptr_t)currBrk) % (NUM_INIT_BLOCKS * BLOCK_SIZE);
    if (alignment != 0) {
        size_t toAdd = (NUM_INIT_BLOCKS * BLOCK_SIZE) - alignment;
        void* res = sbrk(toAdd);
        if (res == (void*)-1) {
            std::cerr << "Failed alignment sbrk\n";
            return false;
        }
    }

    // 2) Allocate the 4MB (32 * 128KB)
    BASE = (char*)sbrk(NUM_INIT_BLOCKS * BLOCK_SIZE);
    if (BASE == (void*)-1) {
        std::cerr << "Failed sbrk for buddy blocks\n";
        return false;
    }

    // 3) We will store 32 separate blocks (each 128KB) in buddyArray[MAX_ORDER].
    //    Each block is free initially.
    char* runner = BASE;
    for (int i = 0; i < NUM_INIT_BLOCKS; i++) {
        MallocMetadata* block = (MallocMetadata*)runner;
        block->cookie  = GlobalCookie;
        block->size    = BLOCK_SIZE; // 128KB
        block->is_free = true;
        block->is_mmap = false;
        block->order   = MAX_ORDER;  // 10
        block->next    = nullptr;
        block->prev    = nullptr;

        buddyArray[MAX_ORDER].addBlock(block);
        // Update stats for the highest order = 10
        incrementStats(MAX_ORDER, block);

        runner += BLOCK_SIZE;
    }

    return true;
}

// ------------------------------------
// getBuddy: compute the buddy
// ------------------------------------
static MallocMetadata* getBuddy(MallocMetadata* block)
{
    if (!block || block->is_mmap) return nullptr;
    if (block->order < 0 || block->order > MAX_ORDER) return nullptr;

    uintptr_t blockAddr = (uintptr_t)block;
    uintptr_t baseAddr  = (uintptr_t)BASE;
    size_t    size      = block->size;

    long diff = blockAddr - baseAddr;
    // buddy is at +size or -size depending on remainder
    long res = diff % (2 * size);
    if (res == 0) {
        // buddy is to the right
        return (MallocMetadata*)(blockAddr + size);
    } else {
        // buddy is to the left
        return (MallocMetadata*)(blockAddr - size);
    }
}

// ------------------------------------
// split_block: splits one block into two
// ------------------------------------
static MallocMetadata* split_block(MallocMetadata* block)
{
    if (!block) return nullptr;
    size_t half = block->size / 2;
    int oldOrder = block->order;

    // We'll remove the original block from the list first
    // so we can re-add it with the updated size
    buddyArray[oldOrder].removeBlock(block);
    decrementStats(oldOrder, block);

    // update the original block
    block->size  = half;
    block->order = oldOrder - 1;

    // re-insert it into the lower order list
    buddyArray[block->order].addBlock(block);
    incrementStats(block->order, block);

    // create the buddy
    MallocMetadata* buddy = (MallocMetadata*)((char*)block + half);
    buddy->cookie  = GlobalCookie;
    buddy->size    = half;
    buddy->is_free = true;
    buddy->is_mmap = false;
    buddy->order   = oldOrder - 1;
    buddy->next    = nullptr;
    buddy->prev    = nullptr;

    // add buddy to buddyArray[buddy->order]
    buddyArray[buddy->order].addBlock(buddy);
    incrementStats(buddy->order, buddy);

    return block; // Return the "first half"
}

// ------------------------------------
// merge_blocks: merges two buddies
// ------------------------------------
static MallocMetadata* merge_blocks(MallocMetadata* b1, MallocMetadata* b2)
{
    // ensure b1 < b2
    if (b2 < b1) {
        MallocMetadata* tmp = b1;
        b1 = b2;
        b2 = tmp;
    }
    // remove both from their list + stats
    buddyArray[b2->order].removeBlock(b2);
    decrementStats(b2->order, b2);

    buddyArray[b1->order].removeBlock(b1);
    decrementStats(b1->order, b1);

    // double b1
    b1->size *= 2;
    b1->order++;

    // re-add the merged bigger block
    buddyArray[b1->order].addBlock(b1);
    incrementStats(b1->order, b1);

    return b1;
}

// ------------------------------------
// smalloc
// ------------------------------------
void* smalloc(size_t size)
{
    if (size == 0 || size > 100000000) {
        return nullptr;
    }
    if (!is_buddy_initialized) {
        if (!initialize_buddy_allocator()) {
            return nullptr;
        }
    }

    // If requested size + metadata > 128KB => use mmap
    if (size + sizeof(MallocMetadata) > BLOCK_SIZE) {
        MallocMetadata* block = allocate_with_mmap(size);
        if (!block) return nullptr;
        return (char*)block + sizeof(MallocMetadata);
    }

    size_t needed = size + sizeof(MallocMetadata);

    // find the order
    int order = 0;
    size_t currentSize = 128; // base chunk = 128
    while (order <= MAX_ORDER) {
        if (currentSize >= needed) {
            break;
        }
        currentSize <<= 1;
        order++;
    }
    if (order > MAX_ORDER) {
        // can't handle
        return nullptr;
    }

    // search from [order .. MAX_ORDER]
    for (int i = order; i <= MAX_ORDER; i++) {
        MallocMetadata* candidate = buddyArray[i].findFirstFreeBlock(needed);
        if (candidate) {
            // We'll remove from buddyArray[i] + stats
            buddyArray[i].removeBlock(candidate);
            decrementStats(i, candidate);

            candidate->is_free = false;

            // if the block is bigger than needed, keep splitting
            while (candidate->order > order) {
                candidate = split_block(candidate);
                // The split_block function handles stats updates itself
            }
            return (char*)candidate + sizeof(MallocMetadata);
        }
    }

    // none found
    return nullptr;
}

// ------------------------------------
// scalloc
// ------------------------------------
void* scalloc(size_t num, size_t size)
{
    if (num == 0 || size == 0) return nullptr;
    size_t totalSize = num * size;
    if (size != 0 && (totalSize / size) != num) {
        // overflow
        return nullptr;
    }
    void* p = smalloc(totalSize);
    if (!p) return nullptr;
    memset(p, 0, totalSize);
    return p;
}

// ------------------------------------
// sfree
// ------------------------------------
void sfree(void* p)
{
    if (!p) return;
    MallocMetadata* block = (MallocMetadata*)((char*)p - sizeof(MallocMetadata));
    if (block->cookie != GlobalCookie) {
        // canary check
        return;
    }
    if (block->is_free) {
        return;
    }

    // if it's mmap
    if (block->is_mmap) {
        block->is_free = true;
        free_mmap_block(block);
        return;
    }

    // else buddy
    block->is_free = true;
    // add back to buddy
    buddyArray[block->order].addBlock(block);
    incrementStats(block->order, block);

    // attempt merges repeatedly
    while (block->order < MAX_ORDER) {
        MallocMetadata* buddy = getBuddy(block);
        if (!buddy) break;
        // Check if buddy is free, same order, not mmap
        if (buddy->is_free && !buddy->is_mmap && buddy->order == block->order) {
            // remove block before merging
            buddyArray[block->order].removeBlock(block);
            decrementStats(block->order, block);
            // now merge them
            block = merge_blocks(block, buddy);
        } else {
            break;
        }
    }
}

// ------------------------------------
// srealloc
// ------------------------------------
void* srealloc(void* oldp, size_t newSize)
{
    if (newSize == 0) {
        sfree(oldp);
        return nullptr;
    }
    if (!oldp) {
        return smalloc(newSize);
    }

    MallocMetadata* oldBlock = (MallocMetadata*)((char*)oldp - sizeof(MallocMetadata));
    if (oldBlock->cookie != GlobalCookie) {
        return nullptr;
    }

    size_t oldUserSize = oldBlock->size;
    if (oldUserSize >= newSize) {
        // already big enough
        return oldp;
    }

    // if it's mmap or not enough space => new, copy, free old
    bool wasMmap = oldBlock->is_mmap;
    void* newp = smalloc(newSize);
    if (!newp) return nullptr;

    size_t bytesToCopy = (oldUserSize < newSize) ? oldUserSize : newSize;
    memmove(newp, oldp, bytesToCopy);
    sfree(oldp);
    return newp;
}

// ------------------------------------
// Statistics (using sums of buddyStats & mmapStats)
// ------------------------------------
size_t _num_free_blocks()
{
    return sumFreeBlocks();
}

size_t _num_free_bytes()
{
    return sumFreeBytes();
}

size_t _num_allocated_blocks()
{
    return sumAllocatedBlocks();
}

size_t _num_allocated_bytes()
{
    return sumAllocatedBytes();
}

size_t _num_meta_data_bytes()
{
    return sumMetaDataBytes();
}

size_t _size_meta_data()
{
    return sizeof(MallocMetadata);
}

