#include <unistd.h>     // sbrk
#include <sys/mman.h>   // mmap, munmap
#include <cstring>      // memset, memmove
#include <cmath>        // pow
#include <iostream>     // std::cerr, std::cout

// --------------------------------------------------------------------------------
// Constants
// --------------------------------------------------------------------------------
static const int    MAX_ORDER      = 10;          // orders 0..10 => 128..128K
static const size_t BLOCK_SIZE     = 128 * 1024;  // 128KB
static const int    NUM_INIT_BLOCKS= 32;          // 32 blocks => 4MB
static bool         buddy_initialized = false;

// We'll store the base of the entire 4MB region
static char* BASE = nullptr;

// --------------------------------------------------------------------------------
// MallocMetadata (no cookie field)
//   - .size   : total size of this block (including metadata!)
//   - .is_free: whether block is free
//   - .is_mmap: whether allocated via mmap
//   - .order  : if buddy block, order=0..10, else -1 for mmap
//   - .next/.prev: doubly linked pointers in a free list
// --------------------------------------------------------------------------------
struct MallocMetadata {
    size_t size;      // total size of block including this metadata
    bool   is_free;
    bool   is_mmap;
    int    order;

    MallocMetadata* next;
    MallocMetadata* prev;
};

// --------------------------------------------------------------------------------
// A doubly-linked list structure to store free blocks of the same order
// or to store mmap blocks in a separate list
// --------------------------------------------------------------------------------
class BlocksList {
public:
    MallocMetadata* head;

    // We keep stats for easy reference
    size_t num_free_blocks;
    size_t num_free_bytes;        // sum of sizes of free blocks minus metadata
    size_t num_allocated_blocks;  // free + used blocks
    size_t num_allocated_bytes;   // sum of sizes (minus metadata) for all blocks
    size_t num_meta_data_bytes;   // total size of metadata across all blocks

    BlocksList() {
        head = nullptr;
        num_free_blocks      = 0;
        num_free_bytes       = 0;
        num_allocated_blocks = 0;
        num_allocated_bytes  = 0;
        num_meta_data_bytes  = 0;
    }

    // Insert block into list (sorted by address)
    void addBlock(MallocMetadata* block) {
        if (!block) return;

        // Update stats
        num_allocated_blocks++;
        // For "allocated bytes," we exclude metadata: i.e. block->size - sizeof(MallocMetadata)
        num_allocated_bytes += (block->size - sizeof(MallocMetadata));
        num_meta_data_bytes += sizeof(MallocMetadata);

        if (block->is_free) {
            num_free_blocks++;
            num_free_bytes += (block->size - sizeof(MallocMetadata));
        }

        // Insert by address (ascending)
        if (!head) {
            head = block;
            block->prev = nullptr;
            block->next = nullptr;
            return;
        }
        if (block < head) {
            block->next = head;
            block->prev = nullptr;
            head->prev  = block;
            head        = block;
            return;
        }

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

    // Remove block from list
    void removeBlock(MallocMetadata* block) {
        if (!block) return;

        // Update stats
        num_allocated_blocks--;
        num_allocated_bytes  -= (block->size - sizeof(MallocMetadata));
        num_meta_data_bytes  -= sizeof(MallocMetadata);

        if (block->is_free) {
            num_free_blocks--;
            num_free_bytes -= (block->size - sizeof(MallocMetadata));
        }

        // Unlink
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
    // "neededSize" includes metadata (the block->size)
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

// We'll keep an array of free-lists for buddy blocks [0..MAX_ORDER]
static BlocksList buddyArray[MAX_ORDER + 1];
// We'll keep a separate list for mmap blocks
static BlocksList mmapList;

// --------------------------------------------------------------------------------
// Forward declarations
// --------------------------------------------------------------------------------
static bool           initialize_buddy_allocator();
static MallocMetadata* allocate_with_mmap(size_t userSize);
static void            free_mmap_block(MallocMetadata* block);
static int             get_order(size_t sizeNeeded);
static MallocMetadata* split_block(MallocMetadata* block);
static MallocMetadata* getBuddy(MallocMetadata* block);
static MallocMetadata* merge_blocks(MallocMetadata* b1, MallocMetadata* b2);

// --------------------------------------------------------------------------------
// Aligned initialization: 4MB for buddy
// --------------------------------------------------------------------------------
static bool initialize_buddy_allocator()
{
    if (buddy_initialized) return true;
    buddy_initialized = true;

    // 1) Alignment
    void* currBrk = sbrk(0);
    size_t alignment = (uintptr_t)currBrk % (NUM_INIT_BLOCKS * BLOCK_SIZE);
    if (alignment != 0) {
        size_t toAdd = (NUM_INIT_BLOCKS*BLOCK_SIZE) - alignment;
        void* res = sbrk(toAdd);
        if (res == (void*)-1) {
            std::cerr << "Failed alignment sbrk\n";
            return false;
        }
    }

    // 2) Allocate 4MB of memory (32 blocks of 128KB)
    BASE = (char*)sbrk(NUM_INIT_BLOCKS * BLOCK_SIZE);
    if (BASE == (void*)-1) {
        std::cerr << "Failed sbrk for buddy blocks\n";
        return false;
    }

    // 3) Create 32 blocks, each of size=128KB (order=10)
    char* runner = BASE;
    for (int i = 0; i < NUM_INIT_BLOCKS; i++) {
        MallocMetadata* block = (MallocMetadata*)runner;
        block->size    = BLOCK_SIZE; // includes metadata
        block->is_free = true;
        block->is_mmap = false;
        block->order   = MAX_ORDER;  // =10

        block->next    = nullptr;
        block->prev    = nullptr;

        buddyArray[MAX_ORDER].addBlock(block);

        runner += BLOCK_SIZE;
    }

    return true;
}

// --------------------------------------------------------------------------------
// get_order: find smallest order i s.t. 128*(2^i) >= sizeNeeded
// --------------------------------------------------------------------------------
static int get_order(size_t sizeNeeded)
{
    // size for order=0 is 128
    // order=1 => 256
    // ...
    // order=10 => 128KB
    int order = 0;
    size_t current = 128;
    while (order <= MAX_ORDER) {
        if (current >= sizeNeeded) return order;
        current <<= 1; // multiply by 2
        order++;
    }
    return -1; // can't handle bigger than 128KB as buddy
}

// --------------------------------------------------------------------------------
// allocate_with_mmap
// --------------------------------------------------------------------------------
static MallocMetadata* allocate_with_mmap(size_t userSize)
{
    // total size = userSize + metadata
    size_t totalSize = userSize + sizeof(MallocMetadata);
    void* addr = mmap(nullptr, totalSize,
                      PROT_READ|PROT_WRITE,
                      MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    if (addr == MAP_FAILED) {
        return nullptr;
    }
    MallocMetadata* block = (MallocMetadata*)addr;
    block->size    = totalSize;   // includes metadata
    block->is_free = false;
    block->is_mmap = true;
    block->order   = -1;
    block->next    = nullptr;
    block->prev    = nullptr;

    // Insert into mmapList
    mmapList.addBlock(block);

    return block;
}

// --------------------------------------------------------------------------------
// free_mmap_block
// --------------------------------------------------------------------------------
static void free_mmap_block(MallocMetadata* block)
{
    if (!block) return;
    mmapList.removeBlock(block);
    munmap(block, block->size);
}

// --------------------------------------------------------------------------------
// getBuddy: use offset from BASE approach
//   buddy is at address ^ block->size if aligned properly
//   or we can do +size/-size depending on offset % (2*size)
// --------------------------------------------------------------------------------
static MallocMetadata* getBuddy(MallocMetadata* block)
{
    if (!block || block->is_mmap) return nullptr;
    if (block->order < 0 || block->order > MAX_ORDER) return nullptr;

    size_t size = block->size; // includes metadata
    // offset from BASE
    uintptr_t addr   = (uintptr_t)block;
    uintptr_t base   = (uintptr_t)BASE;
    size_t    offset = addr - base;

    // If offset % (2*size)==0 => buddy is to the right, else to the left
    if ((offset % (2*size)) == 0) {
        // buddy is at +size
        return (MallocMetadata*)(addr + size);
    } else {
        return (MallocMetadata*)(addr - size);
    }
}

// --------------------------------------------------------------------------------
// split_block: splits a single block into two buddies of half size
//   returns the "first half," buddy is the "second half"
// --------------------------------------------------------------------------------
static MallocMetadata* split_block(MallocMetadata* block)
{
    if (!block) return nullptr;
    int oldOrder = block->order;
    size_t oldSize = block->size;

    // remove from buddyArray[oldOrder]
    buddyArray[oldOrder].removeBlock(block);

    // new smaller size
    size_t half = oldSize / 2;
    int newOrder = oldOrder - 1;

    // update the original block
    block->size  = half;
    block->order = newOrder;
    block->is_free = true;

    // re-insert the splitted block
    buddyArray[newOrder].addBlock(block);

    // create buddy
    MallocMetadata* buddy = (MallocMetadata*)((char*)block + half);
    buddy->size    = half;
    buddy->is_free = true;
    buddy->is_mmap = false;
    buddy->order   = newOrder;
    buddy->next    = nullptr;
    buddy->prev    = nullptr;

    buddyArray[newOrder].addBlock(buddy);

    return block; // "first half"
}

// --------------------------------------------------------------------------------
// merge_blocks: merges two buddy blocks into one bigger block
// --------------------------------------------------------------------------------
static MallocMetadata* merge_blocks(MallocMetadata* b1, MallocMetadata* b2)
{
    // ensure b1 is the lower address
    if (b2 < b1) {
        MallocMetadata* tmp = b1;
        b1 = b2;
        b2 = tmp;
    }
    int order = b1->order;
    // remove b2 from buddyArray
    buddyArray[order].removeBlock(b2);
    // remove b1 from buddyArray
    buddyArray[order].removeBlock(b1);

    // double b1
    b1->size  *= 2;
    b1->order = order + 1;

    // re-insert
    buddyArray[b1->order].addBlock(b1);

    return b1;
}

// --------------------------------------------------------------------------------
// smalloc
// --------------------------------------------------------------------------------
void* smalloc(size_t size)
{
    if (size == 0 || size > 100000000) {
        return nullptr;
    }
    // first-time init
    if (!buddy_initialized) {
        if (!initialize_buddy_allocator()) {
            return nullptr;
        }
    }

    // If request >= 128KB => use mmap
    if (size + sizeof(MallocMetadata) >= BLOCK_SIZE) {
        MallocMetadata* block = allocate_with_mmap(size);
        if (!block) return nullptr;
        // user ptr
        return (char*)block + sizeof(MallocMetadata);
    }

    // BUDDY logic
    size_t needed = size + sizeof(MallocMetadata);
    int order = get_order(needed);
    if (order < 0 || order > MAX_ORDER) {
        // can't handle
        return nullptr;
    }

    // find free block in [order..MAX_ORDER]
    for (int i = order; i <= MAX_ORDER; i++) {
        MallocMetadata* candidate = buddyArray[i].findFirstFreeBlock(needed);
        if (candidate) {
            // remove it from free list
            buddyArray[i].removeBlock(candidate);

            // if candidate->order > order => we keep splitting
            while (candidate->order > order) {
                candidate = split_block(candidate);
            }

            // now candidate->order == order, mark used
            candidate->is_free = false;
            // remove from free stats
            buddyArray[order].num_free_blocks--;
            buddyArray[order].num_free_bytes -= (candidate->size - sizeof(MallocMetadata));

            return (char*)candidate + sizeof(MallocMetadata);
        }
    }

    // no suitable block found
    return nullptr;
}

// --------------------------------------------------------------------------------
// scalloc
// --------------------------------------------------------------------------------
void* scalloc(size_t num, size_t size)
{
    if (num == 0 || size == 0) return nullptr;
    // check overflow
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

// --------------------------------------------------------------------------------
// sfree
// --------------------------------------------------------------------------------
void sfree(void* p)
{
    if (!p) return;
    MallocMetadata* block = (MallocMetadata*)((char*)p - sizeof(MallocMetadata));
    if (block->is_free) {
        return;
    }
    if (block->is_mmap) {
        // free via mmap
        block->is_free = true;
        free_mmap_block(block);
        return;
    }

    // buddy
    block->is_free = true;
    int order = block->order;
    buddyArray[order].addBlock(block);

    // try merges
    while (block->order < MAX_ORDER) {
        MallocMetadata* buddy = getBuddy(block);
        if (!buddy) break;
        if (buddy->is_free && !buddy->is_mmap && buddy->order == block->order) {
            block = merge_blocks(block, buddy);
        } else {
            break;
        }
    }
}

// --------------------------------------------------------------------------------
// srealloc
// --------------------------------------------------------------------------------
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
    size_t oldUserSize = oldBlock->size - sizeof(MallocMetadata);

    if (oldUserSize >= newSize) {
        // already big enough
        return oldp;
    }

    // If it's mmap or not enough space => allocate new, copy, free old
    if (oldBlock->is_mmap) {
        // if same size, do nothing
        if (oldUserSize == newSize) {
            return oldp;
        }
        void* newp = smalloc(newSize);
        if (!newp) return nullptr;
        memmove(newp, oldp, (oldUserSize < newSize) ? oldUserSize : newSize);
        sfree(oldp);
        return newp;
    } else {
        // buddy block
        // simplest approach: allocate new, copy, free old
        // (You could try merging with buddy to expand in-place, if tests require it)
        void* newp = smalloc(newSize);
        if (!newp) return nullptr;
        memmove(newp, oldp, (oldUserSize < newSize) ? oldUserSize : newSize);
        sfree(oldp);
        return newp;
    }
}

// --------------------------------------------------------------------------------
// Stats
//  5) _num_free_blocks     = sum of free blocks
//  6) _num_free_bytes      = sum of free block sizes minus metadata
//  7) _num_allocated_blocks= sum of allocated blocks (free + used)
//  8) _num_allocated_bytes = sum of allocated blocks' sizes minus metadata
//  9) _num_meta_data_bytes = sum of metadata bytes for all blocks in the heap
// 10) _size_meta_data      = sizeof(MallocMetadata)
// --------------------------------------------------------------------------------
size_t _num_free_blocks()
{
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++) {
        total += buddyArray[i].num_free_blocks;
    }
    total += mmapList.num_free_blocks;
    return total;
}

size_t _num_free_bytes()
{
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++) {
        total += buddyArray[i].num_free_bytes;
    }
    total += mmapList.num_free_bytes;
    return total;
}

size_t _num_allocated_blocks()
{
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++) {
        total += buddyArray[i].num_allocated_blocks;
    }
    total += mmapList.num_allocated_blocks;
    return total;
}

size_t _num_allocated_bytes()
{
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++) {
        total += buddyArray[i].num_allocated_bytes;
    }
    total += mmapList.num_allocated_bytes;
    return total;
}

size_t _num_meta_data_bytes()
{
    size_t total = 0;
    for (int i = 0; i <= MAX_ORDER; i++) {
        total += buddyArray[i].num_meta_data_bytes;
    }
    total += mmapList.num_meta_data_bytes;
    return total;
}

size_t _size_meta_data()
{
    return sizeof(MallocMetadata);
}
