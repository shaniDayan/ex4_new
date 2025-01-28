#include <unistd.h>
#include <sys/mman.h>
#include <cstring>
#include <iostream>
#include <cmath>

#define MAX_ORDER 10
static const size_t BLOCK_SIZE = 128 * 1024; // 128KB
static const int    NUM_INIT_BLOCKS = 32;    // 32 blocks => 4MB total
static bool         is_buddy_initialized = false;

static int GlobalCookie = 0x12345678;
static char* BASE = nullptr; // base of the 4MB region

/**************************************************************
 * MallocMetadata
 **************************************************************/
struct MallocMetadata {
    int    cookie;
    size_t size;      // usable size (excluding metadata)
    bool   is_free;   // is this block free
    bool   is_mmap;   // is this allocated by mmap
    int    order;     // buddy order (if !is_mmap), else -1

    MallocMetadata* next;
    MallocMetadata* prev;
};

/**************************************************************
 * A simple doubly-linked list (by address)
 **************************************************************/
class BlocksList {
public:
    MallocMetadata* head;

    // Stats for demonstration (like code B)
    size_t num_free_blocks;
    size_t num_free_bytes;
    size_t num_allocated_blocks;
    size_t num_allocated_bytes;
    size_t num_meta_data_bytes;

    BlocksList()
    {
        head = nullptr;
        num_free_blocks       = 0;
        num_free_bytes        = 0;
        num_allocated_blocks  = 0;
        num_allocated_bytes   = 0;
        num_meta_data_bytes   = 0;
    }

    void AddBlock(MallocMetadata* b)
    {
        if(!b) return;
        // update stats
        num_allocated_blocks++;
        num_allocated_bytes += b->size;
        num_meta_data_bytes += sizeof(MallocMetadata);
        if(b->is_free) {
            num_free_blocks++;
            num_free_bytes += b->size;
        }
        // insert sorted by address
        if(!head) {
            head = b;
            b->next = nullptr;
            b->prev = nullptr;
            return;
        }
        if(b < head) {
            b->next = head;
            b->prev = nullptr;
            head->prev = b;
            head = b;
            return;
        }
        // otherwise
        MallocMetadata* curr = head;
        while(curr->next && (curr->next < b)) {
            curr = curr->next;
        }
        b->next = curr->next;
        b->prev = curr;
        if(curr->next) {
            curr->next->prev = b;
        }
        curr->next = b;
    }

    void RemoveBlock(MallocMetadata* b)
    {
        if(!b) return;
        // update stats
        num_allocated_blocks--;
        num_allocated_bytes -= b->size;
        num_meta_data_bytes -= sizeof(MallocMetadata);
        if(b->is_free) {
            num_free_blocks--;
            num_free_bytes -= b->size;
        }
        // remove from list
        if(b->prev) {
            b->prev->next = b->next;
        } else {
            if(head == b) {
                head = b->next;
            }
        }
        if(b->next) {
            b->next->prev = b->prev;
        }
        b->next = nullptr;
        b->prev = nullptr;
    }

    MallocMetadata* FindFirstFreeBlock(size_t needed)
    {
        MallocMetadata* curr = head;
        while(curr) {
            if(curr->is_free && curr->size >= needed) {
                return curr;
            }
            curr = curr->next;
        }
        return nullptr;
    }
};

/**************************************************************
 * We maintain an array for buddy orders [0..MAX_ORDER],
 * plus one list for mmap-allocated blocks
 **************************************************************/
static BlocksList buddyArray[MAX_ORDER + 1];
static BlocksList mmapList;

/**************************************************************
 * Forward declarations
 **************************************************************/
static bool initialize_buddy_allocator();
static MallocMetadata* CutInHalf(size_t sizeNeeded);
static void MergeBuddies(MallocMetadata* blockToFree, int mergeTillOrder);
static int  CheckIfMergePossible(MallocMetadata* oldBlock, size_t newSize);

//*************************************************************
// Initialize
//*************************************************************
static bool initialize_buddy_allocator()
{
    if(is_buddy_initialized) return true;
    is_buddy_initialized = true;

    // alignment
    void* currBrk = sbrk(0);
    size_t alignment = (uintptr_t)currBrk % (NUM_INIT_BLOCKS * BLOCK_SIZE);
    if(alignment != 0) {
        size_t toAdd = (NUM_INIT_BLOCKS*BLOCK_SIZE) - alignment;
        void* ret = sbrk(toAdd);
        if(ret == (void*)-1) {
            return false;
        }
    }

    // allocate 4MB
    BASE = (char*)sbrk(NUM_INIT_BLOCKS * BLOCK_SIZE);
    if(BASE == (void*)-1) {
        return false;
    }

    // we create a single chain of 32 blocks in the highest order (order=MAX_ORDER)
    // each of size 128KB
    char* runner = BASE;
    for(int i=0; i<NUM_INIT_BLOCKS; i++) {
        MallocMetadata* block = (MallocMetadata*)runner;
        block->cookie  = GlobalCookie;
        block->size    = BLOCK_SIZE;
        block->is_free = true;
        block->is_mmap = false;
        block->order   = MAX_ORDER;
        block->next    = nullptr;
        block->prev    = nullptr;

        buddyArray[MAX_ORDER].AddBlock(block);
        runner += BLOCK_SIZE;
    }
    return true;
}

/**************************************************************
 * get order for a certain size
 **************************************************************/
static int GetBlockOrder(size_t size)
{
    // same approach as code B
    // find i s.t. 128 * 2^i >= size
    int order = 0;
    size_t current = 128;
    while(order <= MAX_ORDER) {
        if(current >= size) break;
        current <<= 1; // multiply by 2
        order++;
    }
    if(order>MAX_ORDER) return -1;
    return order;
}

/**************************************************************
 * Mmap Alloc/Free
 **************************************************************/
static MallocMetadata* allocate_with_mmap(size_t userSize)
{
    size_t totalSize = userSize + sizeof(MallocMetadata);
    void* addr = mmap(nullptr, totalSize, PROT_READ|PROT_WRITE, MAP_ANONYMOUS|MAP_PRIVATE, -1, 0);
    if(addr == MAP_FAILED) {
        return nullptr;
    }
    MallocMetadata* meta = (MallocMetadata*)addr;
    meta->cookie  = GlobalCookie;
    meta->size    = userSize;
    meta->is_free = false;
    meta->is_mmap = true;
    meta->order   = -1;
    meta->next    = nullptr;
    meta->prev    = nullptr;

    mmapList.AddBlock(meta);
    return meta;
}

static void free_mmap_block(MallocMetadata* block)
{
    if(!block) return;
    mmapList.RemoveBlock(block);
    munmap(block, block->size + sizeof(MallocMetadata));
}

/**************************************************************
 * "CutInHalf" - Splitting logic like code B
 *
 *  This function tries to find a free block in an order >=
 *  the needed size. Then it repeatedly splits until we get
 *  exactly the needed order, updating stats as in code B.
 *
 *  Return: a pointer to the block that exactly fits
 **************************************************************/
static MallocMetadata* CutInHalf(size_t sizeNeeded)
{
    int desiredOrder = GetBlockOrder(sizeNeeded);
    if(desiredOrder < 0) return nullptr;

    // find a free block from [desiredOrder..MAX_ORDER]
    MallocMetadata* found = nullptr;
    int foundOrder = -1;
    for(int i=desiredOrder; i<=MAX_ORDER; i++){
        found = buddyArray[i].FindFirstFreeBlock(sizeNeeded);
        if(found) {
            foundOrder = i;
            break;
        }
    }
    if(!found) return nullptr; // no block big enough

    // If foundOrder == desiredOrder, just return it
    // but code B logic does "if we found a bigger block, we do multiple splits"
    for(int j=foundOrder; j>desiredOrder; j--){
        // Remove from order j
        buddyArray[j].RemoveBlock(found);
        // Update stats exactly as code B does
        buddyArray[j].num_free_blocks--;
        buddyArray[j].num_free_bytes -= found->size;
        buddyArray[j].num_meta_data_bytes -= sizeof(MallocMetadata);
        buddyArray[j].num_allocated_blocks--;
        buddyArray[j].num_allocated_bytes -= found->size;

        // Now we split into two halves
        size_t half = found->size / 2;
        MallocMetadata* secondhalf = (MallocMetadata*)((char*)found + half);

        // The "first" half
        found->size = half;
        found->is_free = true;

        // The "second" half
        secondhalf->cookie  = GlobalCookie;
        secondhalf->size    = half;
        secondhalf->is_free = true;
        secondhalf->next    = nullptr;
        secondhalf->prev    = nullptr;

        // Now we add both halves to order (j-1),
        // updating stats the way code B does
        buddyArray[j-1].AddBlock(found);
        buddyArray[j-1].AddBlock(secondhalf);

        buddyArray[j-1].num_free_bytes += 2*half;
        buddyArray[j-1].num_free_bytes -= sizeof(MallocMetadata);
        buddyArray[j-1].num_free_blocks += 2;
        buddyArray[j-1].num_meta_data_bytes += 2*sizeof(MallocMetadata);
        buddyArray[j-1].num_allocated_blocks += 2;
        buddyArray[j-1].num_allocated_bytes += 2*half;
        buddyArray[j-1].num_allocated_bytes -= sizeof(MallocMetadata);

        // set found to the "first" half (arbitrary),
        // so next iteration will keep splitting the same piece if needed
        found = found;
    }
    // Now found is in the order = desiredOrder
    // Return it
    return found;
}

/**************************************************************
 * MergeBuddies - repeated merges, as code B does
 *   We remove blocks from the lower order and reinsert
 *   them at the higher order, updating stats each time.
 **************************************************************/
static MallocMetadata* FindBuddy(MallocMetadata* block, size_t blockSize)
{
    // code B does something like:
    if(!block) return nullptr;
    long diff = (long)block - (long)BASE;
    long res  = diff % (2*blockSize);
    if(block == (MallocMetadata*)BASE) {
        // buddy is to the right
        return (MallocMetadata*)((char*)block + blockSize);
    }
    else if(block == (MallocMetadata*)((char*)BASE + 32*BLOCK_SIZE - blockSize)) {
        // buddy is to the left
        return (MallocMetadata*)((char*)block - blockSize);
    }
    else {
        if(res == 0) {
            return (MallocMetadata*)((char*)block + blockSize);
        } else {
            return (MallocMetadata*)((char*)block - blockSize);
        }
    }
}

static void MergeBuddies(MallocMetadata* blockToFree, int mergeTillOrder)
{
    // code B merges up to a certain order (or all the way up)
    if(!blockToFree) return;
    if(blockToFree->cookie != GlobalCookie) return;

    int currentOrder = GetBlockOrder(blockToFree->size);
    if(mergeTillOrder == -1) {
        mergeTillOrder = MAX_ORDER;
    }

    for(int j=currentOrder; j<mergeTillOrder; j++){
        MallocMetadata* buddy = FindBuddy(blockToFree, blockToFree->size);
        if(!buddy) return;
        if(buddy->is_free){
            // remove both from the list j
            buddyArray[j].RemoveBlock(blockToFree);
            buddyArray[j].RemoveBlock(buddy);

            buddyArray[j].num_free_blocks -= 2;
            buddyArray[j].num_free_bytes  -= (blockToFree->size)*2;
            buddyArray[j].num_meta_data_bytes -= 2*sizeof(MallocMetadata);
            buddyArray[j].num_allocated_blocks -= 2;
            buddyArray[j].num_allocated_bytes  -= (blockToFree->size)*2;

            // whichever is lower address, we keep it
            if(buddy < blockToFree) {
                buddyArray[j+1].AddBlock(buddy);
                buddy->size *= 2;
                buddyArray[j+1].num_free_bytes += buddy->size;
                buddyArray[j+1].num_free_bytes += sizeof(MallocMetadata);
                buddyArray[j+1].num_free_blocks++;
                buddyArray[j+1].num_meta_data_bytes += sizeof(MallocMetadata);
                buddyArray[j+1].num_allocated_blocks++;
                buddyArray[j+1].num_allocated_bytes += buddy->size;
                buddyArray[j+1].num_allocated_bytes += sizeof(MallocMetadata);

                blockToFree = buddy; // merged block
            }
            else {
                buddyArray[j+1].AddBlock(blockToFree);
                blockToFree->size *= 2;
                buddyArray[j+1].num_free_bytes += blockToFree->size;
                buddyArray[j+1].num_free_bytes += sizeof(MallocMetadata);
                buddyArray[j+1].num_free_blocks++;
                buddyArray[j+1].num_meta_data_bytes += sizeof(MallocMetadata);
                buddyArray[j+1].num_allocated_blocks++;
                buddyArray[j+1].num_allocated_bytes += blockToFree->size;
                buddyArray[j+1].num_allocated_bytes += sizeof(MallocMetadata);
            }
        } else {
            return; // buddy not free
        }
    }
}

/**************************************************************
 * CheckIfMergePossible
 **************************************************************/
static int CheckIfMergePossible(MallocMetadata* oldBlock, size_t newSize)
{
    if(!oldBlock) return -1;
    if(oldBlock->cookie != GlobalCookie) return -1;

    int startOrder = GetBlockOrder(oldBlock->size);
    if(startOrder < 0) return -1;

    size_t currentSize = oldBlock->size;
    MallocMetadata* curr = oldBlock;
    for(int j=startOrder; j<MAX_ORDER; j++){
        if(currentSize >= newSize) return j;
        MallocMetadata* buddy = FindBuddy(curr, currentSize);
        if(buddy && buddy->is_free) {
            // merging feasible
            // next size is *2
            currentSize *= 2;
            // keep whichever is lower address as 'curr'
            if(buddy < oldBlock) {
                curr = buddy;
            } else {
                curr = oldBlock;
            }
        } else {
            return -1;
        }
    }
    return -1;
}

/**************************************************************
 * smalloc
 **************************************************************/
void* smalloc(size_t size)
{
    if(!is_buddy_initialized) {
        if(!initialize_buddy_allocator()) return nullptr;
    }
    if(size == 0 || size > 100000000) {
        return nullptr;
    }

    // if bigger than 128KB => mmap
    if(size + sizeof(MallocMetadata) > BLOCK_SIZE) {
        MallocMetadata* meta = allocate_with_mmap(size);
        if(!meta) return nullptr;
        return (char*)meta + sizeof(MallocMetadata);
    }

    size_t needed = size + sizeof(MallocMetadata);
    // code B approach: call "CutInHalf" to get a block
    MallocMetadata* freeBlock = CutInHalf(needed);
    if(!freeBlock) {
        return nullptr; // no block available
    }
    // now freeBlock is the correct size/order
    // Mark it as used => reduce free blocks etc.
    freeBlock->is_free = false;

    // final correction (like code B does):
    int i = GetBlockOrder(freeBlock->size);
    buddyArray[i].num_free_blocks--;
    buddyArray[i].num_free_bytes -= freeBlock->size;
    // In code B, sometimes we add back `sizeof(MallocMetadata)` if we want
    // to do "num_free_bytes += sizeof(MallocMetadata);" – depends on your exact logic

    return (char*)freeBlock + sizeof(MallocMetadata);
}

/**************************************************************
 * scalloc
 **************************************************************/
void* scalloc(size_t num, size_t size)
{
    if(num == 0 || size == 0) return nullptr;
    size_t totalSize = num*size;
    if(size != 0 && (totalSize / size) != num) {
        // overflow
        return nullptr;
    }
    void* p = smalloc(totalSize);
    if(!p) return nullptr;
    memset(p, 0, totalSize);
    return p;
}

/**************************************************************
 * sfree
 **************************************************************/
void sfree(void* p)
{
    if(!p) return;
    MallocMetadata* meta = (MallocMetadata*)((char*)p - sizeof(MallocMetadata));
    if(meta->cookie != GlobalCookie) {
        // canary check
        return;
    }
    if(meta->is_free) {
        return;
    }
    if(meta->is_mmap) {
        // free via mmap
        meta->is_free = true;
        free_mmap_block(meta);
        return;
    }

    // buddy block
    meta->is_free = true;
    int i = GetBlockOrder(meta->size);
    // code B style: add to array i
    buddyArray[i].AddBlock(meta);
    buddyArray[i].num_free_blocks++;
    buddyArray[i].num_free_bytes += meta->size;
    buddyArray[i].num_free_bytes -= sizeof(MallocMetadata);

    // attempt merges
    MergeBuddies(meta, -1);
}

/**************************************************************
 * srealloc
 **************************************************************/
void* srealloc(void* oldp, size_t newSize)
{
    if(newSize == 0) {
        sfree(oldp);
        return nullptr;
    }
    if(!oldp) {
        return smalloc(newSize);
    }
    MallocMetadata* oldBlock = (MallocMetadata*)((char*)oldp - sizeof(MallocMetadata));
    if(oldBlock->cookie != GlobalCookie)
        return nullptr;

    if(oldBlock->size >= newSize) {
        // already big enough
        return oldp;
    }

    // code B approach:
    // 1) if oldBlock is big enough => done
    // 2) else, check if we can merge to get enough space
    if(!oldBlock->is_mmap) {
        // buddy approach
        int mergeOrder = CheckIfMergePossible(oldBlock, newSize + sizeof(MallocMetadata));
        if(mergeOrder != -1) {
            // we do merges
            MergeBuddies(oldBlock, mergeOrder);
            // fix stats
            buddyArray[mergeOrder].num_free_bytes -= oldBlock->size;
            buddyArray[mergeOrder].num_free_bytes += (oldBlock->size / 2); 
            // or any other final fix that code B does
            return (char*)(oldBlock) + sizeof(MallocMetadata);
        }
    }

    // 3) fallback: allocate new, copy, free old
    void* newp = smalloc(newSize);
    if(!newp) return nullptr;
    size_t bytesToCopy = (oldBlock->size < newSize) ? oldBlock->size : newSize;
    memmove(newp, oldp, bytesToCopy);
    sfree(oldp);
    return newp;
}

/**************************************************************
 * Stats
 **************************************************************/
size_t _num_free_blocks()
{
    size_t total = 0;
    for(int i=0; i<=MAX_ORDER; i++){
        total += buddyArray[i].num_free_blocks;
    }
    total += mmapList.num_free_blocks;
    return total;
}

size_t _num_free_bytes()
{
    size_t total = 0;
    for(int i=0; i<=MAX_ORDER; i++){
        total += buddyArray[i].num_free_bytes;
    }
    total += mmapList.num_free_bytes;
    return total;
}

size_t _num_allocated_blocks()
{
    size_t total = 0;
    for(int i=0; i<=MAX_ORDER; i++){
        total += buddyArray[i].num_allocated_blocks;
    }
    total += mmapList.num_allocated_blocks;
    return total;
}

size_t _num_allocated_bytes()
{
    size_t total = 0;
    for(int i=0; i<=MAX_ORDER; i++){
        total += buddyArray[i].num_allocated_bytes;
    }
    total += mmapList.num_allocated_bytes;
    return total;
}

size_t _num_meta_data_bytes()
{
    size_t total = 0;
    for(int i=0; i<=MAX_ORDER; i++){
        total += buddyArray[i].num_meta_data_bytes;
    }
    total += mmapList.num_meta_data_bytes;
    return total;
}

size_t _size_meta_data()
{
    return sizeof(MallocMetadata);
}
