/*
 * Amrith Deepak
 * AndrewID: amrithd
 * 4/17/14
 * mm.c
 *
 * Structure of free and allocated blocks:
 *  Each block begins with a 4 byte header, its least significant bit is used as
 *  allocation flag while the rest of the bits store the size of the block
 *
 * Organization of the free list:
 *   Explicit list (doubly linked list) is used. The payload of each free
 *   block is used to store the pointers to previous and next free blocks
 *
 * Free list manipulation by allocator
 *  The allocator looks for the first fit in the free list.
 *  Heap is extended if a free block is not available
 *
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"

// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) //printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
printf("Checkheap failed on line %d\n", __LINE__);\
exit(-1);  \
}}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define MINCHUNKSIZE (1*sizeof(uint32_t) + 2*sizeof(void*) + 1*sizeof(uint32_t))

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

//double linked list, explicit list to keep of free blocks
typedef struct POINTERS PTRS;
struct POINTERS
{
    //store pointers to header not payload
    PTRS *prev;
    PTRS *next;
};

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static PTRS *dl_start=NULL, *dl_end=NULL;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void shrink(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

static void remove_freeblock(void *ptr);

/*
 *  Helper functions
 *  ----------------
 */

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static inline int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

// make size multiple of 8
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

// Return the size of the given block in multiples of the word size
static inline unsigned int block_size(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return (block[0] & 0x3FFFFFFF);
}

// Return true if the block is free, false otherwise
static inline int block_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return !(block[0] & 0x40000000);
}

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
static inline void block_mark(uint32_t* block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    unsigned int next = block_size(block) + 1;
    block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
    block[next] = block[0];
}

// Return a pointer to the memory malloc should return
static inline uint32_t* block_mem(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 1));
    
    return block + 1;
}

// Return the header to the previous block
static inline uint32_t* block_prev(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return block - block_size(block - 1) - 1;
}

// Return the header to the next block
static inline uint32_t* block_next(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return block + block_size(block) + 1;
}

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void)
{
    dl_start = dl_end = NULL;
    dbg_printf("\n\n\n\n");
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    
    //allocate the first block
    heap_listp = extend_heap((MINCHUNKSIZE)/WSIZE);
    checkheap(0);
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    char *bp;
    
    dbg_printf("<---mm_malloc---> Request for %d bytes \n", (int)size);
    
    /* $end mmmalloc */
    
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    if(size < 2 * DSIZE)
        size=2 * DSIZE;
    
    asize = 1 * WSIZE + ALIGN(size) + 1 * WSIZE;
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  //line:vm:mm:findfitcall
        place(bp, asize);                  //line:vm:mm:findfitplace
        dbg_printf
        ("<---mm_malloc---> Found a %d bytes free block, returning %lu\n"
         , GET_SIZE(HDRP(bp)), (size_t)bp);
        return bp;
    }
    
    /* No fit found. Get more memory and place the block */
    
    
    uint32_t extendsize = MAX(asize, 1<<9);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;                                  //line:vm:mm:growheap2
    place(bp, asize);                                 //line:vm:mm:growheap3
    dbg_printf
    ("<---mm_malloc---> Allocated %d bytes, Returning %lu\n"
     , (int)asize, (size_t)bp);
    return bp;
}
/* $end mmmalloc */

void add_freeblock(void *bp)
{
    PTRS *free_block = (PTRS*)bp;
    if(dl_start != NULL)//insert at the end
    {
        free_block->prev = dl_end;
        dl_end->next = free_block;
        free_block->next = NULL;
        dl_end = free_block;
    }
    else//list empty
    {
        free_block->prev = free_block->next = NULL;//store the NULLs in payload
        dl_start = dl_end = free_block;//make this as first and last free block
    }
}


/*
 * mm_free - Free a block and add it to free list
 */

void mm_free(void *bp)
{
    if(bp == 0)
        return;
    
    size_t size = GET_SIZE(HDRP(bp));
    dbg_printf("<---mm_free---> %lu (%d bytes)\n", (size_t)bp, (int)size);
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    add_freeblock(bp);
    coalesce(bp);
}

/* $end mmfree */
/*
 * coalesce - Boundary tag coalescing.
 * If prev and/or next blocks are found to be free, they are merged into a
 * bigger free block. Return ptr to coalesced block
 */
/* $begin mmfree */
static void *coalesce(void *bp)
{//TODO: recursively coalesce
    size_t prev_alloc = 1;
    size_t next_alloc = 1;
    
    prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    if (prev_alloc && next_alloc) {
        return bp;
    }
    size_t size = GET_SIZE(HDRP(bp));
    
    if (!prev_alloc) {
        return coalesce(PREV_BLKP(bp));//recursively coalesce prev blocks
    }
    
    if (!next_alloc) {
        dbg_printf("<---coalesce---> Coalescing next block %lu+%u="
                   , size, GET_SIZE(HDRP(NEXT_BLKP(bp))));
        remove_freeblock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        dbg_printf("%lu\n", size);
        if(!GET_ALLOC(HDRP(NEXT_BLKP(bp))))
            return coalesce(bp); //recursively coalesce next blocks
    }
    return bp;
}
/* $end mmfree */

/*
 * mm_realloc
 * when expanding a block, see if prev and/or next blocks are free
 * and try to extend, otherwise do naively when shrinking a block,
 * add the new free block to free list
 *
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }
    
    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }
    
    oldsize = GET_SIZE(HDRP(ptr));
    
    //Is the user requesting to reduce the block size
    size_t asize = size;
    if(asize < 2*DSIZE)
        asize=2*DSIZE;
    asize = 1*WSIZE+ALIGN(size)+1*WSIZE;
    
    if(asize < oldsize)
    {
        shrink(ptr, asize);
        return ptr;
    }
    
    // Check if next block(s) is free and extend this block.
    if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr))))
    {
        coalesce(NEXT_BLKP(ptr));
        dbg_printf("<---mm_realloc---> Next block of size %u is free\n"
                   , GET_SIZE(HDRP(NEXT_BLKP(ptr))));
        size_t new_size = GET_SIZE(HDRP(NEXT_BLKP(ptr))) + GET_SIZE(HDRP(ptr));
        if(new_size >= size)
        {
            remove_freeblock(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size, 1));
            dbg_printf("<---mm_realloc---> Returning Expanded block\n");
            return ptr;
        }
    }
    
    void *newptr = mm_malloc(size);
    if(!newptr) /* If realloc() fails the original block is left untouched  */
        return 0;
    
    /* Copy the old data. */
    if(size < oldsize)
        oldsize = size;
    
    
    memcpy(newptr, ptr, oldsize);
    
    /* Free the old block. */
    mm_free(ptr);
    
    dbg_printf("<---mm_realloc---> realloced and copied\n");
    
    return newptr;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer*/
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    
    dbg_printf("<---extend_heap---> Extending heap by %d bytes\n", (int)size);
    
    add_freeblock(bp);
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
//place() will split a free block into an allocated and a free.
//shrink will split an allocated block into an allocated and a free.
static void shrink(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    if (csize < asize) {
        dbg_printf("<---shrink---> shrinking %lu to %lu\n", csize, asize);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        add_freeblock(bp);
        coalesce(bp);
    }
}
/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= MINCHUNKSIZE) {
        remove_freeblock(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        add_freeblock(bp);
        coalesce(bp);
    }
    else {
        remove_freeblock(bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


//Remove a block from the free list
static void remove_freeblock(void *ptr)
{
    PTRS *fb = (PTRS *)ptr;
    if(dl_start == dl_end)//Only item
        dl_start = dl_end = NULL;
    else if(dl_start == fb)//First item
    {
        dl_start = fb->next;
        dl_start->prev = NULL;
    }
    else if (dl_end == fb)//Last item
    {
        dl_end = fb->prev;
        dl_end->next = NULL;
    }
    else//Middle item
    {
        fb->prev->next = fb->next;
        fb->next->prev = fb->prev;
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes. uses First Fit.
 */
static void *find_fit(size_t asize)
{
    void *bp;
    
    void *best = NULL;
    
    for (bp = dl_start; bp!=NULL; bp = ((PTRS*)bp)->next) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
            if(best != NULL)
            {
                if(GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best)))
                    best = bp;
            }
            else
                best = bp;
        }
    }
    return best;
}


/*
 * calloc - allocate and initialize to 0s
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;
    
    newptr = mm_malloc(bytes);
    memset(newptr, 0, bytes);
    
    return newptr;
}

/*print size and alloc bit in header and footer*/
static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;
    
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));
    
    printf("%p: header: [%lu:%c] footer: [%lu:%c]\n",
           bp, hsize, (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

//checks each block
static void mm_checkblock(void *bp)
{
    //point 4
    if(GET_SIZE(HDRP(bp)) < 24)
        printf("Error: Block is too small\n");
    
    //point 5
    if(!aligned(bp))
        printf("Error: %p is not aligned\n", bp);
    
    //point 6
    if(!in_heap(HDRP(bp)) || !in_heap(FTRP(bp)))
        printf("Error: Block boundary is outside the heap\n");
    
    //point 8
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
    
    //point 9
    if(!GET_ALLOC(HDRP(bp)))
    {
        if(in_heap(HDRP(PREV_BLKP(bp)))){
            if(!GET_ALLOC(HDRP(PREV_BLKP(bp))))
                printf("Error: Prev block is free\n");
        }
        
        if(in_heap(HDRP(NEXT_BLKP(bp)))){
            if(!GET_ALLOC(HDRP(NEXT_BLKP(bp))))
                printf("Error: Next block is free\n");
        }
    }
}


/*
 * mm_checkheap
 * Checks
 *  1. prologue header
 *  2. prologue footer
 *  3. epilogue header
 *  4. block size
 *  5. each block's address alignment
 *  6. each block is within the heap boundaries?
 *  7.
 *  8. each blocks header equals footer
 *  9. No two consecutive free blocks in the heap
 *
 * 10. pointer consistency
 * 11. count of free blocks in blocks and that list match
 * 12. All free pointers point within heap
 */
int mm_checkheap(int verbose)
{
    void *bp = heap_listp;
    void *heap = DSIZE + (char*)mem_heap_lo();
    
    //point 1
    if ((GET_SIZE(HDRP(heap)) != DSIZE) || !GET_ALLOC(HDRP(heap)))
        printf("Bad prologue header\n");
    //point 2
    if ((GET(HDRP(heap_listp)) != GET(HDRP(heap_listp))))
        printf("Bad prologue footer\n");
    
    int count1=0, count2=0;
    
    for (bp = (heap_listp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        mm_checkblock(bp);
        if(!(GET_ALLOC(HDRP(bp))))
            count1++;
    }
    
    //point 3
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
    
    bp = dl_start;
    while(bp != NULL) {
        count2++;
        
        PTRS *block = (PTRS*)bp;
        
        //point 10
        if(block->prev != NULL)
            if(bp != block->prev->next)
                printf("Error: prev pointer inconsistent");
        
        //point 10
        if(block->next != NULL)
            if(bp != block->next->prev)
                printf("Error: next pointer inconsistent");
        
        //point 12
        if(!in_heap(bp))
            printf("Not in heap.");
        
        bp = ((PTRS*)bp)->next;
    }
    
    //point 11
    if(count1 != count2)
        printf("Error: free blocks count not matching");
    return 0;
}