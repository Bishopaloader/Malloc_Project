/*
 * mm.c - Explicit free list based malloc package with first fit placing and real time coalescing.
 * 
 * Here the init function initializes the heap with a padding, header and footer.
 * 
 * Each allocated block is of the form Header, Payload, Footer and each free block is of the form Header,Prev Pointer, Next Pointer, Footer.
 * 
 * Splitting is also done when possible to avoid internal fragmentation.
 * 
 * The free list is not actually a list but a virtual list made by adding pointers of previous free block to newly freed block 
 * 
 * Eack block is added to the top of the virtual list, hence its previou spointer is NULL and next pointer gices the next free block
 * 
 *When a allocated block is freed, pointers are added to its payload and when a free block is allocated, it is removed from virtual free list.
 
 *To find a suitable free block during mallocing/reallocing, the process is eased a lot as entire list doesn't have to be traversed but only the free blocks. 
 
 *Coalescing is done whenever, a block is freed, hence avoiding fragmentation and 
 
 *Some helper functions like extend_heap, first_fit, coalesce, add, rm(standing for remove) have been implemented and used. 
*/

 
 
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Loader",
    /* First member's full name */
    "Aenik Shah",
    /* First member's email address */
    "201101046@daiict.ac.in",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define ALIGNMENT 8
#define WSIZE 4 /* rounds up to the nearest multiple of alignment */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) /*macros*/
#define CHUNKSIZE (1 << 12) /* Extend heap by this many bytes.*/
#define MAX(x, y) ((x) > (y) ? (x) : (y)) /* Pack a size and allocated bit into a word. */
#define PACK(size, alloc) ((size) | (alloc))/* Read and write a word at address p */
#define GET(p) (* ((unsigned int *) (p)))
#define PUT(p, val) (*(unsigned int *)(p) = (val))/* Read the size and allocated fields from address p */
#define GET_SIZE(p) ((unsigned int)GET(p) & ~(ALIGNMENT-1))
#define GET_ALLOC(p) (GET(p) & 0x1)/* Given block pointer bp, compute address of its header and footer */
#define HDRP(bp) ((void *)(bp) - WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - 2*WSIZE)/* Given block pointer bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void*)(bp) + GET_SIZE(((void *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((void*)(bp) - GET_SIZE(((void *)(bp) - 2*WSIZE)))
#define IGNORE(value) (assert((int)value || 1))/*=== MACROS FOR POINTER ARITHMETIC (explicit free list) ===*//* |header|PREV|NEXT|...|footer| *//* Given a header pointer ptr, compute address of NEXT and PREV blocks. Only works if block is free.*/
#define PREV_FREE_BLKP(ptr) (*(void **) (ptr))
#define NEXT_FREE_BLKP(ptr) (*(void **) (ptr + WSIZE))/* Given a header pointer ptr, set the NEXT and PREV pointers to their new addresses. Only works if block is free. */
#define SET_PREV_FREE(bp, prev) (*((void **)(bp)) = prev) /* Given block pointers ptr and prev, set the PREV pointer of ptr to *prev. */
#define SET_NEXT_FREE(bp, next) (*((void **)(bp + WSIZE)) = next) /* Given block pointers ptr and next, set the NEXT pointer of ptr to next*/

static void *free_list_head; /* Points to the first block in the free list.*/
static void *heap_bottom; /* Points to the prologue block.*/
/* function that we need to implement for the implementation of the init,free,realloc functions  */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static void delete_node(void *bp);
static void insert_node(void *bp);

/* 
  mm_init - initialize the malloc package.
 it returns -1 when error otherwise 0
*/
 
int mm_init(void)
{
    
    /* Create the initial empty heap */
    if ((heap_bottom = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_bottom, 0); /* Alignment padding */
    PUT(heap_bottom + (1*WSIZE), PACK(ALIGNMENT, 1)); /* Prologue header */
    PUT(heap_bottom + (2*WSIZE), PACK(ALIGNMENT, 1)); /* Prologue footer */
    PUT(heap_bottom + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    
    heap_bottom += 2*WSIZE;
    
    free_list_head = NULL;
    /* Extend empty heap with free block of CHUNKSIZE bytes.
     * Set the head of the free list to the block pointer of the new memory.
     */
    if ((extend_heap(CHUNKSIZE/WSIZE)) == NULL) {
        return -1;
    }
       return 0;
}


static void *extend_heap(size_t words) {
    void *bp;
    size_t size;
    /* Allocate an even number of words to maintain alignment */
    size = ALIGN(words * WSIZE);
    if ((long)(bp =  mem_sbrk(size)) == -1) 
	{ 
        return NULL;/* Returns double-word aligned chunk of memory following header of epilogue block. Epilogue block header overwritten by header of new free block.*/
    }
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* free block header (overwrites original epilogue header) */
    PUT(FTRP(bp), PACK(size, 0)); /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    return coalesce(bp);/* Coalesce if previous block was free */
}
/* Merges adjacent free blocks in constant time and maintains explicit free list using LIFO policy. */
 static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {
        insert_node(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        insert_node(bp);
    }
    else if (!prev_alloc && next_alloc) {
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_node(bp);
    }
    else {
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_node(bp);
    }
    return bp;
}


/* Remove a block pointer bp from the free list. If we are trying to remove the pointer at the root of the list, need to
 * update the root to be the next block pointer.
 */
static void delete_node(void *bp) {
    
    
    void *next = (void *) NEXT_FREE_BLKP(bp);
    void *prev = (void *) PREV_FREE_BLKP(bp);
    if (prev == NULL) { /* Start of the list */
        free_list_head = next;
    } else {
        SET_NEXT_FREE(prev, next);
    }
    
    if (next != NULL) { /* Not the end of list */
        SET_PREV_FREE(next, prev);
    }
}

/* Add the block pointer bp to the free list in address order*/
static void insert_node(void *bp) {
    void *curr = free_list_head;
    void *saved = curr;
    void *prev = NULL;
    while (curr != NULL && bp < curr) {
        prev = PREV_FREE_BLKP(curr);
        saved = curr;
        curr = NEXT_FREE_BLKP(curr);
    }
    
    SET_PREV_FREE(bp, prev);
    SET_NEXT_FREE(bp, saved);
    if (prev != NULL) {
        SET_NEXT_FREE(prev, bp);
    } else { 
        free_list_head = bp;/* Insert bp before current free list head*/
    }
    if (saved != NULL) {
        SET_PREV_FREE(saved, bp);
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   size_t asize; /* Adjusting block size*/
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;
    /* Ignore spurious requests */
    if (size == 0) {
        return NULL;
    }
    
    /* Adjust block size to include overhead, alignment requirements*/
    if (size <= ALIGNMENT) {
        asize = 2 * ALIGNMENT; /* Minimum block size 16: 8 bytes for alignment, 8 bytes for header and footer*/
    } else {
        asize = ALIGN(size + (2 * WSIZE)); /* Add in overhead bytes and round up to nearest multiple of ALIGNMENT */
    }
    
    /* Search free list for a fit*/
    if ((bp = find_fit(asize)) != NULL) {
        bp = place(bp, asize);
        return bp;
    }
    
    /* No fit found. Get more meomory and place the block. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL; /* No more heap space */
    }
    bp = place(bp, asize);
  
    return bp;
}

static void *find_fit(size_t asize) {
    
 
    void *bp;
    for(bp = free_list_head; bp != NULL; bp = NEXT_FREE_BLKP(bp)) {
        if(asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    //overlap_free_test(bp);
    return NULL; 
}

/* Places the requested block and split the excess. Assumes that block
 * pointed to by bp is large enough to accomodate asize.
 *
 * The first part of the block is allocated and the second part is kept free
 */
 
static void *place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
	int remaining_free_size=csize-asize;
    if ((csize - asize) >= (2*ALIGNMENT)) { // Enough room left to split
        delete_node(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *orig_bp = bp;
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(remaining_free_size, 0));
        PUT(FTRP(bp), PACK(remaining_free_size, 0));
        insert_node(bp);
        bp = orig_bp;
    } else { // No need to split; include entire free block in size.
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        delete_node(bp);
    }
    return bp;
}
/*
  mm_free - frees a block of memory, enabling it to be reused later
 */
void mm_free(void *ptr)
{
 size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);    
}
 /* mm_realloc - reallocates a memory block to update it with the given s 
 */
void *mm_realloc(void *ptr, size_t size)
{  size_t asize; 
    void *bp;
    
    /* Ignore spurious requests */
    if (size == 0) {
        return NULL;
    }
    
    /* Adjust block size to include overhead, alignment requirements*/
    if (size <= ALIGNMENT) {
        asize = 2 * ALIGNMENT; /* Minimum block size 16: 8 bytes for alignment, 8 bytes for header and footer*/
    } else {
        // asize = ALIGN(size + (2 * ALIGNMENT)); /* Add in overhead bytes and round up to nearest multiple of ALIGNMENT */
        asize = ALIGN(size + (2 * WSIZE));
    }
    
    size_t cur_size = GET_SIZE(HDRP(ptr));
    
    if (cur_size > asize) {
        bp = place(ptr, asize);
        assert(bp == ptr);
    } else if (cur_size < asize) {
        void *next_bp = NEXT_BLKP(ptr);
        void *next_block_header = HDRP(next_bp);
        /* see if next block has room for the new size */
      
        if (!GET_ALLOC(next_block_header) && GET_SIZE(next_block_header) >= (asize-cur_size )) {
            delete_node(next_bp);
            PUT(HDRP(ptr), PACK(cur_size + GET_SIZE(next_block_header), 0));
            PUT(FTRP(ptr), PACK(cur_size + GET_SIZE(next_block_header), 0));
            
            void *temp1; // hold data going to be overwritten by the prev pointer in insert_node
            void *temp2; // hold data going to be overwritten by the next pointer in insert_node
            memcpy(&temp1, ptr, WSIZE);
            memcpy(&temp2, ptr + WSIZE, WSIZE);
            
            insert_node(ptr);
            bp = place(ptr, asize);
            
            /* copy back the saved data */
            memcpy(bp, &temp1, WSIZE);
            memcpy(bp + WSIZE, &temp2, WSIZE);
            
          
        } else if ((bp = find_fit(asize)) != NULL) {  /* Search free list for a fit*/
            bp = place(bp, asize);
            memcpy(bp, ptr, cur_size - (2 * WSIZE));
            mm_free(ptr);
        } else {
            /* No fit found. Get more meomory and place the block. */
            size_t extendsize = MAX(asize, CHUNKSIZE);
            if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
                return NULL; /* No more heap space */
            }
            bp = place(bp, asize);
            memcpy(bp, ptr, cur_size - (2 * WSIZE));
            mm_free(ptr);
        }
    } else {
        bp = ptr;
    }
  
    return bp;
}
