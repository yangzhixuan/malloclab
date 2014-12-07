/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* helper macros for manipulating block pointers */
#define WSIZE 4
#define DSIZE 8
#define MINIMAL_BLOCKSIZE 16
#define CHUNKSIZE (1<<12)
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~7)
#define GET_ALLOC(p) (GET(p) & 1)
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define BLOCK_SIZE(bp) (GET_SIZE(HDRP(bp)))
#define LEFT_CHILD(bp) (GET(bp))
#define RIGHT_CHILD(bp) (GET((char*)(bp) + WSIZE))
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(HDRP(bp) - WSIZE))

/* forward declarations and type definitions */
static void *coalesce(void *bp);
typedef unsigned int freenode_offset;


/* pointer to the first (by address order) block (the prologue block) of the heap */
static void* heap_listp;
static void* heap_start;
/* root node of the free block binary search tree */
static freenode_offset free_blocks_tree;

static inline void* getbp(freenode_offset off)
{
    return heap_start + off;
}
static inline freenode_offset getoffset(void* bp)
{
    return (freenode_offset) (bp - heap_start);
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    free_blocks_tree = 0;
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) -1)
        return -1;
    heap_start = heap_listp;
    PUT(heap_listp, 0);     /* for alignment */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += 2 * WSIZE;

    return 0;
}

/*
 * Extend the heap and maintain the epilogue block.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}


/*
 * Search the free block tree for a best fit
 */
static freenode_offset find_fit(freenode_offset root, size_t size)
{
    size_t best_fit = (size_t) 0 - 1;
    freenode_offset best_fit_node = 0;

    while(root != 0) {
        void *bp = getbp(root);
        if(BLOCK_SIZE(bp) >= size) {
            size_t diff = BLOCK_SIZE(bp) - size;
            if(diff <= best_fit) {
                best_fit = diff;
                best_fit_node = root;
            }
            root = LEFT_CHILD(bp);
        } else {
            root = RIGHT_CHILD(bp);
        }
    }
    return best_fit_node;
}

/*
 * Helper function for getting the left most node of the search tree
 */
static freenode_offset get_leftmost_node( freenode_offset root )
{
    assert( root != 0 );

    freenode_offset child = LEFT_CHILD( getbp(root) );
    while(child != 0) {
        root = child;
        child = LEFT_CHILD( getbp(root) );
    }
    return root;
}

/*
 * Remove a free node from the tree.
 */
static freenode_offset remove_freenode(freenode_offset root, freenode_offset node)
{
    if(root == 0) {
        dbg_printf("should not remove nonexistent node\n");
        return 0;
    }
    void *bp = getbp(root);
    void *nodep = getbp(node);
    if(root != node) {
        if(BLOCK_SIZE(nodep) < BLOCK_SIZE(bp)) {
            LEFT_CHILD(bp) = remove_freenode(LEFT_CHILD(bp), node);
        } else {
            RIGHT_CHILD(bp) = remove_freenode(RIGHT_CHILD(bp), node);
        } 
        return root;
    } else {
        if( RIGHT_CHILD(bp) == 0 ) {
            return LEFT_CHILD(bp);
        } else if( LEFT_CHILD(bp) == 0 ) {
            return RIGHT_CHILD(bp);
        }else {
            /* if the node has both children, we have to find the leftmost node
             * in the right subtree to replace this node in the tree */
            freenode_offset newrt;
            newrt = get_leftmost_node( RIGHT_CHILD(bp) );
            RIGHT_CHILD(bp) = remove_freenode( RIGHT_CHILD(bp), newrt);
            void *newrt_bp = getbp(newrt);
            LEFT_CHILD(newrt_bp) = LEFT_CHILD(bp);
            RIGHT_CHILD(newrt_bp) = RIGHT_CHILD(bp);
            return newrt;
        }
    }
}

/*
 *
 */
static freenode_offset insert_freenode(freenode_offset root, freenode_offset node)
{
    if(root == 0)
        return node;
    void *bp = getbp(root);
    void *nodep = getbp(node);
    if(BLOCK_SIZE(nodep) < BLOCK_SIZE(bp)) {
        LEFT_CHILD(bp) = insert_freenode(LEFT_CHILD(bp), node);
    } else {
        RIGHT_CHILD(bp) = insert_freenode(RIGHT_CHILD(bp), node);
    }
    return root;
}

static void place(void *bp, size_t size)
{
    assert(BLOCK_SIZE(bp) >= size);
    size_t csize = BLOCK_SIZE(bp);
    if(csize - size >= MINIMAL_BLOCKSIZE) {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - size, 0));
        PUT(FTRP(bp), PACK(csize - size, 0));
        LEFT_CHILD(bp) = 0;
        RIGHT_CHILD(bp) = 0;
        free_blocks_tree = insert_freenode(free_blocks_tree, getoffset(bp));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * Coalesce adjacent free blocks.
 */
static void* coalesce(void *bp)
{
    void *prev;
    void *next;
    size_t size = BLOCK_SIZE(bp);
    prev = PREV_BLKP(bp);
    if(GET_ALLOC(HDRP(prev)) == 0) {
        free_blocks_tree = remove_freenode(free_blocks_tree, getoffset(prev));
        size += BLOCK_SIZE(prev);
        PUT(HDRP(prev), PACK(size, 0));
        PUT(FTRP(prev), PACK(size, 0));
        bp = prev;
    }
    next = NEXT_BLKP(bp);
    if(GET_ALLOC(HDRP(next)) == 0) {
        free_blocks_tree = remove_freenode(free_blocks_tree, getoffset(next));
        size += BLOCK_SIZE(next);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    return bp;
}
/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;
    size_t extendsize;
    void *bp;
    freenode_offset offset;

    if(size == 0)
        return NULL;

    if(size <= DSIZE)
        asize = MINIMAL_BLOCKSIZE;
    else
        asize = (size + DSIZE + DSIZE - 1) / DSIZE * DSIZE;

    offset = find_fit(free_blocks_tree, asize);

    if(offset == 0) {
        /* can't find a fit, allocate more memory and place the block */
        extendsize = asize;
        if(extendsize < CHUNKSIZE) {
            extendsize = CHUNKSIZE;
        }
        bp = extend_heap(extendsize / WSIZE);
        if(bp == NULL)
            return NULL;
    } else {
        bp = getbp(offset);
        free_blocks_tree = remove_freenode(free_blocks_tree, offset);
    }
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    if(ptr == NULL)
        return;

    size_t size = BLOCK_SIZE(ptr);
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    ptr = coalesce(ptr);
    LEFT_CHILD(ptr) = 0;
    RIGHT_CHILD(ptr) = 0;
    free_blocks_tree = insert_freenode(free_blocks_tree, getoffset(ptr));
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = BLOCK_SIZE(oldptr) - DSIZE;
    if(size < oldsize) 
        oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
}
