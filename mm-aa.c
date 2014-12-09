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
#define CHUNKSIZE ((size_t)0)
#define PACK(size, color, alloc) ((size) | (alloc) | ((color) << 1))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~7)
#define GET_ALLOC(p) (GET(p) & 1)
#define GET_COLOR(p) ((GET(p) >> 1) & 1)
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define BLOCK_SIZE(bp) (GET_SIZE(HDRP(bp)))
#define BLOCK_COLOR(bp) (GET_COLOR(HDRP(bp)))
#define LEFT_CHILD(bp) (GET(bp))
#define RIGHT_CHILD(bp) (GET((char*)(bp) + WSIZE))
#define CHILD(bp, ind) (GET((char*)(bp) + ind * WSIZE))
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(HDRP(bp) - WSIZE))
#define L (0)
#define R (1)
#define BLACK (0)
#define RED (1)
int LEFTER(void *b1, void *b2)
{
    return (BLOCK_SIZE(b1) < BLOCK_SIZE(b2)) 
        || (BLOCK_SIZE(b1) == BLOCK_SIZE(b2) && (b1) < (b2));
}
inline static void setcolor(void *bp, int color)
{
    void *hp = HDRP(bp);
    int size = GET_SIZE(hp);
    int alloc = GET_ALLOC(hp);
    PUT(hp, PACK(size, color, alloc));
}

/* forward declarations and type definitions */
static void *coalesce(void *bp);
typedef unsigned int freenode_offset;
static freenode_offset remove_freenode(freenode_offset root, freenode_offset node);


/* pointer to the first (by address order) block (the prologue block) of the heap */
static void* heap_listp;
static void* nullnode;
/* root node of the free block binary search tree */
static freenode_offset free_blocks_tree;

static inline void* getbp(freenode_offset off)
{
    return nullnode + off;
}
static inline freenode_offset getoffset(void* bp)
{
    return (freenode_offset) (bp - nullnode);
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    free_blocks_tree = 0;
    if((heap_listp = mem_sbrk(8 * WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp, 0);     /* for alignment */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 0, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 0, 1));

    /* the red-black tree nullnode */
    nullnode = heap_listp + 4 * WSIZE;
    PUT(heap_listp + (3*WSIZE), PACK(2*DSIZE, BLACK, 1));
    PUT(heap_listp + (4*WSIZE), 0);
    PUT(heap_listp + (5*WSIZE), 0);
    PUT(heap_listp + (6*WSIZE), PACK(2*DSIZE, BLACK, 1));

    PUT(heap_listp + (7*WSIZE), PACK(0, 0, 1));
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

    PUT(HDRP(bp), PACK(size, 0, 0));
    PUT(FTRP(bp), PACK(size, 0, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1));

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
 * Helper for swapping the color of two nodes
 */
void swap_color(void *b1, void* b2)
{
    int c1 = BLOCK_COLOR(b1);
    setcolor(b1, BLOCK_COLOR(b2));
    setcolor(b2, c1);
}

/*
 * Binary search tree rotation. Arguments l stands for the direction.
 * When l is L, rotate the left son.
 */
static void* rotate(void* rt, int l)
{
    int r = L ^ R ^ l;
    void *newrt = getbp(CHILD(rt, l));
    CHILD(rt, r) = CHILD(newrt, r);
    CHILD(newrt, r) = getoffset(rt);
    return newrt;
}

/*
 * Skew
 */
static void* skew(void* bp)
{
    if(BLOCK_COLOR(getbp(LEFT_CHILD(bp))) == RED) {
        bp = rotate(bp, L);
        swap_color(bp, getbp(RIGHT_CHILD(bp)));
    }
    return bp;
}

/*
 * Split
 */
static void* split(void* root)
{
    void *rbp = getbp(RIGHT_CHILD(root));
    void *rrbp = getbp(RIGHT_CHILD(rbp));
    if(BLOCK_COLOR(rbp) == RED && BLOCK_COLOR(rrbp) == RED) {
        root = rotate(root, R);
        setcolor(getbp(RIGHT_CHILD(root)), BLACK);
    }
    return root;
}

/*
 * Insert nodep into the AA tree and maintain the AA properties.
 */
static void* insertAA(void* bp, void* nodep)
{
    if(bp == nullnode) {
        LEFT_CHILD(nodep) = 0;
        RIGHT_CHILD(nodep) = 0;
        setcolor(nodep, RED);
        return nodep;
    }
    if(LEFTER(nodep, bp)) {
        LEFT_CHILD(bp) = getoffset(insertAA(getbp(LEFT_CHILD(bp)), nodep));
    } else {
        RIGHT_CHILD(bp) = getoffset(insertAA(getbp(RIGHT_CHILD(bp)), nodep));
    }
    bp = skew(bp);
    bp = split(bp);
    return bp;
}

/*
 * Wrapper for insertAA() and make sure the root is BLACK.
 */
static freenode_offset insert_freenode(freenode_offset root, freenode_offset node)
{
    void *rootbp;
    rootbp = insertAA(getbp(root), getbp(node));
    setcolor(rootbp, BLACK);
    return getoffset(rootbp);
}

static void place(void *bp, size_t size)
{
    assert(BLOCK_SIZE(bp) >= size);
    size_t csize = BLOCK_SIZE(bp);
    if(csize - size >= MINIMAL_BLOCKSIZE) {
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - size, 0, 0));
        PUT(FTRP(bp), PACK(csize - size, 0, 0));
        LEFT_CHILD(bp) = 0;
        RIGHT_CHILD(bp) = 0;
        free_blocks_tree = insert_freenode(free_blocks_tree, getoffset(bp));
    } else {
        PUT(HDRP(bp), PACK(csize, 0, 1));
        PUT(FTRP(bp), PACK(csize, 0, 1));
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
        PUT(HDRP(prev), PACK(size, 0, 0));
        PUT(FTRP(prev), PACK(size, 0, 0));
        bp = prev;
    }
    next = NEXT_BLKP(bp);
    if(GET_ALLOC(HDRP(next)) == 0) {
        free_blocks_tree = remove_freenode(free_blocks_tree, getoffset(next));
        size += BLOCK_SIZE(next);
        PUT(HDRP(bp), PACK(size, 0, 0));
        PUT(FTRP(bp), PACK(size, 0, 0));
    }

    return bp;
}

/*
 * Helper function for getting the left most node of the search tree
 */
static void* get_leftmost_node( void *root )
{
    while(LEFT_CHILD(root) != 0) {
        root = getbp(LEFT_CHILD(root));
    }
    return root;
}

/*
 * Decrease the level of root.
 * Child nodes may need repainted.
 */
void decrease_level(void *rt, int decreaseL, int decreaseR)
{
    setcolor(rt, BLACK);
    if(decreaseL) {
        setcolor(getbp(LEFT_CHILD(rt)), RED);
    }
    if(decreaseR) {
        void *rc = getbp(RIGHT_CHILD(rt));
        if(BLOCK_COLOR(rc) == RED) {
            setcolor(getbp(LEFT_CHILD(rc)), RED);
            setcolor(getbp(RIGHT_CHILD(rc)), RED);
        }
        setcolor(rc, RED);
    }
}

/*
 * Removing a leaf node from the AA tree. 
 * The BLACK leaf case if nontrivial.
 */
static void* remove_aa_leaf(void *root, void *node, int *level_diff)
{
    if(root == nullnode) {
        fprintf(stderr, "remove_aa_leaf: can't find the node\n");
        return nullnode;
    }
    if(node == root) {
        // Got the node, it should be a leaf.
        assert(LEFT_CHILD(node) == 0 && RIGHT_CHILD(node) == 0);
        *level_diff = -1;
        return nullnode;
    } else {
        int dir;
        dir = LEFTER(node, root) ? L : R;
        int old_color = BLOCK_COLOR(getbp(CHILD(root, dir)));
        CHILD(root, dir) = getoffset(remove_aa_leaf(getbp(CHILD(root, dir)), node, level_diff));
        if(*level_diff == 0) {
            setcolor(getbp(CHILD(root, dir)), old_color);
        } else {
            if(old_color == RED) {
                setcolor(getbp(CHILD(root, dir)), BLACK);
                *level_diff = 0;
            } else {
                if(dir == L)
                    decrease_level(root, 0, 1);
                else
                    decrease_level(root, 1, 0);
                root = skew(root);

                void *rc = getbp(RIGHT_CHILD(root));
                RIGHT_CHILD(root) = getoffset(skew(rc));

                rc = getbp(RIGHT_CHILD(root));
                void *rrc = getbp(RIGHT_CHILD(rc));
                RIGHT_CHILD(rc) = getoffset(skew(rrc));

                void *newrt = split(root);
                if(newrt != root)
                    *level_diff = 0;
                root = newrt;
                RIGHT_CHILD(root) = getoffset(split(getbp(RIGHT_CHILD(root))));
            }
        }
        return root;
    }
}

/*
 * Replace the old node in the tree with the new one.
 */
static void* replace(void *root, void *old, void *neew)
{
    if(root == nullnode) {
        fprintf(stderr, "Replace: can't find the old node\n");
        return nullnode;
    }
    if(root == old) {
        LEFT_CHILD(neew) = LEFT_CHILD(old);
        RIGHT_CHILD(neew) = RIGHT_CHILD(old);
        setcolor(neew, BLOCK_COLOR(old));
        root = neew;
    } else if(LEFTER(old, root)) {
        LEFT_CHILD(root) = getoffset(replace(getbp(LEFT_CHILD(root)), old, neew));
    } else {
        RIGHT_CHILD(root) = getoffset(replace(getbp(RIGHT_CHILD(root)), old, neew));
    }
    return root;
}

/*
 * Remove a free node from the tree.
 */
static freenode_offset remove_freenode(freenode_offset root, freenode_offset node)
{
    void *rootbp = getbp(root);
    void *nodebp = getbp(node);
    if(LEFT_CHILD(nodebp) == 0 && RIGHT_CHILD(nodebp) == 0) {
        int tmp;
        rootbp = remove_aa_leaf(rootbp, nodebp, &tmp);
        setcolor(rootbp, BLACK);
    } else {
        void *succ = get_leftmost_node(getbp(RIGHT_CHILD(nodebp)));
        root = remove_freenode(root, getoffset(succ));
        rootbp = getbp(root);
        rootbp = replace(rootbp, nodebp, succ);
    }
    return getoffset(rootbp);
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
    PUT(HDRP(ptr), PACK(size, 0, 0));
    PUT(FTRP(ptr), PACK(size, 0, 0));
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
