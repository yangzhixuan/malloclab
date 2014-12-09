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
#include <setjmp.h>

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
#define CACHED_SIZE 64
#define CACHED_CLASSES (CACHED_SIZE / DSIZE)
#define CHUNKSIZE ((size_t) 80)
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
#define PREV_FREE(bp) (GET(bp))
#define NEXT_FREE(bp) (GET((char*)(bp) + WSIZE))
#define CHILD(bp, ind) (GET((char*)(bp) + (ind) * WSIZE))
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(HDRP(bp) - WSIZE))
#define L (0)
#define R (1)
#define BLACK (0)
#define RED (1)

inline static int LEFTER(void *b1, void *b2)
{
    return (BLOCK_SIZE(b1) < BLOCK_SIZE(b2))
        || (BLOCK_SIZE(b1) == BLOCK_SIZE(b2) && b1 < b2);
}

inline static void setcolor(void *bp, int color)
{
     *HDRP(bp) = ((*HDRP(bp)) & (~2)) | (color << 1);
}

/* forward declarations and type definitions */
static void *coalesce(void *bp);
typedef unsigned int freenode_offset;
static void remove_freenode(void* node);


/* pointer to the first (by address order) block (the prologue block) of the heap */
static void* heap_listp;
static void* nullnode;
static void* lists_header;
/* root node of the free block binary search tree */
static void* free_blocks_tree;

static inline void* getbp(freenode_offset off)
{
    return nullnode + off;
}
static inline freenode_offset getoffset(void* bp)
{
    return (freenode_offset) (bp - nullnode);
}

static inline void* getheader(int size)
{
    assert(size >= MINIMAL_BLOCKSIZE && size <= CACHED_SIZE);
    size = size / DSIZE * DSIZE;
    return lists_header + (size - MINIMAL_BLOCKSIZE) * 2;
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    if((heap_listp = mem_sbrk( (1 + 1 + CACHED_CLASSES) * 4 * WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp, 0);     /* for alignment */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 0, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 0, 1));

    /* the red-black tree nullnode */
    free_blocks_tree = nullnode = heap_listp + 4 * WSIZE;
    PUT(heap_listp + (3*WSIZE), PACK(2*DSIZE, BLACK, 1));
    PUT(heap_listp + (4*WSIZE), 0);
    PUT(heap_listp + (5*WSIZE), 0);
    PUT(heap_listp + (6*WSIZE), PACK(2*DSIZE, BLACK, 1));

    /* headers for the cached lists */
    int i;
    for(i = 0; i < CACHED_CLASSES; i++) {
        PUT(heap_listp + (7+i*4+0)*WSIZE, PACK(2*DSIZE, 0, 1));
        PUT(heap_listp + (7+i*4+1)*WSIZE, 0);
        PUT(heap_listp + (7+i*4+2)*WSIZE, 0);
        PUT(heap_listp + (7+i*4+3)*WSIZE, PACK(2*DSIZE, 0, 1));
    }
    lists_header = heap_listp + 7*WSIZE;

    PUT(heap_listp + ((7+CACHED_CLASSES*4)*WSIZE), PACK(0, 0, 1));
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
 *
 */
static void* find_fit(size_t size)
{

    if(size <= CACHED_SIZE) {
        void *header = getheader(size);
        if(NEXT_FREE(header) != 0) {
            return getbp(NEXT_FREE(header));
        }
        return find_fit(size + (size == CACHED_SIZE ? 1 : DSIZE));
    } else {
        size_t best_fit = (size_t) 0 - 1;
        void *best_fit_node = NULL;
        void *bp = free_blocks_tree;

        while(bp != nullnode) {
            if(BLOCK_SIZE(bp) >= size) {
                size_t diff = BLOCK_SIZE(bp) - size;
                if(diff <= best_fit) {
                    best_fit = diff;
                    best_fit_node = bp;
                    if(diff == 0)
                        break;
                }
                bp = getbp(LEFT_CHILD(bp));
            } else {
                bp = getbp(RIGHT_CHILD(bp));
            }
        }
        return best_fit_node;
    }
}


/*
 * Binary search tree rotation. Arguments l stands for the direction.
 * When l is L, rotate the left son.
 */
inline static void* rotate(void* rt, int l)
{
    int r = L ^ R ^ l;
    void *newrt = getbp(CHILD(rt, l));
    CHILD(rt, l) = CHILD(newrt, r);
    CHILD(newrt, r) = getoffset(rt);
    return newrt;
}

/*
 * Skew
 */
inline static void* skew(void* bp)
{
    if(BLOCK_COLOR(getbp(LEFT_CHILD(bp))) == RED) {
        bp = rotate(bp, L);
        void *rbp = getbp(RIGHT_CHILD(bp));
        setcolor(bp, BLOCK_COLOR(rbp));
        setcolor(rbp, RED);
    }
    return bp;
}

/*
 * Split
 */
inline static void* split(void* root)
{
    void *rbp = getbp(RIGHT_CHILD(root));
    void *rrbp = getbp(RIGHT_CHILD(rbp));
    if(BLOCK_COLOR(rbp) == RED && BLOCK_COLOR(rrbp) == RED) {
        root = rotate(root, R);
        setcolor(rrbp, BLACK);
    }
    return root;
}

/*
 * Insert nodep into the AA tree and maintain the AA properties.
 */
static void* insertAA(void* bp, void* nodep)
{
    if(bp == nullnode) {
        // set two children point to nullnode
        *(long*)nodep = 0;
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
 * 
 */
static void insert_freenode(void *node)
{
    if(BLOCK_SIZE(node) <= CACHED_SIZE) {
        /* free blocks smaller than CACHED_SIZE bytes will be stored 
         * in segregated lists rather than the red black tree */
        void *header = getheader(BLOCK_SIZE(node));
        NEXT_FREE(node) = NEXT_FREE(header);
        if(NEXT_FREE(node) != 0) {
            PREV_FREE(getbp(NEXT_FREE(node))) = getoffset(node);
        }
        NEXT_FREE(header) = getoffset(node);
        PREV_FREE(node) = getoffset(header);
    } else {
        void *rootbp;
        free_blocks_tree = insertAA(free_blocks_tree, node);
        setcolor(free_blocks_tree, BLACK);
    }
}

static void place(void *bp, size_t size)
{
    size_t csize = BLOCK_SIZE(bp);
    if(csize - size >= MINIMAL_BLOCKSIZE) {
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - size, 0, 0));
        PUT(FTRP(bp), PACK(csize - size, 0, 0));
        LEFT_CHILD(bp) = 0;
        RIGHT_CHILD(bp) = 0;
        insert_freenode(bp);
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
        remove_freenode(prev);
        size += BLOCK_SIZE(prev);
        PUT(HDRP(prev), PACK(size, 0, 0));
        PUT(FTRP(prev), PACK(size, 0, 0));
        bp = prev;
    }
    next = NEXT_BLKP(bp);
    if(GET_ALLOC(HDRP(next)) == 0) {
        remove_freenode(next);
        size += BLOCK_SIZE(next);
        PUT(HDRP(bp), PACK(size, 0, 0));
        PUT(FTRP(bp), PACK(size, 0, 0));
    }

    return bp;
}


/*
 * Decrease the level of root.
 * Child nodes may need repainted.
 */
static inline void decrease_level(void *rt, int dir)
{
    setcolor(rt, BLACK);
    if(dir == L) {
        setcolor(getbp(LEFT_CHILD(rt)), RED);
    } else {
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
                decrease_level(root, L^R^dir);
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
    void *oldroot = root;
    freenode_offset *prt_Pointer = NULL;
    while(root != nullnode) {
        if(root == old) {
            LEFT_CHILD(neew) = LEFT_CHILD(old);
            RIGHT_CHILD(neew) = RIGHT_CHILD(old);
            setcolor(neew, BLOCK_COLOR(old));
            if(prt_Pointer == NULL) {
                oldroot = neew;
            } else {
                *prt_Pointer = getoffset(neew);
            }
            return oldroot;
        } else if(LEFTER(old, root)) {
            prt_Pointer = & LEFT_CHILD(root);
            root = getbp(LEFT_CHILD(root));
        } else {
            prt_Pointer = & RIGHT_CHILD(root);
            root = getbp(RIGHT_CHILD(root));
        }
    }

    fprintf(stderr, "Replace: can't find the old node\n");
    return root;
}

/*
 * Helper function for getting the left most node of the search tree
 */
static void* get_leftmost_node( void *root, freenode_offset **prtPointer)
{
    while(LEFT_CHILD(root) != 0) {
        *prtPointer = &LEFT_CHILD(root);
        root = getbp(LEFT_CHILD(root));
    }
    return root;
}

/*
 * 
 */
static void remove_freenode(void* nodebp)
{
    assert(GET_ALLOC(nodebp) == 0);
    if(BLOCK_SIZE(nodebp) <= CACHED_SIZE) {
        void *prev = getbp(PREV_FREE(nodebp));
        void *next = getbp(NEXT_FREE(nodebp));   /* maybe nullnode */
        NEXT_FREE(prev) = getoffset(next);
        if(next != nullnode) {
            PREV_FREE(next) = getoffset(prev);
        }
    } else {
        int tmp;
        if(LEFT_CHILD(nodebp) == 0 && RIGHT_CHILD(nodebp) == 0) {
            free_blocks_tree = remove_aa_leaf(free_blocks_tree, nodebp, &tmp);
            setcolor(free_blocks_tree, BLACK);
        } else {
            freenode_offset *succ_parent = &RIGHT_CHILD(nodebp);
            void *succ = get_leftmost_node(getbp(RIGHT_CHILD(nodebp)), &succ_parent);
            if(RIGHT_CHILD(succ) == 0) {
                if(BLOCK_COLOR(succ) == RED) {
                    *succ_parent = 0;
                } else {
                    free_blocks_tree = remove_aa_leaf(free_blocks_tree, succ, &tmp);
                    setcolor(free_blocks_tree, BLACK);
                }
            } else {
                *succ_parent = RIGHT_CHILD(succ);
                setcolor(getbp(RIGHT_CHILD(succ)), BLACK);
            }
            free_blocks_tree = replace(free_blocks_tree, nodebp, succ);
        }
    }
}

/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;
    size_t extendsize;
    void *bp;

    if(size == 0)
        return NULL;

    if(size <= DSIZE)
        asize = MINIMAL_BLOCKSIZE;
    else
        asize = (size + DSIZE + DSIZE - 1) / DSIZE * DSIZE;

    bp = find_fit(asize);

    if(bp == NULL) {
        /* can't find a fit, allocate more memory and place the block */
        extendsize = asize;
        if(extendsize <= CHUNKSIZE) {
            extendsize = CHUNKSIZE;
        }
        bp = extend_heap(extendsize / WSIZE);
        if(bp == NULL)
            return NULL;
    } else {
        remove_freenode(bp);
    }
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free(void *ptr) {
    if(ptr == NULL)
        return;

    size_t size = BLOCK_SIZE(ptr);
    PUT(HDRP(ptr), PACK(size, 0, 0));
    PUT(FTRP(ptr), PACK(size, 0, 0));
    ptr = coalesce(ptr);
    LEFT_CHILD(ptr) = 0;
    RIGHT_CHILD(ptr) = 0;
    insert_freenode(ptr);
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
