/*
 * mm.c
 * Yang Zhixuan 1300012785@pku.edu.cn
 *
 * A (fast) best-fit malloc/free implementation.
 *
 * Small size free blocks(size smaller than CACHED_SIZE), which are frequently
 * referenced, are organized as doubly linked lists(a list corresponds to a block
 * size). Other blocks are maintained as an AA-tree (a variant of red-black tree)
 * indexed by their block size.
 *
 * For every malloc request, we allocate the best fit block. If there are no
 * free block available, call sbrk() for more heap space.
 *
 * Two adjacent free blocks are coalesced immediately whenever possible.
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

/* forward declarations and type definitions */
static void *coalesce(void *bp);
static void remove_freeblock(void* node);
typedef unsigned int offset;

/* helper macros for manipulating block pointers */
#define WSIZE 4
#define DSIZE 8
#define MINIMAL_BLOCKSIZE 16
#define CACHED_SIZE 64
#define CACHED_CLASSES ((CACHED_SIZE - MINIMAL_BLOCKSIZE) / DSIZE + 1)
#define CHUNKSIZE ((size_t) 96)
#define PACK(size, color, alloc) ((size) | (alloc) | ((color) << 1))
#define PACK3(size, used, color, alloc) ((size) | (alloc) | ((color) << 1) | ((used) << 2))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~7)
#define GET_ALLOC(p) (GET(p) & 1)
#define GET_COLOR(p) ((GET(p) >> 1) & 1)
#define GET_PREVUSED(p) ((GET(p) >> 2) & 1)
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define BLOCK_PREVUSED(bp) (GET_PREVUSED(HDRP(bp)))
#define BLOCK_SIZE(bp) (GET_SIZE(HDRP(bp)))
#define BLOCK_ALLOC(bp) (GET_ALLOC(HDRP(bp)))
#define BLOCK_COLOR(bp) (GET_COLOR(HDRP(bp)))
#define LEFT_CHILD(bp) (GET(bp))
#define RIGHT_CHILD(bp) (GET((char*)(bp) + WSIZE))
#define NEXT_FREE(bp) (GET(bp))
#define PREV_FREE(bp) (GET((char*)(bp) + WSIZE))
#define CHILD(bp, ind) (GET((char*)(bp) + (ind) * WSIZE))
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(HDRP(bp) - WSIZE))
#define L (0)
#define R (1)
#define BLACK (0)
#define RED (1)
inline static void setcolor(void *bp, int color)
{
     *HDRP(bp) = ((*HDRP(bp)) & (~2)) | (color << 1);
}

inline static void setprevused(void *bp, int used)
{
     *HDRP(bp) = ((*HDRP(bp)) & (~4)) | (used << 2);
}

/* pointer to the first (by address order) block (the prologue block) of the heap */
static void* heap_start;
static void* nullnode;
static void* lists_header;
static void* first_block;
static void* epilogue;
/* root node of the free block binary search tree */
static void* free_blocks_tree;

/*
 * Block pointers are stored as 32-bit offset to save space.
 */
static inline void* getbp(offset off)
{
    return nullnode + off;
}

static inline offset getoffset(void* bp)
{
    return (offset) (bp - nullnode);
}

/*
 * Get the header of the list corresponding to the size.
 */
static inline void* getheader(int size)
{
#ifdef DEBUG
    assert(size % DSIZE == 0);
#endif
    return lists_header + (size - MINIMAL_BLOCKSIZE) / (DSIZE / WSIZE);
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) 
{
    int i, a_classes = CACHED_CLASSES;

    /* make sure CACHED_CLASSES is odd to satisfy the align requirement */
    if(a_classes % 2 == 0)
        a_classes += 1;

    if((heap_start = mem_sbrk( (a_classes + 4 + 1) * WSIZE)) == (void *) -1) {
        return -1;
    }


    /* the red-black tree nullnode */
    free_blocks_tree = nullnode = heap_start + WSIZE;
    PUT(HDRP(nullnode),  PACK3(4 * WSIZE, 1, BLACK, 1));
    LEFT_CHILD(nullnode) = 0;
    RIGHT_CHILD(nullnode) = 0;
    PUT(FTRP(nullnode), PACK(4 * WSIZE, BLACK, 1));

    /* cached lists headers */
    lists_header = heap_start + 4 * WSIZE;
    for(i = 0; i < a_classes; i++) {
        PUT(lists_header + i * WSIZE, 0);
    }

    first_block = epilogue = heap_start + (4 + a_classes + 1) * WSIZE;
    PUT(HDRP(epilogue), PACK3(0, 1, 0, 1));

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

    int prev_used = GET_PREVUSED(HDRP(bp));
    PUT(HDRP(bp), PACK3(size, prev_used, 0, 0));
    PUT(FTRP(bp), PACK(size, 0, 0));
    epilogue = NEXT_BLKP(bp);
    PUT(HDRP(epilogue), PACK(0, 0, 1));

    return coalesce(bp);
}


/*
 * find_fit: find the best fit free block.
 */
static void* find_fit(size_t size)
{

    if(size <= CACHED_SIZE) {
        void *header = getheader(size);
        if(NEXT_FREE(header) != 0) {
            return getbp(NEXT_FREE(header));
        }
        return find_fit(size + DSIZE);
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
                }
                bp = getbp(LEFT_CHILD(bp));
            } else {
                bp = getbp(RIGHT_CHILD(bp));
            }
        }
        return best_fit_node;
    }
}



/***************************** AA tree functions ******************************/
/******************************************************************************/

/*
 * Determine the order of blocks in the tree.
 * Compare the address if the blocks have the same size so that different blocks
 * have different keys.
 */
inline static int lefter(void *b1, void *b2)
{
    return (BLOCK_SIZE(b1) < BLOCK_SIZE(b2))
        || (BLOCK_SIZE(b1) == BLOCK_SIZE(b2) && (b1) < (b2));
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
 * Skew: AA-tree maintaince operation. 
 * See [http://user.it.uu.se/~arnea/ps/simp.pdf] for detail.
 * Notice that only 1-bit color information is stored here so that maintenance
 * routines are some what more complex than their ordinary forms.
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
 * Split: AA-tree maintaince operation
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
 * Decrease_level: Decrease the level of root. Child nodes may need repainted.
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
 * Insert nodep into the AA tree and maintain the AA properties.
 */
static void* insert_aa_node(void* bp, void* nodep)
{
    if(bp == nullnode) {
        /* set two children point to the nullnode */
        *(long*)nodep = 0;
        setcolor(nodep, RED);
        return nodep;
    }
    if(lefter(nodep, bp)) {
        LEFT_CHILD(bp) = getoffset(insert_aa_node(getbp(LEFT_CHILD(bp)), nodep));
    } else {
        RIGHT_CHILD(bp) = getoffset(insert_aa_node(getbp(RIGHT_CHILD(bp)), nodep));
    }
    bp = skew(bp);
    bp = split(bp);
    return bp;
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
        dir = lefter(node, root) ? L : R;
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
static void* replace_node(void *root, void *old, void *neew)
{
    void *oldroot = root;
    offset *prt_Pointer = NULL;
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
        } else if(lefter(old, root)) {
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
static void* get_leftmost_node( void *root, offset **prtPointer)
{
    while(LEFT_CHILD(root) != 0) {
        *prtPointer = &LEFT_CHILD(root);
        root = getbp(LEFT_CHILD(root));
    }
    return root;
}
/******************************************************************************/


/*
 * add_freeblock
 */
static void add_freeblock(void *node)
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
        free_blocks_tree = insert_aa_node(free_blocks_tree, node);
        setcolor(free_blocks_tree, BLACK);
    }
}

/*
 * place: place a block in the block pointed by bp.
 * If the remaining space is large enough, using the remaining
 * space as a free block.
 */
static void place(void *bp, size_t size)
{
    size_t csize = BLOCK_SIZE(bp);
    int prev_used = GET_PREVUSED(HDRP(bp));
    if(csize - size >= MINIMAL_BLOCKSIZE) {
        PUT(HDRP(bp), PACK3(size, prev_used, 0, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK3(csize - size, 1, 0, 0));
        PUT(FTRP(bp), PACK(csize - size, 0, 0));
        LEFT_CHILD(bp) = 0;
        RIGHT_CHILD(bp) = 0;
        add_freeblock(bp);
    } else {
        PUT(HDRP(bp), PACK3(csize, prev_used, 0, 1));
        setprevused(NEXT_BLKP(bp), 1);
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
    if(GET_PREVUSED(HDRP(bp)) == 0) {
        prev = PREV_BLKP(bp);
        remove_freeblock(prev);
        size += BLOCK_SIZE(prev);
        int prev_used = GET_PREVUSED(HDRP(prev));
        PUT(HDRP(prev), PACK3(size, prev_used, 0, 0));
        PUT(FTRP(prev), PACK(size, 0, 0));
        bp = prev;
    }
    next = NEXT_BLKP(bp);
    if(GET_ALLOC(HDRP(next)) == 0) {
        remove_freeblock(next);
        size += BLOCK_SIZE(next);
        int prev_used = GET_PREVUSED(HDRP(bp));
        PUT(HDRP(bp), PACK3(size, prev_used, 0, 0));
        PUT(FTRP(bp), PACK(size, 0, 0));
    }
    return bp;
}



/*
 * remove_freeblock
 */
static void remove_freeblock(void* nodebp)
{
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
            offset *succ_parent = &RIGHT_CHILD(nodebp);
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
            free_blocks_tree = replace_node(free_blocks_tree, nodebp, succ);
        }
    }
}

/*
 * malloc
 */
void *malloc (size_t size) 
{
    size_t asize;
    size_t extendsize;
    void *bp;

    if(size == 0)
        return NULL;

    asize = (size + WSIZE + DSIZE - 1) / DSIZE * DSIZE;
    if(asize < MINIMAL_BLOCKSIZE)
        asize = MINIMAL_BLOCKSIZE;

    bp = find_fit(asize);

    if(bp == NULL) {
        /* can't find a fit, allocate more memory and place the block */
        extendsize = asize;
        if(GET_PREVUSED(HDRP(epilogue)) == 0) {
              extendsize -= BLOCK_SIZE(PREV_BLKP(epilogue));
        }
        if(extendsize <= CHUNKSIZE) {
            extendsize = CHUNKSIZE;
        }
        bp = extend_heap(extendsize / WSIZE);
        if(bp == NULL)
            return NULL;
    } else {
        remove_freeblock(bp);
    }
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free(void *ptr) 
{
    if(ptr == NULL)
        return;

    size_t size = BLOCK_SIZE(ptr);
    int prev_used = GET_PREVUSED(HDRP(ptr));
    PUT(HDRP(ptr), PACK3(size, prev_used,  0, 0));
    PUT(FTRP(ptr), PACK(size, 0, 0));
    setprevused(NEXT_BLKP(ptr), 0);

    ptr = coalesce(ptr);
    LEFT_CHILD(ptr) = 0;
    RIGHT_CHILD(ptr) = 0;
    add_freeblock(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size)
{
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
    oldsize = BLOCK_SIZE(oldptr) - WSIZE;
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
void *calloc (size_t nmemb, size_t size) 
{
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Functions for testing. See the comment of mm_checkheap() for details.
 *
 */
static int free_blocks_in_implicit_list;
static int free_blocks_in_lists_tree;

void check_implicit_list()
{
    assert(mem_heap_hi() + 1 == epilogue);
    void *block = first_block;
    while(block != epilogue) {
        assert(BLOCK_SIZE(block) % DSIZE == 0);
        if(BLOCK_ALLOC(block) == 1) {
            assert(BLOCK_PREVUSED(NEXT_BLKP(block)) == 1);
        } else {
            free_blocks_in_implicit_list += 1;
            assert(BLOCK_PREVUSED(NEXT_BLKP(block)) == 0);
            assert(BLOCK_ALLOC(NEXT_BLKP(block)) == 1);
            assert(GET_SIZE(FTRP(block)) == BLOCK_SIZE(block));
            assert(GET_ALLOC(FTRP(block)) == BLOCK_ALLOC(block));
        }
        block = NEXT_BLKP(block);
    }
    assert(BLOCK_SIZE(block) == 0);
    assert(BLOCK_ALLOC(block) == 1);
}

void check_freeblocks_tree(void *node)
{
    if(node == nullnode)
        return;
    free_blocks_in_lists_tree += 1;
    assert(BLOCK_ALLOC(node) == 0);
    check_freeblocks_tree(getbp(LEFT_CHILD(node)));
    check_freeblocks_tree(getbp(RIGHT_CHILD(node)));
}

void check_freeblocks()
{
    int size;
    for(size = MINIMAL_BLOCKSIZE; size <= CACHED_SIZE; size+=DSIZE) {
        void *node = getheader(size);
        node = getbp(NEXT_FREE(node));
        while(node != nullnode) {
            free_blocks_in_lists_tree += 1;
            assert(BLOCK_SIZE(node) == size);
            assert(BLOCK_ALLOC(node) == 0);
            node = getbp(NEXT_FREE(node));
        }
    }
    check_freeblocks_tree(free_blocks_tree);
    assert(free_blocks_in_implicit_list == free_blocks_in_lists_tree);
}

static void* predecessor_in_tree;
void check_aa_ordered(void *node)
{
    if(node == nullnode)
        return;
    check_aa_ordered(getbp(LEFT_CHILD(node)));
    assert(lefter(predecessor_in_tree, node));
    predecessor_in_tree = node;
    check_aa_ordered(getbp(RIGHT_CHILD(node)));

}

int black_height(void *bp)
{
    if(bp == nullnode)
        return 0;
    return black_height(getbp(LEFT_CHILD(bp))) 
        + (BLOCK_COLOR(bp) == BLACK);
}

void check_aa_properties(void *node)
{
    if(node == nullnode) {
        assert(BLOCK_COLOR(node) == BLACK);
        return;
    }

    void *lc = getbp(LEFT_CHILD(node));
    void *rc = getbp(RIGHT_CHILD(node));
    check_aa_properties(lc);
    check_aa_properties(rc);
    if(BLOCK_COLOR(node) == RED) {
        assert(BLOCK_COLOR(lc) == BLACK);
        assert(BLOCK_COLOR(rc) == BLACK);
    } else {
        assert(BLOCK_COLOR(lc) == BLACK);
    }
    assert(black_height(lc) == black_height(rc));
}

void check_tree_properties()
{
    predecessor_in_tree = nullnode;
    check_aa_ordered(free_blocks_tree);
    check_aa_properties(free_blocks_tree);
}

/*
 * mm_checkheap: check the consistency of the heap.
 * Checked invariants including:
 * 1. (verbose >= 1) All blocks form an implicit list terminated by the epilogue.
 * 2. (verbose >= 1) PREV_USED tags are correctly maintained in the implicit list.
 * 3. (verbose >= 2) Every block in the segregated lists or the tree is a free block.
 * 4. (verbose >= 2) The number of free blocks in the implicit list matches with
 *                   the number of blocks in the lists or the tree.
 * 5. (verbose >= 2) The size of every block in a list equals to the size corresponded to the list.
 * 6. (verbose >= 3) The AA properties hold for the AA tree.
 */
void mm_checkheap(int verbose) 
{
    free_blocks_in_implicit_list = free_blocks_in_lists_tree = 0;
    if(verbose >= 1) {
        check_implicit_list();
    }
    if(verbose >= 2) {
        check_freeblocks();
    }
    if(verbose >= 3) {
        check_tree_properties();
    }
}
