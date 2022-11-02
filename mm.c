/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * This file is a self-implemented malloc operation that was implemented using
 *the segregated list method.
 *
 * Each memory block consisted of three parts, the header, the footer, and the
 *payload area. The header is an 8-byte integer that was used to store the
 *property of its block. Because all the address was 16-bit aligned, the lower 4
 *bits of a header will always be 0. As a result, the lowest bit was used to
 *record the allocation status of its block. If the lowest bit is 1, it means
 *the block is allocated; 0 means the block is not allocated and is currently
 *free. The upper bits were used to record the size of the block, and it can be
 *extracted by using bit operation and mask. The footer shares the same property
 *as the header, and its purpose is to track the size and the allocation status
 *of a previous block. The payload area has two usages. During allocation, the
 *pointer of the payload area was returned to the malloc caller for them to
 *store their data. During free, the payload area was overwritten by two block
 *pointers for a segregated list. Details about the segregated list will be
 *explained later. As a result, the payload area of the block was implemented by
 *using a union. The address of the payload area can be used for storing both
 *user's data and block pointers.
 *
 * An allocated block will look like this:
 * -------------------------
 * |         header        |
 * |xxxxxxxxxxxxxxxxxxx0001|
 * ||      size       |aloc|
 * |-----------------------|
 * |       payload area    |
 * |                       |
 * |                       |
 * |                       |
 * |                       |
 * |                       |
 * |                       |
 * |-----------------------|
 * |         footer        |
 * |xxxxxxxxxxxxxxxxxxx0001|
 * ||      size       |aloc|
 * -------------------------
 *
 * A free block will look like this:
 * -------------------------
 * |         header        |
 * |xxxxxxxxxxxxxxxxxxx0000|
 * ||      size       |aloc|
 * |-----------------------|
 * |          prev         |
 * |                       |
 * |-----------------------|
 * |          next         |
 * |                       |
 * |-----------------------|
 * |                       |
 * |-----------------------|
 * |         footer        |
 * |xxxxxxxxxxxxxxxxxxx0000|
 * ||      size       |aloc|
 * -------------------------
 *
 * The whole malloc and free operation were implemented based on the segregated
 *list method. Each free list is a doubly linked free list. For each free block,
 *its payload area was overwritten by two block pointers, called prev and next.
 * According to its size, each free block will be placed inside its own free
 *list, and all the free lists will be inside a block pointer array. For this
 *implementation, there are a total of 16 free lists, where the first free lists
 *will have the blocks of size of the minimum block size. The 2nd - 15th free
 *lists will have a block size of [2^5 - 2^19], and the 16th free list will have
 *a block size larger than 2^19. After the heap is initialized, all the indexes
 *of the free list array will be set to NULL, indicating that all the free lists
 *are empty. As blocks are allocated and freed, the freed block will first try
 *to coalesce with its previous block and next block on the heap and finally put
 *inside its corresponding free list according to its size. The insertion
 *strategy is LIFO, where the newest free block is always inserted at the head
 *of the free list.
 *
 * The following is a brief description of how malloc and free work are based on
 *this implementation.
 *
 * When the user calls malloc(size), if the heap is not initialized,
 * it will be initialized by writing a prologue footer and an epilogue header
 *for address alignment purposes and then extending the heap by the size of
 *chunksize (4096 bytes). Then the size will be adjusted for spaces for the
 *header and footer and address alignment. According to this adjusted size, the
 *corresponding free list will be located, and searching will be performed
 *inside this free list to see if there is an available free block on the heap
 *for allocation. If a block is found, this block will be attempted to split if
 *it's too big for this allocation. Then this block(split or not) will be marked
 *as allocated by overwriting its header and footer, and finally, its payload
 *area pointer will be returned to the user. If there is no available free block
 *of this size on the heap, the heap will be extended, and the above operation
 *will be performed.
 *
 * When the user calls free(ptr), its corresponding block will be first located
 *from this pointer. This block will be first marked as free and try to coalesce
 *with its previous and next block on the heap. After possible coalescing, this
 *block will be inserted at the head of its corresponding free list for the next
 *possible allocation.
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Taichen Ling <taichenl@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.
 * Hat tip to Stack Overflow poster chqrlie (see
 * https://stackoverflow.com/questions/72647780).
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__)))
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* Basic constants */
#define LISTSIZE 15
#define MINSHIFT 4
typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 4 * wsize;

/**
 * @brief The minimum size that the heap extends when there is no proper free
 * block left. (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * @brief Mask used to isolate the last bit of the header/footer to acquire
 * block allocation status.
 */
static const word_t alloc_mask = 0x1;

/**
 * @brief Mask which the last four bits are 0 and the previous bits are 1 to
 * isolate the size of a block represented by header/footer
 */
static const word_t size_mask = ~(word_t)0xF;
/**
 * @brief A constant used to determine the seg list index
 */

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;
    union Payload {
        struct Pointer {
            struct block *prev;
            struct block *next;
        } pointer;
        char p[0];
    } payload;
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/** @brief Pointer to the seg list, which is represented by an array of block
 * pointers. */
static block_t *list[LISTSIZE];

static void insertFirst(block_t *block);
static void delete (block_t *block);
static void split(block_t *block, size_t asize);
static int findIndex(size_t asize);
bool checkABlock(block_t *block);
bool checkList(void);
/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(&(block->payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(((char *)&(block->payload)) + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - dsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc);
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * This function takes a free block as an argument and checks its previous and
 * next block's allocation status. If its previous block and next block are not
 * allocated, this function will add this block to the appropriate segregated
 * list and return. If either or both of the previous and next block is freed,
 * this function will coalesce this block with the freed block(s) by writing
 * headers and footers and adding this coalesced block to the appropriate
 * segregated list. This function will return a pointer to the final free block.
 * If the input block is the first block on the heap, this function will not
 * check its previous block because there is no block ahead.
 *
 * @param[in] block
 * @return the pointer to the possibly coalesced free block
 */
static block_t *coalesce_block(block_t *block) {
    dbg_assert(!get_alloc(block));
    size_t thisSize = get_size(block);
    // Case 1: The block is the first block on the heap, can't check previous
    // block or seg fault.
    if (block == heap_start) {
        bool nextAlloc = get_alloc(find_next(block));
        if (nextAlloc) {
            insertFirst(block);
            return block;
        }
        block_t *nextBlock = find_next(block);
        size_t nextSize = get_size(nextBlock);
        delete (nextBlock);
        write_block(block, thisSize + nextSize, false);
        insertFirst(block);
        return block;
    }
    // Case 2: This block is not the first block on the heap
    bool prevAlloc = get_alloc(find_prev(block));
    bool nextAlloc = get_alloc(find_next(block));
    // Case 2.1: Previous block and next block are allocated

    if (prevAlloc && nextAlloc) {
        insertFirst(block);
        return block;
        // Case 2.2: Next block is free, coalesce them.
    } else if (prevAlloc && !nextAlloc) {
        block_t *nextBlock = find_next(block);
        size_t nextSize = get_size(nextBlock);
        delete (nextBlock);
        write_block(block, thisSize + nextSize, false);
        insertFirst(block);
        return block;
        // Case 2.3: Previous block is free, coalesce them.
    } else if (!prevAlloc && nextAlloc) {
        block_t *prevBlock = find_prev(block);
        size_t prevSize = get_size(prevBlock);
        delete (prevBlock);
        write_block(prevBlock, thisSize + prevSize, false);
        insertFirst(prevBlock);
        return prevBlock;
        // Case 2.4: Previous and next block are free, coalesce all of them.
    } else if (!prevAlloc && !nextAlloc) {
        block_t *prevBlock = find_prev(block);
        block_t *nextBlock = find_next(block);
        size_t prevSize = get_size(prevBlock);
        size_t nextSize = get_size(nextBlock);
        delete (prevBlock);
        delete (nextBlock);
        write_block(prevBlock, thisSize + prevSize + nextSize, false);
        insertFirst(prevBlock);
        return prevBlock;
    }
    return NULL;
}

/**
 * @brief
 *
 * This function takes an unsigned block size as an argument and tries to extend
 * the heap size by calling "mem_sbrk. " This function will return a pointer to
 * the extended block if successful or return NULL if it fails to extend the
 * heap.
 *
 * @param[in] size
 * @return pointer to the extended block if succeed, NULL if failed.
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief
 *
 * This function takes an unsigned block size as an argument and tries to find
 * the appropriate free block with a size larger than the required size from the
 * seg list. This function will first compute the index of the seg list where
 * the search should start and search the remaining seg list for an appropriate
 * block. If a block is found, the pointer to this block will be returned. If
 * there is no block found, NULL will be returned.
 *
 * @param[in] asize
 * @return A pointer to the free block if found, NULL if not found.
 */
static block_t *find_fit(size_t asize) {
    int index = findIndex(asize);
    for (int i = index; i < LISTSIZE; i++) {
        block_t *block = list[i];
        while (block != NULL) {
            size_t thisSize = get_size(block);
            // Found fit
            if (thisSize >= asize) {
                return block;
            }
            block = block->payload.pointer.next;
        }
    }
    // No fit found
    return NULL;
}
/**
 * @brief
 * This function takes an unsigned block size as an argument and returns the
 * index of the seg list to which a block of this size should belong.
 *
 * @param[in] asize
 * @return correct seg list index
 */
static int findIndex(size_t asize) {
    if (asize == min_block_size) {
        return 0;
    }
    for (int i = 1; i < LISTSIZE - 1; i++) {
        size_t low = 1L << (MINSHIFT + i);
        size_t high = 1L << (MINSHIFT + i + 1);
        if (asize > low && asize <= high) {
            return i;
        }
    }
    return LISTSIZE - 1;
}
/**
 * @brief
 *
 * This function takes a block pointer as an argument and adds this block
 * pointer to the head of the correct seg list.
 *
 * @param[in] block
 * @return
 */

static void insertFirst(block_t *block) {
    size_t blockSize = get_size(block);
    int index = findIndex(blockSize);
    // If the seg list this block should belong to is empty, this block will be
    // assigned as the head
    if (list[index] == NULL) {
        block->payload.pointer.next = NULL;
        list[index] = block;
        return;
    }
    // If the seg list is not empty, set this block as the new head, and the old
    // head as the next.
    block_t *prevHead = list[index];
    block->payload.pointer.next = prevHead;
    prevHead->payload.pointer.prev = block;
    list[index] = block;
}
/**
 * @brief
 *
 * This function takes a block pointer as an argument and delete this block
 * pointer from the corresponding seg list.
 *
 * @param[in] block
 */
static void delete (block_t *block) {
    size_t blockSize = get_size(block);
    int index = findIndex(blockSize);
    // If this block is the head of the seg list
    if (list[index] == block) {
        block_t *nextBlock = block->payload.pointer.next;
        list[index] = nextBlock;
        return;
    }
    // If this block is not the head of the seg list
    block_t *prevBlock = block->payload.pointer.prev;
    block_t *nextBlock = block->payload.pointer.next;
    prevBlock->payload.pointer.next = nextBlock;
    if (nextBlock != NULL) {
        nextBlock->payload.pointer.prev = prevBlock;
    }
}
/**
 * @brief
 *
 * This function takes an allocated block pointer and an unsigned block size as
 * arguments and tries to split the allocated block into two blocks. If the
 * block size is large enough, the input block will be split, and the extra part
 * will be freed and inserted into its corresponding seg list. The precondition
 * and postcondition are that the pointer to the block has to be allocated all
 * the time.
 *
 * @param[in] block
 */
static void split(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    delete (block);
    size_t thisSize = get_size(block);
    if (thisSize - asize >= min_block_size) {
        block_t *nextBlock;
        write_block(block, asize, true);
        nextBlock = find_next(block);
        write_block(nextBlock, thisSize - asize, false);
        insertFirst(nextBlock);
    }
    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * This function will check the blocks on the heap and the blocks inside the seg
 * list. For the heap, the block address alignment, block address inside the
 * boundary, block size, block header-footer consistency, and consecutive free
 * blocks will be checked. For the seg list, the pointer consistency, block
 * address inside the boundary, block number from the heap and the list, and the
 * free block index will be checked.
 *
 * @param[in] line
 * @return true if no errors found, false if any error found.
 */

bool mm_checkheap(int line) {
    block_t *block = heap_start;
    // check prologue
    if ((void *)find_prev_footer(block) < mem_heap_lo()) {
        dbg_printf("No prologue footer!\n");
        return false;
    }
    // check all the blocks
    for (; get_size(block) != 0; block = find_next(block)) {
        if (!checkABlock(block)) {
            dbg_printf("Called Line: %d\n", line);
            return false;
        }
    }
    // check epilogue
    if ((void *)block > mem_heap_hi()) {
        dbg_printf("No Epilogue Header!\n");
        return false;
    }
    // check seg list
    return checkList();
}
bool checkABlock(block_t *block) {
    // Check for address alignment
    if (((size_t) & (block->payload)) % 16 != 0) {
        dbg_printf("payload address %p is not aligned!\n",
                   (void *)&(block->payload));
    }
    // Check block lie within heap boundaries
    if ((void *)block > mem_heap_hi() || (void *)block < mem_heap_lo()) {
        dbg_printf("A block is not lie within heap boundaries\n");
        dbg_printf("This block address is %p\n", (void *)block);
        return false;
    }
    // Check block header and footer
    if (block->header != *(header_to_footer(block))) {
        dbg_printf("A block's header and footer do not match\n");
        dbg_printf("This block address is %p, block header is %ld, block "
                   "footer is %ld\n",
                   (void *)block, block->header, *header_to_footer(block));
        return false;
    }
    if (get_size(block) < min_block_size) {
        dbg_printf("A block's size is less than the min block size\n");
        dbg_printf("This block address is %p, block header is %ld, block "
                   "footer is %ld\n",
                   (void *)block, block->header, *header_to_footer(block));
        return false;
    }
    // Check consecutive free block
    if (block != heap_start && !get_alloc(block) &&
        !get_alloc(find_prev(block))) {
        dbg_printf("Consecutive free blocks in the heap!\n");
        dbg_printf("The two blocks' addresses are %p, %p\n",
                   (void *)(find_prev(block)), (void *)block);
        return false;
    }
    return true;
}

bool checkList(void) {
    // Check if pointers are consistent
    for (int i = 0; i < LISTSIZE; i++) {
        if (list[i] == NULL) {
            continue;
        }
        if (list[i]->payload.pointer.next == NULL) {
            continue;
        }
        block_t *block = list[i];
        block_t *nextBlock = block->payload.pointer.next;
        while (nextBlock != NULL) {
            if (block->payload.pointer.next != nextBlock) {
                dbg_printf("Two consecutive free blocks inside the list do not "
                           "match!\n");
                dbg_printf("Their addresses are %p, %p\n", (void *)block,
                           (void *)nextBlock);
                return false;
            }
            if (block != nextBlock->payload.pointer.prev) {
                dbg_printf("Two consecutive free blocks inside the list do not "
                           "match!\n");
                dbg_printf("Their addresses are %p, %p\n", (void *)block,
                           (void *)nextBlock);
                return false;
            }
            block = block->payload.pointer.next;
            nextBlock = nextBlock->payload.pointer.next;
        }
    }
    // Check if free lists pointers are in bound
    for (int i = 0; i < LISTSIZE; i++) {
        if (list[i] == NULL) {
            continue;
        }
        block_t *block = list[i];
        while (block != NULL) {
            if ((void *)block > mem_heap_hi() ||
                (void *)block < mem_heap_lo()) {
                dbg_printf("A free list is out of bound\n");
                dbg_printf("The address is %p\n", (void *)block);
                return false;
            }
            block = block->payload.pointer.next;
        }
    }
    // Check if the number of free block matches.
    int freeFromHeap = 0;
    int freeFromList = 0;
    for (block_t *block = heap_start; get_size(block) != 0;
         block = find_next(block)) {
        if (!get_alloc(block)) {
            freeFromHeap++;
        }
    }
    for (int i = 0; i < LISTSIZE; i++) {
        if (list[i] == NULL) {
            continue;
        }
        block_t *block = list[i];
        while (block != NULL) {
            freeFromList++;
            block = block->payload.pointer.next;
        }
    }
    if (freeFromHeap != freeFromList) {
        dbg_printf("Free block number in the heap and in the list are not "
                   "consistent\n");
        return false;
    }
    // Check if free blocks are in the right list
    for (int i = 0; i < LISTSIZE; i++) {
        if (list[i] == NULL) {
            continue;
        }
        block_t *block = list[i];
        while (block != NULL) {
            size_t thisSize = get_size(block);
            if (i != findIndex(thisSize)) {
                dbg_printf("A free block is in the wrong seg list\n");
                dbg_printf("This block address is %p \n", (void *)block);
                return false;
            }
            block = block->payload.pointer.next;
        }
    }
    return true;
}

/**
 * @brief
 *
 * This function takes no arguments and initializes the heap by first writing a
 * prologue footer and an epilogue header on the heap. It then extends the heap
 * by chunksize by calling the "extend_heap" function. This function also
 * initializes the seg list array by setting all the list heads point to NULL.
 * If the heap is initialized successfully, this function will return true.
 * Otherwise, return false.
 *
 * @return True if initialization is successful, false if not.
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }
    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(0, true); // Heap epilogue (block header)
    // Heap start at the end of the tail, the epilogue for now
    heap_start = (block_t *)&(start[1]);
    // Initialize the seg list array
    for (int i = 0; i < LISTSIZE; i++) {
        list[i] = NULL;
    }
    // Extend the empty heap with a free block of chunksize bytes
    block_t *extendFreeBlock = extend_heap(chunksize);
    if (extendFreeBlock == NULL) {
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * This function will take a payload size as an argument and tries to allocate
 proper space on the heap for this payload.
 * If the allocation process fails, this function will return NULL.
 * If there is a free block on the heap that has the proper size for allocation,
 this function will mark this block as allocated and return a pointer to its
 payload area.
 * If there is no such a block, this function will extend the heap and tries to
 split the extended block.
 * It will return a pointer to the extended block's payload area if successful
 and NULL if the heap extension fails.

 * @param[in] size
 * @return pointer to block's payload area if successful, NULL if failed.
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;
    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }
    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }
    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);
    // Search the free list for a fit
    block = find_fit(asize);

    // If a fit is found inside the free list
    if (block != NULL) {
        dbg_assert(!get_alloc(block));
        size_t thisSize = get_size(block);
        write_block(block, thisSize, true);
        split(block, asize);
        bp = header_to_payload(block);
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }
    // No fit is found inside the free list, request extra space
    extendsize = max(asize, chunksize);
    block = extend_heap(extendsize);
    if (block == NULL) {
        return bp;
    }
    size_t extraSize = get_size(block);
    write_block(block, extraSize, true);
    split(block, asize);
    bp = header_to_payload(block);
    return bp;
}

/**
 * @brief
 *
 * This function takes an allocated block's payload area pointer and frees its
 * corresponding block. This function will first find the pointer to the block
 * from the pointer to the payload area, and tries to coalesce this freed block
 * with its previous and next block. Finally, insert the block to the proper seg
 * list according to its size. To use this function, the payload pointer passed
 * has to be allocated.
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);

    // Try to coalesce the block with its neighbors
    coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * This function takes an allocated payload area pointer and an unsigned payload
 size as arguments and tries to resize this payload area.
 * If the input new size is 0 or realloc fails, this function will return NULL.
 * If the input payload pointer is NULL, this function will just allocate an
 area according to the input size.
 * Otherwise, this function will allocate a new block according to the input
 size, copy all the memory to the new block, and free the old block.
 * A pointer to the payload area of the new block will be returned if the
 process is successful.

 * @param[in] ptr
 * @param[in] size
 * @return A pointer pointing to the payload area of the new block if
 successful, NULL if failed.
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * This function takes the number of elements and element size as arguments and
 * tries to allocate a block for the total space needed. This function also sets
 * the allocated memory to zero. This function will return a pointer to the
 * allocated block's payload area if successful and return NULL if failed.
 *
 * @param[in] elements
 * @param[in] size
 * @return pointer to allocated block's payload area if successful, NULL if
 * failed.
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
