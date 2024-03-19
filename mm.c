/*
 * mm.c
 *
 * Name: [Stanley Wang & Riggie Lin]
 * 
 * This project we used Explicit List with footer optimization; 
 * 
 * We created a block structure that contains the size of header, next_node, and prev_node. 
 * It makes it a lot easier to navigate through the heap. For debugging purposes, we had a lot of print statements, which could
 * be seen throughout the GitHub history. For the heap checker, we used it mainly to track our free list, to see if everything 
 * is in place within the heap. 
 * 
 * Our general vision for the project is that we made a heap with padding (dummy header and dummy footer),
 * then we will initialize a payload on the free space with a header and footer. Our block structure will always be pointed at
 * the header so that we can modify the header value, previous node address, and next node address. Our free block will always
 * have a header and a footer, but when allocating it, the footer should be overwritten. This is also a part of footer optimization,
 * the second bit of header should be the indicator of whether previous block is allocated or free. The first bit is used for the 
 * current block, indicating if the current block is allocated or free.
 * 
 * For free and coalescing, we first free the given block, then we check for coalescing. Using the second bit of current block and 
 * first bit of the next block, we can check if either of these two blocks are free. If they are free, we get their sizes, remove them
 * from the free list, and add it to the total size, which includes the block we just freed. At the end, we will add a block to the free list,
 * which is the size of the total size that was collected.
 * 
 * NOTE TO GRADER: <IMPORTANT!>
 *  If you are testing the "Heap Checker", its gonna be slow because it has to loop through the entire heap just to make sure there is
 *  no error!
 *  
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

static void *find_fit(size_t);

// Block structure: header size, next node address, prev node address
typedef struct Block {
    size_t size_node;
    struct Block* next_node;
    struct Block* prev_node;
} mem;

// Free block list
struct Block *first;

static void addblock(mem *p, size_t size);
void coalesce(mem* bp);


/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}


/*
 * Initialize: Returns false on error, true on success.
 */
bool mm_init(void)
{
    /* IMPLEMENT THIS */
    void* value = mem_sbrk(16+4096); 

    size_t* end = mem_heap_hi()+1;

    // Set freespace header block
    first = value;
    if (value == (void *)-1) {
        return false;
    }
    *((size_t*) value)= 1;
    mem *mod = value+ 8;
    mod -> size_node = 4096; // Set header size
    mod -> size_node ^= 2; // For dummy footer
    mod -> next_node = NULL; // Set next node
    mod -> prev_node = NULL; // Set prev node
    first = mod; // Set freespace header block to the first free block
    *(end-2)= 4096; // Set freespace footer
    *(end-1)=1; // Set dummy header to be allocated
    return true;
    
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    /* IMPLEMENT THIS */
    size_t* new_heap_end;
    size_t n_size;
    
    if (size == 0) {
    	return NULL;
    }

    // Align with header
    n_size = align(size+8); 

    // Corner case: If aligned less than 32
    if (n_size < 32) {
        n_size = 32;
    }
    
    // Finds the block that "first fits" the size
    mem *pt = find_fit(n_size);
    if (pt!= NULL) {        
        size_t full_size = (pt -> size_node) & (~3); // Gets the full size of the block from find fit
        size_t cut_size = full_size - n_size; // Checks whether or not we need to split the block
        
        // Check for edge condition, if free space is same size or too small
        if ((cut_size <= 32) || (full_size == n_size)) {
            // Updates header (case 1: if prev block is allocated, case 2: if prev block is not allocated)
            if (((pt->size_node) & 2) != 0) {
                pt -> size_node = full_size | 1; // Case 1
                pt -> size_node ^= 2;
            } else {
                pt -> size_node = full_size | 1; // Case 2
            }

            // Updates next block second bit
            *((size_t*)pt+(size_t)(full_size/(sizeof(size_t)))) ^= 2; 

            // Deletes free block from free list
            if ((pt->prev_node) != NULL) {
                (pt -> prev_node) -> next_node = pt -> next_node;
            } else {
                first = pt -> next_node;
            } 

            if ((pt -> next_node)!= NULL) {
                (pt -> next_node) -> prev_node = pt -> prev_node;
            }

            return (size_t*)pt +1;
        }
        
        // Add block, and split if too large
        addblock(pt,n_size); 
        
        return (size_t*)pt + 1 + (size_t)((cut_size/(sizeof(size_t))));
    } else {
        // Extend if does not fit size
        void* newblk = mem_sbrk(n_size);
        if (newblk == (void *)-1) {
            return NULL;
        }

        new_heap_end = mem_heap_hi()+1;
        // Change the old dummy header to new header of the extended space
        mem* extend_blk = (mem*)((char*)newblk-8);

        // Updates header (case 1: if prev block is allocated, case 2: if prev block is not allocated)
        if (((extend_blk->size_node) & 2) != 0) {
            extend_blk -> size_node = n_size | 1; // Case 1
            extend_blk -> size_node ^= 2;
        } else {
            extend_blk -> size_node = n_size | 1; // Case 2
        }
 
        *(new_heap_end-1)=3; // Set new dummy header

        return newblk;
    }
    return NULL;
}

/*
 * addblock: Adds a block and also splits it
 */
static void addblock(mem *p, size_t size)
{
    size_t block_size = (p -> size_node) & (~3);
    size_t extra_size = block_size - size;

    // Updates header (case 1: if prev block is allocated, case 2: if prev block is not allocated)
    if (((p->size_node) & 2) != 0) {
        p -> size_node = extra_size;  // Case 1
        p -> size_node ^= 2;
    } else {
        p -> size_node = extra_size;  // Case 2
    }

    // Changes free block footer
    *((size_t*)p+(size_t)(extra_size/(sizeof(size_t)))-1) = extra_size;

    // Changes allocated block header and the next block's previous block indicator
    *((size_t*)p+(size_t)(extra_size/(sizeof(size_t)))) = size | 1;
    *((size_t*)p+(size_t)(block_size/(sizeof(size_t)))) ^= 2;

}

/*
 * find_fit: Finds a location that fits after passing a size
 */
static void *find_fit(size_t size) 
{
    // Loop begins at the start of free list
    mem *p = first;

    // Find valid free space
    while(p) {
        
        if (((p -> size_node) & (~3)) >= size) {
            return p;
        } 

        p = p -> next_node;
    }
    return NULL;
}

/*
 * free
 */
void free(void* ptr)
{
    /* IMPLEMENT THIS */
   if (ptr == NULL) {
      return;
    }
    
    // Get header block of ptr and set bit value as not allocated
    mem* freeing = (mem*) ((char*)(ptr)-8);
    freeing->size_node = (freeing->size_node) & -2;

    // Set free block footer
    *((size_t*)freeing + (size_t)(((freeing->size_node) & (~3))/sizeof(size_t))-1) = (freeing -> size_node) & (~3);

    // Update next block's current block information
    *((size_t*)freeing + (size_t)(((freeing->size_node) & (~3))/sizeof(size_t))) = *((size_t*)freeing + (size_t)(((freeing->size_node) & (~3))/sizeof(size_t))) & (~2);
    
    // Add block to front of free list
    freeing -> prev_node = NULL;
    freeing -> next_node = first;
    if (first != NULL) {
        first -> prev_node = freeing;
    }
    first = freeing;

    coalesce(freeing); // Joins and merges free block
    
}

/*
 * coalesce: Joins and merges free block
 */
void coalesce(mem *bp)
{ 
    bool left_available = 0; // Indicator for if previous block is available 
    size_t current_size = (bp->size_node) & (~3);
    size_t new_size = current_size; // Keep track of the total size need to be added
    
    // Checks header for previous block availability
    if (((bp -> size_node) & 2) == 0) {
        left_available = 1;
    }
    size_t* prev_block = (size_t*)bp - 1; // Goes to the footer of previous block
    size_t pre_size = (*prev_block & ~3); // Gets size from footer
    size_t* prevo = ((size_t*)bp - (size_t)(pre_size/sizeof(size_t))); 	// Header block of previous block
    size_t* next_block = (size_t*)bp + (size_t)(((bp->size_node) & (~3))/sizeof(size_t)); // Gets address of next block
    mem* nblock = bp;

    // If the previous block is free
    if ((prevo >= (size_t*)(mem_heap_lo())+1) && (prevo < (size_t*)(mem_heap_hi()-7)) && (left_available == 1)){
        
        // Gets previous block
        mem* prevs = (mem*) prevo;

        // Removes the old free block
        if ((prevs->prev_node) != NULL) {
            (prevs -> prev_node) -> next_node = prevs -> next_node;
        } else {
            first = prevs -> next_node;
        } 

        if ((prevs -> next_node)!= NULL) {
            (prevs -> next_node) -> prev_node = prevs -> prev_node;
        }

        // Adds left block size to the total size
        new_size = new_size  + ((prevs->size_node) & (~3)) ;
        nblock = prevs;
    }

    if ((next_block >= (size_t*)mem_heap_lo()+1) && (next_block < (size_t*)(mem_heap_hi()-7)) && (*next_block & 1) != 1){
        // Gets the next block
        mem* nexts = (mem*) next_block;
        
        if ((nexts->prev_node) != NULL) {
            (nexts -> prev_node) -> next_node = nexts -> next_node;
        } else {
            first = nexts -> next_node;
        } 
       
        if ((nexts -> next_node)!= NULL) {
            (nexts -> next_node) -> prev_node = nexts -> prev_node;
        }

        // Adds the right block size to the total size
        new_size = new_size + ((nexts->size_node) & (~3));
    }

    // If there are neighboring free blocks
    if (current_size != new_size) {
        // Removes the old block we just freed from free list
        if ((bp->prev_node) != NULL) {
            (bp -> prev_node) -> next_node = bp -> next_node;
        } else {
            first = bp -> next_node;
        } 

        if ((bp -> next_node)!= NULL) {
            (bp -> next_node) -> prev_node = bp -> prev_node;
        } 

        // Changes the block size to the merged block size
        nblock -> size_node = new_size;
        nblock -> size_node ^= 2;
        *((size_t*) nblock + (size_t)(new_size/sizeof(size_t))-1) = new_size;

        // Adds new block
        nblock -> prev_node = NULL;
        nblock -> next_node = first;
        if (first != NULL) {
            first -> prev_node = nblock;
        }
        first = nblock;
    } 
}


/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    /* IMPLEMENT THIS */
    size_t n_size = size;
    if (oldptr == NULL) {
        return malloc(n_size); 
    }
    
    if (size == 0) {
        free(oldptr);
        return NULL;
    }

    // Malloc a new block
    void *newptr = malloc(n_size); 
    if (newptr != NULL) {
        
        if (newptr == NULL) { 
	        return NULL;
        }

        // Creates a struct at header of the old block
        mem *old_block = (mem*) ((char*)(oldptr)-8); 

        size_t oldptr_size = (old_block ->size_node) & (~3);

        // If the given size is greater than the old block's size
        // Set the given to the old block's size
        if (n_size > oldptr_size) {
	        n_size = oldptr_size;
        }

        // Copies data from old block to the new block
        memcpy(newptr, oldptr, n_size); 
    }
    
    // Frees the old block
    free(oldptr);
    return newptr;
}


/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    /* IMPLEMENT THIS */

    // Check for free list free blocks
    mem* checkssss = first;
    while (checkssss != NULL) {
        size_t* header_loc = (size_t*) checkssss;
        size_t header_size = *header_loc & (~3);
        size_t* footer_loc = ((size_t*)checkssss + (size_t)(header_size/sizeof(size_t))-1);
        size_t footer_size = *footer_loc & (~3);

        // Check if heder is inbound
        if ((header_loc < (size_t*) mem_heap_lo() +1) || (header_loc >= (size_t*) ((char*) mem_heap_hi() -7))) {
            dbg_printf("HEADER OUT OF BOUND");
        }

        // Check if footer is out of bound
        if ((footer_loc < (size_t*) mem_heap_lo() +1) || (footer_loc >= (size_t*) ((char*) mem_heap_hi() -7))) {
            dbg_printf("FOOTER OUT OF BOUND");
        }

        // Check if all free block in free list are freed
        if ((*header_loc & 1) == 1 || (*footer_loc & 1) == 1) {
            dbg_printf("In free heap header and footer are not free in the location of: %p\n", checkssss);
        }

        // Check if header and footer are different sizes
        if (header_size != footer_size) {
            dbg_printf("header and footer size are different size_t: %p\n", checkssss);
        }

        // Check for contiguous blocks
        if ((*header_loc & 2) == 0) {
            dbg_printf("block escaped coalesce before ptr: %p\n",checkssss);
        }

        // Implicitly check through if all free blocks are within free list
        size_t* begin = ((size_t*) mem_heap_lo() + 1);
        while (begin < (size_t*) ((char*) mem_heap_hi() -7)) {
            // Check if a block is free
            if ((( ((mem*) begin) -> size_node) & 1) != 1) {
                // Within free list status (0 = Not in , 1 = In)
                bool within = 0;
                // Loops through free list
                mem* freeloop = first;
                while (freeloop != NULL) {
                    if ((begin) == ((size_t*) freeloop)) {
                        within = 1;
                    }
                    freeloop = freeloop->next_node;
                }
                
                // Prints address of the free block that is not within the free list
                if (within != 1) {
                    dbg_printf("Free block not in free list at: %p\n", begin);
                }

            }

            begin = begin + (size_t)(((((mem*) begin)->size_node) & (~3))/sizeof(size_t));
        }

        checkssss = checkssss->next_node;
    }
#endif /* DEBUG */
    return true;
}