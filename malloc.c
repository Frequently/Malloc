/*
 * Simple, 32-bit and 64-bit clean allocator based on an Segregated free lists,
 * modified first fit, and boundary tag coalescing.
 * Here ten seperate segregated free list are defined which seprate free blocks according to their sizes into these lists.
 * However there is only one heap as per requirement of assignment.
 * Blocks are aligned to double-word boundaries.This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "RNH",
    /* First member's full name */
    "Rajan Pipaliya",
    /* First member's email address */
    "201401163@daiict.ac.in",
    /* Second member's full name (leave blank if none) */
    "Harshal Shah",
    /* Second member's email address (leave blank if none) */
    "201401165@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE       sizeof(void *)         /* word size (bytes) */
#define DSIZE       (2 * WSIZE)            /* doubleword size (bytes) */
#define CHUNKSIZE   (1<<12)      /* initial heap size (bytes) */

#define MAX(x,y) ((x) > (y)?(x) :(y))
#define true 1
#define false 0
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(uintptr_t *)(p))
#define PUT(p,val)      (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)    (GET(p) & 0x1)


/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
void* heaplistp = NULL;
size_t TOTAL_LISTS = 12;
void* free_listp[12];

/*Structure of free blocks: [header][next][prev][][][]...[][footer]
  Thus the bp points to the prevoius free block in the list         */

//get explicit free list previous and next blocks
#define getNext(bp) GET(bp)
#define getPrev(bp) GET((char *)(bp)+WSIZE) //(char*)(bp) casting necessary for raw address manipulation (the bits of the address)

//set explicit free list previous and next blocks
#define setNext(bp, next) PUT(bp, next)
#define setPrev(bp, prev) PUT((char *)(bp)+WSIZE, prev)

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
void place(void *bp, size_t asize ,bool Isheapextended);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);

/* function which are implemented written by us  */
int getlist_index(size_t size);
void add_freelist (void *bp);
void delete_freelist (void *bp);


/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
     Initialises the listpinters to NULL
 */
int mm_init(void)
{
    /* Create the initial empty heap. */
    if ((heaplistp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heaplistp, 0);                         /* Alignment padding */
    PUT(heaplistp + (1 * WSIZE), PACK(DSIZE, 1));   /* Prologue header */ 
    PUT(heaplistp + (2 * WSIZE), PACK(DSIZE, 1));   /* Prologue footer  */
    PUT(heaplistp + (3 * WSIZE), PACK(0, 1));    /* Epilogue header */
    heaplistp += (2 * WSIZE);

    // Intializing the Segregated free lists
    int i;

    for (i = 0; i < TOTAL_LISTS; i++)
        free_listp[i] = NULL;

    return 0;
}

/* add_freelist the free block pointer to appropriate segregated free list */
void add_freelist (void *bp){
    int index = getlist_index(GET_SIZE(HDRP(bp)));
    setNext(bp, free_listp[index]);
    setPrev(bp, NULL);  

    if (free_listp[index] != NULL)
            setPrev(free_listp[index], bp); 
          
    free_listp[index] = bp;

    return;
}
/*delete_freelist Remove the allocated block pointer from its assigned segregated free list */
void delete_freelist (void *bp){
    int index = getlist_index(GET_SIZE(HDRP(bp)));
    if (getPrev(bp) != NULL)
        setNext(getPrev(bp),getNext(bp));

    else 
	free_listp[index] = getNext(bp);

    if (getNext(bp) != NULL)
        setPrev(getNext(bp), getPrev(bp));

    return;
}

/*
   Some  of the helper routines that are used are:
   getlist_index ,find_fit ,add_freelist ,delete_freelist ,extend_heap
*/
/* getlist_index gets the index of the list that satisfies the size classification */
int getlist_index(size_t size) {
    if (size>16384)return 11;
    else if (size>8192)return 10;
    else if (size>4096)return 9;
    else if (size>2048)return 8;
    else if (size>1024)return 7;
    else if (size>512)return 6;
    else if (size>256)return 5;
    else if (size>128)return 4;
    else if (size>64)return 3;
    else if(size>32)return 2;	
    else if(size>16)return 1;
    else return 0;
}


/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignments */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ( (bp = mem_sbrk(size)) == (void *)-1 )
        return NULL;

	/* Initialize free block header/footer and the epilogue header. */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    return bp;

}
/*
find_fit 

 diff <lowest   
 */
void *find_fit(size_t asize) {
   
    void *bestone= NULL;
    size_t lowest= 9999999;
    int index = getlist_index(asize);
    int i;

    // Searching through all the free-list who has size more than the asize
    for (i = index; i < TOTAL_LISTS; i++) { 
        void *bp = free_listp[i];
        while (bp) {
            size_t curr_blocksize = GET_SIZE(HDRP(bp));
            if (!GET_ALLOC(HDRP(bp)) && (asize <= curr_blocksize)) {
                size_t difference = curr_blocksize - asize;
                if (difference < lowest) {                              
                    lowest = difference;
                    bestone = bp;
                }
            }
            bp  = getNext(bp);
        }
	if(bestone!=NULL)
		return bestone;
    }
    return NULL;
}
/* It marks the block as allocated and splits the block if there is a case */
void place(void* bp, size_t asize, bool Isheapextended){

        size_t bsize = GET_SIZE(HDRP(bp));

        if (asize <= bsize-4*WSIZE) {      /* condition for spliting as the allocated size is less than the current block payload size*/

            if (Isheapextended == false) 
            	delete_freelist(bp); 
// We are deleting it because it is already in the free list .If we extend the heap the free block will not be in the freelist so we don't need to delete_freelist it from the list.
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));    
            size_t excess_size = bsize - asize;
            void *new_spliced = NEXT_BLKP(bp); /*If there is any extra space left,we are splitting that space and adding it in the freelist*/
            PUT(HDRP(new_spliced), PACK(excess_size, 0));
            PUT(FTRP(new_spliced), PACK(excess_size, 0));
            add_freelist(new_spliced);
        }
        else {
            PUT(HDRP(bp), PACK(bsize, 1));
            PUT(FTRP(bp), PACK(bsize, 1));
  	    if (Isheapextended == false) 
           	 delete_freelist(bp);
// We are deleting it because it is already in the free list .If we extend the heap the free block will not be in the freelist so we don't need to delete_freelist it from the list.
        }   
}
/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
     calls create_extras when malloc is called for small sizes so that there is abundance of small sized blocks
 */
void *mm_malloc(size_t size){

    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */    
    char * bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else  
	asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
 
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) { // change to use find_fit function
        place(bp, asize, false);
        return bp;
    }
   
    extendsize = MAX(asize, CHUNKSIZE);

    /* No fit found. Get more memory and place the block */
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize, true);

    return bp;
}

/*
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block and calls _coalesce as we need to take care of effect of coalescing in free list also
 */
void mm_free(void *bp){

    if(bp == NULL){
        return;
    }   
 
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}
/*
 * The following routines are internal helper routines.
 */
/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */

/* coalesce
   coalesces the block and takes care of the free blocks (that are used in coalescing) in their assigned segregated list
   case 1 both prev and next block allocated
   case 2 next block allocated prev free
   case 3 prev block allocated next free
   case 4 both prev and next block free
*/

void *coalesce(void *bp){

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
    	add_freelist(bp);      /* Case:1 Both previous block and next block are allocated*/
        return bp;
    }
    else if (!prev_alloc && next_alloc) {
   	void *prev = PREV_BLKP(bp);   /* Case:2  Previous is free and next block is allocated*/
        delete_freelist(prev);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    	add_freelist(PREV_BLKP(bp));
        
	return (PREV_BLKP(bp));
    }
    else if (prev_alloc && !next_alloc) {
  	void *next = NEXT_BLKP(bp);        /* Case:3 Previous is allocated and next block is free  */
        delete_freelist(next);
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
   	add_freelist(bp);
       
	return (bp);
    }
    else {           
    	void *prev = PREV_BLKP(bp); /* Case:4 Both previous and next block are free*/
        void *next = NEXT_BLKP(bp);
        delete_freelist(prev);
        delete_freelist(next);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  + GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
	add_freelist(PREV_BLKP(bp));

        return (PREV_BLKP(bp));
    }
}
/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   If the block can be coalesced with next free block and the reallocation
     request can be satisfied than no new allocation is required.
     Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *mm_realloc(void *ptr, size_t size){

    if (size == 0){
        mm_free(ptr);
        return NULL;
    }

    if (ptr == NULL)
	return (mm_malloc(size));       // If the ptr is null than we have to allocate to a new block and so malloc is called

    size_t curr = GET_SIZE(HDRP(ptr));

    if (size < curr-2*WSIZE) {                       // if size is less than the old block's payload size than we return the current block as it fits 

        return ptr;
    }

/* If the next block is free and sum of size of ptr and size of nextblock of ptr is greater than the size than we coalesce both blocks */
    void *next = NEXT_BLKP(ptr);
    int next_alloc = GET_ALLOC(HDRP(next));
    size_t coalesce_size=(GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr)));

    if (!next_alloc && size <= coalesce_size-2*WSIZE){ 
        delete_freelist(next);
        PUT(HDRP(ptr), PACK(coalesce_size, 1));
        PUT(FTRP(ptr), PACK(coalesce_size, 1));
        return ptr;
    }
            
    void *oldptr = ptr;
    void *newptr;
    size_t size1;
    newptr = mm_malloc(size);  
                       
    if (newptr == NULL)
        return NULL;

    size1 = GET_SIZE(HDRP(oldptr));

    if (size < size1)                // if the blocksize is greater than size that has to be allocated we want it to place the allocated size in the block header so we do this
        size1 = size;

    memcpy(newptr, oldptr, size1);
    mm_free(oldptr);

    return newptr;
}
/*
     * checkheap
     * Check the consistency of the memory heap
     * Return nonzero if the heap is consistant.
     */
 void checkheap(bool verbose){

        int i;
        void *bp;  

        for(i = 0; i < TOTAL_LISTS; i++) {
            bp = free_listp[i];       
  
            while (bp) {                       
                      //Checking for a allocated block in free list

                if (GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1){
                        printf("Found a allocated block in %dth freelist\n",i);

                        return;
                }     
                bp  = getNext(bp);
            }
        }

            if (verbose)
	            printf("Heap (%p):\n", heaplistp);

            if (GET_SIZE(HDRP(heaplistp)) != DSIZE ||!GET_ALLOC(HDRP(heaplistp)))
                    printf("Bad prologue header\n");

            checkblock(heaplistp);

            for (bp = heaplistp; GET_SIZE(HDRP(bp)) > 0; bp = (void *)NEXT_BLKP(bp)) {

	        if (verbose)
          	      printblock(bp);

                checkblock(bp);
        }
            if (verbose)
		printblock(bp);

            if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
           	printf("Bad epilogue header\n");
    }

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */

static void checkblock(void *bp){

    if ((uintptr_t)bp % DSIZE)
        printf("Error: %p is not doubleword aligned\n", bp);

    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}
/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
 

 static void printblock(void *bp){

        bool halloc, falloc;
        size_t hsize, fsize;

        checkheap(false);
        hsize = GET_SIZE(HDRP(bp));
        halloc = GET_ALLOC(HDRP(bp));  
        fsize = GET_SIZE(FTRP(bp));
        falloc = GET_ALLOC(FTRP(bp));  

        if (hsize == 0) {
            printf("%p: end of heap\n", bp);
            return;
        }

        printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
            hsize, (halloc ? 'a' : 'f'), 
            fsize, (falloc ? 'a' : 'f'));
    }



/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
