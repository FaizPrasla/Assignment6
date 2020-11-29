/* 
 * cache.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss. (I examined the trace,
 *  the largest request I saw was for 8 bytes).
 *  2. Instruction loads (I) are ignored, since we are interested in evaluating
 *  trans.c in terms of its data cache performance.
 *  3. data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus an possible eviction.
 *
 * The function printSummary() ias given to print output.
 * Please use this function to print the number of hits, misses and evictions.
 * This is crucial for the driver to evaluate your work. 
 */
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include "cache.h"

//#define DEBUG_ON 
#define ADDRESS_LENGTH 64

/* Globals set by command line args */
int verbosity_cache = 0; /* print trace if set */
int s = 0; /* set index bits */
int b = 0; /* block offset bits */
int E = 0; /* associativity */

/* Derived from command line args */
int S; /* number of sets */
int B; /* block size (bytes) */

/* Counters used to record cache statistics in printSummary().
   test-cache uses these numbers to verify correctness of the cache. */

//Increment when a miss occurs
int miss_count = 0;

//Increment when a hit occurs
int hit_count = 0;

//Increment when an eviction occurs
int eviction_count = 0;

/* 
 * A possible hierarchy for the cache. The helper functions defined below
 * are based on this cache structure.
 * lru is a counter used to implement LRU replacement policy.
 */
typedef struct cache_line {
    char valid;
    mem_addr_t tag;
    unsigned long long int lru;
    byte_t *data;
} cache_line_t;

typedef struct cache_set {
    cache_line_t *lines;
} cache_set_t;

typedef struct cache {
    cache_set_t *sets;
} cache_t;

cache_t cache;
mem_addr_t s_mask;


/* TODO: add more globals, structs, macros if necessary */

/* 
 * Initialize the cache according to specified arguments
 * Called by cache-runner so do not modify the function signature
 * 
 * The code provided here shows you how to initialize a cache structure
 * defined above. It's not complete and feel free to modify/add code.
 */
void initCache(int s_in, int b_in, int E_in)
{
    /* see cache-runner for the meaning of each argument */
    s = s_in;
    b = b_in;
    E = E_in;
    S = (unsigned int) pow(2, s);
    B = (unsigned int) pow(2, b);

    int i, j;
    cache.sets = (cache_set_t*) calloc(S, sizeof(cache_set_t));
    for (i=0; i < S; i++){
        cache.sets[i].lines = (cache_line_t*) calloc(E, sizeof(cache_line_t));
        for (j=0; j<E; j++){
            cache.sets[i].lines[j].valid = 0;
            cache.sets[i].lines[j].tag = 0;
            cache.sets[i].lines[j].lru = 0;
            cache.sets[i].lines[j].data = calloc(B, sizeof(byte_t));
        }
    }
    /* TODO: add more code for initialization */
    s_mask = (mem_addr_t) (S - 1);
}

/* 
 * Free allocated memory. Feel free to modify it
 */
void freeCache()
{
    int i;
    for (i = 0; i < S; i++){
        free(cache.sets[i].lines);     
    }
    free(cache.sets);
}

/* TODO:
 * Get the line for address contained in the cache
 * On hit, return the cache line holding the address
 * On miss, returns NULL
 */
cache_line_t *get_line(word_t addr)
{
    mem_addr_t tag_add = addr >> (s + b);
    cache_set_t cache_set = cache.sets[(mem_addr_t) ((addr >> b) & s_mask)];
    int i;
    for (i = 0; i < E; i++) {
        if (cache_set.lines[i].tag == tag_add){
            if(cache_set.lines[i].valid){
                hit_count++;
                int j;
                for (j = 0; j < E; j++) {
                if (cache_set.lines[j].valid ) {
                    if(cache_set.lines[j].lru < cache_set.lines[i].lru)
                    cache_set.lines[j].lru++;
                }
            }
            cache_set.lines[i].lru = 0;
            return &cache_set.lines[i];
            } 
        }
    }
    miss_count++;
    return NULL;
}

/* TODO:
 * Select the line to fill with the new cache line
 * Return the cache line selected to filled in by addr
 */
cache_line_t *select_line(word_t addr)
{
    mem_addr_t tag_add = addr >> (s + b);
    cache_set_t cache_set = cache.sets[(mem_addr_t) ((addr >> b) & s_mask)];
    int j = 0;
    int biggest_I = 0;
    unsigned long long int farLru = 0;
    while(j < E && cache_set.lines[j].valid){
        if (cache_set.lines[j].lru >= farLru) {
            farLru = cache_set.lines[j].lru;
            biggest_I = j;
        }
        j++;
    }
     if (j != E) {
        // found an invalid entry
        // update other entries 
        for (int k = 0; k < E; k++)
            if (cache_set.lines[k].valid)
                ++cache_set.lines[k].lru;
        // insert line 
        cache_set.lines[j].lru = 0;
        cache_set.lines[j].valid = 1;
        cache_set.lines[j].tag = tag_add;
        // return
        return &cache_set.lines[j];
    } else {
        // all entry is valid, replace the oldest one
        eviction_count++;
        for (int k = 0; k < E; k++)
            cache_set.lines[k].lru++;
        cache_set.lines[biggest_I].lru = 0;
        cache_set.lines[biggest_I].tag = tag_add;
        return &cache_set.lines[biggest_I];
    }
}

/*  TODO:
 * Check if the address is hit in the cache, updating hit and miss data. 
 * Return True if pos hits in the cache.
 */
bool check_hit(word_t pos) 
{
    return get_line(pos) != NULL ? 1 : 0;
}

/*  TODO:
 * Handles Misses, evicting from the cache if necessary. If evicted_pos and evicted_block
 * are not NULL, copy the evicted data and address out.
 * If block is not NULL, copy the data from block into the cache line. 
 * Return True if a line was evicted.
 */ 
bool handle_miss(word_t pos, void *block, word_t *evicted_pos, void *evicted_block) 
{
    return select_line(pos) != NULL ? 1 : 0;
}


/* 
 * Access data at memory address addr
 * If it is already in cache, increast hit_count
 * If it is not in cache, bring it in cache, increase miss count
 * Also increase eviction_count if a line is evicted
 * 
 * Called by cache-runner; no need to modify it if you implement
 * check_hit() and handle_miss()
 */
void accessData(mem_addr_t addr)
{
    if(!check_hit(addr))
        handle_miss(addr, NULL, NULL, NULL);
}