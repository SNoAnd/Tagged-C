/**
 * @todo test test. I've got 3 options, but I don't think all 3 are gonna work.
 * 
 * @file heapleak_overead_1_fault.c
 * @brief Sanity check a single heap overread fault. 
 * @note not for fuzzing. has no I/O
 * 
 * @note
 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 *      (1) heap buffer overwrite (RCE)
 * ---->(2) heap buffer overread (heartbleed)
 *      (3) heap address leak (defeat ASLR in an exploit chain)
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 */

#include <stdlib.h> 
#include <stdio.h>
#define BUF_SIZE 24


int main() {
    char* input = (char*) malloc(BUF_SIZE * sizeof(char));
    for (int i = 0; i < BUF_SIZE; i++)
    {
        // exercise the allocatedcolor 
        input[i] = 'A';
    }

    char oob;
    // 24 = 8*3. No padding, so this should hit unallocated heap
    oob = input[BUF_SIZE + 1];

    free(input);
	return EXIT_SUCCESS;
}