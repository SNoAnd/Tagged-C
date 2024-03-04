/**
 * @todo test the test. Does teh fault get reported in fgets or at top level?
 * @file heapleak_overwrite_1_fault.c
 * @brief Demonstrate a single conditional heap overwrite fault. The input buffer size is 
 *      20 chars, but fgets will write an input of up to 80 chars, overrunning the bounds.
 *      Inputs up to 19 characters should behave normally.
 * @note
 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 * ---->(1) heap buffer overwrite (RCE)
 *      (2) heap buffer overread (heartbleed)
 *      (3) heap address leak (defeat ASLR in an exploit chain)
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 *      (5) heap resource exhaustion/resource leak through memory (OOM )
 * 
 *      (1)(2)(5) are things that SOTA fuzzers can reasonably detect when augmented with 
 *          sanitizers like ASAN. 
 *      However they cannot usually tell (1) and (2) apart from each other or other segfaulting
 *          conditions. 
 *      (5) can sometimes be detected by other means. find_or_create_page() returns null,
 *          linux exit code 137(), etc. 
 */

#include <stdlib.h> 
#include <stdio.h>
#define BUF_SIZE 20
#define MAX_SIZE 80

int main() {
    // an input between 21-80 bytes will write beyond the buffer 
    char* input = (char*) malloc(BUF_SIZE * sizeof(char));
    printf("enter some input:");
    // FILE *fp; instead of stdin if needed. taggedC only supports stdin rn
    // stdin's fp is known by stdlib 

    fgets(input, MAX_SIZE, stdin);

    printf("You entered %s. Hope it doesn't have a problem!", input);
    free(input);
	return EXIT_SUCCESS;
}