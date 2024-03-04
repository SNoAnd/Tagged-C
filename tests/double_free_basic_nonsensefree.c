/**
 * @file double_free_basic_nonsensefree.c
 * @brief Test that we failstop correctly on Nonsense or random frees.
 *      Most often these come from corrupted pointers.
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 80 /*1024*/
int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    printf("enter some input:");
    // FILE *fp; instead of stdin if needed.
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);
    
    // You should only free the pointer to the start of the block malloced
    // (ab)use pointer arthimetic 
    free(input+2); 
    // fuzzer should not get here
    printf("You entered %s. Hope it doesn't have a problem!", input);
	return (EXIT_SUCCESS);
}