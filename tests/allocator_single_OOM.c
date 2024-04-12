/**
 * @file allocator_single_OOM.c
 * @brief When out of memory, malloc should return 0 (null),
 *          not fail inside the allocator. free(0) is always 
 *          legal and should not blow up either. 
 */
#include <stdlib.h> 
#include <stdio.h>
// 80 is used in a lot of other tests
// current max of heap is 4096
#define  MAX_SIZE 160

int main() 
{
    // eat the heap, ptr should be nonzero 
    char* blowupheap = (char*) malloc(4000 * sizeof(char));
    if (blowupheap == NULL) { return EXIT_FAILURE; }

    // should not be able to fit this & return a null ptr 
    // 168 = 160*1 + 8 
    char* input0 = (char*) malloc(MAX_SIZE * sizeof(char));
    if (input0 != NULL) { return EXIT_FAILURE; }
    free(input0);

    //648
    int* input1 = (int*) malloc(MAX_SIZE * sizeof(int));
    if (input1 != NULL) { return EXIT_FAILURE; }
    free(input1);

    // 1344
    long* input2 = (long*) malloc(MAX_SIZE * sizeof(long));
    if (input2 != NULL) { return EXIT_FAILURE; }
    free(input2);

    // 168
    char** input3 = (char**) malloc(MAX_SIZE * sizeof(char*));
    if (input3 != NULL) { return EXIT_FAILURE; }
    free(input3);
	
    // don't leak
    free(blowupheap);
    return (EXIT_SUCCESS);
}