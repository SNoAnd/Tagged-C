/**
 * @file double_free_basic_input_handlabelled.c
 * @brief Most basic DoubleFree tagged policy violation for fuzzing, 
 * doublefrees regardless of input.
 * @note Free sites are hand labelled
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 80 /*1024 too big atm */
int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    printf("enter some input:\n");
    // FILE *fp; instead of stdin if needed.
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);
    label0: free(input);
    label1: free(input); // the most straightforward double free
    // fuzzer should not get here
    printf("You entered %s. Hope it doesn't have a problem!", input);
	return EXIT_SUCCESS;
}