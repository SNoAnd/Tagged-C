/**
 * @file double_free_confused_cleanup_1_handlabelled.c
 * @brief a very simplified version of the error that caused CVE-2017-9078
 *      frees() are hand labelled. 
 *      "root remote code execution because of a double free in cleanup
 *      of TCP listeners when the -a option is enabled"
 * @note "PPP" should fault, AAA should not fault
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 80 /*1024 too big */
int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    printf("enter some input:");
    // FILE *fp; instead of stdin if needed.
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);
    if (input[0] == 'P') {
        label0: free (input);
    }
    label1: free(input);
    printf("You entered %s. Hope it doesn't have a problem!", input);
	return EXIT_SUCCESS;
}