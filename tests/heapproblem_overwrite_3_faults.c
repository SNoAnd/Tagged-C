/**
 * @todo write test to have 3 different overread faults
 * @file heapleak_overwrite_3_fault.c
 * @brief Demonstrate three different conditional heap overwrite faults
 * @note
 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 *      (1) heap buffer overwrite (RCE)
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
#define MAX_SIZE 80

void faux_fgets(char* s, int n, FILE* stream) {
    int read = 0;
    char c;
    do { 
        c = getchar();
        //printf("#%d char: %c\n", read, c);
        s[read] = c;
        //printf("#%d news: %s\n", read, s);
        read++; 
    } while (c != '\n' && c != EOF && (read < n-1));
    s[read+1] = '\0';
    //printf("final s: %s\n", s);
}

int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    printf("enter some input:");
    // FILE *fp; instead of stdin if needed. taggedC only supports stdin rn
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);

    printf("You entered %s. Hope it doesn't have a problem!", input);
    free(input);
	return EXIT_SUCCESS;
}