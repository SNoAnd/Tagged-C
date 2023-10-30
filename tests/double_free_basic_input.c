/**
 * @file double_free_basic_input.c
 * @brief Most basic DoubleFree tagged policy violation for fuzzing.
 *      Looking at godbolt (I think these are in asm D, S form >.< )
 *      gcc 13.2, trunk, the free()s turn into
 *          mov     rax, QWORD PTR [rbp-8]
 *          mov     rdi, rax
 *          call    free
 *      clang x86-64 trunk (both frees)
 *          mov     rdi, qword ptr [rbp - 16]
 *          call    free@PLT
 *      compcert x86 3.12 (both frees)
 *          movl    %ebx, 0(%esp)
 *          call    free
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 1024
int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    printf("enter some input:");
    // FILE *fp; instead of stdin if needed.
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);
    free(input);
    free(input); // the most straightforward double free
    // fuzzer should not get here
    printf("You entered %s. Hope it doesn't have a problem!", input);
	exit(EXIT_SUCCESS);
}