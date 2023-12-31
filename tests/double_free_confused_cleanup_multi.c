/**
 * @file double_free_confused_cleanup_multi.c
 * @brief Contains 2 double frees on different memory for root cause testing. 
 *      Has the same double free on input as confused_cleanup_2 and
 *      a 2nd double free on x if flag !=0
 *      Also relies on 1st two bytes existing. 
 * 
 * @note We expect the fuzzing output to report 0, 1, or 2 failures
 *  depending mostly on 2nd byte in input 
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 80 /*1024*/

// filler function to simulate program going on and doing things 
int foo (int n) {
    return (n*n)+1;
}

int foo2 (int n) {
    return 2*n;
}

int main() {
    int* x = (int*) malloc(sizeof(int));
	*x = 3;
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    printf("enter some input:");
    // FILE *fp; instead of stdin if needed.
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);
    printf("You entered %s. Hope it doesn't have a problem!", input);
    // incoming length is > 2 
    /*if (strlen(input) < 2) {
        printf("That's too short. Try again");
        return EXIT_SUCCESS;
    }
    */
    
    // flag is 2nd byte
    int flag = (char) input[1]; // always enough room in an int for a char
    // simulating a control flag that can trigger clean up twice
    //      6 = 3*2, will trigger this if and a later one
    if (!(flag % 2)) {
        free (input);
    } else {
        free (input);
    } 
    // stand in for "program runs for a while and does other things."
    input[0] = foo2(foo(input[0]));
    // simulating later clean up in the program after doing other things for a while 
    if (!(flag % 3)) {
        free (input);
    }

    // if flag is not 0, double free
    if (flag) {
        free (x);
    }
    free(x);
	return EXIT_SUCCESS;
}