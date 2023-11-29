/**
 * @file double_free_confused_cleanup_multi_handlabelled.c
 * @brief Contains 2 double frees on different memory for root cause testing. 
 *      Has the same double free on input as confused_cleanup_2 and
 *      a 2nd double free on x if flag !=0
 *      Also relies on 1st three bytes existing. 
 * 
 * @note We expect the fuzzing output to report 0, 1, or 2 failures
 *  depending mostly on 2nd byte in input 
 * 
 *  B = 66 dec (/ 6, /2 and /3) 
 *      "BBB" -> 2 (only input will trigger)
 *            -> for input, triggers dfree, label0, label2 
 *            -> for x, triggers dfree, label3, label4 (if we got there)
 *  2 = 50 dec ( /2 but not /3)
 *      "222" -> 1 
 *            -> for input, free at label0 (safe)
 *            -> for x, triggers dfree for x, label3, label4
 *      "220" -> 0
 *            -> for input, free at label0 (safe)
 *            -> for x, free at label4 (safe, skips label 3)
 *              
 *  ! = 33 dec ( /3 but not /2)
 *      "!!!" -> 1
 *            -> for input, triggers dfree at label1, label2
 *            -> for x, triggers dfree for x, label3, label4
 *      "!!0" -> 2 (only input will trigger)
 *            -> for input, triggers dfree at label1, label2 
 *            -> for x, free at label4 (safe)
 * 
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 80 /*1024 */

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
    char* input = (char*) malloc(MAX_SIZE /** sizeof(char)*/ );
    printf("enter some input:");
    // FILE *fp; instead of stdin if needed.
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);
    printf("You entered %s. Hope it doesn't have a problem!", input);
    // incoming length is > 2 
    /*
    if (strlen(input) < 2) {
        printf("That's too short. Try again");
        return EXIT_SUCCESS;
    }
    */

    // flagb2 is 2nd byte
    int flagb2 = (char) input[1]; // always enough room in an int for a char
    // simulating a control flag that can trigger clean up twice
    //      6 = 3*2, will trigger this if and a later one
    if (!(flagb2 % 2)) {
        label0: free (input);
    } else {
        label1: free (input);
    } 
    // stand in for "program runs for a while and does other things."
    input[0] = foo2(foo(input[0]));
    // simulating later clean up in the program after doing other things for a while 
    if (!(flagb2 % 3)) {
        label2: free (input);
    }

    // if 3rd byte is not '0', double free
    int flagb3 = (char) input[2];
    if (flagb3 != '0') {
        label3: free (x);
    }
     label4: free (x);
	return EXIT_SUCCESS;
}