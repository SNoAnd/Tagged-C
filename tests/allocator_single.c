#include <stdlib.h> 
#include <stdio.h>
// 80 is used in a lot of other tests
#define  MAX_SIZE 160

int main() {

    // 168 = 160*1 + 8 
    char* input0 = malloc(MAX_SIZE * sizeof(char));
    free(input0);

    //648
    int* input1 = malloc(MAX_SIZE * sizeof(int));
    free(input1);

    // 1344
    long* input2 = malloc(MAX_SIZE * sizeof(long));
    free(input2);

    // 168
    char** input3 = malloc(MAX_SIZE * sizeof(char*));
    free(input3);
	
    return (EXIT_SUCCESS);
}