#include <stdlib.h> 
#include <stdio.h>
#define BUF_SIZE 24


int main() {
    char* input = (char*) malloc(BUF_SIZE * sizeof(char));
    input[BUF_SIZE+1] = 'A';
    free(input);
	return EXIT_SUCCESS;
}