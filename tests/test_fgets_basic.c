#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 100
int main() {
    char input[MAX_SIZE];
    printf("enter some input:\n");
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);
    printf("You entered %s. Hope it doesn't have a problem!", input);
	return EXIT_SUCCESS;
}