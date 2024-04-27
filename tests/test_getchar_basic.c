#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 100
int main() {
    char input[MAX_SIZE];
    printf("enter some input:\n");
    // stdin's fp is known by stdlib  
    int c = getchar();	  
    // fgets(input, MAX_SIZE, stdin);
    input[0] = c;
    input[1] = '\0';
    printf("You entered %s. Hope it doesn't have a problem!", input);
	return EXIT_SUCCESS;
}
