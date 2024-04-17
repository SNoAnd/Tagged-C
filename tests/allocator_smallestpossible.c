#include <stdlib.h> 
#include <stdio.h>

int main() {
    char* input0 = malloc(1 * sizeof(char));
    free(input0);
    return (EXIT_SUCCESS);
}