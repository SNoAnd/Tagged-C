/**
 * kicking it old school 
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 40 //size to read


void faux_fgets(char* s, int n, FILE* stream) {
    printf("did we get to here?");
    int read = 0;
    char c;
    do { 
        c = getchar();
        read++; 
        printf("#%d char: %c\n", read, c);
        s[read] = c;
    } while (c != '\n' && c != EOF && (read < n-1));
    s[read+1] = '\0';
    printf("final s: %s\n", s);
}

int main () {
    char input[MAX_SIZE];
    printf("enter some input:\n");
    faux_fgets(input, MAX_SIZE, stdin);
    printf("You entered: %s", input);
    return 0;
}