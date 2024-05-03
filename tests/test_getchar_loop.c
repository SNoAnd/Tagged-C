/**
 * kicking it old school 
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 6 //size to read. fgets promises \0 at end


void faux_fgets(char* s, int n, FILE* stream) {
    int read = 0;
    char c;
    do { 
        c = getchar();
        //printf("#%d char: %c.\n", read, c);
        s[read] = c;
        //printf("#%d news: %s.\n", read, s);
        read++; 
    } while (c != '\n' && c != EOF && (read < n));
    //printf("read:%d\n", read);
    if (read < n) {
        //write over newline from io
        //printf("s[%d]\n", read-1);
        s[read-1] = '\0';
    } 
    else {
        //printf("maxed buffer.\n");
        s[n-1] = '\0';
    }
    //printf("final s: %s.\n", s);
}

int main () {
    char input[MAX_SIZE];
    printf("enter some input:\n");
    faux_fgets(input, MAX_SIZE, stdin);
    printf("You entered: %s.\n", input);
    return 0;
}