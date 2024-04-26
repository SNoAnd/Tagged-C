/**
 * kicking it old school 
 */
#include <stdio.h>

int main () {
    char c;
    do { 
        c = getchar(); 
        printf("char: %c\n");
    } while (c != '\n' && c != EOF);
return 0;
}