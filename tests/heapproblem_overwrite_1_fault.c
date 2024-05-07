#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 10 //size to read
#define BUF_SIZE 5 //size of smaller buff to get overreads during strcpy
/**
 * TaggedC does not have strlen. 
 * NB: strlen does not include the \0 terminator
*/
int strlen(char *p) {
  int c = 0;
  while (*p != '\0') {
    p++;
    c++;
  }
  return c;
}

/**
 * fgets is mangling tags, but we think getchar will preserve that 
 *  fgets adds the \0 at n-1 th spot 
 * NB: fgets returns an s techically, though most users never check it 
 * NB: taggedc only supports stdin, not all streams
*/
void faux_fgets(char* s, int n, FILE* stream) {
    int read = 0;
    char c;
    do { 
        c = getchar();
        s[read] = c;
        read++; 
    } while (c != '\n' && c != EOF && (read < n));
    //write over newline from io if shorter than buffer
    if (read < n) { s[read-1] = '\0'; } 
    else          { s[n-1] = '\0'; }
}

/**
 * TaggedC doesn't have strcpy.  
*/
char* strcpy(char* destination, const char* source) {
    int src_len = strlen(source);
    //printf("strcpy: src: %s, len: %d", source, src_len);
    for (int i = 0; i<src_len;i++ ) {
        destination[i] = source[i];
        //printf("%d: %s\n",i, destination);
    }
    return destination;
}

int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    
    // fill the buffer so overwriting \0 does the right thing
    // by default its full of 00s, not very realistic
    //for(int i=0; i < MAX_SIZE; i++ ) {input[i] ='B';}

    printf("Even cases are safe.\nEnter some input:");
    faux_fgets(input, MAX_SIZE, stdin);
    //printf(input);
    int input_len = strlen(input); // does not inlcude the \0

    // Poo to trigger case
    if ((char) input[0] == 'P') {
        // OOB write
        int input_len = strlen(input); // does not inlcude the \0
        input[input_len+1] = 'A';
        // print should run until a null...which we removed
        printf("1:You entered %s.Hope it doesn't have a problem!", input);
    }
    else {
        printf("2:You entered %s.\n", input);
    }

    // PIE exercises both
    // III exercises just this one. want to see the classic strcpy OOB
    // can trigger here if input is too short since were missing a check 
    //      less exploitable, more bad form   
    if ((char) input[1] == 'I') {
        // buf_size is half the size of max, if max is filled, even if its
        //      properly terminated, it should still raise overread
        printf(input);
        char* inputcpy = (char*) malloc(BUF_SIZE * sizeof(char));
        // @TODO can remove this once the logging is fully in place
        //      rn this will failstop w/o the writes 
        for(int i=0; i < BUF_SIZE; i++ ) {input[i] ='C';}
        // fails with a storeT failstop 
        char* inputcpy_2 = strcpy(inputcpy, input);
        // should not get here
        printf("3:You entered %s.Hope it doesn't have a problem!", inputcpy_2);
    }
    else {
        printf("4:You entered %s.\n", input);
    }
    //OOPS
    if ((char) input[2] == 'P') {
        // off by one error counting down
        for(int i = input_len; i >= 0; i--) {
            input[i-1] = 'D';
        }
        printf("1:You entered %s.Hope it doesn't have a problem!", input);
    }
     else {
        printf("6:You entered %s.\n", input);
    }
    // give the fuzzer a benign branch to poke at 
    if ((char) input[3] == 'E') {printf("?: dummy conditional case\n"); }

    free(input);
	return EXIT_SUCCESS;
}