/**
 * @todo write test to have 3 different overread faults
 * @file heapleak_overwrite_3_fault.c
 * @brief Demonstrate three different conditional heap overwrite faults
 * @note
 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 *      (1) heap buffer overwrite (RCE)
 *      (2) heap buffer overread (heartbleed)
 *      (3) heap address leak (defeat ASLR in an exploit chain)
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 *      (5) heap resource exhaustion/resource leak through memory (OOM )
 * FOOD == clean exit
 * hi  == clean exit  
 * faults: 
 * P000000000 
 * 0I00000000
 * 00P0000000
 * 000E000000
 */

#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 10
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
 * TaggedC doesn't have strcpy. It is a bit odd that you give it the buffer
 *      and it returns another pointer to it, now that I think about it. 
*/
char* strcpy(char* destination, const char* source) {
    int src_len = strlen(source);
    for (int i = 0; i<src_len;i++ ) {
        destination[i] = source[i];
    }
    return destination;
}

int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    
    // fill the buffer so overwriting \0 does the right thing
    // by default its full of 00s, not very realistic
    //for(int i=0; i < MAX_SIZE; i++ ) {input[i] ='B';}

    printf("Even prints are safe.\nEnter some input:");
    faux_fgets(input, MAX_SIZE, stdin);
    //printf(input);
    int input_len = strlen(input); // does not inlcude the \0

    if (input_len < 4) {
        printf("Too short! Try again.\n");
        return EXIT_SUCCESS;
    }

    if ((char) input[0] == 'P') {
        // write 1 past the \0, should failstop
        input[input_len +1 ] = 'A';
        printf("1:You entered %s.Hope it doesn't have a problem!", input);
    }
    else {
        printf("2:You entered %s.\n", input);
    }
 
    if ((char) input[1] == 'I') {
        // off by one(ish) error counting up. the null term is at input[len]
        //  and that is legally yours wrt the heap
        for(int i = 0; i <= (input_len+1); i++) {
            input[i] = 'U';
        }
        printf("3:You entered %s.Hope it doesn't have a problem!", input);
    }
    else {
        printf("4:You entered %s.\n", input);
    }

    if ((char) input[2] == 'P') {
        input[-1] = 'D';
        printf("5:You entered %s.Hope it doesn't have a problem!", input);
    }
    else {
        printf("6:You entered %s.\n", input);
    }
  
    if ((char) input[3] == 'E') {
        char* smallbuf = (char*) malloc((MAX_SIZE/2) * sizeof(char));
        // should blow up in the handcoded strcpy above 
        char * inputcpy_ptr = strcpy(smallbuf, input);
        printf("7:You entered %s.Hope it doesn't have a problem!", inputcpy_ptr);
    }
    else {
        printf("8:You entered %s.\n", input);
    }
    /*
    // left for when/if we expand to full memory protection
    if ((char) input[4] == '!') {
        // NB: heapproblem does not protect the stack, so this will cheerfully smash it
        //  without failstoping
        char inputcpy[BUF_SIZE];
        // should blow up in the handcoded strcpy above 
        char * inputcpy_ptr = strcpy(inputcpy, input);
        printf("?:You entered %s.Hope it doesn't have a problem!", inputcpy_ptr);
    }
    */

    free(input);
	return EXIT_SUCCESS;
}