/**
 * @file heapleak_overead_getchar_3_faults.c
 * @brief Demonstrate a single conditional heap overread fault. w/o fgets
 * @note Overreads in a single program are usually tied to mis-use of strcpy or
 *      strcat. This presents a problem for us: we don't have the strlib.
 * 
 * @note Heartbleed was a slightly different wrinkle. It trusted the (untrustable) 
 *      user input to say how long the message was. 
 * 
 * @note https://cqr.company/web-vulnerabilities/buffer-over-read/ has a nice checklist
 * 
 * @note
 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 *      (1) heap buffer overwrite (RCE)
 * ---->(2) heap buffer overread (heartbleed)
 *      (3) heap address leak (defeat ASLR in an exploit chain)
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 *      (5) heap resource exhaustion/resource leak through memory (OOM )
 */

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
 * TaggedC doesn't have strcpy. It is a bit odd that you give it the buffer
 *      and it returns another pointer to it, now that I think about it. 
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
    for(int i=0; i < MAX_SIZE; i++ ) {input[i] ='B';}

    printf("Even cases are safe.\nEnter some input:");
    faux_fgets(input, MAX_SIZE, stdin);
    //printf(input);
    int input_len = strlen(input); // does not inlcude the \0

    // Poo to trigger case
    if ((char) input[0] == 'P') {
        // carefully write over the null terminator, but not beyond so
        //  as not to trigger the overwrite protection but still 
        //  lead to overread
        int input_len = strlen(input); // does not inlcude the \0
        input[input_len] = 'A';
        // print should run until a null...which we removed
        printf("1:You entered %s.Hope it doesn't have a problem!", input);
    }
    else {
        printf("2:You entered %s.\n", input);
    }

    // PIE exercises both
    // III exercises just this one. want to see the classic strcpy overread
    //      (which would then turn into overwrite)
    // can trigger here if input is too short since were missing a check 
    //      less exploitable, more bad form   
    if ((char) input[1] == 'I') {
        // off by one(ish) error counting up. the null term is at input[len]
        //  and that is legally yours wrt the heap
        for(int i = 0; i <= (input_len+1); i++) {
            printf("%d:%c\n", i, input[i]);
        }
        printf("3:You entered %s.Hope it doesn't have a problem!", input);
    }
    else {
        printf("4:You entered %s.\n", input);
    }
    //OOPS
    if ((char) input[2] == 'P') {
        // off by one error counting down
        for(int i = input_len; i >= 0; i--) {
            printf("%d:%c\n", i, input[i-1]);
        }
        printf("1:You entered %s.Hope it doesn't have a problem!", input);
    }
     else {
        printf("6:You entered %s.\n", input);
    }
    // give the fuzzer a benign branch to poke at 
    if ((char) input[3] == 'E') {printf("?: dummy conditional case\n"); }
    /*
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