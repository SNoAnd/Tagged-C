/**
 * @file heapleak_overead_getchar_1_fault.c
 * @brief Demonstrate a single conditional heap overread fault. w/o fgets
 * @note Overreads in a single program are usually tied to mis-use of strcpy or
 *      strcat. This presents two problems for us: we don't have the strlib, and
 *      the policy should notice the overwrite. 
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
#define BUF_SIZE 5 //size of smaller buff to get overeads
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
    for(int i=0; i < MAX_SIZE; i++ ) {input[i] ='B';}

    printf("Even cases are safe.\nEnter some input:");
    faux_fgets(input, MAX_SIZE, stdin);

    // Poo to trigger case
    if ((char) input[0] == 'P') {
        // carefully write over the null terminator, but not beyond so
        //  as not to trigger the overwrite protection but still 
        //  lead to overread
        int input_len = strlen(input); // does not inlcude the \0
        input[input_len] = 'A';
        // print should run until a null...
        printf("1:You entered %s.\nHope it doesn't have a problem!", input);
    }
    else {
        printf("2:You entered %s.\n", input);
    }

    // PIE exercises both
    // III exercises just this one 
    // can trigger here if input is too short  
    if ((char) input[1] == 'I') {
        // buf_size is half the size of max
        char inputcpy[BUF_SIZE];
        char * inputcpy_ptr = strcpy(inputcpy, input);

        printf("3:You entered %s.\nHope it doesn't have a problem!", inputcpy_ptr);
    }
    else {
        printf("4:You entered %s.\n", input);
    }

    free(input);
	return EXIT_SUCCESS;
}