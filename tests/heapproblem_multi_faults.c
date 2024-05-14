/**
 * @todo write test. This is the "BIG test" once all the smaller tests are working 
 * 
 * @file heapleak_multi_fault
 * @brief Demonstrate a variety of heap behavior in 1 program. Ideally get all 3
 * @note
 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 *      (1) heap buffer overwrite (RCE)
 *      (2) heap buffer overread (heartbleed)
 *      (3) heap address leak (defeat ASLR in an exploit chain)
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 * @note Inputs:
 * 
 */

#include <stdlib.h> 
#include <stdio.h>
// no padding 
#define MAX_SIZE 32
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
    for (int i = 0; i<src_len;i++ ) {
        destination[i] = source[i];
    }
    return destination;
}

void cleaner(char* input, int len) {
    char* smallbuf = (char*) malloc((MAX_SIZE/2) * sizeof(char));

    if(len >= 6 && (char)input[5] == 'C') {
        // overwrite
        // off by one(ish) error counting up. the null term is at input[len]
        //  and that is legally yours wrt the heap
        for(int i = 0; i <= (len+1); i++) {
            input[i] = 'U';
        }
    } else if (len >= 7 && (char)input[6] == 'L') {
        char* smallbuf = (char*) malloc((MAX_SIZE/2) * sizeof(char));
        // overwrite, should blow up in the handcoded strcpy above 
        char * inputcpy_ptr = strcpy(smallbuf, input);
        printf("7:You entered %s.Hope it doesn't have a problem!", inputcpy_ptr);
    } else if (len >= 8 && (char)input[7] == 'E') {
        // will later double free
        free(smallbuf);
    } else if (len >= 9 && (char)input[8] == 'A') {
        // overread, off by one(ish) error counting up. the null term is at input[len]
        //  and that is legally yours wrt the heap
        for(int i = 0; i <= (len+1); i++) {
            printf("%d:%c\n", i, input[i]);
        }
    } else if (len >= 10 && (char)input[9] == 'N') {
        // overread, off by one error counting down
        for(int i = len; i >= 0; i--) {
            printf("%d:%c\n", i, input[i-1]);
        }
    } else if (len >= 11 && (char)input[10] == 'E') {
        printf("TODO, put fault here\n");
    } else if (len >= 12 && (char)input[11] == 'R') {
        printf("TODO, put fault here\n");
    } else if (len >= 13 && (char)input[12] == '!') {
        printf("TODO, put fault here\n");
    }
    free(smallbuf);
}

int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    // for the potential overreads 
    for(int i=0; i < MAX_SIZE; i++ ) {input[i] ='A';}

    printf("Enter some input:");
    faux_fgets(input, MAX_SIZE, stdin);
    int input_len = strlen(input); // does not inlcude the \0

    if (input_len < 4) {
        printf("Too short! Try again.\n");
        return EXIT_SUCCESS;
    }
    if((char) input[0] == 'P') {
        if((char) input[1] == 'I') {
            if((char)input[2] == 'P') {
                if((char)input[3] == 'E') {
                    if(input_len >= 5 && (char)input[4] == '-') {
                        printf("dummy case\n");
                    }
                    else {
                        cleaner(input, input_len);
                    }
                } 
            } 
        }
    }
    else {
        printf("You entered %s.\n", input);
    }
    return EXIT_SUCCESS;
}