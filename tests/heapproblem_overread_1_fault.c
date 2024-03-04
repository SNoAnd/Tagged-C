/**
 * @todo test test. I've got 3 options, but I don't think all 3 are gonna work.
 * 
 * @file heapleak_overead_1_fault.c
 * @brief Demonstrate a single conditional heap overread fault. 
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
 * 
 *      (1)(2)(5) are things that SOTA fuzzers can reasonably detect when augmented with 
 *          sanitizers like ASAN. 
 *      However they cannot usually tell (1) and (2) apart from each other or other segfaulting
 *          conditions. 
 *      (5) can sometimes be detected by other means. find_or_create_page() returns null,
 *          linux exit code 137(), etc. 
 */

#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 40
#define BUF_SIZE 20
/**
 * TaggedC does not have strlen. 
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
    printf("enter some input:");
    // FILE *fp; instead of stdin if needed. taggedC only supports stdin rn
    // stdin's fp is known by stdlib  
    fgets(input, MAX_SIZE, stdin);

    if ((char) input[0] == 'P') {
        // I think this won't do what i want 
        printf("You entered %.80s.\nHope it doesn't have a problem!", input);
    }
    else {
        printf("You entered %s.\nHope it doesn't have a problem!", input);
    }

    // if input is > 20 chars, this should over write...and then over read?
    //      hum, I just want the over read...
    if ((char) input[1] == 'I') {

        char inputcpy[BUF_SIZE];
        char * inputcpy_ptr = strcpy(inputcpy, input);

        printf("You entered %s.\nHope it doesn't have a problem!", inputcpy_ptr);
    }
    else {
        printf("You entered %s.\nHope it doesn't have a problem!", input);
    }

    if ((char) input[2] == 'P') {
        // carefully write over the null terminators, but not beyond so
        //      as not to trigger the overwrite protection
        int input_len = strlen(input);
        for (int i = 0; i < input_len; i++) {
            if (input[i] == '\0') {
                input[i] = 'A';
            }
        }
        printf("You entered %s.\nHope it doesn't have a problem!", input);
    }
    else {
        printf("You entered %s.\nHope it doesn't have a problem!", input);
    }


    free(input);
	return EXIT_SUCCESS;
}