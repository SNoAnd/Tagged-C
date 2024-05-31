/**
 * @todo write test
 * @file heapleak_leftoversecret_1_fault.c
 * @brief Demonstrate a single conditional secret left over in the heap 
 * @note
 * "heap leak" can mean just about any problem with the heap. There are at least 5:
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 */

#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 80
#define MAX_TOKEN_SIZE 20

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

/** TaggedC doesn't have strcpy.  */
char* strcpy(char* destination, const char* source) {
    int src_len = strlen(source);
    for (int i = 0; i<src_len;i++ ) {
        destination[i] = source[i];
    }
    return destination;
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
 * Simulate a service that gets a secret from a vault, api, etc
 * return length of key, 0 if key could not be retreived 
*/
int get_secret_from_vault(char* destination) {
    // https://codelabs.cs.pdx.edu/labs/W7.1_cloud_setup/index.html?index=..%2F..cs495#1
    char* source = "bUbcM250Ej3OS";
    int src_len = strlen(source);
    int i = 0;
    for (i = 0; i<src_len;i++ ) {
        destination[i] = source[i];
    }
    return i;
}
int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    printf("enter some input:");
    faux_fgets(input, MAX_SIZE, stdin);
    int input_len = strlen(input); // does not inlcude the \0

    if (input_len < 4) {
        printf("too short \n");
        return EXIT_SUCCESS;
    }

        // get & use token normally
    char* token = (char*) malloc(MAX_TOKEN_SIZE * sizeof(char));
    int secret_len = get_secret_from_vault(token);
    if (secret_len > 0) { 
        // nominally use the secret to do things
        printf("got the secret token\n");
    }
    // secret should now be left in the heap
    free(token);
    if((char) input[0] == 'P') {
        if((char) input[1] == 'I') {
            if((char)input[2] == 'P') {
                if((char)input[3] == 'E') {
                    // go heap dumpster diving; last used is the heap root and we're the right size
                    char* dumpsterdive = (char*) malloc(MAX_TOKEN_SIZE * sizeof(char));
                    // should trigger inside printf as it reads it to print
                    printf("left in the trash: %s", dumpsterdive);
                    free(dumpsterdive);
                }
            }
        }
    } 
    printf("You entered %s. Hope it doesn't have a problem!", input);
    free(input);
	return EXIT_SUCCESS;
}