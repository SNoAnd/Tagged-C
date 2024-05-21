/**
 * @todo write test
 * @file heapleak_leftoversecret_basic.c
 * @brief Demonstrate a single secret left over in the heap, no io
 * @note
 * "heap leak" can mean just about any problem with the heap. There are at least 5. 
 *      This one is the heap 
 *      (4) heap secret recovery from improper clean up (steal keys that were correctly
 *              freed but not zeroed out)
 */

#include <stdlib.h> 
#include <stdio.h>
#define MAX_INPUT_SIZE 80
#define MAX_TOKEN_SIZE 20

/**
 * Simulate a service that gets a secret from a vault, api, etc
 * 
 * return length of key, 0 if key could not be retreived 
 * 
 * 
*/

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
    char* input = (char*) malloc(MAX_INPUT_SIZE * sizeof(char));
    char* token = (char*) malloc(MAX_TOKEN_SIZE * sizeof(char));
    int len = get_secret_from_vault(token);
    if (len > 0) { printf(token); }
    // secret should now be left in the heap
    free(token);
    // go heap dumpster diving
    char* dumpsterdive = (char*) malloc(MAX_TOKEN_SIZE * sizeof(char));
    // should trigger inside printf as it reads it to print
    printf(dumpsterdive);

    free(dumpsterdive);
    free(input);
	return EXIT_SUCCESS;
}