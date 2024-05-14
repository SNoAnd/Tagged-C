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
#define MAX_SIZE 80

/**
 * Simulate a service that gets a secret from a vault, api, etc
 * 
 * return length of key, 0 if key could not be retreived 
 * 
 * @TODO drop in a hardcoded token 
 * 
*/
int get_secret_from_vault() {

}
int main() {
    char* input = (char*) malloc(MAX_SIZE * sizeof(char));

    free(input);
	return EXIT_SUCCESS;
}