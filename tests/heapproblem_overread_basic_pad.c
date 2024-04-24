/**
 * @todo test test. I've got 3 options, but I don't think all 3 are gonna work.
 * 
 * @file heapleak_overead_1_fault.c
 * @brief Sanity check a single heap overread fault. 

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
#define BUF_SIZE 20


int main() {
    char* input = (char*) malloc(BUF_SIZE * sizeof(char));
    for (int i = 0; i < BUF_SIZE; i++)
    {
        // check that we can write to it, we should
        input[i] = 'A';
    }
    input[BUF_SIZE -1] = '\0';
    // check that you can safely copy from the buffer
    char oob = input[0];
    //Out Of Bound read hits padding. need blocks of 8, an alloc of 20 will be 20+padding
    oob = input[BUF_SIZE + 1];

    free(input);
	return EXIT_SUCCESS;
}