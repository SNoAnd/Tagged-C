/**
 * @file heapleak_overread_getchar_1_fault.c
 * @brief Demonstrate a single conditional heap overread fault
 *    for fuzzing. Need "PIPE" at start to trigger 

 */

#include <stdlib.h> 
#include <stdio.h>
// the 3 test has allocator padding to 8 byte align.
//  try with no padding here
#define MAX_SIZE 16

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

int main() {
  char* input = (char*) malloc(MAX_SIZE * sizeof(char));
    
  printf("Enter some input:");
  faux_fgets(input, MAX_SIZE, stdin);
  //printf(input);
  int input_len = strlen(input); // does not inlcude the \0
  // PIPE
  if((char) input[0] == 'P') {
    if((char) input[1] == 'I') {
      if((char)input[2] == 'P') {
        if((char)input[3] == 'E') {
          // fill the buffer so overwriting \0 does the right thing
          // by default its full of 00s, aka \0
          for(int i=0; i < MAX_SIZE; i++ ) {input[i] ='B';}
          input[input_len] = 'A';
          // print should run until a null...which we removed
          printf("1:You entered %s.Hope it doesn't have a problem!", input);
        } 
      }
    }
  }
  else {
      printf("You entered %s.\n", input);
  }
  free(input);
	return EXIT_SUCCESS;
}