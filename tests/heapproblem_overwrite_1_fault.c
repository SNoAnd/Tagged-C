/**
 * @file heapproblem_overwrite_1_fault.c
 * @brief 1 conditional overwrite fault 
 * 
 */
#include <stdlib.h> 
#include <stdio.h>
#define MAX_SIZE 10 //size to read
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
          // OOB write
          int input_len = strlen(input); 
          // input 0,len-1, \0 at len, len+1 OOB
          input[input_len+1] = 'A';
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