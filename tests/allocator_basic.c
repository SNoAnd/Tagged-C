#include <stdlib.h> 
#include <stdio.h>
// heap size is currently 4096, but has no merge
// change big size to 1000 to OOM heap
#define  BIG_SIZE 500
#define  MED_SIZE 100
#define   SM_SIZE 16
#define BABY_SIZE 1

int main() {
    // try a bunch of big blocks
    char* bigchar0 = (char*) malloc(BIG_SIZE * sizeof(char));
    char* bigchar1 = (char*) malloc(BIG_SIZE * sizeof(char));
    char* bigchar2 = (char*) malloc(BIG_SIZE * sizeof(char));
    char* bigchar3 = (char*) malloc(BIG_SIZE * sizeof(char));

    // try a bunch of small ones
    char* babychar0 = (char*) malloc(BABY_SIZE * sizeof(char));
    char* babychar1 = (char*) malloc(BABY_SIZE * sizeof(char));
    char* babychar2 = (char*) malloc(BABY_SIZE * sizeof(char));
    char* babychar3 = (char*) malloc(BABY_SIZE * sizeof(char));
    char* babychar4 = (char*) malloc(BABY_SIZE * sizeof(char));

    // free the small ones 
    free(babychar0);
    free(babychar1);
    free(babychar2);
    free(babychar3);
    free(babychar4);

    //ints are 4 by default, ptrs are 8 
    // alternate for re-use case
    int* medint0 = (int*) malloc(MED_SIZE * sizeof(int));
    int* medint1 = (int*) malloc(MED_SIZE * sizeof(int));
    free(medint0);
    int* medint2 = (int*) malloc(MED_SIZE * sizeof(int));
    free(medint1);
    int* medint3 = (int*) malloc(MED_SIZE * sizeof(int));
    free(medint2);
    free(medint3);

    // return big blocks 
    free(bigchar0);
    free(bigchar1);
    free(bigchar2);
    free(bigchar3);

    // should force a split?  maybe?
    char* smchar0 = (char*) malloc(SM_SIZE * sizeof(char));
    char* babychar5 =(char*) malloc(BABY_SIZE * sizeof(char));
    free(smchar0);
    free(babychar5);
	return (EXIT_SUCCESS);
}