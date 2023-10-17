#include "stdlib.h"

int main() {
	int* x = (int*) malloc(sizeof(int));
	*x = 3;
	free(x);
	free(x);
	return *x;
}
