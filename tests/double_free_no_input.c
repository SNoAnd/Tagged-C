// This isn't yet a fuzz target because it doesn't take input.
// However, it's still useful for policy sanity checking
#include "stdlib.h"

int main() {
	int* x = (int*) malloc(sizeof(int));
	*x = 3;
	free(x);
	free(x);
	return *x;
}
