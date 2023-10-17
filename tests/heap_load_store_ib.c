#include "stdlib.h"

struct S {
	int contents;
};

int main() {
	struct S* s = (struct S*) malloc(sizeof(struct S));
	s->contents = 42;
	return s->contents;
}
