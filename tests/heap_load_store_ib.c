#include "stdlib.h"

struct S {
	int contents;
};

int main() {
	struct S* s = (struct S*) malloc(sizeof(struct S));
	s->contents = 42;
	if (s->contents) {
		return 0;
	} else {
		return -1;
	}
}
