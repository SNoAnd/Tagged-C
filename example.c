#include <stdio.h>

int f() {
	return 0;
}

void publish(int x) {
	printf("%d\n", x);
	return;
}

int main() {
	int secret = 5;
	int sensitive[4] = {0,0,0,0};
	int (*foo)() = f;
	int res = (*foo)();
	if (sensitive[0] == 42)
		publish(secret);
	else
		publish(res);
	return 0;
}
