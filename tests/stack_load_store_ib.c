int main() {
	int x[3];

	for (int i = 0; i < 3; i++) {
		x[i] = 5;
	}

	if (x[0]) {
		return 0;
	} else {
		return -1;
	}
}
