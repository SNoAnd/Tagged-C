int main() {
	int x[3];
	int y[3];

	// Default layout: SP                          Base
	//                  | [y0][y1][y2][x0][x1][x2] |
	for (int i = 2; i > -2; i--) {
		x[i] = i;
	}

	if (y[4]) {
		return 0;
	} else {
		return -1;
	}
}
