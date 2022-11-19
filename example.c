int f() {
	return 0;
}

void publish(int x) {
	return;
}

int main() {
	int secret = 5;
	int sensitive[4] = {0,0,0,0};
	int res = f();
	if (sensitive[0] == 42)
		publish(secret);
	else
		publish(res);
	return 0;
}
