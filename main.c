int foo() {
	*(char*)0 = 0;
}

int main() {
	foo();
	return 0;
}
