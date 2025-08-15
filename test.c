int main(void) {
    int i = 529;
    for (int a=0;a<=i/2;a++) {
        if (a*a == i) {
            return a;
        }
    }
    return 0;
}