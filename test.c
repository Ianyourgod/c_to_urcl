int sqrt(int i) {
    for (int a=0;a<=i/2;a++) {
        if (a*a == i) {
            return a;
        }
    }
    return -1;
}

int main(void) {
    int i = 529;
    return sqrt(i);
}