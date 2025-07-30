int main(void) {
    int pow(int a, int b);
    return pow(2, 7);
}

int pow(int a, int b) {
    int out = 1;
    for (;b>0;b-=1) {
        out *= a;
    }
    return out;
}