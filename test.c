int expensive(int x) {
    x = x * x + x;
    x = x * x + x;
    return x;
}

int main(void) {
    int i = 12;
    return expensive(i);
}