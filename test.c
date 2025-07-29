int main() {
    int a = 0;
    int b = 4;
    while (b > 0) {
        a += b;
        b -= 1;
        if (b == 1) {
            break;
        }
    }
    return a;
}