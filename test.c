int main() {
    int b;
    int a = b = 5;
    a = (a >> 1) + 3;
    return a == b;
}