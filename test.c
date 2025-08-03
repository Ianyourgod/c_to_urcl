int x = 20;

int b(int *a) {
    *a = 3;
}

int main(void) {
    b(&x);

    return x;
}