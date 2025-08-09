union Sigma {
    int a;
    int* b;
};

int main(void) {
    union Sigma sig;

    int b = 3;

    sig.b = &b;

    return sig.a;
}