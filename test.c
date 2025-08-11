struct Goon {
    int a;
    int b;
    int c;
    int d;
};

int get_c(int a, int b, int c, int d, struct Goon g) {
    return g.c;
}

int main(void) {
    struct Goon g = { 0 };
    g.c = 50;

    return get_c(0,0,0,0,g);
}