struct Goon {
    int a;
    int b;
    int c;
    int d;
};

struct Goon cali(int a, struct Goon g) {
    return (struct Goon){.c=g.c,.a=g.a};
}

int main(void) {
    struct Goon g = { 0 };
    g.c = 50;
    g.a = 40;

    struct Goon new = cali(0,g);

    return new.c + new.a;
}