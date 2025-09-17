struct Goon {
    int a;
    int b;
    int c;
    int d;
};

struct Sig {
    struct Goon g1;
    struct Goon g2;
    struct Goon g3;
};

int main(void) {
    struct Sig a = {
        {
            1, 2, 3, 4
        },
        {
            2, 4, 6, 8
        },
        {
            3, 6, 9, 12
        },
    };

    return a.g3.b;
}