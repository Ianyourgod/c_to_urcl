struct SomeStuff {
    int do_shit;
};

void do_some_stuff(struct SomeStuff *a) {
    a->do_shit = 4;
    while (!a->do_shit) {}
    return;
}

int main(void) {
    struct SomeStuff a = { .do_shit=2 };
    do_some_stuff(&a);
    return a.do_shit;
}