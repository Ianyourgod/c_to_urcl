struct IStoreStuff {
    char a;
};

struct Node {
    int val;
    struct IStoreStuff inner;
};

int main(void) {
    struct Node n = {0};

    n.inner = (struct IStoreStuff){ .a='\n' };

    return n.inner.a;
}