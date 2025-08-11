struct IStoreStuff {
    char a;
};

struct Node {
    int val;
    struct IStoreStuff inner;
};

int main(void) {
    struct Node n = { 0 };

    int sum = 0;
    for (int i=1;i<=10;i++) {
        sum += i;
    }
    return ++sum;
}