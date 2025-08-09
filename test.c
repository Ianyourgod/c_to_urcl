struct Node {
    int val;
    struct Node *next;
};

int main(void) {
    struct Node end = { .val=8, .next=0 };
    struct Node mid2 = { .val=6, .next=&end };
    struct Node mid1 = { .val=4, .next=&mid2 };
    struct Node start = { .val=2, .next=&mid1 };

    int sum = 0;
    struct Node* next = &start;

    while (next) {
        sum += next->val;
        next = next->next;
    }

    return sum;
}