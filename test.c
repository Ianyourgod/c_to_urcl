enum Greek {
    ALPHA,
    SIGMA,
    BETA
};

int main(void) {
    enum Greek item = SIGMA;

    int result = 0;

    switch (item) {
        case ALPHA:
            result = 23;
            break;
        case SIGMA:
            result = 44;
            break;
        case BETA:
            result = 99;
            break;
        default:
            result = -1;
            break;
    }

    return result;
}