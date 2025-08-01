int howMany() {
    static int called_x_times = 0;
    called_x_times += 1;
    return called_x_times;
}

int main(void) {
    for (int i=0;i<99;i+=1) howMany();

    return howMany();
}