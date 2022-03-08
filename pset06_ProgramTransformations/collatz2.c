unsigned int collatz2(unsigned int start) {
    unsigned int flight = 0;
    while (start != 1) {
        flight++;
        if ((start & 1) == 0) {
            start = start >> 1;
        } else {
            start = start * 2 + start + 1;
        }
    }
    return flight;
}
