static unsigned int affine(unsigned int n,
                           unsigned int slope,
                           unsigned int offset) {
    return n * slope + offset;
}

unsigned int collatz1(unsigned int start) {
    if (start == 1)
      return 0;
    else if (start % 2 == 0)
      return collatz1(start / 2) + 1;
    else
      return collatz1(affine(start, 3, 1)) + 1;
}
