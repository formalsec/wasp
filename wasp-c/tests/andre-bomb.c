#include <wasp.h>

void bomb(char* a, unsigned char i, unsigned char j) {
    char boom;
    a[i] = 23;
    if (a[j] == 23) boom = 0;
    else boom = 1;
    __WASP_assert(!boom);
}

int main() {
    char a[3] = {__WASP_symb_int("a1"),
                __WASP_symb_int("a2"),
                __WASP_symb_int("a3")};
    bomb(a, 1, 2);
    return 0;
}
