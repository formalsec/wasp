extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "test03.c", 3, "reach_error"); }


int f(int *p1, int *p2) {
    return p1 == p2;
}

int q;

int main() {
    int a, b;

    q = 0;

    int *p1 = &a;
    int *p2 = &b;

    a = f(p1, p2);

    if (a) {
        goto ERROR;
    }

    return 0;

    ERROR: {reach_error();abort();}
    return 1;
}
