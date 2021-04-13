#include "deque.h"
#include "utils.h"
#include "mockups.h" 

static Deque *deque;
static DequeConf conf;
int stat;

void setup_tests() { stat = deque_new(&deque); }

void teardown_tests() { deque_destroy(deque); }

int main() {
    setup_tests();

    int a = sym_int("a", 32);
    int b = sym_int("b", 32);
    int c = sym_int("c", 32);
    int d = sym_int("d", 32);
    int e = sym_int("e", 32);
    int f = sym_int("f", 32);
    int g = sym_int("g", 32);

    deque_add(deque, &a);
    deque_add(deque, &b);
    deque_add(deque, &c);
    deque_add(deque, &d);
    deque_add(deque, &e);
    deque_add(deque, &f);
    deque_add(deque, &a);

    assert(2 == deque_contains(deque, &a));
    assert(0 == deque_contains(deque, &g));
    assert(1 == deque_contains(deque, &e));

    teardown_tests();
    return 0;
}
