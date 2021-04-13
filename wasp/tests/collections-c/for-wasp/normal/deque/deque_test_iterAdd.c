#include "deque.h"
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

    assume(d != a && d != b && d != c && d != e && d != f);

    DequeIter iter;
    deque_iter_init(&iter, deque);

    size_t i = 0;

    int *el;

    assert(6 == deque_size(deque));

    while (deque_iter_next(&iter, (void *)&el) != CC_ITER_END) {
        if (*el == d)
            deque_iter_add(&iter, &g);
        if (i >= 3) {
            assert(i == deque_iter_index(&iter) - 1);
        }
        i++;
    }
    assert(7 == deque_size(deque));

    void *ret_;
    deque_get_at(deque, 4, &ret_);
    assert(g == *(int *)ret_);

    teardown_tests();
    return 0;
}
