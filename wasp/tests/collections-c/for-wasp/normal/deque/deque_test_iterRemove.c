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
    void *el;
    while (deque_iter_next(&iter, &el) != CC_ITER_END) {
        if (i == 3)
            deque_iter_remove(&iter, NULL);

        if (i > 2) {
            assert(5 == deque_size(deque));
        } else {
            assert(6 == deque_size(deque));
        }
        if (i >= 3) {
            assert(i - 1 == deque_iter_index(&iter));
        }
        i++;
    }

    teardown_tests();
    return 0;
}
