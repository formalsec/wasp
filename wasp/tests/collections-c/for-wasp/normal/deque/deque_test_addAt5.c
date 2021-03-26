#include "deque.h"
#include "mockups.h" 

static Deque *deque;
static DequeConf conf;
int stat;

void setup_tests() { stat = deque_new(&deque); }

void teardown_tests() { deque_destroy(deque); }

int main() {
    setup_tests();

    int a = dyn_sym_int32('a');
    int b = dyn_sym_int32('b');
    int c = dyn_sym_int32('c');
    int d = dyn_sym_int32('d');
    int e = dyn_sym_int32('e');
    int f = dyn_sym_int32('f');
    int g = dyn_sym_int32('g');

    deque_add_last(deque, &a);
    deque_add_last(deque, &b);
    deque_add_last(deque, &c);
    deque_add_last(deque, &d);
    deque_add_last(deque, &e);
    deque_add_last(deque, &f);

    deque_add_at(deque, &g, 1);

    const void *const *buff = deque_get_buffer(deque);
    const int elem = *((int *)buff[7]);

    assert(elem == a);

    const int elem1 = *((int *)buff[0]);
    assert(elem1 == b);

    const int elem2 = *((int *)buff[5]);
    assert(elem2 == f);

    const int elem3 = *((int *)buff[1]);
    assert(elem3 == g);

    teardown_tests();
    return 0;
}
