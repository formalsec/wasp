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

    deque_add_at(deque, &g, 4);

    const void *const *buff = deque_get_buffer(deque);

    assert(buff[4] == &g);

    assert(buff[5] == &e);

    const void *elem = buff[6];
    assert(elem == &f);

    teardown_tests();
    return 0;
}
