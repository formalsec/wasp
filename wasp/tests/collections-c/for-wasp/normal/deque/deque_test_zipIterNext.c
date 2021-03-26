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

    int a = dyn_sym_int32('a');
    char str_a[] = {a, '\0'};

    int b = dyn_sym_int32('b');
    char str_b[] = {b, '\0'};

    int c = dyn_sym_int32('c');
    char str_c[] = {c, '\0'};

    int d = dyn_sym_int32('d');
    char str_d[] = {d, '\0'};

    int e = dyn_sym_int32('e');
    char str_e[] = {e, '\0'};

    int f = dyn_sym_int32('f');
    char str_f[] = {f, '\0'};

    int g = dyn_sym_int32('g');
    char str_g[] = {g, '\0'};

    assume(b != a && b != c && b != d);

    deque_add(deque, str_a);
    deque_add(deque, str_b);
    deque_add(deque, str_c);
    deque_add(deque, str_d);

    Deque *d2;
    deque_new(&d2);

    deque_add(d2, str_e);
    deque_add(d2, str_f);
    deque_add(d2, str_g);

    DequeZipIter zip;
    deque_zip_iter_init(&zip, deque, d2);

    size_t i = 0;

    void *e1, *e2;
    while (deque_zip_iter_next(&zip, &e1, &e2) != CC_ITER_END) {
        if (i == 0) {
            assert(strcmp(str_a, (char *)e1) == 0);
            assert(strcmp(str_e, (char *)e2) == 0);
        }
        if (i == 2) {
            assert(strcmp(str_c, (char *)e1) == 0);
            assert(strcmp(str_g, (char *)e2) == 0);
        }
        i++;
    }
    assert(3 == i);
    deque_destroy(d2);

    teardown_tests();
    return 0;
}
