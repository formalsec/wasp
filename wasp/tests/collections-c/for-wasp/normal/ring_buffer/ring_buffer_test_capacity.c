#include "ring_buffer.h"
#include "utils.h"
#include "mockups.h" 

static int stat;
static Rbuf *rbuf;

void setup_test() { stat = rbuf_new(&rbuf); }

void teardown_test() { rbuf_destroy(rbuf); }

int main() {
    setup_test();

    uint64_t items[10];
    int a = sym_int("a", 32);
    char str_a[] = {a, '\0'};

    int b = sym_int("b", 32);
    char str_b[] = {b, '\0'};

    int c = sym_int("c", 32);
    char str_c[] = {c, '\0'};

    int d = sym_int("d", 32);
    char str_d[] = {d, '\0'};

    int e = sym_int("e", 32);
    char str_e[] = {e, '\0'};

    int f = sym_int("f", 32);
    char str_f[] = {f, '\0'};

    int g = sym_int("g", 32);
    char str_g[] = {g, '\0'};

    int h = sym_int("h", 32);
    char str_h[] = {h, '\0'};

    int i = sym_int("i", 32);
    char str_i[] = {i, '\0'};

    int j = sym_int("j", 32);
    char str_j[] = {j, '\0'};
    rbuf_enqueue(rbuf, a);
    rbuf_enqueue(rbuf, b);
    rbuf_enqueue(rbuf, c);
    rbuf_enqueue(rbuf, d);
    rbuf_enqueue(rbuf, e);
    rbuf_enqueue(rbuf, f);
    rbuf_enqueue(rbuf, g);
    rbuf_enqueue(rbuf, h);
    rbuf_enqueue(rbuf, i);
    rbuf_enqueue(rbuf, j);
    memset(items, 0, sizeof(uint64_t) * 10);
    items[0] = a;
    items[1] = b;
    items[2] = c;
    items[3] = d;
    items[4] = e;
    items[5] = f;
    items[6] = g;
    items[7] = h;
    items[8] = i;
    items[9] = j;

    assert(items[0] == rbuf_peek(rbuf, 0));
    assert(items[1] == rbuf_peek(rbuf, 1));

    int x = sym_int("x", 32);
    char str_x[] = {x, '\0'};

    int y = sym_int("y", 32);
    char str_y[] = {y, '\0'};

    rbuf_enqueue(rbuf, str_x);
    rbuf_enqueue(rbuf, str_y);

    assert(rbuf_peek(rbuf, 0) == str_x);
    assert(rbuf_peek(rbuf, 1) == str_y);
    uint64_t out;
    rbuf_dequeue(rbuf, &out);
    assert(items[2] == out);

    teardown_test();
    return 0;
}
