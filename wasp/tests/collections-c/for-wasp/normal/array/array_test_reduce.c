#include "array.h"
#include "mockups.h" 

void reduce_add(void *e1, void *e2, void *result) {
    int el1 = e1 ? *((int *)e1) : 0;
    int el2 = e2 ? *((int *)e2) : 0;
    *((int *)result) = el1 + el2;
}

static Array *v1;
static Array *v2;
static ArrayConf vc;
static int stat;

int main() {
    stat = array_new(&v1);

    int a = dyn_sym_int32('a');
    int b = dyn_sym_int32('b');
    int c = dyn_sym_int32('c');
    int d = dyn_sym_int32('d');
    int e = dyn_sym_int32('e');
    int result;

    array_add(v1, &a);
    array_reduce(v1, reduce_add, (void *)&result);
    assert(a == result);

    array_add(v1, &b);
    array_reduce(v1, reduce_add, (void *)&result);
    assert(a + b == result);

    array_add(v1, &c);
    array_add(v1, &d);
    array_add(v1, &e);
    array_reduce(v1, reduce_add, (void *)&result);
    assert(a + b + c + d + e == result);

    array_destroy(v1);

    return 0;
}
