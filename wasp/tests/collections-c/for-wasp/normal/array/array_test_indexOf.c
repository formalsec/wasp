#include "array.h"
#include "mockups.h" 

static Array *v1;
static Array *v2;
static ArrayConf vc;
static int stat;

int main() {
    stat = array_new(&v1);

    int a = sym_int("a", 32);
    int b = sym_int("b", 32);
    int c = sym_int("c", 32);

    array_add(v1, &a);
    array_add(v1, &b);
    array_add(v1, &c);

    size_t ai;
    array_index_of(v1, &a, &ai);

    size_t ci;
    array_index_of(v1, &c, &ci);

    assert(0 == ai);
    assert(2 == ci);

    array_destroy(v1);

    return 0;
}
