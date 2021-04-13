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

    int r = sym_int("r", 32);
    assume(r != c);
    array_add(v1, &a);
    array_add(v1, &b);
    array_add(v1, &c);

    array_replace_at(v1, &r, 2, NULL);

    int *repl;
    array_get_at(v1, 2, (void *)&repl);

    assert(*repl != c);
    assert(*repl == r);

    array_destroy(v1);

    return 0;
}
