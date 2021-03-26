#include "treetable.h"
#include "utils.h"
#include "mockups.h" 

static TreeTable *table;

int main() {
    treetable_new(cmp, &table);

    int x = dyn_sym_int32('x');
    int y = dyn_sym_int32('y');
    int z = dyn_sym_int32('z');
    int w = dyn_sym_int32('w');

    int a = dyn_sym_int32('a');

    char str_a[] = {a, '\0'};

    int b = dyn_sym_int32('b');

    char str_b[] = {b, '\0'};

    int c = dyn_sym_int32('c');

    char str_c[] = {c, '\0'};

    assume(z != x && z != y);

    treetable_add(table, &x, str_a);
    treetable_add(table, &y, str_b);
    treetable_add(table, &z, str_c);

    treetable_remove(table, &z, NULL);

    assert(0 == treetable_contains_key(table, &z));

    treetable_destroy(table);
}
