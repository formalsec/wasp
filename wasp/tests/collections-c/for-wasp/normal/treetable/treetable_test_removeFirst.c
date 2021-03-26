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

    int d = dyn_sym_int32('d');

    char str_d[] = {d, '\0'};

    assume(x < y && y < z && z < w);

    treetable_add(table, &z, str_a);
    treetable_add(table, &w, str_b);
    treetable_add(table, &y, str_c);
    treetable_add(table, &x, str_d);

    treetable_remove_first(table, NULL);

    assert(0 == treetable_contains_key(table, &x));

    treetable_destroy(table);
}
