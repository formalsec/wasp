#include "treetable.h"
#include "utils.h"
#include "mockups.h" 

static TreeTable *table;

int main() {
    treetable_new(cmp, &table);

    int x = sym_int("x", 32);
    int y = sym_int("y", 32);
    int z = sym_int("z", 32);
    int w = sym_int("w", 32);

    int a = sym_int("a", 32);

    char str_a[] = {a, '\0'};

    int b = sym_int("b", 32);

    char str_b[] = {b, '\0'};

    int c = sym_int("c", 32);

    char str_c[] = {c, '\0'};

    int d = sym_int("d", 32);

    char str_d[] = {d, '\0'};

    assume(x < y && y < z && z < w);

    treetable_add(table, &z, str_a);
    treetable_add(table, &w, str_b);
    treetable_add(table, &y, str_c);
    treetable_add(table, &x, str_d);

    int *g;
    treetable_get_lesser_than(table, &y, (void *)&g);

    assert(x == *g);

    treetable_destroy(table);
}
