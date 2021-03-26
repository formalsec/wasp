#include "treetable.h"
#include "utils.h"
#include "mockups.h" 

static TreeTable *table;

int main() {
    treetable_new(cmp, &table);

    int x = dyn_sym_int32('x');
    int y = dyn_sym_int32('y');
    int z = dyn_sym_int32('z');

    assume(x < y && y < z);

    int a = dyn_sym_int32('a');

    char str_a[] = {a, '\0'};

    int b = dyn_sym_int32('b');

    char str_b[] = {b, '\0'};

    int c = dyn_sym_int32('c');

    char str_c[] = {c, '\0'};

    treetable_add(table, &x, str_a);
    treetable_add(table, &y, str_b);
    treetable_add(table, &z, str_c);

    TreeTableIter iter;
    treetable_iter_init(&iter, table);

    TreeTableEntry entry;
    while (treetable_iter_next(&iter, &entry) != CC_ITER_END) {
        int const *key = entry.key;

        if (*key == y) {
            assert(CC_OK == treetable_iter_remove(&iter, NULL));

            assert(CC_ERR_KEY_NOT_FOUND == treetable_iter_remove(&iter, NULL));
        }
    }

    assert(2 == treetable_size(table));
    assert(0 == treetable_contains_key(table, &y));

    treetable_destroy(table);
}
