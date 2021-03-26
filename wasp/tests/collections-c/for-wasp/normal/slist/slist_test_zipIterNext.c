#include "slist.h"
#include "utils.h"
#include "mockups.h" 

static SList *list;
static SList *list2;
static int stat;

void setup_test() {
    stat = slist_new(&list);
    slist_new(&list2);
};

void teardown_test() {
    slist_destroy(list);
    slist_destroy(list2);
};

int main() {
    setup_test();

    int a = dyn_sym_int32('a');
    assume(a > 0); assume(a < 127);
    char str_a[] = {a, '\0'};

    int b = dyn_sym_int32('b');
    assume(b > 0); assume(b < 127);
    char str_b[] = {b, '\0'};

    int c = dyn_sym_int32('c');
    assume(c > 0); assume(c < 127);
    char str_c[] = {c, '\0'};

    int d = dyn_sym_int32('d');
    assume(d > 0); assume(d < 127);
    char str_d[] = {d, '\0'};

    int e = dyn_sym_int32('e');
    assume(e > 0); assume(e < 127);
    char str_e[] = {e, '\0'};

    int f = dyn_sym_int32('f');
    assume(f > 0); assume(f < 127);
    char str_f[] = {f, '\0'};

    int g = dyn_sym_int32('g');
    assume(g > 0); assume(g < 127);
    char str_g[] = {g, '\0'};

    slist_add(list, str_a);
    slist_add(list, str_b);
    slist_add(list, str_c);
    slist_add(list, str_d);

    slist_add(list2, str_e);
    slist_add(list2, str_f);
    slist_add(list2, str_g);

    SListZipIter zip;
    slist_zip_iter_init(&zip, list, list2);

    size_t i = 0;

    void *e1, *e2;
    while (slist_zip_iter_next(&zip, &e1, &e2) != CC_ITER_END) {
        if (i == 0) {
            CHECK_EQUAL_C_STRING(str_a, (char *)e1);
            CHECK_EQUAL_C_STRING(str_e, (char *)e2);
        }
        if (i == 2) {
            CHECK_EQUAL_C_STRING(str_c, (char *)e1);
            CHECK_EQUAL_C_STRING(str_g, (char *)e2);
        }
        i++;
    }
    assert(3 == i);

    teardown_test();
    return 0;
}
