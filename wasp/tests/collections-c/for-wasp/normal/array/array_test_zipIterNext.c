#include "array.h"
#include "utils.h"
#include "mockups.h" 

static Array *v1;
static Array *v2;
static ArrayConf vc;
static int stat;

int main() {
    stat = array_new(&v1);

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

    array_add(v1, str_a);
    array_add(v1, str_b);
    array_add(v1, str_c);
    array_add(v1, str_d);

    array_new(&v2);

    array_add(v2, str_e);
    array_add(v2, str_f);
    array_add(v2, str_g);

    ArrayZipIter zip;
    array_zip_iter_init(&zip, v1, v2);

    size_t i = 0;

    void *e1, *e2;
    while (array_zip_iter_next(&zip, &e1, &e2) != CC_ITER_END) {
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
    array_destroy(v2);

    array_destroy(v1);

    return 0;
}
