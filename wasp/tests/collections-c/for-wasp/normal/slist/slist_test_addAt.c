#include "slist.h"
#include "mockups.h" 

static SList *list;
static SList *list2;
static int stat;

int a, b, c, d, e, f, g, h;

void setup_test() {
    slist_new(&list), slist_new(&list2);

    a = sym_int("a", 32);
    b = sym_int("b", 32);
    c = sym_int("c", 32);
    d = sym_int("d", 32);
    e = sym_int("e", 32);
    f = sym_int("f", 32);
    g = sym_int("g", 32);
    h = sym_int("h", 32);

    int *va = (int *)malloc(sizeof(int));
    int *vb = (int *)malloc(sizeof(int));
    int *vc = (int *)malloc(sizeof(int));
    int *vd = (int *)malloc(sizeof(int));

    *va = a;
    *vb = b;
    *vc = c;
    *vd = d;

    slist_add(list, va);
    slist_add(list, vb);
    slist_add(list, vc);
    slist_add(list, vd);

    va = (int *)malloc(sizeof(int));
    vb = (int *)malloc(sizeof(int));
    vc = (int *)malloc(sizeof(int));
    vd = (int *)malloc(sizeof(int));

    *va = e;
    *vb = f;
    *vc = g;
    *vd = h;

    slist_add(list2, va);
    slist_add(list2, vb);
    slist_add(list2, vc);
    slist_add(list2, vd);
};

void teardown_test() {
    slist_destroy(list);
    slist_destroy(list2);
};

int main() {
    setup_test();

    int i = sym_int("i", 32);
    int *ii = (int *)malloc(sizeof(int));

    *ii = i;

    slist_add_at(list, ii, 2);
    assert(5 == slist_size(list));

    int *new;
    slist_get_at(list, 2, (void *)&new);
    assert(*ii == *new);
    assert(CC_OK == slist_add_at(list, ii, 4));
    assert(CC_OK == slist_add_at(list, ii, 0));

    void *el;
    slist_get_first(list, &el);
    assert(*ii == *((int *)el));

    slist_get_first(list, &el);
    assert(*ii == *((int *)el));

    teardown_test();
    return 0;
}
