#include "list.h"
#include "mockups.h" 

static List *list1;
static List *list2;

void setup_tests() { list_new(&list1), list_new(&list2); }

void teardown_test() {
    list_destroy(list1);
    list_destroy(list2);
}

int main() {
    setup_tests();

    int a = dyn_sym_int32('a');
    int b = dyn_sym_int32('b');
    int c = dyn_sym_int32('c');
    int d = dyn_sym_int32('d');
    int e = dyn_sym_int32('e');

    assume(a != b && a != c && a != d && a != e && b != c && b != d && b != e &&
           c != d && c != e && d != e);

    list_add(list1, &a);
    list_add(list1, &b);
    list_add(list1, &b);
    list_add(list1, &c);
    list_add(list1, &d);

    assert(2 == list_contains(list1, &b));
    assert(1 == list_contains(list1, &d));
    assert(0 == list_contains(list1, &e));

    teardown_test();
}
