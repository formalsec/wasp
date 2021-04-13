#include "stack.h"
#include "mockups.h" 

static Stack *s;

void setup_tests() { stack_new(&s); }

void teardown_tests() { stack_destroy(s); }

int main() {
    setup_tests();

    int a = sym_int("a", 32);
    int b = sym_int("b", 32);
    int c = sym_int("c", 32);

    int *p;

    stack_push(s, (void *)&a);
    stack_peek(s, (void *)&p);
    assert(&a == p);

    stack_push(s, (void *)&b);
    stack_peek(s, (void *)&p);
    assert(&b == p);

    stack_push(s, (void *)&c);
    stack_peek(s, (void *)&p);
    assert(&c == p);

    teardown_tests();
    return 0;
}
