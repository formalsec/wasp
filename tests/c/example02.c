#include <wasp.h>

extern int __VERIFIER_nondet_int();

void test(int a, int b) {
  if (a && b) {
    __WASP_assert(a);
  } else {
    if (!a) {}
    if (!b) {}
  }
  __WASP_assert(a || (!a && b) || !b);
}

int main() {
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  test(a, b);
  return 0;
}
