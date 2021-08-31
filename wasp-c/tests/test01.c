#include <wasp.h>

int IFG(int cond, int id) {
  return cond;
}

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
  int a = __WASP_symb_int("a");
  int b = __WASP_symb_int("b");
  test(a, b);
  return 0;
}
