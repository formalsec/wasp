#include <wasp.h>

int main() {
  int a = __WASP_symb_int("a");
  __WASP_assume(a > 0);

  int b = __WASP_symb_int("b");
  __WASP_assume(b == a + 1);

  __WASP_assert(b > 0);
  return 0;
}
