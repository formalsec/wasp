#include <wasp.h>

int main() {
  int a = __WASP_symb_int("a");
  int b;

  if (a > 0) {
    b = a + 1;
    __WASP_assert(b > 0);
  }

  return 0;

}
