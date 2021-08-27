#include <mockups.h>

int __logand(int a, int b) {
  __asm__ __volatile__(
    "local.get 0;"
    "i32.const 0;"
    "i32.ne;"
    "local.get 1;"
    "i32.const 0;"
    "i32.ne;"
    "i32.and;"
    "return;"
  );
}

int __logor(int a, int b) {
  __asm__ __volatile__(
    "local.get 0;"
    "i32.const 0;"
    "i32.ne;"
    "local.get 1;"
    "i32.const 0;"
    "i32.ne;"
    "i32.or;"
    "return;"
  );
}

int IFG(int cond, int id) {
  return cond;
}

void test(int a, int b) {
  if (IFG(__logand(a, b), 1)) {
    assert(a);
  } else {
    if (IFG(!a, 2)) {}
    if (IFG(!b, 3)) {}
  }
  assert(__logor(__logor(a, __logand(!a,  b)), !b));
}

int main() {
  int a = sym_int("a");
  int b = sym_int("b");
  test(a, b);
  return 0;
}
