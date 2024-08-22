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

unsigned int swap(unsigned int x) {
  union { unsigned int i; char c[4]; } src, dst;

  src.i = x;
  dst.c[3] = src.c[0], dst.c[2] = src.c[1];
  dst.c[1] = src.c[2], dst.c[0] = src.c[3];
  return dst.i;
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

void test1(int a, int b) {
  if (a && b) {
    test(a, b);
  } else {
    IFG(!a || !b, 4);
  }
}

int main() {
  int a = sym_int("a");
  int b = sym_int("b");
  test(a, b);
  return 0;
}
