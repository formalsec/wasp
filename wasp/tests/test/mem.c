#include "mockups.h"

extern unsigned char __heap_base;
unsigned int bump_pointer = &__heap_base;

void *malloc(unsigned int size)
{
  unsigned int r = bump_pointer;
  bump_pointer += size;
  return (void*)r;
}

union aux {
  unsigned int i;
  char c[4];
};


unsigned int stack_swap(unsigned int x)
{
  union {unsigned int i; char c[4];} src, dst;

  src.i = x;
  dst.c[3] = src.c[0], dst.c[2] = src.c[1];
  dst.c[1] = src.c[2], dst.c[0] = src.c[3];
  return dst.i;
}

void heap_swap(union aux *t1, union aux *t2, unsigned int x)
{
  t1->i = x;
  t2->c[3] = t1->c[0], t2->c[2] = t1->c[1];
  t2->c[1] = t1->c[2], t2->c[0] = t1->c[3];
}

int start() {
  unsigned int db = 3735928559;
  unsigned int bd = 4022250974;

  int x = dyn_sym_int32('x');
  assume (x == bd);

  // TEST 1 - stack swap (bvops)
  int x_prime = stack_swap(x);
  assert (x_prime == db);

  // TEST 2 - heap swap
  union aux *t1,*t2;
  t1 = (union aux *)malloc(sizeof(union aux));
  t2 = (union aux *)malloc(sizeof(union aux));
 
  heap_swap(t1, t2, x);
  x_prime = t2->i;
  assert (x_prime == db);

  return sizeof(void*);
}
