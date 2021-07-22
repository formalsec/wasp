extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "test25-1.c", 3, "reach_error"); }
extern int __VERIFIER_nondet_int();

struct dummy {
  int a, b;
};

struct cont {
  struct dummy *array;
};

int check(struct cont *pc, int i)
{
  return pc->array[1].b == i;
}

int main()
{
  struct cont cont;
  struct dummy array[10];
  int i, *pa;
  i = __VERIFIER_nondet_int();

  for (int j = 0; j < 10; j++) {
    array[j].a = __VERIFIER_nondet_int();
    array[j].b = __VERIFIER_nondet_int();
  }

  if (i >= 0 && i < 9) {
    cont.array = &array[i];
    pa = &cont.array[0].b;
    if (cont.array[0].b > 0) {
      i =  array[i].b - 10;
      while (i < *pa) {
        ++i;
      }
      if (!check(&cont, i)) {
        goto ERROR;
      }
    }
  }

  return 0;

  ERROR: {reach_error();abort();}
  return 1;
}
