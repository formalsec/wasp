#include "wasp.h"

/* memory operations */
void *__WASP_alloc(void *ptr, unsigned int sz) {
  return ptr;
}
void __WASP_dealloc(void *ptr) { }

/* symbolic values */
int __WASP_symb_int(char *name) {
  return (int)0;
}
long long __WASP_symb_long(char *name) {
  return (long long)0;
}
float __WASP_symb_float(char *name) {
  return (float)0;
}
double __WASP_symb_double(char *name) {
  return (double)0;
}

/* symbolic variable manipulation */
#ifndef assume
void assume(int expr) { return __WASP_assume(expr); }
#endif

void __WASP_assume(int expr) { }
void __WASP_assert(int expr) { }
int __WASP_is_symbolic(void *var, unsigned int sz) {
  return 0;
}

int __WASP_print_stack(int a) {
  return 0;
}

void __WASP_print_pc() {

}

/* special boolean ops */
int and_(int a, int b) {
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

int or_(int a, int b) {
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

int ite(int cond, int a, int b) {
  return cond ? a : b;
}
