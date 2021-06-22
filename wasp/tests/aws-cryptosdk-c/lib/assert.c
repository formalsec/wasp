#include "assert.h"

void assume(int expr) { /* EMPTY*/ }
void assert(int expr) { /* EMPTY*/ }
void *alloc(void *ptr, unsigned int size) { return ptr; }
void dealloc(void *ptr) {  }
int is_symbolic(void *sym_var, unsigned int length) { return 0; }


int    sym_int    (char *name)   { return (int)    0; }
long long  sym_long   (char *name)   { return (long long)   0; }
float  sym_float  (char *name)   { return (float)  0; }
double sym_double (char *name)   { return (double) 0; }

void __CPROVER_assume(int expr) { assume(expr); }
