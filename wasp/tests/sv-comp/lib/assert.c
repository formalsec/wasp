#include "assert.h"

void assume(int expr) { /* EMPTY*/ }
void assert(int expr) { /* EMPTY*/ }

int    sym_int    (char *name)   { return (int)    0; }
long long  sym_long   (char *name)   { return (long long)   0; }
float  sym_float  (char *name)   { return (float)  0; }
double sym_double (char *name)   { return (double) 0; }
