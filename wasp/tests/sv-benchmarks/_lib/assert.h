#ifndef ASSERT_H
#define ASSERT_H

void assume(int);
void assert(int);
void *alloc(void *, unsigned int);
void dealloc(void *);
int is_symbolic(void *, unsigned int);

int    sym_int    (char*);
long long  sym_long   (char*);
float  sym_float  (char*);
double sym_double (char*);

#endif
