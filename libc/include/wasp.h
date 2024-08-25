#ifndef _WASP_H
#define _WASP_H

/* memory operations */
void *__WASP_alloc(void*, unsigned int);
void  __WASP_dealloc(void*);

/* symbolic values */
int       __WASP_symb_int(char *);
long long __WASP_symb_long(char *);
float     __WASP_symb_float(char *);
double    __WASP_symb_double(char *);

/* symbolic variable manipulation */

#ifndef assume
void assume(int);
#endif

void __WASP_assume(int);
void __WASP_assert(int);
int  __WASP_is_symbolic(void *, unsigned int);

/* debug operations*/
int  __WASP_print_stack(int);
void __WASP_print_pc();

/* special boolean ops */
int and_(int, int);
int or_(int, int);
int ite(int, int, int);

#endif
