#ifndef API_H_  
#define API_H_

#include <wasp.h>


#define symbolic void*
#undef NULL
#define NULL (void*)0

#define INT_SIZE (sizeof(int) * 8)
#define LONG_SIZE (sizeof(long) * 8)
#define CHAR_SIZE (sizeof(char) * 8)
#define PTR_SIZE (sizeof(void*) * 8)

#define false 0

typedef unsigned long long restr_t;


void summ_not_implemented_error(char *fname);

void summ_print_byte(char byte);
void* summ_maximize(void* sym_var, unsigned int length);
int summ_is_symbolic(symbolic sym_var, unsigned int length);
symbolic summ_new_sym_var(unsigned int length);


void summ_assume(restr_t restr);

symbolic _solver_Concat(symbolic sym_var, symbolic sym_var2, unsigned int length1, unsigned int length2);
symbolic _solver_Extract(symbolic sym_var, unsigned int start, unsigned int end, unsigned int length);

symbolic _solver_ZeroExt(symbolic sym_var, unsigned int to_extend, unsigned int length);
symbolic _solver_SignExt(symbolic sym_var, unsigned int to_extend, unsigned int length);

void summ_print_restriction(restr_t restr);

restr_t _solver_NOT(restr_t restr1);
restr_t _solver_Or(restr_t restr1, restr_t restr2);
restr_t _solver_And(restr_t restr1, restr_t restr2);
restr_t _solver_EQ(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_NEQ(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_LT(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_LE(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_SLT(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_SLE(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_IF(restr_t restr, symbolic sym_var, symbolic sym_var2, unsigned int length);

int _solver_is_it_possible(restr_t restr);


#endif 
