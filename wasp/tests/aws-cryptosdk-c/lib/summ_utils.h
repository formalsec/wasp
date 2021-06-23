#ifndef SUMM_UTILS_H_  
#define SUMM_UTILS_H_
#define STDIN 0

#define MAX(x, y) (((x) > (y)) ? (x) : (y))
#define MIN(x, y) (((x) < (y)) ? (x) : (y))



restr_t summ_true();
restr_t summ_false();
int _solver_must_be(restr_t restr);
int is_numeric(char c);

restr_t _solver_GE(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_GT(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_SGE(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t _solver_SGT(symbolic sym_var, symbolic sym_var2, unsigned int length);
restr_t sym_is_numeric(symbolic var);
int pow(int x, unsigned n);

restr_t equal_rstr(char* s1, char* s2, int n);
#endif 
