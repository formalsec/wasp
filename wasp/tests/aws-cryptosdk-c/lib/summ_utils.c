/**
Defines Util functions
**/

#include "api.h"

//Simple "True" restriction
restr_t summ_true(){

	int one1 = 1;
	int one2 = 1;

	restr_t _true = _solver_EQ(&one1, &one2, 32);
	return _true;
}

//Simple "False" restriction
restr_t summ_false(){

	int one1 = 1;
	int one2 = 1;

	restr_t _false = _solver_NEQ(&one1, &one2, 32);
	return _false;
}


//Restriction must be asserted
int _solver_must_be(restr_t restr){
	return !_solver_is_it_possible(_solver_NOT(restr));
}

//Concrete char is numeric
int is_numeric(char c){
	return (c >= '0' && c <= '9')? 1 : 0;
}


restr_t _solver_GE(symbolic sym_var, symbolic sym_var2, unsigned int length){
	return _solver_NOT(_solver_LT(sym_var, sym_var2, length));
}

restr_t _solver_GT(symbolic sym_var, symbolic sym_var2, unsigned int length){
	return _solver_NOT(_solver_LE(sym_var, sym_var2, length));
}

restr_t _solver_SGE(symbolic sym_var, symbolic sym_var2, unsigned int length){
	return _solver_NOT(_solver_SLT(sym_var, sym_var2, length));
}

restr_t _solver_SGT(symbolic sym_var, symbolic sym_var2, unsigned int length){
	return _solver_NOT(_solver_SLE(sym_var, sym_var2, length));
}


//Symbolic char is numeric 0 >= sym <= 9
restr_t sym_is_numeric(symbolic var){
	char char_zero = '0';
	char char_nine = '9';

	restr_t _GE_zero = _solver_GE(var, &char_zero, 8);
	restr_t _LE_nine = _solver_LE(var, &char_nine, 8);

	return _solver_And(_GE_zero, _LE_nine);
}


int pow(int x, unsigned n){
	int pow = 1;
	while (n)
	{
		if (n & 1)
			pow *= x;

		n = n >> 1;
		x = x * x;
	}
	return pow;
}