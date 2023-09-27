#include "api.h"
#include "summ_utils.h"

/*
* Definition of Libc's function summaries
*
* The sufix number represents
* the precion degree of the summary
*
***************
*
* 	memchr()
*
****************/

//Does not evaluate symbolic bytes
char* memchr1(char* s, int c, int n){
	int i = 0;
	char chr = (char) c;

	//If length is symbolic maximizes to a concrete length
	if(summ_is_symbolic(&n,32)){
		n = summ_maximize(&n,32);
	}

	while(i < n) {
		
		if(!summ_is_symbolic(&s[i],8) && !summ_is_symbolic(&chr,8) && s[i] == chr){
			return &s[i];
		}

		i++;
	}
	return NULL;
}


char* memchr2(char* s, int c, int n){
	int i = 0;
	char chr = (char) c;

	//If length is symbolic maximizes to a concrete length
	if(summ_is_symbolic(&n,32)){

		int max = summ_maximize(&n, 32);
		restr_t maximize = _solver_EQ(&n, &max, 32);
		summ_assume(maximize);
		n = max;
	}

	while(i < n){
		if(summ_is_symbolic(&s[i],8) || summ_is_symbolic(&chr,8)){
			
			if(!_solver_is_it_possible(_solver_NEQ(&s[i], &chr, 8))){
				break;
			}
			
			else{
				summ_assume(_solver_NEQ(&s[i], &chr, 8));
			}
		}

		else if(s[i] == chr){
			return &s[i];
		}

		i++;
	}
	
	return NULL;
		
}


//Over-approx summary
//Return must be: retval >= s[0] or NULL
char* memchr3(char* s, int c){

	symbolic val = summ_new_sym_var(PTR_SIZE);
	
	void* null = NULL;
	void* ptr = &s[0];
	
	restr_t ptr_rstr = _solver_SGE(&val, &ptr, PTR_SIZE);
	restr_t null_rstr = _solver_EQ(&val, &null, PTR_SIZE);
	
	summ_assume(_solver_Or(ptr_rstr,null_rstr));

	return val;
}



char* memchr4(char* s, int c, int n){

	int i = 0;
	char chr = (char) c;
	char* val = 0;

	//If length is symbolic maximizes to a concrete length
	if(summ_is_symbolic(&n,32)){
		n = summ_maximize(&n,32);
	}

	//Initializes conditions
	restr_t sym_conds = summ_false();      //OR(False, restr)
	restr_t different_conds = summ_true(); //AND(True, restr)

	while(i < n){

		void* ptr = &s[i];
		
		//Either s[i] or chr are symbolic
		if(summ_is_symbolic(&s[i],8) || summ_is_symbolic(&chr,8)){

			if(_solver_is_it_possible(_solver_EQ(&s[i], &chr, 8))){

				if(!summ_is_symbolic(&val,PTR_SIZE)){
					val = summ_new_sym_var(PTR_SIZE);
				}

				restr_t equal = _solver_And(_solver_EQ(&s[i],&chr,8), _solver_EQ(&val,&ptr,PTR_SIZE));
				restr_t aux = _solver_And(equal,different_conds);
				sym_conds = _solver_Or(sym_conds,aux);
			}
			
			if(_solver_is_it_possible(_solver_NEQ(&s[i], &chr, 8))){
				restr_t not_equal_zero = _solver_NEQ(&s[i],&chr,8);
				different_conds = _solver_And(different_conds,not_equal_zero);
			}
			
			else{

				if(summ_is_symbolic(&val,PTR_SIZE)){
					summ_assume(sym_conds);
				}
				return val;
			}
		}

		//Found concrete chr
		else if(s[i] == chr){
			if(!summ_is_symbolic(&val,PTR_SIZE)){
				val = &s[i];	
			}

			else{
				different_conds = _solver_And(different_conds,_solver_EQ(&val,&ptr,PTR_SIZE));
				sym_conds = _solver_Or(sym_conds, different_conds);
			}

			if(summ_is_symbolic(&val,PTR_SIZE)){
				summ_assume(sym_conds);
			}

			return val;
		}
		
		i++;
	}

	//Char not found
	if(!summ_is_symbolic(&val,PTR_SIZE)){
		val = NULL;
	}
	else{
		void* null = NULL;
		different_conds = _solver_And(different_conds,_solver_EQ(&val,&null,PTR_SIZE));
		sym_conds = _solver_Or(sym_conds, different_conds);
	}


	if(summ_is_symbolic(&val,PTR_SIZE)){
		summ_assume(sym_conds);
	}

	//For testing
	//summ_print_restriction(sym_conds);
	
	return val;
}
