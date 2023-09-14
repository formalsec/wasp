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
* 	strlen()
*
****************/


//Does not evaluates symbolic bytes
int strlen1(char* s){
	int i = 0;
	while(summ_is_symbolic(&s[i],8) || !(summ_is_symbolic(&s[i],8) == 0 && s[i] == '\0')){
		i++;
	}
	return i;
}


int strlen2(char* s){
	int i = 0;
	char zero = '\0';

	while(1){
		if(summ_is_symbolic(&s[i],8)){
			
			if(!_solver_is_it_possible(_solver_NEQ(&s[i], &zero, 8))){
				break;
			}
			
			else{
				summ_assume(_solver_NEQ(&s[i], &zero, 8));
			}
		}
		else if(s[i] == '\0'){
			break;
		}
		
		i++;
	}
	return i;
}


int strlen3(char* s){

	int i = 0;
	char zero = '\0';
	int val = 0;

	//Initializes conditions
	restr_t sym_conds = summ_false();      //OR(False, restr)
	restr_t different_conds = summ_true(); //AND(True, restr)

	while(1){
		if(summ_is_symbolic(&s[i],8)){

			if(_solver_is_it_possible(_solver_EQ(&s[i], &zero, 8))){

				if(!summ_is_symbolic(&val,32)){
					val = summ_new_sym_var(32);
				}
				restr_t equal_zero = _solver_And(_solver_EQ(&s[i],&zero,8), _solver_EQ(&val,&i,32));
				restr_t aux = _solver_And(equal_zero,different_conds);
				sym_conds = _solver_Or(sym_conds,aux);
			}
			
			if(_solver_is_it_possible(_solver_NEQ(&s[i], &zero, 8))){
				restr_t not_equal_zero = _solver_NEQ(&s[i],&zero,8);
				different_conds = _solver_And(different_conds,not_equal_zero);
			}
			
			else{

				break;
			}
		}
		else if(s[i] == '\0'){
			if(!summ_is_symbolic(&val,32)){
				val = i;
			}
			else{
				different_conds = _solver_And(different_conds,_solver_EQ(&val,&i,32));
				sym_conds = _solver_Or(sym_conds, different_conds);
			}
			break;
		}
		
		i++;
	}

	if(summ_is_symbolic(&val,32)){
		summ_assume(sym_conds);
	}

	return val;
}
