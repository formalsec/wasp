#include "api.h"
#include "summ_utils.h"
#include "strlen.h"

/*
* Definition of Libc's function summaries
*
* The sufix number represents
* the precion degree of the summary
*
***************
*
* 	strcmp()
*
****************/

//Only compares concrete bytes
int strcmp1(char* s1, char* s2){
	int size1 = strlen1(s1);
	int size2 = strlen1(s2);

	//If sizes differ return imediatly
	if(size1 != size2){
		return 1;
	}

	for(int i = 0; i < size1; i++){
		char c1 = s1[i];
		char c2 = s2[i];

		//Lazy evaluation for SE optimization  
		if(!summ_is_symbolic(&c1,8) && !summ_is_symbolic(&c2,8) && c1 != c2){
			return c1-c2;
		}
	}
	return 0;
}




int strcmp2(char* s1, char* s2){

	int canBeDifferent = 0;
	int canBeEqual = 1;

	//Initializes condition with true
	restr_t equal_conds_restr = summ_true();


	char char_zero = '\0';

	int size1 = strlen1(s1);
	int size2 = strlen1(s2);

	if(size1 < size2 && (!summ_is_symbolic(&s2[size1],8) || 
	!_solver_is_it_possible(_solver_EQ(&s2[size1], &char_zero, 8)))){

		canBeDifferent = 1;
		canBeEqual = 0;
	}

	else if(size1 > size2 && (!summ_is_symbolic(&s1[size2],8) ||
	!_solver_is_it_possible(_solver_EQ(&s1[size2], &char_zero, 8)))){

		canBeDifferent = 1;
		canBeEqual = 0;
	}

	else{

		int sz = MIN(size1,size2);

		for(int i = 0; i < sz; i++){
			char c1 = s1[i];
			char c2 = s2[i];

			//Both chars are concrete and different 
			if(!summ_is_symbolic(&s1[i],8) && !summ_is_symbolic(&s2[i],8) && c1 != c2){
				canBeEqual = 0;
				canBeDifferent = 1;
                break;
			}

			else{
				
				restr_t c1_equals_c2 = _solver_EQ(&c1, &c2, 8);
				restr_t c1_not_equals_c2 = _solver_NEQ(&c1, &c2, 8);

				// c1 == c2
				if(!_solver_is_it_possible(c1_equals_c2)){
					canBeEqual = 0;
					canBeDifferent = 1;
					break;
				}

				else{
					
					// c1 != c2
					if(_solver_is_it_possible(c1_not_equals_c2)){
						canBeDifferent = 1;
					}
					canBeEqual = 1;
					equal_conds_restr = _solver_And(equal_conds_restr, c1_equals_c2);
				}

			}
		}
	}

	

	if(canBeDifferent && canBeEqual){

		symbolic val = summ_new_sym_var(32);

		int zero = 0;
		int one = 1;

		restr_t val_equals_zero = _solver_EQ(&val, &zero, 32);
		restr_t val_equals_one = _solver_EQ(&val, &one, 32);

		equal_conds_restr = _solver_And(equal_conds_restr, val_equals_zero);
		equal_conds_restr = _solver_Or(equal_conds_restr, val_equals_one);

		//For testing
		//summ_print_restriction(equal_conds_restr);


		//Either all chars are equal and val == 0 OR val == 1
		summ_assume(equal_conds_restr);
		return val;
	}

	//If strings can only be different
	else if(canBeDifferent){
		return 1;
	}

	//If strings can only be equal
	else if(canBeEqual){
		return 0;
	}
	
	return -1;

}


int strcmp3(char* s1, char* s2){

	int canBeEqual = 1;
	int canBeLower = 0;
	int canBeGreater = 0;

	//Initializes condition with true
	restr_t equal_conds_restr = summ_true();


	char char_zero = '\0';

	int size1 = strlen1(s1);
	int size2 = strlen1(s2);

	if(size1 < size2 && (!summ_is_symbolic(&s2[size1],8) ||
	!_solver_is_it_possible(_solver_EQ(&s2[size1], &char_zero, 8)))){
		canBeEqual = 0;
	}

	else if(size1 > size2 && (!summ_is_symbolic(&s1[size2],8) ||
	!_solver_is_it_possible(_solver_EQ(&s1[size2], &char_zero, 8)))){
		canBeEqual = 0;
	}


	int sz = MIN(size1,size2);

	for(int i = 0; i < sz; i++){
		char c1 = s1[i];
		char c2 = s2[i];

		//Both chars are concrete and different 
		if(!summ_is_symbolic(&s1[i],8) && !summ_is_symbolic(&s2[i],8) && c1 != c2){
			return c1 - c2;
		}

		//At least one char is symbolic
		else if (summ_is_symbolic(&s1[i],8) || summ_is_symbolic(&s2[i],8)){

			restr_t c1_equals_c2 = _solver_EQ(&c1, &c2, 8); 	 // c1 == c2			
			restr_t c1_lt_c2 = _solver_LT(&c1, &c2, 8); 		 // c1 < c2
			restr_t c1_gt_c2 = _solver_GT(&c1, &c2, 8); 		 // c1 > c2

			//Strings can still be equal
			if(canBeEqual){

				if(!_solver_is_it_possible(c1_equals_c2)){
					canBeEqual = 0;
				}
				else{

					equal_conds_restr = _solver_And(equal_conds_restr, c1_equals_c2);
				}
			}

			//Strings can still be lower or greater
			if(canBeLower == canBeGreater){

					if(_solver_is_it_possible(c1_lt_c2)){
						canBeLower = 1;
					}
					else{canBeLower = 0;}

					if(_solver_is_it_possible(c1_gt_c2)){
						canBeGreater = 1;
					}
					else{canBeGreater = 0;}
			}
		}
	}
	

	symbolic val = summ_new_sym_var(32);
	int zero = 0;
	int one = 1;

	restr_t val_equals_zero = _solver_EQ(&val, &zero, 32);
	restr_t val_equals_one = _solver_EQ(&val, &one, 32);
	restr_t val_lower_zero = _solver_SLT(&val, &zero, 32);

	if(canBeEqual && canBeLower && canBeGreater){

		equal_conds_restr = _solver_And(equal_conds_restr, val_equals_zero);
		equal_conds_restr = _solver_Or(equal_conds_restr, val_equals_one);
		equal_conds_restr = _solver_Or(equal_conds_restr, val_lower_zero);

		//For testing
		//summ_print_restriction(equal_conds_restr);


		//Either all chars are equal and val == 0 OR val < 0 or val == 1
		summ_assume(equal_conds_restr);
		return val;
	}

	else if(!canBeEqual && canBeLower && canBeGreater){

		restr_t val_restr = _solver_Or(val_equals_one, val_lower_zero);

		//For testing
		//summ_print_restriction(val_restr);
		
		//Either val == -1 or val == 1
		summ_assume(val_restr);	
		return val;
	}

	//If can only be lower
	else if(canBeLower){
		return -1;
	}

	//If can only be greater
	else if(canBeGreater){
		return 1;
	}

	//If strings can only be equal
	return 0;
	

}

