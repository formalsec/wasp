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
* 	memcmp()
*
****************/

//Only compares concrete bytes
int memcmp1(void* s1, void* s2, int n){

	//If length is symbolic maximizes to a concrete length
	if(summ_is_symbolic(&n,32)){

		n = summ_maximize(&n, 32);
	}

	unsigned char *str1 = (unsigned char*) s1;
	unsigned char *str2 = (unsigned char*) s2;

	for(int i = 0; i < n; i++){

		unsigned char c1 = *(str1 + i);
		unsigned char c2 = *(str2 + i);

		//Lazy evaluation for SE optimization  
		if(!summ_is_symbolic(&c1,8) && !summ_is_symbolic(&c2,8) && c1 != c2){
			return c1-c2;
		}
	}
	return 0;
}


int memcmp2(void* s1, void* s2, int n){

	int canBeDifferent = 0;
	int canBeEqual = 1;

	//Initializes condition with true
	restr_t equal_conds_restr = summ_true();

	//If length is symbolic maximizes to a concrete length
	if(summ_is_symbolic(&n,32)){

		n = summ_maximize(&n, 32);
	}

	unsigned char *str1 = (unsigned char*) s1;
	unsigned char *str2 = (unsigned char*) s2;


	for(int i = 0; i < n; i++){

		unsigned char c1 = *(str1 + i);
		unsigned char c2 = *(str2 + i);

		//Both chars are concrete and different 
		if(!summ_is_symbolic(&str1[i],8) && !summ_is_symbolic(&str2[i],8) && c1 != c2){
			canBeEqual = 0;
			canBeDifferent = 1;
            break;
		}

		else{

			// c1 == c2
			restr_t c1_equals_c2 = _solver_EQ(&c1, &c2, 8);

			// c1 != c2
			restr_t c1_not_equals_c2 = _solver_NEQ(&c1, &c2, 8);

			if(!_solver_is_it_possible(c1_equals_c2)){
				canBeEqual = 0;
				canBeDifferent = 1;
				break;
			}

			else{
				
				if(_solver_is_it_possible(c1_not_equals_c2)){
					canBeDifferent = 1;
				}
				canBeEqual = 1;
				equal_conds_restr = _solver_And(equal_conds_restr, c1_equals_c2);
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



int memcmp3(char* s1, char* s2, int n){

	int canBeEqual = 1;
	int canBeLower = 0;
	int canBeGreater = 0;

	//Initializes condition with true
	restr_t equal_conds_restr = summ_true();


	if(summ_is_symbolic(&n, 32)){
		n = summ_maximize(&n, 32);
	}

	unsigned char *str1 = (unsigned char*) s1;
	unsigned char *str2 = (unsigned char*) s2;


	for(int i = 0; i < n; i++){

		unsigned char c1 = *(str1 + i);
		unsigned char c2 = *(str2 + i);	

		//Both chars are concrete and different 
		if(!summ_is_symbolic(&s1[i],8) && !summ_is_symbolic(&s2[i],8) && c1 != c2){
			return c1 - c2;
		}

		else if (summ_is_symbolic(&s1[i],8) || summ_is_symbolic(&s2[i],8)){

			restr_t c1_equals_c2 = _solver_EQ(&c1, &c2, 8); 	 // c1 == c2			
			restr_t c1_lt_c2 = _solver_LT(&c1, &c2, 8); 		 // c1 < c2
			restr_t c1_gt_c2 = _solver_GT(&c1, &c2, 8); 		 // c1 > c2

			
			if(canBeEqual){

				if(!_solver_is_it_possible(c1_equals_c2)){
					canBeEqual = 0;
				}
				else{

					equal_conds_restr = _solver_And(equal_conds_restr, c1_equals_c2);
				}
			}

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
	//int minus_one = -1;

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


//Over-approx summary
//Cuts out the wrong path -> all chars are equal and return != 0
int memcmp4(char* s1, char* s2, int n){
	
	int zero = 0;
	symbolic val = summ_new_sym_var(32);

	int size1 = strlen1(s1);
	int size2 = strlen1(s2);

	if(summ_is_symbolic(&n, 32)){
		n = summ_maximize(&n, 32);
	}

	size1 = MIN(size1,n);
	size2 = MIN(size2,n);
	int sz = MIN(size1,size2);	

	restr_t path;
	restr_t eq = equal_rstr(s1, s2, sz+1);
	restr_t zero_restr = _solver_EQ(&val, &zero, 32);
	
	path = _solver_NOT(eq);
	path = _solver_Or(path, zero_restr);

	summ_assume(path);

	return val; 
}

