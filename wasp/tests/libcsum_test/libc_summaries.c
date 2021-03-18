#include "api.h"
#include "utils.h"
/*
* Definition of Libc's functions summaries
*
* The number sufix in some functions represents
* the precion degree of the summary
*
* E.g strcmp2 is finer than strcmp1
*/



/***************
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


/*
* Wrapper for strlen()
*/
int strlen(char * s){
  return strlen1(s);
  //return strlen2(s);
}



/***************
*
* 	strncmp()
*
****************/

//Only compares concrete bytes
int strncmp1(char* s1, char* s2, int n){

	int size1 = strlen(s1);
	int size2 = strlen(s2);

	if(summ_is_symbolic(&n, 32)){
		n = summ_maximize(&n, 32);
	}

	size1 = MIN(size1,n);
	size2 = MIN(size2,n);

	if(size1 != size2){
		return 1;
	}

	int i;
	for(i = 0; i < size1; i++){
		char c1 = s1[i];
		char c2 = s2[i];


		//Lazy evaluation for SE optimization  
		if(summ_is_symbolic(&c1,8) == 0 && summ_is_symbolic(&c2,8) == 0 && c1 != c2){
			return 1;
		}
	}
	return 0;
}

int strncmp2(char* s1, char* s2, int n){

	int canBeDifferent = 0;
	int canBeEqual = 1;

	//Initializes condition with true
	restr_t equal_conds_restr = summ_true();


	char char_zero = '\0';

	int size1 = strlen(s1);
	int size2 = strlen(s2);

	//If sizes are symbolic maximizes to a concrete length
	if(summ_is_symbolic(&size1,32)){
		size1 = summ_maximize(&size1, 32);
	}
	if(summ_is_symbolic(&size2,32)){
		size2 = summ_maximize(&size2, 32);
	}
	if(summ_is_symbolic(&n, 32)){
		n = summ_maximize(&n, 32);
	}


	size1 = MIN(size1,n);
	size2 = MIN(size2,n);


	if(size1 < size2 && (!summ_is_symbolic(&s2[size1],8) || !_solver_is_it_possible(_solver_EQ(&s2[size1], &char_zero, 8)))){
		canBeDifferent = 1;
		canBeEqual = 0;
	}

	else if(size1 > size2 && (!summ_is_symbolic(&s1[size2],8) || !_solver_is_it_possible(_solver_EQ(&s1[size2], &char_zero, 8)))){
		canBeDifferent = 1;
		canBeEqual = 0;
	}

	else{

		int sz = MIN(size1,size2);
		int i;

		for(i = 0; i < sz; i++){
			char c1 = s1[i];
			char c2 = s2[i];

			//Both chars are concrete and different 
			if(!summ_is_symbolic(&s1[i],8) && !summ_is_symbolic(&s2[i],8) && c1 != c2){
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

/*
* Wrapper for strcmp() 
*/
int strncmp(char* s1, char* s2, int n){
  //return strncmp1(s1,s2,n);
	return strncmp2(s1,s2,n);
}





/***************
*
* 	strcmp()
*
****************/

//Only compares concrete bytes
int strcmp1(char* s1, char* s2){
	int size1 = strlen(s1);
	int size2 = strlen(s2);

	if(size1 != size2){
		return 1;
	}

	int i;
	for(i = 0; i < size1; i++){
		char c1 = s1[i];
		char c2 = s2[i];


		//Lazy evaluation for SE optimization  
		if(summ_is_symbolic(&c1,8) == 0 && summ_is_symbolic(&c2,8) == 0 && c1 != c2){
			return 1;
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

	int size1 = strlen(s1);
	int size2 = strlen(s2);

	//If sizes are symbolic maximizes to a concrete length
	if(summ_is_symbolic(&size1,32)){
		size1 = summ_maximize(&size1, 32);
	}
	if(summ_is_symbolic(&size2,32)){
		size2 = summ_maximize(&size2, 32);
	}



	if(size1 < size2 && (!summ_is_symbolic(&s2[size1],8) || !_solver_is_it_possible(_solver_EQ(&s2[size1], &char_zero, 8)))){
		canBeDifferent = 1;
		canBeEqual = 0;
	}

	else if(size1 > size2 && (!summ_is_symbolic(&s1[size2],8) || !_solver_is_it_possible(_solver_EQ(&s1[size2], &char_zero, 8)))){
		canBeDifferent = 1;
		canBeEqual = 0;
	}

	else{

		int sz = MIN(size1,size2);
		int i;

		for(i = 0; i < sz; i++){
			char c1 = s1[i];
			char c2 = s2[i];

			//Both chars are concrete and different 
			if(!summ_is_symbolic(&s1[i],8) && !summ_is_symbolic(&s2[i],8) && c1 != c2){
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

/*
* Wrapper for strcmp() 
*/
int strcmp(char* s1, char* s2){
  //return strcmp1(s1,s2);
	return strcmp2(s1,s2);
}




/***************
*
* 	strcpy()
*
****************/

char* strcpy1(char* dest, char* source){
	int i = 0;

	//Lazy evaluation for SE optimization  
	while(summ_is_symbolic(&source[i],8) || !(summ_is_symbolic(&source[i],8) == 0 && source[i] == '\0')){

		dest[i] = source[i];
		i++;
	}
	dest[i] = '\0';
	return dest;
}

char* strcpy2(char* dest, char* source){
	int i = 0;
	char zero = '\0';

	while(1){
		if(summ_is_symbolic(&source[i],8)){
			
			if(!_solver_is_it_possible(_solver_NEQ(&source[i], &zero, 8))){
				break;
			}
			
			else{
				summ_assume(_solver_NEQ(&source[i], &zero, 8));
			}
		}

		else if(source[i] == '\0'){
			break;
		}
		dest[i] = source[i];
		i++;
	}

	dest[i] = '\0';
	return dest;

}


/*
* Wrapper for strcpy() 
*/
char* strcpy(char* s1, char* s2){
  //return strcpy1(s1,s2);
	return strcpy2(s1,s2);
}




/***************
*
* 	strncpy()
*
****************/

char* strncpy1(char* dest, char* source, int n){
	int i = 0;

	if(summ_is_symbolic(&n, 32)){
		n = summ_maximize(&n, 32);
	}

	//Lazy evaluation for SE optimization  
	while(i < n){

		if(summ_is_symbolic(&source[i],8) || !(summ_is_symbolic(&source[i],8) == 0 && source[i] == '\0')){	

			dest[i] = source[i];
			i++;
		}
		else break;

	}

	dest[i] = '\0';
	return dest;
}


char* strncpy2(char* dest, char* source, int n){
	int i = 0;
	char zero = '\0';


	if(summ_is_symbolic(&n, 32)){
		n = summ_maximize(&n, 32);
	}

	while(i < n){
		if(summ_is_symbolic(&source[i],8)){
			
			if(!_solver_is_it_possible(_solver_NEQ(&source[i], &zero, 8))){
				break;
			}
			
			else{
				summ_assume(_solver_NEQ(&source[i], &zero, 8));
			}
		}

		else if(source[i] == '\0'){
			break;
		}
		dest[i] = source[i];
		i++;
	}

	dest[i] = '\0';
	return dest;

}

/*
* Wrapper for strncpy() 
*/
char* strncpy(char* s1, char* s2, int n){
  //return strncpy1(s1,s2,n);
	return strncpy2(s1,s2,n);
}






/***************
*
* 	strcat()
*
****************/

char* strcat1(char* dest, char* source){

	int i = strlen(dest);

	//Lazy evaluation for SE optimization  
	while(summ_is_symbolic(&source[i],8) || !(summ_is_symbolic(&source[i],8) == 0 && source[i] == '\0')){

		dest[i] = source[i];
		i++;
	}
	dest[i] = '\0';
	return dest;
}



char* strcat2(char* dest, char* source){

	int i = strlen(dest);
	int j = 0;
	char zero = '\0';

	while(1){
		if(summ_is_symbolic(&source[j],8)){
			
			if(!_solver_is_it_possible(_solver_NEQ(&source[j], &zero, 8))){
				break;
			}
			
			else{
				summ_assume(_solver_NEQ(&source[j], &zero, 8));
			}
		}

		else if(source[j] == '\0'){
			break;
		}
		dest[i] = source[j];
		i++;
		j++;
	}

	dest[i] = '\0';
	return dest;

}

/*
* Wrapper for strcat() 
*/
char* strcat(char* s1, char* s2){
  //return strcat1(s1,s2);
	return strcat2(s1,s2);
}



/***************
*
* 	puts()
*
****************/

int puts1(char* s){
	int i = 0;

	//Lazy evaluation for SE optimization  
	while(summ_is_symbolic(&s[i],8) || !(summ_is_symbolic(&s[i],8) == 0 && s[i] == '\0')){

		summ_print_byte(s[i]);
		i++;
	}
	summ_print_byte('\n');
	return i;
}


int puts2(char* s){
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
		summ_print_byte(s[i]);
		i++;
	}
	summ_print_byte('\n');
	return i;
}

/*
* Wrapper for puts() 
*/
int puts(char* s){
  //return puts1(s);
	return puts2(s);
}


/***************
*
* 	putchar()
*
****************/

int putchar(int c){
	summ_print_byte((char)c);
	return c ;
}



/***************
*
* 	getchar()
*
****************/

char getchar(){

	symbolic sym_var = summ_new_sym_var(8);
	return sym_var;
}




/***************
*
* 	fgets()
*
****************/


char* fgets(char *str, unsigned int length, void* stream){
	int i = 0;


	//If length is symbolic maximizes to a concrete length to optimize SE
	if(summ_is_symbolic(&length,32)){

		length = summ_maximize(&length, 32);
	}


	while(length-1 > 0){

		symbolic sym_var = summ_new_sym_var(8);
		str[i++] = sym_var;
		length--;

	}
	str[i] = '\0';
	return str;	

}

/***************
*
* 	atoi()
*
****************/


int atoi1(char *str){

	int i = 0;
	int sign = 1;
	int res = 0;

	while(1){

		// Concrete char
		if(summ_is_symbolic(&str[i],8) == 0){

			if(is_numeric(str[i])){

				res = res * 10 + str[i] - '0';
				i++;
			}

			else if(str[i] == '-' && i == 0){

				sign = -1;
				i++;
			}

			else if(str[i] == '\0'){
				break;
			}

			else return 0;	 
		}



		//Symbolic char
		else {

			if(res == 0){
				symbolic val = summ_new_sym_var(32);
				int size = strlen(str);

				if(size < 10){

					int lower_bound = pow(-10,size-1);
					int upper_bound = pow(10,size);

					restr_t val_GE_lower = _solver_GT(&val, &lower_bound, 32);
					restr_t val_LE_upper = _solver_LT(&val, &upper_bound, 32);
					restr_t bounds_restr = _solver_And(val_GE_lower,val_LE_upper);

					//For testing
					//summ_print_restriction(bounds_restr);
					

					summ_assume(bounds_restr);
				}

				return val;
			}	
		}
	}

	return res * sign;
}

int atoi2(char *str){

	int i = 0;
	int sign = 1;
	int res = 0;

	int sym_numbers = 0;

	//Last char evaluated was symbolic
	int symbolic_previous = 0;

	while(1){

		// Concrete char
		if(summ_is_symbolic(&str[i],8) == 0){

			if(is_numeric(str[i]) && !symbolic_previous){

				res = res * 10 + str[i] - '0';
				i++;
			}

			else if(str[i] == '-' && i == 0){

				sign = -1;
				i++;
			}

			else if(str[i] == '\0'){
				break;
			}

			else return 0;	 
		}



		//Symbolic char
		else {

			restr_t is_numeric = sym_is_numeric(&str[i]);

			if(_solver_is_it_possible(is_numeric)){

				summ_assume(is_numeric);
				symbolic_previous = 1;
				sym_numbers++;
				i++;
			}

			else break;
		}

		//string limit
		if(i>10){
			break;
		}

	}

	//Return val is symbolic
	if(sym_numbers > 0){

		symbolic val = summ_new_sym_var(32);
		int lower_bound;
		int upper_bound;

		if(res == 0){

			//Case: "<sym><sym>..."
			
			if(sign == 1){
				lower_bound = 0;
				upper_bound = pow(10,sym_numbers)-1;
			}

			//Case: "-<sym><sym>..."
			
			else{
				lower_bound = -1 * (pow(10,sym_numbers)-1);
				upper_bound = 0;
			}
		}

		//Case: 123<sym><sym>
		
		else{

			lower_bound = res * sign * pow(10,sym_numbers);
			upper_bound = lower_bound + (pow(10,sym_numbers)-1);
		}

		restr_t val_GE_lower = _solver_GE(&val, &lower_bound, 32);
		restr_t val_LE_upper = _solver_LE(&val, &upper_bound, 32);
		restr_t bounds_restr = _solver_And(val_GE_lower,val_LE_upper);

		//For testing
		//summ_print_restriction(bounds_restr);
		

		summ_assume(bounds_restr);


		return val;

	}

	return res * sign;
}


/*
* Wrapper for atoi() 
*/
int atoi(char* s){
  	return atoi1(s);
	//return atoi2(s);
}

