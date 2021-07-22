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
* 	strncpy()
*
****************/


char* strncpy1(char* dest, char* source, int n){
	int i = 0;

	if(summ_is_symbolic(&n, 32)){
		n = *((int *)summ_maximize(&n, 32));
	}

	while(i < n){

		dest[i] = source[i];

		if((summ_is_symbolic(&source[i],8) == 0 && source[i] == '\0')){
			break;
		}

		i++;

	}

	return dest;
}


char* strncpy2(char* dest, char* source, int n){
	int i = 0;
	char zero = '\0';

	if(summ_is_symbolic(&n, 32)){
		n = *((int *)summ_maximize(&n, 32));
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

	while(i < n){
		dest[i] = '\0';
	}

	return dest;

}
