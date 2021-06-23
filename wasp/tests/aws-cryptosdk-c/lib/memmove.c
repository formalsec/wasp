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
* 	memmove()
*
****************/

void* memmove1(void *dest, void *src, int n){

	//If length is symbolic maximizes to a concrete length to optimize SE
	if(summ_is_symbolic(&n,32)){

		n = summ_maximize(&n, 32);
	}

	unsigned char *str_dest = (unsigned char*) dest;
	unsigned char *str_src = (unsigned char*) src;
	
	char aux_buffer[n];

	for(int i = 0; i < n; i++){

		unsigned char c = *(str_src + i);
		aux_buffer[i] = c;
	}

	for(int j = 0; j < n; j++){

		*(str_dest + j) = aux_buffer[j];	
	}


	return dest;
}



void* memmove2(void *dest, void *src, int n){

	//If length is symbolic maximize and restrict to a concrete length
	if(summ_is_symbolic(&n,PTR_SIZE)){

		int max = summ_maximize(&n, PTR_SIZE);
		restr_t maximize = _solver_EQ(&n, &max, PTR_SIZE);
		summ_assume(maximize);
		n = max;
	}

	unsigned char *str_dest = (unsigned char*) dest;
	unsigned char *str_src = (unsigned char*) src;
	
	char aux_buffer[n];

	for(int i = 0; i < n; i++){

		unsigned char c = *(str_src + i);
		aux_buffer[i] = c;
	}

	for(int j = 0; j < n; j++){

		*(str_dest + j) = aux_buffer[j];	
	}


	return dest;
}
