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
* 	memset()
*
****************/
void *memset1(void *str, int c, int n){

	unsigned char *s = (unsigned char*) str;
	unsigned char c_char = (unsigned char) c;

	//If length is symbolic maximizes to a concrete length
	if(summ_is_symbolic(&n,32)){

		n = *((int *)summ_maximize(&n, 32));
	}

	for(int i = 0; i < n; i++){
		*(s + i) = c_char;
	}

	return str;	
}
