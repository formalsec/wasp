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
* 	memcpy()
*
****************/

void* memcpy1(void *dest, void *src, int n){

	//If length is symbolic maximizes to a concrete length to optimize SE
	if(summ_is_symbolic(&n,32)){

		n = *((int*)summ_maximize(&n, 32));
	}
	
	unsigned char *str_dest = (unsigned char*) dest;
	unsigned char *str_src = (unsigned char*) src;

	for(int i = 0; i < n; i++){

		unsigned char c = *(str_src + i);
		*(str_dest + i) = c;

	}
	return dest;
}
