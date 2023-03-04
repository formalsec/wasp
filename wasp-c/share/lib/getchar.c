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
* 	getchar()
*
****************/

char getchar1(){
	symbolic sym_var = summ_new_sym_var(CHAR_SIZE);
	return sym_var;
}
