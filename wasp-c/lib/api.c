/**
Defines mockup interface with Symbolic Execution Tool
**/

#include "api.h"

/**
 * summ_not_implemented_error - Check is SE tool implements function <fname> 
 * if it's not implemented execution is stopped
 *
 * @fname: Function name
 */
void summ_not_implemented_error(char *fname){
	return;
}





/**
 * summ_print_byte - Prints a byte
 * @byte
 */
void summ_print_byte(char byte){
	summ_not_implemented_error("summ_print_byte");
	return;
}

/**
 * summ_maximize - Maximizes symbolic variable returning a concrete value
 * @sym_var: Address of simbolic variable 
 * @length: size in bits of symbolic variable
 */
void* summ_maximize(symbolic sym_var, unsigned int length){
	summ_not_implemented_error("summ_maximize");
	return NULL;
}

/**
 * summ_is_symbolic - Verifies if concatenation of <length> bits
 * starting from address of sym_var is symbolic

 * @sym_var: Address of simbolic variable 
 * @length: Number of bits
 *
 *	Returns 1 if is symbolic, 
 *			0 otherwise
 */
int summ_is_symbolic(symbolic sym_var, unsigned int length){
  return __WASP_is_symbolic(sym_var, length);
}

/**
 * summ_new_sym_var - Creates a symbolic variable with <length> bits
 * @length
 */
symbolic summ_new_sym_var(unsigned int length){
	if (length <= 32) return __WASP_symb_int("sym_i32");
	else return __WASP_symb_long("sym_i64");
}






/*************************************
 *
 * Constraint solver interface
 *
 *************************************/



/*
 * Add restriction to solver
 */
void summ_assume(restr_t restr){
	summ_not_implemented_error("summ_assume");
	return;
}





/**********************
 * 
 * Binary Operations
 *
 **********************/



/*
 *  _solver_Concat - Concatenation of 2 symbolic variables 
 *
 *  @sym_var: address of symbolic variable 1
 *  @sym_var2: address of symbolic variable 2
 *  @length1:  length in bits of symbolic variable 1
 *  @length2:  length in bits of symbolic variable 2
 *
 */
symbolic _solver_Concat(symbolic sym_var, symbolic sym_var2, unsigned int length1, unsigned int length2){
	summ_not_implemented_error("_solver_Concat");
	return NULL;
}



/*
*  _solver_Extract - Extracts bits from <sym_var> from <start> to <end>
*
*  @sym_var: address of symbolic variable
*  @start: postion of the first bit to be extracted
*  @end: position of the last bit to be extracted + 1
*  @length: length in bits of symbolic variable 
*
*  E.g: if start = 0 and end = 8 the first 8 bits are extracted
*/
symbolic _solver_Extract(symbolic sym_var, unsigned int start, unsigned int end, unsigned int length){
	summ_not_implemented_error("_solver_Extract");
	return NULL;

}



/*********************
*
* Unary Operations
*
*********************/




/*
*  _solver_ZeroExt - Extends symbolic varible <sym_var> with <to_extend> bits
*  the added bits are placed to the left and are 0's
*
*  @sym_var: address of symbolic variable	
*  @to_extend: number of bits
*  @length: length in bits of symbolic variable 
*
*/
symbolic _solver_ZeroExt(symbolic sym_var, unsigned int to_extend, unsigned int length){
	summ_not_implemented_error("_solver_ZeroExt");
	return NULL;
}




/*
*  _solver_ZeroExt - Extends symbolic varible <sym_var> with <to_extend> bits
*   the added bits are placed to the left and are 1's if sym_var is negative and o's otherwise
*
*  @sym_var: address of symbolic variable	
*  @to_extend: number of bits
*  @length: length in bits of symbolic variable 
* 
*/
symbolic _solver_SignExt(symbolic sym_var, unsigned int to_extend, unsigned int length){
	summ_not_implemented_error("_solver_SignExt");
	return NULL;
}


/******************************
*
* Operations with constraints
*
******************************/


/*
 *
 * Pretty print restriction <restr> for debug
 *
 */
void summ_print_restriction(restr_t restr){
	summ_not_implemented_error("summ_print_restriction");
	return;
}


restr_t _solver_NOT(restr_t restr1){
	summ_not_implemented_error("_solver_NOT");
	return 0;
}

restr_t _solver_Or(restr_t restr1, restr_t restr2){
	summ_not_implemented_error("_solver_Or");
	return 0;
}
restr_t _solver_And(restr_t restr1, restr_t restr2){
	summ_not_implemented_error("_solver_And");
	return 0;
}



/*
 *
 * Is assumed that sym_var and sym_var2 have the same length (bits)
 *
 */

restr_t _solver_EQ(symbolic sym_var, symbolic sym_var2, unsigned int length){
	summ_not_implemented_error("_solver_EQ");
	return 0;
}
restr_t _solver_NEQ(symbolic sym_var, symbolic sym_var2, unsigned int length){
	summ_not_implemented_error("_solver_NEQ");
	return 0;
}
restr_t _solver_LT(symbolic sym_var, symbolic sym_var2, unsigned int length){
	summ_not_implemented_error("_solver_LT");
	return 0;
}
restr_t _solver_LE(symbolic sym_var, symbolic sym_var2, unsigned int length){
	summ_not_implemented_error("_solver_LE");
	return 0;
}
/*
* 'S'stands for signed values
*/
restr_t _solver_SLT(symbolic sym_var, symbolic sym_var2, unsigned int length){
	summ_not_implemented_error("_solver_SLT");
	return 0;
}
restr_t _solver_SLE(symbolic sym_var, symbolic sym_var2, unsigned int length){
	summ_not_implemented_error("_solver_SLE");
	return 0;
}

restr_t _solver_IF(restr_t restr, symbolic sym_var, symbolic sym_var2, unsigned int length){
	summ_not_implemented_error("_solver_IF");
	return 0;
}




int _solver_is_it_possible(restr_t restr){
	summ_not_implemented_error("_solver_is_it_possible");
	return 0;
}


