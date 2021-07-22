void abort(void); 
#include <assert.h>
void reach_error() { assert(0); }
void abort(void); 
void assume_abort_if_not(int cond) { 
  if(!cond) {abort();}
}
int __VERIFIER_nondet_int(char*);
void *__VERIFIER_nondet_pointer(char*);

/* Add variable, check for expression equal to it */

void *ldv_malloc(size_t size) {
	if(__VERIFIER_nondet_int("if@14")) {
		return malloc(size);
	} else {
		return 0;
	}
};

void *ldv_successful_malloc(size_t size) {
	void *ptr = malloc(size);
	assume_abort_if_not(ptr!=0);
	return ptr;
};
