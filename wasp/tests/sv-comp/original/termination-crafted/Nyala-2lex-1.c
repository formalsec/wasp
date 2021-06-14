/*
 * Date: 2013-07-13
 * Author: leike@informatik.uni-freiburg.de
 *
 * Simple test case for the lexicographic template.
 * Has the lexicographic ranking function
 * f(x, y) = <x, y>
 *
 */

extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_doub_access_init_const.c", 3, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
	int x, y;
	while (x >= 0 && y >= 0) {
		y = y - 1;
		if (y < 0) {
			x = x - 1;
			y = __VERIFIER_nondet_int();
		}
    __VERIFIER_assert(x >= 0 && y >= 0);
	}
    return 0;
}
