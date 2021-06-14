/*
 * Date: 2014-06-29
 * Author: leike@informatik.uni-freiburg.de
 *
 * This program has the following 3-phase ranking function:
 * f_0(x, y, z) = z
 * f_1(x, y, z) = y
 * f_2(x, y, z) = x
 *
 * The program does not have a nested ranking function.
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

int main()
{
    int x, y, z;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    z = __VERIFIER_nondet_int();
    // prevent overflows
    assume_abort_if_not(x<=65535);
    assume_abort_if_not(-65535<=y && y<=65535);
    assume_abort_if_not(-65535<=z && z<=65535);
	while (x >= 0) {
		if (__VERIFIER_nondet_int() != 0) {
			x = x + y;
		} else {
			x = x + z;
		}
		y = y + z;
		z = z - 1;
	}
	return 0;
}
