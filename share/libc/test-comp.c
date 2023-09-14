#include <wasp.h>
#include <stdio.h>

void exit(int e) { __WASP_assume(0); }
void __assert_fail(const char *id, const char *file,
		unsigned int i, const char *func) {
	__WASP_assert(0);
}

_Bool __VERIFIER_nondet_bool() {
	_Bool var = __WASP_symb_int(NULL);
	__WASP_assume(or_(var == 0, var == 1));
	return var;
}

char __VERIFIER_nondet_char() {
	return (char) __WASP_symb_int(NULL);
}

unsigned char __VERIFIER_nondet_uchar() {
	return (unsigned char) __WASP_symb_int(NULL);
}

short __VERIFIER_nondet_short() {
	return (short) __WASP_symb_int(NULL);
}

unsigned short __VERIFIER_nondet_ushort() {
	return (unsigned short) __WASP_symb_int(NULL);
}

int __VERIFIER_nondet_int() {
	return __WASP_symb_int(NULL);
}

unsigned int __VERIFIER_nondet_uint() {
	return (unsigned int) __WASP_symb_int(NULL);
}

__int128 __VERIFIER_nondet_int128() {
	return __WASP_symb_int(NULL);
}

unsigned __int128 __VERIFIER_nondet_uint128() {
	return (unsigned __int128) __WASP_symb_int(NULL);
}

unsigned int __VERIFIER_nondet_charp() {
	return (unsigned int) __WASP_symb_int(NULL);
}

long __VERIFIER_nondet_long() {
	return (long) __WASP_symb_int(NULL);
}

unsigned long __VERIFIER_nondet_ulong() {
	return (unsigned long) __WASP_symb_int(NULL);
}

float __VERIFIER_nondet_float() {
	return __WASP_symb_float(NULL);
}

double __VERIFIER_nondet_double() {
	return __WASP_symb_double(NULL);
}
