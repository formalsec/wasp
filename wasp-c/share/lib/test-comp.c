#include <wasp.h>

void exit(int e) { __WASP_assume(0); }
void __assert_fail(const char *id, const char *file, 
		unsigned int i, const char *func) {
	__WASP_assert(0);
}

_Bool __VERIFIER_nondet_bool(char *name) {
	_Bool var = __WASP_symb_int(name);
	__WASP_assume(__logor(var == 0, var == 1));
	return var;
}

char __VERIFIER_nondet_char(char *name) {
	return (char) __WASP_symb_int(name);
}

unsigned char __VERIFIER_nondet_uchar(char *name) {
	return (unsigned char) __WASP_symb_int(name);
}

short __VERIFIER_nondet_short(char *name) {
	return (short) __WASP_symb_int(name);
}

unsigned short __VERIFIER_nondet_ushort(char *name) {
	return (unsigned short) __WASP_symb_int(name);
}

int __VERIFIER_nondet_int(char *name) {
	return __WASP_symb_int(name);
}

unsigned int __VERIFIER_nondet_uint(char *name) {
	return (unsigned int) __WASP_symb_int(name);
}

unsigned int __VERIFIER_nondet_charp(char *name) {
	return (unsigned int) __WASP_symb_int(name);
}

long __VERIFIER_nondet_long(char *name) {
	return (long) __WASP_symb_int(name);
}

unsigned long __VERIFIER_nondet_ulong(char *name) {
	return (unsigned long) __WASP_symb_int(name);
}

float __VERIFIER_nondet_float(char *name) {
	return __WASP_symb_float(name);
}

double __VERIFIER_nondet_double(char *name) {
	return __WASP_symb_double(name);
}
