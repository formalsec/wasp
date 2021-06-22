#include <proof_helpers/proof_allocators.h>

extern bool __VERIFIER_nondet_bool(char *);
extern int8_t __VERIFIER_nondet_char(char *);
extern uint8_t __VERIFIER_nondet_uchar(char *);
extern int16_t __VERIFIER_nondet_short(char *);
extern uint16_t __VERIFIER_nondet_ushort(char *);
extern int32_t __VERIFIER_nondet_int(char *);
extern uint32_t __VERIFIER_nondet_uint(char *);
extern int64_t __VERIFIER_nondet_long(char *);
extern uint64_t __VERIFIER_nondet_ulong(char *);
extern uint32_t __VERIFIER_nondet_charp(char *);

bool nondet_bool() { return __VERIFIER_nondet_bool("rbool"); }
int nondet_int() { return __VERIFIER_nondet_int("rint"); }
size_t nondet_size_t() { return __VERIFIER_nondet_ulong("rulong"); }
uint16_t nondet_uint16_t() { return __VERIFIER_nondet_ushort("rushort"); }
uint32_t nondet_uint32_t() { return __VERIFIER_nondet_uint("ruint"); }
uint64_t nondet_uint64_t() { return __VERIFIER_nondet_ulong("rulong"); }
uint8_t nondet_uint8_t() { return __VERIFIER_nondet_uchar("ruchar"); }
void *nondet_voidp() { return (void *)__VERIFIER_nondet_charp("rptr"); }
