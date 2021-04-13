#include "assert.h"

void abort (void) { assume(0); }
void __assert_fail(const char *id, const char *file,
    unsigned int i, const char *func) {
  assert(0);
}

int __VERIFIER_nondet_char(char *name) { 
  int s = sym_int(name, 32);
  assume(s > -127 && s < 127);
  return s;
}
int __VERIFIER_nondet_uchar(char *name) { 
  int s = sym_int(name, 32);
  assume(s >= 0 && s < 256);
  return s;
}
int __VERIFIER_nondet_short(char *name) { 
  int sym_var = sym_int(name, 32);
  assume(sym_var > -32768 && sym_var < 32768);
  return sym_var;
}
int __VERIFIER_nondet_ushort(char *name) { 
  int sym_var = sym_int(name, 32);
  assume(sym_var >= 0 && sym_var < 65536);
  return sym_var;
}
int __VERIFIER_nondet_int(char *name)    { return sym_int(name, 32); }
int __VERIFIER_nondet_uint(char *name)   { return sym_int(name, 32); }
int __VERIFIER_nondet_long(char *name)   { return sym_int(name, 64); }
int __VERIFIER_nondet_ulong(char *name)  { return sym_int(name, 64); }
int __VERIFIER_nondet_double(char *name) { return sym_int(name, 64); }
