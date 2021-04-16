#include "assert.h"

void abort (void) { assume(0); }
void exit (int e) { assert(0); }
void __assert_fail(const char *id, const char *file,
    unsigned int i, const char *func) {
  assert(0);
}
int __VERIFIER_nondet_bool(char *name) {
  int sym_var = sym_int(name);
  assume (sym_var == 0 || sym_var == 1);
  return sym_var;
}
int __VERIFIER_nondet_char(char *name) { 
  int sym_var = sym_int(name);
  assume(sym_var > -127 && sym_var < 127);
  return sym_var;
}
int __VERIFIER_nondet_uchar(char *name) { 
  int sym_var = sym_int(name);
  assume(sym_var >= 0 && sym_var < 256);
  return sym_var;
}
int __VERIFIER_nondet_short(char *name) { 
  int sym_var = sym_int(name);
  assume(sym_var > -32768 && sym_var < 32768);
  return sym_var;
}
int __VERIFIER_nondet_ushort(char *name) { 
  int sym_var = sym_int(name);
  assume(sym_var >= 0 && sym_var < 65536);
  return sym_var;
}
int __VERIFIER_nondet_int(char *name) { return sym_int(name); }
int __VERIFIER_nondet_uint(char *name) { return sym_int(name);   }
int __VERIFIER_nondet_charp(char *name) { return sym_int(name);   }
int __VERIFIER_nondet_long(char *name) { return sym_long(name);   }
int __VERIFIER_nondet_ulong(char *name) { return sym_long(name);   }
float __VERIFIER_nondet_float(char *name) { return sym_float(name); }
double __VERIFIER_nondet_double(char *name) { return sym_double(name); }
