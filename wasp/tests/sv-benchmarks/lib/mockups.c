#include "assert.h"

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
char __VERIFIER_nondet_char(char *name) { 
  int sym_var = sym_int(name);
  //assume(sym_var >= -128 && sym_var <= 127);
  return sym_var & 0x800000ff;
}
unsigned char __VERIFIER_nondet_uchar(char *name) { 
  int sym_var = sym_int(name);
  assume(sym_var >= 0U); //&& sym_var <= 255U);
  return sym_var & 0x000000ff;
}
short __VERIFIER_nondet_short(char *name) { 
  int sym_var = sym_int(name);
  //assume(sym_var >= -32768 && sym_var <= 32767);
  return sym_var & 0x8000ffff;
}
unsigned short __VERIFIER_nondet_ushort(char *name) { 
  int sym_var = sym_int(name);
  assume(sym_var >= 0U); // && sym_var <= 65535U);
  return sym_var & 0x0000ffff;
}

int __VERIFIER_nondet_int(char *name) { return sym_int(name); }

unsigned int __VERIFIER_nondet_uint(char *name) { 
  unsigned int sym_var = sym_int(name);
  assume(sym_var >= 0U);
  return sym_var;
}

unsigned int __VERIFIER_nondet_charp(char *name) { return sym_int(name); }

int __VERIFIER_nondet_long(char *name) { return sym_long(name); }

unsigned int __VERIFIER_nondet_ulong(char *name) { 
  int sym_var = sym_long(name);
  assume(sym_var >= 0U);
  return sym_var;
}

float __VERIFIER_nondet_float(char *name) { return sym_float(name); }

double __VERIFIER_nondet_double(char *name) { return sym_double(name); }
