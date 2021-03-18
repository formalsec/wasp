#ifndef MOCKUPS_H
#define MOCKUPS_H

int dyn_sym_int32(char);
int is_symbolic(int addr, unsigned int length);
void assume(int);
void assert(int);

#endif
