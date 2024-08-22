#ifndef MOCKUPS_H
#define MOCKUPS_H

void *alloc(void*, unsigned int);
void dealloc(void *);

int sym_int(char*);
void assume(int);
void assert(int);

#endif
