#ifndef STDLIB_H
#define STDLIB_H


#include "assert.h"
#include <sys/types.h>

void *alloca(size_t);

void *calloc(size_t, size_t);
void *malloc(size_t);
void free(void *);
void *realloc(void *, size_t);

long int strtol(const char *nptr, char **endptr, int base);
unsigned long int strtoul(const char *nptr, char **endptr, int base);

#endif
