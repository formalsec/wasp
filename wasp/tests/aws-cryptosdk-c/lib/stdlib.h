#ifndef STDLIB_H
#define STDLIB_H


#include "assert.h"
#include <sys/types.h>

void *alloca(size_t);
void *malloc(size_t);
void *realloc(void *, size_t);
void *calloc(size_t, size_t);
void free(void *);

#endif
