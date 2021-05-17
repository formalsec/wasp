#ifndef STDLIB_H
#define STDLIB_H

#define NULL 0

#include "assert.h"

typedef unsigned long size_t;



void *alloca(size_t);
void *malloc(size_t);
void *realloc(void *, size_t);
void *calloc(size_t, size_t);
void free(void *);

#endif
