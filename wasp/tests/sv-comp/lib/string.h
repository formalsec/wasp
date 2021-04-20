#ifndef STRING_H
#define STRING_H

#include "api.h"
#include "utils.h"
#include "accuracy.h"
#include "memset.h"
#include "memcpy.h"
#include "strncpy.h"

void* memcpy(void *, void *, int);
void* memset(void *, int, int);
char* strncpy(char *, char *, int);

#endif
