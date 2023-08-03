#ifndef STRING_H
#define STRING_H

#include <stddef.h>

#include "api.h"
#include "summ_utils.h"
#include "accuracy.h"
#include "memcmp.h"
#include "memset.h"
#include "memcpy.h"
#include "memmove.h"
#include "memchr.h"
#include "strncpy.h"
#include "strlen.h"
#include "strcmp.h"

int strlen(char* s);
int strcmp(char* s1, char* s2);

char* strncpy(char *, char *, int);

int memcmp(void* s1, void* s2, int n);
void* memcpy(void *, void *, int);
void* memset(void *, int, int);
void* memmove(void *dest, void *src, int n);
char* memchr(char* s, int c, int n);

#endif
