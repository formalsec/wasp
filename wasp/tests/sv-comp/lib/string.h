#ifndef STRING_H
#define STRING_H

#include "api.h"
#include "utils.h"
#include "accuracy.h"
#include "memset.h"
#include "memcpy.h"
#include "strncpy.h"
#include "strlen.h"
#include "strcmp.h"

int strlen(char* s);
int strcmp(char* s1, char* s2);

char* strncpy(char *, char *, int);

void* memcpy(void *, void *, int);
void* memset(void *, int, int);

#endif
