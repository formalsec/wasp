#ifndef STRING_H
#define STRING_H

#include <stddef.h>

#include "accuracy.h"
#include "api.h"
#include "memchr.h"
#include "memcmp.h"
#include "memcpy.h"
#include "memmove.h"
#include "memset.h"
#include "strcmp.h"
#include "strlen.h"
#include "strncpy.h"
#include "summ_utils.h"

int strlen(char *s);
int strcmp(char *s1, char *s2);
int strncmp(const char *s1, const char *s2, size_t n);
char *strchr(const char *str, int c);
char *strrchr(const char *str, int c);
char *strerror(int);

char *strcpy(char *, char *);
char *strncpy(char *, char *, int);

int memcmp(void *s1, void *s2, int n);
void *memcpy(void *, void *, int);
void *memset(void *, int, int);
void *memmove(void *dest, void *src, int n);
char *memchr(char *s, int c, int n);

#endif
