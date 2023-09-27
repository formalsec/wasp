#include "string.h"

/***************
 * 	memmove()
 ****************/
void *(*memmove_array[2])(void *, void *, int) = {memmove1, memmove2};
void *memmove(void *dest, void *src, int n) {
  return (*memmove_array[MEMMOVE_ACCURACY - 1])(dest, src, n);
}

/***************
 * 	memcmp()
 ****************/
int (*memcmp_array[4])(void *, void *, int) = {memcmp1, memcmp2, memcmp3,
                                               memcmp4};
int memcmp(void *s1, void *s2, int n) {
  return (*memcmp_array[MEMCMP_ACCURACY - 1])(s1, s2, n);
}

/***************
 * 	memchr()
 ****************/
char *(*memchr_array[4])(char *, int, int) = {memchr1, memchr2, memchr3,
                                              memchr4};
char *memchr(char *s, int c, int n) {
  return (*memchr_array[STRCHR_ACCURACY - 1])(s, c, n);
}

/***************
 * 	memcpy()
 ****************/
void *(*memcpy_array[1])(void *, void *, int) = {memcpy1};
void *memcpy(void *dest, void *src, int n) {
  return (*memcpy_array[MEMCPY_ACCURACY - 1])(dest, src, n);
}

/***************
 * 	memset()
 ****************/
void *(*memset_array[1])(void *, int, int) = {memset1};
void *memset(void *str, int c, int n) {
  return (*memset_array[MEMSET_ACCURACY - 1])(str, c, n);
}

/***************
 * 	strncpy()
 ****************/
char *(*strncpy_array[2])(char *, char *, int) = {strncpy1, strncpy2};
char *strncpy(char *dest, char *source, int n) {
  return (*strncpy_array[STRNCPY_ACCURACY - 1])(dest, source, n);
}

/***************
 * 	strlen()
 ****************/
int (*strlen_array[3])(char *) = {strlen1, strlen2, strlen3};
int strlen(char *s) { return (*strlen_array[STRLEN_ACCURACY - 1])(s); }

/***************
 * 	strncmp()
 ****************/
int (*strcmp_array[3])(char *, char *) = {strcmp1, strcmp2, strcmp3};
int strcmp(char *s1, char *s2) {
  return (*strcmp_array[STRNCMP_ACCURACY - 1])(s1, s2);
}

int strncmp(const char *s1, const char *s2, size_t n) {
  register const unsigned char *a = (const unsigned char *)s1;
  register const unsigned char *b = (const unsigned char *)s2;
  register const unsigned char *fini = a + n;
  while (a != fini) {
    register int res = *a - *b;
    if (res)
      return res;
    if (!*a)
      return 0;
    ++a;
    ++b;
  }
  return 0;
}

char *strcpy(char *dst, char *src) {
  const size_t length = strlen(src);
  memcpy(dst, src, length + 1);
  return dst;
}

char *strchr(register const char *t, int c) {
  register char ch;

  ch = c;
  for (;;) {
    if ((*t == ch))
      break;
    if ((!*t))
      return 0;
    ++t;
#ifndef WANT_SMALL_STRING_ROUTINES
    if ((*t == ch))
      break;
    if ((!*t))
      return 0;
    ++t;
    if ((*t == ch))
      break;
    if ((!*t))
      return 0;
    ++t;
    if ((*t == ch))
      break;
    if ((!*t))
      return 0;
    ++t;
#endif
  }
  return (char *)t;
}

char *strrchr(const char *t, int c) {
  register char ch;
  register const char *l = 0;

  ch = c;
  for (;;) {
    if ((*t == ch))
      l = t;
    if ((!*t))
      return (char *)l;
    ++t;
#ifndef WANT_SMALL_STRING_ROUTINES
    if ((*t == ch))
      l = t;
    if ((!*t))
      return (char *)l;
    ++t;
    if ((*t == ch))
      l = t;
    if ((!*t))
      return (char *)l;
    ++t;
    if ((*t == ch))
      l = t;
    if ((!*t))
      return (char *)l;
    ++t;
#endif
  }
  return (char *)l;
}

char *strerror(int errnum) { return NULL; }
