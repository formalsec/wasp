#include <limits.h>
#include <errno.h>
#include <ctype.h>
#include <stdlib.h>

#define ABS_LONG_MIN 2147483648UL

extern unsigned char __heap_base;
unsigned int bump_pointer = &__heap_base;

void *malloc(size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < size; ++i)
    *((unsigned char *)bump_pointer + i) = 'i';
  bump_pointer += size;
  return (void*)alloc(r, size);
}

void *alloca(size_t size) {
  return malloc(size);
}

void *calloc (size_t nmemb, size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < nmemb * size; ++i)
    *((unsigned int*)(bump_pointer + i)) = 0;
  bump_pointer += (nmemb * size);
  return (void *)alloc(r, nmemb * size);
}

void *realloc(void *ptr, size_t size) {
  dealloc(ptr);
  return (void *)alloc(ptr, size);
}

void free(void *ptr) {
  dealloc(ptr);
}

long int strtol(const char *nptr, char **endptr, int base)
{
  int neg=0;
  unsigned long int v;
  const char*orig=nptr;

  while(isspace(*nptr)) nptr++;

  if (*nptr == '-' && isalnum(nptr[1])) { neg=-1; ++nptr; }
  v=strtoul(nptr,endptr,base);
  if (endptr && *endptr==nptr) *endptr=(char *)orig;
  if (v>=ABS_LONG_MIN) {
    if (v==ABS_LONG_MIN && neg) {
      errno=0;
      return v;
    }
    errno=ERANGE;
    return (neg?LONG_MIN:LONG_MAX);
  }
  return (neg?-v:v);
}

unsigned long int strtoul(const char *ptr, char **endptr, int base)
{
  int neg = 0, overflow = 0;
  unsigned long int v=0;
  const char* orig;
  const char* nptr=ptr;

  while(isspace(*nptr)) ++nptr;

  if (*nptr == '-') { neg=1; nptr++; }
  else if (*nptr == '+') ++nptr;
  orig=nptr;
  if (base==16 && nptr[0]=='0') goto skip0x;
  if (base) {
    register unsigned int b=base-2;
    if (b>34) { errno=EINVAL; return 0; }
  } else {
    if (*nptr=='0') {
      base=8;
skip0x:
      if ((nptr[1]=='x'||nptr[1]=='X') && isxdigit(nptr[2])) {
	nptr+=2;
	base=16;
      }
    } else
      base=10;
  }
  while(*nptr) {
    register unsigned char c=*nptr;
    c=(c>='a'?c-'a'+10:c>='A'?c-'A'+10:c<='9'?c-'0':0xff);
    if (c>=base) break;	/* out of base */
    {
      register unsigned long x=(v&0xff)*base+c;
      register unsigned long w=(v>>8)*base+(x>>8);
      if (w>(ULONG_MAX>>8)) overflow=1;
      v=(w<<8)+(x&0xff);
    }
    ++nptr;
  }
  if (nptr==orig) {		/* no conversion done */
    nptr=ptr;
    errno=EINVAL;
    v=0;
  }
  if (endptr) *endptr=(char *)nptr;
  if (overflow) {
    errno=ERANGE;
    return ULONG_MAX;
  }
  return (neg?-v:v);
}
