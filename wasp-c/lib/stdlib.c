#include <limits.h>
#include <errno.h>
#include <ctype.h>
#include <stdlib.h>

#include "accuracy.h"
#include "getchar.h"
#include "wasp.h"

#define ABS_LONG_MIN 2147483648UL

void abort(void) { __WASP_assume(0); }

extern unsigned char __heap_base;
unsigned int bump_pointer = &__heap_base;

void *malloc(size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < size; ++i)
    *((unsigned char *)bump_pointer + i) = 'i';
  bump_pointer += size;
  return (void*)__WASP_alloc(r, size);
}

void *alloca(size_t size) {
  return malloc(size);
}

void *calloc (size_t nmemb, size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < nmemb * size; ++i)
    *((unsigned int*)(bump_pointer + i)) = 0;
  bump_pointer += (nmemb * size);
  return (void *)__WASP_alloc(r, nmemb * size);
}

void *realloc(void *ptr, size_t size) {
  __WASP_dealloc(ptr);
  return (void *)__WASP_alloc(ptr, size);
}

void free(void *ptr) {
  __WASP_dealloc(ptr);
}

char *getenv(const char *name) { return (char *)0; }
int setenv(const char *name, const char *value, int overwrite) {
  return 0;
}
int unsetenv(const char *name) {
  return 0;
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
static void exch(char* base,size_t size,size_t a,size_t b) {
  char* x=base+a*size;
  char* y=base+b*size;
  while (size) {
    char z=*x;
    *x=*y;
    *y=z;
    --size; ++x; ++y;
  }
}


/* Quicksort with 3-way partitioning, ala Sedgewick */
/* Blame him for the scary variable names */
/* http://www.cs.princeton.edu/~rs/talks/QuicksortIsOptimal.pdf */
static void quicksort(char* base,size_t size,ssize_t l,ssize_t r,
		      int (*compar)(const void*,const void*)) {
  ssize_t i=l-1, j=r, p=l-1, q=r, k;
  char* v=base+r*size;
  if (r<=l) return;
  /*
     We chose the rightmost element in the array to be sorted as pivot,
     which is OK if the data is random, but which is horrible if the
     data is already sorted.  Try to improve by chosing the middle
     element instead.
   */
  exch(base,size,l+(r-l)/2,r);

  for (;;) {
    while (++i != r && compar(base+i*size,v)<0) ;
    while (compar(v,base+(--j)*size)<0) if (j == l) break;
    if (i >= j) break;
    exch(base,size,i,j);
    if (compar(base+i*size,v)==0) exch(base,size,++p,i);
    if (compar(v,base+j*size)==0) exch(base,size,j,--q);
  }
  exch(base,size,i,r); j = i-1; ++i;
  for (k=l; k<p; k++, j--) exch(base,size,k,j);
  for (k=r-1; k>q; k--, i++) exch(base,size,i,k);
  quicksort(base,size,l,j,compar);
  quicksort(base,size,i,r,compar);
}

void qsort(void* base,size_t nmemb,size_t size,int (*compar)(const void*,const void*)) {
  /* check for integer overflows */
  if (nmemb >= (((size_t)-1)>>1) ||
      size >= (((size_t)-1)>>1)) return;
#if 0
  if (sizeof(size_t) < sizeof(unsigned long long)) {
    if ((unsigned long long)size * nmemb > (size_t)-1) return;
  } else {
    if (size*nmemb/nmemb != size) return;
  }
#endif
  if (nmemb>1)
    quicksort(base,size,0,nmemb-1,compar);
}

int posix_memalign(void **memptr, size_t alignment, size_t size) {
  return 0;
}

char (*getchar_array[1]) () = {getchar1};
char getchar(){
	return (*getchar_array[GETCHAR_ACCURACY-1])();
}
