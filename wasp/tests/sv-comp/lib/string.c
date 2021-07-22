#include "string.h"

/***************
* 	memmove()
****************/
void* (*memmove_array[2])(void*, void*, int) = {memmove1, memmove2};
void*  memmove(void *dest, void *src, int n){
	return(*memmove_array[MEMMOVE_ACCURACY-1])(dest,src,n);
}

/***************
* 	memcmp()
****************/
int (*memcmp_array[4])(void*, void*, int) = {memcmp1, memcmp2, memcmp3, memcmp4};
int memcmp(void* s1, void* s2, int n){
	return(*memcmp_array[MEMCMP_ACCURACY-1])(s1,s2,n);
}

/***************
* 	memchr()
****************/
char* (*memchr_array[4]) (char*, int, int) = {memchr1, memchr2, memchr3, memchr4};
char *memchr(char* s, int c, int n){
	return (*memchr_array[STRCHR_ACCURACY-1])(s, c, n);
}

/***************
* 	memcpy()
****************/
void* (*memcpy_array[1])(void*, void*, int) = {memcpy1};
void*  memcpy(void *dest, void *src, int n){
	return(*memcpy_array[MEMCPY_ACCURACY-1])(dest,src,n);
}


/***************
* 	memset()
****************/
void* (*memset_array[1])(void*, int, int) = {memset1};
void*  memset(void *str, int c, int n){
	return(*memset_array[MEMSET_ACCURACY-1])(str,c,n);
}

/***************
* 	strncpy()
****************/
char* (*strncpy_array[2]) (char*, char*, int) = {strncpy1, strncpy2};
char* strncpy(char* dest, char* source, int n){
	return (*strncpy_array[STRNCPY_ACCURACY-1])(dest, source, n);
}

/***************
* 	strlen()
****************/
int (*strlen_array[3]) (char*) = {strlen1, strlen2, strlen3};
int strlen(char * s){
	return (*strlen_array[STRLEN_ACCURACY-1])(s);
}


/***************
* 	strncmp()
****************/
int (*strcmp_array[3]) (char*, char*) = {strcmp1, strcmp2, strcmp3};
int strcmp(char* s1, char* s2){
	return (*strcmp_array[STRNCMP_ACCURACY-1])(s1, s2);
}
