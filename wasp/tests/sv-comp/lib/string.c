#include "string.h"

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
