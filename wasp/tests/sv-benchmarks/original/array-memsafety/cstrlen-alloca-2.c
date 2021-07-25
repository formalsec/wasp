/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);
extern char __VERIFIER_nondet_char(void);

int (cstrlen)(const char *s)
 {
     const char *p = s;
     /* Loop over the data in s.  */
     while (*p != '\0')
         p++;
     return (int)(p - s);
 }

int main() {
    int length1 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
		
		for(int i = 0; i < length1 - 1; i++) 
		{
		  nondetString1[i] = __VERIFIER_nondet_char();
		}

    nondetString1[length1-1] = '\0';
    return cstrlen(nondetString1);
}


