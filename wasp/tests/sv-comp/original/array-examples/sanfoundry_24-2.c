extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int(void);

/*
 * Adapted from http://www.sanfoundry.com/c-programming-examples-arrays/
 * C Program to Print the Number of Odd & Even Numbers in an Array
 */
#define SIZE 100000

void printEven( int i ) {
  __VERIFIER_assert(  ( i % 2 ) == 0  );
  // printf( "%d" , i );
}

void printOdd( int i ) {
  __VERIFIER_assert(  ( i % 2 ) != 0  );
  // printf( "%d" , i );
}

int main()
{
    int array[SIZE];
    int i;
    int num = __VERIFIER_nondet_int();
		
		for(i = 0; i < num; i++) 
		{
		  array[i] = __VERIFIER_nondet_int();
		}
 
    //printf("Even numbers in the array are - ");
    for (i = 0; i < num; i++) // use of uninitialized num
    {
        if (array[i] % 2 == 0)
        {
            printEven( array[i] );
        }
    }
    //printf("\n Odd numbers in the array are -");
    for (i = 0; i < num; i++)
    {
        if (array[i] % 2 != 0)
        {
            printOdd( array[i] );
        }
    }
  return 0;
}
