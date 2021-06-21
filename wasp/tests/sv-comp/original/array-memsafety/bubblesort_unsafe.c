#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void bubbleSort(int numbers[], int array_size)
{
    int i, j, temp;
     
    for (i = (array_size - 1); i >= 0; i--) {
        for (j = 1; j <= i; j++) {
            if (numbers[j-1] > numbers[j]) {
                temp = numbers[j-1];
                numbers[j-1] = numbers[j];
                numbers[j] = temp;
            }
        }
    }
}

int main() {
  int array_size = __VERIFIER_nondet_int();
  int *numbers = (int *) malloc(sizeof(int) * array_size);
  for (int i = 0; i < array_size; ++i)
    numbers[i] = i & 0xff;
  bubbleSort(numbers, array_size);
  return 0;
}
