#include <stdlib.h>
#include <stdio.h>

void test(int mm)
{
  int *ptr;
  int value=0;
  int i=0;

  if (mm % 3) 
    ptr = &mm;
  else
    ptr = &value;
  
  while (i<mm) {
    value += ptr[i++];
    ptr = ptr+i;
  }
  printf("%d\n", value);
}
