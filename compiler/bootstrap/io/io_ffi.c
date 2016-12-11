#include <stdio.h>

void ffiputChar (char* a) {
  putchar(a[0]);
}

void ffigetChar (char* a) {
  int c = getchar();
  if(c == EOF) {
    a[1] = 1;
  } else {
    a[0] = c;
    a[1] = 0;
  }
}
