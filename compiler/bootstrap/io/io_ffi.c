#include <stdio.h>

void ffi0 (char* a) {
  putchar(a[0]);
}

void ffi1 (char* a) {
  int c = getchar();
  if(c == EOF) {
    a[0] = 0;
  } else {
    a[0] = 1;
    ungetc(c, stdin);
  }
}

void ffi2 (char* a) {
  a[0] = getchar();
}
