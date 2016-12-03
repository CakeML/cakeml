#include <stdio.h>

void ffiputChar (char* a) {
  putchar(a[0]);
}

void ffiisEof (char* a) {
  int c = getchar();
  if(c == EOF) {
    a[0] = 0;
  } else {
    a[0] = 1;
    ungetc(c, stdin);
  }
}

void ffigetChar (char* a) {
  a[0] = getchar();
}
