#include<stdio.h>

void ffiputChar(char* a, long len) {
  putchar(a[0]);
}

void ffigetChar(char* a, long len) {
  a[0] = getchar();
}
