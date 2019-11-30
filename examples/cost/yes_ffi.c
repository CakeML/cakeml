/*
  Implements the foreign function interface (FFI) used in the yes program,
  as a thin wrapper around the relevant system calls.
*/
#include <stdio.h>
#include <stdlib.h>

void ffiput_char (unsigned char *c, long clen, unsigned char *a, long alen) {
  printf(c,"%s");
}

void cml_exit(int arg) {
  exit(arg);
}
