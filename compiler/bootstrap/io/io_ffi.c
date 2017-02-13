#include <stdio.h>
#include <string.h>

/*
  argc and argv are exported from cake.S
 */
extern int argc;
extern char **argv;


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

/* NOTE: 256 corresponds to the length of 'a' in the basis library */
#define MAXLEN 256

void ffigetArgs (char *a) {
        int i, j, k;

        for (i = 0, k = 0; (i < argc) && (k < MAXLEN); i++, k++) {
                for (j = 0; j < strlen(argv[i]) && (k+1 < MAXLEN); j++) {
                        a[k++] = argv[i][j];
                }
        }

        return;
}
