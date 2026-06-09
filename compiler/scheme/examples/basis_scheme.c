#include <stdio.h>

void ffischeme_out (unsigned char *c, long clen, unsigned char *a, long alen) {
    for (int i=0; i<clen; i++) {
        putc(c[i],stdout);
    }
}
