/*
  Implements the foreign function interface (FFI) used in the CakeML basis
  library, as a thin wrapper around the relevant system calls.
*/
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <assert.h>

/* clFFI (command line) */

/* argc and argv are exported in cake.S */
extern unsigned int argc;
extern char **argv;

void ffiget_arg_count (unsigned char *c, long clen, unsigned char *a, long alen) {
  a[0] = (char) argc;
  a[1] = (char) (argc / 256);
}

void ffiget_arg_length (unsigned char *c, long clen, unsigned char *a, long alen) {
  int i = a[0] + (a[1] * 256);
  int k = 0;
  while (argv[i][k] != 0) { k++; }
  a[0] = (char) k;
  a[1] = (char) (k / 256);
}

void ffiget_arg (unsigned char *c, long clen, unsigned char *a, long alen) {
  int i = a[0] + (a[1] * 256);
  int k = 0;
  while (argv[i][k] != 0) {
    a[k] = argv[i][k];
    k++;
  }
}

void int_to_byte2(int i, unsigned char *b){
    /* i is encoded on 2 bytes */
    b[0] = (i >> 8) & 0xFF;
    b[1] = i & 0xFF;
}

int byte2_to_int(unsigned char *b){
    return ((b[0] << 8) | b[1]);
}

void int_to_byte8(int i, unsigned char *b){
    /* i is encoded on 8 bytes */
    /* i is cast to long long to ensure having 64 bits */
    /* assumes CHAR_BIT = 8. use static assertion checks? */
    b[0] = ((long long) i >> 56) & 0xFF;
    b[1] = ((long long) i >> 48) & 0xFF;
    b[2] = ((long long) i >> 40) & 0xFF;
    b[3] = ((long long) i >> 32) & 0xFF;
    b[4] = ((long long) i >> 24) & 0xFF;
    b[5] = ((long long) i >> 16) & 0xFF;
    b[6] = ((long long) i >> 8) & 0xFF;
    b[7] =  (long long) i & 0xFF;
}

int byte8_to_int(unsigned char *b){
    return (((long long) b[0] << 56) | ((long long) b[1] << 48) |
             ((long long) b[2] << 40) | ((long long) b[3] << 32) |
             (b[4] << 24) | (b[5] << 16) | (b[6] << 8) | b[7]);
}


/* fsFFI (file system and I/O) */

void ffiopen_in (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(9 <= alen);
  int fd = open((const char *) c, O_RDONLY);
  if (0 <= fd){
    a[0] = 0;
    int_to_byte8(fd, &a[1]);
  }
  else
    a[0] = 1;
}

void ffiopen_out (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(9 <= alen);
  #ifdef __WIN32
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC);
  #else
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
  #endif
  if (0 <= fd){
    a[0] = 0;
    int_to_byte8(fd, &a[1]);
  }
  else
    a[0] = 1;
}

void ffiread (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(clen == 8);
  int fd = byte8_to_int(c);
  int n = byte2_to_int(a);
  assert(alen >= n + 4);
  int nread = read(fd, &a[4], n);
  if(nread < 0){
    a[0] = 1;
  }
  else{
    a[0] = 0;
    int_to_byte2(nread,&a[1]);
  }
}

void ffiwrite (unsigned char *c, long clen, unsigned char *a, long alen){
  assert(clen == 8);
  int fd = byte8_to_int(c);
  int n = byte2_to_int(a);
  int off = byte2_to_int(&a[2]);
  assert(alen >= n + off + 4);
  int nw = write(fd, &a[4 + off], n);
  if(nw < 0){
      a[0] = 1;
  }
  else{
    a[0] = 0;
    int_to_byte2(nw,&a[1]);
  }
}

void fficlose (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(alen >= 1);
  assert(clen == 8);
  int fd = byte8_to_int(c);
  if (close(fd) == 0) a[0] = 0;
  else a[0] = 1;
}

/* GC FFI */
int inGC = 0;
struct timeval t1,t2,lastT;
long microsecs = 0;
int numGC = 0;
int hasT = 0;

void cml_exit(int arg) {
  #ifdef DEBUG_FFI
  {
    fprintf(stderr,"GCNum: %d, GCTime(us): %ld\n",numGC,microsecs);
  }
  #endif
  exit(arg);
}

void ffiexit (unsigned char *c, long clen, unsigned char *a, long alen) {
  if(alen > 0) {
    cml_exit((int)a[0]);
  }
  cml_exit(EXIT_FAILURE);
}


/* empty FFI (assumed to do nothing, but can be used for tracing/logging) */
void ffi (unsigned char *c, long clen, unsigned char *a, long alen) {
  #ifdef DEBUG_FFI
  {
    if (clen == 0)
    {
      if(inGC==1)
      {
        gettimeofday(&t2, NULL);
        microsecs += (t2.tv_usec - t1.tv_usec) + (t2.tv_sec - t1.tv_sec)*1e6;
        numGC++;
        inGC = 0;
      }
      else
      {
        inGC = 1;
        gettimeofday(&t1, NULL);
      }
    } else {
      int indent = 30;
      for (int i=0; i<clen; i++) {
        putc(c[i],stderr);
        indent--;
      }
      for (int i=0; i<indent; i++) {
        putc(' ',stderr);
      }
      struct timeval nowT;
      gettimeofday(&nowT, NULL);
      if (hasT) {
        long usecs = (nowT.tv_usec - lastT.tv_usec) +
                     (nowT.tv_sec - lastT.tv_sec)*1e6;
        fprintf(stderr," --- %ld milliseconds\n",usecs / (long)1000);
      } else {
        fprintf(stderr,"\n");
      }
      gettimeofday(&lastT, NULL);
      hasT = 1;
    }
  }
  #endif
}
