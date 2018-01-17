#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/time.h>

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

/* fsFFI (file system and I/O) */

/* 0 indicates null fd */
int infds[256] = {STDIN_FILENO, STDOUT_FILENO, STDERR_FILENO, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1};

int nextFD() {
  int fd = 0;
  while(fd < 256 && infds[fd] != -1) fd++;
  return fd;
}

void ffiopen_in (unsigned char *c, long clen, unsigned char *a, long alen) {
  int fd = nextFD();
  if (fd <= 255 && (infds[fd] = open((const char *) a, O_RDONLY))){
    a[0] = 0;
    a[1] = fd;
  }
  else
    a[0] = 255;
}

void ffiopen_out (unsigned char *c, long clen, unsigned char *a, long alen) {
  int fd = nextFD();
  if (fd <= 255 && (infds[fd] = open((const char *) a, O_RDWR|O_CREAT|O_TRUNC))){
    a[0] = 0;
    a[1] = fd;
  }
  else
    a[0] = 255;
}

void ffiread (unsigned char *c, long clen, unsigned char *a, long alen) {
  int nread = read(infds[a[0]], &a[3], a[1]);
  if(nread < 0){
    a[0] = 1;
  }
  else{
    a[0] = 0;
    a[1] = nread;
  }
}

void ffiwrite (unsigned char *c, long clen, unsigned char *a, long alen){
  int nw = write(infds[a[0]], &a[3+a[2]], a[1]);
  if(nw < 0){
      a[0] = 1;
  }

  else{
    a[0] = 0;
    a[1] = nw;
  }
}

void fficlose (unsigned char *c, long clen, unsigned char *a, long alen) {
  if (infds[a[0]] && close(infds[a[0]]) == 0) {
    infds[a[0]] = -1;
    a[0] = 1;
  }
  else
    a[0] = 0;
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
    printf("GCNum: %d, GCTime(us): %ld\n",numGC,microsecs);
  }
  #endif
  exit(arg);
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
