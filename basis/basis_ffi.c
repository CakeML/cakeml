#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>

/* commandLine */

/* argc and argv are exported in cake.S */
extern int argc;
extern char **argv;

#define MAXLEN 256

void ffigetArgs (unsigned char *c, long clen, unsigned char *a, long alen) {
        int i, j, k;

        for (i = 0, k = 0; (i < argc) && (k < MAXLEN); i++, k++) {
                for (j = 0; j < strlen(argv[i]) && (k+1 < MAXLEN); j++) {
                        a[k++] = argv[i][j];
                }
        }

        return;
}

/* 0 indicates null fd */
int infds[256] = {STDIN_FILENO, STDOUT_FILENO, STDERR_FILENO, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1};

int nextFD() {
  int fd = 0;
  while(fd < 256 && infds[fd] != -1) fd++;
  return fd;
}

void ffiopen_in (unsigned char *c, long clen, unsigned char *a, long alen) {
  int fd = nextFD();
  if (fd <= 255 && (infds[fd] = open(a, O_RDONLY))){
    a[0] = 0;
    a[1] = fd;
  }
  else
    a[0] = 255;
}

void ffiopen_out (unsigned char *c, long clen, unsigned char *a, long alen) {
  int fd = nextFD();
  if (fd <= 255 && (infds[fd] = open(a, O_RDWR|O_CREAT|O_TRUNC))){
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
/*
void ffiseek (unsigned char *a) {
  int off = lseek(infds[a[0]], a[2], SEEK_SET);
  if (off = -1)
    a[0] = 1;
  else
    a[0] = 0;
}*/
