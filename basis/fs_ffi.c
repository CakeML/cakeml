#include <stdio.h>
#include <string.h>
#include <unistd.h>

FILE* infds[256];

int nextFD() {
  int fd = 0;
  while(fd < 256 && infds[fd] != NULL) fd++;
  return fd;
}

void ffiopen_in (char *a) {
  int fd = nextFD();
  if (fd < 255 && (infds[fd] = fopen(a,"r")))
    a[0] = fd;
  else
    a[0] = 255;
}

void ffiopen_out (char *a) {
  int fd = nextFD();
  if (fd < 255 && (infds[fd] = fopen(a,"w")))
    a[0] = fd;
  else
    a[0] = 255;
}

void ffiread (char *a) {
  int nread = read(fileno(infds[a[0]]), &a[2], a[1]);
  if(nread < 0) a[0] = 0;
  else{
    a[0] = 1; 
    a[1] = nread;
  }
}

void ffiwrite (char * a){
  int nw = write(fileno(infds[a[0]]), &a[2], a[1]);  
  if(nw < 0) a[0] = 0;
  else{
    a[0] = 1; 
    a[1] = nw;
  }
}

void fficlose (char *a) {
  if (infds[a[0]] && fclose(infds[a[0]]) == 0) {
    infds[a[0]] = NULL;
    a[0] = 1;
  }
  else
    a[0] = 0;
}

void ffiseek (char *a) {
  int off = lseek(fileno(infds[a[0]]), a[2], SEEK_SET);
  if (off = -1)
    a[0] = 1;
  else
    a[0] = 0;
}
