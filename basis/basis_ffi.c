/*
  Implements the foreign function interface (FFI) used in the CakeML basis
  library, as a thin wrapper around the relevant system calls.
*/
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <assert.h>
#ifdef EVAL
#include <sys/time.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <signal.h>
#endif

/* This flag is on by default. It catches CakeML's out-of-memory exit codes
 * and prints a helpful message to stderr.
 * Note that this is not specified by the basis library.
 * */
#define STDERR_MEM_EXHAUST

/* clFFI (command line) */

unsigned int argc;
char **argv;

/* exported in cake.S */
extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

extern char cake_text_begin;
extern char cake_codebuffer_begin;
extern char cake_codebuffer_end;

#ifdef EVAL

/* Signal handler for SIGINT */

/* This is set to 1 when the runtime traps a SIGINT */
volatile sig_atomic_t caught_sigint = 0;

void do_sigint(int sig_num)
{
    signal(SIGINT, do_sigint);
    caught_sigint = 1;
}

void ffipoll_sigint (unsigned char *c, long clen, unsigned char *a, long alen)
{
    if (alen < 1) {
        return;
    }
    a[0] = (unsigned char) caught_sigint;
    caught_sigint = 0;
}

void ffikernel_ffi (unsigned char *c, long clen, unsigned char *a, long alen) {
    for (long i = 0; i < clen; i++) {
        putc(c[i], stdout);
    }
}

#else

void ffipoll_sigint (unsigned char *c, long clen, unsigned char *a, long alen) { }

void ffikernel_ffi (unsigned char *c, long clen, unsigned char *a, long alen) { }

#endif

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
  #ifdef EVAL
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
  #else
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC);
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

  #ifdef STDERR_MEM_EXHAUST
  if (arg != 0) {
    fprintf(stderr,"Program exited with nonzero exit code.\n");
  }
  #endif

  #ifdef DEBUG_FFI
  {
    if(arg == 1) {
      fprintf(stderr,"CakeML heap space exhausted.\n");
    }
    else if(arg == 2) {
      fprintf(stderr,"CakeML stack space exhausted.\n");
    }
    fprintf(stderr,"GCNum: %d, GCTime(us): %ld\n",numGC,microsecs);
  }
  #endif

  exit(arg);
}

void ffiexit (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(alen == 1);
  exit((int)a[0]);
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

typedef union {
  double d;
  char bytes[8];
} double_bytes;

// FFI calls for floating-point parsing
void ffidouble_fromString (char *c, long clen, char *a, long alen) {
  double_bytes d;
  sscanf(c, "%lf",&d.d);
  assert (8 == alen);
  for (int i = 0; i < 8; i++){
    a[i] = d.bytes[i];
  }
}

void ffidouble_toString (char *c, long clen, char *a, long alen) {
  double_bytes d;
  assert (256 == alen);
  for (int i = 0; i < 8; i++){
    d.bytes[i] = a[i];
  }
  //snprintf always terminates with a 0 byte if space was sufficient
  int bytes_written = snprintf(&a[0], 255, "%.20g", d.d);
  // snprintf returns number of bytes it would have written if the buffer was
  // large enough -> check that it did not write more than the buffer size - 1
  // for the 0 byte
  assert (bytes_written <= 255);
}

void cml_clear() {
  __builtin___clear_cache(&cake_codebuffer_begin, &cake_codebuffer_end);
}

int main (int local_argc, char **local_argv) {

  argc = local_argc;
  argv = local_argv;

  char *heap_env = getenv("CML_HEAP_SIZE");
  char *stack_env = getenv("CML_STACK_SIZE");
  char *temp; //used to store remainder of strtoul parse

  unsigned long sz = 1024*1024; // 1 MB unit
  unsigned long cml_heap_sz = 1024 * sz;    // Default: 1 GB heap
  unsigned long cml_stack_sz = 1024 * sz;   // Default: 1 GB stack

  // Read CML_HEAP_SIZE env variable (if present)
  // Warning: strtoul may overflow!
  if(heap_env != NULL)
  {
    cml_heap_sz = strtoul(heap_env, &temp, 10);
    cml_heap_sz *= sz; //heap size is read in units of MBs
  }

  if(stack_env != NULL)
  {
    cml_stack_sz = strtoul(stack_env, &temp, 10);
    cml_stack_sz *= sz; //stack size is read in units of MBs
  }

  if(cml_heap_sz < sz || cml_stack_sz < sz) //At least 1MB heap and stack size
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"Too small requested heap (%lu) or stack (%lu) size in bytes.\n",cml_heap_sz, cml_stack_sz);
    #endif
    exit(3);
  }

  if(cml_heap_sz + cml_stack_sz < 8192) // Global minimum heap/stack for CakeML. 4096 for 32-bit architectures
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"Too small requested heap (%lu) + stack (%lu) size in bytes.\n",cml_heap_sz, cml_stack_sz);
    #endif
    exit(3);
  }

  /**
   *  CakeML and its default assembly wrapper expects the following memory layout:
   *
   *  cml_heap      cml_stack      cml_stackend
   *  |             |              |
   *  V             v              v
   *  |--- heap ---||--- stack ---|
   *
   *  The heap/stack are assumed to be in contiguous memory,
   *  cml_heap points to the first address of the heap,
   *  cml_stack points to 1 address past the end of the heap (i.e., the first address of the stack),
   *  cml_stackend points to 1 address past the end of the stack.
   *
   *  All cml_* pointers must be word aligned.
   *  The position cml_stack may be (slightly) dynamically adjusted by CakeML,
   *  see `get_stack_heap_limit` in stack_removeProof
   **/

  cml_heap = malloc(cml_heap_sz + cml_stack_sz); // allocate both heap and stack at once

  if(cml_heap == NULL)
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"failed to allocate sufficient CakeML heap and stack space.\n");
    perror("malloc");
    #endif
    exit(3);
  }

  cml_stack = cml_heap + cml_heap_sz;
  cml_stackend = cml_stack + cml_stack_sz;

  #ifdef EVAL

  /** Set up the "eval" code buffer to be read-write-execute. **/
  if(mprotect(&cake_text_begin, &cake_codebuffer_end - &cake_text_begin,
              PROT_READ | PROT_WRITE | PROT_EXEC))
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"failed to set permissions for CakeML code buffer.\n");
    perror("mprotect");
    #endif
    exit(3);
  }

  /* Set up the signal handler for SIGINTs when running the REPL. */
  for (int i = 0; i < local_argc; i++) {
      if (strcmp(local_argv[i], "--repl") == 0 ||
          strcmp(local_argv[i], "--candle") == 0) {
        signal(SIGINT, do_sigint);
        break;
      }
  }

  #endif

  cml_main(); // Passing control to CakeML

  return 0;
}
