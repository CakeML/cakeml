/*
  Implements the foreign function interface (FFI) used in the CakeML basis
  library, as a thin wrapper around the relevant system calls.
*/
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#include <assert.h>
#include <errno.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* TextIO FFI (POSIX) */
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

/* Double FFI */
#include <math.h>

/* GC and tracing */
#ifdef DEBUG_FFI
#include <sys/time.h> /* POSIX */
#endif

/* Interactive evaluation */
#ifdef EVAL
#include <signal.h>
#include <sys/mman.h> /* POSIX */
#endif

/* This flag is on by default. It catches CakeML's out-of-memory exit codes
 * and prints a helpful message to stderr.
 * Note that this is not specified by the basis library.
 * */
#define STDERR_MEM_EXHAUST

/* Host runtime arguments, shared with the CommandLine FFI. */
unsigned int argc;
char **argv;

/* exported in CakeML .S file */
extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

static void cml_runtime_error(int error, const char *format, ...) {
#ifdef STDERR_MEM_EXHAUST
  va_list args;
  va_start(args, format);
  fputs("CakeML: ", stderr);
  vfprintf(stderr, format, args);
  va_end(args);
  if (error) fprintf(stderr, ": %s", strerror(error));
  fputs(".\n", stderr);
#endif
  exit(3);
}

/* CommandLine FFI (clFFI) */
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

/* TextIO FFI (fsFFI): file descriptors and byte encodings */
static void int_to_byte2(int i, unsigned char *b){
    /* i is encoded on 2 bytes */
    b[0] = (i >> 8) & 0xFF;
    b[1] = i & 0xFF;
}

static int byte2_to_int(unsigned char *b){
    return ((b[0] << 8) | b[1]);
}

static void int_to_byte8(int i, unsigned char *b){
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

static int byte8_to_int(unsigned char *b){
    return (((long long) b[0] << 56) | ((long long) b[1] << 48) |
             ((long long) b[2] << 40) | ((long long) b[3] << 32) |
             (b[4] << 24) | (b[5] << 16) | (b[6] << 8) | b[7]);
}

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
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
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

/* Runtime FFI */
void ffiexit (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(alen == 1);
  exit((int)a[0]);
}

void fficustom (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(0 <= alen);
  assert(0 <= clen);
}

/* Double FFI */
typedef union {
    double num;
    char bytes[sizeof(double)];
} double_bytes;

typedef union {
    int64_t num;
    char bytes[sizeof(int64_t)];
} int_bytes;

void ffidouble_fromString(char *c, long clen, char *a, long alen) {
    double_bytes d;
    char *endp;
    errno = 0;
    d.num = strtod(c, &endp);
    if (errno == ERANGE || (endp && *endp != '\0')) {
        a[0] = 1;
    } else {
        a[0] = 0;
        memcpy(&a[1], d.bytes, sizeof d.bytes);
    }
}

void ffidouble_toString(char *c, long clen, char *a, long alen) {
    double_bytes d;
    memcpy(d.bytes, a, sizeof d.bytes);
    snprintf(a, 255, "%.20g", d.num);
}

void ffidouble_fromInt(char *c, long clen, char *a, long alen) {
    double_bytes d;
    int_bytes i;
    memcpy(i.bytes, a, sizeof i.bytes);
    d.num = (double) i.num;
    memcpy(a, d.bytes, sizeof d.bytes);
}

void ffidouble_toInt(char *c, long clen, char *a, long alen) {
    double_bytes d;
    int_bytes i;
    memcpy(d.bytes, a, sizeof d.bytes);
    i.num = (int64_t) d.num;
    memcpy(a, i.bytes, sizeof i.bytes);
}

void ffidouble_pow(char *c, long clen, char *a, long alen) {
    double_bytes x, y;
    memcpy(x.bytes, a, sizeof x.bytes);
    memcpy(y.bytes, &a[8], sizeof y.bytes);
    x.num = pow(x.num, y.num);
    memcpy(a, x.bytes, sizeof x.bytes);
}

void ffidouble_ln(char *c, long clen, char *a, long alen) {
    double_bytes d;
    memcpy(d.bytes, a, sizeof d.bytes);
    d.num = log(d.num);
    memcpy(a, d.bytes, sizeof d.bytes);
}

void ffidouble_exp(char *c, long clen, char *a, long alen) {
    double_bytes d;
    memcpy(d.bytes, a, sizeof d.bytes);
    d.num = exp(d.num);
    memcpy(a, d.bytes, sizeof d.bytes);
}

void ffidouble_floor(char *c, long clen, char *a, long alen) {
    double_bytes d;
    memcpy(d.bytes, a, sizeof d.bytes);
    d.num = floor(d.num);
    memcpy(a, d.bytes, sizeof d.bytes);
}

/* Interactive evaluation: Interrupt and Candle kernel FFIs */
#ifdef EVAL
/* exported in CakeML .S file */
extern char cake_text_begin;
extern char cake_codebuffer_begin;
extern char cake_codebuffer_end;

static size_t cml_page_size;

/* Signal handler for SIGINT */
/* This is set to 1 when the runtime traps a SIGINT */
static volatile sig_atomic_t caught_sigint = 0;

static void do_sigint(int sig_num)
{
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

static void cml_init_eval(int local_argc, char **local_argv) {
  long page_size = sysconf(_SC_PAGESIZE);
  if (page_size <= 0) {
    cml_runtime_error(0, "cannot determine the page size");
  }
  cml_page_size = (size_t)page_size;
  uintptr_t text = (uintptr_t)&cake_text_begin;
  uintptr_t begin = (uintptr_t)&cake_codebuffer_begin;
  uintptr_t end = (uintptr_t)&cake_codebuffer_end;
  if (text > begin || begin > end ||
      begin - begin % cml_page_size < text || end % cml_page_size != 0) {
    cml_runtime_error(0,
      "unsafe text and code buffer page layout (page size %zu; "
      "text %p, buffer begin %p, buffer end %p)",
      cml_page_size, (void *)&cake_text_begin,
      (void *)&cake_codebuffer_begin, (void *)&cake_codebuffer_end);
  }
  for (int i = 0; i < local_argc; i++) {
    if (strcmp(local_argv[i], "--repl") == 0 ||
        strcmp(local_argv[i], "--candle") == 0) {
      struct sigaction action = {0};
      action.sa_handler = do_sigint;
      action.sa_flags = SA_RESTART;
      sigemptyset(&action.sa_mask);
      if (sigaction(SIGINT, &action, NULL) != 0) {
        cml_runtime_error(errno, "cannot install the SIGINT handler");
      }
      break;
    }
  }
}

#else

void ffipoll_sigint (unsigned char *c, long clen, unsigned char *a, long alen) { }

void ffikernel_ffi (unsigned char *c, long clen, unsigned char *a, long alen) { }

static void cml_init_eval(int local_argc, char **local_argv) { }

#endif

/* Host runtime: exit handling, GC and tracing FFI */
#ifdef DEBUG_FFI
static int inGC = 0;
static struct timeval t1,t2,lastT;
static long microsecs = 0;
static int numGC = 0;
static int hasT = 0;
static long prevOcc = 0;
static long numAllocBytes = 0;
#endif

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
    fprintf(stderr,"Total allocated heap data: %ld bytes\n",numAllocBytes);
  }
  #endif

  exit(arg);
}

void cml_err(int arg) {
  if (arg == 3) {
    fprintf(stderr,"Memory not ready for entry. You may have not run the init code yet, or be trying to enter during an FFI call.\n");
  }

  cml_exit(arg);
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
        long occ = (long)c; // number of bytes in occupied in heap (all live after standard GC)
        // long len = (long)a;
        // fprintf(stderr,"GC stops  %ld %ld \n",occ,len);
        prevOcc = occ;
      }
      else
      {
        inGC = 1;
        gettimeofday(&t1, NULL);
        long occ = (long)c;
        // long len = (long)a;
        // fprintf(stderr,"GC starts %ld %ld \n",occ,len);
        numAllocBytes += (occ - prevOcc);
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

/* Host runtime: code installation */
/* Called out to by the generated code to install len bytes of freshly
 * compiled code at dest. The contract is install_interfer_ok in
 * compiler/backend/semantics/targetSemScript.sml: the destination must end up
 * holding the bytes as they read before the call, whether or not the two
 * regions overlap, hence memmove; and the register that held the source must
 * end up holding the destination, hence the return value. */
void *cml_install(uint8_t *src, size_t len, uint8_t *dest) {
#ifdef EVAL
  if (len == 0) return dest;
  /* CakeML guarantees that the destination range is inside the code buffer. */
  size_t offset = (uintptr_t)dest % cml_page_size;
  void *start = (void *)((uintptr_t)dest - offset);
  size_t size = len + offset;
  if (mprotect(start, size, PROT_WRITE) != 0) {
    cml_runtime_error(errno, "cannot make the code buffer writable");
  }
#endif
  /* memmove matches the semantics; CakeML's nonoverlapping installs could
   * also use memcpy. */
  memmove(dest, src, len);
  __builtin___clear_cache((char *)dest, (char *)dest + len);
#ifdef EVAL
  if (mprotect(start, size, PROT_READ | PROT_EXEC) != 0) {
    cml_runtime_error(errno, "cannot make the code buffer executable");
  }
#endif
  return dest;
}

/* Host runtime: memory allocation and entry point */
/* Heap and stack sizes are positive decimal numbers of mebibytes. */
static size_t cml_memory_size(const char *name) {
  const size_t mib = 1024 * 1024;
  const char *value = getenv(name);
  char *end;
  if (value == NULL) return 1024 * mib;
  errno = 0;
  unsigned long long count = strtoull(value, &end, 10);
  if (*value < '0' || *value > '9' || *end != '\0' || errno == ERANGE ||
      count == 0 || count > SIZE_MAX / mib) {
    cml_runtime_error(0, "invalid %s=\"%s\"; expected a positive decimal "
                      "size in MiB within the addressable range", name, value);
  }
  return (size_t)count * mib;
}

static void cml_init_memory(void) {
  size_t heap_size = cml_memory_size("CML_HEAP_SIZE");
  size_t stack_size = cml_memory_size("CML_STACK_SIZE");
  if (heap_size > SIZE_MAX - stack_size) {
    cml_runtime_error(0, "heap and stack size overflow");
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
  cml_heap = malloc(heap_size + stack_size);
  if (cml_heap == NULL) {
    cml_runtime_error(errno, "cannot allocate the heap and stack");
  }
  cml_stack = (uint8_t *)cml_heap + heap_size;
  cml_stackend = (uint8_t *)cml_stack + stack_size;
}

int main(int local_argc, char **local_argv) {
  argc = local_argc;
  argv = local_argv;
  cml_init_memory();
  cml_init_eval(local_argc, local_argv);
  cml_main();
  return 0;
}
