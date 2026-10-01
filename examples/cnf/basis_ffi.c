/*
  A trimmed version of the original CakeML basis_ffi.c, customized for checkers.
*/
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

/* madvise, for the huge-page hint on the heap and stack */
#include <sys/mman.h>

#ifdef EVAL
#error "This minimal FFI does not support EVAL"
#endif

#ifndef CML_HEAP_SIZE
#define CML_HEAP_SIZE 4096
#endif
#ifndef CML_STACK_SIZE
#define CML_STACK_SIZE 4096
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

/* Host runtime: optional evaluation */
static void cml_init_eval(int local_argc, char **local_argv) {
  (void)local_argc;
  (void)local_argv;
}

/* Host runtime: exit handling */
void cml_exit(int arg) {
#ifdef STDERR_MEM_EXHAUST
  if (arg == 1) fprintf(stderr, "CakeML heap space exhausted.\n");
  if (arg == 2) fprintf(stderr, "CakeML stack space exhausted.\n");
#endif
  exit(arg);
}

/* Host runtime: code installation */
/* Called out to by the generated code to install len bytes of freshly
 * compiled code at dest. The contract is install_interfer_ok in
 * compiler/backend/semantics/targetSemScript.sml: the destination must end up
 * holding the bytes as they read before the call, whether or not the two
 * regions overlap, hence memmove; and the register that held the source must
 * end up holding the destination, hence the return value. */
void *cml_install(uint8_t *src, size_t len, uint8_t *dest) {
  /* memmove matches the semantics; CakeML's nonoverlapping installs could
   * also use memcpy. */
  memmove(dest, src, len);
  __builtin___clear_cache((char *)dest, (char *)dest + len);
  return dest;
}

/* Host runtime: memory allocation and entry point */
/* Heap and stack sizes are positive decimal numbers of mebibytes. */
static size_t cml_memory_size(const char *name, const char *value,
                              unsigned long long default_mib) {
  const size_t mib = 1024 * 1024;
  char *end;
  if (value == NULL) {
    if (default_mib == 0 || default_mib > SIZE_MAX / mib) {
      cml_runtime_error(0, "invalid default size for %s", name);
    }
    return (size_t)default_mib * mib;
  }
  errno = 0;
  unsigned long long count = strtoull(value, &end, 10);
  if (*value < '0' || *value > '9' || *end != '\0' || errno == ERANGE ||
      count == 0 || count > SIZE_MAX / mib) {
    cml_runtime_error(0, "invalid %s=\"%s\"; expected a positive decimal "
                      "size in MiB within the addressable range", name, value);
  }
  return (size_t)count * mib;
}

static void cml_wrapper_help (const char *progname) {
  printf(
    "usage: %s [--CML_HEAP_SIZE=<n>] [--CML_STACK_SIZE=<n>] [--h] <program arguments ...>\n"
    "\n"
    "This help message is printed by the C wrapper (basis_ffi.c) hosting the\n"
    "CakeML program. It documents the wrapper's own flags only; it is NOT the\n"
    "help for the underlying program itself, which receives all remaining\n"
    "arguments unchanged.\n"
    "\n"
    "  --CML_HEAP_SIZE=<n>   set the CakeML heap size to <n> MiB (default: %d)\n"
    "  --CML_STACK_SIZE=<n>  set the CakeML stack size to <n> MiB (default: %d)\n"
    "  --h                   print this wrapper help message and exit\n",
    progname, CML_HEAP_SIZE, CML_STACK_SIZE);
}

/* Consume wrapper flags and pass the remaining arguments to CakeML. */
static void cml_parse_wrapper_args(size_t *heap_size, size_t *stack_size) {
  unsigned int kept = 1;
  for (unsigned int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--h") == 0) {
      cml_wrapper_help(argv[0]);
      exit(0);
    } else if (strncmp(argv[i], "--CML_HEAP_SIZE=", 16) == 0) {
      *heap_size = cml_memory_size("--CML_HEAP_SIZE", argv[i] + 16,
                                   CML_HEAP_SIZE);
    } else if (strncmp(argv[i], "--CML_STACK_SIZE=", 17) == 0) {
      *stack_size = cml_memory_size("--CML_STACK_SIZE", argv[i] + 17,
                                    CML_STACK_SIZE);
    } else {
      argv[kept++] = argv[i];
    }
  }
  argc = kept;
  argv[kept] = NULL;
}

static void cml_init_memory(void) {
  size_t heap_size = cml_memory_size("--CML_HEAP_SIZE", NULL, CML_HEAP_SIZE);
  size_t stack_size = cml_memory_size("--CML_STACK_SIZE", NULL, CML_STACK_SIZE);
  cml_parse_wrapper_args(&heap_size, &stack_size);
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
  /* MiB alignment puts the heap on a page boundary, as madvise requires;
   * the size is a whole number of MiB, as aligned_alloc requires. */
  cml_heap = aligned_alloc(1024 * 1024, heap_size + stack_size);
  if (cml_heap == NULL) {
    cml_runtime_error(errno, "cannot allocate the heap and stack");
  }
#ifdef MADV_HUGEPAGE
  /* Ask Linux to back the heap and stack with transparent huge pages. */
  madvise(cml_heap, heap_size + stack_size, MADV_HUGEPAGE);
#endif
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
