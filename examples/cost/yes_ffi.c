/*
  Implements the foreign function interface (FFI) used in the yes program,
  as a thin wrapper around the relevant system calls.
*/
#include <stdio.h>
#include <stdlib.h>

/* This flag is on by default. It catches CakeML's out-of-memory exit codes
 * and prints a helpful message to stderr.
 * Note that this is not specified by the basis library.
 * */
#define STDERR_MEM_EXHAUST

/* exported in cake.S */
extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

void ffiput_char (unsigned char *c, long clen, unsigned char *a, long alen) {
  printf(c,"%s");
}

void cml_exit(int arg) {

  #ifdef STDERR_MEM_EXHAUST
  // These should never be called if the CakeML program is proved to be
  // safe for space and sufficient heap/stack space is provided
  if(arg == 1) {
    fprintf(stderr,"CakeML heap space exhausted.\n");
  }
  else if(arg == 2) {
    fprintf(stderr,"CakeML stack space exhausted.\n");
  }
  #endif

  exit(arg);
}

void main (int argc, char **argv) {

  unsigned long sz = 1024*1024; // 1 MB unit
  unsigned long cml_heap_sz = 1024 * sz;    // Default: 1 GB heap
  unsigned long cml_stack_sz = 1024 * sz;   // Default: 1 GB stack

  if(cml_heap_sz + cml_stack_sz < cml_heap_sz)
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"Overflow in requested heap (%lu) + stack (%lu) size in bytes.\n",cml_heap_sz, cml_stack_sz);
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
    fprintf(stderr,"malloc() failed to allocate sufficient CakeML heap and stack space.\n");
    #endif
    exit(3);
  }

  cml_stack = cml_heap + cml_heap_sz;
  cml_stackend = cml_stack + cml_stack_sz;

  cml_main(); // Passing control to CakeML
}
