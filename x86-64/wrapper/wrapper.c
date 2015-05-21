#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>

const long long HEAP_SIZE = 1024 * 1024 * 1024;
const long long CODE_HEAP_SIZE = 1024 * 1024 * 1024;

char * alloc_executable(size_t len) { /* len = number of bytes */
  /* Local variables */
  size_t page_size = getpagesize();
  /* Round up so that len is a multiple of getpagesize() */
  if (len % page_size) {
    len &= ~(page_size-1);
    len += page_size;
  }
  /* Open a file for use as scratch memory */
  int fd = 0, ret = 0;
  void *pa = MAP_FAILED;
  char template[] = "/tmp/alloc_executable_XXXXXX";
  fd = mkstemp(template);
  if (fd < 0) return pa;
  unlink(template);
  ret = ftruncate(fd, len);
  if (ret < 0) return pa;
  /* Do the allocation */
  return mmap(NULL, len, PROT_READ|PROT_WRITE|PROT_EXEC, MAP_PRIVATE, fd, 0);
}

int main(int argc, char** argv) {
  /* allocate memory -- code heap must have EXEC rights */
  char *codeheap = alloc_executable(CODE_HEAP_SIZE);
  unsigned long long *heap = malloc(HEAP_SIZE + 16);
  /* start verified code */
  heap[2] = HEAP_SIZE;
  heap[3] = (long) codeheap;
  heap[4] = CODE_HEAP_SIZE;
  heap[5] = (long) (& putchar);
  heap[6] = (long) (& getchar);
  printf(" -- CakeML starting up --\n");
  asm ("    movq %0, %%rax          \n" /* pointer to heap is in rax */
       "    addq $16, %%rax         \n"
       "    pushq %%rsi             \n"
       "    pushq %%rdi             \n"
       "    pushq %%rbp             \n"
       "    jmp L2                  \n"
       "    .align 4                \n"
       "L1: .include \"asm_code.s\" \n" /* ret address on top of stack */
       "L2: call L1                 \n"
       "    popq %%rbp              \n"
       "    popq %%rdi              \n"
       "    popq %%rsi              \n"
       : /* no output */ : /* input: heap */ "r"(heap)
       : /* clobbered */ "%rax","%rbx","%rcx","%rdx",
         "%r8","%r9","%r10","%r11","%r12","%r13","%r14","%r15","memory");
  printf("\n -- CakeML shutting down --\n");
  return 0;
}
