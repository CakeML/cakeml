#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>

const HEAP_SIZE = 1024 * 1024 * 1024;
const CODE_HEAP_SIZE = 4 * 1024 * 1024;

int main(int argc, char** argv) {
  /* allocate memory -- code heap must have EXEC rights */
  void *codeheap = malloc(CODE_HEAP_SIZE);
  mprotect(codeheap, CODE_HEAP_SIZE, PROT_READ|PROT_WRITE|PROT_EXEC);
  unsigned long long *heap = malloc(HEAP_SIZE);
  /* check precondition
  assert ((& heap) % 8 == 0);
  assert ((& codeheap) % 8 == 0);
  assert (0x100 <= HEAP_SIZE);
  assert (HEAP_SIZE < 0x1000000000000);
  assert (CODE_HEAP_SIZE < 0x1000000000000);
     start verified code */
  heap[0] = HEAP_SIZE;
  heap[1] = (long) (& codeheap);
  heap[2] = CODE_HEAP_SIZE;
  heap[3] = (long) (& putchar);
  heap[4] = (long) (& getchar);
  asm ("    movq %0, %%rax          \n" /* pointer to heap is in rax */
       "    jmp L2                  \n"
       "    .align 4                \n"
       "L1: .include \"asm_code.s\" \n" /* ret address on top of stack */
       "L2: call L1                 \n"
       : /* no output */ : /* input: heap */ "r"(heap)
       : /* clobbered */ "%rax","%rbx","%rcx","%rdx", "memory");
  return 0;
}
