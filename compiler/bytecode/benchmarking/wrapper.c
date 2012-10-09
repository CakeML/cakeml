#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <time.h>
#include "wrapper.h"

void asm_exec(long *);

/* main function */

int main(int argc, char** argv) {

  long reps = 10000;  /* number of repetitions */

  if (argc > 1) {
    reps = atoi(argv[1]);
    if (reps < 1) { reps = 1; }
  }

  printf("Bytecode tester (built %s)\n", NOW);

  setvbuf(stdout, NULL, _IONBF, 0); // this line makes sure stdout is not buffered

  long* heap = malloc(8 * 1024 * 1024);
  long* exp_stack = malloc(8 * 1024);

  exp_stack[0] = (long)heap;
  exp_stack[1] = 45;
  exp_stack[2] = reps;

  printf("Starting %ld runs ...\n", reps);

  clock_t start = clock();

  asm_exec(exp_stack);

  clock_t end = clock();
  float seconds = (float)(end - start) / CLOCKS_PER_SEC;

  printf("\n  Resulting stack:\n");

  int k;
  for(k = 0; k < exp_stack[1]; k++) {
    printf("    stack[%d] = %ld\n",k,exp_stack[k+2] / 2);
  }

  printf("\n  Heap:  %ld bytes used\n",exp_stack[0]);
  printf("  Stack: %ld items left on stack\n",exp_stack[1]);
  printf("  Time:  %1.3f seconds for %ld runs\n\n", seconds, reps);

  exit(EXIT_SUCCESS);
}


