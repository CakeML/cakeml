#ifndef BYTECODE_INST_H
#define BYTECODE_INST_H

#include <limits.h>
#include <stdbool.h>

typedef struct {
  bool isLab;
  unsigned long num;
} loc;

typedef struct { unsigned long num1, num2; } two_num;

typedef union {
  two_num two_num;
  unsigned long num;
  long integer;
  char character;
  loc loc;
} inst_args;

typedef enum { 
  pop_i, pops_i, shift_i, push_int_i, cons_i, load_i, store_i, load_rev_i,
  el_i, tag_eq_i, is_block_i, equal_i, add_i, sub_i, mult_i, div_i, mod_i,
  less_i, label_i, jump_i, jump_if_i, call_i, jump_ptr_i, call_ptr_i,
  push_ptr_i, return_i, push_exc_i, pop_exc_i, ref_i, deref_i, update_i,
  stop_i, tick_i, print_i, print_c_i
} inst_tag;

typedef struct {
  inst_tag tag;
  inst_args args;
} inst;

struct inst_list {
  inst car;
  struct inst_list* cdr;
};

typedef struct inst_list inst_list;

#define MAX_TAG (0xffff - 4)
#define MAX_BLOCK (ULONG_MAX >> 16)

#endif
