#ifndef BYTECODE_INST_H
#define BYTECODE_INST_H

#include <limits.h>

typedef struct {
  int isLab;
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

/* The lower 16 bits of the value's tag indicates it's type:
 * 0 -> Number
 * 1 -> Code pointer
 * 2 -> Reference pointer
 * 3 -> Stack pointer
 * 4 and over represent a block, where the type of the block depends on how much over 4:
 *    0 -> false
 *    1 -> true
 *    2 -> unit
 *    3 -> closure
 *    higher numbers are used for user-defined constructors.
 *
 * The tag field above these 16 bits indicates the length of the block for 
 * blocks and means nothing for non-blocks.
 */

#define NUMBER 0
#define CODE_PTR 1
#define REF_PTR 2
#define STACK_PTR 3
#define CONS 4

#define FALSE_TAG 0
#define TRUE_TAG 1
#define UNIT_TAG 2
#define CLOSURE_TAG 3

struct value {
  unsigned long tag;
  union { long number; struct value *block; } arg;
};

typedef struct value value;

#define GET_TAG(v) (v.tag & 0xffff)
#define GET_LEN(v) (v.tag >> 16)
#define SET_TAG(v,t,l) v.tag = ((t) | ((l) << 16))

#define MAX_TAG (0xffff - 4)
#define MAX_BLOCK (ULONG_MAX >> 16)

#endif
