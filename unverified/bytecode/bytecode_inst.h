#include <limits.h>

typedef union {
  struct { unsigned long num1, num2; } two_num;
  unsigned long num;
  long integer;
  char character;
  struct { int isLab; unsigned long num; } loc;
} struct_args;

typedef struct {
  unsigned int tag;
  struct_args args;
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
  union { long number; struct value *block; };
};

typedef struct value value;

#define GET_TAG(v) (v.tag & 0xffff)
#define GET_LEN(v) (v.tag >> 16)
#define SET_TAG(v,t,l) v.tag = ((t) | ((l) << 16))

#define MAX_TAG (0xffff - 4)
#define MAX_BLOCK (ULONG_MAX >> 16)
