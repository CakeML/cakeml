#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include "bytecode_inst.h"

extern FILE *yyin;
extern int yyparse(inst_list **parse_result);
extern inst_list* decode(FILE *in);

unsigned long static inline get_loc(loc loc) {
  if (loc.isLab)
    assert(false);
  return loc.num;
}

unsigned long inst_list_length(inst_list *l) {
  unsigned long len = 0;
  while (l != NULL) {
    len++;
    l = l->cdr;
  };
  return len;
}

inst* inst_list_to_array(inst_list *l, unsigned long length) {
  unsigned long i;
  inst_list *next;
  inst *prog_array = malloc((length + 1) * sizeof(inst));

  for (i = length; i > 0; i--) {
    next = l->cdr;
    prog_array[i-1] = l->car;
    free(l); 
    l = next;
  };

  prog_array[length].tag = stop_i; 

  return prog_array;
}

void check_locations(inst *prog, unsigned long num_inst) {
  unsigned long i;
  unsigned long loc;

  for(i = 0; i < num_inst; i++) {
    if (prog[i].tag == jump_i || prog[i].tag == jump_if_i || prog[i].tag == call_i || prog[i].tag == push_ptr_i) {
      loc = get_loc(prog[i].args.loc);
      if (loc >= num_inst) {
	printf("instruction number %lu has bad location %lu\n", i, loc);
	exit(1);
      }
    }
  }
  return;
}
 
/* We represent values as single words.  If the lowest bit is 0, then it is a
 * signed fixnum.  Code pointers and stack pointers are also represented as
 * fixnums.  If the lowest bit is 1 and the next lowest bit is also 1, then it
 * is a pointer to a bignum, non-empty block, or reference.  If the lowest two
 * bits are 01, then it is an empty block.  Non-empty blocks, references and
 * bignums all start with a header word.  The lower 16 bits of the header are
 * its tag, and the remaining bits are the size of the object. */

typedef unsigned long value;
typedef long fixnum;

static inline bool is_fixnum(value v) {
  return ((v & 0x1) == 0x0);
}

static inline fixnum get_fixnum(value v) {
  return (((fixnum)v) >> 1);
}

static inline value tag_fixnum(fixnum n) {
  return (n << 1);
}

static inline value get_unsigned_fixnum(value v) {
  return (v >> 1);
}

static inline value tag_unsigned_fixnum(value n) {
  return (n << 1);
}

static inline bool is_empty_block(value v) {
  return ((v & 0x3) == 0x1);
}

static inline value get_empty_block(value v) {
  return (v >> 2);
}

static inline value tag_empty_block(value v) {
  return ((v << 2) | 0x1);
}

static inline bool is_pointer(value v) {
  return ((v & 0x3) == 0x3);
}

static inline value get_pointer(value v) {
  return (v >> 2);
}

static inline value tag_pointer(value v) {
  return ((v << 2) | 0x3);
}

typedef enum { 
  bignum_tag = 0, 
  ref_tag = 1, 
  /* The following are 2 greater than the compiler expects in emitted cons
   * instructions. */
  false_tag = 2, 
  true_tag = 3, 
  unit_tag = 4, 
  closure_tag = 5
} block_tag;

static inline block_tag get_header_tag(value h) {
  return (h & 0xffff);
}

static inline value get_header_size(value h) {
  return (h >> 16);
}

static inline value build_header(block_tag tag, unsigned long length) {
  return ((length << 16) | tag);
}

void static print_value(value *heap, value v) {
  if (is_fixnum(v)) {
    fixnum n = get_fixnum(v);
    if (n < 0)
      printf("~%ld",-n);
    else
      printf("%ld",n);
  }
  else if (is_empty_block(v))
    switch (get_empty_block(v)) {
      case true_tag:
        printf("true");
	break;
      case false_tag:
	printf("false");
	break;
      case unit_tag:
	printf("()");
	break;
      default:
	printf("<constructor>");
	break;
    }
  else
    switch (get_header_tag(heap[get_pointer(v)])) {
      case ref_tag:
        printf("<ref>");
	break;
      default:
	printf("<constructor>");
	break;
    }
}

static inline value bool_to_val(bool i) {
  if (i)
    return tag_empty_block(true_tag);
  else
    return tag_empty_block(false_tag);
}

static inline int value_cmp(value v1, value v2) {
  if (v1 == v2)
    return 1;
  else
    return 0;
}

static int equal(value *heap, value v1, value v2) {
  if ((is_fixnum(v1) && is_fixnum(v2)) || (is_empty_block(v1) && is_empty_block(v2)))
    return value_cmp(v1,v2);
  else if (is_pointer(v1) && is_pointer(v2)) {
    value p1 = get_pointer(v1);
    value p2 = get_pointer(v2);
    value h1 = heap[p1];
    value h2 = heap[p2];
    value tag1 = get_header_tag(h1);
    value tag2 = get_header_tag(h2);
    if (tag1 == closure_tag || tag2 == closure_tag)
      return 2;
    else if (tag1 != tag2)
      return 0;
    else if (tag1 == ref_tag)
      return value_cmp(v1,v2);
    else {
      int i;
      for (i = 1; i <= get_header_size(h1); i++) {
	int res = equal(heap, heap[p1+i], heap[p2+i]);
	if (res != 1)
	  return res;
      }
      return 1;
    }
  }
  else 
    return 0;
}

static inline fixnum sml_div(fixnum n1, fixnum n2) {
  if (n1 % n2 != 0 && ((n1 < 0) != (n2 < 0)))
    return ((n1 / n2) - 1);
  else
    return (n1 / n2);
}

static inline fixnum sml_mod(fixnum n1, fixnum n2) {
  return (n1 - sml_div(n1,n2) * n2);
}


#define STACK_SIZE 1000000
#define HEAP_SIZE 1000000

static value stack[STACK_SIZE];
static value heap[HEAP_SIZE];

static inline void check_stack(unsigned int sp) { 
  if (sp >= STACK_SIZE) {
    printf("stack overflow\n"); 
    exit(1); 
  }
}

static inline void check_heap(unsigned int next_heap) { 
  if (next_heap >= HEAP_SIZE) {
    printf("heap overflow\n"); 
    exit(1);
  }
}

void run(inst code[]) {

  /* The stack pointer sp will point to the lowest unused stack slot */
  unsigned long sp = 0;
  unsigned long pc = 0;
  unsigned long handler = 0;
  unsigned long next_heap = 0;

  unsigned long tmp_sp1, tmp_sp2;
  value tmp_frame;
  int tmp;
  bool b;

  while (true) {

    switch (code[pc].tag) {
      case pop_i:
	sp--;
	pc++;
	break;
      case pops_i:
	tmp_sp1 = sp;
	sp -= code[pc].args.num;
	stack[sp-1] = stack[tmp_sp1-1];
	pc++;
	break;
      case shift_i:
	if (code[pc].args.two_num.num2 != 0) {
	  tmp_sp1 = sp - code[pc].args.two_num.num1;
	  tmp_sp2 = tmp_sp1 - code[pc].args.two_num.num2;
	  for (; tmp_sp1 < sp; tmp_sp1++, tmp_sp2++)
	    stack[tmp_sp2] = stack[tmp_sp1];
	  sp = tmp_sp2;
	}
	pc++;
	break;
      case push_int_i:
	check_stack(sp);
	stack[sp] = tag_fixnum(code[pc].args.num);
	sp++;
	pc++;
	break;
      case cons_i:
	if (code[pc].args.two_num.num2 == 0) {
	  check_stack(sp);
	  stack[sp] = tag_empty_block(code[pc].args.two_num.num1);
	  sp++;
	}
	else {
	  unsigned long i, tag, length;
	  tag = code[pc].args.two_num.num1 + 2;
	  length = code[pc].args.two_num.num2;
	  check_heap(next_heap + length);
	  heap[next_heap] = build_header(tag,length);
	  for (i = 0; i < length; i++)
	    heap[next_heap+1+i] = stack[sp-length+i];
	  sp -= length;
	  stack[sp] = tag_pointer(next_heap);
	  next_heap += 1 + length;
	  sp++;
	}
	pc++;
	break;
      case load_i:
	check_stack(sp);
	stack[sp] = stack[sp-1-code[pc].args.num];
	sp++;
	pc++;
	break;
      case store_i:
	stack[sp-2-code[pc].args.num] = stack[sp-1];
	sp--;
	pc++;
	break;
      case load_rev_i:
	check_stack(sp);
	stack[sp] = stack[code[pc].args.num];
	sp++;
	pc++;
	break;
      case el_i:
	stack[sp-1] = heap[get_pointer(stack[sp-1]) + code[pc].args.num + 1];
	pc++;
	break;
      case tag_eq_i:
	if (is_empty_block(stack[sp-1]))
  	  stack[sp-1] = bool_to_val(code[pc].args.num == get_empty_block(stack[sp-1]));
        else
	  stack[sp-1] = bool_to_val(get_header_tag(heap[get_pointer(stack[sp-1])]) == code[pc].args.num + 2);
	pc++;
	break;
      case is_block_i:
	if (is_empty_block(stack[sp-1]))
	  stack[sp-1] = bool_to_val(true);
	else
	  stack[sp-1] = bool_to_val(get_header_tag(heap[get_pointer(stack[sp-1])]) >= 2);
	pc++;
	break;
      case equal_i:
	tmp = equal(heap, stack[sp-1], stack[sp-2]);
	if (tmp == 0 || tmp == 1)
	  stack[sp-2] = bool_to_val(tmp);
	else {
	  stack[sp-2] = tag_fixnum(0);
	}
	sp--;
	pc++;
	break;
      case less_i:
	stack[sp-2] = bool_to_val(get_fixnum(stack[sp-2]) < get_fixnum(stack[sp-1]));
	sp--;
	pc++;
	break;
      case add_i:
	stack[sp-2] = tag_fixnum(get_fixnum(stack[sp-2]) + get_fixnum(stack[sp-1]));
	sp--;
	pc++;
	break;
      case sub_i:
	stack[sp-2] = tag_fixnum(get_fixnum(stack[sp-2]) - get_fixnum(stack[sp-1]));
	sp--;
	pc++;
	break;
      case mult_i:
	stack[sp-2] = tag_fixnum(get_fixnum(stack[sp-2]) * get_fixnum(stack[sp-1]));
	sp--;
	pc++;
	break;
      case div_i:
	stack[sp-2] = tag_fixnum(sml_div(get_fixnum(stack[sp-2]), get_fixnum(stack[sp-1])));
	sp--;
	pc++;
	break;
      case mod_i:
	stack[sp-2] = tag_fixnum(sml_mod(get_fixnum(stack[sp-2]), get_fixnum(stack[sp-1])));
	sp--;
	pc++;
	break;
      case label_i:
	pc++;
	break;
      case jump_i:
	pc = get_loc(code[pc].args.loc);
	break;
      case jump_if_i:
	if (get_empty_block(stack[sp-1]) == true_tag)
	  pc = get_loc(code[pc].args.loc);
	else
	  pc++;
	sp--;
	break;
      case call_i:
	check_stack(sp);
	stack[sp] = stack[sp-1];
	stack[sp-1] = tag_unsigned_fixnum(pc+1);
	pc = get_loc(code[pc].args.loc);
	sp++;
	break;
      case call_ptr_i:
	tmp_frame = stack[sp-1];
	stack[sp-1] = stack[sp-2];
	stack[sp-2] = tag_unsigned_fixnum(pc+1);
	pc = get_unsigned_fixnum(tmp_frame);
	break;
      case jump_ptr_i:
	sp--;
	pc = get_unsigned_fixnum(stack[sp]);
	break;
      case push_ptr_i:
	check_stack(sp);
	stack[sp] = tag_unsigned_fixnum(get_loc(code[pc].args.loc));
	sp++;
	pc++;
	break;
      case return_i:
	pc = get_unsigned_fixnum(stack[sp-2]);
	stack[sp-2] = stack[sp-1];
	sp--;
	break;
      case push_exc_i:
	check_stack(sp);
	handler = sp;
	stack[sp] = tag_unsigned_fixnum(handler);
	sp++;
	pc++;
	break;
      case pop_exc_i:
	tmp_frame = stack[sp-1];
	tmp_sp1 = get_unsigned_fixnum(stack[handler]);
	stack[handler] = tmp_frame;
	sp = handler + 1;
	handler = tmp_sp1;
	pc++;
	break;
      case ref_i:
	check_heap(next_heap + 1);
	heap[next_heap] = build_header(ref_tag, 1);
	heap[next_heap + 1] = stack[sp-1];
	stack[sp-1] = tag_pointer(next_heap);
	next_heap += 2;
	pc++;
	break;
      case deref_i:
	stack[sp-1] = heap[get_pointer(stack[sp-1]) + 1];
	pc++;
	break;
      case update_i:
	heap[get_pointer(stack[sp-2]) + 1] = stack[sp-1];
	sp -= 2;
	pc++;
	break;
      case tick_i:
	pc++;
	break;
      case print_i:
	print_value(heap, stack[sp-1]);
	sp--;
	pc++;
	break;
      case print_c_i:
	putchar(code[pc].args.character);
	pc++;
	break;
      case stop_i:
	return;
      default:
	assert(false);
	break;
    }
  }
}

int main(int argc, char** argv) {
  inst_list *parse_result;
  inst *prog_array;
  unsigned long num_inst;
  FILE *in;

  if (argc == 2 && (strcmp(argv[1],"-b"))) {
    yyin = fopen(argv[1], "r");
    if (yyin == NULL) {
      printf("Could not open input file %s\n", argv[1]);
      exit(1);
    };
    yyparse(&parse_result);
    fclose(yyin);
  }
  else if (argc == 3 && !(strcmp(argv[1],"-b"))) {
    in = fopen(argv[2], "rb");
    if (in == NULL) {
      printf("Could not open input file %s\n", argv[2]);
      exit(1);
    };
    parse_result = decode(in);
    fclose(in);
   }
  else {
    printf("usage: cakeml-byte filename or cakeml-byte -b filename\n");
    exit(1);
  }
		 
  num_inst = inst_list_length(parse_result);
  prog_array = inst_list_to_array(parse_result, num_inst);
  check_locations(prog_array, num_inst);
  run(prog_array);

  return 0;
}
