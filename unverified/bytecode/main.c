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
  // The following are 3 greater than the compiler expects in emitted cons
  // instructions.
  forward_pointer_tag = 2,
  false_tag = 3, 
  true_tag = 4, 
  unit_tag = 5, 
  closure_tag = 6,
  string_tag = 7
} block_tag;

#define SKIP_TAGS 3

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
      case string_tag:
	printf("\"\"");
	break;
      default:
	printf("<constructor>");
	break;
    }
  else {
    value p = get_pointer(v);
    value v2 = heap[p];
    switch (get_header_tag(v2)) {
      case ref_tag:
        printf("<ref>");
	break;
      case closure_tag:
        printf("<fn>");
	break;
      case string_tag:
	{
	  int i;
	  int l = get_header_size(v2);
	  char* s = malloc(sizeof(char) * l + 1);
	  for (i = 0; i <= l; i++) {
	    s[i] = get_fixnum(heap[p+i]);
	  };
	  s[i] = 0;
	  printf("\"%s\"", s);
	  free(s);
	  break;
	}
      default:
	printf("<constructor>");
	break;
    }
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
    else if (h1 != h2) // If the tags and lengths aren't the same
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

#define STACK_SIZE 1000000
#define GLOBALS_SIZE 1000000
#define HEAP_SIZE 1000000
static value stack[STACK_SIZE];

static value globals [GLOBALS_SIZE];

static inline void check_stack(unsigned int sp) { 
  if (sp >= STACK_SIZE) {
    printf("stack overflow\n"); 
    exit(1); 
  }
}

static inline void check_globals(unsigned int gp) { 
  if (gp > GLOBALS_SIZE) {
    printf("globals overflow\n"); 
    exit(1); 
  }
}

// Move the object at ptr in the from heap to the to heap, starting at
// to_next_free.  Updates to_next_free, and returns the location that the value
// has been moved to.  ptr must be a pointer value.
static value gc_move(value *from, value *to, value ptr, unsigned long *to_next_free) {
  value header, p;
  unsigned long i, next;

  next = *to_next_free;
  p = get_pointer(ptr);
  header = from[p];

  if (get_header_tag(header) == forward_pointer_tag)
    return from[p+1];
  else {
    to[next] = header;
    for (i = 1; i <= get_header_size(header); i++)
      to[next + i] = from[p + i];
    *to_next_free = next + i;

    // install forward pointer
    from[p] = build_header(forward_pointer_tag, 1); 
    from[p+1] = next;
    return next;
  }
}

static value gc(unsigned long root_len, value* roots, value *from, value *to) {
  value i, to_next_free, to_next_copy;

  to_next_free = 0;
  to_next_copy = 0;

  // Copy roots into the to heap
  for (i = 0; i < root_len; i++)
    if (is_pointer(roots[i]))
      roots[i] = tag_pointer(gc_move(from, to, roots[i], &to_next_free));

  while (to_next_copy < to_next_free) {
    /* invariant: to_next_copy should be pointing at a header of an object whose
     * contents have not been copied. */
    unsigned long i;
    unsigned long length = get_header_size(to[to_next_copy]);
    for (i = 1; i <= length; ++i)
      if (is_pointer(to[to_next_copy + i])) 
	to[to_next_copy + i] = tag_pointer(gc_move(from, to, to[to_next_copy + i], &to_next_free));

    to_next_copy += length + 1;
  }

 // printf("used words: %lu\n", to_next_free);

  return to_next_free;
}

static inline value alloc(value size, value *next, value heap_size, value **heap, value sp) {
  if (*next + size > heap_size) {
    value *to = malloc(heap_size * sizeof(value));
    value i = gc(sp, stack, *heap, to);
    if (i + size > heap_size) {
      printf("Out of memory\n");
      exit(1);
    }
    else {
      *next = i + size;
      free(*heap);
      *heap = to;
      return i;
    }
  }
  else {
    value i = *next;
    *next = *next + size;
    return i;
  }
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



void run(inst code[]) {

  // The stack pointer sp will point to the lowest unused stack slot
  unsigned long sp = 0;
  unsigned long pc = 0;
  unsigned long handler = 0;
  unsigned long next_heap = 0;
  unsigned long next_global = 0;

  unsigned long tmp_sp1;
  value tmp_frame, ptr;
  int tmp;

  value *heap = malloc(HEAP_SIZE * sizeof(value));

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
      case push_int_i:
	check_stack(sp);
	stack[sp] = tag_fixnum(code[pc].args.num);
	sp++;
	pc++;
	break;
      case cons_i:
	if (code[pc].args.two_num.num2 == 0) {
	  check_stack(sp);
	  stack[sp] = tag_empty_block(code[pc].args.two_num.num1 + SKIP_TAGS);
	  sp++;
	}
	else {
	  block_tag tag;
	  value i, length;
	  tag = code[pc].args.two_num.num1 + SKIP_TAGS;
	  length = code[pc].args.two_num.num2;
	  ptr = alloc(length + 1, &next_heap, HEAP_SIZE, &heap, sp);
	  heap[ptr] = build_header(tag,length);
	  for (i = 0; i < length; i++)
	    heap[ptr+1+i] = stack[sp-length+i];
	  sp -= length;
	  stack[sp] = tag_pointer(ptr);
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
      case el_i:
	stack[sp-1] = heap[get_pointer(stack[sp-1]) + code[pc].args.num + 1];
	pc++;
	break;
      case tag_eq_i:
	if (is_empty_block(stack[sp-1]))
  	  stack[sp-1] = bool_to_val(code[pc].args.num + SKIP_TAGS == get_empty_block(stack[sp-1]));
        else
	  stack[sp-1] = bool_to_val(get_header_tag(heap[get_pointer(stack[sp-1])]) == code[pc].args.num + SKIP_TAGS);
	pc++;
	break;
      case is_block_i:
	if (is_empty_block(stack[sp-1]))
	  stack[sp-1] = bool_to_val(true);
	else if (is_pointer(stack[sp-1]))
	  stack[sp-1] = bool_to_val(get_header_tag(heap[get_pointer(stack[sp-1])]) >= SKIP_TAGS);
	else
	  stack[sp-1] = bool_to_val(false);
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
	ptr = alloc(2, &next_heap, HEAP_SIZE, &heap, sp);
	heap[ptr] = build_header(ref_tag, 1);
	heap[ptr + 1] = stack[sp-1];
	stack[sp-1] = tag_pointer(ptr);
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
      case galloc_i:
	next_global += code[pc].args.num;
	check_globals(next_global);
	pc++;
	break;
      case gread_i:
	check_stack(sp);
	stack[sp] = globals[code[pc].args.num];
	sp++;
	pc++;
	break;
      case gupdate_i:
	globals[code[pc].args.num] = stack[sp-1];
	sp--;
	pc++;
	break;
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
