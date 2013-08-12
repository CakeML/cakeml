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

void static inline print_value(value v) {
  switch (GET_TAG(v)) {
    case NUMBER:
      if (v.arg.number < 0)
	printf("~%ld",-v.arg.number);
      else
	printf("%ld",v.arg.number);
      break;
    case REF_PTR:
      printf("<ref>");
      break;
    case CODE_PTR:
    case STACK_PTR:
      printf("<error>");
      break;
    default: /* a block */
      switch (GET_TAG(v) - CONS) {
	case TRUE_TAG:
	  printf("true");
	  break;
	case FALSE_TAG:
	  printf("false");
	  break;
	case UNIT_TAG:
	  printf("()");
	  break;
	case CLOSURE_TAG:
	  printf("<fn>");
	  break;
	default:
	  printf("<constructor>");
	  break;
      }
  }
}

unsigned long static inline bool_to_tag(bool i) {
  if (i)
    return TRUE_TAG + CONS;
  else
    return FALSE_TAG + CONS;
}

int equal(value v1, value v2) {

  unsigned long tag1 = GET_TAG(v1);
  unsigned long tag2 = GET_TAG(v2);
  unsigned long i;

  if (tag1 == CODE_PTR || tag1 == STACK_PTR || tag2 == CODE_PTR || tag2 == STACK_PTR)
    return 3;
  else if ((tag1 == NUMBER && tag2 == NUMBER) || (tag1 == REF_PTR && tag2 == REF_PTR))
    if (v2.arg.number == v1.arg.number)
      return 1;
    else 
      return 0;
  else if (tag1 == NUMBER || tag2 == NUMBER || tag1 == REF_PTR || tag2 == REF_PTR)
    return 0;
  else /* two blocks */
    if (tag1 == CLOSURE_TAG + CONS || tag2 == CLOSURE_TAG + CONS)
      return 2;
    else if (tag1 != tag2)
      return 0;
    else {
      for (i = 0; i < GET_LEN(v2); i++) {
	int res = equal(v1.arg.block[i], v2.arg.block[i]);
	if (res != 1)
	  return res;
      }
      return 1;
    }
}

static inline long sml_div(long n1, long n2) {
  if (n1 % n2 != 0 && ((n1 < 0) != (n2 < 0)))
    return ((n1 / n2) - 1);
  else
    return (n1 / n2);
}

static inline long sml_mod(long n1, long n2) {
  return (n1 - sml_div(n1,n2) * n2);
}


#define STACK_SIZE 1000000
#define REF_SIZE 1000000

static value stack[STACK_SIZE];
static value refs[REF_SIZE];

static inline void check_stack(unsigned int sp) { 
  if (sp >= STACK_SIZE) {
    printf("stack overflow\n"); 
    exit(1); 
  }
}

static inline void check_refs(unsigned int next_ref) { 
  if (next_ref >= REF_SIZE) {
    printf("ref overflow\n"); 
    exit(1);
  }
}

void run(inst code[]) {

  /* The stack pointer sp will point to the lowest unused stack slot */
  unsigned long sp = 0;
  unsigned long pc = 0;
  unsigned long handler = 0;
  unsigned long next_ref = 0;

  unsigned long tmp_sp1, tmp_sp2;
  value tmp_frame;
  value *block;
  int tmp;

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
	SET_TAG(stack[sp], NUMBER, 0);
	stack[sp].arg.number = code[pc].args.num;
	sp++;
	pc++;
	break;
      case cons_i:
	if (code[pc].args.two_num.num2 == 0) {
	  check_stack(sp);
	  SET_TAG(stack[sp], CONS + code[pc].args.two_num.num1, 0);
	  sp++;
	}
	else {
	  unsigned long i;
	  block = malloc(code[pc].args.two_num.num2 * sizeof(value));
	  for (i = 0; i < code[pc].args.two_num.num2; i++)
		  block[i] = stack[sp-code[pc].args.two_num.num2+i];
	  sp -= code[pc].args.two_num.num2;
	  SET_TAG(stack[sp], CONS + code[pc].args.two_num.num1, code[pc].args.two_num.num2);
	  stack[sp].arg.block = block;
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
	stack[sp-1] = stack[sp-1].arg.block[code[pc].args.num];
	pc++;
	break;
      case tag_eq_i:
	SET_TAG(stack[sp-1], bool_to_tag(GET_TAG(stack[sp-1]) == code[pc].args.num + CONS), 0);
	pc++;
	break;
      case is_block_i:
	SET_TAG(stack[sp-1], bool_to_tag(GET_TAG(stack[sp-1]) >= CONS), 0);
	pc++;
	break;
      case equal_i:
	tmp = equal(stack[sp-1], stack[sp-2]);
	if (tmp == 0 || tmp == 1)
	  SET_TAG(stack[sp-2], bool_to_tag(tmp), 0);
	else {
	  SET_TAG(stack[sp-2], NUMBER, 0);
	  stack[sp-2].arg.number = tmp - 2;
	}
	sp--;
	pc++;
	break;
      case less_i:
	SET_TAG(stack[sp-2], bool_to_tag(stack[sp-2].arg.number < stack[sp-1].arg.number), 0);
	sp--;
	pc++;
	break;
      case add_i:
	SET_TAG(stack[sp-2], NUMBER, 0);
	stack[sp-2].arg.number = stack[sp-2].arg.number + stack[sp-1].arg.number;
	sp--;
	pc++;
	break;
      case sub_i:
	SET_TAG(stack[sp-2], NUMBER, 0);
	stack[sp-2].arg.number = stack[sp-2].arg.number - stack[sp-1].arg.number;
	sp--;
	pc++;
	break;
      case mult_i:
	SET_TAG(stack[sp-2], NUMBER, 0);
	stack[sp-2].arg.number = stack[sp-2].arg.number * stack[sp-1].arg.number;
	sp--;
	pc++;
	break;
      case div_i:
	SET_TAG(stack[sp-2], NUMBER, 0);
	stack[sp-2].arg.number = sml_div(stack[sp-2].arg.number,stack[sp-1].arg.number);
	sp--;
	pc++;
	break;
      case mod_i:
	SET_TAG(stack[sp-2], NUMBER, 0);
	stack[sp-2].arg.number = sml_mod(stack[sp-2].arg.number, stack[sp-1].arg.number);
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
	if (GET_TAG(stack[sp-1]) == TRUE_TAG + CONS)
	  pc = get_loc(code[pc].args.loc);
	else
	  pc++;
	sp--;
	break;
      case call_i:
	check_stack(sp);
	stack[sp] = stack[sp-1];
	SET_TAG(stack[sp-1], CODE_PTR, 0);
	stack[sp-1].arg.number = pc+1;
	pc = get_loc(code[pc].args.loc);
	sp++;
	break;
      case call_ptr_i:
	tmp_frame = stack[sp-1];
	stack[sp-1] = stack[sp-2];
	SET_TAG(stack[sp-2], CODE_PTR, 0);
	stack[sp-2].arg.number = pc+1;
	pc = tmp_frame.arg.number;
	break;
      case jump_ptr_i:
	sp--;
	pc = stack[sp].arg.number;
	break;
      case push_ptr_i:
	check_stack(sp);
	SET_TAG(stack[sp], CODE_PTR, 0);
	stack[sp].arg.number = get_loc(code[pc].args.loc);
	sp++;
	pc++;
	break;
      case return_i:
	pc = stack[sp-2].arg.number;
	stack[sp-2] = stack[sp-1];
	sp--;
	break;
      case push_exc_i:
	check_stack(sp);
	handler = sp;
	SET_TAG(stack[sp], STACK_PTR, 0);
	stack[sp].arg.number = handler;
	sp++;
	pc++;
	break;
      case pop_exc_i:
	tmp_frame = stack[sp-1];
	tmp_sp1 = stack[handler].arg.number;
	stack[handler] = tmp_frame;
	sp = handler + 1;
	handler = tmp_sp1;
	pc++;
	break;
      case ref_i:
	check_refs(next_ref);
	refs[next_ref] = stack[sp-1];
	SET_TAG(stack[sp-1], REF_PTR, 0);
	stack[sp-1].arg.number = next_ref;
	next_ref++;
	pc++;
	break;
      case deref_i:
	stack[sp-1] = refs[stack[sp-1].arg.number];
	pc++;
	break;
      case update_i:
	refs[stack[sp-2].arg.number] = stack[sp-1];
	sp -= 2;
	pc++;
	break;
      case tick_i:
	pc++;
	break;
      case print_i:
	print_value(stack[sp-1]);
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
