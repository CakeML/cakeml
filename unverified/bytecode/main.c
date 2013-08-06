#include <stdio.h>
#include <stdlib.h>
#include "bytecode_inst.h"
#include "bytecode.tab.h"

extern FILE *yyin;
extern int yyparse(inst_list **parse_result);

unsigned long inst_list_length(inst_list *l) {
  unsigned long len = 0;
  while (l != NULL) {
    len++;
    l = l->cdr;
  };
  return len;
};

inst* inst_list_to_array(inst_list *l, unsigned long length) {
  int i;
  inst_list *next;
  inst *prog_array = malloc((length + 1) * sizeof(inst));

  for (i = length - 1; i >= 0; i--) {
    next = l->cdr;
    prog_array[i] = l->car;
    free(l); 
    l = next;
  };

  prog_array[length].tag = HALT_T; 

  return prog_array;
}

#define NUMBER 0
#define CODE_PTR 1
#define REF_PTR 2
#define STACK_PTR 3
#define CONS 4

#define FALSE_TAG 0
#define TRUE_TAG 1
#define UNIT_TAG 2
#define CLOSURE_TAG 3
#define BLOCK_TAG 4

struct value {
  long long tag;
  union { long number; struct { long length; struct value *values; } block; };
};

typedef struct value value;

void inline print_value(value v) {
  switch (v.tag) {
    case NUMBER:
      if (v.number < 0)
	printf("~%ld",-v.number);
      else
	printf("%ld",v.number);
      break;
    case REF_PTR:
      printf("<ref>");
      break;
    case CODE_PTR:
    case STACK_PTR:
      printf("<error>");
      break;
    default: /* a block */
      switch (v.tag - CONS) {
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

long inline bool_to_tag(int i) {
  if (i)
    return TRUE_TAG + CONS;
  else
    return FALSE_TAG + CONS;
}

int equal(value v1, value v2) {

  long tag1 = v1.tag;
  long tag2 = v2.tag;
  int i;

  if (tag1 == CODE_PTR || tag1 == STACK_PTR || tag2 == CODE_PTR || tag2 == STACK_PTR)
    return 3;
  else if ((tag1 == NUMBER && tag2 == NUMBER) || (tag1 == REF_PTR && tag2 == REF_PTR))
    if (v2.number == v1.number)
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
      for (i = 0; i < v2.block.length; i++) {
	int res = equal(v1.block.values[i], v2.block.values[i]);
	if (res != 1)
	  return res;
      }
      return 0;
    }
}

#define STACK_SIZE 1000000
#define REF_SIZE 1000000

value stack[STACK_SIZE];
value refs[REF_SIZE];

#define CHECK_STACK(sp) { if (sp >= STACK_SIZE) { printf("stack overflow\n"); exit(1); } }
#define CHECK_REFS(next_ref) { if (next_ref >= REF_SIZE) { printf("ref overflow\n"); exit(1); } }

void run(inst code[]) {

  /* The stack pointer sp will point to the lowest unused stack slot */
  long sp = 0;
  long pc = 0;
  long handler = 0;
  long next_ref = 0;

  long tmp_sp1, tmp_sp2, i;
  value tmp_frame;
  value *block;
  int tmp;

  while (1) {

    switch (code[pc].tag) {
      case POP_T:
	sp--;
	pc++;
	break;
      case POPS_T:
	tmp_sp1 = sp;
	sp -= code[pc].args.num;
	stack[sp-1] = stack[tmp_sp1-1];
	pc++;
	break;
      case SHIFT_T:
	if (code[pc].args.two_num.num2 != 0) {
	  tmp_sp1 = sp - code[pc].args.two_num.num1;
	  tmp_sp2 = tmp_sp1 - code[pc].args.two_num.num2;
	  for (; tmp_sp1 < sp; tmp_sp1++, tmp_sp2++)
	    stack[tmp_sp2] = stack[tmp_sp1];
	  sp = tmp_sp2;
	}
	pc++;
	break;
      case PUSH_INT_T:
	CHECK_STACK(sp);
	stack[sp].tag = NUMBER;
	stack[sp].number = code[pc].args.num;
	sp++;
	pc++;
	break;
      case CONS_T:
	if (code[pc].args.two_num.num2 == 0) {
	  CHECK_STACK(sp);
	  stack[sp].tag = CONS + code[pc].args.two_num.num1;
	  stack[sp].block.length = 0;
	  sp++;
	}
	else {
	  block = malloc(code[pc].args.two_num.num2 * sizeof(value));
	  for (i = 0; i < code[pc].args.two_num.num2; i++)
		  block[i] = stack[sp-1-code[pc].args.two_num.num2+i];
	  sp -= code[pc].args.two_num.num2;
	  stack[sp].tag = CONS + code[pc].args.two_num.num1;
	  stack[sp].block.values = block;
	  stack[sp].block.length = code[pc].args.two_num.num2;
	}
	pc++;
	break;
      case LOAD_T:
	CHECK_STACK(sp);
	stack[sp] = stack[sp-1-code[pc].args.num];
	sp++;
	pc++;
	break;
      case STORE_T:
	stack[sp-2-code[pc].args.num] = stack[sp-1];
	sp--;
	pc++;
	break;
      case LOAD_REV_T:
	CHECK_STACK(sp);
	stack[sp] = stack[code[pc].args.num];
	sp++;
	pc++;
	break;
      case EL_T:
	stack[sp-1] = stack[sp-1].block.values[code[pc].args.num];
	pc++;
	break;
      case TAG_EQ_T:
	stack[sp-1].tag = bool_to_tag(stack[sp-1].tag == code[pc].args.num);
	pc++;
	break;
      case IS_BLOCK_T:
	stack[sp-1].tag = bool_to_tag(stack[sp-1].tag >= CONS);
	pc++;
	break;
      case EQUAL_T:
	tmp = equal(stack[sp-1], stack[sp-2]);
	if (tmp == 0 || tmp == 1)
	  stack[sp-2].tag = bool_to_tag(tmp);
	else {
	  stack[sp-2].tag = NUMBER;
	  stack[sp-2].number = tmp - 2;
	}
	sp--;
	pc++;
	break;
      case LESS_T:
	stack[sp-2].tag = bool_to_tag(stack[sp-2].number < stack[sp-1].number);
	sp--;
	pc++;
	break;
      case ADD_T:
	stack[sp-2].tag = NUMBER;
	stack[sp-2].number = stack[sp-2].number + stack[sp-1].number;
	sp--;
	pc++;
	break;
      case SUB_T:
	stack[sp-2].tag = NUMBER;
	stack[sp-2].number = stack[sp-2].number - stack[sp-1].number;
	sp--;
	pc++;
	break;
      case MULT_T:
	stack[sp-2].tag = NUMBER;
	stack[sp-2].number = stack[sp-2].number * stack[sp-1].number;
	sp--;
	pc++;
	break;
      case DIV_T:
	stack[sp-2].tag = NUMBER;
	stack[sp-2].number = stack[sp-2].number / stack[sp-1].number;
	sp--;
	pc++;
	break;
      case MOD_T:
	stack[sp-2].tag = NUMBER;
	stack[sp-2].number = stack[sp-2].number % stack[sp-1].number;
	sp--;
	pc++;
	break;
      case JUMP_T:
	pc = code[pc].args.num;
	break;
      case JUMP_IF_T:
	if (stack[sp-1].tag == TRUE_TAG + CONS)
	  pc = code[pc].args.num;
	else
	  pc++;
	sp--;
	break;
      case CALL_T:
	CHECK_STACK(sp);
	stack[sp] = stack[sp-1];
	stack[sp-1].tag = CODE_PTR;
	stack[sp-1].number = pc+1;
	pc = code[pc].args.num;
	sp++;
	break;
      case CALL_PTR_T:
	tmp_frame = stack[sp-1];
	stack[sp-1] = stack[sp-2];
	stack[sp-2].tag = CODE_PTR;
	stack[sp-2].number = pc+1;
	pc = tmp_frame.number;
	break;
      case JUMP_PTR_T:
	sp--;
	pc = stack[sp].number;
	break;
      case PUSH_PTR_T:
	CHECK_STACK(sp);
	stack[sp].tag = CODE_PTR;
	stack[sp].tag = code[pc].args.num;
	sp++;
	pc++;
	break;
      case RETURN_T:
	pc = stack[sp-2].number;
	stack[sp-2] = stack[sp-1];
	sp--;
	break;
      case PUSH_EXC_T:
	CHECK_STACK(sp);
	handler = sp;
	stack[sp].tag = STACK_PTR;
	stack[sp].number = handler;
	sp++;
	pc++;
	break;
      case POP_EXC_T:
	tmp_frame = stack[sp-1];
	tmp_sp1 = stack[handler].number;
	stack[handler] = tmp_frame;
	sp = handler + 1;
	handler = tmp_sp1;
	pc++;
	break;
      case REF_T:
	CHECK_REFS(next_ref);
	refs[next_ref] = stack[sp-1];
	stack[sp-1].tag = REF_PTR;
	stack[sp-1].number = next_ref;
	next_ref++;
	pc++;
	break;
      case DEREF_T:
	stack[sp-1] = refs[stack[sp-1].number];
	pc++;
	break;
      case UPDATE_T:
	refs[stack[sp-2].number] = stack[sp-1];
	sp -= 2;
	pc++;
	break;
      case TICK_T:
	pc++;
	break;
      case PRINT_T:
	print_value(stack[sp-1]);
	sp--;
	pc++;
	break;
      case PRINT_C_T:
	putchar(code[pc].args.character);
	pc++;
	break;
      case HALT_T:
	return;
    }
    fflush(stdout);
    exit(1);
  }
}

int main(int argc, char** argv) {
  inst_list *parse_result;
  inst *prog_array;

  if (argc != 2) {
    printf("usage: cakeml-byte filename\n");
    exit(1);
  };
  yyin = fopen(argv[1], "r");
  if (yyin == NULL) {
    printf("Could not open input file %s\n", argv[1]);
    exit(1);
  };
  yyparse(&parse_result);
  fclose(yyin);
  prog_array = inst_list_to_array(parse_result, inst_list_length(parse_result));
  run(prog_array);
  fflush(stdout);

  return 0;
}
