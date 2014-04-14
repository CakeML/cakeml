#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>
#include <stdbool.h>
#include "bytecode_inst.h"

/* How many bytes each field of the encoding has */
#define ENCODING_TYPE uint64_t
#define ENCODING_SIZE sizeof(ENCODING_TYPE)

unsigned long decode_num(FILE* in, unsigned int inst_num) {
  ENCODING_TYPE num;
  size_t num_read = fread(&num, ENCODING_SIZE, 1, in);
  if (num_read < 1) {
    printf("Decoder %d: missing argument\n", inst_num);
    exit(1);
  }
  if (num > ULONG_MAX) {
    printf("Decoder %d: number too big %" PRIx64 "\n", inst_num, num);
    exit(1);
  }
  return num;
}

two_num decode_2num(FILE* in, unsigned int inst_num) {
  two_num res;
  ENCODING_TYPE num[2];
  size_t num_read = fread(&num, ENCODING_SIZE, 2, in);
  if (num_read < 2) {
    printf("Decoder %d: missing argument\n", inst_num);
    exit(1);
  }
  if (num[0] > ULONG_MAX) {
    printf("Decoder %d: number too big %" PRIx64 "\n", inst_num, num[0]);
    exit(1);
  } 
  else if (num[1] > ULONG_MAX) {
    printf("Decoder %d: number too big %" PRIx64 "\n", inst_num, num[1]);
    exit(1);
  } 
  res.num1 = num[0];
  res.num2 = num[1];
  return res;
}

inst_list* decode(FILE *in) {
  ENCODING_TYPE tag;
  size_t num_read;
  inst_list *program = NULL;
  inst_list *next_inst;
  unsigned long i;
  unsigned int inst_num = 0;

  while (true) {
    num_read = fread(&tag, ENCODING_SIZE, 1, in);
    if (num_read < 1)
      return program;

    next_inst = malloc(sizeof(inst_list));
    switch (tag) {
      case 0:
        next_inst->car.tag = pop_i;
	break;
      case 1:
	next_inst->car.tag = pops_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 3:
	next_inst->car.tag = push_int_i;
	i = decode_num(in, inst_num);
	if (-i < LONG_MIN) {
	  printf("Decoder %d: number too small for pushInt -%lu\n", inst_num, i);
	  exit(1);
	}	
	next_inst->car.args.integer = -i;
	break;
      case 4:
	next_inst->car.tag = push_int_i;
	i = decode_num(in, inst_num);
	if (i > LONG_MAX) {
	  printf("Decoder %d: number too big for pushInt %lu\n", inst_num, i);
	  exit(1);
	}	
	next_inst->car.args.integer = i;
	break;
      case 5:
	/* TODO: check that the block and tag aren't too big */
	next_inst->car.tag = cons_i;
	next_inst->car.args.two_num = decode_2num(in, inst_num);
	break;
      case 6:
	next_inst->car.tag = load_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 7:
	next_inst->car.tag = store_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 9:
	next_inst->car.tag = el_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 10:
	next_inst->car.tag = tag_eq_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 11:
        next_inst->car.tag = is_block_i;
	break;
      case 12:
        next_inst->car.tag = equal_i;
	break;
      case 13:
        next_inst->car.tag = add_i;
	break;
      case 14:
        next_inst->car.tag = sub_i;
	break;
      case 15:
        next_inst->car.tag = mult_i;
	break;
      case 16:
        next_inst->car.tag = div_i;
	break;
      case 17:
        next_inst->car.tag = mod_i;
	break;
      case 18:
        next_inst->car.tag = less_i;
	break;
      case 19:
	next_inst->car.tag = label_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 20:
	next_inst->car.tag = jump_i;
	next_inst->car.args.loc.isLab = 1;
	next_inst->car.args.loc.num = decode_num(in, inst_num);
	break;
      case 21:
	next_inst->car.tag = jump_i;
	next_inst->car.args.loc.isLab = 0;
	next_inst->car.args.loc.num = decode_num(in, inst_num);
	break;
      case 22:
	next_inst->car.tag = jump_if_i;
	next_inst->car.args.loc.isLab = 1;
	next_inst->car.args.loc.num = decode_num(in, inst_num);
	break;
      case 23:
	next_inst->car.tag = jump_if_i;
	next_inst->car.args.loc.isLab = 0;
	next_inst->car.args.loc.num = decode_num(in, inst_num);
	break;
      case 24:
	next_inst->car.tag = call_i;
	next_inst->car.args.loc.isLab = 1;
	next_inst->car.args.loc.num = decode_num(in, inst_num);
	break;
      case 25:
	next_inst->car.tag = call_i;
	next_inst->car.args.loc.isLab = 0;
	next_inst->car.args.loc.num = decode_num(in, inst_num);
	break;
      case 27:
        next_inst->car.tag = call_ptr_i;
	break;
      case 28:
	next_inst->car.tag = push_ptr_i;
	next_inst->car.args.loc.isLab = 1;
	next_inst->car.args.loc.num = decode_num(in, inst_num);
	break;
      case 29:
	next_inst->car.tag = push_ptr_i;
	next_inst->car.args.loc.isLab = 0;
	next_inst->car.args.loc.num = decode_num(in, inst_num);
	break;
      case 30:
        next_inst->car.tag = return_i;
	break;
      case 31:
        next_inst->car.tag = push_exc_i;
	break;
      case 32:
        next_inst->car.tag = pop_exc_i;
	break;
      case 33:
        next_inst->car.tag = ref_i;
	break;
      case 34:
        next_inst->car.tag = deref_i;
	break;
      case 35:
        next_inst->car.tag = update_i;
	break;
      case 36:
        next_inst->car.tag = galloc_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 37:
        next_inst->car.tag = galloc_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 38:
        next_inst->car.tag = galloc_i;
	next_inst->car.args.num = decode_num(in, inst_num);
	break;
      case 39:
        next_inst->car.tag = stop_i;
	break;
      case 8:
        next_inst->car.tag = tick_i;
	break;
      case 26:
        next_inst->car.tag = print_i;
	break;
      case 2:
        next_inst->car.tag = print_c_i;
	i = decode_num(in, inst_num);
	if (i > CHAR_MAX) {
	  printf("Decoder %d: number too big for printC %lu\n",inst_num, i);
	  exit(1);
	}	
	next_inst->car.args.character = i;
	break;
      default:
	printf("Decoder %d: bad tag %" PRIx64 "\n", inst_num, tag); 
	exit(1);
	break;
    }	
    next_inst->cdr = program;
    program = next_inst;
    inst_num++;
  }
}
