%{
#include <stdio.h>
#include <stdlib.h>
%}

%code requires{
#include "bytecode_inst.h"
}

%union {
  unsigned long num;
  long integer;
  char character;
  struct inst_list *insts;
};

%token <num> NUM_T
%token <integer> INT_T
%token <character> CHAR_T
%token POP_T POPS_T PUSH_INT_T CONS_T LOAD_T STORE_T
%token EL_T TAG_EQ_T IS_BLOCK_T EQUAL_T ADD_T SUB_T MULT_T DIV_T MOD_T LESS_T 
%token LABEL_T JUMP_T JUMP_IF_T CALL_T CALL_PTR_T RETURN_T 
%token PUSH_EXC_T POP_EXC_T REF_T DEREF_T UPDATE_T STOP_T TICK_T PRINT_T 
%token PRINT_C_T LAB_T ADDR_T PUSH_PTR_T GALLOC_T GUPDATE_T GREAD_T

%type <insts> insts inst stack_op loc
%type <integer> num_or_int

%start insts_top
%locations
%pure-parser
%parse-param { inst_list** parse_result }

%{

void yyerror(YYLTYPE *locp, inst_list** parse_result, char *s, ...) /* Called by yyparse on error */
{
  printf ("Parser: %s near line: %d column: %d\n", s, locp->first_line, locp->first_column);
  exit(1);
}

extern int yylex(YYSTYPE * yylval_param,YYLTYPE * yylloc_param );

%}

%%

num_or_int:
   NUM_T { 
     if ($1 > LONG_MAX) 
       yyerror(&yylloc, NULL, "number too big");
     else
       $$ = (long)$1;
   }
 | INT_T { $$ = $1; }

stack_op: 
   POP_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = pop_i;
     $$ = next;
   }
 | POPS_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = pops_i;
     next->car.args.num = $2;
     $$ = next;
   }
 | PUSH_INT_T num_or_int {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = push_int_i;
     next->car.args.integer = $2;
     $$ = next;
   }
 | CONS_T NUM_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     if ($2 > MAX_TAG) {
       yyerror(&yylloc, NULL, "tag too big");
     }
     if ($3 > MAX_BLOCK) {
       yyerror(&yylloc, NULL, "block size too big");
     }
     next->car.tag = cons_i;
     next->car.args.two_num.num1 = $2;
     next->car.args.two_num.num2 = $3;
     $$ = next;
   }
 | LOAD_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = load_i;
     next->car.args.num = $2;
     $$ = next;
   }
 | STORE_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = store_i;
     next->car.args.num = $2;
     $$ = next;
   }
 | EL_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = el_i;
     next->car.args.num = $2;
     $$ = next;
   }
 | TAG_EQ_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = tag_eq_i;
     next->car.args.num = $2;
     $$ = next;
   }
 | IS_BLOCK_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = is_block_i;
     $$ = next;
   }
 | EQUAL_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = equal_i;
     $$ = next;
   }
 | ADD_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = add_i;
     $$ = next;
   }
 | SUB_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = sub_i;
     $$ = next;
   }
 | MULT_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = mult_i;
     $$ = next;
   }
 | DIV_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = div_i;
     $$ = next;
   }
 | MOD_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = mod_i;
     $$ = next;
   }
 | LESS_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = less_i;
     $$ = next;
   }
;

loc:
   LAB_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.args.loc.isLab = 1;
     next->car.args.loc.num = $2;
     $$ = next;
   }
 | ADDR_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.args.loc.isLab = 0;
     next->car.args.loc.num = $2;
     $$ = next;
   }
;

inst:
   stack_op { 
     $$ = $1;
   }
 | LABEL_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = label_i;
     next->car.args.num = $2;
     $$ = next;
   }
 | JUMP_T loc {
     $2->car.tag = jump_i;
     $$ = $2;
   }
 | JUMP_IF_T loc {
     $2->car.tag = jump_if_i;
     $$ = $2;
   }
 | CALL_T loc {
     $2->car.tag = call_i;
     $$ = $2;
   }
 | CALL_PTR_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = call_ptr_i;
     $$ = next;
   }
 | PUSH_PTR_T loc {
     $2->car.tag = push_ptr_i;
     $$ = $2;
   }
 | RETURN_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = return_i;
     $$ = next;
   }
 | PUSH_EXC_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = push_exc_i;
     $$ = next;
   }
 | POP_EXC_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = pop_exc_i;
     $$ = next;
   }
 | REF_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = ref_i;
     $$ = next;
   }
 | DEREF_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = deref_i;
     $$ = next;
   }
 | UPDATE_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = update_i;
     $$ = next;
   }
 | STOP_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = stop_i;
     $$ = next;
   }
 | TICK_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = tick_i;
     $$ = next;
   }
 | PRINT_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = print_i;
     $$ = next;
   }
 | PRINT_C_T CHAR_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = print_c_i;
     next->car.args.character = $2;
     $$ = next;
   }
 | GUPDATE_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = gupdate_i;
     next->car.args.num = $2;
     $$ = next;
   }
 | GREAD_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = gread_i;
     next->car.args.num = $2;
     $$ = next;
   }
 | GALLOC_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = galloc_i;
     next->car.args.num = $2;
     $$ = next;
   }

;

insts:
    { $$ = NULL; }
 | insts inst { 
    $2->cdr = $1;
    $$ = $2;
   }
;

insts_top:
  insts {
    *parse_result = $1;
  }

%%


