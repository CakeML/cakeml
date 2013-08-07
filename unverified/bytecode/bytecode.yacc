%{
#include <stdio.h>
#include <stdlib.h>
#include "bytecode_inst.h"
%}


%union {
  unsigned long num;
  long integer;
  char character;
  struct inst_list *insts;
};

%token <num> NUM_T
%token <integer> INT_T
%token <character> CHAR_T
%token POP_T POPS_T SHIFT_T PUSH_INT_T CONS_T LOAD_T STORE_T LOAD_REV_T 
%token EL_T TAG_EQ_T IS_BLOCK_T EQUAL_T ADD_T SUB_T MULT_T DIV_T MOD_T LESS_T 
%token LABEL_T JUMP_T JUMP_IF_T CALL_T JUMP_PTR_T CALL_PTR_T RETURN_T 
%token PUSH_EXC_T POP_EXC_T REF_T DEREF_T UPDATE_T STOP_T TICK_T PRINT_T 
%token PRINT_C_T LAB_T ADDR_T PUSH_PTR_T
%token HALT_T /* Not really a token, but we use these to tag our internal instruction representation too. */

%type <insts> insts inst stack_op loc
%type <integer> num_or_int

%start insts_top
%locations
%pure-parser
%parse-param { inst_list** parse_result }

%{

void yyerror(YYLTYPE *locp, inst_list** parse_result, char *s, ...) /* Called by yyparse on error */
{
  printf ("%s near line: %d column: %d\n", s, locp->first_line, locp->first_column);
  exit(3);
};

extern int yylex(YYSTYPE * yylval_param,YYLTYPE * yylloc_param );

%}

%%

num_or_int:
   NUM_T { $$ = (long)$1 }
 | INT_T { $$ = $1 }

stack_op: 
   POP_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = POP_T;
     $$ = next;
   }
 | POPS_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = POPS_T;
     next->car.args.num = $2;
     $$ = next;
   }
 | SHIFT_T NUM_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = SHIFT_T;
     next->car.args.two_num.num1 = $2;
     next->car.args.two_num.num2 = $3;
     $$ = next;
   }
 | PUSH_INT_T num_or_int {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = PUSH_INT_T;
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
     next->car.tag = CONS_T;
     next->car.args.two_num.num1 = $2;
     next->car.args.two_num.num2 = $3;
     $$ = next;
   }
 | LOAD_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = LOAD_T;
     next->car.args.num = $2;
     $$ = next;
   }
 | STORE_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = STORE_T;
     next->car.args.num = $2;
     $$ = next;
   }
 | LOAD_REV_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = LOAD_REV_T;
     next->car.args.num = $2;
     $$ = next;
   }
 | EL_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = EL_T;
     next->car.args.num = $2;
     $$ = next;
   }
 | TAG_EQ_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = TAG_EQ_T;
     next->car.args.num = $2;
     $$ = next;
   }
 | IS_BLOCK_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = IS_BLOCK_T;
     $$ = next;
   }
 | EQUAL_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = EQUAL_T;
     $$ = next;
   }
 | ADD_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = ADD_T;
     $$ = next;
   }
 | SUB_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = SUB_T;
     $$ = next;
   }
 | MULT_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = MULT_T;
     $$ = next;
   }
 | DIV_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = DIV_T;
     $$ = next;
   }
 | MOD_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = MOD_T;
     $$ = next;
   }
 | LESS_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = LESS_T;
     $$ = next;
   }
;

loc:
/*
   LAB_T NUM_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.args.loc.isLab = 1;
     next->car.args.loc.num = $2;
     $$ = next;
   }
 |
*/
 ADDR_T NUM_T {
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
     next->car.tag = LABEL_T;
     next->car.args.num = $2;
     $$ = next;
   }
 | JUMP_T loc {
     $2->car.tag = JUMP_T;
     $$ = $2;
   }
 | JUMP_IF_T loc {
     $2->car.tag = JUMP_IF_T;
     $$ = $2;
   }
 | CALL_T loc {
     $2->car.tag = CALL_T;
     $$ = $2;
   }
 | JUMP_PTR_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = JUMP_PTR_T;
     $$ = next;
   }
 | CALL_PTR_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = CALL_PTR_T;
     $$ = next;
   }
 | PUSH_PTR_T loc {
     $2->car.tag = PUSH_PTR_T;
     $$ = $2;
   }
 | RETURN_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = RETURN_T;
     $$ = next;
   }
 | PUSH_EXC_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = PUSH_EXC_T;
     $$ = next;
   }
 | POP_EXC_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = POP_EXC_T;
     $$ = next;
   }
 | REF_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = REF_T;
     $$ = next;
   }
 | DEREF_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = DEREF_T;
     $$ = next;
   }
 | UPDATE_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = UPDATE_T;
     $$ = next;
   }
 | STOP_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = STOP_T;
     $$ = next;
   }
 | TICK_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = TICK_T;
     $$ = next;
   }
 | PRINT_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = PRINT_T;
     $$ = next;
   }
 | PRINT_C_T CHAR_T {
     inst_list* next = malloc(sizeof(inst_list));
     next->car.tag = PRINT_C_T;
     next->car.args.character = $2;
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


