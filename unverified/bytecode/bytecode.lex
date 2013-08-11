%{
#include <stdlib.h>
#include "bytecode.tab.h"
%}

%option bison-bridge bison-locations

%option noyywrap

%{
  /* handle locations */
  int yycolumn = 1;

  #define YY_USER_ACTION yylloc->first_line = yylloc->last_line = yylineno; \
    yylloc->first_column = yycolumn; yylloc->last_column = yycolumn+yyleng-1; \
    yycolumn += yyleng;
%}

%%

\n { yycolumn = 1; yylineno++;}
[ \t]+ { }
"pop" return POP_T;
"pops" return POPS_T;
"shift" return SHIFT_T;
"pushInt" return PUSH_INT_T;
"cons" return CONS_T;
"load" return LOAD_T;
"store" return STORE_T;
"loadRev" return LOAD_REV_T;
"el" return EL_T;
"tagEq" return TAG_EQ_T;
"isBlock" return IS_BLOCK_T;
"=" return EQUAL_T;
"+" return ADD_T;
"-" return SUB_T;
"*" return MULT_T;
"/" return DIV_T;
"%" return MOD_T;
"<" return LESS_T;

"label" return LABEL_T;
"jump" return JUMP_T;
"jumpIf" return JUMP_IF_T;
"call" return CALL_T;
"jumpPtr" return JUMP_PTR_T;
"callPtr" return CALL_PTR_T;
"pushPtr" return PUSH_PTR_T;
"return" return RETURN_T;
"pushExc" return PUSH_EXC_T;
"popExc" return POP_EXC_T;
"ref" return REF_T;
"deref" return DEREF_T;
"update" return UPDATE_T;
"stop" return STOP_T;
"tick" return TICK_T;
"print" return PRINT_T;
"printC" return PRINT_C_T;

"lab" return LAB_T;
"addr" return ADDR_T;

"'"."'" { yylval->character = yytext[1]; return CHAR_T; }

[0-9]+ { 
  yylval->num = strtoul(yytext, NULL, 10); 
  if (errno == ERANGE) {
    printf("Lexer: number %s too big at line: %d column: %d\n", yytext, yylloc->first_line, yylloc->first_column); 
    exit(1); 
  }
  else 
    return NUM_T;
  }
-[0-9]+ { 
  yylval->integer = strtol(yytext, NULL, 10); 
  if (errno == ERANGE) {
    printf("Lexer: number %s too small at line: %d column: %d\n", yytext, yylloc->first_line, yylloc->first_column); 
    exit(1); 
  }
  else 
    return INT_T;
}

<<EOF>> { return 0; }

. { printf("Lexer: error at line: %d column: %d\n", yylloc->first_line, yylloc->first_column); exit(1); }

%%
