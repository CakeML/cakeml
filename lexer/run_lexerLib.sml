open preamble;
open computeLib optionTheory;
open lexer_specTheory regexpTheory lexer_spec_to_dfaTheory lexer_runtimeTheory;


val _ = set_skip the_compset ``eval_option_case`` (SOME 1);
val _ = set_skip the_compset ``eval_let`` (SOME 1);
val _ = set_skip the_compset ``COND`` (SOME 1);
val _ = set_skip the_compset ``$\/`` (SOME 1);
val _ = set_skip the_compset ``$/\`` (SOME 1);
val _ = add_funs [IN_LIST_TO_SET]

