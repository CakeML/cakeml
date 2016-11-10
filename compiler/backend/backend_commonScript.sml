open HolKernel Parse boolLib bossLib;
open preamble

val _ = new_theory "backend_common";
val _ = set_grammar_ancestry ["arithmetic"]

(* these must match what the prim_types_program generates *)

val _ = Define `bind_tag      = 0`;
val _ = Define `chr_tag       = 1`;
val _ = Define `div_tag       = 2`;
val _ = Define `subscript_tag = 3`;

val _ = Define `true_tag  = 0`;
val _ = Define `false_tag = 1`;

val _ = Define `nil_tag   = 0`;
val _ = Define `cons_tag  = 0`;

val _ = Define `none_tag  = 0`;
val _ = Define `some_tag  = 0`;

val _ = Define `tuple_tag = 0`;

val bool_to_tag_def = Define`
  bool_to_tag b = if b then true_tag else false_tag`


val stack_num_stubs_def = Define`
  stack_num_stubs = 4n`;

val word_num_stubs_def = Define`
  word_num_stubs = stack_num_stubs + 1 (* raise *)`;

val data_num_stubs_def = Define`
  data_num_stubs = word_num_stubs + 5`;

val bvl_num_stubs_def = Define`
  bvl_num_stubs = data_num_stubs + 4
`;


val _ = export_theory();
