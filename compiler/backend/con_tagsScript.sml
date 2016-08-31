open HolKernel Parse boolLib bossLib;

val _ = new_theory "con_tags";

val _ = numLib.prefer_num();

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

val bool_to_tag_def = Define`
  bool_to_tag b = if b then true_tag else false_tag`


val _ = export_theory();
