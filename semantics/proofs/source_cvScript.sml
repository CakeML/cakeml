(*
  Translation of the CakeML AST and related types for use with cv_compute.
*)
Theory source_cv[no_sig_docs]
Ancestors
  location namespace ast ast_temp
  cv_std basis_cv
Libs
  preamble cv_typeLib

val res = define_from_to “:location$locn”;
val res = define_from_to “:location$locs”;

val res = define_from_to “:('n, 'm) namespace$id”;
val res = define_from_to “:('n, 'v, 'm) namespace$namespace”;

val res = define_from_to “:ast$lit”;
val res = define_from_to “:ast$opn”;
val res = define_from_to “:ast$opb”;
val res = define_from_to “:ast$opw”;
val res = define_from_to “:ast$shift”;
val res = define_from_to “:ast$fp_cmp”;
val res = define_from_to “:ast$fp_uop”;
val res = define_from_to “:ast$fp_bop”;
val res = define_from_to “:ast$fp_top”;
val res = define_from_to “:ast$word_size”;
val res = define_from_to “:ast$thunk_mode”;
val res = define_from_to “:ast$thunk_op”;
val res = define_from_to “:ast$test”;
val res = define_from_to “:ast$prim_type”;
val res = define_from_to “:ast_temp$arith”;
val res = define_from_to “:ast$op”;
val res = define_from_to “:ast$op_class”;
val res = define_from_to “:ast$lop”;
val res = define_from_to “:ast$ast_t”;
val res = define_from_to “:ast$pat”;
val res = define_from_to “:ast$exp”;
val res = define_from_to “:ast$dec”;
