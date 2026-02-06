(*
  Translation of the CakeML AST and related types for use with cv_compute.
*)
Theory source_cv[no_sig_docs]
Ancestors
  location namespace ast ast_temp
  cv_std basis_cv
Libs
  preamble cv_typeLib

val res = from_to_thm_for “:location$locn”;
val res = from_to_thm_for “:location$locs”;

val res = from_to_thm_for “:('n, 'm) namespace$id”;
val res = from_to_thm_for “:('n, 'v, 'm) namespace$namespace”;

val res = from_to_thm_for “:ast$dec”;
