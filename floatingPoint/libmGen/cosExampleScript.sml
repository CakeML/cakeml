(*
  Example libm function generated from cosine certificate of Dandelion
*)
open libmLib cosDeg3Theory;

val _ = new_theory "cosExample";

Theorem cos_cml_code_corr = implement cos_example_def "cos"

val _ = export_theory();
