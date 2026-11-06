(*
  CV encoding of the CakeML basis program.
*)
Theory basisProg_cv[no_sig_docs]
Ancestors
  basisProg source_cv
Libs
  preamble cv_transLib

val _ = cv_trans_deep_embedding EVAL basis_def;
