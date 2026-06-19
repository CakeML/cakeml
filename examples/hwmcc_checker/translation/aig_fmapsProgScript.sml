(*
  Setting up translator for the fmap instances that are used in aig_to_cnf.
*)
Theory aig_fmapsProg
Ancestors
  aig_cert_encodeProg aig_to_cnf
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_cert_encodeProg";

val r = translate fmap_update_def;
