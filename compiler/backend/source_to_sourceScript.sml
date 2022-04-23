(*
  This phase collects all source-to-source transformations.
 *)

open preamble;
open source_letTheory;

val _ = new_theory "source_to_source";

val _ = set_grammar_ancestry ["source_let", "misc"];

Definition compile_def:
  compile = source_let$compile_decs
End

val _ = export_theory ();

