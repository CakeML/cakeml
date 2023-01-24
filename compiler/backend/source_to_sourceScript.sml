(*
  This phase collects all source-to-source transformations.
 *)

open preamble;
open source_letTheory source_lift_constsTheory;

val _ = new_theory "source_to_source";

val _ = set_grammar_ancestry ["source_let", "source_lift_consts", "misc"];

Definition compile_def:
  compile prog =
    let prog = source_let$compile_decs prog in
    let prog = source_lift_consts$compile_decs prog in
      prog
End

val _ = export_theory ();
