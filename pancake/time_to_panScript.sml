(*
  Compilation from timeLang to panLang
*)
open preamble pan_commonTheory
     timeLangTheory panLangTheory

val _ = new_theory "time_to_pan"

val _ = set_grammar_ancestry ["pan_common", "timeLang", "panLang"];


(*
  steps to take:
  1. write a panLang program that actually represents an FSM with timing constraints
  2. also write the corresponding timeLang prrogram
*)


(*
  1. I need to have imperative programming language
  2. How to program FSM in an imperative language
  3. this is the thing

  what is the difference between an FSM and TA

*)

val _ = export_theory();
