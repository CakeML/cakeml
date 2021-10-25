(*
  This is file implements a "smart" version of ClosLang's Op
  constructor. When possible, this smart constructor breaks
  the operation into faster separate operators.
*)
open preamble closLangTheory;

val _ = new_theory "clos_op";

val _ = set_grammar_ancestry ["closLang"]

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Definition SmartOp_def:
  SmartOp tra op xs = closLang$Op tra op xs
End

val _ = export_theory();
