(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory crepLangTheory

val _ = new_theory "pan_to_crep"

val _ = set_grammar_ancestry ["panLang","crepLang","backend_common"];

Definition compile_exp_def:
  compile_exp (e:'a panLang$exp) = (ARB:'a crepLang$exp)
End


Definition compile_def:
  compile (p:'a panLang$prog list) = (ARB:'a crepLang$prog list)
End

val _ = export_theory();
