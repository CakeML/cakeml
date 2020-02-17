(*
  Compilation from panLang to crepLang.
*)
open preamble crepLangTheory wheatLangTheory

val _ = new_theory "crep_to_wheat"

val _ = set_grammar_ancestry ["crepLang","wheatLang","backend_common"];

Definition compile_exp_def:
  compile_exp (e:'a crepLang$exp) = (ARB:'a wheatLang$exp)
End


Definition compile_def:
  compile (p:'a crepLang$prog list) = (ARB:'a wheatLang$prog list)
End

val _ = export_theory();
