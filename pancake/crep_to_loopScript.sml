(*
  Compilation from crepLang to panLang.
*)
open preamble crepLangTheory loopLangTheory

val _ = new_theory "crep_to_loop"

val _ = set_grammar_ancestry ["crepLang","loopLang", "backend_common"];


val _ = export_theory();
