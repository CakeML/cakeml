(*
  Testing of the word common sub-expression elimination.
*)

open preamble to_wordCompileTheory word_cseTheory word_allocTheory;

val _ = new_theory "word_cse_test";

val tm = foldr_example_ssa |> concl |> dest_eq |> snd

val tm2 = “let p = word_common_subexp_elim ^tm in
             remove_dead p LN”

Theorem test = EVAL tm2;

val _ = export_theory();
