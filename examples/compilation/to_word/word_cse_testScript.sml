(*
  Testing of the word common sub-expression elimination.
*)

open preamble to_wordCompileTheory word_comSubExpElimTheory word_allocTheory;

val _ = new_theory "word_cse_test";

val tm = foldr_example_ssa |> concl |> dest_eq |> snd

val tm' = “let p = word_cse ^tm in
           remove_dead p LN”

val res = EVAL tm';

val res2 = EVAL “word_cse ^tm”;

val _ = export_theory();
