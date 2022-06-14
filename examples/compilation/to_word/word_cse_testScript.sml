(*
  Testing of the word common sub-expression elimination.
*)

open preamble to_wordCompileTheory word_cseTheory word_allocTheory;

val _ = new_theory "word_cse_test";

val tm = foldr_example_ssa |> concl |> dest_eq |> snd

Definition word_cse_compact_def:
  word_cse_compact p =
  let (_,_,_,_,_,_,p') = word_cse 0 [] LN (empty listCmp) LN (empty listCmp) p in
    p'
End

val tm' = “let p = word_cse_compact ^tm in
           remove_dead p LN”

val res = EVAL tm';

val res2 = EVAL “word_cse_compact ^tm”;

val _ = export_theory();
