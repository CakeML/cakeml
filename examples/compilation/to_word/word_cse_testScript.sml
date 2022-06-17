(*
  Testing of the word common sub-expression elimination.
*)

open preamble to_wordCompileTheory word_cseTheory word_allocTheory;

val _ = new_theory "word_cse_test";

val tm = foldr_example_ssa |> concl |> dest_eq |> snd

Definition word_cse_compact_def:
  word_cse_compact p =
  let (_,p') = word_cse empty_data p in
    p'
End

val tm' = “let p = word_cse_compact ^tm in
           remove_dead p LN”

val prog = “(Seq (Inst (Arith (Binop Add 3 1 (Reg 2)))) (Inst (Arith (Binop Add 4 1 (Reg 2)))))”

val prog2 = “Seq (Move 0 [(37,2);(39,4)]) (If Equal 41 (Imm 2w) (Return 37 2) (Return 37 2))”;


EVAL “^tm”;

EVAL “word_cse_compact ^prog2”;

val res = EVAL tm';

val res2 = EVAL “word_cse_compact ^tm”;

val _ = export_theory();
