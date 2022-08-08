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

val prog = “Seq (Inst (Const 1 0w)) (Inst (Const 3 5w))”

val prog = “Seq (Inst (Const 1 0w))
             (Seq (Inst (Arith (Binop Add 3 1 (Reg 1))))
              (Inst (Arith (Binop Add 4 1 (Reg 1)))))”

val prog2 = “(Seq (Move 0 [(37,2);(39,4)]) (If Equal 41 (Imm 2w) (Return 37 2) (Return 37 2))):64 wordLang$prog”;

val fact_begin = “Move 1 [(37,0); (41,2); (45,4); (49,6)] ▸
                  Inst (Const 189 0w) ▸ Inst (Const 193 0w) ▸
                  OpCurrHeap Add 69 37 ▸
                  OpCurrHeap Add 71 37 ▸
                  Inst (Arith (Shift Lsr 65 41 9)) ▸
                  Inst (Arith (Shift Lsr 67 41 9))
                 ” (*works *)

val fact_begin2 = “Move 1 [(37,0); (41,2); (45,4); (49,6)] ▸
                   Inst (Const 53 18w) ▸ Move 0 [(2,45)] ▸
                   Move 1 [(181,37); (177,49)] ▸ Inst (Const 185 0w) ▸
                   Inst (Const 189 0w) ▸ Inst (Const 193 0w) ▸ Move 1 [(197,53)] ▸
                   Inst (Const 201 0w) ▸ Move 1 [(205,41)] ▸ Move 1 [(209,45)] ▸
                   Inst (Const 213 0w) ▸ Inst (Const 217 0w)
                   ”

EVAL “^tm'”;

EVAL “word_cse_compact ^prog”;

     EVAL “w2n 5w = w2n 0w”;

EVAL “word_cse_compact ^fact_begin”;
EVAL “w2n_def 0w”
val res = EVAL tm';

val res2 = EVAL “word_cse_compact ^tm”;

val _ = export_theory();
