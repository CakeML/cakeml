(*
  Evaluation of a timeLang program
*)
open preamble
     time_to_targetTheory time_to_panTheory compilationLib (* helloProgTheory *);

val _ = new_theory "time_eval";

(* example *)

val prog = “
  ([(1n,[Tm (Output 5) [] [strlit "a"] 2n []]);
    (2n,[Tm (Input 3)  [] [strlit "b"] 1n []])],
   SOME 4n)”

(*

  this generates a wordLang program:

  val tm = mk_comb(“time_to_pan$compile_prog”,prog) |> inst [alpha |-> “:64”]
  val th = EVAL tm
  val pan_prog = th |> concl |> rand
  val th1 = EVAL “pan_to_word$compile_prog ^pan_prog”
  val word_prog = th1 |> concl |> rand
  val ty1 = type_of word_prog

*)

val _ = export_theory();
