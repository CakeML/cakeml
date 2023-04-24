(*
    Proof of correspondence between functional big-step
    and itree semantics for Pancake.
*)

open preamble panLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           ffiTheory
           itreeTauTheory
           panSemTheory
           panItreeSemPropsTheory in end;

val _ = new_theory "panItreeSemEquiv";

(* Prerequisite lemmata *)

(* find a way to relate the operation of evaluate to the operation of mrec  *)
(* then the below is easily proven. *)

Theorem evaluate_diverge_eq:
  evaluate (p,s) = (SOME TimeOut,s') ⇔
                 itree_diverges (evaluate_itree p s)
Proof
QED

Theorem semantics_diverge_eq:
  semantics s entry = Diverge io ⇔
            itree_diverges (itree_oracle_walk ext_call_oracle_h (semantics_itree s entry))
Proof
QED

(* After reading Hrutvik's proofs, seems in all likelihood cleanest approach is to draw the obvious
 correspondence between semantics by relating the steps in evaluate to the steps performed by mrec, possibly in a small-step way.
                i.e. relate evaluate's recursion to mrec's iterated evaluation.

 This way we can show that divergence in one semantics produces divergence in the other, by necessity of both
      performing infinite operations. *)

val _ = export_theory();
