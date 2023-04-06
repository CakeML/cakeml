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

(* Proof of correspondence between semantics *)
(* Proof outline:
 A compositional proof shows the outer most conditions, i.e. divergence, occur only for the same
   inner conditions.

 For example, semantics = Diverge only when evaluate = TimeOut only when a specific list of conditions are true,
     and these are exactly the same conditions that cause evaluate_itree to produce a divergent tree, and thus
     semantics_itree to produce a divergent tree.

 Likewise for the other cases. *)

(* State sequence theory *)

(* Relating program statements *)

(* there is a seq of states, the guard is true in every one, and that seq
 is transitive: meaning each produces the next under evaluate, the first is the first and the final
    is the final. *)

Theorem evaluate_timeout_while:
  ∀g p s s'. (evaluate (While g p,s) = (SOME TimeOut,s')) ⇒
             ∃trace m. trace = [s] ++ m ++ [s'] ∧ EVERY (λx. x = SOME (ValWord w) ∧ w ≠ 0w) (MAP (flip eval g) trace)
Proof
  cheat
(* the proof should be trivial:
   take sseq as [s,s'] as such a sequence.
   then clearly eval s g and eval s' g produce the correct results.
   then any other intermediate sequence [s,...,s'] for s.clock > 1 also holds. *)
QED

(* Theorem evaluate_timeout_cases: *)
(*   ∀p s s'. (evaluate (p,s) = (SOME TimeOut,s')) *)
(* Proof *)
(*   cheat *)
(* QED *)

Theorem evaluate_semantics_corr:
  ∀p s s'. (evaluate (p,s) = (SOME TimeOut,s')) ⇔
           itree_diverges $ evaluate_itree p s
Proof
  cheat
QED

Theorem semantics_corr:
  ∃s entry. (semantics s entry = Diverge evl) ⇔
             itree_diverges (itree_oracle_walk ext_call_oracle_h (semantics_itree s entry))
Proof
  cheat
QED

val _ = export_theory();
