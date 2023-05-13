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

(* Theorem evaluate_diverge_eq: *)
(*   evaluate (p,s) = (SOME TimeOut,s') ⇔ *)
(*                  itree_diverges (evaluate_itree p s) *)
(* Proof *)
(* QED *)

(* Theorem semantics_diverge_eq: *)
(*   semantics s entry = Diverge io ⇔ *)
(*             itree_diverges (itree_oracle_walk ext_call_oracle_h (semantics_itree s entry)) *)
(* Proof *)
(* QED *)

Type itree_play_set[local] = “:('b + 'c,'a) path -> bool”;

(* Need an ITree fold? or some function to produce the ITree rooted after traversing a partiular
 possibly infinite path (llist)... *)
(* This is required to complete the itree_plays definition *)

CoInductive itree_plays:
  (t = Ret r ⇒ itree_plays t (stopped_at (INR r))) ∧
  (t = Vis e k ⇒ itree_plays t (stopped_at (INL e))) ∧
  (itree_plays t p ∧
   (toList (LAPPEND (labels p) [|a|]) = SOME labList ⇒
    itree_el t (MAP (λx. SOME x) lablist) = Event e) ⇒
   itree_plays t (pcons (INL e) a p))
End

CoInductive itree_max_plays:
(t = Ret r ⇒ itree_max_plays t (stopped_at (INR r))) ∧
(itree_plays t p ∧
 (toList (LAPPEND (labels p) [|a|]) = SOME lablist ⇒
  itree_el t (MAP (λx. SOME x) lablist) = Return r) ⇒
 itree_max_plays t (pcons (INR r) a p)) ∧
(itree_max_plays t p ∧
 (toList (LAPPEND (labels p) [|a|]) = SOME lablist ⇒
  itree_el t (MAP (λx. SOME x) lablist) = Event e) ⇒
 itree_max_plays t (pcons (INL e) a p))
End

(* We can consider this in terms of Game semantics:
  - The ITree semantics produces a game tree for every possible Pancake program.
  - The set of all "moves" is every possible behaviour of that Pancake program.
  - A strategy σ ⊆ M, is one such behaviour.
  - The games considered here are "potentially infinite."
  - An FFI oracle determines a particular strategy in the game tree by representing the O moves.

  ITrees are not quite a game semantics.
    - The A (answer) type could be seen as representing a subtree wherein O chooses which answer to provide.
    - The Vis event is the P move which is determined by the FFI function to be called and the arguments provided.
 *)

(* Considered in terms of ITree traces:

    A trace is a possibly infinite sequence of zero or more IO events.
    - This is effectively a deterministic strategy as each IO event captures the Player move (FFI call)
    and the Oponent move (the ffi_result).

  Given an ITree, we can produce the set of all plays (all possible interactions) by:
    - Firstly removing all the Tau nodes.
    - At each Vis node, building an IO event by:
        - Noting the event type.
        - Choosing a term of the response type.
        - Zipping the last arg from the event with the term of the response type.
        - Repeating l. 71.

    This algorithm linearises a tree structure into a possibly infinite set of possibly infinite IO event traces.
    It must be done in a procedural way in order to be decidable.
    Lazy set of lazy lists?
 *)

(* Then to solve the final goal in the ⇒ direction, we can do case analysis over this possibly infinite set:
    - Divergence, as indicated by an infinite trace.
        - Suffices to show the two semantics produce the same IO event trace (every possible finite prefix is equal)
    - Termination (failure and return), as indicated by a finite trace.
        - Need to show that the leaf in the tree reachable by this trace produces the same outcome (failure or return value) as
        produced by some oracle in the functional big step semantics.
 *)

(*
    To solve the final goal in the ≤= direction, we need to show that the oracle producing any result in
    the functional semantics, must necessarily produce an equivalent trace (w.r.t. the criteria in the ⇒ direction)
    that exists in our possibly infinite set.

     This is true because we can show that the oracle which produced some result in the big step semantics, will follow
     a path in the ITree generation that will result in the same outcome.
*)

Definition itree_behaviour_def:
  itree_behaviour t p io =
  case itree_el t p of
    Silence => Diverge (fromList io)
  | Return r => (case r of
                   SOME (FinalFFI e) => Terminate (FFI_outcome e) io
                 | SOME (Return _) => Terminate Success io
                 | _ => Fail)
  | Event e => Fail
End

(* Final goal:

   1. For every path that can be generated from an ITree produced by the ITree semantics, there is an oracle
   that produces an equivalent result in the functional semantics.
   2. For every oracle, there is a path producing a corresponding result in the ITree semantics.
 *)

Theorem itree_semantics_paths_corr:
  t = semantics_itree s entry ⇒
  ∀p. p ∈ (itree_paths t)
Proof
QED

val _ = export_theory();
