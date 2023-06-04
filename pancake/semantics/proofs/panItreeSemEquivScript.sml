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
           panItreeSemTheory
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
(*             itree_diverges (itree_oracle_walk ext_call_oracle_h (itree_semantics s entry)) *)
(* Proof *)
(* QED *)

Type itree_play_set[local] = “:(itree_el) path -> bool”;

(* Need an ITree fold? or some function to produce the ITree rooted after traversing a particular
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

(* Defines an equivalence between FFI behaviours and maximal ITree paths. *)
(* Definition same_behaviour_def: *)
(* End *)

(* Design like fold:
 Fold an itree into an FFI behaviour, where the oracle choice determines which behaviour is selected for folding.
 (possibly performed as the comp of two functions: behaviour = fold o select)
 Then the equivalence becomes trivial equivalence in the same datatype.
 Read up on coinductive selection and fold algorithms.
 *)

(* Maps an ITree into the llist representing the path taken by a given oracle. *)

(* Need an itree_unfold (or fold) like mechanism to convert an itree
 into a llist, accounting for Tau values.

 How to relate llist type to nodes in an itree, where each
     Vis node becomes an element of the ITree (by choosing a path using the oracle) and using
     the response to create an IO event. *)
(* Need a co-recursive function for this... *)

(* Seems _interp_ provides a good example of "folding over an ITree"
 in order to produce some other (possibly Monadic) datatype. *)
(* Requires llist to support an iter operation and to be monadic with
 bind and ret operators. *)
(* Use LUNFOLD to create the llist *)
(* The "oracle" here is of type ffi_state *)

Definition query_oracle_def[nocompute]:
  query_oracle fs (FFI_call s conf bytes) = call_FFI fs s conf bytes
End

Definition make_io_event_def[nocompute]:
  make_io_event (FFI_call s conf bytes) rbytes =
                IO_event s conf (ZIP (bytes,rbytes))
End

(* Maps a path in an itree to an option llist, where Tau:s are represented by NONE
 and IO events by SOME e. *)
Definition itree_oracle_beh_def:
  itree_oracle_beh or t = LUNFOLD
                          (λ(or,t). itree_CASE t
                                               (K NONE)
                                               (λu. SOME ((or,u),NONE))
                                               (λe k. case query_oracle or e of
                                                        FFI_return or' bytes =>
                                                          SOME ((or',k (FFI_return or' bytes)),SOME (make_io_event e bytes))
                                                      | FFI_final (Final_event s conf bytes outcome) =>
                                                          SOME ((or,k (FFI_final (Final_event s conf bytes outcome))),SOME (make_io_event e bytes))))
                          (or,t)
End

(* Maps a path in an itree to the result of computation, when assuming
 the computation terminates. *)
Definition itree_oracle_outcome_def:
  itree_oracle_outcome or t = THE $ LHD o LFILTER (λx. x ≠ NONE) $ LUNFOLD
                              (λs. case s of
                                     SOME (or,t) =>
                                       itree_CASE t
                                                  (λr. SOME (NONE,SOME r))
                                                  (λu. SOME (SOME (or,u),NONE))
                                                  (λe k. case query_oracle or e of
                                                           FFI_return or' bytes =>
                                                             SOME (SOME (or',k (FFI_return or' bytes)),NONE)
                                                         | FFI_final (Final_event s conf bytes outcome) =>
                                                             SOME (SOME (or,k (FFI_final (Final_event s conf bytes outcome))),NONE))
                                   | NONE => NONE)
                              (SOME (or,t))
End

(* TBC *)
Definition same_outcome_def:
End

(* same_behaviour: an eqv relation between itree behaviours (repr as llists of IO events)
 and FFI behaviours, a datatype of three elements, the non-divergent of which contain llists of IO events *)
Definition same_behaviour_def:
  (* Divergence: IO event lists are equiv by weak bisimulation as the itree behaviour contains
     NONE for each Tau. *)
  (same_behaviour or t (Diverge ioll) ⇔
     (itree_oracle_beh or t) EQUIV ioll) ∧
  (* Termination: Finite IO event list is equiv to itree list by weak bisimulation, up to len of vanilla list.
     NB we lack an ability to compare computed outcomes at this level.
     Thus requiring a separate soundness proof at the evaluate level. *)
  (same_behaviour or t (Terminate outcome iol) ⇔
     (itree_oracle_beh or t) EQUIV (fromList iol)) ∧
  (* Failure: Covered by evaluate corres. *)
  (same_behaviour or t Fail ⇔ T)
End

(* Main correspondence *)
(* Proves soundness: there is always an equivalent behaviour in the itree semantics that can be selected
 using the oracle that produced the behaviour in the big-step semantics. *)

(* NB the choice of state (s) is irrelevant in the itree semantics and is provided only
 for allowing generisation over every possible Pancake program (stored in state and accessed by an entrypoint). *)
Theorem itree_semantics_corres:
  ∀s entry or.
  same_behaviour or
  (itree_semantics s entry)
  (semantics (s with <| ffi with <| oracle := or |>|>) entry)
Proof
  cheat
QED

(* Evaluate correspondence *)
(* Proves partial soundness: if a computation terminates,
the two semantics produce identical results. *)
Theorem itree_semantics_evaluate_corres:
  ∀s p or.
  ∃k. SND (evaluate p,s with <| clock := k; ffi with <|oracle := or |>|>) ≠ SOME TimeOut ⇒
      same_outcome or
                   (itree_evaluate p s)
                   (evaluate p,s with <| clock := k; ffi with <| oracle := or |>|>)
Proof
  cheat
QED

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


(* Final goal:

   1. For every path that can be generated frong

   that produces an equivalent result in the functional semantics.
   2. For every oracle, there is a path producing a corresponding result in the ITree semantics.
 *)

val _ = export_theory();
