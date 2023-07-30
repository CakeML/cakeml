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

Definition query_oracle_def[nocompute]:
  query_oracle ffis (FFI_call s conf bytes) = call_FFI ffis s conf bytes
End

Definition make_io_event_def[nocompute]:
  make_io_event (FFI_call s conf bytes) rbytes =
                IO_event s conf (ZIP (bytes,rbytes))
End

(* Performs oracle trace selection and folds trace into
 result of computation, or NONE if divergent. *)
Definition itree_oracle_outcome_def:
  itree_oracle_outcome or t =
  LHD $ LFLATTEN $ LUNFOLD
           (λs. case s of
                  SOME (or,t) =>
                    itree_CASE t
                               (λr. SOME (NONE,[|r|]))
                               (λu. SOME (SOME (or,u),LNIL))
                               (λe k. case query_oracle or e of
                                        FFI_return or' bytes =>
                                          SOME (SOME (or',k (FFI_return or' bytes)),LNIL)
                                      | FFI_final (Final_event s conf bytes outcome) =>
                                          SOME (SOME (or,k (FFI_final (Final_event s conf bytes outcome))),LNIL))
                | NONE => NONE)
           (SOME (or,t))
End

CoInductive itree_oracle_term_path:
  (∀x. itree_oracle_term_path or (Ret x)) ∧
  (∀u. itree_oracle_term_path or u ⇒ itree_oracle_term_path or (Tau u)) ∧
  (∀e g. (itree_oracle_term_path or (g (query_oracle or e)) ⇒ itree_oracle_term_path or (Vis e g)))
End

(* Maps a path in an itree to an io_event llist *)
Definition itree_oracle_beh_def:
  itree_oracle_beh or t =
  LFLATTEN $ LUNFOLD
           (λ(or,t). itree_CASE t
                                (K NONE)
                                (λu. SOME ((or,u),LNIL))
                                (λe k. case query_oracle or e of
                                         FFI_return or' bytes =>
                                           SOME ((or',k (FFI_return or' bytes)),[|make_io_event e bytes|])
                                       | FFI_final (Final_event s conf bytes outcome) =>
                                           SOME ((or,k (FFI_final (Final_event s conf bytes outcome))),[|make_io_event e bytes|])))
           (or,t)
End

(* An eqv relation between itree behaviours (io_event llist) and FFI behaviours;
 a datatype of three elements, the non-divergent of which contain llists of IO
 events *)

Definition same_behaviour_def:
  (same_behaviour or t (Diverge ioll) ⇔
     (itree_oracle_beh or t) = ioll) ∧
  (same_behaviour or t (Terminate outcome iol) ⇔
     (∃iotrace. LTAKE (LENGTH iol) (itree_oracle_beh or t) = SOME iotrace ∧ iotrace = iol) ∧
     (∃r. outcome = Success ⇔ (itree_oracle_outcome or t) = SOME (SOME (Return r))) ∧
     (∃e. outcome = (FFI_outcome e) ⇔ (itree_oracle_outcome or t) = SOME (SOME (FinalFFI e)))) ∧
  (same_behaviour or t Fail ⇔ ∃r. (itree_oracle_outcome or t) = SOME r ∧
                                  ∀e res. r ≠ SOME (FinalFFI e) ∧ r ≠ SOME (Return res))
End

(* An eqv relation between evaluate and evaluate_itree outcomes; which we expect
 to match as follow the same pattern of rules for computing state and final
 outcomes. *)
Definition same_outcome_def:
  (same_outcome or t (NONE,s) ⇔
     itree_oracle_outcome or t = SOME NONE) ∧
  (same_outcome or t (SOME r,s) ⇔
     itree_oracle_outcome or t = SOME (SOME r))
End

(* Main correspondence *)
(* Proves soundness: there is always an equivalent behaviour in the itree
 semantics that can be selected using the oracle that produced the behaviour in
 the big-step semantics. *)

(* Bisimulation relation on io_event llists *)
CoInductive ioe_trace_bisim:
  (ioe_trace_bisim ffis LNIL LNIL) ∧
  (ffis.oracle e ffis.ffi_state conf bytes = Oracle_return ffi' bytes' ∧
   LHD l1 = SOME (IO_event e conf (ZIP (bytes,bytes'))) ∧
   LHD l2 = SOME (IO_event e conf (ZIP (bytes,bytes'))) ∧
   ioe_trace_bisim (ffis with ffi_state := ffi') (THE (LTL l1)) (THE (LTL l2)) ⇒
   ioe_trace_bisim ffis l1 l2)
End

(* NB the choice of state (s) is irrelevant in the itree semantics and is provided only
 for allowing generalisation over every possible Pancake program (stored in state and accessed by an entrypoint). *)

(* Theorem foo_lemma: *)
(* Proof *)
(* QED *)

Theorem fbs_sem_div_eq_itree_lemma:
  ∀s entry or. semantics (s with ffi := or) entry = Diverge l ⇒
               ioe_trace_bisim or (itree_oracle_beh or (itree_semantics s entry)) l
Proof
  rpt gen_tac >>
  disch_tac >>
  (* how to prove objects are in a coinductive relation? *)
(* prove that the singleton set containing the pair of compared elements is a subset of the relation *)
(* by showing it satisfies all the rules?*)
  (* This is one approach taken in the Sangiorgi Coinduction book. *)
QED

Theorem foo:
  ∀ffis. IN $ {(ffis,[||],[||])} ffis [||] [||] ⇒ ioe_trace_bisim ffis [||] [||]
Proof
QED

Theorem itree_semantics_corres:
  same_behaviour or (itree_semantics s entry) (semantics (s with ffi := or) entry)
Proof
  Cases_on ‘semantics (s with ffi := or) entry’
  (* FBS divergence *)
  >- (rw [same_behaviour_def] >>
      rw [Once LLIST_BISIMULATION] >>
      qexists_tac ‘ioe_trace_bisim or’ >>
      CONJ_TAC
      >- ()
     (* Need to rethink how I use a coind relation to prove bisimulation of the two
      llists.
      LLIST_BISIMULATION notably contains all suffix lists that are also bisimilar.
      So the bisimulation we construct must have the same property.
      Which means if we want to prove that two llists under some oracle are in our bisim,
      we need to construct the relation closed backwards under the rules starting at our two llists.
      This relation will be one of the post-fixed points of ioe_trace_bisim and thus contained in ioe_trace_bisim.

      So how do we construct a relation that is closed-backwards under some rules starting at specific constants?
      Seems like we need a corecursive construction that generates this relation and that we can expand in our proof
      to show that the relation is a subset of ioe_trace_bisim.
         *)
            (* Need to construct a relation between or, itree_sem and sem, then *)
(*                 convert the goal into the implication required of HO_MATCH_MP_TAC, *)
(*                 then it will require that I prove my constructed relation has all the properties of *)
(*                 the ioe_trace_rel relation. *)
(*              *)
        )
End

(* Evaluate correspondence *)
(* Proves partial soundness: if a computation terminates,
the two semantics produce identical results. *)
Theorem itree_semantics_evaluate_corres:
  ∀s p ffis k. FST (evaluate (p,s with <| clock := k; ffi := ffis |>)) ≠ SOME TimeOut ⇒
      same_outcome ffis (itree_evaluate p s) (evaluate (p,s with <| clock := k; ffi := ffis |>))
Proof
  rw[] >>
  Cases_on ‘FST (evaluate (p,s with <|clock := k; ffi := ffis|>))’
  (* FBS evaluates to NONE *)
  >- (rw [same_outcome_def] >>
           )
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
