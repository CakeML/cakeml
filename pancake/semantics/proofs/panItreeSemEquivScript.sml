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
           panItreeSemTheory in end;
           (* panItreeSemPropsTheory in end; *)

val _ = new_theory "panItreeSemEquiv";

Overload "case" = “itree_CASE”;

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
  same_outcome or t (SOME r,s) ⇔
     THE (itree_oracle_outcome or t) = (SOME r)
End

(* Theorem same_outcome_bind_ret: *)
(*   ∀s s' r r' ffis t t' f. same_outcome ffis t (SOME r,s) ∧ t = itree_bind t' f ⇒ *)
(* Proof *)
(* QED *)

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

Theorem fbs_eval_clock_and_ffi_eq:
  ∀s e k ffis.
     eval s e = eval (s with <| clock := k; ffi := ffis |>) e
Proof
  recInduct panSemTheory.eval_ind >>
  rw [panSemTheory.eval_def] >>
  metis_tac [OPT_MMAP_cong]
QED

Theorem opt_mmap_eval_clock_ffi_eq:
  ∀s e k ffis.
     OPT_MMAP (eval s) e = OPT_MMAP (eval (s with <| clock := k; ffi := ffis |>)) e
Proof
  rw [] >>
  ho_match_mp_tac OPT_MMAP_cong >>
  rw [fbs_eval_clock_and_ffi_eq]
QED

(* NB the choice of state (s) is irrelevant in the itree semantics and is provided only
 for allowing generalisation over every possible Pancake program (stored in state and accessed by an entrypoint). *)

(* Theorem foo_lemma: *)
(* Proof *)
(* QED *)

(* Theorem fbs_sem_div_eq_itree_lemma: *)
(*   ∀s entry or. semantics (s with ffi := or) entry = Diverge l ⇒ *)
(*                ioe_trace_bisim or (itree_oracle_beh or (itree_semantics s entry)) l *)
(* Proof *)
(*   rpt gen_tac >> *)
(*   disch_tac >> *)
(*   (* how to prove objects are in a coinductive relation? *) *)
(* (* prove that the singleton set containing the pair of compared elements is a subset of the relation *) *)
(* (* by showing it satisfies all the rules?*) *)
(*   (* This is one approach taken in the Sangiorgi Coinduction book. *) *)
(* QED *)

Theorem itree_semantics_corres:
  same_behaviour or (itree_semantics s entry) (semantics (s with ffi := or) entry)
Proof
  cheat
QED

(* Cases_on ‘semantics (s with ffi := or) entry’ >> *)
(* FBS divergence *)
(* >- (rw [same_behaviour_def] >> *)
(*     rw [Once LLIST_BISIMULATION] >> *)
(*     qexists_tac ‘ioe_trace_bisim or’ >> *)
(*     CONJ_TAC) *)

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

Theorem same_outcome_seq1:
  same_outcome (ffis:(β ffi_state)) (itree_evaluate (c1:(α panLang$prog)) s) (SOME r,s':((α,β) state)) ⇒
  same_outcome ffis (itree_evaluate (Seq c1 c2) s) (SOME r,s')
Proof
  cheat
QED

Theorem same_outcome_seq2:
  same_outcome ffis (itree_evaluate c1 s) (NONE,s'':((α,β) state)) ∧
  same_outcome ffis (itree_evaluate c2 s'') (r,s':((α,β) state)) ⇒
  same_outcome ffis (itree_evaluate (Seq c1 c2) s) (r,s')
Proof
  cheat
QED

Triviality evaluate_seq_cases:
  evaluate (Seq c1 c2,s) = (SOME r,s') ⇒
  fix_clock s (evaluate (c1,s)) = (SOME r,s') ∨
  ∃s''. (fix_clock s (evaluate (c1,s)) = (NONE,s'') ∧ evaluate (c2,s'') = (SOME r,s'))
Proof
  disch_tac >>
  fs [panSemTheory.evaluate_def] >>
  pairarg_tac >>
  Cases_on ‘res’ >>
  fs []
QED

Triviality evaluate_fix_clock_res_eq:
  ∀p. fix_clock s (evaluate (p,s)) = (SOME r,s') ⇒
      ∃s''. evaluate (p,s) = (SOME r,s'')
Proof
  rw [] >>
  Cases_on ‘evaluate (p,s)’ >>
  Cases_on ‘q’ >>
  fs [panSemTheory.fix_clock_def]
QED

(* Evaluate correspondence *)
(* Proves partial soundness: if a computation terminates,
the two semantics produce identical results. *)
Theorem itree_semantics_evaluate_corr:
  ∀p s s' r k ffis. evaluate (p,s) = (SOME r,s') ∧ r ≠ TimeOut ∧ s.clock = k ∧ s.ffi = ffis ⇒
      same_outcome ffis (itree_evaluate p s) (SOME r,s')
Proof
  recInduct panSemTheory.evaluate_ind >>
  REVERSE (rpt strip_tac)
  (* ExtCall *)
  >- (fs [panSemTheory.evaluate_def] >>
      fs [AllCaseEqs()] >>
      rw [panItreeSemTheory.itree_evaluate_def] >>
      rw [panItreeSemTheory.itree_mrec_def] >>
      rw [panItreeSemTheory.h_prog_def] >>
      rw [panItreeSemTheory.h_prog_rule_ext_call_def] >>
      fs [GSYM fbs_eval_clock_and_ffi_eq] >>
      rw [same_outcome_def] >>
      rw [itreeTauTheory.itree_iter_def] >>
      rw [Once itreeTauTheory.itree_unfold] >>
      rw [Once itreeTauTheory.itree_unfold] >>
      rw [itree_oracle_outcome_def] >>
      rw [Once LUNFOLD]
      (* Case: everything evaluates as expected *)
      >- (rw [query_oracle_def] >>
          Cases_on ‘outcome’ >>
          rw [Once itreeTauTheory.itree_unfold] >>
          rw [Once itreeTauTheory.itree_unfold] >>
          rw [Once itreeTauTheory.itree_unfold] >>
          rw [Once itreeTauTheory.itree_unfold] >>
          rw [Once itreeTauTheory.itree_unfold] >>
          rw [Once LUNFOLD] >>
          rw [Once LUNFOLD] >>
          rw [Once LUNFOLD] >>
          rw [Once LUNFOLD] >>
          rw [Once LUNFOLD]
          ))
  (* Seq *)
  >- (imp_res_tac evaluate_seq_cases
      >- (imp_res_tac evaluate_fix_clock_res_eq >>
          fs [] >>
          imp_res_tac same_outcome_seq1))
  (* TODO: recInduct appears to be broken as it introduces the assum: evaluate (c1,s) = (SOME r,s') when
   the definition for evaluate (Seq c1 c2,s) is based exclusively on fix_clock s ()*)

  )

(* Notes:

 Case analysis for seq subgoal
      1. evaluate (c1,s) = (SOME r,s')
        a. if r = TimeOut, then use a lemma that evaluate (Seq...,s) = (SOME r,s') ∧ r ≠ TimeOut ⇒ evaluation of neither program individually can timeout.
        b. if r ≠ TimeOut, then we get that itree_evaluate c1 s has outcome (SOME r,s') by same_outcome_seq1 thm.
      2. evaluate (c1,s) = (NONE,s'')
        a. this gives us the second part of assumption 1 which says if evaluate (c2,s'') produces a SOME result, then our itree has the same result.
        b. evaluate (c2,s'') = (SOME r,s') - where s' is the same state as in evaluate (Seq c1 c2,s)
            i. if r = TimeOut, then use the lemma as above to show this is a contradiction.
            ii. if r ≠ TimeOut, then we have that itree_evaluate c2 s'' produces the same result as evaluate; namely, (SOME r,s')
                a. need to ensure this s' is the free variable, i.e. the same state as in evaluate (Seq c1 c2,s)
        c. evaluate (c2,s'') = (NONE,ARB) - we don't care about the state in this case
            i. we can show that if evaluate (Seq c1 c2,s) produces some result, then this situation cannot happen.

Proof sketch:

    1. establish a lemma that shows that:
        evaluate (Seq c1 c2,s) = (SOME r,s') ⇒
            evaluate (c1,s) = (SOME r,s') ∨ (evaluate (c1,s) = (NONE,s'') ∧ evaluate (c2,s'') = (SOME r,s'))
    2. use the above lemma to decompose our goal into two subgoals, dependent on which evaluate returns a result.
    3. for evaluate (c1,s) = (SOME r,s')
        a. have a lemma that shows that the absence of TimeOut in a Seq result propagates into the individual programs, i.e.
            evaluate (Seq c1 c2,s) = (SOME r,s') ∧ r ≠ TimeOut ⇒
            (evaluate (c1,s) = (SOME r,ARB) ⇒ r ≠ TimeOut) ∧
            (evaluate (c2,s) = (SOME r,ARB) ⇒ r ≠ TimeOut)
        b. by 3a, we can only have that that r ≠ TimeOut and so we get by assum 1 that itree_evaluate c1 s has the same result: (SOME r,s') for r ≠ TimeOut
            i. by same_outcome_seq1 we solve the goal.
    4. for evaluate (c1,s) = (NONE,s'') ∧ evaluate (c2,s'') = (SOME r,s')
       a. by the assum 0 we get the inner implication
       b. by lemma of 3a we have that r ≠ TimeOut and so we can derive that itree_evaluate c2 s'' has the same outcome as evaluate: (SOME r,s')
       c. by same_outcome_seq2 we solve the goal.

*)

(* ----------------------------------- *)


ASM_CASES_TAC “∀s'. evaluate (c1,s) = (SOME r,s')”
      (* First term resolves to value *)
      >- (pop_assum (fn th => ASSUME_TAC $ SPEC “s':(α,β) state” th) >>
          res_tac >> rw [same_outcome_seq1])
      (* First term does not resolve to value *)
      >- (ASM_CASES_TAC “evaluate (c1,s) = (NONE,s'')”
          >- (ASM_CASES_TAC “evaluate (c2,s'') = (SOME r,s')”
              (* Second term resolves to value *)
              >- (fs [same_outcome_seq2] >>
                 ))
         )
     )
  (* Call *)
  >- (fs [panSemTheory.evaluate_def] >>
      every_case_tac >>
      rw [panItreeSemTheory.itree_evaluate_def] >>
      rw [panItreeSemTheory.itree_mrec_def] >>
      rw [panItreeSemTheory.h_prog_def] >>
      rw [panItreeSemTheory.h_prog_rule_call_def] >>
      fs [GSYM fbs_eval_clock_and_ffi_eq] >>
      fs [GSYM opt_mmap_eval_clock_ffi_eq] >>
      rw [itreeTauTheory.itree_iter_def] >>
      rw [Once itreeTauTheory.itree_unfold] >>
      rw [Once itreeTauTheory.itree_unfold] >>
      rw [same_outcome_def] >>
      rw [itree_oracle_outcome_def] >>
      rw [Once LUNFOLD] >>
      rw [itreeTauTheory.itree_bind_def]
      (* Case: evaluating the callee returns (NONE,s') *)
      >- (
       )
      (* TODO: Need to establish recursion thm for same_outcome
         - To match the recInduct on evaluate_def *)
  (* Skip *)
  >- (fs [panSemTheory.evaluate_def])
  (* Dec *)
  >- (rw [same_outcome_def] >>
      rw [panItreeSemTheory.itree_evaluate_def] >>
      rw [panItreeSemTheory.itree_mrec_def] >>
      rw [panItreeSemTheory.h_prog_def] >>
      rw [panItreeSemTheory.h_prog_rule_dec_def] >>
      Cases_on ‘eval s e’
      (* eval s e = NONE *)
      >- (rw [] >>
          fs [panSemTheory.evaluate_def] >>
          ‘eval (s with <|clock := k; ffi := ffis|>) e = NONE’ by rw [GSYM fbs_eval_clock_and_ffi_eq] >>
          fs[] >>
          rw [Once itreeTauTheory.itree_unfold] >>
          rw [itree_oracle_outcome_def] >>
          rw [Once LUNFOLD])
      (* eval s e = SOME x *)
      >- (
            rw [] >>
       )
      )
QED

(* Useful garbage *)
(* fs [CaseEqs ["option"]] *)
(* >- (rw [panItreeSemTheory.itree_evaluate_def] >> *)
(*     rw [panItreeSemTheory.itree_mrec_def] >> *)
(*     rw [panItreeSemTheory.h_prog_def] >> *)
(*     rw [panItreeSemTheory.h_prog_rule_ext_call_def] >> *)
(*     ‘eval s ptr1 = eval (s with <|clock := k; ffi := ffis|>) ptr1’ by rw [fbs_eval_clock_and_ffi_eq] >> *)
(*     fs [] >> *)
(*     rw [Once itreeTauTheory.itree_unfold] >> *)
(*     rw [same_outcome_def] >> *)
(*     rw [itree_oracle_outcome_def] >> *)
(*     rw [Once LUNFOLD] *)
(*    ) *)
(* >- (full_case_tac >> *)
(*     rw [panItreeSemTheory.itree_evaluate_def] >> *)
(*     rw [panItreeSemTheory.itree_mrec_def] >> *)
(*     rw [panItreeSemTheory.h_prog_def] >> *)
(*     rw [panItreeSemTheory.h_prog_rule_ext_call_def] >> *)
(*     ‘eval s len2 = eval (s with <|clock := k; ffi := ffis|>) len2’ by rw [fbs_eval_clock_and_ffi_eq] >> *)
(*     ‘eval s ptr1 = eval (s with <|clock := k; ffi := ffis|>) ptr1’ by rw [fbs_eval_clock_and_ffi_eq] >> *)
(*     fs [] >> *)
(*     (* STILL NEED TO REDUCE CASE EXPR *) *)
(*   ) *)
(* Elim all these cases as at least one eval is NONE *)
(* rw [panItreeSemTheory.itree_evaluate_def] >> *)
(* rw [same_outcome_def] >> *)
(* rw [itree_oracle_outcome_def] >> *)
(* rw [panItreeSemTheory.itree_mrec_def] >> *)
(* rw [panItreeSemTheory.h_prog_def] >> *)
(* rw [panItreeSemTheory.h_prog_rule_ext_call_def] >> *)
(* ‘eval s len2 = eval (s with <|clock := k; ffi := ffis|>) len2’ by rw [fbs_eval_clock_and_ffi_eq] >> *)
(* ASSUM_LIST (fn thl => ‘eval s len2 = NONE’ by (rw thl)) >> *)


(* EVERY_CASE_TAC >> *)
(* rw [Once itreeTauTheory.itree_unfold] >> *)
(* rw [same_outcome_def] >> *)
(* rw [itree_oracle_outcome_def] >> *)
(* rw [Once LUNFOLD] *)
(* How to reduce a case where every outcome is the same to that outcome? *)

(* >- (EVERY_CASE_TAC >> *)
(*     rw [panItreeSemTheory.itree_evaluate_def] >> *)
(*     rw [panItreeSemTheory.itree_mrec_def] >> *)
(*     rw [panItreeSemTheory.h_prog_def] >> *)
(*     rw [panItreeSemTheory.h_prog_rule_ext_call_def] >> *)
(*     ‘eval s ptr1 = eval (s with <|clock := k; ffi := ffis|>) ptr1’ by rw [fbs_eval_clock_and_ffi_eq] >> *)
(*     POP_ASSUM_LIST (fn thl => ‘eval s ptr1 = NONE’ by (rw thl)) >> *)
(*     rw [] >> *)
(*     rw [Once itreeTauTheory.itree_unfold] >> *)
(*     rw [same_outcome_def] >> *)
(*     rw [itree_oracle_outcome_def] >> *)
(*         rw [Once LUNFOLD]) *)
(* ) *)


(* Final goal:

   1. For every path that can be generated frong

   that produces an equivalent result in the functional semantics.
   2. For every oracle, there is a path producing a corresponding result in the ITree semantics.
 *)

val _ = export_theory();
