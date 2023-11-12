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

Definition query_oracle_def[nocompute]:
  query_oracle ffis (FFI_call s conf bytes) = call_FFI ffis s conf bytes
End

Definition make_io_event_def[nocompute]:
  make_io_event (FFI_call s conf bytes) rbytes =
                IO_event s conf (ZIP (bytes,rbytes))
End

(* Maps an itree t into a llist repr of the complete branch
 determined by a branching choice function f. *)
Definition itree_branch_def:
  itree_branch f s t =
  LUNFOLD
  (λseed. case seed of
         NONE => NONE
       | SOME (t',s') =>
           (case t' of
              Ret r => SOME (NONE,[|r|])
            | Tau t'' => SOME (SOME (t'',s'),LNIL)
            | Vis e k =>
                let (a,s'') = (f s' e) in
                    SOME (SOME (k a,s''),LNIL)))
  (SOME (t,s))
End

val k = “k:α -> (δ,γ,α) itree”;

Theorem branch_simps[simp]:
  (itree_branch f s (Ret r) = [|[|r|]|]) ∧
  (itree_branch f s (Tau t) = LNIL:::(itree_branch f s t))
Proof
  conj_tac >>
  rw [itree_branch_def] >>
  rpt (rw [Once LUNFOLD])
QED

Theorem branch_bind_thm:
  itree_branch f s (itree_bind t k) =
  (itree_branch f s t):::(itree_branch f s (k $ THE $ LHD $ LFLATTEN $ itree_branch f s t))
Proof
  rw [Once LLIST_BISIMULATION] >>
  cheat
QED

(*
 We use itree branch to get a nice llist repr of a branch in a tree determined by f.
 If such a branch is finite then itree_leaf will return its last element.
*)

(* Returns the result in the leaf reached by walking a semtree using the
 specified oracle to make branching choices; or NONE for divergent trees. *)

(* Do we need a concrete value or can we talk about "the value if it's ever reached"? *)

(* Takes a function f : e -> a # f and an itree t, and returns either NONE for
infinite depth paths or SOME r where r is the result in the leaf of the tree
found by allowing f to decide branching *)

Definition itree_leaf_def:
  itree_leaf f s t = LHD $ LFLATTEN $ itree_branch f s t
End

Theorem leaf_bind_trans:
  (k (THE (itree_leaf f s t))) = t' ⇒
  itree_leaf f s (itree_bind t k) = itree_leaf f s t'
Proof
  cheat
QED

Triviality leaf_branch_thm:
  itree_leaf f s t = SOME r ⇒
  LHD $ LFLATTEN $ itree_branch f s t = SOME r
Proof
  rw [itree_leaf_def]
QED

Triviality branch_leaves_eq:
  itree_branch f s t = itree_branch f s t' ⇒
  itree_leaf f s t = itree_leaf f s t'
Proof
  rw [itree_leaf_def]
QED


Theorem leaf_bind_thm:
  itree_leaf f s t = SOME r ⇒
  itree_leaf f s (itree_bind t ^k) = itree_leaf f s (itree_bind (Ret r) k)
Proof
  disch_tac >>
  rw [itreeTauTheory.itree_bind_thm] >>
  irule branch_leaves_eq >>
  ‘r = THE $ LHD $ LFLATTEN $ itree_branch f s t’ by (gs [itree_leaf_def]) >>
  Cases_on ‘k r’
  >- (rw [] >> rw [branch_bind_thm])
QED

(* Definition itree_leaf_def: *)
(*   itree_leaf or (t:(α,β) semtree) = *)
(*   LHD $ LFLATTEN $ LUNFOLD *)
(*            (λs. case s of *)
(*                   SOME (or,t) => *)
(*                     itree_CASE t *)
(*                                (λr. SOME (NONE,[|r|])) *)
(*                                (λu. SOME (SOME (or,u),LNIL)) *)
(*                                (λe k. case query_oracle or e of *)
(*                                         FFI_return or' bytes => *)
(*                                           SOME (SOME (or',k (FFI_return or' bytes)),LNIL) *)
(*                                       | FFI_final (Final_event s conf bytes outcome) => *)
(*                                           SOME (SOME (or,k (FFI_final (Final_event s conf bytes outcome))),LNIL)) *)
(*                 | NONE => NONE) *)
(*            (SOME (or,t)) *)
(* End *)

(* Can we prove something like:
  - if we know the leaf of some mtree t1 and we know the leaf of some mtree t2,
  then we know the leaf of their composition (bind) ? *)

(* This would give us compositional reasoning about mtree production in the
itree semantics. *)

(* What in fact is the direct composition of trees?

 - This is not what itree_bind does as it applies a tree to a function which
produces one of a potentially infinite number of trees. *)

Theorem itree_evaluate_seq_cases:
  itree_evaluate (Seq c1 c2) s =
  sem_outer
  do
    (r,s') <- itree_mrec_sem (c1,s);
    if r = NONE then itree_mrec_sem (c2,s') else Ret (r,s')
  od
Proof
  cheat
QED

(* from h_prog_rule_seq we can show that seq composition of two trees in the semantics
 is the same as a bind with the first evaluate and an if condition that extends the tree
    with the second evaluate so long as the first evaluate has a result of NONE.

 hence:
    h_prog_rule_seq gives:
        (itree_evaluate p1 s) BIND (λ(res,s'). if res = NONE then itree_evaluate p2 s'))

 we then need to show that itree_leaf produces the intuitive results in a bound tree:

    itree_leaf (t1 BIND k) = itree_leaf


 *)


(* this requires a connection between itree_leaf and itree_bind *)
(* Theorem itree_leaf_seq1: *)
(*   itree_leaf or (itree_evaluate c1 s) = SOME (SOME r) ⇒ *)
(*   itree_leaf or (itree_evaluate (Seq c1 c2) s) = SOME (SOME r) *)
(* Proof *)
(*   disch_tac >> *)
(*     rw [itree_e] *)
(* QED *)

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
     (∃r. outcome = Success ⇔ (itree_leaf or t) = SOME (SOME (Return r))) ∧
     (∃e. outcome = (FFI_outcome e) ⇔ (itree_leaf or t) = SOME (SOME (FinalFFI e)))) ∧
  (same_behaviour or t Fail ⇔ ∃r. (itree_leaf or t) = SOME r ∧
                                  ∀e res. r ≠ SOME (FinalFFI e) ∧ r ≠ SOME (Return res))
End

(* An eqv relation between evaluate and evaluate_itree outcomes; which we expect
 to match as follow the same pattern of rules for computing state and final
 outcomes. *)
Definition same_outcome_def:
  same_outcome or t (SOME r,s) ⇔
     THE (itree_leaf or t) = (SOME r)
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

(* NB the choice of state (s) is irrelevant in the itree semantics and is
 provided only for allowing generalisation over every possible Pancake program
 (stored in state and accessed by an entrypoint). *)

Theorem itree_semantics_corres:
  same_behaviour or (itree_semantics s entry) (semantics (s with ffi := or) entry)
Proof
  cheat
QED

(* Need to be able to say:

 If an itree_evaluate has some leaf BLAH, then mrec applied to some Vis will have the __same leaf__ as
 Ret BLAH bound to the ktree from the Vis...


 If the leaf of some tree is BLAH then the result passed to the ktree in an itree_bind is BLAH'

 ----

 Need also to be able to express each mrec rule involving Vis as the direct bind
 between a tree and the corresponding ktree rather than mrec applied to a Vis node.

 *)


(* same_outcome should probably be called "itree_result" or similar *)

(* Need to reason compositionally about the leaves in an itree using an oracle *)

(* Need to relate same_outcome to h_prog rules
 possibly using some useful itree theorems; about binding, etc. *)
Theorem same_outcome_seq1:
  same_outcome (ffis:(β ffi_state)) (itree_evaluate (c1:(α panLang$prog)) s) (SOME r,s':((α,β) state)) ⇒
  same_outcome ffis (itree_evaluate (Seq c1 c2) s) (SOME r,s')
Proof
  disch_tac >>
  rw [panItreeSemTheory.itree_evaluate_def] >>
  rw [panItreeSemTheory.itree_mrec_def] >>
  rw [panItreeSemTheory.h_prog_def] >>
  rw [panItreeSemTheory.h_prog_rule_seq_def] >>
QED

Theorem same_outcome_seq2:
  evaluate (c1,s) = (NONE,s'':((α,β) state)) ∧
  same_outcome s''.ffi (itree_evaluate c2 s'') (r,s':((α,β) state)) ⇒
  same_outcome ffis (itree_evaluate (Seq c1 c2) s) (r,s')
Proof
  cheat
QED

Triviality evaluate_seq_cases:
  evaluate (Seq c1 c2,s) = (SOME r,s') ⇒
  evaluate (c1,s) = (SOME r,s') ∨
  ∃s''. evaluate (c1,s) = (NONE,s'') ∧ evaluate (c2,s'') = (SOME r,s')
Proof
  disch_tac >>
  fs [panSemTheory.evaluate_def] >>
  pairarg_tac >>
  Cases_on ‘res’ >>
  fs []
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
      rw [itree_leaf_def] >>
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
  (* TODO: Consider using drule / drule all for this... *)
  >- (imp_res_tac evaluate_seq_cases
      >- (fs [] >> imp_res_tac same_outcome_seq1 >> fs [])
      >- (fs [] >> imp_res_tac same_outcome_seq2 >> fs []))

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
      rw [itree_leaf_def] >>
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
          rw [itree_leaf_def] >>
          rw [Once LUNFOLD])
      (* eval s e = SOME x *)
      >- (
            rw [] >>
       )
      )
QED

(* Final goal:

   1. For every path that can be generated frong

   that produces an equivalent result in the functional semantics.
   2. For every oracle, there is a path producing a corresponding result in the ITree semantics.
 *)

val _ = export_theory();
