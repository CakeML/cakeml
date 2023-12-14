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
  query_oracle ffis (FFI_call s conf bytes) =
  case call_FFI ffis s conf bytes of
    FFI_return ffis' bytes => (FFI_return ffis' bytes,ffis')
  | FFI_final e => (FFI_final e,ffis)
End

Definition make_io_event_def[nocompute]:
  make_io_event (FFI_call s conf bytes) rbytes =
                IO_event s conf (ZIP (bytes,rbytes))
End

(* TODO: Redefine itree_path so it has the property:
 path (bind t k) = path t::(path (k (leaf t))) *)
(* TODO: cheat the above property and see if it solves
 the seq case. *)

(* path def using the HOL path type:
 'a = choice type, INL is the state given to f to make branching choices (i.e. ffi state),
 'b = the e type in the itree.
*)
Definition itree_path_def:
  itree_path f s t =
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

(* Takes a function f : e -> a # f and an itree t, and returns either NONE for
infinite depth paths or SOME r where r is the result in the leaf of the tree
found by allowing f to decide branching *)

Definition itree_leaf_def:
  itree_leaf f s t = LHD $ LFLATTEN $ itree_path f s t
End

(* XXX: the third itree_path cannot use s as it must use the state for f which was produced
 with an answer that led to the branch where the leaf appears. *)
(* The definition of itree_path needs to be updated to reflect this. *)
Theorem bind_path_thm:
  itree_path f s (itree_bind t k) =
  itree_path f s t::(itree_path f s (k (THE $ itree_leaf f s t)))
Proof
  cheat
QED

Definition htree_path_def:
  htree_path f s (t:('a,'b) htree) =
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

Definition htree_leaf_def:
  htree_leaf f s (t:('a,'b) htree) = LHD $ LFLATTEN $ htree_path f s t
End


val k = “k:α -> (δ,γ,α) itree”;

Theorem path_simps[simp]:
  (itree_path f s (Ret r) = [|[|r|]|]) ∧
  (itree_path f s (Tau t) = LNIL:::(itree_path f s t)) ∧
  (itree_path f s (Vis e k) = let (a,s') = (f s e) in
                                    LNIL:::(itree_path f s' (k a)))
Proof
  rpt strip_tac >>
  rw [itree_path_def]
  >- (rw [Ntimes LUNFOLD 2])
  >- (rw [Once LUNFOLD])
  >- (rw [Once LUNFOLD] >>
         Cases_on ‘f s e’ >> rw[])
QED

Theorem itree_bind_ret_inv:
  itree_bind t k = Ret x ⇒ ∃r. (k r) = Ret x
Proof
  disch_tac >>
  Cases_on ‘t’ >>
  fs [itreeTauTheory.itree_bind_thm] >>
  metis_tac []
QED

Theorem itree_bind_ret_tree:
  itree_bind t k = Ret x ⇒
  ∃y. t = Ret y
Proof
  disch_tac >>
  Cases_on ‘t’
  >- (metis_tac [itreeTauTheory.itree_bind_thm]) >>
  fs [itreeTauTheory.itree_bind_def]
QED

Theorem itree_bind_ret_inv_gen:
  itree_bind t k = Ret x ⇒
  ∃y. t = Ret y ∧ (k y) = Ret x
Proof
  disch_tac >>
  Cases_on ‘t’
  >- (qexists_tac ‘x'’ >> rw [] >>
      fs [itreeTauTheory.itree_bind_thm]) >>
      fs [itreeTauTheory.itree_bind_def]
QED

(* Theorem itree_bind_tau_inv: *)
(*   itree_bind t k = Tau u ⇒ *)
(* Proof *)
(* QED *)

Theorem leaf_bind_thm:
  (* itree_leaf f s t ≠ NONE ⇒ *)
  itree_leaf f s (itree_bind t k) = itree_leaf f s (k $ THE $ itree_leaf f s t)
Proof
  cheat
  (* disch_tac >> *)
  (* AP_TERM_TAC >> *)
  (* rw [Once itreeTauTheory.itree_bisimulation] >> *)
  (* qexists_tac *)
  (* ‘λx y. *)
  (*       (?t k. x = itree_bind t k ∧ *)
  (*              y = k $ THE $ itree_leaf f s t) ∨ *)
  (*       x = y’ >> *)
  (* rw [] *)
  (* >- metis_tac[] *)
  (* >- (pop_assum (assume_tac o GSYM) >> *)
  (*     drule itree_bind_ret_inv_gen >> *)
  (*     disch_tac >> gs [] >> *)
  (*     ‘THE $ itree_leaf f s (Ret y) = y’ by (rw [itree_leaf_def]) >> gs []) *)
  (* >- (pop_assum (assume_tac o GSYM) >> *)
  (*     qexists_tac ‘u’ >> gs [] >>) *)
QED

Theorem leaf_bind_trans:
  (k (THE (itree_leaf f s t))) = t' ⇒
  itree_leaf f s (itree_bind t k) = itree_leaf f s t'
Proof
  cheat
QED

(* Triviality leaf_branch_thm: *)
(*   itree_leaf f s t = SOME r ⇒ *)
(*   LHD $ LFLATTEN $ itree_branch f s t = SOME r *)
(* Proof *)
(*   rw [itree_leaf_def] *)
(* QED *)

(* Triviality branch_leaves_eq: *)
(*   itree_branch f s t = itree_branch f s t' ⇒ *)
(*   itree_leaf f s t = itree_leaf f s t' *)
(* Proof *)
(*   rw [itree_leaf_def] *)
(* QED *)

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

CoInductive itree_oracle_term_path:
  (∀x. itree_oracle_term_path or (Ret x)) ∧
  (∀u. itree_oracle_term_path or u ⇒ itree_oracle_term_path or (Tau u)) ∧
  (∀e g. (itree_oracle_term_path or (g (query_oracle or e)) ⇒ itree_oracle_term_path or (Vis e g)))
End

(* Maps a path in an itree to an io_event llist *)
Definition itree_oracle_beh_def:
  itree_oracle_beh ffis t =
  LFLATTEN $ LUNFOLD
           (λ(ffis,t).
                    case t of
                      Ret r => NONE
                    | Tau u => SOME ((ffis,u),LNIL)
                    | Vis e k => (case query_oracle ffis e of
                                    (FFI_return ffis' bytes,_) =>
                                      SOME ((ffis',k (FFI_return ffis' bytes)),[|make_io_event e bytes|])
                                  | (FFI_final (Final_event ename conf bytes outcome),_) =>
                                      SOME ((ffis,k (FFI_final (Final_event ename conf bytes outcome))),[|make_io_event e bytes|])))
           (ffis,t)
End

(* An eqv relation between itree behaviours (io_event llist) and FFI behaviours;
 a datatype of three elements, the non-divergent of which contain llists of IO
 events *)

(* XXX: This needs to be improved. *)
Definition same_behaviour_def:
  (same_behaviour or t (Diverge ioll) ⇔
     (itree_oracle_beh or t) = ioll) ∧
  (same_behaviour or t (Terminate outcome iol) ⇔
     (∃iotrace. LTAKE (LENGTH iol) (itree_oracle_beh or t) = SOME iotrace ∧ iotrace = iol) ∧
     (∃r. outcome = Success ⇔ (THE $ itree_leaf query_oracle or t) = SOME (Return r)) ∧
     (∃e. outcome = (FFI_outcome e) ⇔ (THE $ itree_leaf query_oracle or t) = NONE))
End

(* An eqv relation between evaluate and evaluate_itree outcomes; which we expect
 to match as follow the same pattern of rules for computing state and final
 outcomes. *)
Definition same_outcome_def:
  same_outcome ffis t (SOME r,s) ⇔
    (THE $ itree_leaf query_oracle ffis t) = (SOME r)
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
  same_behaviour ffis (itree_semantics s entry) (semantics (s with ffi := ffis) entry)
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

val s = “s:(α,β) state”;
val s' = “s':(α,β) state”;
val s'' = “s'':(α,β) state”;

(* Proof that knowledge of the leaf of (itree_evaluate c1 s) gives us knowledge of the leaf of
 h_prog (c1,s) *)
(* Theorem itree_evaluate_seq1_lem: *)
(* Proof *)
(* QED *)

(* TODO *)
(* Theorem htree_leaf_bind_thm: *)
(*   itree_leaf f s (itree_evaluate c1 s) = SOME r ⇒ *)
(*   itree_leaf f s (sem_outer  $ mrec_sem $ itree_bind (h_prog (c1,s)) k) = itree_leaf f s (sem_outer $ mrec_sem $ k $ ) *)
(* Proof *)
(* QED *)

(* XXX: Every htree produced by h_prog is only a single node. *)
(* TODO *)
(* Prove the sister theorem of leaf_bind_thm to show that:

 itree_leaf f s $ sem_outer $ mrec_sem $ itree_bind ht k =
 itree_leaf f s $ sem_outer $ mrec_sem $ k $ htree_leaf f s ht

 And then show that:

 itree_leaf f s $ itree_evaluate p1 s = SOME r ⇒
 htree_leaf f s $ h_prog (p1,s) = SOME r

 *)

(* itree_mrec sequentially composes htree's with monad_bind *)

(* htree theory *)
(* equational theory at the level of mrec_sem applied to htree's,
 which construct the itree semantics. *)

Triviality mrec_seq_simple:
  h_prog (c1,s) = Ret (SOME r,s') ⇒
  mrec_sem (h_prog_rule_seq c1 c2 s) = Tau (Ret (SOME r,s'))
Proof
  disch_tac >>
  rw [panItreeSemTheory.h_prog_rule_seq_def] >>
  rw [panItreeSemTheory.mrec_sem_def] >>
  rw [panItreeSemTheory.mrec_body_def] >>
  rw [Once itreeTauTheory.itree_iter_thm] >>
  rw [panItreeSemTheory.mrec_iter_body_def]
QED

Triviality mrec_seq_step2:
  THE $ itree_leaf f s (h_prog (c1,s)) = (SOME r,s') ⇒
  mrec_sem (h_prog_rule_seq c1 c2 s) = Tau (Ret (SOME r,s'))
Proof
  disch_tac >>
  rw [panItreeSemTheory.h_prog_rule_seq_def]
QED

(* TODO: Continue to the above work to progress leaf and path combinators
 into mrec_Sem. *)

(* What expression shows that the "value taken by a bind abstraction is XYZ" ? *)

Theorem itree_evaluate_seq_cases:
  (same_outcome ffis (itree_evaluate c1 ^s) (SOME r,^s') ∨
   ∃s'':((α,β) state). same_outcome s''.ffi (itree_evaluate c2 s'') (SOME r,s')) ⇒
  same_outcome ffis (itree_evaluate (Seq c1 c2) s) (SOME r,s')
Proof
  disch_tac >>
  pop_assum DISJ_CASES_TAC
  >- (gs [same_outcome_def] >>
      rw [panItreeSemTheory.itree_evaluate_def] >>
      rw [panItreeSemTheory.h_prog_rule_seq_def] >>

      (* One possible strategy:
      1. Establish a thm that allows us to infer knowledge of the leaves of a h_prog (a,b) htree from the leaves of a semtree constructed from that htree.
      2. Establish a thm that allows us to, using a leaf statement over a bind, reduce a reduce a monad_bind statement into a constant.
      *)
      )
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
  >- (irule itree_evaluate_seq_cases >>
      imp_res_tac evaluate_seq_cases >> fs []
      >- (disj2_tac >>
          qexists_tac ‘s'':(α,β) state’ >> gs []))
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
