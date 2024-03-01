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

val _ = new_theory "panItreeSemEquiv";


Definition query_oracle_def[nocompute]:
  query_oracle ffis (FFI_call s conf bytes) =
  case call_FFI ffis s conf bytes of
    FFI_return ffis' bytes' => (FFI_return ffis' bytes',bytes',ffis')
  | FFI_final (Final_event name conf' bytes' outcome) =>
              (FFI_final (Final_event name conf' bytes' outcome),bytes',ffis)
End

Definition make_io_event_def[nocompute]:
  make_io_event (FFI_call s conf bytes) rbytes =
                IO_event s conf (ZIP (bytes,rbytes))
End

val t = “t:('a,'b,'c) itree”;

(* Path over semtrees:
 - states consist of (ffi_state x 'a result option) pairs,
 - transition labels have type: 'b sem_vis_event option
 *)
Definition semtree_path_def:
  semtree_path f s ^t =
  unfold (λ(t,s1). case t of
                     Ret r => (s1,SOME r)
                   | Tau u => (s1,NONE)
                   | Vis e k => let (a,s1') = (f s1 e) in (s1',NONE))
         (λ(t,s1). case t of
                     Ret r => NONE
                   | Tau u => SOME ((u,s1),NONE)
                   | Vis e k => let (a,s1') = (f s1 e) in
                                    SOME ((k a,s1'),SOME e))
         (t,s)
End

val st = “st:('a,'b) stree”;

(* Produces a llist of the IO events on a path in the given tree
 determined by a stateful branching choice function. *)
Definition stree_trace_def:
  stree_trace f fs ^st =
  LFLATTEN $ LUNFOLD
  (λ(fs',t). case t of
                 Ret r => NONE
               | Tau u => SOME ((fs',u),LNIL)
               | Vis e k => let (a,rbytes,fs'') = f fs' e in
                                SOME ((fs'',k a),[|make_io_event e rbytes|]))
  (fs,st)
End

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

(*

ltree is the monad of leaves of an mtree (essentially branches that contain only
Ret and Tau nodes).

ltree_lift lifts the mtree monad into the ltree monad and satisfies the usual
monad transformer laws.

*)

val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;

val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;

Definition ltree_lift_def:
  (ltree_lift f st (mt:('a,'b) mtree)):('a,'b) ltree =
  itree_iter
  (λ(t,st). case t of
        Ret x => Ret (INR x)
       | Tau u => Ret (INL (u,st))
       | Vis (e,k) g => let (a,rbytes,st') = (f st e) in
                            Ret (INL ((g o k) a,st')))
  (mt,st)
End

Definition ltree_converges_def:
  ltree_converges lt ⇔ ∃r. lt ≈ Ret r
End

Definition ltree_diverges_def:
  ltree_diverges lt ⇔ ¬(ltree_converges lt)
End

Theorem ltree_lift_cases:
  (ltree_lift f st (Ret x) = Ret x) ∧
  (ltree_lift f st (Tau u) = Tau (ltree_lift f st u)) ∧
  (ltree_lift f st (Vis (e,k) g) = let (a,rbytes,st') = (f st e) in
                                   Tau (ltree_lift f st' ((g o k) a)))
Proof
  rpt strip_tac >>
  rw [ltree_lift_def] >>>
     LASTGOAL (Cases_on ‘f st e’ >> Cases_on ‘r’) >>>
     ALLGOALS (rw [Once itreeTauTheory.itree_iter_thm])
QED

Theorem itree_bind_left_ident_over_f:
  f $ Ret x >>= k = f (k x)
Proof
  AP_TERM_TAC >>
  rw [itreeTauTheory.itree_bind_thm]
QED

Theorem itree_eq_imp_wbisim:
  t = t' ⇒ t ≈ t'
Proof
  rw [Once itreeTauTheory.itree_wbisim_strong_coind] >>
  rw [itreeTauTheory.itree_wbisim_refl]
QED

Theorem itree_bind_left_ident_wbisim:
  Ret r >>= k ≈ k r
Proof
  rw [itree_eq_imp_wbisim]
QED

Theorem itree_bind_thm_wbisim:
  t ≈ Ret r ⇒ t >>= k ≈ k r
Proof
  disch_tac >>
  drule itreeTauTheory.itree_bind_resp_t_wbisim >>
  rw [itree_bind_left_ident_wbisim]
QED

(* TODO: Finish this *)
Theorem msem_ret_wbisim_eq:
  mrec_sem ht ≈ Ret x ⇒
  ht ≈ Ret x
Proof
  fs [panItreeSemTheory.mrec_sem_def] >>
  namedCases_on ‘ht’ ["x","x","x"] >>
  cheat
QED

Theorem itree_wbisim_monad_equiv:
  Ret x ≈ Ret x' ⇔
  x = x'
Proof
  cheat
QED

Theorem itree_wbisim_ret_u:
  Ret x ≈ u ⇒
  u = Ret x
Proof
  cheat
QED

Theorem itree_wbisim_vis_ret:
  Ret x ≈ Vis e k ⇒ F
Proof
  rw [Once itreeTauTheory.itree_wbisim_cases]
QED

Theorem msem_strip_tau:
  (strip_tau ht (Ret x) ⇒
   mrec_sem ht = mrec_sem (Ret x)) ∧
  (strip_tau ht (Vis (INL seed) k) ⇒
   mrec_sem ht = Tau (case ht of
                   Tau u => mrec_sem u
                      | _ => mrec_sem ht)) ∧
  (strip_tau ht (Vis (INR e) k) ⇒
   mrec_sem ht = (case ht of
                    Tau u => mrec_sem u
                    | _ => mrec_sem ht)) ∧
  (strip_tau ht (Tau u) ⇒
   mrec_sem ht = mrec_sem u)
Proof
  cheat
QED

Theorem strip_tau_vis_wbisim:
  ∀e k k'. strip_tau t (Vis e k) ∧ strip_tau t' (Vis e k') ∧ (∀r. k r ≈ k' r) ⇒
  t ≈ t'
Proof
  cheat
QED

(* TODO: Finish this *)
Theorem msem_resp_wbisim:
  ht ≈ ht' ⇒
  mrec_sem ht ≈ mrec_sem ht'
Proof
  cheat
  (* disch_tac >> *)
  (* irule itreeTauTheory.itree_wbisim_strong_coind >> *)
  (* qexists_tac ‘λx y. (∃ht1 ht2. ht1 ≈ ht2 ∧ x = mrec_sem ht1 ∧ y = mrec_sem ht2)’ >> *)
  (* rw [] >> *)
  (* (* change to last_x_assum *) *)
  (* pop_last_assum kall_tac >> *)
  (* gs [Once itreeTauTheory.itree_wbisim_cases] *)
  (* >- (Cases_on ‘e’ *)
  (*     >- (disj1_tac >> *)
  (*         qexists_tac ‘case ht1 of *)
  (*                        Tau u => mrec_sem u *)
  (*                      | _ => mrec_sem (h_prog x >>= k)’ >> *)
  (*         qexists_tac ‘case ht2 of *)
  (*                        Tau u => mrec_sem u *)
  (*                      | _ => mrec_sem (h_prog x >>= k')’ >> *)
  (*         rpt strip_tac *)
  (*         >- (fs [Once itreeTauTheory.strip_tau_cases]) *)
  (*         >- (fs [Once itreeTauTheory.strip_tau_cases]) *)
  (*         >- (disj1_tac >> *)
  (*             qexists_tac ‘case ht1 of *)
  (*                            Tau u => u *)
  (*                          | _ => h_prog x >>= k’ >> *)
  (*             qexists_tac ‘case ht2 of *)
  (*                            Tau u => u *)
  (*                          | _ => h_prog x >>= k'’ >> *)
  (*             rpt strip_tac >> *)
  (*             fs [Once itreeTauTheory.strip_tau_cases] *)
  (*             >- (ho_match_mp_tac strip_tau_vis_wbisim >> *)
  (*                 qexists_tac ‘INL x’ >> *)
  (*                 qexists_tac ‘k’ >> *)
  (*                 qexists_tac ‘k'’ >> *)
  (*                 rw []) >> *)
  (*             (* >- (‘ht1 ≈ Tau (h_prog x >>= k')’ suffices_by (rw []) >>) *) *)
  (*             cheat) >> *)
  (*         cheat) >> *)
  (*     cheat) >> *)
  (* cheat *)
QED

Theorem msem_bind_left_ident:
  mrec_sem ht ≈ Ret x ⇒
  mrec_sem (ht >>= k) ≈ mrec_sem (k x)
Proof
  disch_tac >>
  irule msem_resp_wbisim >>
  drule msem_ret_wbisim_eq >>
  disch_tac >>
  rw [itree_bind_thm_wbisim]
QED

(* Does mrec_sem distribute over bind? *)

(* corollary of ltree left ident law specialised to mrec_sem *)
Theorem msem_compos:
  mrec_sem (h_prog seed) ≈ Ret x ⇒
  mrec_sem (Vis (INL seed) k) ≈ mrec_sem (k x)
Proof
  disch_tac >>
  rw [panItreeSemTheory.mrec_sem_simps] >>
  rw [msem_bind_left_ident]
QED

(* TODO: Only the two theorems below need be proved to complete the
 correspondence proof at the level of wbisim equivalence for ltree's, i.e. by
 converting itree's into branches (still an ITree type) and showing equivalence
 with FBS semantics.

 NB Part of the work for ltree_lift_msem_resp_wbisim is already complete in
 msem_resp_wbisim.
 *)
Theorem ltree_lift_msem_resp_wbisim:
  ht ≈ ht' ⇒
  ltree_lift f st (mrec_sem ht) ≈ ltree_lift f st (mrec_sem ht')
Proof
  cheat
QED

val g = “g:('a,'b) mtree_ans -> ('a,'b) ltree”;

Theorem itree_wbisim_bind_trans:
  t1 ≈ t2 ∧ t1 >>= k ≈ t3 ⇒
  t2 >>= k ≈ t3
Proof
  strip_tac >>
  irule itreeTauTheory.itree_wbisim_trans >>
  qexists_tac ‘t1 >>= k’ >>
  strip_tac
  >- (irule itreeTauTheory.itree_bind_resp_t_wbisim >>
      rw [itreeTauTheory.itree_wbisim_sym])
  >- (rw [])
QED

Theorem itree_wbisim_bind_conv:
  ltree_lift f st (mrec_sem ht) ≈ Ret x ⇒
  (ltree_lift f st (mrec_sem ht) >>= ^g) ≈ g x
Proof
  disch_tac >>
  ‘ltree_lift f st (mrec_sem ht) ≈ ltree_lift f st (mrec_sem ht)’
    by (rw [itreeTauTheory.itree_wbisim_refl]) >>
  irule itree_wbisim_bind_trans >>
  qexists_tac ‘Ret x’ >>
  strip_tac
  >- (rw [itreeTauTheory.itree_wbisim_sym])
  >- (rw [itree_bind_thm_wbisim,
            itreeTauTheory.itree_wbisim_refl])
QED

Theorem msem_cases_tau:
  mrec_sem ht = Tau u ⇒
  (∃seed k. ht = Vis (INL seed) k) ∨
  (∃v. ht = Tau v)
Proof
  cheat
QED

Theorem msem_lift_monad_law:
  mrec_sem (ht >>= k) =
  (mrec_sem ht) >>= mrec_sem o k
Proof
  cheat
  (* rw [Once itreeTauTheory.itree_bisimulation] >> *)
  (* qexists_tac ‘λx y. ∃t k. x = mrec_sem (t >>= k) ∧ y = mrec_sem t >>= mrec_sem o k’ >> *)
  (* rw [] *)
  (* >- (metis_tac []) *)
  (* (* Ret *) *)
  (* >- (pop_assum (assume_tac o GSYM) >> *)
  (*     Cases_on ‘t'’ *)
  (*     >- (gvs [panItreeSemTheory.mrec_sem_simps]) *)
  (*     >- (gvs [panItreeSemTheory.mrec_sem_simps]) *)
  (*     >- (Cases_on ‘a’ >> *)
  (*         gvs [panItreeSemTheory.mrec_sem_simps]) *)
  (*     (* Tau *) *)
  (*     >- (irule *)
  (*        (* Vis e k *) *)
QED

Theorem ltree_lift_monad_law:
  ltree_lift f st (mt >>= k) =
  (ltree_lift f st mt) >>= (ltree_lift f st) o k
Proof
  cheat
QED

Theorem ltree_lift_bind_left_ident:
  (ltree_lift f st (mrec_sem ht)) ≈ Ret x ⇒
  (ltree_lift f st (mrec_sem (ht >>= k))) ≈ (ltree_lift f st (mrec_sem (k x)))
Proof
  disch_tac >>
  rw [msem_lift_monad_law] >>
  rw [ltree_lift_monad_law] >>
  drule itree_wbisim_bind_conv >>
  disch_tac >>
  pop_assum (assume_tac o (SPEC “(ltree_lift f st ∘ mrec_sem ∘ k):('a,'b) lktree”)) >>
  fs [o_THM]
QED

Theorem ltree_lift_compos:
  ltree_lift f st (mrec_sem (h_prog seed)) ≈ Ret x ⇒
  ltree_lift f st (mrec_sem (Vis (INL seed) k)) ≈ ltree_lift f st (mrec_sem (k x))
Proof
  disch_tac >>
  rw [panItreeSemTheory.mrec_sem_simps] >>
  rw [ltree_lift_cases] >>
  rw [ltree_lift_bind_left_ident]
QED

(* Theorem mrec_sem_ret_inv_thm: *)
(*   mrec_sem t = Ret r ⇒ t = Ret r *)
(* Proof *)
(*   disch_tac >> *)
(*   Cases_on ‘t’ >> *)
(*   fs [panItreeSemTheory.mrec_sem_simps] *)
(*   >- (Cases_on ‘a’ >> fs []) *)
(* QED *)

Theorem mrec_sem_bind_thm:
  (mrec_sem (itree_bind (Ret x) k) = mrec_sem (k x)) ∧
  (mrec_sem (itree_bind (Tau u) k) = Tau $ mrec_sem (itree_bind u k)) ∧
  (mrec_sem (itree_bind (Vis e g) k) = mrec_sem (Vis e (λx. itree_bind (g x) k)))
Proof
  rpt strip_tac >>
  rw [panItreeSemTheory.mrec_sem_simps]
QED

Theorem mrec_sem_leaf_compos:
  leaf_of ffis (mrec_sem (rh seed)) = Return x ⇒
  leaf_of ffis (mrec_sem (Vis (INL seed) k)) = leaf_of ffis (mrec_sem (k x))
Proof
  disch_tac >>
  cheat
QED

(* Main correspondence theorem *)

(* Extension for ffi$behaviour capturing evaluation result
 of convergent computations *)
Datatype:
  sem_behaviour =
    SemDiverge (io_event llist)
    | SemTerminate (('a result option) # ('a,'b) state) (io_event list)
    | SemFail
End

Definition fbs_semantics_beh_def:
  fbs_semantics_beh s prog =
  if ∃k. case FST (panSem$evaluate (prog,s with clock := k)) of
         | SOME TimeOut => F
         | SOME (FinalFFI _) => F
         | SOME (Return _) => F
         | _ => T
  then SemFail
  else case some res.
        ∃k t r. panSem$evaluate (prog,s with clock := k) = (r,t) ∧
         res = SemTerminate (r,t) t.ffi.io_events
       of
       | SOME res => res
       | NONE => SemDiverge (build_lprefix_lub
                             (IMAGE (λk. fromList
                                         (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
End

Definition itree_semantics_beh_def:
  itree_semantics_beh s prog =
  let lt = ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,s))) in
      if ltree_converges lt
      then case some res. ∃r t. lt ≈ Ret (r,t) ∧ res = r of
              | SOME TimeOut => SemTerminate (r,t) t.ffi.io_events
              | SOME (FinalFFI _) => SemTerminate (r,t) t.ffi.io_events
              | SOME (Return _) => SemTerminate (r,t) t.ffi.io_events
              | _ => SemFail
      else SemDiverge (stree_trace query_oracle s.ffi (to_stree (mrec_sem (h_prog (prog,s)))))
End

Theorem itree_semantics_corres:
  semantics s prog
Proof
QED


(* We need to be careful how we formulate the predicate P so that recInduct instantiates evaluate_ind
 to a useful set of subgoals.

 TODO: Consider using some other approach (besides itree_el on the mtree_path) that gives us
 compositional rules over the mrec semantics.

 *)
Theorem evaluate_mtree_path_corr:
  ∀p s. s.clock = k ∧ s.ffi = ffis ⇒
        leaf_of ffis (mrec_sem $ h_prog (p,s)) = Return (evaluate (p,s))
Proof
  recInduct panSemTheory.evaluate_ind >>
  rpt (strip_tac) >>
  (* Skip *)
  >- (rw [panSemTheory.evaluate_def] >>
      rw [panItreeSemTheory.h_prog_def] >>
      rw [the_mtree_path_def,leaf_of_def] >>
      rw [toList])
  (* Dec *)
  >- (Cases_on ‘eval s e’
      >- (rw [panItreeSemTheory.h_prog_def] >>
          rw [panItreeSemTheory.h_prog_rule_dec_def] >>
          fs [panSemTheory.evaluate_def] >>
          rw [the_mtree_path_def,leaf_of_def] >>
          rw [toList_THM])
      >- (rw [] >>
         drule mrec_sem_leaf_compos >>
         rw [] >>
         rw [panItreeSemTheory.h_prog_def] >>
         rw [panItreeSemTheory.h_prog_rule_dec_def] >>
         Cases_on ‘evaluate (prog,s with locals := s.locals |+ (v,x))’ >>
         rw [] >>
         rw [panSemTheory.evaluate_def] >>
         rw [leaf_of_def,the_mtree_path_def] >>
         rw [toList_THM])
QED

(* TODO: Have only one proof for the correspondence
 and compare both IO event traces and results (if convergent)
*)
Theorem evaluate_mtree_path_corr_ltree:
  ∀p s. s.clock = k ∧ s.ffi = ffis ⇒
        ltree_lift query_oracle s.ffi (mrec_sem $ h_prog (p,s)) ≈ Ret (evaluate (p,s))
Proof
  recInduct panSemTheory.evaluate_ind >>
  rpt strip_tac
  (* Skip *)
  >- (rw [panSemTheory.evaluate_def] >>
      rw [panItreeSemTheory.h_prog_def] >>
      rw [panItreeSemTheory.mrec_sem_simps] >>
      rw [ltree_lift_cases] >>
      rw [itreeTauTheory.itree_wbisim_refl])
  (* Dec *)
  >- (Cases_on ‘eval s e’
      >- (rw [panItreeSemTheory.h_prog_def,
                panItreeSemTheory.h_prog_rule_dec_def] >>
          rw [panItreeSemTheory.mrec_sem_simps] >>
          rw [panSemTheory.evaluate_def] >>
          rw [ltree_lift_cases] >>
          rw [itreeTauTheory.itree_wbisim_refl])
      >- (rw [] >>
          rw [panItreeSemTheory.h_prog_def,
                panItreeSemTheory.h_prog_rule_dec_def] >>
          drule ltree_lift_compos >>
          disch_tac >>
          rw [panSemTheory.evaluate_def] >>
          Cases_on ‘evaluate (prog,s with locals := s.locals |+ (v,x))’ >>
          rw [] >>
          pop_assum kall_tac >>
          pop_assum (assume_tac o (SPEC “(λ(res,s'). Ret (res,s' with locals := res_var s'.locals (v,FLOOKUP (s:('a,'a) state).locals v))):('a,'a) hktree”)) >>
          fs [panItreeSemTheory.mrec_sem_simps,
              ltree_lift_cases])
     )
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
     (∃r. outcome = Success ⇔ (itree_leaf_val query_oracle or t) = SOME (Return r)) ∧
     (∃e. outcome = (FFI_outcome e) ⇔ (itree_leaf_val query_oracle or t) = NONE))
End

(* An eqv relation between evaluate and evaluate_itree outcomes; which we expect
 to match as follow the same pattern of rules for computing state and final
 outcomes. *)
Definition same_outcome_def:
  same_outcome ffis t (SOME r,s) ⇔
    itree_leaf_val query_oracle ffis t = (SOME r)
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

Theorem itree_evaluate_htree_leaf:
  itree_leaf_val f s (itree_evaluate c1 s) = x ⇒
  itree_bind (h_prog (c1,s)) k = k x
Proof
  cheat
QED

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
      ‘itree_leaf_val query_oracle ffis (itree_evaluate (Seq c1 c2) s) =
       itree_leaf_val query_oracle ffis (itree_evaluate c1 s)’ suffices_by (rw []) >>
      (* irule leaf_val_path_eq >> *)
      (* AP_TERM_TAC >> *)
      (* rw [itree_evaluate_eq_htree] >> *)
      rw [panItreeSemTheory.itree_evaluate_def] >>
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
  evaluate (p,s) = (SOME r,s') ∧ r ≠ TimeOut ∧ s.clock = k ∧ s.ffi = ffis ⇒
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
