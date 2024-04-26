(*
    Proof of correspondence between functional big-step
    and itree semantics for Pancake.
*)

open preamble
     itreeTauTheory
     panSemTheory
     panItreePropsTheory
     panItreeSemTheory
     panLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           ffiTheory
           panPropsTheory
            in end;

val _ = new_theory "panItreeSemEquiv";

val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;
Overload "case" = “itree_CASE”;

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

(* Path over semtrees:
 - states consist of (ffi_state x 'a result option) pairs,
 - transition labels have type: 'b sem_vis_event option
 *)
val t = “t:('a,'b,'c) itree”;

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

(* Produces a llist of the IO events on a path in the given tree
 determined by a stateful branching choice function. *)
val st = “st:('a,'b) stree”;

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

(* ltree is the monad of leaves of an mtree (essentially branches that contain
only Ret and Tau nodes).

ltree_lift lifts the mtree monad into the ltree monad and satisfies the usual
monad transformer laws. *)

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
     ALLGOALS (rw [Once itree_iter_thm])
QED

(* this lemma is false as stated.
    Counterexample:
      ht = Vis (INL (Skip,ARB)) $ K $ Ret x
Theorem msem_ret_wbisim_eq:
  mrec_sem (Vis (INL (Skip,ARB)) $ K $ Ret x) ≈ Ret x ⇒
  ht ≈ Ret x
Proof
  cheat
QED
*)

(* this lemma is false as stated. Counterexample: u = Tau $ Ret x
Theorem itree_wbisim_ret_u:
  Ret x ≈ u ⇒
  u = Ret x
Proof
  cheat
QED
*)

Theorem strip_tau_FUNPOW:
  ∀t1 t2. strip_tau t1 t2 ⇒
        ∃n. t1 = FUNPOW Tau n $ t2
Proof
  Induct_on ‘strip_tau’ >>
  rw[]
  >- (qrefine ‘SUC _’ >>
      rw[FUNPOW_SUC] >>
      metis_tac[]
     ) >>
  qexists ‘0’ >>
  rw[]
QED

Theorem FUNPOW_Tau_wbisim:
  FUNPOW Tau n x ≈ x
Proof
  Induct_on ‘n’ >>
  rw[itree_wbisim_refl,FUNPOW_SUC]
QED

Theorem FUNPOW_Tau_wbisim_intro:
  x ≈ y ⇒ FUNPOW Tau n x ≈ FUNPOW Tau n' y
Proof
  metis_tac[FUNPOW_Tau_wbisim,itree_wbisim_trans,itree_wbisim_refl,itree_wbisim_sym]
QED

Theorem strip_tau_vis_wbisim:
  ∀e k k'. strip_tau t (Vis e k) ∧ strip_tau t' (Vis e k') ∧ (∀r. k r ≈ k' r) ⇒
  t ≈ t'
Proof
  rpt strip_tac >>
  imp_res_tac strip_tau_FUNPOW >>
  gvs[] >>
  irule FUNPOW_Tau_wbisim_intro >>
  rw[Once itree_wbisim_cases]
QED

Theorem itree_wbisim_Ret_FUNPOW:
  t ≈ Ret x ⇒ ∃n. t = FUNPOW Tau n $ Ret x
Proof
  rw[Once itree_wbisim_cases] >>
  drule_then irule strip_tau_FUNPOW
QED

Theorem msem_bind_left_ident:
  mrec_sem ht ≈ Ret x ⇒
  mrec_sem (ht >>= k) ≈ mrec_sem (k x)
Proof
  strip_tac >>
  dxrule itree_wbisim_Ret_FUNPOW >>
  simp[PULL_EXISTS] >>
  qid_spec_tac ‘ht’ >>
  Induct_on ‘n’
  >- (rw[] >>
      Cases_on ‘ht’ >> gvs[mrec_sem_simps,itree_wbisim_refl] >>
      rename1 ‘Vis e’ >> Cases_on ‘e’ >> gvs[mrec_sem_simps,itree_wbisim_refl]) >>
  rw[FUNPOW_SUC] >>
  Cases_on ‘ht’ >> gvs[mrec_sem_simps,itree_wbisim_refl] >>
  rename1 ‘Vis e’ >> Cases_on ‘e’ >> gvs[mrec_sem_simps,itree_wbisim_refl] >>
  first_x_assum dxrule >>
  gvs[itree_bind_assoc]
QED

(* corollary of ltree left ident law specialised to mrec_sem *)
Theorem msem_compos:
  mrec_sem (h_prog seed) ≈ Ret x ⇒
  mrec_sem (Vis (INL seed) k) ≈ mrec_sem (k x)
Proof
  disch_tac >>
  rw [mrec_sem_simps] >>
  rw [msem_bind_left_ident]
QED

(* TODO: Only the two theorems below need be proved to complete the
 correspondence proof at the level of wbisim equivalence for ltree's, i.e. by
 converting itree's into branches (still an ITree type) and showing equivalence
 with FBS semantics.

 NB Part of the work for ltree_lift_msem_resp_wbisim is already complete in
 msem_resp_wbisim.
 *)

Theorem strip_tau_mrec_sem_Ret:
  ∀x y. strip_tau x (Ret y) ⇒ strip_tau (mrec_sem x) (mrec_sem (Ret y))
Proof
  Induct_on ‘strip_tau’ >>
  rw[mrec_sem_simps]
QED

Theorem strip_tau_ltree_lift_Ret:
  ∀x y. strip_tau x (Ret y) ⇒ strip_tau (ltree_lift f st x) (ltree_lift f st (Ret y))
Proof
  Induct_on ‘strip_tau’ >>
  rw[ltree_lift_cases]
QED

Theorem strip_tau_mrec_sem_INR:
  ∀x x' k. strip_tau x (Vis (INR x') k) ⇒ strip_tau (mrec_sem x) (mrec_sem (Vis (INR x') k))
Proof
  Induct_on ‘strip_tau’ >>
  rw[mrec_sem_simps] >>
  rw[mrec_sem_simps]
QED

Theorem strip_tau_mrec_sem_INL:
  ∀x x' k. strip_tau x (Vis (INL x') k) ⇒
        ∃t n. mrec_sem x = Tau $ mrec_sem (FUNPOW Tau n $ h_prog x' >>= k)
Proof
  Induct_on ‘strip_tau’ >>
  rw[] >>
  rw[mrec_sem_simps]
  >- (qrefine ‘SUC _’ >>
      rw[mrec_sem_simps,FUNPOW_SUC] >>
      metis_tac[]
     ) >>
  qexists ‘0’ >>
  simp[]
QED

Theorem msem_resp_wbisim:
  ht ≈ ht' ⇒ mrec_sem ht ≈ mrec_sem ht'
Proof
  strip_tac >>
  irule itree_wbisim_coind_upto >>
  qexists_tac ‘λx y. ∃x' y'. x = mrec_sem x' ∧ y = mrec_sem y' ∧ x' ≈ y'’ >>
  reverse conj_tac >- metis_tac[itree_wbisim_refl,itree_wbisim_trans] >>
  pop_assum kall_tac >>
  rw[] >>
  pop_assum mp_tac >>
  rw[Once itree_wbisim_cases,PULL_EXISTS]
  >- (gvs[mrec_sem_simps] >> metis_tac[])
  >- (rename1 ‘Vis e’ >>
      Cases_on ‘e’
      >- (imp_res_tac strip_tau_mrec_sem_INL >>
          rw[] >>
          rpt disj1_tac >>
          rpt $ first_x_assum $ irule_at $ Pos hd >>
          rpt $ irule_at (Pos hd) EQ_REFL >>
          irule FUNPOW_Tau_wbisim_intro >>
          irule itree_bind_resp_k_wbisim >>
          simp[]) >>
      imp_res_tac strip_tau_mrec_sem_INR >>
      disj2_tac >> disj1_tac >>
      gvs[mrec_sem_simps] >>
      rpt $ first_x_assum $ irule_at $ Pos hd >>
      simp[] >>
      strip_tac >>
      disj1_tac >>
      rw[GSYM mrec_sem_simps] >>
      rpt $ irule_at (Pos hd) EQ_REFL >>
      gvs[]) >>
  imp_res_tac strip_tau_mrec_sem_Ret >>
  gvs[mrec_sem_simps] >> metis_tac[]
QED

Theorem ltree_lift_Vis_alt:
  ltree_lift f st (Vis ek g) =
  (let (a,rbytes,st') = f st $ FST ek in Tau (ltree_lift f st' ((g ∘ (SND ek)) a)))
Proof
  Cases_on ‘ek’ >> rw[ltree_lift_cases]
QED

Theorem strip_tau_ltree_lift_Vis:
  ∀x e k. strip_tau x (Vis e k) ⇒
        ∃t n. ltree_lift f st x =
              Tau $ ltree_lift f (SND $ SND $ f st $ FST e)
                  (FUNPOW Tau n $ k $ SND e $ FST $ f st $ FST e)
Proof
  Induct_on ‘strip_tau’ >>
  rw[ltree_lift_cases,ltree_lift_Vis_alt] >>
  rw[ltree_lift_cases,ltree_lift_Vis_alt]
  >- (qrefine ‘SUC _’ >>
      rw[ltree_lift_cases,FUNPOW_SUC] >>
      metis_tac[]
     ) >>
  qexists ‘0’ >>
  rw[ELIM_UNCURRY]
QED

Theorem ltree_lift_resp_wbisim:
  t ≈ t' ⇒ ltree_lift f st t ≈ ltree_lift f st t'
Proof
  strip_tac >>
  irule itree_wbisim_coind_upto >>
  qexists_tac ‘λx y. ∃x' y' f st. x = ltree_lift f st x' ∧ y = ltree_lift f st y' ∧ x' ≈ y'’ >>
  reverse conj_tac >- metis_tac[itree_wbisim_refl,itree_wbisim_trans] >>
  pop_assum kall_tac >>
  rw[] >>
  pop_assum mp_tac >>
  rw[Once itree_wbisim_cases,PULL_EXISTS]
  >- (gvs[ltree_lift_cases] >> metis_tac[])
  >- (rpt $ dxrule_then (qspecl_then [‘st’,‘f’] strip_assume_tac) strip_tau_ltree_lift_Vis >>
      gvs[] >>
      rpt $ disj1_tac >>
      rpt $ irule_at (Pos hd) EQ_REFL >>
      match_mp_tac FUNPOW_Tau_wbisim_intro >>
      simp[]) >>
  rpt $ dxrule_then (qspecl_then [‘st’,‘f’] strip_assume_tac) strip_tau_ltree_lift_Ret >>
  gvs[ltree_lift_cases] >>
  metis_tac[]
QED

Theorem ltree_lift_msem_resp_wbisim:
  ht ≈ ht' ⇒
  ltree_lift f st (mrec_sem ht) ≈ ltree_lift f st (mrec_sem ht')
Proof
  metis_tac[ltree_lift_resp_wbisim,msem_resp_wbisim]
QED

val g = “g:('a,'b) mtree_ans -> ('a,'b) ltree”;

Theorem ltree_wbisim_bind_conv:
  ltree_lift f st (mrec_sem ht) ≈ Ret x ⇒
  (ltree_lift f st (mrec_sem ht) >>= ^g) ≈ g x
Proof
  disch_tac >>
  ‘ltree_lift f st (mrec_sem ht) ≈ ltree_lift f st (mrec_sem ht)’
    by (rw [itree_wbisim_refl]) >>
  irule itree_wbisim_bind_trans >>
  qexists_tac ‘Ret x’ >>
  strip_tac
  >- (rw [itree_wbisim_sym])
  >- (rw [itree_bind_thm_wbisim,
            itree_wbisim_refl])
QED

Theorem msem_lift_monad_law:
  mrec_sem (ht >>= k) =
  (mrec_sem ht) >>= mrec_sem o k
Proof
  cheat
QED

Definition ltree_lift_state_def:
  ltree_lift_state f st t =
  SND $
  WHILE
    (λ(t,st). case t of Ret _ => F | _ => T)
    (λ(t,st).
        case t of
        | Ret _ => (t,st)
        | Tau t => (t,st)
        | Vis (e,k) g =>
          let (a,rbytes,st') = f st e in
            ((g ∘ k) a,st')
    )
    (t,st)
End

Theorem ltree_lift_state_simps:
  ltree_lift_state f st (Ret x) = st ∧
  ltree_lift_state f st (Tau t) = ltree_lift_state f st t ∧
  ltree_lift_state f st (Vis ek g) =
   let (a,rbytes,st') = f st (FST ek) in
     ltree_lift_state f st' ((g ∘ (SND ek)) a)
Proof
  rpt conj_tac >>
  rw[ltree_lift_state_def, Once whileTheory.WHILE] >>
  rw[ELIM_UNCURRY] >>
  PURE_TOP_CASE_TAC >> rw[]
QED

Theorem ltree_lift_monad_law:
  ltree_lift f st (mt >>= k) =
  (ltree_lift f st mt) >>= (ltree_lift f (ltree_lift_state f st mt)) o k
Proof
  rw[Once itree_strong_bisimulation] >>
  qexists ‘CURRY {(ltree_lift f st (mt >>= k),
                  (ltree_lift f st mt) >>= (ltree_lift f (ltree_lift_state f st mt)) o k)
                  | T
                 }’ >>
  conj_tac >- (rw[ELIM_UNCURRY,EXISTS_PROD] >> metis_tac[]) >>
  rw[ELIM_UNCURRY,EXISTS_PROD] >>
  rename [‘ltree_lift f st t >>= _’]
  >~ [‘Ret’]
  >- (Cases_on ‘t’ >> gvs[ltree_lift_cases,ltree_lift_state_simps,ltree_lift_Vis_alt,
                          ELIM_UNCURRY])
  >~ [‘Tau’]
  >- (Cases_on ‘t’ >>
      gvs[ltree_lift_cases,ltree_lift_state_simps,ltree_lift_Vis_alt]
      >- metis_tac[]
      >- metis_tac[] >>
      pairarg_tac >> gvs[ltree_lift_state_simps] >>
      metis_tac[])
  >~ [‘Vis’]
  >- (Cases_on ‘t’ >>
      gvs[ltree_lift_cases,ltree_lift_state_simps,ltree_lift_Vis_alt,ELIM_UNCURRY] >>
      rename1 ‘ltree_lift _ _ tt’ >> Cases_on ‘tt’ >> gvs[ltree_lift_cases,ltree_lift_Vis_alt,ELIM_UNCURRY])
QED

Theorem ltree_lift_bind_left_ident:
  (ltree_lift f st (mrec_sem ht)) ≈ Ret x ⇒
  (ltree_lift f st (mrec_sem (ht >>= k))) ≈ (ltree_lift f st (mrec_sem (k x)))
Proof
  disch_tac >>
  rw [msem_lift_monad_law] >>
  rw [ltree_lift_monad_law] >>
  drule ltree_wbisim_bind_conv >>
  disch_tac >>
  pop_assum (assume_tac o (SPEC “(ltree_lift f st ∘ mrec_sem ∘ k):('a,'b) lktree”)) >>
  fs [o_THM]
QED

Theorem ltree_lift_compos:
  ltree_lift f st (mrec_sem (h_prog seed)) ≈ Ret x ⇒
  ltree_lift f st (mrec_sem (Vis (INL seed) k)) ≈ ltree_lift f st (mrec_sem (k x))
Proof
  disch_tac >>
  rw [mrec_sem_simps] >>
  rw [ltree_lift_cases] >>
  rw [ltree_lift_bind_left_ident]
QED

Theorem mrec_sem_bind_thm:
  (mrec_sem (itree_bind (Ret x) k) = mrec_sem (k x)) ∧
  (mrec_sem (itree_bind (Tau u) k) = Tau $ mrec_sem (itree_bind u k)) ∧
  (mrec_sem (itree_bind (Vis e g) k) = mrec_sem (Vis e (λx. itree_bind (g x) k)))
Proof
  rpt strip_tac >>
  rw [mrec_sem_simps]
QED

Theorem mrec_sem_leaf_compos:
  leaf_of ffis (mrec_sem (rh seed)) = Return x ⇒
  leaf_of ffis (mrec_sem (Vis (INL seed) k)) = leaf_of ffis (mrec_sem (k x))
Proof
  cheat
QED

(* Main correspondence theorem *)

(* Extension for ffi$behaviour capturing evaluation result
 of convergent computations *)
Datatype:
  sem_behaviour =
    SemDiverge (io_event llist)
    | SemTerminate (('a result option) # ('a,'b) bstate) (io_event list)
    | SemFail
End

Definition fbs_semantics_beh_def:
  fbs_semantics_beh s prog =
  if ∃k. FST $ panSem$evaluate (prog,(reclock s) with clock := k) ≠ SOME TimeOut
  then (case some (r,s'). ∃k. evaluate (prog,(reclock s) with clock := k) = (r,s') ∧ r ≠ SOME TimeOut of
         SOME (r,s') => (case r of
                           SOME (Return _) => SemTerminate (r,unclock s') s'.ffi.io_events
                         | SOME (FinalFFI _) => SemTerminate (r,unclock s') s'.ffi.io_events
                         | SOME Error => SemFail
                         | _ =>  SemTerminate (r,unclock s') s'.ffi.io_events)
       | NONE => SemFail)
  else SemDiverge (build_lprefix_lub
                   (IMAGE (λk. fromList
                               (SND (evaluate (prog,(reclock s) with clock := k))).ffi.io_events) UNIV))
End

Definition itree_semantics_beh_def:
  itree_semantics_beh s prog =
  let lt = ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,s))) in
      case some (r,s'). lt ≈ Ret (r,s') of
      | SOME (r,s') => (case r of
                      SOME TimeOut => SemTerminate (r,s') s'.ffi.io_events
                    | SOME (FinalFFI _) => SemTerminate (r,s') s'.ffi.io_events
                    | SOME (Return _) => SemTerminate (r,s') s'.ffi.io_events
                    | SOME Error => SemFail
                    | _ => SemTerminate (r,s') s'.ffi.io_events)
      | NONE => SemDiverge (stree_trace query_oracle s.ffi (to_stree (mrec_sem (h_prog (prog,s)))))
End

Theorem itree_sem_div_compos_thm:
  itree_semantics_beh (s with locals := s.locals |+ (v,x)) prog = SemDiverge l ⇒
  itree_semantics_beh s (Dec v e prog) = SemDiverge l
Proof
  cheat
QED

Theorem fbs_sem_div_compos_thm:
  fbs_semantics_beh s (Dec v e prog) = SemDiverge l ∧
  eval (reclock s) e = SOME x ⇒
  fbs_semantics_beh (s with locals := s.locals |+ (v,x)) prog = SemDiverge l
Proof
  rpt strip_tac>>
  fs[fbs_semantics_beh_def,Once evaluate_def] >>
  fs[bool_case_eq]>-
  rpt (FULL_CASE_TAC>>fs[])>>
  disj2_tac>>
  conj_tac>-
   (strip_tac>>first_x_assum $ qspec_then ‘k’ assume_tac>>
    FULL_CASE_TAC>>fs[]>>
    pairarg_tac>>fs[]>>gvs[panPropsTheory.eval_upd_clock_eq,panItreeSemTheory.reclock_def])>>
  irule lprefix_lubTheory.IMP_build_lprefix_lub_EQ>>
  conj_asm1_tac>-
   (simp[lprefix_chain_def]>>
    rpt strip_tac>>fs[]>>
    Cases_on ‘k' < k’>-
     (disj2_tac>>
      simp[LPREFIX_def,from_toList]>>
      irule IS_PREFIX_TRANS>>
      irule_at Any panPropsTheory.evaluate_add_clock_io_events_mono>>
      qexists_tac ‘k - k'’>>fs[])>>
    fs[NOT_LESS]>>
    disj1_tac>>
    simp[LPREFIX_def,from_toList]>>
    irule IS_PREFIX_TRANS>>
    irule_at Any panPropsTheory.evaluate_add_clock_io_events_mono>>
    qexists_tac ‘k' - k’>>fs[])>>
  conj_asm1_tac>-
   (simp[lprefix_chain_def]>>
    rpt strip_tac>>fs[]>>
    Cases_on ‘k' < k’>-
     (disj2_tac>>
      simp[LPREFIX_def,from_toList]>>
      irule IS_PREFIX_TRANS>>
      irule_at Any panPropsTheory.evaluate_add_clock_io_events_mono>>
      qexists_tac ‘k - k'’>>fs[])>>
    fs[NOT_LESS]>>
    disj1_tac>>
    simp[LPREFIX_def,from_toList]>>
    irule IS_PREFIX_TRANS>>
    irule_at Any panPropsTheory.evaluate_add_clock_io_events_mono>>
    qexists_tac ‘k' - k’>>fs[])>>
  conj_tac>-
   (simp[lprefix_rel_def]>>
    rpt strip_tac>>
    simp[PULL_EXISTS]>>
    simp[LPREFIX_def,from_toList]>>
    simp[Once evaluate_def,
         panItreeSemTheory.reclock_def,
         panPropsTheory.eval_upd_clock_eq]>>
    pairarg_tac>>fs[]>>
    qexists_tac ‘k’>>fs[])>>
  simp[lprefix_rel_def]>>
  rpt strip_tac>>
  simp[PULL_EXISTS]>>
  simp[LPREFIX_def,from_toList]>>
  simp[SimpR “isPREFIX”, Once evaluate_def,
       panItreeSemTheory.reclock_def,
       panPropsTheory.eval_upd_clock_eq]>>
  qexists_tac ‘k’>>
  pairarg_tac>>fs[panItreeSemTheory.reclock_def]
QED

Theorem fbs_sem_conv_compos_thm:
  fbs_semantics_beh s (Dec v e prog) = SemTerminate p l ∧
  eval (reclock s) e = SOME x ⇒
  fbs_semantics_beh (s with locals := s.locals |+ (v,x)) prog = SemTerminate p l
Proof
  cheat
QED

Theorem itree_sem_conv_compos_thm:
  itree_semantics_beh (s with locals := s.locals |+ (v,x)) prog = SemTerminate p l ⇒
  itree_semantics_beh s (Dec v e prog) = SemTerminate p l
Proof
  cheat
QED

Theorem fbs_sem_fail_compos_thm:
  fbs_semantics_beh s (Dec v e prog) = SemFail ∧
  eval (reclock s) e = SOME x ⇒
  fbs_semantics_beh (s with locals := s.locals |+ (v,x)) prog = SemFail
Proof
  cheat
QED

Theorem itree_sem_fail_compos_thm:
  itree_semantics_beh (s with locals := s.locals |+ (v,x)) prog = SemFail ⇒
  itree_semantics_beh s (Dec v e prog) = SemFail
Proof
  cheat
QED

Theorem fbs_semantics_beh_simps:
  fbs_semantics_beh s Skip = SemTerminate (NONE,s) s.ffi.io_events ∧
  (eval (reclock s) e = NONE ⇒ fbs_semantics_beh s (Dec v e prog) ≠ SemTerminate p l)
Proof
  rw []
  >- (rw [fbs_semantics_beh_def,
          evaluate_def] >>
      DEEP_INTRO_TAC some_intro >> rw [EXISTS_PROD] >>
      ntac 2 TOP_CASE_TAC >>
      pairarg_tac >> gvs [panItreeSemTheory.unclock_def,panItreeSemTheory.reclock_def,
                          panItreeSemTheory.bstate_component_equality])
  >- (rw [fbs_semantics_beh_def,
          evaluate_def] >>
      rw [panPropsTheory.eval_upd_clock_eq] >>
      DEEP_INTRO_TAC some_intro >> rw [] >>
      FULL_CASE_TAC >> fs [])
QED

Theorem itree_semantics_beh_simps:
  (itree_semantics_beh s Skip = SemTerminate (NONE, s) s.ffi.io_events) ∧
  (eval (reclock s) e = NONE ⇒
   itree_semantics_beh s (Dec v e prog) = SemFail)
Proof
  rw []
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (ntac 2 TOP_CASE_TAC >>
          fs [h_prog_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,
          mrec_sem_simps] >>
      fs [ltree_lift_cases] >>
      fs [Once itree_wbisim_cases])>>
  rw [itree_semantics_beh_def]>>
  DEEP_INTRO_TAC some_intro >> rw [EXISTS_PROD]>>
  fs [itree_semantics_beh_def,
      h_prog_def,
      h_prog_rule_dec_def] >>
  rpt CASE_TAC>>gvs[]>>
  fs [ltree_lift_cases,
      mrec_sem_simps] >>
  fs [Once itree_wbisim_cases]
QED

Theorem fbs_semantics_beh_cases:
  fbs_semantics_beh s prog = SemDiverge l ⇔
  (∀k. FST (evaluate (prog,(reclock s) with clock := k)) = SOME TimeOut) ∧
  l = LUB (IMAGE
           (λk. fromList
                (SND (evaluate (prog,(reclock s) with clock := k))).ffi.io_events) 𝕌(:num))
Proof
  EQ_TAC
  >- (rpt strip_tac >>>
          TRYALL (fs [fbs_semantics_beh_def] >>
                  rpt (FULL_CASE_TAC >> gvs [])))
  >- (rw [fbs_semantics_beh_def])
QED

Theorem itree_sem_while_fails:
  eval (reclock s) e = x ∧ (x = NONE ∨ x = SOME (ValLabel v1) ∨ x = SOME (Struct v2)) ⇒
  itree_semantics_beh s (While e c) = SemFail
Proof
  rw [itree_semantics_beh_def] >>
  gvs [h_prog_def,
       h_prog_rule_while_def,
       Once itree_iter_thm,
       mrec_sem_simps,
       ltree_lift_cases] >>
  DEEP_INTRO_TAC some_intro >>
  rw [] >>>
     ALLGOALS ((fs [ELIM_UNCURRY] >>
                ‘x = (SOME Error,s)’ by (fs [Once itree_wbisim_cases]) >>
                rw [])
               ORELSE (qexists_tac ‘(SOME Error,s)’ >>
                       rw [itree_wbisim_refl]))
QED

Theorem itree_sem_while_no_loop:
  eval (reclock s) e = SOME (ValWord 0w) ⇒
  itree_semantics_beh s (While e c) = SemTerminate (NONE,s) s.ffi.io_events
Proof
  rw [itree_semantics_beh_def] >>
  gvs [h_prog_def,
       h_prog_rule_while_def,
       Once itree_iter_thm,
       mrec_sem_simps,
       ltree_lift_cases] >>
  DEEP_INTRO_TAC some_intro >>
  rw [] >>>
     ALLGOALS ((fs [ELIM_UNCURRY] >>
                ‘x = (NONE,s)’ by (fs [Once itree_wbisim_cases]) >>
                rw [])
               ORELSE (qexists_tac ‘(NONE,s)’ >>
                       rw [itree_wbisim_refl]))
QED

(* Final goal:

   1. For every path that can be generated frong

   that produces an equivalent result in the functional semantics.
   2. For every oracle, there is a path producing a corresponding result in the ITree semantics.
 *)

Theorem itree_semantics_corres:
  fbs_semantics_beh s prog = itree_semantics_beh s prog
Proof
  rw [fbs_semantics_beh_def]
  >- (DEEP_INTRO_TAC some_intro >> reverse $ rw []
      >- (gvs [ELIM_UNCURRY]) >>
      pairarg_tac >> gvs [] >>
      CONV_TAC SYM_CONV >>
      last_x_assum kall_tac >>
      ‘s = unclock(reclock s with clock := k')’
        by(gvs[panItreeSemTheory.reclock_def,
               panItreeSemTheory.unclock_def,
               panItreeSemTheory.bstate_component_equality]) >>
      pop_assum $ PURE_ONCE_REWRITE_TAC o single >>
      rename1 ‘itree_semantics_beh(unclock t)’ >>
      rpt $ pop_assum MP_TAC >>
      MAP_EVERY qid_spec_tac [‘s'’,‘r’,‘t’,‘prog’] >>
      recInduct evaluate_ind >> rw []
      >~ [‘While’]
      >- (rgs [Once evaluate_def,
               AllCaseEqs()] >> gvs []>>
          TRY (rw [itree_sem_while_fails,panPropsTheory.eval_upd_clock_eq])
           >- (cheat) >>
          CONV_TAC SYM_CONV >>
          irule EQ_TRANS>>
          irule_at Any itree_sem_while_no_loop>>
          fs[unclock_def,panPropsTheory.eval_upd_clock_eq])>>
      (* All remaining terms... for convg case *)
      cheat)
  (* Div *)
  >- (CONV_TAC SYM_CONV >>
      Cases_on ‘itree_semantics_beh s prog’ >>
      simp []
      >- (irule $ iffLR lprefix_lubTheory.build_prefix_lub_intro >>
          rw []
          (* lprefix case *)
          >- (rw [lprefix_lubTheory.lprefix_chain_def] >>
              Induct_on ‘k’ >>
              Induct_on ‘k'’ >>
              qid_spec_tac ‘s’ >>
              qid_spec_tac ‘prog’ >>
              recInduct panSemTheory.evaluate_ind >>
              rw []
              >~ [‘While’]
               (* lprefix -> while case *)
              >- (DISJ1_TAC >>
                  rw [Once panSemTheory.evaluate_def] >>
                  TOP_CASE_TAC >>
                  rw []
               )
             )
           (* lprefix_lub case *)
          >- (cheat
           ))
      >- (cheat)
      >- (cheat)
      >- (simp [lprefix_lubTheory.lprefix_lub_def] >>
          conj_asm1_tac
          >- (cheat)
          >- (rw [] >>
              (* Prove l is the least prefix *)
              cheat)
          >- (cheat)
          >- (cheat)))
     (*    Cases_on ‘eval s e’ *)
     (* >- (fs [Once evaluate_def, *)
     (*         panPropsTheory.eval_upd_clock_eq]) *)
     (* >- (Cases_on ‘x’ >> gvs [] *)
     (*     >- (Cases_on ‘w’ >> gvs [] *)
     (*         >- (Cases_on ‘c' ≠ 0w’ >> gvs [] *)
     (*             >- (Cases_on ‘s'.clock’ >> gvs [] *)
     (*                ) *)
     (*            ) *)
     (*        ) *)
     (*    Cases_on ‘fbs_semantics_beh s prog’ *)
     (* (* Div *) *)
     (* >-  (fs [fbs_semantics_beh_cases] >> *)
     (*      CONV_TAC SYM_CONV >> *)
     (*      Q.PAT_UNDISCH_TAC ‘∀k. _ = SOME TimeOut’ >> *)
     (*      qid_spec_tac ‘s’ >> *)
     (*      qid_spec_tac ‘prog’ >> *)
     (*      recInduct evaluate_ind >> *)
     (*      rw [] *)
     (*      (* While *) *)
     (*      >- (Cases_on ‘eval s' e’ *)
     (*          >- (fs [Once evaluate_def, *)
     (*                  panPropsTheory.eval_upd_clock_eq]) *)
     (*          >- (Cases_on ‘x’ >> gvs [] *)
     (*              >- (Cases_on ‘w’ >> gvs [] *)
     (*                  >- (Cases_on ‘c' ≠ 0w’ >> gvs [] *)
     (*                      >- (Cases_on ‘s'.clock’ >> gvs [] *)
     (*                         ) *)
     (*                     ) *)
     (*                 ) *)
     (*             ) *)
     (*         ) *)
     (*      (* Skip *) *)
     (*      >- (Cases_on ‘fbs_semantics_beh s Skip’ >> *)
     (*          fs [fbs_semantics_beh_simps] *)
     (*          (* Fail is equiv *) *)
     (*          >- (rw [itree_semantics_beh_simps])) *)
     (*      (* Dec *) *)
     (*      >- (Cases_on ‘fbs_semantics_beh s (Dec v e prog)’ *)
     (*          (* Div *) *)
     (*          >- (Cases_on ‘eval s e’ >> rw [] *)
     (*              >- (fs [fbs_semantics_beh_def, *)
     (*                      evaluate_def] >> *)
     (*                  gvs [panPropsTheory.eval_upd_clock_eq] >> *)
     (*                  UNDISCH_TAC “(case *)
     (*                               some(r,s'). ∃k. *)
     (*                                 (r = SOME Error ∧ s with clock := k = s') ∧ r ≠ SOME TimeOut *)
     (*                               of *)
     (*                                 NONE => SemFail *)
     (*                               | SOME (r,s') => *)
     (*                                   case r of *)
     (*                                     NONE => SemFail *)
     (*                                   | SOME Error => SemFail *)
     (*                                   | SOME TimeOut => SemFail *)
     (*                                   | SOME Break => SemFail *)
     (*                                   | SOME Continue => SemFail *)
     (*                                   | SOME (Return v6) => SemTerminate (r,s') s'.ffi.io_events *)
     (*                                   | SOME (Exception v7 v8) => SemFail *)
     (*                                   | SOME (FinalFFI v9) => SemTerminate (r,s') s'.ffi.io_events) = *)
     (*                               SemDiverge l” >> *)
     (*                  DEEP_INTRO_TAC some_intro >> rw [] >> *)
     (*                  FULL_CASE_TAC >> gvs []) *)
     (*              >- (drule fbs_sem_div_compos_thm >> disch_tac >> *)
     (*                  gvs [] >> *)
     (*                  ‘SemDiverge l = itree_semantics_beh s (Dec v e prog)’ suffices_by (gvs []) >> *)
     (*                  irule (GSYM itree_sem_div_compos_thm) >> *)
     (*                  qexists_tac ‘x’ >> rw [])) *)
     (*          (* Conv *) *)
     (*          >- (Cases_on ‘eval s e’ >> rw [] *)
     (*              >- (fs [fbs_semantics_beh_simps]) *)
     (*              >- (drule fbs_sem_conv_compos_thm >> disch_tac >> *)
     (*                  gvs [] >> *)
     (*                  ‘SemTerminate p l = itree_semantics_beh s (Dec v e prog)’ suffices_by (gvs []) >> *)
     (*                  irule (GSYM itree_sem_conv_compos_thm) >> *)
     (*                  qexists_tac ‘x’ >> rw [])) *)
     (*          (* Fail *) *)
     (*          >- (Cases_on ‘eval s e’ >> rw [] *)
     (*              >- (fs [itree_semantics_beh_simps]) *)
     (*              >- (drule fbs_sem_fail_compos_thm >> disch_tac >> *)
     (*                  gvs [] >> *)
     (*                  irule itree_sem_fail_compos_thm >> *)
     (*                  qexists_tac ‘x’ >> rw []))) *)
     (*      (* Assign *) *)
     (*      >- (Cases_on ‘fbs_semantics_beh s (Assign v src)’ >> *)
     (*          fs [fbs_semantics_beh_simps] >> rw [] >> *)
     (*          rw [itree_semantics_beh_simps]) *)
     (*      (* Store *) *)
     (*      >- (Cases_on ‘fbs_semantics_beh s (Store dst src)’ >> *)
     (*         ) *)
     (*     ) *)
QED

(* JÅP: I don't think this below lemma will be provable as stated *)

Theorem evaluate_mtree_path_corr_ltree:
  ∀p s. s.clock = k ∧ s.ffi = ffis ⇒
        ltree_lift query_oracle s.ffi (mrec_sem $ h_prog (p,s)) ≈ Ret (evaluate (p,s))
Proof
  recInduct evaluate_ind >>
  rpt strip_tac
  (* Skip *)
  >- (rw [evaluate_def] >>
      rw [h_prog_def] >>
      rw [mrec_sem_simps] >>
      rw [ltree_lift_cases] >>
      rw [itree_wbisim_refl])
  (* Dec *)
  >- (Cases_on ‘eval s e’
      >- (rw [h_prog_def,
              h_prog_rule_dec_def] >>
          rw [mrec_sem_simps] >>
          rw [evaluate_def] >>
          rw [ltree_lift_cases] >>
          rw [itree_wbisim_refl])
      >- (rw [] >>
          rw [h_prog_def,
              h_prog_rule_dec_def] >>
          drule ltree_lift_compos >>
          disch_tac >>
          rw [evaluate_def] >>
          Cases_on ‘evaluate (prog,s with locals := s.locals |+ (v,x))’ >>
          rw [] >>
          pop_assum kall_tac >>
          pop_assum (assume_tac o (SPEC “(λ(res,s'). Ret (res,s' with locals := res_var s'.locals (v,FLOOKUP (s:('a,'b) state).locals v))):('a,'b) hktree”)) >>
          fs [mrec_sem_simps,
              ltree_lift_cases]) >>
      cheat) >>
  cheat
QED

val _ = export_theory();
