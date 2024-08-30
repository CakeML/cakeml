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
  stree_trace f p fs ^st =
  LFLATTEN $ LUNFOLD
  (λ(fs',t). case t of
                 Ret r => NONE
               | Tau u => SOME ((fs',u),LNIL)
               | Vis e k => let (a,rbytes,fs'') = f fs' e in
                              if p a then
                                SOME ((fs'',k a),[|make_io_event e rbytes|])
                              else
                                SOME ((fs'', k a),LNIL))
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

(***)

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

Theorem msem_tau_cong:
  mrec_sem ht = Tau u ⇔
  (∃u'. ht = Tau u' ∧ u = mrec_sem u') ∨
  (∃e k. ht = Vis (INL e) k ∧ u = mrec_sem (h_prog e >>= k))
Proof
  EQ_TAC
  >- (disch_tac >>
      Cases_on ‘ht’ >>
      gvs [mrec_sem_simps] >>
      reverse $ Cases_on ‘a’
      >- (gvs [mrec_sem_simps]) >>
      qexists_tac ‘x’ >>
      fs [mrec_sem_simps])
  >- (disch_tac >>
      Cases_on ‘ht’
      >- (pop_assum DISJ_CASES_TAC >>
          gvs [])
      >- (reverse $ pop_assum DISJ_CASES_TAC
          >- gvs [mrec_sem_simps] >>
          ‘u = mrec_sem u'’ by (fs []) >>
          rw [mrec_sem_simps])
      >- rgs [mrec_sem_simps])
QED

(* NB: >>= is not idempotent *)
Theorem itree_bind_tau_cong:
  t >>= k = Tau u ⇔
  (∃x. t = Ret x ∧ Tau u = k x) ∨
  ∃u'. t = Tau u' ∧ u = u' >>= k
Proof
  EQ_TAC
  >- (disch_tac >>
      Cases_on ‘t’ >>
      fs [itree_bind_thm])
  >- (disch_tac >>
      Cases_on ‘t’ >>
      metis_tac [itree_bind_thm])
QED

Theorem msem_ret_cong:
  mrec_sem ht = Ret x ⇔ ht = Ret x
Proof
  EQ_TAC >>
  Cases_on ‘ht’ >>
  rw [mrec_sem_simps] >>
  Cases_on ‘a’ >>
  rw [mrec_sem_simps]
QED

Theorem msem_vis_cong:
  mrec_sem ht = Vis e k ⇔
  (∃k'. ht = Vis (INR e) k' ∧ k = Tau o mrec_sem o k')
Proof
  EQ_TAC >>
  Cases_on ‘ht’ >>
  rw [mrec_sem_simps] >>
  Cases_on ‘a’ >>
  fs [mrec_sem_simps]
QED

Theorem itree_bind_tau_abs:
  (λx. Tau (f x)) = Tau o f
Proof
  CONV_TAC FUN_EQ_CONV >>
  rw []
QED

Theorem msem_lift_monad_law:
  mrec_sem (ht >>= k) =
  (mrec_sem ht) >>= mrec_sem o k
Proof
  rw[Once itree_strong_bisimulation] >>
  qexists ‘CURRY ({(mrec_sem (ht >>= k),mrec_sem ht >>= mrec_sem ∘ k) | T} ∪
                  {(Tau $ mrec_sem (ht >>= k),Tau $ mrec_sem ht >>= mrec_sem ∘ k) | T}
                 )’ >>
  conj_tac >- (rw[EXISTS_PROD] >> metis_tac[]) >>
  rw[]
  >- (Cases_on ‘ht’ >> gvs[mrec_sem_simps] >>
      rename1 ‘Vis e’ >> Cases_on ‘e’ >> gvs[mrec_sem_simps])
  >- (Cases_on ‘ht’ >> gvs[mrec_sem_simps,PULL_EXISTS,EXISTS_PROD]
      >- metis_tac[]
      >- metis_tac[] >>
      rename1 ‘Vis e’ >> Cases_on ‘e’ >> gvs[mrec_sem_simps] >>
      metis_tac[itree_bind_assoc])
  >- metis_tac[] >>
  Cases_on ‘ht’ >> gvs[mrec_sem_simps,PULL_EXISTS,EXISTS_PROD]
  >- metis_tac[] >>
  rename1 ‘mrec_sem (Vis e _)’ >>
  Cases_on ‘e’ >>
  gvs[mrec_sem_simps] >>
  metis_tac[]
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
  (ltree_lift f st (mrec_sem (ht >>= k))) ≈ (ltree_lift f (ltree_lift_state f st (mrec_sem ht)) (mrec_sem (k x)))
Proof
  disch_tac >>
  rw [msem_lift_monad_law] >>
  rw [ltree_lift_monad_law] >>
  drule ltree_wbisim_bind_conv >>
  disch_tac >>
  irule itree_wbisim_trans >>
  pop_assum $ irule_at $ Pos hd >>
  rw[o_THM,itree_wbisim_refl]
QED

Theorem ltree_lift_compos:
  ltree_lift f st (mrec_sem (h_prog seed)) ≈ Ret x ⇒
  ltree_lift f st (mrec_sem (Vis (INL seed) k)) ≈ ltree_lift f (ltree_lift_state f st (mrec_sem $ h_prog seed)) (mrec_sem (k x))
Proof
  disch_tac >>
  rw [mrec_sem_simps] >>
  rw [ltree_lift_cases, ltree_lift_bind_left_ident]
QED

(* TODO: move *)
Theorem to_stree_simps:
  to_stree (Ret x) = Ret x ∧
  to_stree (Tau t) = Tau (to_stree t) ∧
  to_stree (Vis eg k) = Vis (FST eg) (to_stree ∘ k ∘ SND eg)
Proof
  rw[to_stree_def] >>
  rw[Once itree_unfold] >>
  Cases_on ‘eg’ >> gvs[]
QED

Theorem to_stree_monad_law:
  to_stree (mt >>= k) =
  to_stree mt >>= to_stree ∘ k
Proof
  rw[Once itree_strong_bisimulation] >>
  qexists ‘CURRY {(to_stree (mt >>= k),
                  (to_stree mt) >>= (to_stree o k))
                  | T
                 }’ >>
  conj_tac >- (rw[ELIM_UNCURRY,EXISTS_PROD] >> metis_tac[]) >>
  rw[ELIM_UNCURRY,EXISTS_PROD] >>
  rename [‘to_stree t >>= _’]
  >~ [‘Ret’]
  >- (Cases_on ‘t’ >> gvs[to_stree_simps,ELIM_UNCURRY])
  >~ [‘Tau’]
  >- (Cases_on ‘t’ >>
      gvs[to_stree_simps] >>
      metis_tac[])
  >~ [‘Vis’]
  >- (Cases_on ‘t’ >>
      gvs[to_stree_simps,ELIM_UNCURRY] >>
      metis_tac[])
QED

Theorem mrec_sem_bind_thm:
  (mrec_sem (itree_bind (Ret x) k) = mrec_sem (k x)) ∧
  (mrec_sem (itree_bind (Tau u) k) = Tau $ mrec_sem (itree_bind u k)) ∧
  (mrec_sem (itree_bind (Vis e g) k) = mrec_sem (Vis e (λx. itree_bind (g x) k)))
Proof
  rpt strip_tac >>
  rw [mrec_sem_simps]
QED
(* Main correspondence theorem *)

(* Extension for ffi$behaviour capturing evaluation result
 of convergent computations *)
Datatype:
  sem_behaviour =
    SemDiverge (io_event llist)
    | SemTerminate (('a result option) # ('a,'b) bstate)
    | SemFail
End

Definition fbs_semantics_beh_def:
  fbs_semantics_beh s prog =
  if ∃k. FST $ panSem$evaluate (prog,(reclock s) with clock := k) ≠ SOME TimeOut
  then (case some (r,s'). ∃k. evaluate (prog,(reclock s) with clock := k) = (r,s') ∧ r ≠ SOME TimeOut of
         SOME (r,s') => (case r of
                           SOME (Return _) => SemTerminate (r,unclock s')
                         | SOME (FinalFFI _) => SemTerminate (r,unclock s')
                         | SOME Error => SemFail
                         | _ =>  SemTerminate (r,unclock s'))
       | NONE => SemFail)
  else SemDiverge (build_lprefix_lub
                   (IMAGE (λk. fromList
                               (SND (evaluate (prog,(reclock s) with clock := k))).ffi.io_events) UNIV))
End

Definition event_filter_def:
  event_filter (FFI_return _ _) = T ∧
  event_filter _ = F
End

Definition itree_semantics_beh_def:
  itree_semantics_beh s prog =
  let lt = ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,s))) in
      case some (r,s'). lt ≈ Ret (r,s') of
      | SOME (r,s') => (case r of
                      SOME TimeOut => SemTerminate (r,s')
                    | SOME (FinalFFI _) => SemTerminate (r,s')
                    | SOME (Return _) => SemTerminate (r,s')
                    | SOME Error => SemFail
                    | _ => SemTerminate (r,s'))
      | NONE => SemDiverge (LAPPEND (fromList(s.ffi.io_events)) (stree_trace query_oracle event_filter s.ffi (to_stree (mrec_sem (h_prog (prog,s))))))
End

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

Theorem fbs_semantics_beh_simps:
  fbs_semantics_beh s Skip = SemTerminate (NONE,s) ∧
  fbs_semantics_beh s (Annot ann) = SemTerminate (NONE,s) ∧
  (eval (reclock s) e = NONE ⇒ fbs_semantics_beh s (Dec v e prog) ≠ SemTerminate p)
Proof
  rw []
  >~ [‘Dec _ _ _’]
  >- (rw [fbs_semantics_beh_def,
          evaluate_def] >>
      rw [panPropsTheory.eval_upd_clock_eq] >>
      DEEP_INTRO_TAC some_intro >> rw [] >>
      FULL_CASE_TAC >> fs [])>>
 (rw [fbs_semantics_beh_def,
          evaluate_def] >>
      DEEP_INTRO_TAC some_intro >> rw [EXISTS_PROD] >>
      ntac 2 TOP_CASE_TAC >>
      pairarg_tac >> gvs [panItreeSemTheory.unclock_def,panItreeSemTheory.reclock_def,
                          panItreeSemTheory.bstate_component_equality])
QED

Theorem ltree_lift_nonret_bind:
  (∀x. ¬(ltree_lift f st p ≈ Ret x))
  ⇒ ltree_lift f st p >>= k = ltree_lift f st p
Proof
  strip_tac >> CONV_TAC SYM_CONV >>
  rw[Once itree_bisimulation] >>
  qexists ‘CURRY {(ltree_lift f st p, ltree_lift f st p >>= k) |
                     (∀x. ¬(ltree_lift f st p ≈ Ret x))}’ >>
  conj_tac >- (rw[EXISTS_PROD] >> metis_tac[]) >>
  pop_assum kall_tac >>
  rw[] >>
  pairarg_tac >> gvs[]
  >- metis_tac[itree_wbisim_refl] >>
  Cases_on ‘p’ >>
  gvs[ltree_lift_cases,
      ltree_lift_Vis_alt,
      EXISTS_PROD,
      ELIM_UNCURRY
     ] >>
  metis_tac[]
QED

Theorem stree_trace_simps:
  stree_trace f p fs (Tau t) = stree_trace f p fs t ∧
  stree_trace f p fs (Ret r) = [||]
  (* TODO: Vis *)
Proof
  rw[stree_trace_def] >>
  rw[Once LUNFOLD]
QED

Theorem ltree_lift_nonret_bind_stree:
  (∀x. ¬(ltree_lift f st p ≈ Ret x))
  ⇒ stree_trace f q st (to_stree p >>= k) = stree_trace f q st $ to_stree p
Proof
  strip_tac >> CONV_TAC SYM_CONV >>
  simp[stree_trace_def] >>
  AP_TERM_TAC >>
  rw[Once LUNFOLD_BISIMULATION] >>
  qexists ‘CURRY {((st,to_stree p), (st, to_stree p >>= k)) |
                     (∀x. ¬(ltree_lift f st p ≈ Ret x))}’ >>
  conj_tac >- (rw[EXISTS_PROD] >> metis_tac[]) >>
  pop_assum kall_tac >>
  rw[] >>
  rpt(pairarg_tac >> gvs[]) >>
  Cases_on ‘p’ >>
  gvs[ltree_lift_cases,
      ltree_lift_Vis_alt,
      to_stree_simps,
      stree_trace_simps,
      EXISTS_PROD,
      ELIM_UNCURRY,
      itree_wbisim_neq
     ] >>
  metis_tac[]
QED

Theorem mrec_sem_FUNPOW_Tau:
  mrec_sem (FUNPOW Tau n t) = FUNPOW Tau n (mrec_sem t)
Proof
  Induct_on ‘n’>>fs[FUNPOW_SUC,mrec_sem_simps]
QED

Theorem ltree_lift_FUNPOW_Tau:
  ltree_lift f st (FUNPOW Tau n t) = FUNPOW Tau n (ltree_lift f st t)
Proof
  Induct_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases]
QED

Theorem to_stree_FUNPOW_Tau:
  to_stree (FUNPOW Tau n t) = FUNPOW Tau n (to_stree t)
Proof
  MAP_EVERY qid_spec_tac [‘t’,‘n’]>>
  Induct_on ‘n’>>rw[]>>
  simp[FUNPOW_SUC,to_stree_simps]
QED

Theorem stree_trace_FUNPOW_Tau:
  stree_trace f p st (FUNPOW Tau n t) = stree_trace f p st t
Proof
  Induct_on ‘n’>>fs[FUNPOW_SUC,stree_trace_simps]
QED

Theorem itree_semantics_beh_Dec:
  itree_semantics_beh s (Dec vname e prog) =
  case eval (reclock s) e of
    NONE => SemFail
  | SOME value =>
      case itree_semantics_beh (s with locals := s.locals |+ (vname,value)) prog of
      | SemTerminate (res,s') =>
          SemTerminate (res,s' with locals := res_var s'.locals (vname,FLOOKUP s.locals vname))
      | res => res
Proof
  rw[itree_semantics_beh_def] >>
  Cases_on ‘eval (reclock s) e’ >>
  gvs[h_prog_def,h_prog_dec_def,mrec_sem_simps,ltree_lift_cases,
      itree_wbisim_neq,
      ELIM_UNCURRY
     ] >>
  CONV_TAC SYM_CONV >>
  DEEP_INTRO_TAC some_intro >>
  reverse conj_tac
  >- (rw[msem_lift_monad_law,
         ltree_lift_monad_law,
         ltree_lift_nonret_bind,
         to_stree_monad_law,
         to_stree_simps,
         stree_trace_simps,
         ltree_lift_nonret_bind_stree
        ]) >>
  rw[] >>
  rename1 ‘Ret r’ >> Cases_on ‘r’ >> gvs[] >>
  drule ltree_lift_bind_left_ident >>
  qmatch_goalsub_abbrev_tac ‘_ >>= k1’ >>
  disch_then $ qspec_then ‘k1’ mp_tac >>
  unabbrev_all_tac >>
  simp[mrec_sem_simps,ltree_lift_cases] >>
  strip_tac >>
  DEEP_INTRO_TAC some_intro >>
  reverse conj_tac
  >- (rw[] >> gvs[]) >>
  rw[] >>
  dxrule_then strip_assume_tac itree_wbisim_sym >>
  dxrule itree_wbisim_trans >>
  strip_tac >>
  first_x_assum dxrule >>
  rw[itree_wbisim_neq] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[])
QED

Theorem itree_semantics_beh_If:
  itree_semantics_beh s (If e p1 p2) =
  case eval (reclock s) e of
  | SOME(ValWord g) => itree_semantics_beh s (if g ≠ 0w then p1 else p2)
  | _ => SemFail
Proof
  rw[itree_semantics_beh_def] >>
  Cases_on ‘eval (reclock s) e’ >>
  gvs[h_prog_def,h_prog_cond_def,mrec_sem_simps,ltree_lift_cases,
      itree_wbisim_neq,
      ELIM_UNCURRY
     ] >>
  CONV_TAC SYM_CONV >>
  PURE_TOP_CASE_TAC >> gvs[mrec_sem_simps,ltree_lift_cases,itree_wbisim_neq] >>
  PURE_TOP_CASE_TAC >> gvs[mrec_sem_simps,ltree_lift_cases,itree_wbisim_neq] >>
  rename1 ‘h_prog(p,s)’ >>
  PURE_TOP_CASE_TAC >> gvs[] >>
  gvs[stree_trace_simps,to_stree_simps]
QED

Theorem ret_eq_funpow_tau:
  (Ret x = FUNPOW Tau n (Ret y)) ⇔ x = y ∧ n = 0
Proof
  Cases_on ‘n’ >> rw[FUNPOW_SUC]
QED

Theorem tau_eq_funpow_tau:
  (Tau t = FUNPOW Tau n (Ret x)) ⇔ ∃n'. n = SUC n' ∧ t = FUNPOW Tau n' (Ret x)
Proof
  Cases_on ‘n’ >> rw[FUNPOW_SUC]
QED

Theorem FUNPOW_Tau_bind_thm:
  ∀k x n t.
    t >>= k = FUNPOW Tau n (Ret x)
    ⇒
    ∃n' n'' y. t = FUNPOW Tau n' (Ret y) ∧
               k y = FUNPOW Tau n'' (Ret x) ∧
               n' + n'' = n
Proof
  ntac 2 strip_tac >>
  Induct >>
  rw[FUNPOW_SUC] >>
  Cases_on ‘t’ >> gvs[itree_bind_thm,ret_eq_funpow_tau,tau_eq_funpow_tau,PULL_EXISTS] >>
  first_x_assum dxrule >>
  rw[] >>
  first_x_assum $ irule_at Any >>
  irule_at (Pos hd) EQ_REFL >>
  simp[]
QED

Theorem ltree_lift_state_bind_funpow:
  ∀k x m f st t.
    ltree_lift f st t = FUNPOW Tau m (Ret x)
    ⇒
    ltree_lift_state f st (t >>= k) =
    ltree_lift_state f (ltree_lift_state f st t) (k x)
Proof
  ntac 2 strip_tac >>
  Induct >>
  rw[FUNPOW_SUC] >>
  Cases_on ‘t’ >>
  gvs[ltree_lift_cases,ltree_lift_state_simps,
      ltree_lift_Vis_alt,
      ELIM_UNCURRY]
QED

Theorem mrec_sem_while_unfold:
  mrec_sem (h_prog (While e p,s)) =
  case eval(reclock s) e of
    SOME (ValWord w) =>
      if w = 0w then Ret (NONE, s)
      else
        Tau(mrec_sem (h_prog (p,s)) >>=
            λ(res,s').
              case res of
                NONE => Tau $ mrec_sem (h_prog (While e p, s'))
              | SOME Break => Ret (NONE, s')
              | SOME Continue => Tau $ mrec_sem (h_prog (While e p, s'))
              | _ => Ret (res, s')
           )
  | _ => Ret(SOME Error, s)
Proof
  rw[h_prog_def,h_prog_while_def] >>
  rw[Once itree_iter_thm] >>
  PURE_TOP_CASE_TAC >> gvs[mrec_sem_simps] >>
  PURE_TOP_CASE_TAC >> gvs[mrec_sem_simps] >>
  PURE_TOP_CASE_TAC >> gvs[mrec_sem_simps] >>
  reverse $ PURE_TOP_CASE_TAC >> gvs[mrec_sem_simps] >>
  rw[msem_lift_monad_law] >>
  AP_TERM_TAC >>
  simp[FUN_EQ_THM] >>
  PairCases >>
  rw[] >>
  PURE_TOP_CASE_TAC >> gvs[mrec_sem_simps] >>
  PURE_TOP_CASE_TAC >> gvs[mrec_sem_simps]
QED

Theorem ltree_lift_state_lift:
  ltree_lift query_oracle s.ffi (mrec_sem (h_prog (p,s))) ≈ Ret (res,s')
  ⇒
  (ltree_lift_state query_oracle s.ffi (mrec_sem (h_prog (p,s)))) = s'.ffi
Proof
  strip_tac >> dxrule itree_wbisim_Ret_FUNPOW >>
  simp[PULL_EXISTS] >>
  MAP_EVERY qid_spec_tac [‘p’,‘s’,‘res’,‘s'’] >>
  Induct_on ‘n’ using COMPLETE_INDUCTION >>
  CONV_TAC $ RESORT_FORALL_CONV rev >>
  Cases
  >~ [‘Dec’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_dec_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          h_prog_dec_def,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau
         ] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau] >>
      rename [‘ltree_lift _ _ _ = FUNPOW Tau mm _’] >>
      last_x_assum $ qspec_then ‘mm’ mp_tac >>
      impl_tac >- simp[] >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
      disch_then $ drule_at $ Pos last >>
      qmatch_goalsub_abbrev_tac ‘h_prog (a1,a2)’ >>
      disch_then $ qspecl_then [‘a2’,‘a1’] mp_tac >>
      unabbrev_all_tac >>
      simp[] >>
      strip_tac >>
      qmatch_goalsub_abbrev_tac ‘_ >>= a1’ >>
      drule_then (qspec_then ‘a1’ mp_tac) ltree_lift_state_bind_funpow >>
      unabbrev_all_tac >>
      rw[mrec_sem_simps,ltree_lift_state_simps])
  >~ [‘If’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_cond_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          h_prog_dec_def,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau
         ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau
         ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau
         ] >>
      first_x_assum irule >>
      first_x_assum $ irule_at Any >>
      simp[])
  >~ [‘While’]
  >- (rw[ltree_lift_cases,mrec_sem_simps,
         Once mrec_sem_while_unfold,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_REWRITE_TAC[Once mrec_sem_while_unfold] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      gvs[tau_eq_funpow_tau] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          FUNPOW_Tau_bind,FUNPOW_ADD] >>
      last_assum $ drule_at Any >>
      impl_tac >- simp[] >>
      strip_tac >>
      qpat_x_assum ‘ltree_lift _ s.ffi _ = _ ’ assume_tac >>
      qmatch_goalsub_abbrev_tac ‘_ >>= a1’ >>
      drule_then (qspec_then ‘a1’ mp_tac) ltree_lift_state_bind_funpow >>
      unabbrev_all_tac >>
      strip_tac >>
      simp[mrec_sem_simps,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_state_simps,
          ltree_lift_cases,
          tau_eq_funpow_tau
         ]
      >- (last_x_assum $ irule_at $ Pos hd >>
          first_x_assum $ irule_at $ Pos last >>
          simp[]) >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_state_simps,
          ltree_lift_cases,
          tau_eq_funpow_tau,
          ret_eq_funpow_tau
         ] >>
      last_x_assum $ irule_at $ Pos hd >>
      first_x_assum $ irule_at $ Pos last >>
      simp[])
  >~ [‘ExtCall’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_ext_call_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      rpt(PURE_TOP_CASE_TAC >>
          gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
              ltree_lift_state_simps,ret_eq_funpow_tau,
              tau_eq_funpow_tau]) >>
      gvs[query_oracle_def,ELIM_UNCURRY,AllCaseEqs(),
          tau_eq_funpow_tau,ret_eq_funpow_tau
         ] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[empty_locals_defs]))
  >~ [‘ShMemLoad’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_sh_mem_load_def,nb_op_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      rpt(PURE_TOP_CASE_TAC >>
          gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
              ltree_lift_state_simps,ret_eq_funpow_tau,
              tau_eq_funpow_tau]) >>
      gvs[query_oracle_def,ELIM_UNCURRY,AllCaseEqs(),
          tau_eq_funpow_tau,ret_eq_funpow_tau
         ] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[empty_locals_defs]))
  >~ [‘ShMemStore’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_sh_mem_store_def,nb_op_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      rpt(PURE_TOP_CASE_TAC >>
          gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
              ltree_lift_state_simps,ret_eq_funpow_tau,
              tau_eq_funpow_tau]) >>
      gvs[query_oracle_def,ELIM_UNCURRY,AllCaseEqs(),
          tau_eq_funpow_tau,ret_eq_funpow_tau
         ] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[empty_locals_defs]))
  >~ [‘Call’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_call_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          tau_eq_funpow_tau] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          FUNPOW_Tau_bind] >>
      irule EQ_TRANS >>
      irule_at (Pos hd) ltree_lift_state_bind_funpow >>
      first_assum $ irule_at $ Pos hd >>
      rename [‘ltree_lift _ s.ffi _ = FUNPOW _ mm (Ret st)’] >>
      Cases_on ‘st’ >>
      last_assum $ qspec_then ‘mm’ mp_tac >>
      impl_tac >- simp[] >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
      disch_then $ drule_at $ Pos last >>
      qmatch_goalsub_abbrev_tac ‘h_prog (a1,a2)’ >>
      disch_then $ qspecl_then [‘a2’,‘a1’] mp_tac >>
      unabbrev_all_tac >>
      simp[] >>
      strip_tac >>
      gvs[] >>
      gvs[oneline h_handle_call_ret_def] >>
      rpt(IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
              tau_eq_funpow_tau,empty_locals_defs,
              set_var_def,panSemTheory.set_var_def]) >>
      qmatch_goalsub_abbrev_tac ‘_ _ a1.ffi (_ (_ (_, a2)))’ >>
      ‘a1.ffi = a2.ffi’ by(rw[Abbr ‘a1’, Abbr ‘a2’]) >>
      pop_assum SUBST_ALL_TAC >>
      first_x_assum irule >>
      first_x_assum $ irule_at $ Pos last >>
      simp[])
  >~ [‘DecCall’]
   >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_deccall_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          tau_eq_funpow_tau] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          FUNPOW_Tau_bind] >>
      irule EQ_TRANS >>
      irule_at (Pos hd) ltree_lift_state_bind_funpow >>
      first_assum $ irule_at $ Pos hd >>
      rename [‘ltree_lift _ s.ffi _ = FUNPOW _ mm (Ret st)’] >>
      Cases_on ‘st’ >>
      last_assum $ qspec_then ‘mm’ mp_tac >>
      impl_tac >- simp[] >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
      disch_then $ drule_at $ Pos last >>
      qmatch_goalsub_abbrev_tac ‘h_prog (a1,a2)’ >>
      disch_then $ qspecl_then [‘a2’,‘a1’] mp_tac >>
      unabbrev_all_tac >>
      simp[] >>
      strip_tac >>
      gvs[] >>
      gvs[oneline h_handle_deccall_ret_def] >>
      (* TODO *)
      rpt(IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
              tau_eq_funpow_tau,empty_locals_defs,
              set_var_def,panSemTheory.set_var_def]) >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau] >>
      rename [‘ltree_lift _ _ _ = FUNPOW Tau mm _’] >>
      last_x_assum $ qspec_then ‘mm’ mp_tac >>
      impl_tac >- simp[] >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
      disch_then $ drule_at $ Pos last >>
      qmatch_goalsub_abbrev_tac ‘h_prog (a1,a2)’ >>
      disch_then $ qspecl_then [‘a2’,‘a1’] mp_tac >>
      unabbrev_all_tac >>
      simp[] >>
      strip_tac >>
      qmatch_goalsub_abbrev_tac ‘_ >>= a1’ >>
      drule_then (qspec_then ‘a1’ mp_tac) ltree_lift_state_bind_funpow >>
      unabbrev_all_tac >>
      rw[mrec_sem_simps,ltree_lift_state_simps])
  >~ [‘Seq’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_seq_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      gvs[tau_eq_funpow_tau] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          FUNPOW_Tau_bind,FUNPOW_ADD] >>
      last_assum $ drule_at Any >>
      impl_tac >- simp[] >>
      strip_tac >>
      qpat_x_assum ‘ltree_lift _ s.ffi _ = _ ’ assume_tac >>
      qmatch_goalsub_abbrev_tac ‘_ >>= a1’ >>
      drule_then (qspec_then ‘a1’ mp_tac) ltree_lift_state_bind_funpow >>
      unabbrev_all_tac >>
      strip_tac >>
      simp[mrec_sem_simps,ltree_lift_state_simps] >>
      reverse IF_CASES_TAC >>
      gvs[ltree_lift_state_simps,mrec_sem_simps,ltree_lift_cases,
          ret_eq_funpow_tau,tau_eq_funpow_tau
         ] >>
      last_x_assum irule >>
      first_x_assum $ irule_at $ Pos last >>
      simp[]
     )
  >~ [‘Raise’]
  >- (pop_assum kall_tac >>
      rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_raise_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau] >>
      rpt(IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
              ltree_lift_state_simps,empty_locals_defs])) >>
  rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
     h_prog_store_def,
     h_prog_store_byte_def,
     h_prog_assign_def,
     h_prog_raise_def,
     h_prog_return_def,
     ltree_lift_state_simps,
     ret_eq_funpow_tau
    ] >>
  rpt (PURE_TOP_CASE_TAC >>
       gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
           ltree_lift_state_simps,ret_eq_funpow_tau,
           tau_eq_funpow_tau,empty_locals_defs])
QED

Theorem ltree_lift_state_lift':
  ltree_lift query_oracle (s:('a,'b)state).ffi (mrec_sem (h_prog (p,t))) ≈ Ret (res,s') ∧
  t.ffi = s.ffi  ==>
  (ltree_lift_state query_oracle s.ffi (mrec_sem (h_prog (p,t)))) = s'.ffi
Proof
  metis_tac[ltree_lift_state_lift]
QED

Theorem stree_trace_Vis:
  stree_trace f p st (Vis e k) =
  let (a,rbytes,st') = f st e in
    if p a then
      make_io_event e rbytes:::stree_trace f p st' (k a)
    else
      stree_trace f p st' (k a)
Proof
  rw[stree_trace_def] >>
  rw[Once LUNFOLD] >>
  rw[ELIM_UNCURRY]
QED

Theorem stree_trace_bind_append:
  ltree_lift f st t ≈ Ret x
  ⇒ stree_trace f p st (to_stree t >>= k) =
    LAPPEND (stree_trace f p st (to_stree t)) (stree_trace f p (ltree_lift_state f st t) (k x))
Proof
  strip_tac >> dxrule itree_wbisim_Ret_FUNPOW >>
  simp[PULL_EXISTS] >>
  MAP_EVERY qid_spec_tac [‘t’,‘st’] >>
  Induct_on ‘n’ >>
  rw[FUNPOW_SUC]
  >- (Cases_on ‘t’ >> rw[] >>
      gvs[ltree_lift_cases,to_stree_simps,itree_wbisim_neq,stree_trace_simps,
          ltree_lift_state_simps,ltree_lift_Vis_alt,ELIM_UNCURRY]) >>
  Cases_on ‘t’ >> rw[] >>
  gvs[ltree_lift_cases,to_stree_simps,itree_wbisim_neq,stree_trace_simps,
      stree_trace_Vis,ltree_lift_state_simps,ltree_lift_Vis_alt,ELIM_UNCURRY] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem stree_trace_ret_events:
  ltree_lift query_oracle st.ffi (mrec_sem (h_prog (p,st))) ≈ Ret (res,st')
  ⇒ fromList st'.ffi.io_events =
    LAPPEND (fromList st.ffi.io_events) (stree_trace query_oracle event_filter st.ffi (to_stree (mrec_sem (h_prog (p,st)))))
Proof
  strip_tac >> dxrule itree_wbisim_Ret_FUNPOW >>
  simp[PULL_EXISTS] >>
  MAP_EVERY qid_spec_tac [‘p’,‘st’,‘res’,‘st'’] >>
  Induct_on ‘n’ using COMPLETE_INDUCTION >>
  CONV_TAC $ RESORT_FORALL_CONV rev >>
  Induct
  >~ [‘Dec’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_dec_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          h_prog_dec_def,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,
          LAPPEND_NIL_2ND
         ] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law,
         to_stree_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau] >>
      rename [‘ltree_lift _ _ _ = FUNPOW Tau mm _’] >>
      last_x_assum $ qspec_then ‘mm’ mp_tac >>
      impl_tac >- simp[] >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
      disch_then $ drule_at $ Pos last >>
      qmatch_goalsub_abbrev_tac ‘h_prog (a1,a2)’ >>
      disch_then $ qspecl_then [‘a2’,‘a1’] mp_tac >>
      unabbrev_all_tac >>
      simp[] >>
      strip_tac >>
      AP_TERM_TAC >>
      CONV_TAC SYM_CONV >>
      irule EQ_TRANS >>
      irule_at (Pos hd) stree_trace_bind_append >>
      irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
      first_x_assum $ irule_at $ Pos hd >>
      simp[to_stree_simps,stree_trace_simps,mrec_sem_simps,LAPPEND_NIL_2ND]
     )
  >~ [‘If’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_cond_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          h_prog_dec_def,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,
          LAPPEND_NIL_2ND
         ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,
          LAPPEND_NIL_2ND
         ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,
          LAPPEND_NIL_2ND
         ] >>
      first_x_assum irule >>
      first_x_assum $ irule_at Any >>
      simp[])
  >~ [‘While’]
  >- (rw[ltree_lift_cases,mrec_sem_simps,
         Once mrec_sem_while_unfold,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_REWRITE_TAC[Once mrec_sem_while_unfold] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      gvs[tau_eq_funpow_tau] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law,to_stree_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          FUNPOW_Tau_bind,FUNPOW_ADD] >>
      last_assum $ drule_at Any >>
      impl_tac >- simp[] >>
      strip_tac >>
      rename1 ‘ltree_lift _ s.ffi _ = FUNPOW _ _ (Ret (ress,ss))’ >>
      qmatch_asmsub_abbrev_tac ‘ltree_lift _ a1’ >>
      subgoal ‘a1 = ss.ffi’ >> unabbrev_all_tac
      >- (irule ltree_lift_state_lift >>
          irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
          first_x_assum $ irule_at $ Pos hd) >>
      simp[] >>
      gvs[] >>
      Cases_on ‘ress’ >> gvs[ltree_lift_cases,tau_eq_funpow_tau] >>
      TRY(rename1 ‘Ret (SOME rr, _)’ >> Cases_on ‘rr’ >>
          gvs[ltree_lift_cases,tau_eq_funpow_tau]) >>
      gvs[ret_eq_funpow_tau]
      >~ [‘Ret (SOME Error, _)’]
      >- (AP_TERM_TAC >>
          CONV_TAC SYM_CONV >>
          irule EQ_TRANS >>
          irule_at (Pos hd) stree_trace_bind_append >>
          irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
          first_x_assum $ irule_at $ Pos hd >>
          simp[to_stree_simps,stree_trace_simps,mrec_sem_simps,LAPPEND_NIL_2ND]) >>
      last_x_assum $ drule_at $ Pos last >> rw[LAPPEND_ASSOC] >>
      AP_TERM_TAC >>
      CONV_TAC SYM_CONV >>
      irule EQ_TRANS >>
      irule_at (Pos hd) stree_trace_bind_append >>
      irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
      first_x_assum $ irule_at $ Pos hd >>
      simp[to_stree_simps,stree_trace_simps,mrec_sem_simps,LAPPEND_NIL_2ND])
  >~ [‘ExtCall’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_ext_call_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      rpt(PURE_TOP_CASE_TAC >>
          gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
              ltree_lift_state_simps,ret_eq_funpow_tau,
              tau_eq_funpow_tau]) >>
      gvs[query_oracle_def,ELIM_UNCURRY,AllCaseEqs(),
          tau_eq_funpow_tau,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,
          oneline event_filter_def,
          LAPPEND_NIL_2ND
         ] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[empty_locals_defs]) >>
      gvs[stree_trace_Vis,make_io_event_def,
          ffiTheory.call_FFI_def,AllCaseEqs(),
          query_oracle_def,to_stree_simps,mrec_sem_simps,stree_trace_simps,
          GSYM LAPPEND_fromList,
          oneline event_filter_def,
          LAPPEND_NIL_2ND]
     )
  >~ [‘ShMemLoad’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_sh_mem_load_def,nb_op_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      rpt(PURE_TOP_CASE_TAC >>
          gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
              ltree_lift_state_simps,ret_eq_funpow_tau,
              tau_eq_funpow_tau]) >>
      gvs[query_oracle_def,ELIM_UNCURRY,AllCaseEqs(),
          tau_eq_funpow_tau,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,
          oneline event_filter_def,
          LAPPEND_NIL_2ND
         ] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[empty_locals_defs]) >>
      gvs[stree_trace_Vis,make_io_event_def,
          ffiTheory.call_FFI_def,AllCaseEqs(),
          query_oracle_def,to_stree_simps,mrec_sem_simps,stree_trace_simps,
          GSYM LAPPEND_fromList, oneline event_filter_def, LAPPEND_NIL_2ND])
  >~ [‘ShMemStore’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_sh_mem_store_def,nb_op_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      rpt(PURE_TOP_CASE_TAC >>
          gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
              ltree_lift_state_simps,ret_eq_funpow_tau,
              tau_eq_funpow_tau]) >>
      gvs[query_oracle_def,ELIM_UNCURRY,AllCaseEqs(),
          tau_eq_funpow_tau,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,
          oneline event_filter_def,
          LAPPEND_NIL_2ND
         ] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[empty_locals_defs]) >>
      gvs[stree_trace_Vis,make_io_event_def,
          ffiTheory.call_FFI_def,AllCaseEqs(),
          query_oracle_def,to_stree_simps,mrec_sem_simps,stree_trace_simps,
          GSYM LAPPEND_fromList, oneline event_filter_def, LAPPEND_NIL_2ND])
  >~ [‘Call’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_call_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          tau_eq_funpow_tau,to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND
         ] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law,to_stree_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          FUNPOW_Tau_bind,FUNPOW_ADD] >>
      rename1 ‘ltree_lift _ s.ffi _ = FUNPOW _ _ (Ret xx)’ >>
      PairCases_on ‘xx’ >>
      qmatch_asmsub_abbrev_tac ‘ltree_lift _ a1’ >>
      subgoal ‘a1 = xx1.ffi’ >> unabbrev_all_tac
      >- (PURE_REWRITE_TAC [Once $ GSYM $ SIMP_CONV (srw_ss()) [] “(s with locals := r).ffi”] >>
          irule ltree_lift_state_lift >>
          irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
          simp[] >> metis_tac[]) >>
      simp[] >>
      gvs[] >>
      gvs[oneline h_handle_call_ret_def] >>
      CONV_TAC SYM_CONV >>
      irule EQ_TRANS >>
      irule_at (Pos hd) $ METIS_PROVE []  “x = y ⇒ f x = f y” >>
      irule_at (Pos hd) stree_trace_bind_append >>
      irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
      first_assum $ irule_at $ Pos hd >>
      simp[to_stree_simps,stree_trace_simps,mrec_sem_simps,LAPPEND_NIL_2ND] >>
      CONV_TAC SYM_CONV >>
      simp[oneline h_handle_call_ret_def] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND]
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[]) >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      simp[empty_locals_defs]
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (PURE_TOP_CASE_TAC >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
          simp[empty_locals_defs]
          >- (irule EQ_TRANS >>
              last_x_assum $ irule_at $ Pos hd >>
              irule_at Any EQ_TRANS >>
              first_x_assum $ irule_at $ Pos $ hd o tl >>
              qrefine ‘_ with locals := _’ >>
              simp[] >>
              irule_at (Pos hd) EQ_REFL >>
              simp[]) >>
          PURE_TOP_CASE_TAC >> gvs[] >> CASE_TAC
          >- (gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,to_stree_simps,
                  stree_trace_simps,LAPPEND_NIL_2ND] >>
              simp[set_var_def,panSemTheory.set_var_def] >>
              irule EQ_TRANS >>
              last_x_assum $ irule_at $ Pos hd >>
              irule_at Any EQ_TRANS >>
              first_x_assum $ irule_at $ Pos $ hd o tl >>
              simp[] >>
              qrefine ‘_ with locals := _’ >>
              simp[] >>
              irule_at (Pos hd) EQ_REFL >>
              simp[]) >>
          CASE_TAC >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,to_stree_simps,
              stree_trace_simps,LAPPEND_NIL_2ND] >>
          simp[set_var_def,panSemTheory.set_var_def] >>
          irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          simp[] >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (PURE_TOP_CASE_TAC >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
          simp[empty_locals_defs]
          >- (irule EQ_TRANS >>
              last_x_assum $ irule_at $ Pos hd >>
              irule_at Any EQ_TRANS >>
              first_x_assum $ irule_at $ Pos $ hd o tl >>
              qrefine ‘_ with locals := _’ >>
              simp[] >>
              irule_at (Pos hd) EQ_REFL >>
              simp[]) >>
          rpt(IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >> gvs[]) >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,to_stree_simps,
              stree_trace_simps,LAPPEND_NIL_2ND,mrec_sem_simps,
              tau_eq_funpow_tau
             ] >>
          simp[set_var_def,panSemTheory.set_var_def,empty_locals_defs]
          >~ [‘set_var’] (* Ret handler case*)
          >- (irule EQ_TRANS >>
              last_assum $ irule_at $ Pos hd >>
              irule_at Any EQ_TRANS >>
              first_assum $ irule_at $ Pos $ hd o tl >>
              simp[] >>
              qrefine ‘set_var _ _ (_ with locals := _)’ >>
              gvs[set_var_def,panSemTheory.set_var_def] >>
              first_assum $ irule_at $ Pos hd >>
              simp[GSYM LAPPEND_ASSOC] >>
              AP_THM_TAC >>
              AP_TERM_TAC >>
              irule EQ_TRANS >>
              last_x_assum $ irule_at $ Pos hd >>
              irule_at Any EQ_TRANS >>
              first_x_assum $ irule_at $ Pos $ hd o tl >>
              simp[] >>
              qrefine ‘_ with locals := _’ >>
              simp[] >>
              irule_at (Pos hd) EQ_REFL >>
              simp[]) >>
          irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          simp[] >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[]))
  >~ [‘DecCall’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_deccall_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,ltree_lift_state_simps,
          tau_eq_funpow_tau,to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND
         ] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law,to_stree_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          FUNPOW_Tau_bind,FUNPOW_ADD] >>
      PairCases_on ‘y’ >>
      qmatch_asmsub_abbrev_tac ‘ltree_lift _ a1’ >>
      subgoal ‘a1 = y1.ffi’ >> unabbrev_all_tac
      >- (PURE_REWRITE_TAC [Once $ GSYM $ SIMP_CONV (srw_ss()) [] “(s with locals := r).ffi”] >>
          irule ltree_lift_state_lift >>
          irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
          simp[] >> metis_tac[]) >>
      simp[] >>
      gvs[] >>
      gvs[oneline h_handle_deccall_ret_def] >>
      CONV_TAC SYM_CONV >>
      irule EQ_TRANS >>
      irule_at (Pos hd) $ METIS_PROVE []  “x = y ⇒ f x = f y” >>
      irule_at (Pos hd) stree_trace_bind_append >>
      irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
      first_assum $ irule_at $ Pos hd >>
      simp[to_stree_simps,stree_trace_simps,mrec_sem_simps,LAPPEND_NIL_2ND] >>
      CONV_TAC SYM_CONV >>
      simp[oneline h_handle_deccall_ret_def] >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND]
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[]) >>
      PURE_TOP_CASE_TAC >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,LAPPEND_NIL_2ND] >>
      simp[empty_locals_defs]
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (IF_CASES_TAC >>
          gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
              h_prog_dec_def, ret_eq_funpow_tau,
              ltree_lift_state_simps,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              to_stree_simps,stree_trace_simps,
              LAPPEND_NIL_2ND
             ] >>
           gvs[msem_lift_monad_law,ltree_lift_monad_law,
               to_stree_monad_law]
           >- (gvs[set_var_def,panSemTheory.set_var_def] >>
               simp[GSYM LAPPEND_ASSOC] >>
               drule FUNPOW_Tau_bind_thm >>
               rw[] >>
               pairarg_tac >>
               gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau] >>
               rename [‘ltree_lift _ y1.ffi _ = FUNPOW Tau mm _’] >>
               last_assum $ qspec_then ‘mm’ mp_tac >>
               impl_tac >- simp[] >>
               disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
               disch_then $ drule_at $ Pos last >>
               qmatch_goalsub_abbrev_tac ‘h_prog (a1,a2)’ >>
               disch_then $ qspecl_then [‘a2’,‘a1’] mp_tac >>
               unabbrev_all_tac >>
               simp[] >>
               strip_tac >>
               last_x_assum $ qspec_then ‘n''’ assume_tac >> fs[] >>
               first_x_assum $ qspecl_then [‘y1’,‘SOME (Return v)’,‘st with locals := r’,‘q’] assume_tac >> gvs[] >>
               AP_TERM_TAC >>
               CONV_TAC SYM_CONV >>
               irule EQ_TRANS >>
               irule_at (Pos hd) stree_trace_bind_append >>
               irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
               first_x_assum $ irule_at $ Pos hd >>
               simp[to_stree_simps,stree_trace_simps,mrec_sem_simps,LAPPEND_NIL_2ND])
           >- (irule EQ_TRANS >>
               last_x_assum $ irule_at $ Pos hd >>
               irule_at Any EQ_TRANS >>
               first_x_assum $ irule_at $ Pos $ hd o tl >>
               simp[] >>
               qrefine ‘_ with locals := _’ >>
               simp[] >>
               irule_at (Pos hd) EQ_REFL >>
               simp[]
           )
      )
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      >- (irule EQ_TRANS >>
          last_x_assum $ irule_at $ Pos hd >>
          irule_at Any EQ_TRANS >>
          first_x_assum $ irule_at $ Pos $ hd o tl >>
          qrefine ‘_ with locals := _’ >>
          simp[] >>
          irule_at (Pos hd) EQ_REFL >>
          simp[])
      )
  >~ [‘Seq’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_seq_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau,
         to_stree_simps,stree_trace_simps,
         LAPPEND_NIL_2ND
        ] >>
      gvs[tau_eq_funpow_tau] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law,
          to_stree_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          FUNPOW_Tau_bind,FUNPOW_ADD] >>
      last_assum $ drule_at Any >>
      impl_tac >- simp[] >>
      strip_tac >>
      rename1 ‘ltree_lift _ s.ffi _ = FUNPOW _ _ (Ret (_,ss))’ >>
      qmatch_asmsub_abbrev_tac ‘ltree_lift _ a1’ >>
      subgoal ‘a1 = ss.ffi’ >> unabbrev_all_tac
      >- (irule ltree_lift_state_lift >>
          irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
          first_x_assum $ irule_at $ Pos hd) >>
      simp[] >>
      reverse PURE_FULL_CASE_TAC >>
      gvs[ltree_lift_cases,mrec_sem_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau]
      >- (AP_TERM_TAC >>
          CONV_TAC SYM_CONV >>
          irule EQ_TRANS >>
          irule_at (Pos hd) stree_trace_bind_append >>
          irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
          first_x_assum $ irule_at $ Pos hd >>
          simp[to_stree_simps,stree_trace_simps,mrec_sem_simps,LAPPEND_NIL_2ND]) >>
      last_x_assum $ drule_at Any >>
      impl_tac >- simp[] >>
      disch_then SUBST_ALL_TAC >>
      rw[] >>
      simp[LAPPEND_ASSOC] >>
      AP_TERM_TAC >>
      CONV_TAC SYM_CONV >>
      irule EQ_TRANS >>
      irule_at (Pos hd) stree_trace_bind_append >>
      irule_at (Pos hd) FUNPOW_Tau_imp_wbisim >>
      first_x_assum $ irule_at $ Pos hd >>
      simp[to_stree_simps,stree_trace_simps,mrec_sem_simps,LAPPEND_NIL_2ND]) >>
  rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
     h_prog_store_def,
     h_prog_store_byte_def,
     h_prog_assign_def,
     h_prog_raise_def,
     h_prog_return_def,
     ltree_lift_state_simps,
     ret_eq_funpow_tau,
     to_stree_simps,
     stree_trace_simps,
     LAPPEND_NIL_2ND
    ] >>
  rpt (IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >>
       gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
           ltree_lift_state_simps,ret_eq_funpow_tau,
           tau_eq_funpow_tau,empty_locals_defs,
           to_stree_simps,stree_trace_simps,
           LAPPEND_NIL_2ND
           ])
QED

Theorem stree_trace_ret_events':
  ltree_lift query_oracle (s:('a,'b)state).ffi (mrec_sem (h_prog (p,st))) ≈ Ret (res,st') ∧
  st.ffi = s.ffi
  ⇒ fromList st'.ffi.io_events =
    LAPPEND (fromList st.ffi.io_events) (stree_trace query_oracle event_filter st.ffi (to_stree (mrec_sem (h_prog (p,st)))))
Proof
   metis_tac[stree_trace_ret_events]
QED

Theorem itree_semantics_beh_Seq:
  itree_semantics_beh s (Seq p1 p2) =
  case itree_semantics_beh s p1 of
    SemTerminate (NONE, s') =>
      itree_semantics_beh s' p2
  | res => res
Proof
  rw[itree_semantics_beh_def,h_prog_def,h_prog_seq_def,mrec_sem_simps,ltree_lift_cases,
      itree_wbisim_neq,ELIM_UNCURRY
     ] >>
  CONV_TAC SYM_CONV >>
  DEEP_INTRO_TAC some_intro >>
  reverse conj_tac
  >- (rw[msem_lift_monad_law,
         ltree_lift_monad_law,
         ltree_lift_nonret_bind,
         to_stree_monad_law,
         to_stree_simps,
         stree_trace_simps,
         ltree_lift_nonret_bind_stree
        ]) >>
  rw[] >>
  rename1 ‘Ret r’ >> Cases_on ‘r’ >> gvs[] >>
  drule ltree_lift_bind_left_ident >>
  qmatch_goalsub_abbrev_tac ‘_ >>= k1’ >>
  disch_then $ qspec_then ‘k1’ mp_tac >>
  unabbrev_all_tac >>
  reverse $ rw[mrec_sem_simps,ltree_lift_cases]
  >- (DEEP_INTRO_TAC some_intro >>
      reverse conj_tac
      >- (rw[] >> gvs[]) >>
      rw[] >>
      dxrule_then strip_assume_tac itree_wbisim_sym >>
      dxrule itree_wbisim_trans >>
      strip_tac >>
      first_x_assum dxrule >>
      rw[itree_wbisim_neq] >>
      PURE_CASE_TAC >> gvs[] >>
      PURE_CASE_TAC >> gvs[]) >>
  drule ltree_lift_state_lift >>
  strip_tac >>
  gvs[ltree_lift_monad_law,msem_lift_monad_law] >>
  DEEP_INTRO_TAC some_intro >>
  reverse conj_tac
  >- (rw[] >> gvs[] >>
      DEEP_INTRO_TAC some_intro >>
      conj_tac >- metis_tac[itree_wbisim_trans,itree_wbisim_sym,itree_wbisim_refl] >>
      disch_then kall_tac >>
      simp[to_stree_simps,stree_trace_simps,to_stree_monad_law] >>
      qmatch_goalsub_abbrev_tac ‘_ >>= k1’ >>
      drule_then (qspecl_then [‘event_filter’,‘k1’] assume_tac) stree_trace_bind_append >>
      simp[] >>
      drule stree_trace_ret_events >>
      simp[] >>
      disch_then kall_tac >>
      simp[LAPPEND_ASSOC,Abbr ‘k1’,mrec_sem_simps,
           to_stree_simps,stree_trace_simps]) >>
  Cases >>
  rw[] >>
  PURE_CASE_TAC >> gvs[]
  >- (DEEP_INTRO_TAC some_intro >>
      reverse conj_tac
      >- (simp[FORALL_PROD] >>
          irule_at (Pos hd) itree_wbisim_trans >>
          irule_at (Pos hd) itree_bind_resp_t_wbisim >>
          first_x_assum $ irule_at $ Pos hd >>
          simp[ltree_lift_cases,mrec_sem_simps] >>
          metis_tac[]) >>
      simp[FORALL_PROD] >>
      rw[] >>
      dxrule_then assume_tac itree_wbisim_sym >>
      dxrule itree_wbisim_trans >>
      disch_then drule >>
      strip_tac >>
      dxrule itree_wbisim_sym >>
      strip_tac >>
      dxrule_then assume_tac itree_wbisim_sym >>
      dxrule itree_wbisim_trans >>
      disch_then drule >>
      strip_tac >>
      dxrule itree_wbisim_sym >>
      strip_tac >>
      gvs[itree_wbisim_neq]) >>
  DEEP_INTRO_TAC some_intro >>
  reverse conj_tac
  >- (PURE_CASE_TAC >>
      simp[FORALL_PROD] >>
      irule_at (Pos hd) itree_wbisim_trans >>
      irule_at (Pos hd) itree_bind_resp_t_wbisim >>
      first_x_assum $ irule_at $ Pos hd >>
      simp[ltree_lift_cases,mrec_sem_simps] >>
      metis_tac[]) >>
  simp[FORALL_PROD] >>
  rw[] >>
  dxrule_then assume_tac itree_wbisim_sym >>
  dxrule itree_wbisim_trans >>
  disch_then drule >>
  strip_tac >>
  dxrule itree_wbisim_sym >>
  strip_tac >>
  dxrule_then assume_tac itree_wbisim_sym >>
  dxrule itree_wbisim_trans >>
  disch_then drule >>
  strip_tac >>
  dxrule itree_wbisim_sym >>
  strip_tac >>
  gvs[itree_wbisim_neq] >>
  PURE_CASE_TAC >> gvs[]
QED

Theorem mrec_sem_Call_simps:
  mrec_sem (h_prog (Call ty texp aexp, s)) =
  case (eval (reclock s) texp,OPT_MMAP (eval (reclock s)) aexp) of
    (SOME(ValLabel fname), SOME args) =>
      (case lookup_code s.code fname args of
         NONE => Ret (SOME Error,s)
       | SOME (c_prog,newlocals) =>
           Tau (mrec_sem (h_prog (c_prog,s with locals := newlocals)) >>=
                         mrec_sem ∘ h_handle_call_ret ty s))
  | _ => Ret (SOME Error,s)
Proof
  simp[h_prog_def,h_prog_call_def,h_handle_call_ret_def]>>
  rpt (PURE_CASE_TAC>>gvs[])>>
  simp[mrec_sem_simps,msem_lift_monad_law]
QED

Theorem itree_semantics_beh_Call:
  itree_semantics_beh s (Call ty texp aexp) =
  case (eval (reclock s) texp,OPT_MMAP (eval (reclock s)) aexp) of
    (SOME (ValLabel fname), SOME args) =>
      (case lookup_code s.code fname args of
         NONE => SemFail
       | SOME (c_prog,newlocals) =>
           (case itree_semantics_beh (s with locals := newlocals) c_prog of
              SemTerminate (SOME (Return rv),s') =>
                (case ty of
                   NONE => SemTerminate (SOME (Return rv),empty_locals s')
                 | SOME (NONE,_) => SemTerminate (NONE, s' with locals := s.locals)
                 | SOME (SOME rt,_) =>
                     if is_valid_value s.locals rt rv then
                       SemTerminate (NONE,set_var rt rv (s' with locals := s.locals))
                     else SemFail)
            | SemTerminate (SOME (Exception eid exn),s') =>
                (case ty of
                   NONE => SemTerminate (SOME (Exception eid exn),empty_locals s')
                 | SOME (_, NONE) => SemTerminate (SOME (Exception eid exn),empty_locals s')
                 | SOME (_, SOME (eid',ev,pp)) =>
                     if eid = eid' then
                       (case FLOOKUP s.eshapes eid of
                          NONE => SemFail
                        | SOME sh =>
                            if shape_of exn = sh
                               ∧ is_valid_value s.locals ev exn then
                              itree_semantics_beh (set_var ev exn (s' with locals := s.locals)) pp
                            else SemFail)
                     else SemTerminate (SOME (Exception eid exn),empty_locals s'))
            | SemTerminate (SOME Break,s') => SemFail (*SemTerminate (SOME Error,s')*)
            | SemTerminate (SOME Continue,s') => SemFail (*SemTerminate (SOME Error, s')*)
            | SemTerminate (NONE,s') => SemFail (*SemTerminate (SOME Error, s')*)
            | SemTerminate (res,s') => SemTerminate (res,empty_locals s')
            | res => res)
       | _ => SemFail)
  | _ => SemFail
Proof
  rw[itree_semantics_beh_def] >>
  rw[mrec_sem_Call_simps]>>
  CONV_TAC SYM_CONV >>
  PURE_TOP_CASE_TAC >> gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs()] >>
      pairarg_tac >> gvs[]) >>
  reverse PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs()] >>
      pairarg_tac >> gvs[]) >>
  PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
      pairarg_tac >> gvs[]) >>
  PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
      pairarg_tac >> gvs[]) >>
  PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
      pairarg_tac >> gvs[]) >>

  PURE_TOP_CASE_TAC>>gvs[]>>
  gvs[ltree_lift_cases,ltree_lift_monad_law]>>
  qmatch_goalsub_abbrev_tac ‘X >>= _’>>
  Cases_on ‘X’>>
  TRY (rename1 ‘Ret xx’>>Cases_on ‘xx’>>gvs[])
  >- (DEEP_INTRO_TAC some_intro >>fs[]>>
      TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
      simp[FORALL_PROD]>>rpt strip_tac>>
      ‘ltree_lift query_oracle (s with locals := r).ffi
       (mrec_sem (h_prog (q,s with locals := r))) ≈ Ret (q',r')’ by
        simp[Once itree_wbisim_cases]>>
      drule ltree_lift_state_lift>>
      pop_assum kall_tac>>strip_tac>>fs[]>>
      TRY (fs[Once itree_wbisim_cases]>>
           rw[]>>NO_TAC)>>
      rename1 ‘_ ≈ Ret (qq,rr)’>>
      ‘qq = q' ∧ rr = r'’ by fs[Once itree_wbisim_cases]>>
      fs[]>>

      PURE_CASE_TAC>>gvs[h_handle_call_ret_def]>> (* res *)
      simp[mrec_sem_simps,ltree_lift_cases]
      >- (simp[Once itree_wbisim_cases]>>
          DEEP_INTRO_TAC some_intro >>
          simp[FORALL_PROD,Once itree_wbisim_cases])>>
      PURE_CASE_TAC>>gvs[h_handle_call_ret_def]>> (* SOME result *)
      simp[mrec_sem_simps,ltree_lift_cases]>>
      DEEP_INTRO_TAC some_intro >>fs[FORALL_PROD]>>
      TRY (simp[Once itree_wbisim_cases]>>
           simp[Once itree_wbisim_cases]>>
           rw[]>>NO_TAC)
(* Return *)
      >- (
       PURE_CASE_TAC>>gvs[h_handle_call_ret_def]
       >- (simp[mrec_sem_simps,ltree_lift_cases]>>
           simp[Once itree_wbisim_cases]>>
           simp[Once itree_wbisim_cases])>>
       PURE_CASE_TAC>>gvs[]>>
       simp[mrec_sem_simps,ltree_lift_cases]>>
       rpt (PURE_CASE_TAC>>gvs[])>>
       simp[mrec_sem_simps,ltree_lift_cases]>>
       simp[Once itree_wbisim_cases]>>
       simp[Once itree_wbisim_cases])>>
(* Exception *)
      PURE_CASE_TAC>>gvs[]>>  (* calltyp *)
      simp[mrec_sem_simps,ltree_lift_cases]
      >- (simp[Once itree_wbisim_cases]>>
          simp[Once itree_wbisim_cases])>>
      PURE_CASE_TAC>>gvs[]>>  (* calltyp = SOME _ *)
      simp[mrec_sem_simps,ltree_lift_cases]>>
      PURE_CASE_TAC>>gvs[]>>  (* calltyp = SOME (_,?) *)
      simp[mrec_sem_simps,ltree_lift_cases]
      >- (simp[Once itree_wbisim_cases]>>
          simp[Once itree_wbisim_cases])>>
      rename1 ‘SOME (_, SOME xxx)’>>
      PairCases_on ‘xxx’>>fs[]>>
      PURE_TOP_CASE_TAC>>gvs[]>>
      simp[mrec_sem_simps,ltree_lift_cases]>>
      TRY (simp[Once itree_wbisim_cases]>>
           simp[Once itree_wbisim_cases]>>NO_TAC)>>
      PURE_TOP_CASE_TAC>>gvs[]>>
      simp[mrec_sem_simps,ltree_lift_cases]
          >- (simp[Once itree_wbisim_cases]>>
              simp[Once itree_wbisim_cases])>>
      PURE_TOP_CASE_TAC>>fs[]>>
      simp[mrec_sem_simps,ltree_lift_cases]
      >- (rw[]>>gvs[]
          >- (DEEP_INTRO_TAC some_intro >>
              simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]>>
              drule_then rev_drule wbisim_Ret_unique>>
              rw[]>>gvs[])>>
          DEEP_INTRO_TAC some_intro >>
          simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]>>
          drule itree_eq_imp_wbisim>>strip_tac>>
          ‘ltree_lift query_oracle (s with locals := r).ffi
           (mrec_sem (h_prog (q,s with locals := r))) ≈
           Ret (SOME (Exception m' v),r')’ by simp[]>>
          drule stree_trace_ret_events>>strip_tac>>fs[]>>
          simp[Once LAPPEND_ASSOC]>>
          qmatch_goalsub_abbrev_tac ‘LAPPEND X _’>>
          ‘LFINITE X’ by simp[Abbr‘X’,LFINITE_fromList]>>
          simp[LAPPEND11_FINITE1]>>
          drule (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>strip_tac>>
          simp[to_stree_simps,stree_trace_simps,to_stree_monad_law]>>
          simp[h_handle_call_ret_def,o_DEF,LAMBDA_PROD]>>
          simp[mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
          simp[set_var_defs])>>
      qmatch_goalsub_abbrev_tac ‘if X ∧ Y then _ else _’>>
      Cases_on ‘X’>>gvs[]>>
      simp[mrec_sem_simps,ltree_lift_cases]>>
      simp[Once itree_wbisim_cases]>>
      simp[Once itree_wbisim_cases])
(* Tau *)
  >- (fs[]>>
      DEEP_INTRO_TAC some_intro >>
      simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]>>
      DEEP_INTRO_TAC some_intro >>
      simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]
      >- (qmatch_asmsub_abbrev_tac ‘X = Tau u’>>
          rename1 ‘u ≈ Ret (v,w)’>>
          ‘X ≈ Ret (v,w)’ by gvs[Abbr‘X’]>>
          fs[Abbr‘X’]>>
          ‘ltree_lift query_oracle (s with locals := r).ffi (mrec_sem (h_prog (q,s with locals := r))) ≈ Ret (v,w)’ by simp[]>>
          drule ltree_lift_state_lift>>
          pop_assum kall_tac>>strip_tac>>
          gvs[]>>
          qmatch_asmsub_abbrev_tac ‘_ >>= X’>>
          ‘u >>= X ≈ (Ret (v,w) >>= X)’ by
            (irule itree_bind_resp_t_wbisim>>fs[])>>
          gvs[Abbr‘X’]>>
          qmatch_asmsub_abbrev_tac ‘_ >>= _ ≈ X’>>
          rename1 ‘_ ≈ Ret (v',w')’>>
          ‘X ≈ Ret (v',w')’ by
            (irule itree_wbisim_trans>>
             first_assum $ irule_at Any>>
             irule itree_wbisim_sym>>fs[])>>
          fs[Abbr‘X’]>>

          PURE_CASE_TAC>>gvs[]>>
          PURE_CASE_TAC>>gvs[h_handle_call_ret_def]>>
          TRY (gvs[mrec_sem_simps,ltree_lift_cases]>>
               fs[Once itree_wbisim_cases]>>NO_TAC)
          >- (PURE_CASE_TAC>>gvs[]>>
              PURE_CASE_TAC>>gvs[]>>
              TRY (gvs[mrec_sem_simps,ltree_lift_cases]>>
                   fs[Once itree_wbisim_cases]>>NO_TAC)>>
              PURE_CASE_TAC>>gvs[]>>
              PURE_CASE_TAC>>gvs[]>>
              gvs[mrec_sem_simps,ltree_lift_cases,set_var_defs]>>
              fs[Once itree_wbisim_cases])>>
          PURE_CASE_TAC>>gvs[]>>
          PURE_CASE_TAC>>gvs[]>>
          TRY (gvs[mrec_sem_simps,ltree_lift_cases]>>
               fs[Once itree_wbisim_cases]>>NO_TAC)>>
          PURE_CASE_TAC>>gvs[]>>
          PURE_CASE_TAC>>gvs[]>>
          TRY (gvs[mrec_sem_simps,ltree_lift_cases]>>
               fs[Once itree_wbisim_cases]>>NO_TAC)>>
          PURE_CASE_TAC>>gvs[]>>
          PURE_CASE_TAC>>gvs[]>>
          PURE_CASE_TAC>>gvs[]>>
          TRY (gvs[mrec_sem_simps,ltree_lift_cases]>>
               fs[Once itree_wbisim_cases]>>NO_TAC)>>
          PURE_TOP_CASE_TAC>>gvs[]>>
          gvs[mrec_sem_simps,ltree_lift_cases,set_var_defs]
          >- (DEEP_INTRO_TAC some_intro >>
              simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]>>gvs[]>>
              drule_then rev_drule wbisim_Ret_unique>>rw[])>>
          qmatch_goalsub_abbrev_tac ‘if X ∧ Y then _ else _’>>
          Cases_on ‘X’>>gvs[]>>
          simp[mrec_sem_simps,ltree_lift_cases]>>
          fs[Once itree_wbisim_cases])
      >- (qmatch_asmsub_abbrev_tac ‘Y = Tau u’>>
          rename1 ‘u ≈ Ret (v,w)’>>
          ‘Y ≈ Ret (v,w)’ by gvs[Abbr‘Y’]>>
          fs[Abbr‘Y’]>>
          ‘ltree_lift query_oracle (s with locals := r).ffi (mrec_sem (h_prog (q,s with locals := r))) ≈ Ret (v,w)’ by simp[]>>
          drule ltree_lift_state_lift>>
          pop_assum kall_tac>>strip_tac>>
          gvs[]>>
          qmatch_asmsub_abbrev_tac ‘_ >>= X’>>
          ‘u >>= X ≈ X (v,w)’ by
            (irule itree_wbisim_trans>>
             irule_at Any itree_bind_resp_t_wbisim>>
             first_assum $ irule_at Any>>
             fs[]>>irule itree_wbisim_refl)>>
          ‘∀x. (u >>= X ≈ Ret x) = (X (v,w) ≈ Ret x)’ by
            (simp[EQ_IMP_THM]>>rw[]>>
             irule itree_wbisim_trans>>
             first_assum $ irule_at Any>>fs[]>>
             irule itree_wbisim_sym>>fs[])>>fs[]>>
          pop_assum kall_tac>>
          gvs[Abbr‘X’]>>
          rpt (PURE_CASE_TAC>>gvs[h_handle_call_ret_def]>>
               fs[mrec_sem_simps,ltree_lift_cases]>>
               TRY (rfs[Once itree_wbisim_cases]>>NO_TAC))>>
          TRY (qpat_x_assum ‘_ = NONE’ mp_tac)>>
          TRY (qpat_x_assum ‘_ = SOME _’ mp_tac)>>
          DEEP_INTRO_TAC some_intro >>
          simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]
          >- (
           ‘ltree_lift query_oracle (s with locals := r).ffi (mrec_sem (h_prog (q,s with locals := r))) ≈ Ret (SOME (Exception m' v),w)’ by simp[]>>
           drule stree_trace_ret_events>>strip_tac>>fs[]>>
           simp[Once LAPPEND_ASSOC]>>
           qmatch_goalsub_abbrev_tac ‘LAPPEND X _’>>
           ‘LFINITE X’ by simp[Abbr‘X’,LFINITE_fromList]>>
           simp[LAPPEND11_FINITE1]>>
           simp[to_stree_simps,stree_trace_simps,to_stree_monad_law]>>
           drule (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>strip_tac>>
           fs[h_handle_call_ret_def]>>
           simp[mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
           simp[set_var_defs])>>
          FULL_CASE_TAC>>fs[]
          >- fs[mrec_sem_simps,ltree_lift_cases]>>
          qmatch_asmsub_abbrev_tac ‘X ⇒ Y’>>
          Cases_on ‘X’>>gvs[]>>
          fs[mrec_sem_simps,ltree_lift_cases]>>
          fs[Once itree_wbisim_cases])
      >- (Cases_on ‘u’>>gvs[Once itree_bind_thm]
          >- (gvs[Once itree_wbisim_cases,GSYM FORALL_PROD])
          >- (drule itree_wbisim_Ret_FUNPOW>>strip_tac>>
              drule FUNPOW_Tau_bind_thm>>strip_tac>>
              qpat_x_assum ‘u' = _’ assume_tac>>
              drule FUNPOW_Tau_imp_wbisim>>
              strip_tac>>gvs[GSYM FORALL_PROD])>>
          gvs[Once itree_wbisim_cases,GSYM FORALL_PROD]>>
          gvs[Once itree_wbisim_cases,GSYM FORALL_PROD])>>
      ‘LFINITE (fromList s.ffi.io_events)’ by simp[LFINITE_fromList]>>
      simp[LAPPEND11_FINITE1]>>
      simp[to_stree_simps,stree_trace_simps,to_stree_monad_law]>>
      irule (GSYM ltree_lift_nonret_bind_stree)>>
      CCONTR_TAC>>gvs[GSYM FORALL_PROD])>>
(* Vis *)
  simp[Once itree_wbisim_cases]>>
  DEEP_INTRO_TAC some_intro >>
  simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]>>
  simp[Once itree_wbisim_cases]>>
  DEEP_INTRO_TAC some_intro >>
  simp[FORALL_PROD]>>
  qmatch_goalsub_abbrev_tac ‘LAPPEND X _’>>
  ‘LFINITE X’ by simp[Abbr‘X’,LFINITE_fromList]>>
  simp[LAPPEND11_FINITE1]>>
  simp[to_stree_monad_law,to_stree_simps,stree_trace_simps]>>
  CONV_TAC SYM_CONV>>
  irule ltree_lift_nonret_bind_stree>>
  fs[]>>simp[Once itree_wbisim_cases]
QED

Theorem mrec_sem_DecCall_simps:
  mrec_sem (h_prog (DecCall rt sh texp aexp prog1, s)) =
  case (eval (reclock s) texp,OPT_MMAP (eval (reclock s)) aexp) of
    (SOME(ValLabel fname), SOME args) =>
      (case lookup_code s.code fname args of
         NONE => Ret (SOME Error,s)
       | SOME (c_prog,newlocals) =>
           Tau (mrec_sem (h_prog (c_prog,s with locals := newlocals)) >>=
                         mrec_sem ∘ h_handle_deccall_ret rt sh prog1 s))
  | _ => Ret (SOME Error,s)
Proof
  simp[h_prog_def, h_prog_deccall_def, h_handle_deccall_ret_def]>>
  rpt (PURE_CASE_TAC>>gvs[])>>
  simp[mrec_sem_simps,msem_lift_monad_law]
QED

Theorem itree_semantics_beh_DecCall:
  itree_semantics_beh s (DecCall rt sh texp aexp prog1) =
   case (eval (reclock s) texp,OPT_MMAP (eval (reclock s)) aexp) of
    (SOME (ValLabel fname), SOME args) =>
      (case lookup_code s.code fname args of
         NONE => SemFail
       | SOME (c_prog,newlocals) =>
           (case itree_semantics_beh (s with locals := newlocals) c_prog of
              SemTerminate (SOME (Return rv),s') =>
                (if shape_of rv = sh then
                   case itree_semantics_beh (set_var rt rv (s' with locals := s.locals)) prog1 of
                   | SemTerminate (rs,s'') =>
                       SemTerminate (rs,s'' with locals := res_var s''.locals (rt, FLOOKUP s.locals rt))
                   | res => res
                 else SemFail)
            | SemTerminate (SOME Break,s') => SemFail
            | SemTerminate (SOME Continue,s') => SemFail
            | SemTerminate (NONE,s') => SemFail
            | SemTerminate (res,s') => SemTerminate (res,empty_locals s')
            | res => res)
       | _ => SemFail)
  | _ => SemFail
Proof
  rw[itree_semantics_beh_def] >>
  rw[mrec_sem_DecCall_simps] >>
  CONV_TAC SYM_CONV >>
  PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases, itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD, AllCaseEqs()] >>
      pairarg_tac >> gvs[]) >>
  reverse PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
   >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs()] >>
      pairarg_tac >> gvs[]) >>
  PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
      pairarg_tac >> gvs[]) >>
  PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
      pairarg_tac >> gvs[]) >>
  PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
      pairarg_tac >> gvs[]) >>
  PURE_TOP_CASE_TAC>>gvs[]>>
  gvs[ltree_lift_cases,ltree_lift_monad_law]>>
  qmatch_goalsub_abbrev_tac ‘X >>= _’>>
  Cases_on ‘X’>>
  TRY (rename1 ‘Ret xx’>>Cases_on ‘xx’>>gvs[])
  >- (DEEP_INTRO_TAC some_intro >>fs[]>>
      TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
      simp[FORALL_PROD]>>rpt strip_tac>>
      ‘ltree_lift query_oracle (s with locals := r).ffi
       (mrec_sem (h_prog (q,s with locals := r))) ≈ Ret (q',r')’ by
        simp[Once itree_wbisim_cases]>>
      drule ltree_lift_state_lift>>
      pop_assum kall_tac>>strip_tac>>fs[]>>
      TRY (fs[Once itree_wbisim_cases]>>
           rw[]>>NO_TAC)>>
      rename1 ‘_ ≈ Ret (qq,rr)’>>
      ‘qq = q' ∧ rr = r'’ by fs[Once itree_wbisim_cases]>>
      fs[]>>
      PURE_CASE_TAC>>gvs[h_handle_deccall_ret_def]>> (* res *)
      simp[mrec_sem_simps,ltree_lift_cases]
      >- (simp[Once itree_wbisim_cases]>>
          DEEP_INTRO_TAC some_intro >>
          simp[FORALL_PROD,Once itree_wbisim_cases])>>
      PURE_CASE_TAC>>gvs[h_handle_deccall_ret_def]>> (* SOME result *)
      simp[mrec_sem_simps,ltree_lift_cases]>>
      DEEP_INTRO_TAC some_intro >>fs[FORALL_PROD]>>
      TRY (simp[Once itree_wbisim_cases]>>
           simp[Once itree_wbisim_cases]>>
           rw[]>>NO_TAC) >>
      rw[set_var_def, panSemTheory.set_var_def] >>  simp[mrec_sem_simps,ltree_lift_cases]
(* Return *)
      >- (drule ltree_lift_bind_left_ident >>
          qmatch_goalsub_abbrev_tac ‘_ >>= k1’ >>
          disch_then $ qspec_then ‘k1’ mp_tac >>
          unabbrev_all_tac >>
          rw[mrec_sem_simps,ltree_lift_cases] >>
          DEEP_INTRO_TAC some_intro >>
          reverse conj_tac
          >- (rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
              metis_tac[]) >>
          simp[FORALL_PROD]>>fs[]>>rw[]>>
          dxrule_then strip_assume_tac itree_wbisim_sym >>
          dxrule itree_wbisim_trans >>
          strip_tac >>
          first_x_assum dxrule >>
          rw[itree_wbisim_neq] >>
          PURE_CASE_TAC >> gvs[] >>
          PURE_CASE_TAC >> gvs[])
      >- (DEEP_INTRO_TAC some_intro >>
          simp[FORALL_PROD]>>fs[]>>rw[] >>
          gvs[itree_wbisim_neq])
      >- (DEEP_INTRO_TAC some_intro >>
          simp[FORALL_PROD]>>fs[]>>rw[msem_lift_monad_law,
                                      ltree_lift_monad_law,
                                      ltree_lift_nonret_bind,
                                      to_stree_monad_law,
                                      to_stree_simps,
                                      stree_trace_simps,
                                      ltree_lift_nonret_bind_stree]
          >- (drule itree_wbisim_Ret_FUNPOW >> strip_tac >>
              drule FUNPOW_Tau_bind_thm>>strip_tac>>
              qpat_x_assum ‘ltree_lift _ _ _ = FUNPOW _ _ _’ assume_tac >>
              drule FUNPOW_Tau_imp_wbisim >>
              dxrule EQ_SYM >>
              rw[] >>
              Cases_on ‘y’ >>
              PRED_ASSUM is_forall $ qspecl_then [‘q'’, ‘r''’] assume_tac >>
              gvs[Once itree_wbisim_cases]) >>
          simp[to_stree_simps, stree_trace_simps] >>
          ‘ltree_lift query_oracle (s with locals := r).ffi
           (mrec_sem (h_prog (q,s with locals := r))) ≈
           Ret (SOME (Return v),r')’ by simp[] >>
          drule stree_trace_ret_events>>strip_tac>>fs[]>>
          simp[Once LAPPEND_ASSOC]>>
          qmatch_goalsub_abbrev_tac ‘LAPPEND X _’>>
          ‘LFINITE X’ by simp[Abbr‘X’,LFINITE_fromList]>>
          simp[LAPPEND11_FINITE1]>>
          drule (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>strip_tac>>
          simp[to_stree_simps,stree_trace_simps,to_stree_monad_law]>>
          simp[h_handle_deccall_ret_def,o_DEF,LAMBDA_PROD]>>
          simp[mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
          simp[set_var_defs] >>
          AP_TERM_TAC >>
          rw[msem_lift_monad_law,
             ltree_lift_monad_law,
             ltree_lift_nonret_bind,
             to_stree_monad_law,
             to_stree_simps,
             stree_trace_simps,
             ltree_lift_nonret_bind_stree] >>
          simp[mrec_sem_simps] >>
          irule EQ_SYM >>
          irule ltree_lift_nonret_bind_stree >>
          gvs[FORALL_PROD]) >>
      DEEP_INTRO_TAC some_intro >>
      conj_tac
      >- (rw[] >> gvs[] >>
          Cases_on ‘x'’ >>
          gvs[itree_wbisim_neq]) >>
      rw[] >> gvs[] >>
      qexists_tac ‘(SOME Error, r')’ >>
      gvs[itree_wbisim_neq])
(* Tau *)
     >- (rw[]>>
         DEEP_INTRO_TAC some_intro >>
         simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]>>
         DEEP_INTRO_TAC some_intro >>
         simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]
         >- (qmatch_asmsub_abbrev_tac ‘X = Tau u’>>
             rename1 ‘u ≈ Ret (v,w)’>>
             ‘X ≈ Ret (v,w)’ by gvs[Abbr‘X’]>>
             fs[Abbr‘X’]>>
             ‘ltree_lift query_oracle (s with locals := r).ffi (mrec_sem (h_prog (q,s with locals := r))) ≈ Ret (v,w)’ by simp[]>>
             drule ltree_lift_state_lift>>
             pop_assum kall_tac>>strip_tac>>
             gvs[]>>
             qmatch_asmsub_abbrev_tac ‘_ >>= X’>>
             ‘u >>= X ≈ (Ret (v,w) >>= X)’ by
               (irule itree_bind_resp_t_wbisim>>fs[])>>
             gvs[Abbr‘X’]>>
             qmatch_asmsub_abbrev_tac ‘_ >>= _ ≈ X’>>
             rename1 ‘_ ≈ Ret (v',w')’>>
             ‘X ≈ Ret (v',w')’ by
               (irule itree_wbisim_trans>>
                first_assum $ irule_at Any>>
                irule itree_wbisim_sym>>fs[])>>
             fs[Abbr‘X’]>>
             PURE_CASE_TAC>>gvs[set_var_def, panSemTheory.set_var_def] >>
             PURE_CASE_TAC>>gvs[h_handle_deccall_ret_def, set_var_def, panSemTheory.set_var_def]>>
             TRY (gvs[mrec_sem_simps,ltree_lift_cases]>>
                  fs[Once itree_wbisim_cases]>>NO_TAC) >>
             IF_CASES_TAC >> gvs[] >>
             TRY (gvs[mrec_sem_simps,ltree_lift_cases]>>
                  fs[Once itree_wbisim_cases]>>NO_TAC) >>
             DEEP_INTRO_TAC some_intro >>
             first_x_assum $ strip_assume_tac o SRULE[mrec_sem_simps, ltree_lift_cases] >>
             conj_tac
             >-(simp[FORALL_PROD]>>fs[]>>gvs[] >>
                rw[] >>
                drule ltree_lift_bind_left_ident >>
                qmatch_asmsub_abbrev_tac ‘_ >>= k1’ >>
                disch_then $ qspec_then ‘k1’ mp_tac >>
                unabbrev_all_tac >>
                simp[mrec_sem_simps,ltree_lift_cases] >>
                qpat_x_assum ‘ltree_lift _ _ (mrec_sem ( _ >>= _ )) ≈ _’ assume_tac >>
                rw[] >>
                dxrule_then strip_assume_tac itree_wbisim_sym >>
                dxrule itree_wbisim_trans >>
                strip_tac >>
                first_x_assum dxrule >>
                rw[itree_wbisim_neq] >>
                rpt(PURE_TOP_CASE_TAC >> gvs[])) >>
             gvs[msem_lift_monad_law,
                 ltree_lift_monad_law,
                 ltree_lift_nonret_bind,
                 to_stree_monad_law,
                 to_stree_simps,
                 stree_trace_simps,
                 ltree_lift_nonret_bind_stree] >>
             drule itree_wbisim_Ret_FUNPOW >> strip_tac >>
             drule FUNPOW_Tau_bind_thm>>strip_tac>>
             qpat_x_assum ‘ltree_lift _ _ _ = FUNPOW _ _ _’ assume_tac >>
             drule FUNPOW_Tau_imp_wbisim>>
             qpat_x_assum ‘ltree_lift _ _ _ = FUNPOW _ _ _’ kall_tac >>
             rw[FORALL_PROD] >>
             Cases_on ‘y’ >>
             gvs[Once itree_wbisim_cases,GSYM FORALL_PROD])
         >- (qmatch_asmsub_abbrev_tac ‘Y = Tau u’>>
             rename1 ‘u ≈ Ret (v,w)’>>
             ‘Y ≈ Ret (v,w)’ by gvs[Abbr‘Y’]>>
             fs[Abbr‘Y’]>>
             ‘ltree_lift query_oracle (s with locals := r).ffi (mrec_sem (h_prog (q,s with locals := r))) ≈ Ret (v,w)’ by simp[]>>
             drule ltree_lift_state_lift>>
             pop_assum kall_tac>>strip_tac>>
             gvs[]>>
             qmatch_asmsub_abbrev_tac ‘_ >>= X’>>
             ‘u >>= X ≈ X (v,w)’ by
               (irule itree_wbisim_trans>>
                irule_at Any itree_bind_resp_t_wbisim>>
                first_assum $ irule_at Any>>
                fs[]>>irule itree_wbisim_refl)>>
             ‘∀x. (u >>= X ≈ Ret x) = (X (v,w) ≈ Ret x)’ by
               (simp[EQ_IMP_THM]>>rw[]>>
                irule itree_wbisim_trans>>
                first_assum $ irule_at Any>>fs[]>>
                irule itree_wbisim_sym>>fs[])>>fs[]>>
             pop_assum kall_tac>>
             gvs[Abbr‘X’]>>
             rpt (PURE_CASE_TAC>>gvs[h_handle_deccall_ret_def]>>
                  fs[mrec_sem_simps,ltree_lift_cases]>>
                  TRY (rfs[Once itree_wbisim_cases, itree_wbisim_neq]>>NO_TAC))>>
             TRY (qpat_x_assum ‘_ = NONE’ mp_tac)>>
             TRY (qpat_x_assum ‘_ = SOME _’ mp_tac)>>
             DEEP_INTRO_TAC some_intro >>
             simp[FORALL_PROD]>>fs[set_var_defs, itree_wbisim_neq]>>rw[] >>
             TRY (CCONTR_TAC >> rw[] >>
                  drule ltree_lift_bind_left_ident >>
                  qmatch_asmsub_abbrev_tac ‘h_prog _ >>= k1’ >>
                  disch_then $ qspec_then ‘k1’ mp_tac >>
                  unabbrev_all_tac >>
                  simp[mrec_sem_simps,ltree_lift_cases])
             >- (‘ltree_lift query_oracle (s with locals := r).ffi
                  (mrec_sem (h_prog (q,s with locals := r))) ≈ Ret (SOME (Return v),w)’ by simp[]>>
                 drule stree_trace_ret_events>>strip_tac>>fs[]>>
                 simp[Once LAPPEND_ASSOC]>>
                 qmatch_goalsub_abbrev_tac ‘LAPPEND X _’>>
                 ‘LFINITE X’ by simp[Abbr‘X’,LFINITE_fromList]>>
                 simp[LAPPEND11_FINITE1]>>
                 simp[to_stree_simps,stree_trace_simps,to_stree_monad_law]>>
                 drule (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>strip_tac>>
                 fs[h_handle_deccall_ret_def]>>
                 simp[mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
                 simp[set_var_defs] >>
                 AP_TERM_TAC >>
                 rw[msem_lift_monad_law,
                    ltree_lift_monad_law,
                    ltree_lift_nonret_bind,
                    to_stree_monad_law,
                    to_stree_simps,
                    stree_trace_simps,
                    ltree_lift_nonret_bind_stree] >>
                 simp[mrec_sem_simps] >>
                 irule EQ_SYM >>
                 irule ltree_lift_nonret_bind_stree >>
                 gvs[FORALL_PROD]) >>
             FULL_CASE_TAC >> gvs[]
             >- (fs[mrec_sem_simps,ltree_lift_cases] >>
                 CCONTR_TAC >> rw[] >>
                 drule ltree_lift_bind_left_ident >>
                 qmatch_asmsub_abbrev_tac ‘h_prog _ >>= k1’ >>
                 disch_then $ qspec_then ‘k1’ mp_tac >>
                 unabbrev_all_tac >>
                 simp[mrec_sem_simps,ltree_lift_cases]) >>
             fs[mrec_sem_simps,ltree_lift_cases] >>
             fs[Once itree_wbisim_cases])
         >- (Cases_on ‘u’>>gvs[Once itree_bind_thm]
             >- (gvs[Once itree_wbisim_cases,GSYM FORALL_PROD])
             >- (drule itree_wbisim_Ret_FUNPOW>>strip_tac>>
                 drule FUNPOW_Tau_bind_thm>>strip_tac>>
                 qpat_x_assum ‘u' = _’ assume_tac>>
                 drule FUNPOW_Tau_imp_wbisim>>
                 strip_tac>>gvs[GSYM FORALL_PROD])>>
             gvs[Once itree_wbisim_cases,GSYM FORALL_PROD] >>
             gvs[Once itree_wbisim_cases,GSYM FORALL_PROD]) >>
         ‘LFINITE (fromList s.ffi.io_events)’ by simp[LFINITE_fromList]>>
         simp[LAPPEND11_FINITE1]>>
         simp[to_stree_simps,stree_trace_simps,to_stree_monad_law]>>
         irule (GSYM ltree_lift_nonret_bind_stree)>>
         CCONTR_TAC>>gvs[GSYM FORALL_PROD]) >>
(* Vis *)
  simp[Once itree_wbisim_cases]>>
  DEEP_INTRO_TAC some_intro >>
  simp[FORALL_PROD]>>fs[set_var_defs]>>rw[]>>
  simp[Once itree_wbisim_cases]>>
  DEEP_INTRO_TAC some_intro >>
  simp[FORALL_PROD]>>
  qmatch_goalsub_abbrev_tac ‘LAPPEND X _’>>
  ‘LFINITE X’ by simp[Abbr‘X’,LFINITE_fromList]>>
  simp[LAPPEND11_FINITE1]>>
  simp[to_stree_monad_law,to_stree_simps,stree_trace_simps]>>
  CONV_TAC SYM_CONV>>
  irule ltree_lift_nonret_bind_stree>>
  fs[]>>simp[Once itree_wbisim_cases]
QED

Theorem itree_semantics_beh_While:
  itree_semantics_beh s (While e p) =
  case eval (reclock s) e of
    SOME(ValWord w) =>
      (if w = 0w then
         SemTerminate (NONE,s)
       else
         (case itree_semantics_beh s p of
            SemTerminate (NONE,s') => itree_semantics_beh s' (While e p)
          | SemTerminate (SOME Break, s') => SemTerminate (NONE,s')
          | SemTerminate (SOME Continue, s') => itree_semantics_beh s' (While e p)
          | res => res
         ))
  | _ => SemFail
Proof
  rw[itree_semantics_beh_def] >>
  rw[Once mrec_sem_while_unfold] >>
  CONV_TAC SYM_CONV >>
  PURE_TOP_CASE_TAC >> gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs()] >>
      pairarg_tac >> gvs[]) >>
  reverse PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs()] >>
      pairarg_tac >> gvs[]) >>
  reverse PURE_TOP_CASE_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
      pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >>
  gvs[ltree_lift_cases,itree_wbisim_neq]
  >- (DEEP_INTRO_TAC some_intro >>
      rw[EXISTS_PROD,AllCaseEqs(),ltree_lift_cases] >>
      pairarg_tac >> gvs[]) >>
  DEEP_INTRO_TAC some_intro >>
  reverse conj_tac
  >- (rw[msem_lift_monad_law,
         ltree_lift_monad_law,
         ltree_lift_nonret_bind,
         to_stree_monad_law,
         to_stree_simps,
         stree_trace_simps,
         ltree_lift_nonret_bind_stree] >>
      rename1 ‘_ >>= k’ >>
      gvs[FORALL_PROD] >>
      drule_then (qspecl_then [‘k’] mp_tac) $ SIMP_RULE (srw_ss()) [FORALL_PROD] ltree_lift_nonret_bind >>
      rw[] >>
      rw[some_def,ELIM_UNCURRY] >>
      rw[Once mrec_sem_while_unfold] >>
      simp[to_stree_simps,stree_trace_simps,
           to_stree_monad_law] >>
      simp[ltree_lift_nonret_bind_stree,FORALL_PROD]) >>
  simp[FORALL_PROD] >> rw[] >>
  PURE_CASE_TAC >> gvs[]
  >- (DEEP_INTRO_TAC some_intro >>
      simp[FORALL_PROD] >>
      rw[]
      >- (DEEP_INTRO_TAC some_intro >>
          reverse conj_tac
          >- (strip_tac >>
              spose_not_then kall_tac >>
              pop_assum mp_tac >>
              rw[FORALL_PROD,EXISTS_PROD] >>
              irule_at (Pos hd) itree_wbisim_trans >>
              simp[msem_lift_monad_law,ltree_lift_monad_law] >>
              irule_at (Pos hd) itree_bind_resp_t_wbisim >>
              first_assum $ irule_at $ Pos hd >>
              simp[ltree_lift_cases] >>
              metis_tac[ltree_lift_state_lift]) >>
          simp[FORALL_PROD] >>
          rpt strip_tac >>
          dxrule_then strip_assume_tac itree_wbisim_sym >>
          dxrule itree_wbisim_trans >>
          simp[msem_lift_monad_law,ltree_lift_monad_law] >>
          disch_then $ resolve_then Any mp_tac itree_bind_resp_t_wbisim >>
          disch_then drule >>
          simp[] >>
          strip_tac >>
          dxrule itree_wbisim_sym >>
          simp[ltree_lift_cases] >>
          pop_assum mp_tac >> drule ltree_lift_state_lift >>
          rpt strip_tac >>
          gvs[] >>
          dxrule_then strip_assume_tac itree_wbisim_sym >>
          drule itree_wbisim_trans >>
          disch_then drule >>
          rw[itree_wbisim_neq]) >>
      DEEP_INTRO_TAC some_intro >>
      reverse conj_tac
      >- (simp[FORALL_PROD] >>
          disch_then kall_tac >>
          simp[SimpR “$=”, Once mrec_sem_while_unfold,to_stree_simps,stree_trace_simps,to_stree_monad_law] >>
          qmatch_goalsub_abbrev_tac ‘_ >>= k1’ >>
          drule_then (qspecl_then [‘event_filter’, ‘k1’] assume_tac) stree_trace_bind_append >>
          simp[] >>
          drule stree_trace_ret_events >>
          simp[] >>
          disch_then kall_tac >>
          simp[LAPPEND_ASSOC,Abbr ‘k1’,mrec_sem_simps,
               to_stree_simps,stree_trace_simps] >>
          metis_tac[ltree_lift_state_lift]) >>
      simp[FORALL_PROD] >>
      rw[] >>
      spose_not_then kall_tac >>
      qpat_x_assum ‘∀x. _’ mp_tac >>
      simp[] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      dxrule_then strip_assume_tac itree_wbisim_sym >>
      dxrule itree_wbisim_trans >>
      disch_then $ resolve_then Any mp_tac itree_bind_resp_t_wbisim >>
      disch_then drule >>
      simp[ltree_lift_cases] >>
      strip_tac >>
      metis_tac[itree_wbisim_sym,ltree_lift_state_lift]) >>
  PURE_CASE_TAC >> gvs[]
  >~ [‘Ret (SOME Continue, _)’]
  >- (
      DEEP_INTRO_TAC some_intro >>
      simp[FORALL_PROD] >>
      rw[]
      >- (DEEP_INTRO_TAC some_intro >>
          reverse conj_tac
          >- (strip_tac >>
              spose_not_then kall_tac >>
              pop_assum mp_tac >>
              rw[FORALL_PROD,EXISTS_PROD] >>
              irule_at (Pos hd) itree_wbisim_trans >>
              simp[msem_lift_monad_law,ltree_lift_monad_law] >>
              irule_at (Pos hd) itree_bind_resp_t_wbisim >>
              first_assum $ irule_at $ Pos hd >>
              simp[ltree_lift_cases] >>
              metis_tac[ltree_lift_state_lift]) >>
          simp[FORALL_PROD] >>
          rpt strip_tac >>
          dxrule_then strip_assume_tac itree_wbisim_sym >>
          dxrule itree_wbisim_trans >>
          simp[msem_lift_monad_law,ltree_lift_monad_law] >>
          disch_then $ resolve_then Any mp_tac itree_bind_resp_t_wbisim >>
          disch_then drule >>
          simp[] >>
          strip_tac >>
          dxrule itree_wbisim_sym >>
          simp[ltree_lift_cases] >>
          pop_assum mp_tac >> drule ltree_lift_state_lift >>
          rpt strip_tac >>
          gvs[] >>
          dxrule_then strip_assume_tac itree_wbisim_sym >>
          drule itree_wbisim_trans >>
          disch_then drule >>
          rw[itree_wbisim_neq]) >>
      DEEP_INTRO_TAC some_intro >>
      reverse conj_tac
      >- (simp[FORALL_PROD] >>
          disch_then kall_tac >>
          simp[SimpR “$=”, Once mrec_sem_while_unfold,to_stree_simps,stree_trace_simps,to_stree_monad_law] >>
          qmatch_goalsub_abbrev_tac ‘_ >>= k1’ >>
          drule_then (qspecl_then [‘event_filter’, ‘k1’] assume_tac) stree_trace_bind_append >>
          simp[] >>
          drule stree_trace_ret_events >>
          simp[] >>
          disch_then kall_tac >>
          simp[LAPPEND_ASSOC,Abbr ‘k1’,mrec_sem_simps,
               to_stree_simps,stree_trace_simps] >>
          metis_tac[ltree_lift_state_lift]) >>
      simp[FORALL_PROD] >>
      rw[] >>
      spose_not_then kall_tac >>
      qpat_x_assum ‘∀x. _’ mp_tac >>
      simp[] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      dxrule_then strip_assume_tac itree_wbisim_sym >>
      dxrule itree_wbisim_trans >>
      disch_then $ resolve_then Any mp_tac itree_bind_resp_t_wbisim >>
      disch_then drule >>
      simp[ltree_lift_cases] >>
      strip_tac >>
      metis_tac[itree_wbisim_sym,ltree_lift_state_lift])
     >>
  DEEP_INTRO_TAC some_intro >>
  simp[FORALL_PROD] >>
  (conj_tac
   >- (rpt strip_tac >>
       dxrule_then strip_assume_tac itree_wbisim_sym >>
       dxrule itree_wbisim_trans >>
       simp[msem_lift_monad_law,ltree_lift_monad_law] >>
       disch_then $ resolve_then Any mp_tac itree_bind_resp_t_wbisim >>
       disch_then drule >>
       simp[ltree_lift_cases,itree_wbisim_neq])) >>
  irule_at (Pos hd) itree_wbisim_trans >>
  simp[msem_lift_monad_law,ltree_lift_monad_law] >>
  irule_at (Pos hd) itree_bind_resp_t_wbisim >>
  first_assum $ irule_at $ Pos hd >>
  simp[ltree_lift_cases] >>
  rw[itree_wbisim_neq]
QED

Theorem itree_semantics_beh_simps:
  (itree_semantics_beh s Skip = SemTerminate (NONE, s)) ∧
  (itree_semantics_beh s (Annot ann) = SemTerminate (NONE, s)) ∧
  (itree_semantics_beh s (Assign v src) =
   case eval (reclock s) src of
     NONE => SemFail
   | SOME val =>
       if is_valid_value s.locals v val then
         SemTerminate (NONE, s with locals := s.locals |+ (v,val))
       else SemFail
  ) ∧
  (itree_semantics_beh s (Store dst src) =
   case (eval (reclock s) dst,eval (reclock s) src) of
   | (SOME (ValWord addr),SOME value) =>
       (case mem_stores addr (flatten value) s.memaddrs s.memory of
          NONE => SemFail
        | SOME m => SemTerminate (NONE,s with memory := m))
   | _ => SemFail) ∧
  (itree_semantics_beh s (StoreByte dst src) =
   case (eval (reclock s) dst,eval (reclock s) src) of
   | (SOME (ValWord addr),SOME (ValWord w)) =>
       (case mem_store_byte s.memory s.memaddrs s.be addr (w2w w) of
          NONE => SemFail
        | SOME m => SemTerminate (NONE,s with memory := m))
   | _ => SemFail) ∧
  (itree_semantics_beh s (Return e) =
   case eval (reclock s) e of
         NONE => SemFail
       | SOME value =>
         if size_of_shape (shape_of value) ≤ 32 then
           SemTerminate (SOME (Return value),empty_locals s)
         else SemFail) ∧
  (itree_semantics_beh s (Raise eid e) =
   case (FLOOKUP s.eshapes eid,eval (reclock s) e) of
          | (SOME sh,SOME value) =>
            (if shape_of value = sh ∧ size_of_shape (shape_of value) ≤ 32 then
              SemTerminate (SOME (Exception eid value),empty_locals s)
             else SemFail)
          | _ => SemFail) ∧
  (itree_semantics_beh s Break = SemTerminate (SOME Break,s)
   ) ∧
  (itree_semantics_beh s Continue = SemTerminate (SOME Continue,s)
   ) ∧
  (itree_semantics_beh s Tick = SemTerminate (NONE,s)
   )
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
      fs [Once itree_wbisim_cases])
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
      fs [Once itree_wbisim_cases])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (rpt(PURE_CASE_TAC >> gvs[]) >>
          fs [h_prog_def,h_prog_assign_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_assign_def,
          mrec_sem_simps] >>
      rpt(PURE_CASE_TAC >> gvs[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (rpt(PURE_CASE_TAC >> gvs[]) >>
          fs [h_prog_def,h_prog_store_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_store_def,
          mrec_sem_simps] >>
      rpt(PURE_CASE_TAC >> gvs[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (rpt(PURE_CASE_TAC >> gvs[]) >>
          fs [h_prog_def,h_prog_store_byte_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_store_byte_def,
          mrec_sem_simps] >>
      rpt(PURE_CASE_TAC >> gvs[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (rpt(PURE_CASE_TAC >> gvs[]) >>
          fs [h_prog_def,h_prog_return_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases, empty_locals_def,
              panSemTheory.empty_locals_def]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_return_def,
          mrec_sem_simps] >>
      rpt(PURE_CASE_TAC >> gvs[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY, empty_locals_def,
              panSemTheory.empty_locals_def])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (pairarg_tac >> gvs[] >>
          rpt(PURE_FULL_CASE_TAC >> simp[]) >>
          fs [h_prog_def,h_prog_raise_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
          fs [Once itree_wbisim_cases, empty_locals_def,
              panSemTheory.empty_locals_def,
              ltree_lift_cases,mrec_sem_simps
             ]
         ) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_raise_def,
          mrec_sem_simps] >>
      gvs[FORALL_PROD] >>
      rpt(PURE_TOP_CASE_TAC >> simp[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY, empty_locals_def,
              panSemTheory.empty_locals_def] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
      gvs[mrec_sem_simps,ltree_lift_cases])>>
  rw [itree_semantics_beh_def]>>
  DEEP_INTRO_TAC some_intro >> rw [EXISTS_PROD]>>
  fs [itree_semantics_beh_def,
      h_prog_def,
      h_prog_dec_def] >>
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
       h_prog_while_def,
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

(* TODO: move *)
Theorem read_write_bytearray_lemma:
  ∀n addr bytes.
   good_dimindex(:α) ∧
   read_bytearray (addr:α word) n (mem_load_byte m addrs be) = SOME bytes
   ⇒ write_bytearray addr bytes m addrs be = m
Proof
  Induct >>
  rw[Once $ oneline read_bytearray_def,AllCaseEqs(),mem_load_byte_def] >>
  gvs[write_bytearray_def,mem_store_byte_def] >>
  gvs[set_byte_get_byte,good_dimindex_def]
QED

Theorem itree_semantics_corres_evaluate:
  ∀prog t r s'.
    good_dimindex (:α) ∧
    evaluate (prog:'a prog,t) = (r,s') ∧
    r ≠ SOME TimeOut ⇒
    itree_semantics_beh (unclock t) prog =
    case r of
      NONE => SemTerminate (r,unclock s')
    | SOME Error => SemFail
    | SOME TimeOut => SemTerminate (r,unclock s')
    | SOME Break => SemTerminate (r,unclock s')
    | SOME Continue => SemTerminate (r,unclock s')
    | SOME (Return v6) => SemTerminate (r,unclock s')
    | SOME (Exception v7 v8) => SemTerminate (r,unclock s')
    | SOME (FinalFFI v9) => SemTerminate (r,unclock s')
Proof
  recInduct evaluate_ind >> rw []
  >~ [‘While’]
  >- (qpat_x_assum ‘evaluate _ = _’ $ strip_assume_tac o REWRITE_RULE[Once evaluate_def] >>
      simp[Once itree_semantics_beh_While] >>
      gvs[AllCaseEqs(),panPropsTheory.eval_upd_clock_eq,PULL_EXISTS] >>
      pairarg_tac >>
      gvs[AllCaseEqs(),panPropsTheory.eval_upd_clock_eq,PULL_EXISTS] >>
      metis_tac[unclock_reclock_access])
  >~ [‘Dec’]
  >- (gvs[itree_semantics_beh_Dec,
          evaluate_def,
          panPropsTheory.eval_upd_clock_eq,
          AllCaseEqs()
         ] >>
      pairarg_tac >> gvs[] >>
      qpat_x_assum ‘_ = itree_semantics_beh _ _’ $ strip_assume_tac o GSYM >>
      gvs[])
  >~ [‘Seq’]
  >- (gvs[itree_semantics_beh_Seq,
          evaluate_def
         ] >>
      pairarg_tac >> gvs[AllCaseEqs()] >>
      metis_tac[])
  >~ [‘If’]
  >- (gvs[itree_semantics_beh_If,
          evaluate_def,
          panPropsTheory.eval_upd_clock_eq,
          AllCaseEqs()])
  >~ [‘Call’]
  >- (qpat_x_assum ‘evaluate _ = _’ $ strip_assume_tac o REWRITE_RULE[Once evaluate_def] >>
      simp[Once itree_semantics_beh_Call] >>
      gvs[AllCaseEqs(),panPropsTheory.eval_upd_clock_eq,PULL_EXISTS]>>
      gvs[panPropsTheory.opt_mmap_eval_upd_clock_eq1,empty_locals_defs,
          set_var_defs] >>
      metis_tac[unclock_reclock_access])
  >~ [‘DecCall’]
  >- (qpat_x_assum ‘evaluate _ = _’ $ strip_assume_tac o REWRITE_RULE[Once evaluate_def] >>
      simp[Once itree_semantics_beh_DecCall] >>
      gvs[AllCaseEqs(),panPropsTheory.eval_upd_clock_eq,PULL_EXISTS]>>
      gvs[panPropsTheory.opt_mmap_eval_upd_clock_eq1,empty_locals_defs,
          set_var_defs] >>
      TRY(Cases_on ‘shape’) >>
      qpat_x_assum ‘_ = itree_semantics_beh _ _’ $ strip_assume_tac o GSYM >>
      TRY(pairarg_tac >> gvs[]) >>
      metis_tac[unclock_reclock_access]
     )
  >~ [‘ExtCall’]
  >- (gvs[evaluate_def,AllCaseEqs(),
          itree_semantics_beh_def,
          h_prog_def,
          h_prog_ext_call_def,
          panPropsTheory.eval_upd_clock_eq,
          mrec_sem_simps,
          ltree_lift_cases,
          some_def,
          itree_wbisim_neq,
          EXISTS_PROD,
          ffiTheory.call_FFI_def,
          PULL_EXISTS
         ] >>
      TRY(rename1 ‘Error’ >>
          rw[ELIM_UNCURRY] >>
          metis_tac[SELECT_REFL,FST,SND,PAIR]) >>
      rw[ELIM_UNCURRY,
         itree_wbisim_tau_eqn,
         query_oracle_def,
         itree_wbisim_neq,
         ffiTheory.call_FFI_def,
         empty_locals_defs
        ] >>
      qexists ‘NONE’ >> qexists_tac ‘unclock s’ >>
      rw[]
      >- metis_tac[FST,SND,PAIR] >>
      gvs[state_component_equality,unclock_def] >>
      irule $ GSYM read_write_bytearray_lemma >>
      metis_tac[])
  >~ [‘ShMemLoad’]
  >- (Cases_on ‘op’ >>
      gvs[evaluate_def,AllCaseEqs(),
          itree_semantics_beh_def,
          h_prog_def,
          h_prog_sh_mem_load_def,
          nb_op_def,
          sh_mem_load_def,
          panPropsTheory.eval_upd_clock_eq,
          mrec_sem_simps,
          ltree_lift_cases,
          some_def,
          itree_wbisim_neq,
          EXISTS_PROD,
          ffiTheory.call_FFI_def,
          PULL_EXISTS
         ] >>
      TRY (rename1 ‘Error’ >>
           rw[ELIM_UNCURRY] >>
           metis_tac[SELECT_REFL,FST,SND,PAIR])>>
      rw[ELIM_UNCURRY,
         itree_wbisim_tau_eqn,
         query_oracle_def,
         itree_wbisim_neq,
         ffiTheory.call_FFI_def,
         empty_locals_defs,
         set_var_defs
        ]
     )
  >~ [‘ShMemStore’]
  >- (Cases_on ‘op’ >>
      Cases_on ‘r’ >>
      gvs[evaluate_def,AllCaseEqs(),
          itree_semantics_beh_def,
          h_prog_def,
          h_prog_sh_mem_store_def,
          nb_op_def,
          sh_mem_store_def,
          panPropsTheory.eval_upd_clock_eq,
          mrec_sem_simps,
          ltree_lift_cases,
          some_def,
          itree_wbisim_neq,
          EXISTS_PROD,
          ffiTheory.call_FFI_def,
          PULL_EXISTS
         ] >>
      TRY (rename1 ‘Error’ >>
           rw[ELIM_UNCURRY] >>
           metis_tac[SELECT_REFL,FST,SND,PAIR])>>
      rw[ELIM_UNCURRY,
         itree_wbisim_tau_eqn,
         query_oracle_def,
         itree_wbisim_neq,
         ffiTheory.call_FFI_def,
         empty_locals_defs,
         set_var_defs
        ]
     ) >>
  gvs[evaluate_def,itree_semantics_beh_simps,panPropsTheory.eval_upd_clock_eq,
      AllCaseEqs()] >>
  gvs[dec_clock_def, empty_locals_def, panSemTheory.empty_locals_def]
QED

Theorem ltree_lift_corres_evaluate:
  good_dimindex (:α) ∧
  evaluate (prog:'a prog,s) = (r,s') ∧
  r ≠ SOME TimeOut ∧
  r ≠ SOME Error ⇒
  ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,unclock s))) ≈ Ret (r,unclock s')
Proof
  rpt strip_tac >>
  drule_all itree_semantics_corres_evaluate >>
  rw[itree_semantics_beh_def,AllCaseEqs()] >>
  qpat_x_assum ‘$some _ = SOME _’ mp_tac >>
  DEEP_INTRO_TAC some_intro >>
  simp[FORALL_PROD] >> rw[]
QED

Theorem ltree_lift_corres_evaluate_error:
  good_dimindex (:α) ∧
  evaluate (prog:'a prog,s) = (SOME Error,s') ⇒
  ∃s''. ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,unclock s))) ≈ Ret (SOME Error,s'')
Proof
  rpt strip_tac >>
  drule_then drule itree_semantics_corres_evaluate >>
  rw[itree_semantics_beh_def,AllCaseEqs()] >>
  qpat_x_assum ‘$some _ = SOME _’ mp_tac >>
  DEEP_INTRO_TAC some_intro >>
  simp[FORALL_PROD] >> rw[] >>
  first_x_assum $ irule_at Any
QED

Theorem  nonret_trans:
  (∀p. ¬(X ≈ Ret p)) ∧
  X ≈ Y ⇒
  (∀w. ¬(Y ≈ Ret w))
Proof
  rpt strip_tac>>
  drule_then rev_drule itree_wbisim_trans>>
  rw[]
QED

Theorem ret_bind_nonret:
  X ≈ Ret p ⇒
  (∀p. ¬(X >>= Y ≈ Ret p)) = (∀w. ¬(Y p ≈ Ret w))
Proof
  rpt strip_tac>>
  rw[EQ_IMP_THM]>>strip_tac
  >- (‘X >>= Y ≈ Ret w’ by
        (irule itree_wbisim_trans>>
         irule_at Any itree_bind_resp_t_wbisim>>
         first_assum $ irule_at Any>>
         simp[Once itree_bind_thm])>>gvs[])>>
  ‘Y p ≈ Ret p'’ by
    (irule itree_wbisim_trans>>
     first_assum $ irule_at Any>>
rev_drule itree_bind_resp_t_wbisim>>
  disch_then $ qspec_then ‘Y’ assume_tac>>
     fs[Once itree_bind_thm]>>
     irule itree_wbisim_sym>>gvs[])>>gvs[]
QED

Theorem move_locals_to_ffi:
  ltree_lift query_oracle s.ffi
  (mrec_sem (h_prog (p,s with locals := r))) = FUNPOW Tau n (Ret (q,r')) ⇔
  ltree_lift query_oracle (s with locals := r).ffi
             (mrec_sem (h_prog (p,s with locals := r))) = FUNPOW Tau n (Ret (q,r'))

Proof
  rw []
QED

Theorem FUNPOW_Tau_eq_elim[simp]:
  FUNPOW Tau n t = FUNPOW Tau n t' ⇔
  t = t'
Proof
  simp[FUNPOW_eq_elim]
QED

Theorem ltree_Ret_to_evaluate:
  ∀s r s' prog:'a prog.
  good_dimindex (:α) ∧
  ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,s))) ≈ Ret (r,s') ⇒
  ∃k k'. evaluate (prog,reclock s with clock := k) = (r,reclock s' with clock := k')
         ∧ r ≠ SOME TimeOut ∧ k' ≤ k
Proof
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL] >> strip_tac >>
  ConseqConv.ONCE_CONSEQ_REWRITE_TAC ([itree_wbisim_Ret_FUNPOW],[],[]) >>
  simp[PULL_EXISTS] >>
  Induct_on ‘n’ using COMPLETE_INDUCTION >>
  ntac 3 strip_tac >> Cases >>
  TRY (rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
          ltree_lift_cases,
          ret_eq_funpow_tau,
          tau_eq_funpow_tau
         ] >>
       rw[state_component_equality]>>NO_TAC)
  >~ [‘Dec’]
  >- (rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_dec_def,
         panPropsTheory.eval_upd_clock_eq
        ] >>
      PURE_FULL_CASE_TAC >>
      gvs[h_prog_def,mrec_sem_simps,
          ltree_lift_cases,ret_eq_funpow_tau,
          tau_eq_funpow_tau,h_prog_dec_def,
          panPropsTheory.eval_upd_clock_eq,
          msem_lift_monad_law,
          ltree_lift_monad_law
         ]
      >- rw[state_component_equality] >>
      imp_res_tac FUNPOW_Tau_bind_thm >>
      gvs[] >>
      pairarg_tac >>
      gvs[] >>
      rename [‘ltree_lift _ _.ffi _ = FUNPOW Tau mm _’] >>
      last_x_assum $ qspec_then ‘mm’ mp_tac >>
      impl_tac >- simp[] >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
      disch_then $ drule_at $ Pos last >>
      qmatch_goalsub_abbrev_tac ‘h_prog (a1,a2)’ >>
      disch_then $ qspecl_then [‘a2’,‘a1’] mp_tac >>
      unabbrev_all_tac >>
      simp[] >>
      strip_tac >>
      first_x_assum $ irule_at $ Pos last >>
      gvs[FUNPOW_Tau_bind,mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau]
     )
  >~ [‘Assign’]
  >- (rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_assign_def,
         panPropsTheory.eval_upd_clock_eq
        ] >>
      rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law
             ]) >>
      rw[state_component_equality])
  >~ [‘Store’]
  >- (rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_store_def,
         panPropsTheory.eval_upd_clock_eq
        ] >>
      rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law
             ]) >>
      rw[state_component_equality])
  >~ [‘StoreByte’]
  >- (rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_store_byte_def,
         panPropsTheory.eval_upd_clock_eq
        ] >>
      rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law
             ]) >>
      rw[state_component_equality])
  >~ [‘Seq’]
  >- (rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_seq_def,
         panPropsTheory.eval_upd_clock_eq,
         msem_lift_monad_law,ltree_lift_monad_law
        ] >>
      imp_res_tac FUNPOW_Tau_bind_thm >>
      gvs[] >>
      pairarg_tac >>
      gvs[] >>
      rename [‘ltree_lift _ _.ffi _ = FUNPOW Tau mm _’] >>
      last_assum $ qspec_then ‘mm’ mp_tac >>
      impl_tac >- simp[] >>
      disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
      disch_then $ drule_at $ Pos last >>
      qmatch_goalsub_abbrev_tac ‘h_prog (a1,a2)’ >>
      disch_then $ qspecl_then [‘a2’,‘a1’] mp_tac >>
      unabbrev_all_tac >>
      simp[] >>
      strip_tac >>
      reverse PURE_FULL_CASE_TAC
      >- (gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau] >>
          first_x_assum $ irule_at $ Pos last >>
          simp[]) >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          tau_eq_funpow_tau] >>
      imp_res_tac FUNPOW_Tau_imp_wbisim >>
      imp_res_tac ltree_lift_state_lift >>
      gvs[] >>
      rename1 ‘kka ≤ kkb’ >>
      first_x_assum $ drule_at $ Pos last >>
      impl_tac >- simp[] >>
      strip_tac >>
      rename1 ‘kkc ≤ kkd’ >>
      qpat_x_assum ‘evaluate _ = (NONE,_)’ assume_tac >>
      drule_then (qspec_then ‘kkd’ mp_tac)  panPropsTheory.evaluate_add_clock_eq >>
      rw[] >>
      qexists ‘kkb + kkd’ >>
      qexists ‘kka + kkc’ >>
      simp[] >>
      rpt $ qpat_x_assum ‘evaluate _ = (NONE,_)’ kall_tac >>
      drule_then (qspec_then ‘kka’ mp_tac)  panPropsTheory.evaluate_add_clock_eq >>
      rw[])
  >~ [‘If’]
  >- (rw [Once evaluate_def] >>
      simp [panPropsTheory.eval_upd_clock_eq] >>
      Cases_on ‘eval (reclock s) e’ >> rw []
      >- (gvs [h_prog_def,h_prog_cond_def,mrec_sem_simps,
                ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      ntac 2 (reverse $ TOP_CASE_TAC
      >- (gvs [h_prog_def,h_prog_cond_def,mrec_sem_simps,ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw [])) >>
      Cases_on ‘c = 0w’ >> rw [] >>
      gvs [h_prog_def,h_prog_cond_def,mrec_sem_simps,
           ltree_lift_cases,tau_eq_funpow_tau] >>
      last_assum $ drule_at (Pos last) >> simp [])
  >~ [‘While’]
  >- (rw [Once evaluate_def] >>
      simp [panPropsTheory.eval_upd_clock_eq] >>
      Cases_on ‘eval (reclock s) e’ >> rw []
      >- (gvs [h_prog_def,h_prog_while_def,mrec_sem_simps,
               Once itree_iter_thm,ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      ntac 2 (reverse $ TOP_CASE_TAC
              >- (gvs [h_prog_def,h_prog_while_def,mrec_sem_simps,
                       Once itree_iter_thm,ltree_lift_cases] >>
                  drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
                  ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
                  ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
                  qexistsl_tac [‘k’,‘k’] >> rw [])) >>
      Cases_on ‘c = 0w’ >> rw []
      >- (gvs [h_prog_def,h_prog_while_def,mrec_sem_simps,
               Once itree_iter_thm,ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = NONE’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      qrefine ‘SUC _’ >> rw [] >>
      rw [dec_clock_def] >>
      gvs [Once mrec_sem_while_unfold,
           panPropsTheory.eval_upd_clock_eq,
           ltree_lift_cases,tau_eq_funpow_tau,
           ltree_lift_monad_law] >>
      imp_res_tac FUNPOW_Tau_bind_thm >> gvs [] >>
      Cases_on ‘y’ >>
      (* TODO: generated names *)
      last_assum $ drule_at (Pos last) >> rw [] >>
      qrefine ‘k + _’ >>
      drule_all panPropsTheory.evaluate_add_clock_eq >> simp [] >>
      Cases_on ‘q’ >> gvs []
      >- (rw [] >>
          drule_then (assume_tac o MATCH_MP ltree_lift_state_lift) FUNPOW_Tau_imp_wbisim >>
          gvs [] >>
          ntac 2 (pop_assum kall_tac) >>
          gvs [ltree_lift_cases,tau_eq_funpow_tau] >>
          last_assum $ drule_at (Pos last) >> rw [] >>
          drule_all panPropsTheory.evaluate_add_clock_eq >>
          rw [] >>
          ‘evaluate (While e p,reclock r' with clock := k' + k'') =
           (r,reclock s' with clock := k' + k'³')’ by (gvs []) >>
          qexistsl_tac [‘k''’,‘k' + k'''’] >> rw [])
      >- (rw [] >>
          FULL_CASE_TAC >> gvs []
          >- (drule_then (assume_tac o MATCH_MP ltree_lift_state_lift) FUNPOW_Tau_imp_wbisim >>
              gvs [ltree_lift_cases] >>
              ntac 3 (pop_assum kall_tac) >>
              drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
              ‘r = SOME Error ∧ s' = r'’ by (gvs [itree_wbisim_neq]) >>
              qexistsl_tac [‘0’,‘k'’] >> rw [])
          >- (drule_then (assume_tac o MATCH_MP ltree_lift_state_lift) FUNPOW_Tau_imp_wbisim >>
              gvs [ltree_lift_cases] >>
              ntac 3 (pop_assum kall_tac) >>
              drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
              ‘r = NONE ∧ s' = r'’ by (gvs [itree_wbisim_neq]) >>
              qexistsl_tac [‘0’,‘k'’] >> rw [])
          >- (drule_then (assume_tac o MATCH_MP ltree_lift_state_lift) FUNPOW_Tau_imp_wbisim >>
              gvs [ltree_lift_cases,tau_eq_funpow_tau] >>
              ntac 3 (pop_assum kall_tac) >>
              last_assum $ drule_at (Pos last) >> rw [] >>
              drule_all panPropsTheory.evaluate_add_clock_eq >> rw [] >>
              ‘evaluate (While e p,reclock r' with clock := k' + k'') =
               (r,reclock s' with clock := k' + k'³')’ by (gvs []) >>
              qexistsl_tac [‘k''’,‘k' + k'''’] >> rw [])
          >- (drule_then (assume_tac o MATCH_MP ltree_lift_state_lift) FUNPOW_Tau_imp_wbisim >>
              gvs [ltree_lift_cases] >>
              ntac 3 (pop_assum kall_tac) >>
              drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
              ‘r = SOME (Return v) ∧ s' = r'’ by (gvs [itree_wbisim_neq]) >>
              qexistsl_tac [‘0’,‘k'’] >> rw [])
          >- (drule_then (assume_tac o MATCH_MP ltree_lift_state_lift) FUNPOW_Tau_imp_wbisim >>
              gvs [ltree_lift_cases] >>
              ntac 3 (pop_assum kall_tac) >>
              drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
              ‘r = SOME (Exception m v) ∧ s' = r'’ by (gvs [itree_wbisim_neq]) >>
              qexistsl_tac [‘0’,‘k'’] >> rw [])
          >- (drule_then (assume_tac o MATCH_MP ltree_lift_state_lift) FUNPOW_Tau_imp_wbisim >>
              gvs [ltree_lift_cases] >>
              ntac 3 (pop_assum kall_tac) >>
              drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
              ‘r = SOME (FinalFFI f) ∧ s' = r'’ by (gvs [itree_wbisim_neq]) >>
              qexistsl_tac [‘0’,‘k'’] >> rw [])))
  >~ [‘Call’]
  >- (rw [Once evaluate_def] >>
      simp [panPropsTheory.eval_upd_clock_eq] >>
      Cases_on ‘eval (reclock s) e’ >> rw []
      >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      reverse $ TOP_CASE_TAC >> rw []
      >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      TOP_CASE_TAC >> rw []
      >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      simp [panPropsTheory.opt_mmap_eval_upd_clock_eq1] >>
      Cases_on ‘OPT_MMAP (eval (reclock s)) l’ >> rw []
      >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      Cases_on ‘lookup_code s.code m x’ >> rw []
      >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      TOP_CASE_TAC >>
      qrefine ‘SUC _’ >> simp [dec_clock_def] >>
      gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
           ltree_lift_cases,tau_eq_funpow_tau,msem_lift_monad_law,
           ltree_lift_monad_law] >>
      imp_res_tac FUNPOW_Tau_bind_thm >>
      Cases_on ‘y’ >> gvs [] >>
      pop_assum kall_tac >>
      ‘ltree_lift query_oracle (s with locals := r').ffi
       (mrec_sem (h_prog (q,s with locals := r'))) =
       FUNPOW Tau n'' (Ret (q',r''))’ by (gvs [Once move_locals_to_ffi]) >>
      last_assum $ drule_at (Pos last) >> rw [] >>
      drule panPropsTheory.evaluate_add_clock_eq >> simp [] >>
      disch_tac >>
      qrefine ‘k + _’ >> rw [] >>
      Cases_on ‘q'’ >> rw []
      >- (gvs [FUNPOW_Tau_bind,
               h_handle_call_ret_def,
               mrec_sem_simps,ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs [] >>
          qexistsl_tac [‘0’,‘k'’] >> rw []) >>
      TOP_CASE_TAC >> rw [] >>
      gvs [FUNPOW_Tau_bind,
           h_handle_call_ret_def,
           mrec_sem_simps,ltree_lift_cases]
      >- (drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs [] >>
          qexistsl_tac [‘0’,‘k'’] >>
          simp [empty_locals_defs] >>
          gvs [FUNPOW_Tau_bind,h_handle_call_ret_def,mrec_sem_simps,
               ltree_lift_cases] >>
          ‘r = SOME Error ∧ s' = empty_locals r''’
            by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                gvs []) >>
          rw [empty_locals_defs])
      >- (drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs [] >>
          qexistsl_tac [‘0’,‘k'’] >>
          simp [empty_locals_defs] >>
          gvs [FUNPOW_Tau_bind,h_handle_call_ret_def,mrec_sem_simps,
               ltree_lift_cases])
      >- (drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs [] >>
          qexistsl_tac [‘0’,‘k'’] >>
          simp [empty_locals_defs] >>
          gvs [FUNPOW_Tau_bind,h_handle_call_ret_def,mrec_sem_simps,
               ltree_lift_cases])
      >- (Cases_on ‘o'’ >> rw []
          >- (gvs [FUNPOW_Tau_bind,h_handle_call_ret_def,
                   mrec_sem_simps,ltree_lift_cases] >>
              ‘r = SOME (Return v) ∧ s' = empty_locals r''’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >>
              rw [empty_locals_defs]) >>
          FULL_CASE_TAC >> rw [] >>
          Cases_on ‘is_valid_value s.locals rt v’ >> Cases_on ‘q'’>> rw []
          >- (gvs [FUNPOW_Tau_bind,h_handle_call_ret_def,
                   mrec_sem_simps,ltree_lift_cases] >>
              ‘r = NONE ∧ s' = r'' with locals := s.locals’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >>
              rw [set_var_defs])
          >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
                   ltree_lift_cases] >>
              Cases_on ‘is_valid_value s.locals x' v’ >> gvs[h_prog_def,h_prog_call_def,mrec_sem_simps,
                                                             ltree_lift_cases]
              >- (‘r = NONE ∧ s' = set_var x' v (r'' with locals := s.locals)’
                    by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                        gvs []) >>
                  qexistsl_tac [‘0’,‘k'’] >>
                  rw [set_var_defs]) >>
              ‘r = SOME Error ∧ s' = r''’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >>
              rw [set_var_defs])
          >- (gvs [FUNPOW_Tau_bind,h_handle_call_ret_def,
                   mrec_sem_simps,ltree_lift_cases] >>
              ‘r = NONE ∧ s' = r'' with locals := s.locals’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >>
              rw [set_var_defs]) >>
          gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
               ltree_lift_cases] >>
          Cases_on ‘is_valid_value s.locals x' v’ >> gvs[h_prog_def,h_prog_call_def,mrec_sem_simps,
                                                         ltree_lift_cases]
          >- (‘r = NONE ∧ s' = set_var x' v (r'' with locals := s.locals)’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >>
              rw [set_var_defs]) >>
          ‘r = SOME Error ∧ s' = r''’
            by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >>
              rw [set_var_defs])
      >- (Cases_on ‘o'’ >> rw []
          >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
                   ltree_lift_cases] >>
              ‘r = SOME (Exception m' v) ∧ s' = empty_locals r''’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >> rw [empty_locals_defs]) >>
          ntac 2 (FULL_CASE_TAC >> rw [])
          >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
                   ltree_lift_cases] >>
              ‘r = SOME (Exception m' v) ∧ s' = empty_locals r''’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >>
              rw [empty_locals_defs]) >>
          ntac 4 (FULL_CASE_TAC >> rw [])
          >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
                   ltree_lift_cases] >>
              ‘r = SOME Error ∧ s' = r''’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >> rw [])
          >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
                   ltree_lift_cases] >>
              ‘r = SOME (Exception m' v) ∧ s' = empty_locals r''’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >>
              rw [empty_locals_defs])
          >- (Cases_on ‘shape_of v = x' ∧ is_valid_value s.locals q'' v’ >> rw []
              >- (gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
                       ltree_lift_cases,FUNPOW_SUC,set_var_defs] >>
                  qpat_x_assum ‘ltree_lift query_oracle s.ffi
                                (mrec_sem (h_prog (q,s with locals := r'))) =
                                FUNPOW Tau n'' (Ret (SOME (Exception m' v),r''))’ assume_tac >>
                  drule_at_then (Pos last) assume_tac FUNPOW_Tau_imp_wbisim >>
                  ‘ltree_lift query_oracle (s with locals := r').ffi
                   (mrec_sem (h_prog (q,s with locals := r'))) ≈
                   Ret (SOME (Exception m' v),r'')’ by (gvs [Once move_locals_to_ffi]) >>
                  drule_all_then assume_tac ltree_lift_state_lift >>
                  gvs [FUNPOW_ADD] >>
                  gvs [tau_eq_funpow_tau] >>
                  ‘ltree_lift query_oracle (r'' with locals := s.locals |+ (q'',v)).ffi
                   (mrec_sem (h_prog (r'⁴',r'' with locals := s.locals |+ (q'',v)))) =
                   FUNPOW Tau n' (Ret (r,s'))’ by (gvs []) >>
                  last_assum $ drule_at (Pos last) >> rw [] >>
                  drule_then assume_tac panPropsTheory.evaluate_add_clock_eq >> gvs [] >>
                  qexistsl_tac [‘k''’,‘k' + k'''’] >> rw []) >>
              gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
                   ltree_lift_cases,FUNPOW_SUC,set_var_defs] >>
              ‘r = SOME Error ∧ s' = r''’
                by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                    gvs []) >>
              qexistsl_tac [‘0’,‘k'’] >> rw []) >>
          gvs [h_prog_def,h_prog_call_def,mrec_sem_simps,
               ltree_lift_cases,FUNPOW_SUC,set_var_defs] >>
          ‘r = SOME (Exception m' v) ∧ s' = empty_locals r''’
            by (drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs []) >>
          qexistsl_tac [‘0’,‘k'’] >> rw [empty_locals_defs]) >>
      ‘r = SOME (FinalFFI f) ∧ s' = empty_locals r''’
        by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
            gvs []) >>
      qexistsl_tac [‘0’,‘k'’] >> rw [empty_locals_defs])
  >~ [‘DecCall’]
  >- (rw [Once evaluate_def] >>
      simp [panPropsTheory.eval_upd_clock_eq] >>
      Cases_on ‘eval (reclock s) e’ >> rw []
      >- (gvs [h_prog_def,h_prog_deccall_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      reverse $ TOP_CASE_TAC >> rw []
      >- (gvs [h_prog_def,h_prog_deccall_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      TOP_CASE_TAC >> rw []
      >- (gvs [h_prog_def,h_prog_deccall_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      simp [panPropsTheory.opt_mmap_eval_upd_clock_eq1] >>
      Cases_on ‘OPT_MMAP (eval (reclock s)) l’ >> rw []
      >- (gvs [h_prog_def,h_prog_deccall_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      Cases_on ‘lookup_code s.code m' x’ >> rw []
      >- (gvs [h_prog_def,h_prog_deccall_def,mrec_sem_simps,
               ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_imp_wbisim >>
          ‘r = SOME Error’ by (gvs [itree_wbisim_neq]) >>
          ‘s = s'’ by (gvs [itree_wbisim_neq]) >>
          qexistsl_tac [‘k’,‘k’] >> rw []) >>
      TOP_CASE_TAC >>
      qrefine ‘SUC _’ >> simp [dec_clock_def] >>
      gvs [h_prog_def,h_prog_deccall_def,mrec_sem_simps,
           ltree_lift_cases,tau_eq_funpow_tau,msem_lift_monad_law,
           ltree_lift_monad_law] >>
      imp_res_tac FUNPOW_Tau_bind_thm >>
      Cases_on ‘y’ >> gvs [] >>
      pop_assum kall_tac >>
      ‘ltree_lift query_oracle (s with locals := r').ffi
       (mrec_sem (h_prog (q,s with locals := r'))) =
       FUNPOW Tau n'' (Ret (q',r''))’ by (gvs [Once move_locals_to_ffi]) >>
      last_assum $ drule_at (Pos last) >> rw [] >>
      drule panPropsTheory.evaluate_add_clock_eq >> simp [] >>
      disch_tac >>
      qrefine ‘k + _’ >> rw [] >>
      Cases_on ‘q'’ >> rw []
      >- (gvs [FUNPOW_Tau_bind,
               h_handle_deccall_ret_def,
               mrec_sem_simps,ltree_lift_cases] >>
          drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs [] >>
          qexistsl_tac [‘0’,‘k'’] >> rw []) >>
      TOP_CASE_TAC >> rw [] >>
      gvs [FUNPOW_Tau_bind,
           h_handle_deccall_ret_def,
           mrec_sem_simps,ltree_lift_cases]
      >- (drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs [] >>
          qexistsl_tac [‘0’,‘k'’] >>
          simp [empty_locals_defs] >>
          gvs [FUNPOW_Tau_bind,h_handle_deccall_ret_def,mrec_sem_simps,
               ltree_lift_cases] >>
          ‘r = SOME Error ∧ s' = empty_locals r''’
            by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                gvs []) >>
          rw [empty_locals_defs])
      >- (drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs [] >>
          qexistsl_tac [‘0’,‘k'’] >>
          simp [empty_locals_defs] >>
          gvs [FUNPOW_Tau_bind,h_handle_deccall_ret_def,mrec_sem_simps,
               ltree_lift_cases])
      >- (drule_then assume_tac FUNPOW_Tau_Ret_eq >> gvs [] >>
          qexistsl_tac [‘0’,‘k'’] >>
          simp [empty_locals_defs] >>
          gvs [FUNPOW_Tau_bind,h_handle_deccall_ret_def,mrec_sem_simps,
               ltree_lift_cases])
      >- (PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,h_prog_dec_def,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law,
              set_var_defs,
              FUNPOW_ADD]
          >- (imp_res_tac FUNPOW_Tau_bind_thm >>
              gvs[] >>
              pairarg_tac >>
              gvs[mrec_sem_simps, ltree_lift_cases] >>
              dxrule FUNPOW_Tau_imp_wbisim >>
              rw[itree_wbisim_neq] >>
              qpat_x_assum ‘ltree _ s.ffi _ = FUNPOW Tau _ _ ’ $ assume_tac >>
              dxrule FUNPOW_Tau_imp_wbisim >>
              rw[] >>
              ‘ltree_lift query_oracle (s with locals := r').ffi
               (mrec_sem (h_prog (q,s with locals := r'))) ≈
               Ret (SOME (Return v),r'')’ by simp[] >>
              dxrule ltree_lift_state_lift >>
              rw[] >> gvs[] >>
              ‘ltree_lift query_oracle (r'' with locals := s.locals |+ (m,v)).ffi
               (mrec_sem (h_prog (p,r'' with locals := s.locals |+ (m,v)))) =
               FUNPOW Tau n''' (Ret (r,s''))’ by simp[] >>
              last_x_assum $ qspec_then ‘n'''’ mp_tac >>
              impl_tac >- simp[] >>
              disch_then $ resolve_then (Pos hd) mp_tac EQ_TRANS >>
              disch_then $ drule_at $ Pos last >>
              disch_then $ qspecl_then [‘r'' with locals := s.locals |+ (m,v)’,‘p’] mp_tac >>
              simp[] >>
              strip_tac >>
              qexistsl_tac [‘k''’, ‘k''' + k'’] >>
              drule panPropsTheory.evaluate_add_clock_eq >>
              disch_then $ qspec_then ‘k'’ assume_tac >>
              gvs[]) >>
             rw[state_component_equality])
      >- (‘r = SOME (Exception m'' v) ∧ s' = empty_locals r''’
            by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
                gvs []) >>
          qexistsl_tac [‘0’,‘k'’] >>
          rw [empty_locals_defs]) >>
      ‘r = SOME (FinalFFI f) ∧ s' = empty_locals r''’
        by (drule_then assume_tac FUNPOW_Tau_Ret_eq >>
            gvs []) >>
      qexistsl_tac [‘0’,‘k'’] >>
      rw [empty_locals_defs])
  >~ [‘ExtCall’]
  >- (PRED_ASSUM is_forall kall_tac >>
      rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_ext_call_def,
         panPropsTheory.eval_upd_clock_eq
        ] >>
      rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law,
              ffiTheory.call_FFI_def,
              query_oracle_def,empty_locals_defs
             ]) >>
      rw[state_component_equality] >>
      metis_tac[read_write_bytearray_lemma])
  >~ [‘Raise’]
  >- (PRED_ASSUM is_forall kall_tac >>
      rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_raise_def,
         panPropsTheory.eval_upd_clock_eq
        ] >>
      rpt $ qexists ‘0’ >>
      rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law
             ]) >>
      rw[state_component_equality,empty_locals_defs])
  >~ [‘Return’]
  >- (PRED_ASSUM is_forall kall_tac >>
      rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_return_def,
         panPropsTheory.eval_upd_clock_eq
        ] >>
      rpt $ qexists ‘0’ >>
      rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law
             ]) >>
      rw[state_component_equality,empty_locals_defs])
  >~ [‘ShMemLoad’]
  >- (PRED_ASSUM is_forall kall_tac >>
      rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_sh_mem_load_def,
         panPropsTheory.eval_upd_clock_eq,
         oneline nb_op_def,
         oneline sh_mem_load_def
        ] >>
      rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law,
              ffiTheory.call_FFI_def,
              query_oracle_def,empty_locals_defs,
              set_var_def, panSemTheory.set_var_def
             ]) >>
      rw[state_component_equality])
  >~ [‘ShMemStore’]
  >- (PRED_ASSUM is_forall kall_tac >>
      rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,ret_eq_funpow_tau,
         tau_eq_funpow_tau,h_prog_sh_mem_store_def,
         panPropsTheory.eval_upd_clock_eq,
         oneline nb_op_def,
         oneline sh_mem_store_def
        ] >>
      rpt(IF_CASES_TAC ORELSE PURE_FULL_CASE_TAC >>
          gvs[h_prog_def,mrec_sem_simps,
              ltree_lift_cases,ret_eq_funpow_tau,
              tau_eq_funpow_tau,
              panPropsTheory.eval_upd_clock_eq,
              msem_lift_monad_law,
              ltree_lift_monad_law,
              ffiTheory.call_FFI_def,
              query_oracle_def,empty_locals_defs,
              set_var_def, panSemTheory.set_var_def
             ]) >>
      rw[state_component_equality])
  >~ [‘Tick’]
  >- (rw[Once evaluate_def,h_prog_def,mrec_sem_simps,
         ltree_lift_cases,
         ret_eq_funpow_tau,
         tau_eq_funpow_tau
        ] >>
      qrefine ‘SUC _’ >>
      rw[state_component_equality,dec_clock_def])
QED

Theorem ltree_Ret_to_evaluate':
    good_dimindex (:α) ∧
    ltree_lift query_oracle (t:('a,'b)state).ffi (mrec_sem (h_prog (prog,s))) ≈
               Ret (r,s')
    ∧ (s:('a,'b)bstate).ffi = t.ffi ⇒
    ∃k k'. evaluate (prog,reclock s with clock := k) = (r,reclock s' with clock := k')
           ∧ r ≠ SOME TimeOut ∧ k' ≤ k
Proof
  rpt strip_tac>>
  drule ltree_Ret_to_evaluate>>
  disch_then $ qspecl_then [‘s’,‘r’,‘s'’,‘prog’] assume_tac>>
  gvs[]>>metis_tac[]
QED

Theorem evaluate_stree_trace_LPREFIX:
  evaluate (prog:'a prog,reclock s with clock := k) = (SOME TimeOut,s') ∧
  (∀p. ¬(ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,s))) ≈ Ret p)) ∧
  good_dimindex (:α) ⇒
  LPREFIX
  (fromList s'.ffi.io_events)
  (LAPPEND (fromList s.ffi.io_events)
           (stree_trace query_oracle event_filter s.ffi
                        (to_stree (mrec_sem (h_prog (prog,s))))))
Proof
  strip_tac>>
  qabbrev_tac ‘x=reclock s with clock :=k’>>
  ‘s.ffi = x.ffi’ by simp[Abbr‘x’]>>fs[]>>
  Cases_on ‘evaluate(prog,x)’>>fs[]>>
  ‘s = unclock x’ by simp[Abbr‘x’]>>gvs[]>>
  qhdtm_x_assum ‘Abbrev’ kall_tac>>fs[]>>
  rpt (pop_assum mp_tac)>>
  MAP_EVERY qid_spec_tac [‘s’,‘k’,‘r’,‘q’,‘x’, ‘prog’]>>
  recInduct evaluate_ind>>rw[]>>fs[Once evaluate_def]>>
  rpt (pairarg_tac>>gvs[])>>gvs[]>>
  TRY (drule panPropsTheory.evaluate_io_events_mono>>strip_tac)>>
  fs[LPREFIX_APPEND]>> (* why APPEND?? *)
  TRY (simp[GSYM LAPPEND_fromList]>>
       simp[Once LAPPEND_ASSOC]>>
       simp[LFINITE_fromList, LAPPEND11_FINITE1]>>
       gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])>>NO_TAC)
  >- (* Dec *)
   (gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])>>
    fs[h_prog_def,h_prog_dec_def,mrec_sem_simps,ltree_lift_cases,
       msem_lift_monad_law,to_stree_simps,stree_trace_simps,to_stree_monad_law,
       panPropsTheory.eval_upd_clock_eq,ltree_lift_monad_law]>>
    qmatch_asmsub_abbrev_tac ‘¬(X >>= Y ≈ _)’>>
    Cases_on ‘∃w. X ≈ Ret w’>>fs[]
    >- (fs[Abbr‘X’]>>
        drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
        Cases_on ‘w’>>fs[Abbr‘Y’]>>
        fs[mrec_sem_simps,ltree_lift_cases]>>
        fs[Once itree_wbisim_cases])>>
    fs[Abbr‘X’]>>
    drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
    strip_tac>>fs[]>>metis_tac[])
  (* ShMemLoad *)
   >>~- ([‘ShMemLoad’],
         gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])>>
         fs[h_prog_def,h_prog_sh_mem_load_def,mrec_sem_simps,ltree_lift_cases,
            to_stree_simps,stree_trace_simps,ltree_lift_monad_law,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1,set_var_defs,
         panPropsTheory.eval_upd_clock_eq,to_stree_monad_law]>>
         Cases_on ‘op’>>fs[nb_op_def,sh_mem_load_def]>>
         rpt (FULL_CASE_TAC>>gvs[]))
   (* ShMemStore *)
   >>~- ([‘ShMemStore’],
         gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])>>
         fs[h_prog_def,h_prog_sh_mem_store_def,mrec_sem_simps,ltree_lift_cases,
            to_stree_simps,stree_trace_simps,ltree_lift_monad_law,
            panPropsTheory.opt_mmap_eval_upd_clock_eq1,set_var_defs,
            panPropsTheory.eval_upd_clock_eq,to_stree_monad_law]>>
         Cases_on ‘op’>>fs[nb_op_def,sh_mem_store_def]>>
         rpt (FULL_CASE_TAC>>gvs[]))
  >- (* Seq *)
   (gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])
    >- (drule_then drule ltree_lift_corres_evaluate>>strip_tac>>fs[]>>
        fs[h_prog_def,h_prog_seq_def,mrec_sem_simps,ltree_lift_cases,
           msem_lift_monad_law,to_stree_simps,stree_trace_simps,
           to_stree_monad_law,
           panPropsTheory.eval_upd_clock_eq,ltree_lift_monad_law]>>
        imp_res_tac ltree_lift_state_lift'>>fs[]>>
        drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
        imp_res_tac stree_trace_ret_events'>>gvs[]>>
        imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>
        fs[mrec_sem_simps,ltree_lift_cases,to_stree_simps,
           stree_trace_simps]>>
        gvs[Once LAPPEND_ASSOC]>>
        metis_tac[])>>
    fs[h_prog_def,h_prog_seq_def,mrec_sem_simps,ltree_lift_cases,
       to_stree_simps,stree_trace_simps,panPropsTheory.eval_upd_clock_eq]>>
    fs[msem_lift_monad_law,ltree_lift_monad_law,to_stree_monad_law]>>
    qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
    Cases_on ‘∃w. X ≈ Ret w’
    >- (fs[Abbr‘X’]>>Cases_on ‘w’>>
        drule_then drule ltree_Ret_to_evaluate'>>gvs[]>>strip_tac>>
        qspecl_then [‘c1’,‘s’,‘k-s.clock’] assume_tac(panPropsTheory.evaluate_add_clock_io_events_mono)>>
        ‘s.clock < k’ by
          (CCONTR_TAC>>fs[NOT_LESS]>>
           drule panPropsTheory.evaluate_add_clock_eq>>
           disch_then $ qspec_then ‘s.clock-k’ assume_tac>>gvs[]>>
           ‘s with clock := s.clock = s’ by
             simp[state_component_equality]>>fs[])>>
        gvs[]>>
        imp_res_tac stree_trace_ret_events'>>gvs[]>>
        drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
        fs[Abbr‘Y’]>>
        imp_res_tac (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
        imp_res_tac ltree_lift_state_lift'>>fs[]>>
        imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>gvs[]>>
        gvs[IS_PREFIX_APPEND]>>
        fs[GSYM LAPPEND_fromList]>>
        fs[Once LAPPEND_ASSOC]>>
        fs[LFINITE_fromList, LAPPEND11_FINITE1]>>
        qpat_x_assum ‘LAPPEND _ _ = _’ $ assume_tac o GSYM >> fs[]>>
        fs[Once LAPPEND_ASSOC]>>metis_tac[])>>
    fs[Abbr‘X’]>>
    imp_res_tac (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
    fs[]>>metis_tac[])
  >- (* If *)
   (gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])>>
    fs[h_prog_def,h_prog_cond_def,ltree_lift_cases,stree_trace_simps,
       panPropsTheory.eval_upd_clock_eq,mrec_sem_simps,to_stree_simps]>>
    FULL_CASE_TAC>>gvs[]>>metis_tac[])
  >- (* While *)
   (qpat_x_assum ‘_ = (SOME TimeOut,_)’ mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]
    >- (strip_tac>>gvs[empty_locals_defs]>>metis_tac[])>>
    CASE_TAC>>gvs[]
    (* res = NONE *)
    >- (strip_tac>>
        first_x_assum $ qspec_then ‘r’ mp_tac>>gvs[]>>
        qpat_x_assum ‘_ = (NONE,_)’ assume_tac>>
        drule_then drule ltree_lift_corres_evaluate>>strip_tac>>gvs[]>>
        ‘∀x. (dec_clock x).ffi = x.ffi’ by simp[dec_clock_def]>>fs[]>>
        imp_res_tac ltree_lift_state_lift'>>gvs[]>>
        impl_tac >-
         (last_x_assum mp_tac>>
          simp[Once mrec_sem_while_unfold]>>
          simp[mrec_sem_simps,ltree_lift_cases,
               to_stree_simps,panPropsTheory.eval_upd_clock_eq,
               stree_trace_simps,ltree_lift_monad_law,to_stree_monad_law]>>
          strip_tac>>
          drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
          gvs[mrec_sem_simps,ltree_lift_cases,
              stree_trace_simps,ltree_lift_monad_law,to_stree_monad_law])>>
        impl_tac >-
         (qpat_x_assum ‘_ = (SOME _,_)’ mp_tac>>simp[Once evaluate_def])>>
        strip_tac>>
        simp[Once mrec_sem_while_unfold,mrec_sem_simps,ltree_lift_cases,
             to_stree_simps,panPropsTheory.eval_upd_clock_eq,
             stree_trace_simps,ltree_lift_monad_law,to_stree_monad_law]>>
        imp_res_tac stree_trace_ret_events'>>gvs[]>>
        imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>gvs[]>>
        fs[mrec_sem_simps,ltree_lift_cases,to_stree_simps,
           stree_trace_simps]>>
        fs[Once LAPPEND_ASSOC]>>
        metis_tac[])>>
    (* res = SOME x *)
    CASE_TAC>>gvs[]>>strip_tac>>gvs[]>>
    ‘∀x. (dec_clock x).ffi = x.ffi’ by simp[dec_clock_def]>>fs[]
    >- (fs[Once mrec_sem_while_unfold,mrec_sem_simps,ltree_lift_cases,
           to_stree_simps,stree_trace_simps,panPropsTheory.eval_upd_clock_eq,
           ltree_lift_monad_law,to_stree_monad_law]>>
        qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
        Cases_on ‘∃p. X ≈ Ret p’
        >-
         (fs[Abbr‘X’]>>
          Cases_on ‘p’>>rename1 ‘Ret (q,r')’>>
          imp_res_tac ltree_lift_state_lift'>>fs[]>>
         qspecl_then [‘dec_clock s’,‘r'’,‘unclock (dec_clock s)’,‘q’,‘c’] assume_tac(GEN_ALL ltree_Ret_to_evaluate')>>
         gvs[]>>
         qspecl_then [‘c’,‘dec_clock s’,‘k-(dec_clock s).clock’] assume_tac(panPropsTheory.evaluate_add_clock_io_events_mono)>>
         ‘(dec_clock s).clock < k’ by
           (CCONTR_TAC>>fs[NOT_LESS]>>
            drule panPropsTheory.evaluate_add_clock_eq>>
            disch_then $ qspec_then ‘(dec_clock s).clock-k’ assume_tac>>
            gvs[]>>
            ‘(dec_clock s with clock := (dec_clock s).clock) = dec_clock s’
              by simp[state_component_equality]>>fs[])>>
          gvs[]>>
          drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
          fs[Abbr‘Y’]>>Cases_on ‘q’>>
          gvs[mrec_sem_simps,ltree_lift_cases]>>
          imp_res_tac stree_trace_ret_events'>>gvs[]>>
          pop_assum $ assume_tac o GSYM>>
          imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>gvs[]>>
          gvs[to_stree_simps,stree_trace_simps]>>
          simp[GSYM LAPPEND_ASSOC]>>
          fs[IS_PREFIX_APPEND]>>
          simp[GSYM LAPPEND_fromList]>>
          simp[LAPPEND_ASSOC]>>metis_tac[])>>
        fs[Abbr‘X’]>>
        drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
        strip_tac>>gvs[]>>metis_tac[])>>
    last_x_assum $ qspec_then ‘r’ mp_tac>>gvs[]>>
    qpat_x_assum ‘_ = (SOME Continue,_)’ assume_tac>>
    drule_then drule ltree_lift_corres_evaluate>>strip_tac>>gvs[]>>
    imp_res_tac ltree_lift_state_lift'>>gvs[]>>
    impl_tac >-
     (last_x_assum mp_tac>>
      simp[Once mrec_sem_while_unfold]>>
      simp[mrec_sem_simps,ltree_lift_cases,
           to_stree_simps,panPropsTheory.eval_upd_clock_eq,
           stree_trace_simps,ltree_lift_monad_law,to_stree_monad_law]>>
      strip_tac>>
      drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
      gvs[mrec_sem_simps,ltree_lift_cases,
          stree_trace_simps,ltree_lift_monad_law,to_stree_monad_law])>>
    impl_tac >-
     (qpat_x_assum ‘_ = (SOME TimeOut,_)’ mp_tac>>simp[Once evaluate_def])>>
    strip_tac>>
    simp[Once mrec_sem_while_unfold,mrec_sem_simps,ltree_lift_cases,
         to_stree_simps,panPropsTheory.eval_upd_clock_eq,
         stree_trace_simps,ltree_lift_monad_law,to_stree_monad_law]>>
    imp_res_tac stree_trace_ret_events'>>gvs[]>>
    imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>gvs[]>>
    fs[mrec_sem_simps,ltree_lift_cases,to_stree_simps,
       stree_trace_simps]>>
    fs[Once LAPPEND_ASSOC]>>
    metis_tac[])
  >~[‘Tick’]
  >- (gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])>>
      fs[h_prog_def,empty_locals_defs,mrec_sem_simps,to_stree_simps,
         stree_trace_simps]>>metis_tac[])
  >~ [‘Call’]
  >- (gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])
      >- (fs[empty_locals_defs]>>metis_tac[])
      >- (fs[Once mrec_sem_Call_simps,
             panPropsTheory.eval_upd_clock_eq,
             panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
          fs[to_stree_simps,stree_trace_simps,ltree_lift_cases,
             ltree_lift_monad_law,to_stree_monad_law]>>
          ‘(dec_clock s).ffi = s.ffi’ by simp[dec_clock_def]>>fs[]>>
          qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
          Cases_on ‘∃p. X ≈ Ret p’
          >-(fs[Abbr‘X’]>>Cases_on ‘p’>>rename1 ‘Ret (q,r')’>>
             imp_res_tac ltree_lift_state_lift'>>fs[]>>
             drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
             Cases_on ‘q’>>gvs[Abbr‘Y’]>>
             gvs[mrec_sem_simps,ltree_lift_cases,h_handle_call_ret_def]>>
             TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
             rename1 ‘Ret (SOME xx,r')’>>Cases_on ‘xx’>>
             gvs[mrec_sem_simps,ltree_lift_cases,h_handle_call_ret_def]>>
             TRY (fs[Once itree_wbisim_cases]>>NO_TAC)
             (* Return *)
             >- (rpt (FULL_CASE_TAC>>
                      gvs[mrec_sem_simps,ltree_lift_cases])>>
                 fs[Once itree_wbisim_cases])>>
             (* Exception *)
             rpt (FULL_CASE_TAC>>
                  gvs[mrec_sem_simps,ltree_lift_cases])>>
             TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
             gvs[set_var_defs]>>
             imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>gvs[]>>
             qspecl_then [‘dec_clock s’,‘r'’,‘unclock (dec_clock s) with locals := newlocals’,
                          ‘SOME (Exception m v)’,‘prog’] assume_tac(GEN_ALL ltree_Ret_to_evaluate')>>
             gvs[]>>
             qspecl_then [‘prog’,‘dec_clock s with locals := newlocals’,
                          ‘k-(dec_clock s).clock’] assume_tac(panPropsTheory.evaluate_add_clock_io_events_mono)>>
             ‘(dec_clock s).clock < k’ by
               (CCONTR_TAC>>fs[NOT_LESS]>>
                drule panPropsTheory.evaluate_add_clock_eq>>
                disch_then $ qspec_then ‘(dec_clock s).clock-k’ assume_tac>>
                gvs[]>>
                ‘(dec_clock s with clock := (dec_clock s).clock) = dec_clock s’
                  by simp[state_component_equality]>>fs[])>>
             gvs[h_handle_call_ret_def]>>
             gvs[mrec_sem_simps,ltree_lift_cases,set_var_defs,
                 to_stree_simps,stree_trace_simps]>>
             drule panPropsTheory.evaluate_io_events_mono>>strip_tac>>fs[]>>
             gvs[IS_PREFIX_APPEND,empty_locals_defs]>>
             imp_res_tac stree_trace_ret_events'>>gvs[]>>
             qpat_assum ‘_ ++ _ = _ ++ _’ $ assume_tac o GSYM>>fs[]>>
             fs[GSYM LAPPEND_fromList]>>
             fs[Once (GSYM LAPPEND_ASSOC)]>>
             qpat_x_assum ‘LAPPEND _ _ = LAPPEND _ _’ $ assume_tac o GSYM >> fs[]>>
             fs[Once LAPPEND_ASSOC]>>metis_tac[])>>
          gvs[Abbr‘X’]>>
          drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
          strip_tac>>gvs[empty_locals_defs]>>metis_tac[])>>
      (* RetCall *)
      fs[Once mrec_sem_Call_simps,set_var_defs,
         panPropsTheory.eval_upd_clock_eq,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
      fs[to_stree_simps,stree_trace_simps,ltree_lift_cases,
         ltree_lift_monad_law,to_stree_monad_law]>>
      ‘(dec_clock s).ffi = s.ffi’ by simp[dec_clock_def]>>fs[]>>
      drule_then rev_drule ltree_lift_corres_evaluate>>strip_tac>>gvs[]>>
      imp_res_tac ltree_lift_state_lift'>>gvs[]>>
      imp_res_tac stree_trace_ret_events'>>gvs[]>>
      imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>gvs[]>>
      drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
      fs[to_stree_simps,stree_trace_simps,ltree_lift_cases,
         ltree_lift_monad_law,to_stree_monad_law]>>
      gvs[h_handle_call_ret_def]>>
      gvs[mrec_sem_simps,ltree_lift_cases,set_var_defs,
          to_stree_simps,stree_trace_simps]>>
      fs[Once LAPPEND_ASSOC]>>metis_tac[]) >>
(* DecCall*)
  gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])
  >- (fs[empty_locals_defs]>>metis_tac[])
  >- (fs[Once mrec_sem_DecCall_simps,
         panPropsTheory.eval_upd_clock_eq,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
      fs[to_stree_simps,stree_trace_simps,ltree_lift_cases,
         ltree_lift_monad_law,to_stree_monad_law]>>
      ‘(dec_clock s).ffi = s.ffi’ by simp[dec_clock_def]>>fs[]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃p. X ≈ Ret p’
      >-(fs[Abbr‘X’]>>Cases_on ‘p’>>rename1 ‘Ret (q,r')’>>
         imp_res_tac ltree_lift_state_lift'>>fs[]>>
         drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
         Cases_on ‘q’>>gvs[Abbr‘Y’]>>
         gvs[mrec_sem_simps,ltree_lift_cases,h_handle_deccall_ret_def]>>
         TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
         rename1 ‘Ret (SOME xx,r')’>>Cases_on ‘xx’>>
         gvs[mrec_sem_simps,ltree_lift_cases,h_handle_deccall_ret_def]>>
         TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
         (* Return *)
         rpt (FULL_CASE_TAC>>
              gvs[mrec_sem_simps,ltree_lift_cases])>>
         TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
         gvs[set_var_defs]>>
         imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>gvs[]>>
         qspecl_then [‘dec_clock s’,‘r'’,‘unclock (dec_clock s) with locals := newlocals’,
                      ‘SOME (Return v)’,‘prog’] assume_tac(GEN_ALL ltree_Ret_to_evaluate')>>
         gvs[]>>
         qspecl_then [‘prog’,‘dec_clock s with locals := newlocals’,
                      ‘k-(dec_clock s).clock’] assume_tac(panPropsTheory.evaluate_add_clock_io_events_mono)>>
         ‘(dec_clock s).clock < k’ by
           (CCONTR_TAC>>fs[NOT_LESS]>>
            drule panPropsTheory.evaluate_add_clock_eq>>
            disch_then $ qspec_then ‘(dec_clock s).clock-k’ assume_tac>>
            gvs[]>>
            ‘(dec_clock s with clock := (dec_clock s).clock) = dec_clock s’
              by simp[state_component_equality]>>fs[])>>
         gvs[h_handle_deccall_ret_def]>>
         gvs[mrec_sem_simps,ltree_lift_cases,set_var_defs,
             to_stree_simps,stree_trace_simps]>>
         drule panPropsTheory.evaluate_io_events_mono>>strip_tac>>fs[]>>
         gvs[IS_PREFIX_APPEND,empty_locals_defs]>>
         imp_res_tac stree_trace_ret_events'>>gvs[]>>
         qpat_assum ‘_ ++ _ = _ ++ _’ $ assume_tac o GSYM>>fs[]>>
         fs[GSYM LAPPEND_fromList]>>
         fs[Once (GSYM LAPPEND_ASSOC)]>>
         qpat_x_assum ‘LAPPEND _ _ = LAPPEND _ _’ $ assume_tac o GSYM >> fs[]>>
         fs[Once LAPPEND_ASSOC]>>metis_tac[])>>
      gvs[Abbr‘X’]>>
      drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
      strip_tac>>gvs[empty_locals_defs]>>metis_tac[])>>
  (* prog1 Return *)
  fs[Once mrec_sem_DecCall_simps,set_var_defs,
     panPropsTheory.eval_upd_clock_eq,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  fs[to_stree_simps,stree_trace_simps,ltree_lift_cases,
     ltree_lift_monad_law,to_stree_monad_law]>>
  ‘(dec_clock s).ffi = s.ffi’ by simp[dec_clock_def]>>fs[]>>
  drule_then rev_drule ltree_lift_corres_evaluate>>strip_tac>>gvs[]>>
  imp_res_tac ltree_lift_state_lift'>>gvs[]>>
  imp_res_tac stree_trace_ret_events'>>gvs[]>>
  imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>gvs[]>>
  drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
  fs[to_stree_simps,stree_trace_simps,ltree_lift_cases,
     ltree_lift_monad_law,to_stree_monad_law]>>
  gvs[h_handle_deccall_ret_def]>>
  gvs[mrec_sem_simps,ltree_lift_cases,set_var_defs,
      to_stree_simps,stree_trace_simps]>>
  Cases_on ‘∀x. ¬(ltree_lift query_oracle st.ffi
            (mrec_sem (h_prog (prog1,unclock st with locals := s.locals |+ (rt,retv)))) ≈ Ret x)’
  >- (rw[msem_lift_monad_law,
         ltree_lift_monad_law,
         ltree_lift_nonret_bind,
         to_stree_monad_law,
         to_stree_simps,
         stree_trace_simps,
         ltree_lift_nonret_bind_stree] >>
      fs[Once LAPPEND_ASSOC] >>
      metis_tac[]) >>
  gvs[mrec_sem_simps,
      msem_lift_monad_law,
      ltree_lift_monad_law,
      ltree_lift_nonret_bind,
      to_stree_monad_law,
      to_stree_simps,
      stree_trace_simps,
      ltree_lift_nonret_bind_stree] >>
  drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
  Cases_on ‘x’ >>
  gvs[mrec_sem_simps,ltree_lift_cases,set_var_defs,
      to_stree_simps,stree_trace_simps]>>
  fs[Once itree_wbisim_cases]
QED

Theorem nonret_imp_timeout:
  ∀s r s' prog:'a prog k.
    good_dimindex (:α) ∧
    (∀p. ¬(ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,s))) ≈ Ret p)) ⇒
    ∃s'. evaluate (prog,reclock s with clock := k) = (SOME TimeOut,s')
Proof
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  Cases_on ‘evaluate (prog,reclock s with clock := k)’ >>
  rename1 ‘_ = (res,st)’ >>
  Cases_on ‘res = SOME Error’ >> gvs[]
  >-  (imp_res_tac ltree_lift_corres_evaluate_error >>
       gvs[]) >>
  imp_res_tac ltree_lift_corres_evaluate >>
  gvs[]
QED

Theorem nonret_imp_timeout':
  good_dimindex (:α) ∧
    (∀p. ¬(ltree_lift query_oracle (t:('a,'b)state).ffi (mrec_sem (h_prog (prog,s))) ≈ Ret p)) ∧ t.ffi = s.ffi ⇒
    ∃s'. evaluate (prog:'a prog,reclock s with clock := k) = (SOME TimeOut,s')
Proof
  strip_tac>>
  irule nonret_imp_timeout>>
  gvs[]
QED

Theorem nonret_imp_spin:
  ∀f st t.
    (∀p. ¬(ltree_lift f st t ≈ Ret p)) ⇒
    ltree_lift f st t = spin
Proof
  rpt strip_tac >>
  CONV_TAC SYM_CONV >>
  rw[Once itree_bisimulation] >>
  qexists ‘CURRY {(spin, ltree_lift f st t) | (∀p. ¬(ltree_lift f st t ≈ Ret p))}’ >>
  conj_tac >- (rw[EXISTS_PROD] >> metis_tac[]) >>
  pop_assum kall_tac >>
  rw[] >>
  gvs[UNCURRY_eq_pair]
  >- (qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin])
  >- (rename1 ‘ltree_lift f st t’ >>
      Cases_on ‘t’ >>
      gvs[ltree_lift_cases,itree_wbisim_neq]
      >- (qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin] >> metis_tac[])
      >- (Cases_on ‘a’ >> gvs[ltree_lift_cases,UNCURRY_eq_pair,PULL_EXISTS] >>
          pairarg_tac >>
          gvs[] >>
          qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin] >>
          metis_tac[]))
  >- (qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin])
QED

(** divergence **)

(* move *)
Definition lnil_def:
 lnil = LUNFOLD (λu. SOME ((),[||])) ()
End

(* move *)
Theorem lnil:
  [||]:::lnil = lnil
Proof
  simp[lnil_def]>>
  simp[SimpR“$=”,Once LUNFOLD]
QED

Theorem mrec_sem_spin:
  mrec_sem spin = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY {(mrec_sem spin, Tau spin)}’>>
  simp[]>>
  conj_tac >- (irule spin)>>
  once_rewrite_tac[spin]>>simp[mrec_sem_simps]>>
  irule_at (Pos last) spin>>
  simp[Once spin,mrec_sem_simps]
QED

Theorem ltree_lift_spin:
  ltree_lift f st spin = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY {(Tau (ltree_lift f st spin),Tau spin)}’>>
  simp[spin]>>
  simp[Once spin,ltree_lift_cases]
QED

Theorem to_stree_spin:
  to_stree spin = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY {(Tau (to_stree spin),Tau spin)}’>>
  simp[spin]>>
  simp[Once spin,to_stree_simps]
QED

Theorem stree_trace_spin_LNIL:
  stree_trace q p st spin = LNIL
Proof
  fs[stree_trace_def]>>
  qpat_abbrev_tac ‘X=LUNFOLD _’>>
  ‘every ($= [||]) (X (st,spin))’
    by (irule every_coind>>
        qexists ‘{X (st, spin); X (st, Tau spin)}’>>rw[Abbr‘X’]>>
        TRY (fs[Once LUNFOLD,Once spin]>>NO_TAC)>>
        disj1_tac>>
        pop_assum mp_tac>>
        simp[Once LUNFOLD,Once spin])>>
  simp[Once LFLATTEN]
QED

Theorem ltree_lift_FUNPOW_wbisim:
  ltree_lift q st (FUNPOW Tau n t) ≈ ltree_lift q st t
Proof
  MAP_EVERY qid_spec_tac [‘t’,‘n’]>>
  Induct_on ‘n’>>rw[]
  >- irule itree_wbisim_refl>>
  simp[FUNPOW_SUC,ltree_lift_cases]
QED

Theorem not_less_opt_lemma:
  (∀k. ¬less_opt
       n (SOME
          (LENGTH
           (SND (evaluate (prog:'a prog,reclock s with clock := k))).ffi.
           io_events))) ⇒
  ∃k'. (∀k. k' ≤ k ⇒
            LENGTH
            (SND (evaluate (prog,reclock s with clock := k))).ffi.
            io_events =
            LENGTH
            (SND (evaluate (prog,reclock s with clock := k'))).ffi.
            io_events)
Proof
  strip_tac>>
  fs[less_opt_def,NOT_LESS]>>
  qabbrev_tac ‘f = (λx. LENGTH (SND (evaluate (prog, reclock s with clock := x))).ffi.io_events)’>>
  fs[]>>
  ‘∀k k'. k ≤ k' ⇒ f k ≤ f k'’
    by (fs[Abbr‘f’]>>
        rpt strip_tac>>
        drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
        assume_tac (Q.SPECL [‘prog:'a prog’,‘reclock s with clock := k’,‘p’]
                     panPropsTheory.evaluate_add_clock_io_events_mono)>>
        fs[IS_PREFIX_APPEND])>>
  ‘∃k. ∀k'. k ≤ k' ⇒ f k' ≤  f k’ by
    (CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
     last_x_assum mp_tac>>fs[NOT_LESS_EQUAL]>>
     Cases_on ‘n < f k’>>fs[NOT_LESS]>- metis_tac[]>>
     drule LESS_EQUAL_ADD>>strip_tac>>
     gvs[]>>
     pop_assum mp_tac>>
     qid_spec_tac ‘p’>>
     Induct>>rw[]
     >- (first_x_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
         qexists ‘k'’>>rw[])>>
     fs[PULL_FORALL]>>
     first_x_assum $ qspec_then ‘k'’ assume_tac>>fs[]>>
     simp[GSYM ADD_SUC,GSYM LESS_EQ_IFF_LESS_SUC]>>
     irule_at Any LESS_LESS_EQ_TRANS>>
     irule_at Any (iffRL LESS_MONO_EQ)>>
     first_assum $ irule_at Any>>
     simp[LESS_EQ_IFF_LESS_SUC]>>
     metis_tac[])>>
  qexists ‘k’>>rw[]>>
  metis_tac[LESS_EQUAL_ANTISYM]
QED

(* move *)
Theorem evaluate_min_clock:
  evaluate (prog,s) = (q,r) ∧ q ≠ SOME TimeOut ⇒
  ∃k. evaluate (prog,s with clock := k) = (q,r with clock := 0)
Proof
  qabbrev_tac ‘x = r with clock := 0’>>
  ‘r = x with clock := x.clock + r.clock’
    by simp[state_component_equality,Abbr‘x’]>>
  pop_assum (fn h => rewrite_tac[Once h])>>strip_tac>>
  drule_all panPropsTheory.evaluate_clock_sub>>
  strip_tac>>fs[]>>metis_tac[]
QED

Theorem mrec_Ret_const_ffi:
  mrec_sem (h_prog (prog,s)) = FUNPOW Tau n (Ret (q,r)) ⇒ r.ffi = s.ffi
Proof
  map_every qid_spec_tac [‘q’,‘r’,‘s’,‘prog’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]
  >- (rpt (pop_assum mp_tac)>>
      map_every qid_spec_tac [‘q’,‘r’,‘s’,‘prog’]>>
      Induct>>rw[]>>
      TRY (fs[h_prog_def,mrec_sem_simps,
              h_prog_dec_def,
              h_prog_return_def,
              h_prog_raise_def,
              h_prog_call_def,
              h_prog_deccall_def,
              h_prog_ext_call_def,
              h_prog_cond_def,
              h_prog_seq_def,
              h_prog_store_def,
              h_prog_store_byte_def,
              h_prog_assign_def,
              empty_locals_defs,
              panPropsTheory.eval_upd_clock_eq,
              panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
           rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
           fs[bstate_component_equality]>>NO_TAC)
      >- (fs[Once mrec_sem_while_unfold,mrec_sem_simps,
             panPropsTheory.eval_upd_clock_eq]>>
          rpt (FULL_CASE_TAC>>fs[mrec_sem_simps]))>>
      TRY (Cases_on ‘m’)>>
      fs[h_prog_def,h_prog_sh_mem_load_def,
         h_prog_sh_mem_store_def, nb_op_def,
         mrec_sem_simps]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps]))>>
  rename1 ‘SUC n’>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘q’,‘r’,‘s’,‘prog’]>>
  Induct>>rw[]>>
  TRY (fs[h_prog_def,mrec_sem_simps,
          h_prog_dec_def,
          h_prog_return_def,
          h_prog_raise_def,
          h_prog_call_def,
          h_prog_cond_def,
          h_prog_seq_def,
          h_prog_store_def,
          h_prog_store_byte_def,
          h_prog_assign_def,
          panPropsTheory.eval_upd_clock_eq]>>
       rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>NO_TAC)
  (* Dec *)
  >- (fs[h_prog_def,h_prog_dec_def,mrec_sem_simps,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      fs[msem_lift_monad_law]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          Cases_on ‘t’>>
          fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
          fs[ELIM_UNCURRY,mrec_sem_simps]>>
          rename1 ‘FUNPOW _ _ (Ret x')’>>Cases_on ‘x'’>>
          drule FUNPOW_Tau_Ret_eq>>strip_tac>>gvs[]>>
          irule EQ_TRANS>>
          first_x_assum $ irule_at Any>>
          first_assum $ irule_at Any>>gvs[])>>
      imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ,Once spin])
  (* Seq *)
  >- (fs[h_prog_def,h_prog_seq_def,mrec_sem_simps]>>
      fs[msem_lift_monad_law]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          Cases_on ‘t’>>
          fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
          fs[ELIM_UNCURRY,mrec_sem_simps]>>
          rename1 ‘FUNPOW _ _ (Ret x)’>>Cases_on ‘x’>>fs[]>>
          FULL_CASE_TAC>>fs[mrec_sem_simps]>>
          fs[GSYM FUNPOW]
          >- (‘SUC n' ≤ n’ by
                (CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
                 qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                 rfs[FUNPOW_min_cancel,Tau_INJ]>>
                 Cases_on ‘SUC n' - n’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ]>>
              irule EQ_TRANS>>
              first_assum $ irule_at (Pos last)>>
              first_x_assum $ irule_at (Pos last)>>
              first_assum $ irule_at Any>>
              first_assum $ irule_at Any>>gvs[])>>
          imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[]>>
          first_x_assum irule>>
          first_x_assum $ irule_at Any>>simp[])>>
      imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ,Once spin])
  (* If *)
  >- (fs[h_prog_def,h_prog_cond_def,mrec_sem_simps,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      first_x_assum irule>>
      first_x_assum $ irule_at Any>>simp[])
  (* While *)
  >- (fs[Once mrec_sem_while_unfold,mrec_sem_simps,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      fs[msem_lift_monad_law]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          Cases_on ‘t’>>
          fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
          fs[ELIM_UNCURRY,mrec_sem_simps]>>
          rename1 ‘Ret x’>>Cases_on ‘x’>>fs[]>>
          rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
          fs[GSYM FUNPOW]>>
          TRY (imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[]>>
               first_x_assum irule>>
               first_assum $ irule_at Any>>gvs[]>>NO_TAC)>>
          ‘SUC n' ≤ n’ by
            (CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
             qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
             rfs[FUNPOW_min_cancel,Tau_INJ]>>
             Cases_on ‘SUC n' - n’>>fs[FUNPOW_SUC])>>
          fs[FUNPOW_min_cancel,Tau_INJ]>>
          irule EQ_TRANS>>
          first_assum $ irule_at (Pos last)>>
          first_x_assum $ irule_at (Pos last)>>
          first_assum $ irule_at Any>>
          first_assum $ irule_at Any>>gvs[])>>
      imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ,Once spin])
  (* Call *)
  >- (fs[Once mrec_sem_Call_simps,mrec_sem_simps,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      fs[msem_lift_monad_law]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          Cases_on ‘t’>>
          fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
          fs[ELIM_UNCURRY,mrec_sem_simps]>>
          rename1 ‘FUNPOW _ _ (Ret x')’>>Cases_on ‘x'’>>
          rename1 ‘FUNPOW _ _ (Ret (q0,r0))’>>
          Cases_on ‘q0’>>fs[h_handle_call_ret_def,mrec_sem_simps]
          >- (imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[]>>
              irule EQ_TRANS>>
              first_x_assum $ irule_at (Pos hd)>>
              first_assum $ irule_at Any>>gvs[])>>
          rename1 ‘(SOME x',_)’>>Cases_on ‘x'’>>
          fs[h_handle_call_ret_def,mrec_sem_simps]>>
          rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
          fs[empty_locals_defs]>>
          TRY (imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[]>>
               irule EQ_TRANS>>
               first_x_assum $ irule_at (Pos hd)>>
               first_assum $ irule_at Any>>gvs[]>>NO_TAC)
          >- (imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[set_var_defs]>>
              irule EQ_TRANS>>
              first_x_assum $ irule_at Any>>
              first_x_assum $ irule_at Any>>gvs[])>>
          fs[GSYM FUNPOW]>>
          ‘SUC n' ≤ n’ by
            (CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
             qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
             rfs[FUNPOW_min_cancel,Tau_INJ]>>
             Cases_on ‘SUC n' - n’>>fs[FUNPOW_SUC])>>
          fs[FUNPOW_min_cancel,Tau_INJ,set_var_defs]>>
          irule EQ_TRANS>>
          last_assum $ irule_at (Pos hd)>>
          last_assum $ irule_at (Pos (el 2))>>
          simp[]>>
          irule EQ_TRANS>>
          irule_at (Pos last) EQ_TRANS>>
          last_assum $ irule_at (Pos hd)>>
          last_assum $ irule_at (Pos (el 2))>>gvs[])>>
      imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ,Once spin])
  (* DecCall *)
  >- (fs[Once mrec_sem_DecCall_simps,mrec_sem_simps,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      fs[msem_lift_monad_law]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          Cases_on ‘t’>>
          fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
          fs[ELIM_UNCURRY,mrec_sem_simps]>>
          rename1 ‘FUNPOW _ _ (Ret x')’>>Cases_on ‘x'’>>
          rename1 ‘FUNPOW _ _ (Ret (q0,r0))’>>
          Cases_on ‘q0’>>fs[h_handle_deccall_ret_def,mrec_sem_simps]
          >- (imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[]>>
              irule EQ_TRANS>>
              first_x_assum $ irule_at (Pos hd)>>
              first_assum $ irule_at Any>>gvs[])>>
          rename1 ‘(SOME x',_)’>>Cases_on ‘x'’>>
          fs[h_handle_deccall_ret_def,mrec_sem_simps]>>
          rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
          fs[empty_locals_defs]>>
          TRY (imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[]>>
               irule EQ_TRANS>>
               first_x_assum $ irule_at (Pos hd)>>
               first_assum $ irule_at Any>>gvs[]>>NO_TAC) >>
          fs[GSYM FUNPOW, set_var_defs]>>
          ‘SUC n' ≤ n’ by
            (CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
             qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
             rfs[FUNPOW_min_cancel,Tau_INJ]>>
             Cases_on ‘SUC n' - n’>>fs[FUNPOW_SUC])>>
          fs[FUNPOW_min_cancel,Tau_INJ,set_var_defs, msem_lift_monad_law]>>
          qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
          Cases_on ‘∃t. strip_tau X t’>>fs[]
          >- (drule_then assume_tac strip_tau_FUNPOW>> fs[] >>
              Cases_on ‘t’>>
              fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
              fs[ELIM_UNCURRY,mrec_sem_simps]>>
              rename1 ‘FUNPOW _ _ (Ret x')’>>Cases_on ‘x'’>>
              drule FUNPOW_Tau_Ret_eq>>strip_tac>>gvs[]>>
              first_assum $ drule_at Any >>
              first_x_assum kall_tac >>
              rw[] >>
              first_assum $ drule_at Any >>
              rw[]) >>
          imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
          qhdtm_x_assum ‘FUNPOW’ mp_tac>>
          rewrite_tac[Once (Q.SPEC ‘n - SUC n'’ spin_FUNPOW_Tau)]>>
          simp[FUNPOW_eq_elim,Tau_INJ,Once spin])>>
      imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ,Once spin])
  (* ExtCall *)
  >- (fs[h_prog_def,h_prog_ext_call_def,mrec_sem_simps,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps]))>>
  TRY (Cases_on ‘m’)>>
  fs[h_prog_def,h_prog_sh_mem_load_def,
     h_prog_sh_mem_store_def, nb_op_def,
     mrec_sem_simps]>>
  rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])
QED

Theorem bounded_0_FFI_final_w:
  (∀k'.
    s.ffi.io_events =
    (SND (evaluate (prog,s with clock := k'))).ffi.io_events) ∧
  s.clock = 0 ∧
  good_dimindex (:α) ∧
  mrec_sem (h_prog (prog,unclock s:('a,'b) bstate)) ≈ Vis a g ⇒
  ¬ (event_filter (FST (query_oracle s.ffi (FST a))))
Proof
  strip_tac>>
  imp_res_tac itree_wbisim_Vis_FUNPOW>>
  pop_assum kall_tac>>
  qpat_x_assum ‘_ ≈ _’ kall_tac>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘a’,‘k’,‘s’,‘prog’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘a’,‘k’,‘s’,‘prog’]>>
  Induct >> rpt strip_tac>>
  TRY (fs[h_prog_def,mrec_sem_simps,
          h_prog_dec_def,
          h_prog_return_def,
          h_prog_raise_def,
          h_prog_call_def,
          h_prog_cond_def,
          h_prog_seq_def,
          h_prog_store_def,
          h_prog_store_byte_def,
          h_prog_assign_def,
          panPropsTheory.eval_upd_clock_eq]>>
       rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
       fs[Once itree_wbisim_cases]>>NO_TAC)>>
  pop_assum mp_tac>>simp[]
  (* Dec *)
  >- (fs[h_prog_def,h_prog_dec_def,mrec_sem_simps,
         Once evaluate_def,msem_lift_monad_law,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      fs[ELIM_UNCURRY,msem_lift_monad_law]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          Cases_on ‘t’>>
          fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
          gvs[wbisim_FUNPOW_Tau,mrec_sem_simps]>>
          dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>gvs[]>>
          qmatch_asmsub_abbrev_tac ‘(prog,t)’>>
          last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
          ‘s.ffi = (reclock t).ffi’ by simp[Abbr‘t’]>>
          pop_assum (fn h => rewrite_tac[h])>>
          first_x_assum irule>>gvs[Abbr‘t’]>>metis_tac[])>>
      imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      once_rewrite_tac[Q.SPEC ‘n'’ spin_FUNPOW_Tau]>>
      simp[FUNPOW_eq_elim,Tau_INJ]>>
      simp[Once spin])
  (* Seq *)
  >- (fs[h_prog_def,h_prog_seq_def,mrec_sem_simps,
        Once evaluate_def]>>
      fs[msem_lift_monad_law]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[wbisim_FUNPOW_Tau]
      >- (imp_res_tac strip_tau_FUNPOW>>
          Cases_on ‘t’>>
          fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
          fs[ELIM_UNCURRY,mrec_sem_simps]
          >- (rename1 ‘Ret x’>>Cases_on ‘x’>>rename1 ‘(q,r)’>>fs[]>>
              FULL_CASE_TAC>>fs[mrec_sem_simps]>>
              gvs[GSYM FUNPOW_SUC,FUNPOW_Tau_neq2]>>
              fs[GSYM FUNPOW]>>
              ‘SUC n ≤ n'’
                by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                    qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                    rfs[FUNPOW_min_cancel,Tau_INJ]>>
                    Cases_on ‘SUC n - n'’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ]>>
              drule mrec_Ret_const_ffi>>strip_tac>>
              pop_assum $ assume_tac o GSYM>>fs[]>>
              last_x_assum $ qspec_then ‘n' - SUC n’ assume_tac>>fs[]>>
             ‘r.ffi = (reclock r).ffi’ by simp[]>>
              pop_assum (fn h => rewrite_tac [h])>>
              first_x_assum irule>>simp[]>>
              first_assum $ irule_at Any>>
              ‘ltree_lift query_oracle s.ffi
               (mrec_sem(h_prog(prog,unclock s))) ≈ Ret (NONE,r)’
                by (gvs[ltree_lift_cases,ltree_lift_FUNPOW_Tau,
                        wbisim_FUNPOW_Tau]>>
                    irule itree_wbisim_refl)>>
              drule_then drule ltree_Ret_to_evaluate'>>strip_tac>>fs[]>>
              dxrule evaluate_min_clock>>
              pop_assum kall_tac>>
              strip_tac>>gvs[]>>
             rename1 ‘evaluate(prop,s with clock := k')’>>
              strip_tac>>
              first_assum $ qspec_then ‘k'’ mp_tac>>
              CASE_TAC>>fs[]>>gvs[]>>
              ‘reclock r with clock := 0 = reclock r’
                by simp[state_component_equality]>>fs[]>>
              assume_tac (Q.SPECL [‘prog'’,‘reclock r’,‘k''’] panPropsTheory.evaluate_add_clock_io_events_mono)>>
              fs[IS_PREFIX_APPEND]>>
              Cases_on ‘evaluate(prog',reclock r)’>>gvs[]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>
              pop_assum mp_tac>>fs[IS_PREFIX_APPEND]>>
              gvs[]>>
              Cases_on ‘q ≠ SOME TimeOut’>>fs[]
              >- (drule panPropsTheory.evaluate_add_clock_eq>>
                  strip_tac>>
                 first_x_assum $ qspec_then ‘k''’ assume_tac>>rfs[]>>gvs[])>>
              first_x_assum $ qspec_then ‘k' + k''’ assume_tac>>gvs[]>>
              rev_drule panPropsTheory.evaluate_add_clock_eq>>
              strip_tac>>
              first_x_assum $ qspec_then ‘k''’ assume_tac>>gvs[])>>
          imp_res_tac FUNPOW_Tau_Vis_eq>>gvs[]>>
          last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
          first_x_assum irule>>gvs[]>>
          first_assum $ irule_at Any>>
          strip_tac>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>
          FULL_CASE_TAC>>fs[]>>
          Cases_on ‘evaluate(prog,s with clock := k')’>>fs[]>>
          Cases_on ‘evaluate(prog',r)’>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          pop_assum mp_tac>>
          fs[IS_PREFIX_APPEND])>>
      imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ,Once spin])
  (* If *)
  >- (fs[h_prog_def,h_prog_cond_def,mrec_sem_simps,
         Once evaluate_def,msem_lift_monad_law,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      last_x_assum $ qspec_then ‘n'’ assume_tac>>fs[]>>
      first_x_assum irule>>gvs[]>>
      first_x_assum $ irule_at Any>>gvs[])
  (* While *)
  >- (fs[Once mrec_sem_while_unfold,Once evaluate_def,
         panPropsTheory.eval_upd_clock_eq,mrec_sem_simps]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          Cases_on ‘t’>>
          fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]
          >- (rename1 ‘Ret x’>>Cases_on ‘x’>>rename1 ‘(q,r)’>>fs[]>>
              rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
              gvs[GSYM FUNPOW_SUC,FUNPOW_Tau_neq2]>>
              fs[GSYM FUNPOW]>>
              ‘SUC n ≤ n'’
                by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                    qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                    rfs[FUNPOW_min_cancel,Tau_INJ]>>
                    Cases_on ‘SUC n - n'’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ]>>
              drule mrec_Ret_const_ffi>>strip_tac>>
              pop_assum $ assume_tac o GSYM>>fs[]>>
              last_x_assum $ qspec_then ‘n' - SUC n’ assume_tac>>fs[]>>
             ‘r.ffi = (reclock r).ffi’ by simp[]>>
              pop_assum (fn h => rewrite_tac [h])>>
              first_x_assum irule>>simp[]>>
              first_assum $ irule_at Any>>
              qmatch_asmsub_abbrev_tac ‘strip_tau _ (Ret (res,_))’>>
              ‘ltree_lift query_oracle s.ffi
               (mrec_sem(h_prog(prog,unclock s))) ≈ Ret (res,r)’
                by (gvs[ltree_lift_cases,ltree_lift_FUNPOW_Tau,
                        wbisim_FUNPOW_Tau,Abbr‘res’]>>
                    irule itree_wbisim_refl)>>
              fs[Abbr‘res’]>>
              drule_then drule ltree_Ret_to_evaluate'>>strip_tac>>fs[]>>
              dxrule evaluate_min_clock>>
              pop_assum kall_tac>>
              strip_tac>>gvs[]>>
              rename1 ‘evaluate(prog,s with clock := k')’>>
              strip_tac>>
              ‘reclock r with clock := 0 = reclock r’
                by simp[state_component_equality]>>fs[]>>
              first_assum $ qspec_then ‘SUC k'’ mp_tac>>
              rewrite_tac[dec_clock_def]>>
              (PURE_CASE_TAC
               >- gvs[]>>
               mp_tac (Q.SPECL [‘While e prog’,‘reclock r’,‘k''’] panPropsTheory.evaluate_add_clock_io_events_mono)>>
               simp[IS_PREFIX_APPEND])>>
              strip_tac>>
              strip_tac>>
              Cases_on ‘evaluate(While e prog,reclock r)’>>gvs[]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>fs[]>>
              pop_assum mp_tac>>
              pop_assum mp_tac>>
              fs[IS_PREFIX_APPEND]>>
              gvs[]>>
              (Cases_on ‘q ≠ SOME TimeOut’>>fs[]
               >- (drule panPropsTheory.evaluate_add_clock_eq>>
                   strip_tac>>
                   first_x_assum $ qspec_then ‘k''’ assume_tac>>rfs[]>>gvs[])>>
               first_x_assum $ qspec_then ‘SUC (k' + k'')’ assume_tac>>gvs[]>>
               fs[dec_clock_def])>>
              rev_drule panPropsTheory.evaluate_add_clock_eq>>
              strip_tac>>
              first_x_assum $ qspec_then ‘k''’ assume_tac>>gvs[])>>
          imp_res_tac FUNPOW_Tau_Vis_eq>>gvs[]>>
          last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
          first_x_assum irule>>gvs[]>>
          first_assum $ irule_at Any>>
          strip_tac>>
          first_x_assum $ qspec_then ‘SUC k'’ assume_tac>>
          FULL_CASE_TAC>>fs[dec_clock_def]>>
          Cases_on ‘evaluate(prog,s with clock := k')’>>fs[]>>
          Cases_on ‘evaluate(While e prog,r)’>>fs[]>>
          rpt (CASE_TAC>>fs[])>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          pop_assum mp_tac>>
          fs[IS_PREFIX_APPEND])>>
      imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ,Once spin])
  (* Call *)
  >- (fs[Once mrec_sem_Call_simps,mrec_sem_simps,
         Once evaluate_def,msem_lift_monad_law,
         panPropsTheory.eval_upd_clock_eq,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
      pop_assum mp_tac>>
      ntac 6 (TOP_CASE_TAC>>fs[mrec_sem_simps])>>strip_tac>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          fs[Abbr‘X’]>>Cases_on ‘t’>>
          fs[wbisim_FUNPOW_Tau,itree_bind_thm,FUNPOW_Tau_bind]>>
          gvs[Abbr‘Y’]
          >- (rename1 ‘Ret x'’>>Cases_on ‘x'’>>fs[]>>rename1 ‘Ret (q',r')’>>
              Cases_on ‘q'’>>fs[h_handle_call_ret_def,mrec_sem_simps]>>
              rename1 ‘Ret (SOME x',r')’>>Cases_on ‘x'’>>
              fs[h_handle_call_ret_def,mrec_sem_simps]>>
              rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
              (* exception *)
              fs[GSYM FUNPOW,set_var_defs]>>
              ‘SUC n ≤ n'’
                by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                    qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                    rfs[FUNPOW_min_cancel,Tau_INJ]>>
                    Cases_on ‘SUC n - n'’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ]>>gvs[]>>
              drule mrec_Ret_const_ffi>>strip_tac>>
              pop_assum $ assume_tac o GSYM>>fs[]>>
              last_x_assum $ qspec_then ‘n' - SUC n’ assume_tac>>fs[]>>
              ‘r'.ffi = (reclock r' with locals := s.locals |+ (q'',v)).ffi’ by simp[]>>
              pop_assum (fn h => rewrite_tac[h])>>
              first_x_assum irule>>simp[]>>
              first_assum $ irule_at Any>>
              rename1 ‘h_prog(prog,r' with locals := s.locals |+ (q0,v))’>>
              ‘ltree_lift query_oracle s.ffi
               (mrec_sem(h_prog(q,unclock s with locals := r))) ≈
               Ret (SOME (Exception m' v),r')’
                by (gvs[ltree_lift_cases,ltree_lift_FUNPOW_Tau,
                        wbisim_FUNPOW_Tau]>>
                    irule itree_wbisim_refl)>>
              qmatch_asmsub_abbrev_tac ‘h_prog(q,t)’>>
              ‘t.ffi = s.ffi’ by simp[Abbr‘t’]>>
              drule_then drule ltree_Ret_to_evaluate'>>strip_tac>>rfs[]>>
              dxrule evaluate_min_clock>>
              pop_assum kall_tac>>
              strip_tac>>gvs[]>>
              rename1 ‘evaluate(q,reclock t with clock := k')’>>
              strip_tac>>
              ‘reclock r' with clock := 0 = reclock r'’
                by simp[state_component_equality]>>fs[]>>
              first_assum $ qspec_then ‘SUC k'’ mp_tac>>
              rewrite_tac[dec_clock_def]>>
              PURE_TOP_CASE_TAC >- gvs[] >>
              fs[Abbr‘t’]>>
              qmatch_goalsub_abbrev_tac ‘(prog,t')’>>
              assume_tac (Q.SPECL [‘prog’,‘t'’,‘k''’] panPropsTheory.evaluate_add_clock_io_events_mono)>>
              fs[IS_PREFIX_APPEND]>>
              Cases_on ‘evaluate(prog,t')’>>gvs[]>>
              fs[Abbr‘t'’]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>
              pop_assum mp_tac>>fs[IS_PREFIX_APPEND]>>
              strip_tac>>gvs[]>>
              Cases_on ‘q' ≠ SOME TimeOut’>>fs[]
              >- (drule panPropsTheory.evaluate_add_clock_eq>>
                  strip_tac>>
                  first_x_assum $ qspec_then ‘k''’ assume_tac>>rfs[]>>gvs[])>>
              first_x_assum $ qspec_then ‘SUC (k' + k'')’ assume_tac>>
              gvs[dec_clock_def]>>
              rev_drule panPropsTheory.evaluate_add_clock_eq>>
              strip_tac>>
              first_x_assum $ qspec_then ‘k''’ assume_tac>>gvs[])>>
          dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>gvs[]>>
          last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
          first_x_assum $ qspecl_then [‘q’,‘s with locals := r’,‘g’,‘a’] assume_tac>>
          gvs[ltree_lift_Vis_alt,ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
          first_x_assum irule>>
          strip_tac>>
          first_x_assum $ qspec_then ‘SUC k'’ assume_tac>>
          FULL_CASE_TAC>>fs[dec_clock_def]>>
          rpt (CASE_TAC>>fs[empty_locals_defs,set_var_defs])>>
          qmatch_goalsub_abbrev_tac ‘evaluate (prog,t)’>>
          Cases_on ‘evaluate(prog,t)’>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          pop_assum mp_tac>>
          fs[IS_PREFIX_APPEND,Abbr‘t’])>>
      imp_res_tac strip_tau_spin>>fs[spin_bind]>>
      qpat_x_assum ‘FUNPOW _ _ _ = spin’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ]>>
      simp[Once spin])
  (* DecCall *)
  >- (fs[Once mrec_sem_DecCall_simps,mrec_sem_simps,
         Once evaluate_def,msem_lift_monad_law,
         panPropsTheory.eval_upd_clock_eq,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
      pop_assum mp_tac>>
      rpt (TOP_CASE_TAC>>fs[mrec_sem_simps])>>strip_tac>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          fs[Abbr‘X’]>>Cases_on ‘t’>>
          fs[wbisim_FUNPOW_Tau,itree_bind_thm,FUNPOW_Tau_bind]>>
          gvs[Abbr‘Y’]
          >- (rename1 ‘Ret x'’>>Cases_on ‘x'’>>fs[]>>rename1 ‘Ret (q',r')’>>
              Cases_on ‘q'’>>fs[h_handle_deccall_ret_def,mrec_sem_simps]>>
              rename1 ‘Ret (SOME x',r')’>>Cases_on ‘x'’>>
              fs[h_handle_deccall_ret_def,mrec_sem_simps]>>
              rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
              (* exception *)
              fs[GSYM FUNPOW,set_var_defs]>>
              ‘SUC n ≤ n'’
                by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                    qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                    rfs[FUNPOW_min_cancel,Tau_INJ]>>
                    Cases_on ‘SUC n - n'’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ,mrec_sem_FUNPOW_Tau]>>
              drule mrec_Ret_const_ffi>>strip_tac>>
              pop_assum $ assume_tac o GSYM>>fs[]>>
              fs[msem_lift_monad_law] >>
              qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
              Cases_on ‘∃t. strip_tau X t’>>fs[]
              >- (drule_then assume_tac strip_tau_FUNPOW>> fs[] >>
                  Cases_on ‘t’>>
                  fs[Abbr‘X’,Abbr‘Y’,FUNPOW_Tau_bind,mrec_sem_FUNPOW_Tau]>>
                  fs[ELIM_UNCURRY,mrec_sem_simps]>>
                  ‘n'' ≤ n' - SUC n’
                    by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                        qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                        rfs[FUNPOW_min_cancel,Tau_INJ]>>
                        Cases_on ‘n'' + SUC n - n'’>>fs[FUNPOW_SUC])>>
                  fs[FUNPOW_min_cancel,Tau_INJ,mrec_sem_FUNPOW_Tau,FUNPOW_Tau_bind]>>
                  qmatch_asmsub_abbrev_tac ‘X = FUNPOW Tau (_ - _) _’>>
                  ‘FUNPOW Tau 0 X = FUNPOW Tau (n' − (n'' + SUC n)) (Vis a k)’ by simp[FUNPOW_0] >>
                  unabbrev_all_tac >>
                  dxrule_then assume_tac FUNPOW_Tau_Vis_eq >>
                  gvs[] >>
                  last_x_assum kall_tac >>
                  last_x_assum $ qspec_then ‘n''’ assume_tac >>
                  ‘r'.ffi = (reclock r' with locals := s'.locals |+ (m,v)).ffi’ by simp[]>>
                  pop_assum (fn h => rewrite_tac[h])>>
                  first_x_assum irule>>simp[]>>
                  first_assum $ irule_at Any>>
                  ‘ltree_lift query_oracle s'.ffi
                   (mrec_sem(h_prog(q,unclock s' with locals := r))) ≈
                   Ret (SOME (Return v),r')’
                    by (gvs[ltree_lift_cases,ltree_lift_FUNPOW_Tau,
                            wbisim_FUNPOW_Tau]>>
                        irule itree_wbisim_refl)>>
                  qmatch_asmsub_abbrev_tac ‘h_prog(q,t)’>>
                  ‘t.ffi = s'.ffi’ by simp[Abbr‘t’]>>
                  drule_then drule ltree_Ret_to_evaluate'>>strip_tac>>rfs[]>>
                  dxrule evaluate_min_clock>>
                  pop_assum kall_tac>>
                  strip_tac>>gvs[]>>
                  strip_tac>>
                  ‘reclock r' with clock := 0 = reclock r'’
                    by simp[state_component_equality]>>fs[]>>
                  first_assum $ qspec_then ‘SUC k''’ mp_tac>>
                  rewrite_tac[dec_clock_def]>>
                  PURE_TOP_CASE_TAC >- gvs[] >>
                  fs[Abbr‘t’]>>
                  qmatch_goalsub_abbrev_tac ‘(prog,t')’>>
                  assume_tac (Q.SPECL [‘prog’,‘t'’,‘k'’] panPropsTheory.evaluate_add_clock_io_events_mono)>>
                  fs[IS_PREFIX_APPEND]>>
                  Cases_on ‘evaluate(prog,t')’>>gvs[]>>
                  fs[Abbr‘t'’]>>
                  imp_res_tac panPropsTheory.evaluate_io_events_mono>>
                  pop_assum mp_tac>>fs[IS_PREFIX_APPEND]>>
                  strip_tac>>gvs[]>>
                  Cases_on ‘q' ≠ SOME TimeOut’>>fs[]
                  >- (drule panPropsTheory.evaluate_add_clock_eq>>
                      strip_tac>>
                      first_x_assum $ qspec_then ‘k'’ assume_tac>>rfs[]>>gvs[])>>
                  first_x_assum $ qspec_then ‘SUC (k'' + k')’ assume_tac>>
                  gvs[dec_clock_def]>>
                  rev_drule panPropsTheory.evaluate_add_clock_eq>>
                  strip_tac>>
                  first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[]) >>
              imp_res_tac strip_tau_spin>>gvs[spin_bind]>>
              qhdtm_x_assum ‘FUNPOW’ mp_tac>> gvs[mrec_sem_spin] >>
              rewrite_tac[Once (Q.SPEC ‘n' - SUC n’ spin_FUNPOW_Tau)]>>
              simp[FUNPOW_eq_elim,Tau_INJ,Once spin]) >>
          dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>gvs[]>>
          last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
          first_x_assum $ qspecl_then [‘q’,‘s' with locals := r’,‘g’,‘a’] assume_tac>>
          gvs[ltree_lift_Vis_alt,ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
          first_x_assum irule>>
          strip_tac>>
          first_x_assum $ qspec_then ‘SUC k'’ assume_tac>>
          FULL_CASE_TAC>>fs[dec_clock_def]>>
          rpt (CASE_TAC>>fs[empty_locals_defs,set_var_defs])>>
          qmatch_goalsub_abbrev_tac ‘evaluate (prog,t)’>>
          Cases_on ‘evaluate(prog,t)’>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          pop_assum mp_tac>>
          fs[IS_PREFIX_APPEND,Abbr‘t’])>>
      imp_res_tac strip_tau_spin>>fs[spin_bind]>>
      qpat_x_assum ‘FUNPOW _ _ _ = spin’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ]>>
      simp[Once spin])
  (* ExtCall *)
  >- (fs[h_prog_def,h_prog_ext_call_def,Once evaluate_def,
         panPropsTheory.eval_upd_clock_eq,mrec_sem_simps]>>
      rpt (PURE_FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      gvs[event_filter_def,query_oracle_def,ffiTheory.call_FFI_def]>>
      rpt (PURE_FULL_CASE_TAC>>fs[])>>
      gvs[empty_locals_defs,mrec_sem_simps,event_filter_def,ffiTheory.call_FFI_def]>>
      gvs[ffiTheory.ffi_state_component_equality])>>
  (* ShMem *)
  TRY(Cases_on ‘m’)>>
  fs[h_prog_def,h_prog_sh_mem_store_def,
     h_prog_sh_mem_load_def, Once evaluate_def,
     nb_op_def,
     panPropsTheory.eval_upd_clock_eq,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1,
     mrec_sem_simps]>>
  rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
  Cases_on ‘o'’ >> gvs[nb_op_def] >>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>
  fs[nb_op_def,sh_mem_load_def,sh_mem_store_def]>>
  rpt (FULL_CASE_TAC>>fs[])>>
  gvs[event_filter_def,query_oracle_def,ffiTheory.call_FFI_def]>>
  rpt (FULL_CASE_TAC>>fs[])>>
  gvs[empty_locals_defs,mrec_sem_simps,event_filter_def,ffiTheory.call_FFI_def]>>
  gvs[ffiTheory.ffi_state_component_equality]
QED

Theorem Vis_FFI_final_thm:
  mrec_sem(h_prog(prog,s)) ≈ Vis a g ∧
  (¬ event_filter (FST (query_oracle s.ffi (FST a)))) ⇒
  ∃f r. ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,s))) ≈ Ret (SOME (FinalFFI f),r)
Proof
  strip_tac>>
  dxrule itree_wbisim_Vis_FUNPOW>>strip_tac>>
  pop_assum kall_tac>>
  rpt (pop_assum mp_tac)>>
  MAP_EVERY qid_spec_tac [‘q’,‘r’,‘a’,‘k’,‘s’,‘prog’,‘n’]>>
  completeInduct_on ‘n’>>
  rpt gen_tac>>
  pop_assum mp_tac>>
  MAP_EVERY qid_spec_tac [‘q’,‘r’,‘a’,‘k’,‘s’,‘prog’]>>
  Induct >>rpt gen_tac>>ntac 3 strip_tac>>
  TRY (fs[h_prog_def,
            h_prog_assign_def,
            h_prog_raise_def,
            h_prog_return_def,
            h_prog_store_def,
            h_prog_store_byte_def,
            panPropsTheory.eval_upd_clock_eq,
            LAPPEND_NIL_2ND,empty_locals_defs,
            mrec_sem_simps,ltree_lift_cases]>>
       rpt (FULL_CASE_TAC>>
            fs[mrec_sem_simps,ltree_lift_cases])>>
       pairarg_tac>>gvs[]>>
       rpt FULL_CASE_TAC>>gvs[]>>NO_TAC)
  (* Dec *)
  >- (fs[h_prog_def,h_prog_dec_def,
         panPropsTheory.eval_upd_clock_eq,mrec_sem_simps]>>
      rpt FULL_CASE_TAC>>
      fs[mrec_sem_simps,ltree_lift_cases,
         msem_lift_monad_law,ltree_lift_monad_law]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases]>>
      fs[o_DEF,mrec_sem_simps,ELIM_UNCURRY]>>
      fs[ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          fs[Abbr‘X’]>>Cases_on ‘t’>>
          fs[wbisim_FUNPOW_Tau,itree_bind_thm,FUNPOW_Tau_bind]>>
          gvs[Abbr‘Y’]>>
          dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>gvs[]>>
          first_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
          qmatch_asmsub_abbrev_tac ‘(prog,t)’>>
          first_x_assum $ qspecl_then [‘prog’,‘t’,‘g’,‘a’] assume_tac>>
          gvs[]>>
          ‘t.ffi = s.ffi’ by simp[Abbr‘t’]>>fs[]>>gvs[]>>
          fs[ltree_lift_Vis_alt]>>
          pairarg_tac>>fs[ltree_lift_monad_law]>>
          Cases_on ‘FST a’>>fs[]>>
          fs[query_oracle_def]>>
          rpt (FULL_CASE_TAC>>gvs[])>>
          dxrule EQ_SYM>>strip_tac>>gvs[event_filter_def]>>
          fs[o_DEF,ltree_lift_cases]>>
          qmatch_goalsub_abbrev_tac ‘X >>= _ ≈ _’>>
          Cases_on ‘∃p. strip_tau X p’>>fs[]
          >- (drule strip_tau_FUNPOW>>strip_tac>>
              fs[FUNPOW_Tau_bind,wbisim_FUNPOW_Tau]>>
              Cases_on ‘p’>>fs[itree_bind_thm]
              >- fs[itree_wbisim_neq]>>
              fs[Once itree_wbisim_cases])>>
          imp_res_tac strip_tau_spin>>fs[spin_bind]>>
          rev_dxrule itree_wbisim_sym>>strip_tac>>
          drule (iffLR wbisim_spin_eq)>>
          simp[Once spin])>>
      imp_res_tac strip_tau_spin>>fs[spin_bind]>>
      qpat_x_assum ‘FUNPOW _ _ _ = spin’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ]>>
      simp[Once spin])
  (* Seq *)
 >- (fs[h_prog_def,h_prog_seq_def,mrec_sem_simps,
         panPropsTheory.eval_upd_clock_eq,ltree_lift_cases]>>
      rpt FULL_CASE_TAC>>
      fs[mrec_sem_simps,ltree_lift_cases,ltree_lift_FUNPOW_Tau,
         msem_lift_monad_law,ltree_lift_monad_law,wbisim_FUNPOW_Tau]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases]>>
      fs[o_DEF,mrec_sem_simps,ELIM_UNCURRY]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          fs[Abbr‘X’]>>Cases_on ‘t’>>
          fs[wbisim_FUNPOW_Tau,itree_bind_thm,FUNPOW_Tau_bind]>>
          gvs[Abbr‘Y’]
          >- (Cases_on ‘FST x = NONE’>>fs[mrec_sem_simps]>>
              fs[GSYM FUNPOW]>>
              ‘SUC n ≤ n'’
                by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                    qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                    rfs[FUNPOW_min_cancel,Tau_INJ]>>
                    Cases_on ‘SUC n - n'’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ]>>
              Cases_on ‘x’>>gvs[]>>rename1 ‘Ret (NONE,r')’>>
              drule mrec_Ret_const_ffi>>strip_tac>>
              pop_assum $ assume_tac o GSYM>>fs[]>>
              first_x_assum $ qspec_then ‘n' - SUC n’ assume_tac>>
              first_x_assum irule>>simp[]>>
              first_assum $ irule_at Any)>>
          dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>fs[]>>
          first_x_assum $ qspec_then ‘n'’ assume_tac>>fs[]>>
          first_x_assum $ qspecl_then [‘prog’,‘s’,‘g’,‘a’] assume_tac>>fs[]>>
          gvs[ltree_lift_Vis_alt]>>
          pairarg_tac>>fs[ltree_lift_monad_law]>>
          irule_at Any itree_wbisim_trans>>
          irule_at Any itree_bind_resp_t_wbisim>>
          first_assum $ irule_at Any>>
          simp[itree_bind_thm,mrec_sem_simps,ltree_lift_cases]>>
          irule_at Any itree_wbisim_refl)>>
      imp_res_tac strip_tau_spin>>fs[spin_bind]>>
      qpat_x_assum ‘FUNPOW _ _ _ = spin’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ]>>
      simp[Once spin])
  (* If *)
  >- (fs[h_prog_def,h_prog_cond_def,mrec_sem_simps,
         panPropsTheory.eval_upd_clock_eq,ltree_lift_cases]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases,mrec_sem_simps]>>
      first_x_assum $ qspec_then ‘n'’ assume_tac>>fs[]>>
      first_x_assum irule>>gvs[]>>metis_tac[])
  (* While *)
  >- (fs[Once mrec_sem_while_unfold,mrec_sem_simps,ltree_lift_cases,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases,mrec_sem_simps]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          fs[Abbr‘X’]>>Cases_on ‘t’>>
          fs[wbisim_FUNPOW_Tau,itree_bind_thm,FUNPOW_Tau_bind]>>
          gvs[Abbr‘Y’]
          >- (rename1 ‘Ret x’>>Cases_on ‘x’>>fs[]>>rename1 ‘Ret (q,r)’>>
              rpt (FULL_CASE_TAC>>fs[])>>
              fs[GSYM FUNPOW]>>
              ‘SUC n ≤ n'’
                by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                    qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                    rfs[FUNPOW_min_cancel,Tau_INJ]>>
                    Cases_on ‘SUC n - n'’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ]>>gvs[]>>
              drule mrec_Ret_const_ffi>>strip_tac>>
              pop_assum $ assume_tac o GSYM>>fs[]>>
              first_x_assum $ qspec_then ‘n' - SUC n’ assume_tac>>fs[]>>
              fs[ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
              first_x_assum irule>>simp[]>>metis_tac[])>>
          dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>fs[]>>
          first_x_assum $ qspec_then ‘n'’ assume_tac>>fs[]>>
          first_x_assum $ qspecl_then [‘prog’,‘s’,‘g’,‘a’] assume_tac>>fs[]>>
          gvs[ltree_lift_Vis_alt,ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
          pairarg_tac>>fs[ltree_lift_monad_law]>>
          irule_at Any itree_wbisim_trans>>
          irule_at Any itree_bind_resp_t_wbisim>>
          first_assum $ irule_at Any>>
          simp[itree_bind_thm,ltree_lift_cases,mrec_sem_simps]>>
          irule_at Any itree_wbisim_refl)>>
      imp_res_tac strip_tau_spin>>fs[spin_bind]>>
      qpat_x_assum ‘FUNPOW _ _ _ = spin’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ]>>
      simp[Once spin])
     (* Call *)
  >- (fs[Once mrec_sem_Call_simps,mrec_sem_simps,ltree_lift_cases,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases,mrec_sem_simps]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          fs[Abbr‘X’]>>Cases_on ‘t’>>
          fs[wbisim_FUNPOW_Tau,itree_bind_thm,FUNPOW_Tau_bind]>>
          gvs[Abbr‘Y’]
          >- (rename1 ‘Ret x'’>>Cases_on ‘x'’>>fs[]>>rename1 ‘Ret (q',r')’>>
              Cases_on ‘q'’>>fs[h_handle_call_ret_def,mrec_sem_simps]>>
              rename1 ‘Ret (SOME x',r')’>>Cases_on ‘x'’>>
              fs[h_handle_call_ret_def,mrec_sem_simps]>>
              rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
              fs[GSYM FUNPOW,set_var_defs]>>
              ‘SUC n ≤ n'’
                by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                    qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                    rfs[FUNPOW_min_cancel,Tau_INJ]>>
                    Cases_on ‘SUC n - n'’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ]>>gvs[]>>
              drule mrec_Ret_const_ffi>>strip_tac>>
              pop_assum $ assume_tac o GSYM>>fs[]>>
              first_x_assum $ qspec_then ‘n' - SUC n’ assume_tac>>fs[]>>
              fs[ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
              ‘r'.ffi = (r' with locals := s.locals |+ (q'',v)).ffi’
                by simp[]>>
              pop_assum (fn h => rewrite_tac[h])>>
              first_x_assum irule>>simp[]>>metis_tac[])>>
          dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>fs[]>>
          first_x_assum $ qspec_then ‘n'’ assume_tac>>fs[]>>
          first_x_assum $ qspecl_then [‘q’,‘s with locals := r’,‘g’,‘a’] assume_tac>>
          gvs[ltree_lift_Vis_alt,ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
          pairarg_tac>>fs[ltree_lift_monad_law]>>
          irule_at Any itree_wbisim_trans>>
          irule_at Any itree_bind_resp_t_wbisim>>
          first_assum $ irule_at Any>>
          simp[itree_bind_thm,ltree_lift_cases,mrec_sem_simps,
               h_handle_call_ret_def]>>
          irule_at Any itree_wbisim_refl)>>
      imp_res_tac strip_tau_spin>>fs[spin_bind]>>
      qpat_x_assum ‘FUNPOW _ _ _ = spin’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ]>>
      simp[Once spin])
  (* DecCall *)
  >- (fs[Once mrec_sem_DecCall_simps,mrec_sem_simps,ltree_lift_cases,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases,mrec_sem_simps]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃t. strip_tau X t’>>fs[]
      >- (imp_res_tac strip_tau_FUNPOW>>
          fs[Abbr‘X’]>>Cases_on ‘t’>>
          fs[wbisim_FUNPOW_Tau,itree_bind_thm,FUNPOW_Tau_bind]>>
          gvs[Abbr‘Y’]
          >- (rename1 ‘Ret x'’>>Cases_on ‘x'’>>fs[]>>rename1 ‘Ret (q',r')’>>
              Cases_on ‘q'’>>fs[h_handle_deccall_ret_def,mrec_sem_simps]>>
              rename1 ‘Ret (SOME x',r')’>>Cases_on ‘x'’>>
              fs[h_handle_deccall_ret_def,mrec_sem_simps]>>
              rpt (FULL_CASE_TAC>>fs[mrec_sem_simps])>>
              fs[GSYM FUNPOW,set_var_defs]>>
              ‘SUC n ≤ n'’
                by (CCONTR_TAC>>dxrule (iffLR  NOT_LESS_EQUAL)>>strip_tac>>
                    qhdtm_x_assum ‘FUNPOW’ $ assume_tac o GSYM>>
                    rfs[FUNPOW_min_cancel,Tau_INJ]>>
                    Cases_on ‘SUC n - n'’>>fs[FUNPOW_SUC])>>
              fs[FUNPOW_min_cancel,Tau_INJ]>>gvs[]>>
              drule mrec_Ret_const_ffi>>strip_tac>>
              pop_assum $ assume_tac o GSYM>>fs[]>>
              fs[msem_lift_monad_law] >>
              qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
              Cases_on ‘∃t. strip_tau X t’>>fs[]
              >- (imp_res_tac strip_tau_FUNPOW>>
                  fs[Abbr‘X’]>>Cases_on ‘t’>>
                  fs[wbisim_FUNPOW_Tau,itree_bind_thm,FUNPOW_Tau_bind]>>
                  gvs[Abbr‘Y’,ELIM_UNCURRY,mrec_sem_simps, o_DEF]>>
                  fs[ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
                  dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>gvs[]>>
                  last_x_assum kall_tac >>
                  last_x_assum $ qspec_then ‘n' - SUC n’ assume_tac >> gvs[] >>
                  qmatch_asmsub_abbrev_tac ‘(prog,t)’>>
                  first_x_assum $ qspecl_then [‘prog’,‘t’,‘g’,‘a’] assume_tac>>
                  gvs[]>>
                  ‘t.ffi = r'.ffi’ by simp[Abbr‘t’]>>fs[]>>gvs[]>>
                  fs[ltree_lift_Vis_alt]>>
                  pairarg_tac>>fs[ltree_lift_monad_law]>>
                  Cases_on ‘FST a’>>fs[]>>
                  fs[query_oracle_def]>>
                  rpt (FULL_CASE_TAC>>gvs[])>>
                  dxrule EQ_SYM>>strip_tac>>gvs[event_filter_def]>>
                  fs[o_DEF,ltree_lift_cases]>>
                  qmatch_goalsub_abbrev_tac ‘X >>= _ ≈ _’>>
                  Cases_on ‘∃p. strip_tau X p’>>fs[]
                  >- (drule strip_tau_FUNPOW>>strip_tac>>
                      fs[FUNPOW_Tau_bind,wbisim_FUNPOW_Tau]>>
                      Cases_on ‘p’>>fs[itree_bind_thm]
                      >- fs[itree_wbisim_neq]>>
                      fs[Once itree_wbisim_cases]) >>
                  imp_res_tac strip_tau_spin>>fs[spin_bind]>>
                  rev_dxrule itree_wbisim_sym>>strip_tac>>
                  drule (iffLR wbisim_spin_eq)>>
                  simp[Once spin]) >>
              imp_res_tac strip_tau_spin>>fs[spin_bind]>>
              qpat_x_assum ‘FUNPOW _ _ _ = spin’ mp_tac>>
              rewrite_tac[Once (Q.SPEC ‘n' - SUC n’ spin_FUNPOW_Tau)]>>
              simp[FUNPOW_eq_elim,Tau_INJ]>>
              simp[Once spin]) >>
          dxrule FUNPOW_Tau_Vis_eq>>strip_tac>>fs[]>>
          first_x_assum $ qspec_then ‘n'’ assume_tac>>fs[]>>
          first_x_assum $ qspecl_then [‘q’,‘s' with locals := r’,‘g’,‘a’] assume_tac>>
          gvs[ltree_lift_Vis_alt,ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau]>>
          pairarg_tac>>fs[ltree_lift_monad_law]>>
          irule_at Any itree_wbisim_trans>>
          irule_at Any itree_bind_resp_t_wbisim>>
          first_assum $ irule_at Any>>
          simp[itree_bind_thm,ltree_lift_cases,mrec_sem_simps,
               h_handle_deccall_ret_def]>>
          irule_at Any itree_wbisim_refl) >>
      imp_res_tac strip_tau_spin>>fs[spin_bind]>>
      qpat_x_assum ‘FUNPOW _ _ _ = spin’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘n'’ spin_FUNPOW_Tau)]>>
      simp[FUNPOW_eq_elim,Tau_INJ]>>
      simp[Once spin])
  (* ExitCall *)
  >- (fs[h_prog_def,h_prog_ext_call_def,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (PURE_FULL_CASE_TAC>>fs[mrec_sem_simps])>>
      Cases_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases,mrec_sem_simps]>>
      gvs[ltree_lift_Vis_alt]>>
      pairarg_tac>>fs[ltree_lift_cases,mrec_sem_simps]>>
      CASE_TAC>>fs[query_oracle_def,event_filter_def]>>
      irule_at Any itree_wbisim_refl)>>
  TRY (Cases_on ‘m’)>>
   fs[h_prog_def,h_prog_sh_mem_store_def,
     h_prog_sh_mem_load_def, Once evaluate_def,
     nb_op_def,ltree_lift_cases,
     panPropsTheory.eval_upd_clock_eq,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1,
     mrec_sem_simps]>>
  rpt (PURE_FULL_CASE_TAC>>fs[mrec_sem_simps])>>
  Cases_on ‘n’>>fs[FUNPOW_SUC,ltree_lift_cases,mrec_sem_simps]>>
  gvs[ltree_lift_Vis_alt]>>
  pairarg_tac>>fs[ltree_lift_cases,mrec_sem_simps]>>
  CASE_TAC>>fs[query_oracle_def,event_filter_def]>>
  irule_at Any itree_wbisim_refl
QED

Theorem nonret_imp_mrec_sem_spin:
  (∀k'. s.ffi.io_events =
        (SND (evaluate (prog,s with clock := k'))).ffi.io_events) ∧
  (∀p. ¬(ltree_lift query_oracle s.ffi
                    (mrec_sem (h_prog (prog,unclock s))) ≈ Ret p)) ∧
  s.clock = 0 ∧ good_dimindex (:α) ⇒
  mrec_sem (h_prog (prog,unclock (s:('a,'b)state))) = spin
Proof
  strip_tac>>
  Cases_on ‘∃t. strip_tau (mrec_sem(h_prog(prog,unclock s))) t’>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>
      Cases_on ‘t’>>
      gvs[ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau,ltree_lift_cases]
      >- fs[Once itree_wbisim_cases]>>
      drule bounded_0_FFI_final_w>>
      rpt (disch_then $ drule_at Any)>>
      imp_res_tac FUNPOW_Tau_imp_wbisim>>
      disch_then $ drule_at Any>>strip_tac>>
      drule Vis_FFI_final_thm>>strip_tac>>gvs[]>>
      gvs[ltree_lift_FUNPOW_Tau,wbisim_FUNPOW_Tau])>>
  imp_res_tac strip_tau_spin
QED

Theorem clock_0_imp_LNIL:
  (∀k'. s.ffi.io_events
        = (SND(evaluate(prog,s with clock:=k'))).ffi.io_events) ∧
  (∀p. ¬(ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,unclock s))) ≈ Ret p)) ∧
  s.clock = 0 ∧ good_dimindex (:'a) ⇒
  stree_trace query_oracle event_filter s.ffi (to_stree (mrec_sem (h_prog (prog,unclock (s:('a,'b) state))))) = [||]
Proof
  simp[stree_trace_def]>>
  simp[LFLATTEN_EQ_NIL]>>
  strip_tac>>
  irule every_coind>>
  qexists ‘{lnil}’>>
  simp[]>>rw[]>>
  TRY (fs[Once (GSYM lnil)]>>NO_TAC)>>
  simp[lnil_def]>>
  simp[Once LUNFOLD_BISIMULATION]>>
  qexists ‘CURRY {((s.ffi,to_stree(mrec_sem(h_prog(prog,unclock s)))),())
           | prog,s | (mrec_sem(h_prog(prog,unclock s)) = spin) ∧
                      (∀k'. s.ffi.io_events =
                            (SND (evaluate (prog,s with clock := k'))).ffi.io_events) ∧
                      (∀p. ¬(ltree_lift query_oracle s.ffi
                                        (mrec_sem (h_prog (prog,unclock s))) ≈ Ret p)) ∧
                      s.clock = 0}’>>
  rw[] >-
   (simp[EXISTS_PROD]>>
    irule_at Any EQ_REFL>>
    irule_at Any EQ_REFL>>gvs[]>>
    irule nonret_imp_mrec_sem_spin>>gvs[])>>
  Cases_on ‘x’>>fs[]>>
  simp[to_stree_simps,to_stree_spin]>>
  rewrite_tac[Once spin]>>simp[EXISTS_PROD]>>
  irule_at Any EQ_REFL>>
  first_assum $ irule_at Any>>
  first_assum $ irule_at Any>>
  simp[to_stree_spin]
QED

Theorem bounded_trace_eq:
  (∀k'. s.clock < k' ⇒ (SND(evaluate(prog:'a prog,s))).ffi.io_events
                       = (SND(evaluate(prog,s with clock:=k'))).ffi.io_events) ∧
  (∀p. ¬(ltree_lift query_oracle s.ffi (mrec_sem (h_prog (prog,unclock s))) ≈ Ret p)) ∧
  good_dimindex (:'a) ⇒
  LAPPEND (fromList (s.ffi.io_events)) (stree_trace query_oracle event_filter s.ffi (to_stree (mrec_sem (h_prog (prog,unclock s))))) =
  fromList (SND (evaluate (prog, s))).ffi.io_events
Proof
  MAP_EVERY qid_spec_tac [‘s’,‘prog’]>>
  recInduct evaluate_ind>>rw[]>>
  TRY (simp[h_prog_def,Once evaluate_def,
            h_prog_assign_def,
            h_prog_raise_def,
            h_prog_return_def,
            h_prog_ext_call_def,
            h_prog_store_def,
            h_prog_dec_def,
            h_prog_store_byte_def,
            panPropsTheory.eval_upd_clock_eq,
            LAPPEND_NIL_2ND,empty_locals_defs,
            mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
       rpt (PURE_CASE_TAC>>
            simp[mrec_sem_simps,to_stree_simps,stree_trace_simps,
                 stree_trace_Vis,LAPPEND_NIL_2ND])>>
       pairarg_tac>>gvs[]>>
       PURE_CASE_TAC>>gvs[]>>NO_TAC)
  (* Dec *)
  >- (fs[h_prog_def,h_prog_dec_def,Once evaluate_def,
         panPropsTheory.eval_upd_clock_eq,
         mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
      rpt CASE_TAC>>rpt FULL_CASE_TAC>>
      fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,
         LAPPEND_NIL_2ND,stree_trace_Vis,ltree_lift_cases,
         msem_lift_monad_law,to_stree_monad_law,ltree_lift_monad_law]>>
      pairarg_tac>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,t)’>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃p. X ≈ Ret p’>>fs[]
      >- (fs[Abbr‘X’]>>Cases_on ‘p’>>rename1 ‘Ret (q,r')’>>
          imp_res_tac ltree_lift_state_lift'>>fs[]>>
          drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
          gvs[Abbr‘Y’]>>
          gvs[mrec_sem_simps,ltree_lift_cases]>>
          fs[Once itree_wbisim_cases])>>
      fs[Abbr‘X’]>>
      drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
      strip_tac>>gvs[]>>
      (*      last_x_assum $ qspec_then ‘t’ assume_tac>>gvs[Abbr‘t’]>>*)
      last_x_assum irule>>
      fs[Once evaluate_def,panPropsTheory.eval_upd_clock_eq]>>
      rpt strip_tac>>
      last_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[]>>
      pairarg_tac>>gvs[])
  (* ShMemLoad *)
  >~ [‘ShMemLoad’]
  >- (Cases_on ‘op’>>
      fs[h_prog_def,h_prog_sh_mem_load_def,
         nb_op_def,
         panPropsTheory.eval_upd_clock_eq,ltree_lift_cases,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1,
         mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
      rpt (CASE_TAC>>
           fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,
              stree_trace_Vis,ltree_lift_cases,
              msem_lift_monad_law,
              to_stree_monad_law,ltree_lift_monad_law])>>
      TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
      pairarg_tac>>fs[]>>FULL_CASE_TAC>>
      fs[Once itree_wbisim_cases])
  (* ShMemStore *)
  >~ [‘ShMemStore’]
  >- (Cases_on ‘op’>>
      fs[h_prog_def,h_prog_sh_mem_store_def,
         nb_op_def,
         panPropsTheory.eval_upd_clock_eq,ltree_lift_cases,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1,
         mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
      rpt (CASE_TAC>>
           fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,
              stree_trace_Vis,ltree_lift_cases,
              msem_lift_monad_law,
              to_stree_monad_law,ltree_lift_monad_law])>>
      TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
      pairarg_tac>>fs[]>>FULL_CASE_TAC>>
      fs[Once itree_wbisim_cases])
  (* Seq *)
  >- (fs[h_prog_def,h_prog_seq_def,Once evaluate_def,
         panPropsTheory.eval_upd_clock_eq,ltree_lift_cases,
         mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
      rpt FULL_CASE_TAC>>pairarg_tac>>
      fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,stree_trace_Vis,
         ltree_lift_cases,
         msem_lift_monad_law,to_stree_monad_law,ltree_lift_monad_law]>>
      FULL_CASE_TAC>>fs[]
      (* NONE *)
      >- (drule_then drule ltree_lift_corres_evaluate>>strip_tac>>gvs[]>>
          imp_res_tac ltree_lift_state_lift'>>fs[]>>
          drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
          gvs[mrec_sem_simps,ltree_lift_cases]>>
          imp_res_tac stree_trace_ret_events'>>gvs[]>>
          imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>
          gvs[]>>
          fs[mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
          fs[Once evaluate_def]>>
          simp[GSYM LAPPEND_ASSOC]>>
          last_x_assum irule>>
          rpt strip_tac>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>strip_tac>>fs[]>>
          first_x_assum $ qspec_then ‘k'- s1.clock’ assume_tac>>fs[]>>
          gvs[]>>
          first_x_assum $ qspec_then ‘s.clock + k'- s1.clock’ assume_tac>>
          fs[])>>
      qmatch_asmsub_abbrev_tac ‘¬(X >>= Y ≈ Ret _)’>>
      Cases_on ‘∃p. X ≈ Ret p’
      >- (fs[Abbr‘X’]>>Cases_on ‘p’>>rename1 ‘Ret (q,r')’>>
          imp_res_tac ltree_lift_state_lift'>>fs[]>>
          drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
          imp_res_tac stree_trace_ret_events'>>gvs[]>>
          imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>
          gvs[]>>
          simp[mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
          gvs[Abbr‘Y’]>>
          gvs[mrec_sem_simps,ltree_lift_cases]>>
          FULL_CASE_TAC>>gvs[mrec_sem_simps,ltree_lift_cases]>>
          TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
          drule_then drule ltree_Ret_to_evaluate'>>strip_tac>>gvs[]>>
          Cases_on ‘res ≠ SOME TimeOut’>>fs[]
          >- (Cases_on ‘s.clock < k’>>fs[NOT_LESS]
              >- (rev_drule panPropsTheory.evaluate_add_clock_eq>>
                  strip_tac>>gvs[]>>
                  first_x_assum $ qspec_then ‘k-s.clock’ assume_tac>>
                  gvs[])>>
              drule panPropsTheory.evaluate_add_clock_eq>>
              strip_tac>>gvs[]>>
              first_x_assum $ qspec_then ‘s.clock-k’ assume_tac>>gvs[]>>
              ‘s with clock := s.clock = s’
                by simp[state_component_equality]>>fs[])>>
          drule evaluate_min_clock>>strip_tac>>gvs[]>>
          qpat_x_assum ‘evaluate (c1,s with clock := k) = _’ kall_tac>>
          qpat_x_assum ‘k' ≤ k’ kall_tac>>
          rename1 ‘evaluate (c1,s with clock := k) = _’>>
          ‘s.clock < k’
            by (CCONTR_TAC>>fs[NOT_LESS]>>
                drule panPropsTheory.evaluate_add_clock_eq>>strip_tac>>gvs[]>>
                first_x_assum $ qspec_then ‘s.clock - k’ assume_tac>>gvs[]>>
                ‘s with clock := s.clock = s’ by simp[state_component_equality]>>gvs[])>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>gvs[]>>
          simp[GSYM LAPPEND_ASSOC]>>
          pop_assum kall_tac>>
          first_assum $ qspec_then ‘k’ mp_tac>>
          impl_tac >- fs[] >>
          rewrite_tac[Once evaluate_def]>>
          fs[to_stree_simps,stree_trace_simps]>>
          qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>gvs[]>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          strip_tac>>gvs[]>>
          ‘(SND (evaluate (c1,s))).ffi.io_events ≼
           (SND (evaluate (c1,s with clock := k))).ffi.io_events’
            by (irule IS_PREFIX_TRANS>>
                irule_at Any panPropsTheory.evaluate_add_clock_io_events_mono>>
                drule (GSYM LESS_ADD)>>strip_tac>>
                pop_assum $ assume_tac o SIMP_RULE std_ss [Once ADD_COMM]>>
                pop_assum $ (fn h => rewrite_tac[h])>>
                metis_tac[IS_PREFIX_REFL])>>
          fs[IS_PREFIX_APPEND]>>rfs[]>>gvs[]>>
          ‘stree_trace query_oracle event_filter r'.ffi
           (to_stree (mrec_sem (h_prog (c2,r')))) = [||]’
            by (‘r'=unclock (reclock r')’ by simp[]>>
                pop_assum (fn h => once_rewrite_tac[h])>>
                ‘(unclock(reclock r')).ffi = (reclock r').ffi’ by simp[]>>
                pop_assum (fn h => once_rewrite_tac[h])>>
                ‘(reclock r' with clock := 0).clock = 0’
                  by simp[state_component_equality]>>
                irule clock_0_imp_LNIL>>
                gvs[]>>
                strip_tac>>
                drule_then drule nonret_imp_timeout>>strip_tac>>gvs[]>>
                first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[]>>
                last_x_assum $ qspec_then ‘k+k'’ assume_tac>>gvs[]>>
                pop_assum $ assume_tac o SIMP_RULE std_ss [Once evaluate_def]>>
                pop_assum $ mp_tac o SIMP_RULE std_ss [SimpR“$=”,Once evaluate_def]>>
                gvs[]>>
                pairarg_tac>>gvs[]>>
                qpat_x_assum ‘evalaute (c1,s with clock := k) = _’ assume_tac>>
                drule panPropsTheory.evaluate_add_clock_eq>>
                strip_tac>>gvs[]>>
                first_x_assum $ qspec_then ‘k'’ $ assume_tac o SIMP_RULE std_ss [Once ADD_COMM]>>
                simp[Once evaluate_def])>>
          gvs[LAPPEND_NIL_2ND])>>
      (* c1 nonret *)
      fs[Abbr‘X’]>>
      fs[Once evaluate_def,ELIM_UNCURRY]>>
      drule_then drule nonret_imp_timeout'>>
      strip_tac>>fs[]>>
      first_assum $ qspec_then ‘s.clock’ assume_tac>>
      ‘s with clock := s.clock = s’ by simp[state_component_equality]>>
      fs[]>>fs[]>>
      drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
      strip_tac>>fs[]>>gvs[]>>
      irule EQ_TRANS>>
      last_x_assum $ irule_at Any>>gvs[]>>
      rpt strip_tac>>gvs[]>>
      last_assum $ qspec_then ‘k'’ assume_tac>>
      first_assum $ qspec_then ‘k'’ assume_tac>>
      fs[])
  (* If *)
  >- (fs[h_prog_def,h_prog_cond_def,
         panPropsTheory.eval_upd_clock_eq,ltree_lift_cases,
         mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
      rpt CASE_TAC>>
      fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,stree_trace_Vis,
         ltree_lift_cases,
         msem_lift_monad_law,to_stree_monad_law,ltree_lift_monad_law]>>
      TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
      fs[Once evaluate_def]>>
      fs[Once evaluate_def,panPropsTheory.eval_upd_clock_eq]>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      (Cases_on ‘∃p. X ≈ Ret p’
       >- (fs[Abbr‘X’]>>Cases_on ‘p’>>rename1 ‘Ret (q,r')’>>
           imp_res_tac ltree_lift_state_lift'>>fs[]>>
           drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
           gvs[Abbr‘Y’]>>
           gvs[mrec_sem_simps,ltree_lift_cases]>>
           fs[Once itree_wbisim_cases])>>
       fs[Abbr‘X’]>>
       drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
       strip_tac>>gvs[]))
  (* While *)
  >- (Cases_on ‘s.clock = 0’>>fs[]
      >- (fs[Once evaluate_def]>>
          rpt (CASE_TAC>>fs[])>>
          TRY (fs[Once mrec_sem_while_unfold,ltree_lift_cases,
                  panPropsTheory.eval_upd_clock_eq]>>
               fs[Once itree_wbisim_cases]>>NO_TAC)>>
          ‘∀k'.
            s.ffi.io_events =
            (SND (evaluate (While e c,s with clock := k'))).ffi.io_events’
            by (rpt strip_tac>>Cases_on ‘k'’>>fs[]>>
                ‘s with clock := 0 = s’ by gvs[state_component_equality]>>
                gvs[]>>fs[Once evaluate_def,empty_locals_defs])>>
          drule clock_0_imp_LNIL>>fs[]>>
          strip_tac>>gvs[empty_locals_defs,LAPPEND_NIL_2ND])>>
      (* s.clock ≠ 0 *)
      qpat_x_assum ‘∀p. ¬ (_ ≈ _)’ mp_tac>>
      once_rewrite_tac[mrec_sem_while_unfold,evaluate_def]>>
      simp[panPropsTheory.eval_upd_clock_eq,ltree_lift_cases,
           mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
      rpt CASE_TAC>>
      fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,
         stree_trace_Vis,ltree_lift_cases,
         msem_lift_monad_law,to_stree_monad_law,ltree_lift_monad_law]>>
      TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
      strip_tac>>
      qmatch_asmsub_abbrev_tac ‘X >>= Y’>>
      Cases_on ‘∃p. X ≈ Ret p’>>fs[]
      >-(fs[Abbr‘X’]>>Cases_on ‘p’>>rename1 ‘Ret (q,r')’>>
         imp_res_tac ltree_lift_state_lift'>>fs[]>>
         drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
         fs[Abbr‘Y’]>>
         reverse (Cases_on ‘q = NONE ∨ q = SOME Continue’)
         >- (rpt (FULL_CASE_TAC>>gvs[ltree_lift_cases])>>
             fs[Once itree_wbisim_cases])>>
         imp_res_tac stree_trace_ret_events'>>gvs[]>>
         imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>
         gvs[ltree_lift_cases,to_stree_simps,stree_trace_simps]>>
         drule_then drule ltree_Ret_to_evaluate'>>strip_tac>>gvs[]>>
         drule evaluate_min_clock>>fs[]>>
         pop_assum kall_tac>>
         pop_assum kall_tac>>
         strip_tac>>
         rename1 ‘s with clock := k’>>
         qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
         simp[GSYM LAPPEND_ASSOC]>>
         pairarg_tac>>fs[]>>
         (Cases_on ‘(dec_clock s).clock < k’>>fs[NOT_LESS]
          >- (Cases_on ‘res≠SOME TimeOut’>>fs[]
              >- (drule panPropsTheory.evaluate_add_clock_eq>>strip_tac>>gvs[]>>
                  first_x_assum $ qspec_then ‘k - (dec_clock s).clock’ mp_tac>>
                  simp[]>>simp[dec_clock_def]>>
                  strip_tac>>gvs[]>>
                  ‘unclock (reclock r' with clock := 0) = unclock (s1 with clock := SUC k + s1.clock - s.clock)’
                    by (qpat_assum ‘reclock _ with clock := _ = _’ (fn h => rewrite_tac[h])>>fs[])>>
                  gvs[]>>
                  pop_assum mp_tac>>
                  simp[state_component_equality]>>
                  strip_tac>>gvs[dec_clock_def])>>
              last_assum $ qspec_then ‘SUC k’ mp_tac>>
              impl_tac >- fs[dec_clock_def]>>
              once_rewrite_tac[evaluate_def]>>
              simp[panPropsTheory.eval_upd_clock_eq,dec_clock_def]>>
              qmatch_goalsub_abbrev_tac ‘SND X’>>
              Cases_on ‘X’>>fs[]>>
              ‘r.ffi = r'.ffi’
                by (pop_assum mp_tac>>
                    simp[Once evaluate_def,
                         panPropsTheory.eval_upd_clock_eq]>>
                    rpt CASE_TAC>>fs[empty_locals_defs]>>strip_tac>>gvs[])>>
              strip_tac>>gvs[]>>
              ‘stree_trace query_oracle event_filter r'.ffi
               (to_stree (mrec_sem (h_prog (While e c,r')))) = [||]’
                by (‘r'=unclock (reclock r')’ by simp[]>>
                    pop_assum (fn h => once_rewrite_tac[h])>>
                    ‘(unclock(reclock r')).ffi = (reclock r').ffi’ by simp[]>>
                    pop_assum (fn h => once_rewrite_tac[h])>>
                    ‘(reclock r' with clock := 0).clock = 0’
                      by simp[state_component_equality]>>
                    irule clock_0_imp_LNIL>>
                    gvs[]>>
                    strip_tac>>
                    drule_then drule nonret_imp_timeout>>strip_tac>>gvs[]>>
                    first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[]>>
                    last_x_assum $ qspec_then ‘SUC (k+k')’ assume_tac>>gvs[]>>
                    pop_assum $ assume_tac o SIMP_RULE std_ss [Once evaluate_def]>>
                    pop_assum $ mp_tac o SIMP_RULE std_ss [SimpR“$=”,Once evaluate_def]>>
                    fs[panPropsTheory.eval_upd_clock_eq]>>gvs[]>>
                    impl_tac >- gvs[dec_clock_def]>>
                    pairarg_tac>>gvs[]>>
                    ‘dec_clock (s with clock := SUC (k + k')) = s with clock := k + k'’
                      by simp[dec_clock_def]>>gvs[]>>
                    rev_drule panPropsTheory.evaluate_add_clock_eq>>
                    strip_tac>>gvs[]>>
                    first_x_assum $ qspec_then ‘k'’ $ assume_tac o SIMP_RULE std_ss [Once ADD_COMM]>>
                    gvs[])>>
              gvs[]>>gvs[LAPPEND_NIL_2ND])>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          strip_tac>>gvs[]>>
          first_x_assum $ qspec_then ‘(dec_clock s).clock - k’ assume_tac>>
          gvs[]>>
          ‘s with clock := (dec_clock s).clock = dec_clock s’
            by simp[state_component_equality,dec_clock_def]>>gvs[]>>
          first_x_assum irule>>
          rpt strip_tac>>
          last_x_assum assume_tac>>
          first_assum $ qspec_then ‘SUC (k+k')’ mp_tac>>
          (impl_tac >- gvs[dec_clock_def])>>
          disch_then $ assume_tac o SIMP_RULE std_ss [Once evaluate_def]>>
          pop_assum $ assume_tac o SIMP_RULE std_ss [SimpR“$=”,Once evaluate_def]>>
          gvs[panPropsTheory.eval_upd_clock_eq]>>
          ‘dec_clock (s with clock := SUC (k + k')) = s with clock := k + k'’
            by simp[dec_clock_def]>>gvs[]>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          strip_tac>>gvs[]>>
          first_assum $ qspec_then ‘k'’ $ assume_tac o SIMP_RULE std_ss [Once ADD_COMM]>>
          gvs[]))>>
      (* nonret *)
      ‘(dec_clock s).ffi = s.ffi’ by simp[dec_clock_def]>>fs[]>>
      fs[Abbr‘X’]>>
      drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
      strip_tac>>gvs[]>>
      drule_then drule nonret_imp_timeout'>>strip_tac>>fs[]>>
      first_assum $ qspec_then ‘s.clock - 1’ assume_tac>>
      ‘s with clock := s.clock - 1 = dec_clock s’
        by simp[state_component_equality,dec_clock_def]>>fs[]>>
      simp[Once evaluate_def]>>
      last_x_assum $ qspec_then ‘dec_clock s’ assume_tac>>gvs[]>>
      last_x_assum $ irule>>gvs[]>>
      rpt strip_tac>>
      last_x_assum $ qspec_then ‘SUC k'’ mp_tac>>gvs[]>>
      impl_tac >- fs[dec_clock_def]>>
      simp[SimpR“$=”,Once evaluate_def,
           panPropsTheory.eval_upd_clock_eq]>>
      ‘0 < SUC k'’ by fs[]>>fs[]>>
      ‘dec_clock (s with clock := SUC k') = s with clock := k'’
        by simp[dec_clock_def]>>
      fs[]>>
      first_assum $ qspec_then ‘k'’ assume_tac>>fs[]>>
      simp[Once evaluate_def,panPropsTheory.eval_upd_clock_eq]>>
      ‘dec_clock s with clock := k' = s with clock := k'’
        by (rewrite_tac[dec_clock_def]>>simp[dec_clock_def])>>fs[])
  (* Tick *)
  >~ [‘Tick’]
  >- (fs[h_prog_def]>>
      gvs[mrec_sem_simps,ltree_lift_cases]>>
      fs[Once itree_wbisim_cases])
  (* Call *)
  >~ [‘Call’]
  >- (Cases_on ‘s.clock = 0’>>fs[]
      >- (fs[Once evaluate_def]>>
          rpt (CASE_TAC>>fs[])>>
          TRY (fs[Once mrec_sem_Call_simps,ltree_lift_cases,
                  panPropsTheory.opt_mmap_eval_upd_clock_eq1,
                  panPropsTheory.eval_upd_clock_eq]>>
               fs[Once itree_wbisim_cases]>>NO_TAC)>>
          fs[empty_locals_defs]>>
          ‘∀k'.
            s.ffi.io_events =
            (SND (evaluate (Call caltyp trgt argexps,s with clock := k'))).ffi.io_events’
            by (rpt strip_tac>>Cases_on ‘k'’>>fs[]>>
                ‘s with clock := 0 = s’ by gvs[state_component_equality]>>
                gvs[]>>fs[Once evaluate_def,empty_locals_defs])>>
          drule clock_0_imp_LNIL>>fs[]>>
          strip_tac>>gvs[empty_locals_defs,LAPPEND_NIL_2ND])>>
      (* s.clock ≠ 0 *)
      fs[Once mrec_sem_Call_simps,
         panPropsTheory.eval_upd_clock_eq,ltree_lift_cases,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1,
         mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
      rpt CASE_TAC>>
      fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,
         stree_trace_Vis,ltree_lift_cases,set_var_defs,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1,
         msem_lift_monad_law,to_stree_monad_law,ltree_lift_monad_law,
         LAPPEND_NIL_2ND]>>
      TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
      qmatch_asmsub_abbrev_tac ‘¬(X >>= Y ≈ _)’>>
      Cases_on ‘∃p. X ≈ Ret p’
      (* ret *)
      >- (fs[Abbr‘X’]>>Cases_on ‘p’>>rename1 ‘Ret (q',r')’>>
          imp_res_tac ltree_lift_state_lift'>>fs[]>>
          drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
          gvs[Abbr‘Y’]>>
          gvs[mrec_sem_simps,ltree_lift_cases]>>
          reverse (Cases_on ‘∃ei ex. q' = SOME (Exception ei ex)’)
          >- (Cases_on ‘q'’>>
              fs[h_handle_call_ret_def,ltree_lift_cases,mrec_sem_simps]>>
              TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
              rename1 ‘(SOME x',_)’>>Cases_on ‘x'’>>
              gvs[ltree_lift_cases,mrec_sem_simps,h_handle_call_ret_def]>>
              rpt (FULL_CASE_TAC>>
                   gvs[ltree_lift_cases,mrec_sem_simps])>>
              fs[Once itree_wbisim_cases])>>
          gvs[h_handle_call_ret_def]>>
          rpt (FULL_CASE_TAC>>fs[mrec_sem_simps,ltree_lift_cases])>>
          TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
          imp_res_tac stree_trace_ret_events'>>gvs[]>>
          imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>
          gvs[ltree_lift_cases,to_stree_simps,stree_trace_simps]>>
          drule_then drule ltree_Ret_to_evaluate'>>strip_tac>>gvs[]>>
          drule evaluate_min_clock>>fs[]>>
          pop_assum kall_tac>>
          pop_assum kall_tac>>
          strip_tac>>
          rename1 ‘s with clock := k’>>
          fs[Once evaluate_def]>>gvs[]>>
          TOP_CASE_TAC>>gvs[]>>
          rename1 ‘evaluate (q,dec_clock s with locals := r) = (q'',r'')’>>
          gvs[h_handle_call_ret_def,mrec_sem_simps,to_stree_simps,
              stree_trace_simps,set_var_defs,dec_clock_def]>>
          Cases_on ‘q'' = SOME TimeOut’>>fs[]
          >- (simp[GSYM LAPPEND_ASSOC]>>gvs[]>>
              qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>gvs[]>>
              qpat_abbrev_tac ‘X = stree_trace _ _ _ _’>>
              gvs[empty_locals_defs]>>
              ‘s.clock - 1 < k’
                by (CCONTR_TAC>>fs[NOT_LESS]>>
                    rev_drule panPropsTheory.evaluate_add_clock_eq>>
                    strip_tac>>gvs[]>>
                    first_x_assum $ qspec_then ‘(s.clock - 1) - k’ assume_tac>>
                    gvs[dec_clock_def])>>
              first_assum $ qspec_then ‘SUC k’ mp_tac>>
              impl_tac >- simp[]>>
              rewrite_tac[Once evaluate_def]>>
              fs[panPropsTheory.eval_upd_clock_eq,
                 panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
              simp[dec_clock_def]>>strip_tac>>gvs[set_var_defs]>>
              ‘∀w. ¬(ltree_lift query_oracle (reclock r').ffi
                                (mrec_sem (h_prog
                                           (r'³',r' with locals := s.locals |+ (q'³',ex)))) ≈
                                Ret w)’
                by simp[]>>
              drule_then drule nonret_imp_timeout'>>gvs[]>>
              strip_tac>>
              first_x_assum $ qspec_then ‘0’ assume_tac>>gvs[]>>
              qabbrev_tac ‘t = s with <| locals:=r;clock:=s.clock -1|>’>>
              ‘∃m. k = t.clock + m’
                by (simp[Abbr‘t’]>>
                    drule (GSYM LESS_ADD)>>
                    strip_tac>>gvs[]>>
                    ‘1 ≤ p + s.clock’
                      by (imp_res_tac LESS_OR>>fs[])>>
                    metis_tac[ADD_EQ_SUB])>>
              ‘(SND (evaluate (q,t))).ffi.io_events ≼
               (SND (evaluate (q,t with clock := t.clock + m'))).ffi.io_events’
                by (irule panPropsTheory.evaluate_add_clock_io_events_mono)>>
              gvs[Abbr‘t’]>>fs[IS_PREFIX_APPEND]>>
              qpat_x_assum ‘_ = (SOME TimeOut,s')’ assume_tac>>
              drule panPropsTheory.evaluate_io_events_mono>>
              fs[IS_PREFIX_APPEND]>>
              strip_tac>>fs[]>>
              ‘X = LNIL’ by
                (fs[Abbr‘X’]>>
                 qmatch_goalsub_abbrev_tac ‘h_prog (_,t)’>>
                 ‘t=unclock (reclock t)’ by simp[Abbr‘t’]>>
                 pop_assum (fn h => once_rewrite_tac[h])>>
                 ‘r'.ffi = (reclock t).ffi’ by simp[Abbr‘t’]>>
                 pop_assum (fn h => once_rewrite_tac[h])>>
                 irule clock_0_imp_LNIL>>gvs[Abbr‘t’]>>
                 strip_tac>>
                 ‘∀w. ¬(ltree_lift query_oracle (reclock r').ffi
                     (mrec_sem (h_prog
                           (r'³',r' with locals := s.locals |+ (q'³',ex)))) ≈
                                   Ret w)’
                   by simp[]>>
                 drule_then drule nonret_imp_timeout'>>gvs[]>>
                 strip_tac>>
                 first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[]>>
                 first_x_assum $ qspec_then ‘SUC k' + (m' + s.clock - 1)’ assume_tac>>
                 pop_assum $ mp_tac o SIMP_RULE std_ss [SimpR“$=”,Once evaluate_def]>>
                 fs[panPropsTheory.eval_upd_clock_eq,
                    panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
                 gvs[dec_clock_def,ADD1,set_var_defs]>>
                 TOP_CASE_TAC>>gvs[]>>
                 rev_drule panPropsTheory.evaluate_add_clock_eq>>
                 strip_tac>>gvs[])>>
              gvs[empty_locals_defs,LAPPEND_NIL_2ND])>>
          ‘k < s.clock’
            by (CCONTR_TAC>>fs[NOT_LESS]>>
                drule panPropsTheory.evaluate_add_clock_eq>>
                strip_tac>>gvs[]>>
                first_x_assum $ qspec_then ‘k - (dec_clock s).clock’ assume_tac>>
                gvs[dec_clock_def]>>
                fs[state_component_equality])>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          strip_tac>>gvs[]>>
          first_x_assum $ qspec_then ‘(dec_clock s).clock - k’ assume_tac>>
          gvs[dec_clock_def,set_var_defs]>>
          gvs[h_handle_call_ret_def,mrec_sem_simps,to_stree_simps,
              stree_trace_simps,set_var_defs]>>
          simp[GSYM LAPPEND_ASSOC]>>
          first_x_assum irule>>
          rpt strip_tac>>gvs[]>>
          first_x_assum $ qspec_then ‘k' + k + 1’ assume_tac>>
          fs[Once evaluate_def]>>
          fs[panPropsTheory.opt_mmap_eval_upd_clock_eq1,
             panPropsTheory.eval_upd_clock_eq]>>
          gvs[dec_clock_def]>>
          FULL_CASE_TAC>>gvs[]>>
          qhdtm_x_assum ‘evaluate’ assume_tac>>
          qpat_x_assum ‘evaluate _ = (_, reclock _ with clock := 0)’ mp_tac>>
          drule panPropsTheory.evaluate_add_clock_eq>>
          strip_tac>>gvs[]>>
          strip_tac>>gvs[]>>
          first_x_assum $ qspec_then ‘SUC (k' + k - s.clock)’ assume_tac>>
          gvs[dec_clock_def,set_var_defs,ADD1])>>
      (* nonret *)
      ‘(dec_clock s).ffi = s.ffi’ by simp[dec_clock_def]>>fs[]>>
      fs[Abbr‘X’]>>
      drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
      strip_tac>>gvs[]>>
      drule_then drule nonret_imp_timeout'>>strip_tac>>fs[]>>
      first_assum $ qspec_then ‘s.clock-1’ assume_tac>>
      ‘s with clock := s.clock - 1 = dec_clock s’
        by simp[state_component_equality,dec_clock_def]>>fs[]>>
      irule EQ_TRANS>>
      first_x_assum $ irule_at Any>>
      last_x_assum assume_tac>>
      conj_tac >-
       (rpt strip_tac>>
        first_x_assum $ qspec_then ‘SUC k'’ mp_tac>>
        simp[Once evaluate_def,empty_locals_defs]>>fs[dec_clock_def]>>
        strip_tac>>
        once_rewrite_tac[evaluate_def]>>
        simp[panPropsTheory.eval_upd_clock_eq,
             panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
        fs[dec_clock_def]>>
        TOP_CASE_TAC>>gvs[]>>
        first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[empty_locals_defs])>>
      simp[Once evaluate_def,empty_locals_defs]>>fs[dec_clock_def])
  (* DecCall *)
  >~ [‘DecCall’]
  >- (Cases_on ‘s.clock = 0’>>fs[]
      >- (fs[Once evaluate_def]>>
          rpt (CASE_TAC>>fs[])>>
          TRY (fs[Once mrec_sem_DecCall_simps,ltree_lift_cases,
                  panPropsTheory.opt_mmap_eval_upd_clock_eq1,
                  panPropsTheory.eval_upd_clock_eq]>>
               fs[Once itree_wbisim_cases]>>NO_TAC)>>
          fs[empty_locals_defs]>>
          ‘∀k'.
            s.ffi.io_events =
            (SND (evaluate (DecCall rt shape trgt argexps prog1,s with clock := k'))).ffi.io_events’
            by (rpt strip_tac>>Cases_on ‘k'’>>fs[]>>
                ‘s with clock := 0 = s’ by gvs[state_component_equality]>>
                gvs[]>>fs[Once evaluate_def,empty_locals_defs])>>
          drule clock_0_imp_LNIL>>fs[]>>
          strip_tac>>gvs[empty_locals_defs,LAPPEND_NIL_2ND])>>
      (* s.clock ≠ 0 *)
      fs[Once mrec_sem_DecCall_simps,
         panPropsTheory.eval_upd_clock_eq,ltree_lift_cases,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1,
         mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
      rpt CASE_TAC>>
      fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,
         stree_trace_Vis,ltree_lift_cases,set_var_defs,
         panPropsTheory.opt_mmap_eval_upd_clock_eq1,
         msem_lift_monad_law,to_stree_monad_law,ltree_lift_monad_law,
         LAPPEND_NIL_2ND]>>
      TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
      qmatch_asmsub_abbrev_tac ‘¬(X >>= Y ≈ _)’>>
      Cases_on ‘∃p. X ≈ Ret p’
      (* ret *)
      >- (fs[Abbr‘X’]>>Cases_on ‘p’>>rename1 ‘Ret (q',r')’>>
          imp_res_tac ltree_lift_state_lift'>>fs[]>>
          drule_then drule (iffLR ret_bind_nonret)>>strip_tac>>
          gvs[Abbr‘Y’]>>
          gvs[mrec_sem_simps,ltree_lift_cases]>>
          reverse (Cases_on ‘∃retv st. q' = SOME (Return retv)’)
          >- (Cases_on ‘q'’>>
              fs[h_handle_deccall_ret_def,ltree_lift_cases,mrec_sem_simps]>>
              TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
              rename1 ‘(SOME x',_)’>>Cases_on ‘x'’>>
              gvs[ltree_lift_cases,mrec_sem_simps,h_handle_deccall_ret_def]>>
              rpt (FULL_CASE_TAC>>
                   gvs[ltree_lift_cases,mrec_sem_simps])>>
              fs[Once itree_wbisim_cases]) >>
          gvs[h_handle_deccall_ret_def,mrec_sem_simps,
              to_stree_simps,stree_trace_simps,
              msem_lift_monad_law,to_stree_monad_law,
              ltree_lift_monad_law, LAPPEND_NIL_2ND,
              stree_trace_Vis,ltree_lift_cases] >>
          rpt (FULL_CASE_TAC>>fs[mrec_sem_simps,ltree_lift_cases])
          >- (imp_res_tac stree_trace_ret_events'>>gvs[]>>
              imp_res_tac (INST_TYPE [delta|->alpha] stree_trace_bind_append)>>
              gvs[ltree_lift_cases,to_stree_simps,stree_trace_simps]>>
              drule_then drule ltree_Ret_to_evaluate'>>strip_tac>>gvs[]>>
              drule evaluate_min_clock>>fs[]>>
              pop_assum kall_tac>>
              pop_assum kall_tac>>
              strip_tac>>
              rename1 ‘s with clock := k’>>
              fs[Once evaluate_def]>>gvs[]>>
              TOP_CASE_TAC>>gvs[]>>
              rename1 ‘evaluate (q,dec_clock s with locals := r) = (q'',r'')’>>
              gvs[h_handle_deccall_ret_def,mrec_sem_simps,to_stree_simps,
                  stree_trace_simps,set_var_defs,dec_clock_def]>>
              gvs[h_handle_deccall_ret_def,mrec_sem_simps,
                  to_stree_simps,stree_trace_simps,
                  msem_lift_monad_law,to_stree_monad_law,
                  ltree_lift_monad_law, LAPPEND_NIL_2ND,
                  stree_trace_Vis,ltree_lift_cases] >>
              gvs[ltree_lift_cases, o_DEF, mrec_sem_simps,
                  ltree_lift_monad_law, msem_lift_monad_law, ELIM_UNCURRY] >>
              qmatch_asmsub_abbrev_tac ‘_ >>= Y’ >>
              ‘∀w. ¬(ltree_lift query_oracle r'.ffi
                                (mrec_sem (h_prog (prog1,r' with locals := s.locals |+ (rt,retv)))) ≈ Ret w)’
                by (CCONTR_TAC >> gvs[] >>
                    Cases_on ‘w’ >> fs[] >>
                    imp_res_tac ret_bind_nonret >>
                    pop_assum kall_tac >>
                    unabbrev_all_tac >>
                    fs[Once itree_wbisim_cases]) >>
              drule_then assume_tac (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree) >>
              gvs[to_stree_simps] >>
              Cases_on ‘q'' = SOME TimeOut’>>fs[]
              >- (simp[GSYM LAPPEND_ASSOC]>>gvs[]>>
                  qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>gvs[]>>
                  qpat_abbrev_tac ‘X = stree_trace _ _ _ _’>>
                  gvs[empty_locals_defs]>>
                  ‘s.clock - 1 < k’
                    by (CCONTR_TAC>>fs[NOT_LESS]>>
                        rev_drule panPropsTheory.evaluate_add_clock_eq>>
                        strip_tac>>gvs[]>>
                        first_x_assum $ qspec_then ‘(s.clock - 1) - k’ assume_tac>>
                        gvs[dec_clock_def])>>
                  first_assum $ qspec_then ‘SUC k’ mp_tac>>
                  impl_tac >- simp[]>>
                  rewrite_tac[Once evaluate_def]>>
                  fs[panPropsTheory.eval_upd_clock_eq,
                     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
                  simp[dec_clock_def]>>strip_tac>>gvs[set_var_defs]>>
                  ‘∀w. ¬(ltree_lift query_oracle (reclock r').ffi
                                    (mrec_sem (h_prog (prog1,r' with locals := s.locals |+ (rt,retv)))) ≈ Ret w)’
                    by simp[] >>
                  drule_then drule nonret_imp_timeout'>>gvs[ELIM_UNCURRY]>>
                  strip_tac>>
                  first_x_assum $ qspec_then ‘0’ assume_tac>>gvs[]>>
                  qabbrev_tac ‘t = s with <| locals:=r;clock:=s.clock -1|>’>>
                  ‘∃m. k = t.clock + m’
                    by (simp[Abbr‘t’]>>
                        drule (GSYM LESS_ADD)>>
                        strip_tac>>gvs[]>>
                        ‘1 ≤ p + s.clock’
                          by (imp_res_tac LESS_OR>>fs[])>>
                        metis_tac[ADD_EQ_SUB])>>
                  ‘(SND (evaluate (q,t))).ffi.io_events ≼
                   (SND (evaluate (q,t with clock := t.clock + m'))).ffi.io_events’
                    by (irule panPropsTheory.evaluate_add_clock_io_events_mono)>>
                  gvs[Abbr‘t’]>>fs[IS_PREFIX_APPEND]>>
                  qpat_x_assum ‘_ = (SOME TimeOut,s')’ assume_tac>>
                  drule panPropsTheory.evaluate_io_events_mono>>
                  fs[IS_PREFIX_APPEND]>>
                  strip_tac>>fs[]>>
                  ‘X = LNIL’ by
                    (fs[Abbr‘X’]>>
                     qmatch_goalsub_abbrev_tac ‘h_prog (_,t)’>>
                     ‘t=unclock (reclock t)’ by simp[Abbr‘t’]>>
                     pop_assum (fn h => once_rewrite_tac[h])>>
                     ‘r'.ffi = (reclock t).ffi’ by simp[Abbr‘t’]>>
                     pop_assum (fn h => once_rewrite_tac[h])>>
                     irule clock_0_imp_LNIL>>gvs[Abbr‘t’]>>
                     strip_tac>>
                     ‘∀w. ¬(ltree_lift query_oracle (reclock r').ffi
                                       (mrec_sem (h_prog
                                                  (prog1,r' with locals := s.locals |+ (rt,retv)))) ≈
                                       Ret w)’
                       by simp[]>>
                     drule_then drule nonret_imp_timeout'>>gvs[]>>
                     strip_tac>>
                     first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[]>>
                     first_x_assum $ qspec_then ‘SUC k' + (m' + s.clock - 1)’ assume_tac>>
                     pop_assum $ mp_tac o SIMP_RULE std_ss [SimpR“$=”,Once evaluate_def]>>
                     fs[panPropsTheory.eval_upd_clock_eq,
                        panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
                     gvs[dec_clock_def,ADD1,set_var_defs]>>
                     TOP_CASE_TAC>>gvs[]>>
                     rev_drule panPropsTheory.evaluate_add_clock_eq>>
                     strip_tac>>gvs[]) >>
                  gvs[empty_locals_defs,LAPPEND_NIL_2ND]) >>
              ‘k < s.clock’
                by (CCONTR_TAC>>fs[NOT_LESS]>>
                    drule panPropsTheory.evaluate_add_clock_eq>>
                    strip_tac>>gvs[]>>
                    first_x_assum $ qspec_then ‘k - (dec_clock s).clock’ assume_tac>>
                    gvs[dec_clock_def]>>
                    fs[state_component_equality])>>
              rev_drule panPropsTheory.evaluate_add_clock_eq>>
              strip_tac>>gvs[]>>
              first_x_assum $ qspec_then ‘(dec_clock s).clock - k’ assume_tac>>
              gvs[dec_clock_def,set_var_defs]>>
              gvs[h_handle_deccall_ret_def,mrec_sem_simps,to_stree_simps,
                  stree_trace_simps,set_var_defs]>>
              simp[GSYM LAPPEND_ASSOC]>>
              first_x_assum irule>>
              rpt strip_tac>>gvs[]>>
              first_x_assum $ qspec_then ‘k' + k + 1’ assume_tac>>
              fs[Once evaluate_def]>>
              fs[panPropsTheory.opt_mmap_eval_upd_clock_eq1,
                 panPropsTheory.eval_upd_clock_eq]>>
              gvs[dec_clock_def]>>
              FULL_CASE_TAC>>gvs[ELIM_UNCURRY]>>
              qhdtm_x_assum ‘evaluate’ mp_tac>>
              qhdtm_x_assum ‘evaluate’ assume_tac>>
              drule panPropsTheory.evaluate_add_clock_eq>>
              strip_tac>>gvs[]>>
              strip_tac>>gvs[]>>
              first_x_assum $ qspec_then ‘SUC (k' + k - s.clock)’ assume_tac>>
              gvs[dec_clock_def,set_var_defs,ADD1]) >>
          fs[Once itree_wbisim_cases]) >>
      (* nonret *)
      ‘(dec_clock s).ffi = s.ffi’ by simp[dec_clock_def]>>fs[]>>
      fs[Abbr‘X’]>>
      drule (INST_TYPE [delta|->alpha] ltree_lift_nonret_bind_stree)>>
      strip_tac>>gvs[]>>
      drule_then drule nonret_imp_timeout'>>strip_tac>>fs[]>>
      first_assum $ qspec_then ‘s.clock-1’ assume_tac>>
      ‘s with clock := s.clock - 1 = dec_clock s’
        by simp[state_component_equality,dec_clock_def]>>fs[]>>
      irule EQ_TRANS>>
      first_x_assum $ irule_at Any>>
      last_x_assum assume_tac>>
      conj_tac >-
       (rpt strip_tac>>
        first_x_assum $ qspec_then ‘SUC k'’ mp_tac>>
        simp[Once evaluate_def,empty_locals_defs]>>fs[dec_clock_def]>>
        strip_tac>>
        once_rewrite_tac[evaluate_def]>>
        simp[panPropsTheory.eval_upd_clock_eq,
             panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
        fs[dec_clock_def]>>
        TOP_CASE_TAC>>gvs[]>>
        first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[empty_locals_defs])>>
      simp[Once evaluate_def,empty_locals_defs]>>fs[dec_clock_def])>>
  (* ExtCall *)
  fs[h_prog_def,h_prog_ext_call_def,
     panPropsTheory.eval_upd_clock_eq,ltree_lift_cases,
     mrec_sem_simps,to_stree_simps,stree_trace_simps]>>
  rpt (PURE_CASE_TAC>>
       fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,
          stree_trace_Vis,ltree_lift_cases,LAPPEND_NIL_2ND,
          msem_lift_monad_law,to_stree_monad_law,ltree_lift_monad_law])>>
  TRY (fs[Once itree_wbisim_cases]>>NO_TAC)>>
  pairarg_tac>>fs[]>>FULL_CASE_TAC>>
  fs[mrec_sem_simps,to_stree_simps,stree_trace_simps,
     stree_trace_Vis,ltree_lift_cases,
     msem_lift_monad_law,to_stree_monad_law,ltree_lift_monad_law]>>
  fs[Once itree_wbisim_cases]
QED


(* Final goal:

   1. For every path that can be generated frong

   that produces an equivalent result in the functional semantics.
   2. For every oracle, there is a path producing a corresponding result in the ITree semantics.
 *)

Theorem itree_semantics_corres:
  good_dimindex(:α) ⇒
  fbs_semantics_beh s prog = itree_semantics_beh s (prog:α prog)
Proof
  rw [fbs_semantics_beh_def]
  >- (DEEP_INTRO_TAC some_intro >> reverse $ rw []
      >- (gvs [ELIM_UNCURRY]) >>
      pairarg_tac >> gvs [] >>
      CONV_TAC SYM_CONV >>
      qpat_x_assum ‘FST _ ≠ _’ kall_tac >>
      ‘s = unclock(reclock s with clock := k')’
        by(gvs[panItreeSemTheory.reclock_def,
               panItreeSemTheory.unclock_def,
               panItreeSemTheory.bstate_component_equality]) >>
      pop_assum $ PURE_ONCE_REWRITE_TAC o single >>
      metis_tac[itree_semantics_corres_evaluate])
  >- (CONV_TAC SYM_CONV >> fs [] >>
      rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >>
      reverse CONJ_TAC
      (* Case: ltree_lift and evaluate diverge... *)
      >- (rw [FORALL_PROD] >>fs[GSYM FORALL_PROD]>>
          irule (iffLR lprefix_lubTheory.build_prefix_lub_intro)>>
          conj_asm2_tac
          >- (irule lprefix_lubTheory.lprefix_lub_is_chain>>metis_tac[])>>
          simp[lprefix_lubTheory.lprefix_lub_def]>>fs[]>>
          conj_asm1_tac>>rpt strip_tac>>gvs[]
          >- (first_x_assum $ qspec_then ‘k’ assume_tac>>
              irule evaluate_stree_trace_LPREFIX>>gvs[]>>
              qmatch_asmsub_abbrev_tac ‘FST X’>>Cases_on ‘X’>>
              gvs[]>>metis_tac[])>>
          (* least upper bound *)
          Cases_on ‘∀n. (∃k. less_opt n (SOME (LENGTH (SND (evaluate(prog,reclock s with clock := k))).ffi.io_events)))’>>fs[]
          >- fs[LPREFIX_NTH]>>
          (* evaluate traces are bounded *)
          fs[PULL_EXISTS]>>
          dxrule not_less_opt_lemma>>strip_tac>>gvs[]>>
          qabbrev_tac ‘x=reclock s with clock := k'’>>
          ‘∀k. x.clock < k ⇒
               (SND (evaluate (prog,x))).ffi.io_events =
               (SND (evaluate (prog,x with clock := k))).ffi.io_events’
            by (rpt strip_tac>>
                first_x_assum $ qspec_then ‘k’ assume_tac>>
                qspecl_then [‘prog’,‘x’,‘k-x.clock’] assume_tac(panPropsTheory.evaluate_add_clock_io_events_mono)>>
                rfs[Abbr‘x’]>>
                gvs[GSYM IS_PREFIX_LENGTH_ANTI])>>
          drule bounded_trace_eq>>gvs[Abbr‘x’])
      (* False cases: ltree_lift converges and evalate diverges... *)
      >- (simp [FORALL_PROD] >> rw [] >>
          spose_not_then kall_tac >>
          last_x_assum mp_tac >> simp [] >>
          drule_at (Pos last) ltree_Ret_to_evaluate >>
          rw [PULL_EXISTS] >>
          qexists_tac ‘k’ >> rw []))
QED

(* A path p (aka. maximal answer trace) is an (:'a semtree_ans llist)
 that describes a particular path in an itree. Such a path is valid iff
 is_valid_path t p = T
*)
CoInductive is_valid_path:
  (∀x. is_valid_path (Ret x) [||]) ∧
  (∀t p. is_valid_path t p ⇒ is_valid_path (Tau t) p) ∧
  (∀e k t. is_valid_path t p ∧ (∃a. k a = t) ⇒ is_valid_path (Vis e k) (a:::p))
End

Datatype:
  atrace_ffi =
  <| alist : 'a semtree_ans llist |>
End

(* Inverse of stree_trace *)
(* Given an llist of answers (not events), produces an oracle that
 returns those answers in the order given and hence which would produce the same
         path as the given llist.
 *)

Definition stree_trace_oracle_def:
  (stree_trace_oracle : 'a atrace_ffi oracle) s st conf bytes =
     case st.alist of
       (FFI_return st' bytes):::as => Oracle_return (st with alist := as) bytes
     | (FFI_final (Final_event s' conf' bytes' outcome)):::as => Oracle_final outcome
     | LNIL => Oracle_final FFI_failed
End

Theorem itree_semantics_completeness:
  good_dimindex(:α) ⇒
  ∀(path : 'a semtree_ans llist).
    is_valid_path (to_stree (mrec_sem (h_prog (prog,s)))) path ⇒
    ∃(or : 'a atrace_ffi oracle).
      let ffi_or_state = <| oracle := or; ffi_state := <| alist := path |>; io_events := [] |> in
        (build_lprefix_lub (IMAGE (λk. fromList (SND (evaluate (prog,((reclock s) with <| clock := k; ffi := ffi_or_state |>)))).ffi.io_events) UNIV) =
         stree_trace query_oracle event_filter ffi_or_state (to_stree (mrec_sem (h_prog (prog,s))))) ∧
        case toList path of
             SOME finPath =>
          let (r,s') = evaluate (prog,(reclock s) with ffi := ffi_or_state) in
            ltree_lift query_oracle ffi_or_state (mrec_sem (h_prog (prog,s))) ≈ Ret (r,unclock s')
            | NONE => T
Proof
  rw [] >>
  qexists_tac ‘stree_trace_oracle’ >> reverse $ rw []
  >- (Cases_on ‘toList path’ >> rw [] >>
      qpat_x_assum ‘is_valid_path _ _’ mp_tac >>
      pairarg_tac >> rw [] >>
      qpat_x_assum ‘evaluate _ = (r,s')’ mp_tac >>
      MAP_EVERY qid_spec_tac [‘s’,‘r’,‘s'’,‘prog’] >>
      recInduct evaluate_ind >> rw []
      >~ [‘Skip’]
      >- (gvs [Once evaluate_def] >>
          rw [h_prog_def,mrec_sem_simps,ltree_lift_cases,
              itree_wbisim_neq] >>
          (* TODO: Reduces to proving itree state is the same as FBS state which has the specific oracle
             implanted. *)
          (* Not sure if this is true and whether we want to take another approach. *)
          cheat) >>
      cheat)
  >- (cheat)
QED

val _ = export_theory();
