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
  Ret x ≈ u ⇒ u = Ret x
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

(* this lemma appears to be about a combinator we no longer use
Theorem mrec_sem_leaf_compos:
  leaf_of ffis (mrec_sem (rh seed)) = Return x ⇒
  leaf_of ffis (mrec_sem (Vis (INL seed) k)) = leaf_of ffis (mrec_sem (k x))
Proof
  cheat
QED
*)

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
      | NONE => SemDiverge (fromList(s.ffi.io_events) ++ₗ stree_trace query_oracle s.ffi (to_stree (mrec_sem (h_prog (prog,s)))))
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
  stree_trace f fs (Tau t) = stree_trace f fs t ∧
  stree_trace f fs (Ret r) = [||]
  (* TODO: Vis *)
Proof
  rw[stree_trace_def] >>
  rw[Once LUNFOLD]
QED

Theorem ltree_lift_nonret_bind_stree:
  (∀x. ¬(ltree_lift f st p ≈ Ret x))
  ⇒ stree_trace f st (to_stree p >>= k) = stree_trace f st $ to_stree p
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

Theorem itree_semantics_beh_Dec:
  itree_semantics_beh s (Dec vname e prog) =
  case eval (reclock s) e of
    NONE => SemFail
  | SOME value =>
      case itree_semantics_beh (s with locals := s.locals |+ (vname,value)) prog of
      | SemTerminate (res,s') ffis =>
          SemTerminate (res,s' with locals := res_var s'.locals (vname,FLOOKUP s.locals vname)) ffis
      | res => res
Proof
  rw[itree_semantics_beh_def] >>
  Cases_on ‘eval (reclock s) e’ >>
  gvs[h_prog_def,h_prog_rule_dec_def,mrec_sem_simps,ltree_lift_cases,
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
  gvs[h_prog_def,h_prog_rule_cond_def,mrec_sem_simps,ltree_lift_cases,
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

Theorem bind_FUNPOW_eqn:
  FUNPOW Tau n (Ret x) >>= k =
  FUNPOW Tau n (k x)
Proof
  Induct_on ‘n’ >>
  gvs[FUNPOW_SUC]
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
  rw[h_prog_def,h_prog_rule_while_def] >>
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
  Induct
  >~ [‘Dec’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_dec_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          h_prog_rule_dec_def,
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
         h_prog_rule_cond_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          h_prog_rule_dec_def,
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
          bind_FUNPOW_eqn,FUNPOW_ADD] >>
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
         h_prog_rule_ext_call_def,
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
  >~ [‘ShMem’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_sh_mem_def,
         oneline h_prog_rule_sh_mem_op_def,
         h_prog_rule_sh_mem_load_def,
         h_prog_rule_sh_mem_store_def,
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
         h_prog_rule_call_def,
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
          tau_eq_funpow_tau
         ] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          bind_FUNPOW_eqn] >>
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
  >~ [‘Seq’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_seq_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      gvs[tau_eq_funpow_tau] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          bind_FUNPOW_eqn,FUNPOW_ADD] >>
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
         h_prog_rule_raise_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau] >>
      rpt(IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
              ltree_lift_state_simps,empty_locals_defs])) >>
  rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
     h_prog_rule_store_def,
     h_prog_rule_store_byte_def,
     h_prog_rule_assign_def,
     h_prog_rule_raise_def,
     h_prog_rule_return_def,
     ltree_lift_state_simps,
     ret_eq_funpow_tau
    ] >>
  rpt (PURE_TOP_CASE_TAC >>
       gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
           ltree_lift_state_simps,ret_eq_funpow_tau,
           tau_eq_funpow_tau,empty_locals_defs])
QED

Theorem stree_trace_Vis:
  stree_trace f st (Vis e k) =
  let (a,rbytes,st') = f st e in
    make_io_event e rbytes:::stree_trace f st' (k a)
Proof
  rw[stree_trace_def] >>
  rw[Once LUNFOLD] >>
  rw[ELIM_UNCURRY]
QED

Theorem stree_trace_bind_append:
  ltree_lift f st t ≈ Ret x
  ⇒ stree_trace f st (to_stree t >>= k) =
    stree_trace f st(to_stree t) ++ₗ stree_trace f (ltree_lift_state f st t) (k x)
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
      stree_trace_Vis,ltree_lift_state_simps,ltree_lift_Vis_alt,ELIM_UNCURRY]
QED

Theorem stree_trace_ret_events:
  ltree_lift query_oracle st.ffi (mrec_sem (h_prog (p,st))) ≈ Ret (res,st') ∧
  res ≠ SOME Error
  ⇒ fromList st'.ffi.io_events =
    fromList st.ffi.io_events ++ₗ stree_trace query_oracle st.ffi (to_stree (mrec_sem (h_prog (p,st))))
Proof
  cheat (*
  strip_tac >> dxrule itree_wbisim_Ret_FUNPOW >>
  simp[PULL_EXISTS] >>
  MAP_EVERY qid_spec_tac [‘p’,‘st’,‘res’,‘st'’] >>
  Induct_on ‘n’ using COMPLETE_INDUCTION >>
  CONV_TAC $ RESORT_FORALL_CONV rev >>
  Induct
  >~ [‘Dec’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_dec_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          h_prog_rule_dec_def,
          ltree_lift_state_simps,ret_eq_funpow_tau,
          tau_eq_funpow_tau,
          to_stree_simps,stree_trace_simps,
          LAPPEND_NIL_2ND
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
      rw[mrec_sem_simps,ltree_lift_state_simps] >>
      cheat
     )
  >~ [‘If’]
  >- (cheat >>
      rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_cond_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      PURE_TOP_CASE_TAC >>
      gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
          h_prog_rule_dec_def,
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
  >- (cheat
      (*rw[ltree_lift_cases,mrec_sem_simps,
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
          bind_FUNPOW_eqn,FUNPOW_ADD] >>
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
      simp[] *))
  >~ [‘ExtCall’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_ext_call_def,
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
          LAPPEND_NIL_2ND
         ] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[empty_locals_defs]) >>
      gvs[stree_trace_Vis,make_io_event_def,
          ffiTheory.call_FFI_def,AllCaseEqs(),
          query_oracle_def,to_stree_simps,mrec_sem_simps,stree_trace_simps,
          GSYM LAPPEND_fromList
         ]
     )
  >~ [‘ShMem’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_sh_mem_def,
         oneline h_prog_rule_sh_mem_op_def,
         h_prog_rule_sh_mem_load_def,
         h_prog_rule_sh_mem_store_def,
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
          LAPPEND_NIL_2ND
         ] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[empty_locals_defs]) >>
      gvs[stree_trace_Vis,make_io_event_def,
          ffiTheory.call_FFI_def,AllCaseEqs(),
          query_oracle_def,to_stree_simps,mrec_sem_simps,stree_trace_simps,
          GSYM LAPPEND_fromList])
  >~ [‘Call’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_call_def,
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
          tau_eq_funpow_tau
         ] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          bind_FUNPOW_eqn] >>
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
  >~ [‘Seq’]
  >- (rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
         h_prog_rule_seq_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau
        ] >>
      gvs[tau_eq_funpow_tau] >>
      gvs[msem_lift_monad_law,ltree_lift_monad_law] >>
      drule FUNPOW_Tau_bind_thm >>
      rw[] >>
      pairarg_tac >>
      gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
          bind_FUNPOW_eqn,FUNPOW_ADD] >>
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
         h_prog_rule_raise_def,
         ltree_lift_state_simps,
         ret_eq_funpow_tau] >>
      rpt(IF_CASES_TAC ORELSE PURE_TOP_CASE_TAC >>
          gvs[mrec_sem_simps,ltree_lift_cases,ret_eq_funpow_tau,
              ltree_lift_state_simps,empty_locals_defs])) >>
  rw[ltree_lift_cases,h_prog_def,mrec_sem_simps,
     h_prog_rule_store_def,
     h_prog_rule_store_byte_def,
     h_prog_rule_assign_def,
     h_prog_rule_raise_def,
     h_prog_rule_return_def,
     ltree_lift_state_simps,
     ret_eq_funpow_tau
    ] >>
  rpt (PURE_TOP_CASE_TAC >>
       gvs[ltree_lift_cases,h_prog_def,mrec_sem_simps,
           ltree_lift_state_simps,ret_eq_funpow_tau,
           tau_eq_funpow_tau,empty_locals_defs]) *)
QED

Theorem itree_semantics_beh_Seq:
  itree_semantics_beh s (Seq p1 p2) =
  case itree_semantics_beh s p1 of
    SemTerminate (NONE, s') _ =>
      itree_semantics_beh s' p2
  | res => res
Proof
  rw[itree_semantics_beh_def,h_prog_def,h_prog_rule_seq_def,mrec_sem_simps,ltree_lift_cases,
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
      drule_then (qspec_then ‘k1’ assume_tac) stree_trace_bind_append >>
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

Theorem itree_semantics_beh_While:
  itree_semantics_beh s (While e p) =
  case eval (reclock s) e of
    SOME(ValWord w) =>
      (if w = 0w then
         SemTerminate (NONE,s) s.ffi.io_events
       else
         (case itree_semantics_beh s p of
            SemTerminate (NONE,s') _ => itree_semantics_beh s' (While e p)
          | SemTerminate (SOME Break, s') _ => SemTerminate (NONE,s') s'.ffi.io_events
          | SemTerminate (SOME Continue, s') _ => itree_semantics_beh s' (While e p)
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
      drule_then (qspec_then ‘k’ mp_tac) $ SIMP_RULE (srw_ss()) [FORALL_PROD] ltree_lift_nonret_bind >>
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
          drule_then (qspec_then ‘k1’ assume_tac) stree_trace_bind_append >>
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
          drule_then (qspec_then ‘k1’ assume_tac) stree_trace_bind_append >>
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
  (itree_semantics_beh s Skip = SemTerminate (NONE, s) s.ffi.io_events) ∧
  (itree_semantics_beh s (Assign v src) =
   case eval (reclock s) src of
     NONE => SemFail
   | SOME val =>
       if is_valid_value s.locals v val then
         SemTerminate (NONE, s with locals := s.locals |+ (v,val)) s.ffi.io_events
       else SemFail
  ) ∧
  (itree_semantics_beh s (Store dst src) =
   case (eval (reclock s) dst,eval (reclock s) src) of
   | (SOME (ValWord addr),SOME value) =>
       (case mem_stores addr (flatten value) s.memaddrs s.memory of
          NONE => SemFail
        | SOME m => SemTerminate (NONE,s with memory := m) s.ffi.io_events)
   | _ => SemFail) ∧
  (itree_semantics_beh s (StoreByte dst src) =
   case (eval (reclock s) dst,eval (reclock s) src) of
   | (SOME (ValWord addr),SOME (ValWord w)) =>
       (case mem_store_byte s.memory s.memaddrs s.be addr (w2w w) of
          NONE => SemFail
        | SOME m => SemTerminate (NONE,s with memory := m) s.ffi.io_events)
   | _ => SemFail) ∧
  (itree_semantics_beh s (Return e) =
   case eval (reclock s) e of
         NONE => SemFail
       | SOME value =>
         if size_of_shape (shape_of value) ≤ 32 then
           SemTerminate (SOME (Return value),empty_locals s) s.ffi.io_events
         else SemFail) ∧
  (itree_semantics_beh s (Raise eid e) =
   case (FLOOKUP s.eshapes eid,eval (reclock s) e) of
          | (SOME sh,SOME value) =>
            (if shape_of value = sh ∧ size_of_shape (shape_of value) ≤ 32 then
              SemTerminate (SOME (Exception eid value),empty_locals s) s.ffi.io_events
             else SemFail)
          | _ => SemFail) ∧
  (itree_semantics_beh s Break = SemTerminate (SOME Break,s) s.ffi.io_events
   ) ∧
  (itree_semantics_beh s Continue = SemTerminate (SOME Continue,s) s.ffi.io_events
   ) ∧
  (itree_semantics_beh s Tick = SemTerminate (NONE,s) s.ffi.io_events
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
      >- (rpt(PURE_CASE_TAC >> gvs[]) >>
          fs [h_prog_def,h_prog_rule_assign_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_rule_assign_def,
          mrec_sem_simps] >>
      rpt(PURE_CASE_TAC >> gvs[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (rpt(PURE_CASE_TAC >> gvs[]) >>
          fs [h_prog_def,h_prog_rule_store_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_rule_store_def,
          mrec_sem_simps] >>
      rpt(PURE_CASE_TAC >> gvs[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (rpt(PURE_CASE_TAC >> gvs[]) >>
          fs [h_prog_def,h_prog_rule_store_byte_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_rule_store_byte_def,
          mrec_sem_simps] >>
      rpt(PURE_CASE_TAC >> gvs[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (rpt(PURE_CASE_TAC >> gvs[]) >>
          fs [h_prog_def,h_prog_rule_return_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          fs [Once itree_wbisim_cases, empty_locals_def,
              panSemTheory.empty_locals_def]) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_rule_return_def,
          mrec_sem_simps] >>
      rpt(PURE_CASE_TAC >> gvs[]) >>
      fs [ltree_lift_cases, mrec_sem_simps] >>
      fs [Once itree_wbisim_cases, ELIM_UNCURRY, empty_locals_def,
              panSemTheory.empty_locals_def])
  >- (rw [itree_semantics_beh_def] >>
      DEEP_INTRO_TAC some_intro >> rw []
      >- (pairarg_tac >> gvs[] >>
          rpt(PURE_FULL_CASE_TAC >> simp[]) >>
          fs [h_prog_def,h_prog_rule_raise_def,
              mrec_sem_simps] >>
          fs [ltree_lift_cases] >>
          rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
          fs [Once itree_wbisim_cases, empty_locals_def,
              panSemTheory.empty_locals_def,
              ltree_lift_cases,mrec_sem_simps
             ]
         ) >>
      simp[EXISTS_PROD]>>
      fs [h_prog_def,h_prog_rule_raise_def,
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

Theorem h_prog_Ret_ffi_const:
  ∀p s s'.
  h_prog (p, s) = Ret (r, s') ⇒ s.ffi = s'.ffi
Proof
  Induct>>
  fs[h_prog_def,
     h_prog_rule_dec_def,
     h_prog_rule_return_def,
     h_prog_rule_raise_def,
     h_prog_rule_ext_call_def,
     h_prog_rule_call_def,
     h_prog_rule_while_def,
     h_prog_rule_cond_def,
     h_prog_rule_sh_mem_def,
     h_prog_rule_sh_mem_def,
     h_prog_rule_seq_def,
     h_prog_rule_store_def,
     h_prog_rule_store_byte_def,
     h_prog_rule_assign_def]>>
  rpt strip_tac>>
  gvs[panPropsTheory.eval_upd_clock_eq,AllCaseEqs(),
      empty_locals_defs]
  >- (gvs[Once itree_iter_thm,
         panPropsTheory.eval_upd_clock_eq]>>
      rpt (FULL_CASE_TAC>>fs[]))>>
  Cases_on ‘m’>>fs[h_prog_rule_sh_mem_op_def]>>
  fs[h_prog_rule_sh_mem_load_def,h_prog_rule_sh_mem_store_def]>>
  rpt (FULL_CASE_TAC>>fs[])
QED

Theorem itree_semantics_beh_while_SemFail:
  ((itree_semantics_beh (unclock s1) (While e c) = SemFail ∧
    (itree_semantics_beh (unclock s) c =
     SemTerminate (NONE,unclock s1) s1.ffi.io_events ∨
     itree_semantics_beh (unclock s) c =
     SemTerminate (SOME Continue,unclock s1) s1.ffi.io_events) ∨
    itree_semantics_beh (unclock s) c = SemFail)) ∧
  w ≠ 0w ∧
  eval s e = SOME (ValWord w) ⇒
  itree_semantics_beh (unclock s) (While e c) = SemFail
Proof
  strip_tac>>
  fs[itree_semantics_beh_def]>>
  fs[AllCaseEqs()]>>gvs[]>>
  last_x_assum mp_tac>>
  DEEP_INTRO_TAC some_intro >> reverse $ rw []>>
  TRY (qpat_x_assum ‘_ = SOME (_,_)’ mp_tac>>
       DEEP_INTRO_TAC some_intro >> reverse $ rw [])>>
  simp[PULL_EXISTS]>>
  DEEP_INTRO_TAC some_intro >>
  fs[]>>
  (‘∃x. (λ(r,s').
           ltree_lift query_oracle s.ffi
                      (mrec_sem (h_prog (While e c,unclock s)))
                      ≈ Ret (r,s') ∧ r = SOME Error) x’ by
     (gvs[EXISTS_PROD]>>
      simp[h_prog_def,h_prog_rule_while_def]>>
      simp[Once itree_iter_thm,
           panPropsTheory.eval_upd_clock_eq]>>
      fs[mrec_sem_simps,ltree_lift_cases]>>
      fs[msem_lift_monad_law]>>
      fs[ltree_lift_monad_law]>>
      irule_at Any itree_wbisim_trans>>
      irule_at Any itree_bind_resp_t_wbisim>>
      first_assum $ irule_at Any>>
      simp[Once itree_bind_thm]>>
      simp[mrec_sem_simps,ltree_lift_cases]>>
      TRY (irule_at Any itree_wbisim_refl>>NO_TAC)>>
      irule_at Any itree_wbisim_trans>>
      last_assum $ irule_at Any>>

      simp[h_prog_def,h_prog_rule_while_def]>>
      qabbrev_tac ‘ss = unclock s’>>
      ‘(ltree_lift_state query_oracle ss.ffi
             (mrec_sem (h_prog (c,ss)))) = (unclock s1).ffi’ by
        (irule ltree_lift_state_lift>>
         fs[Abbr ‘ss’]>>
         first_assum $ irule_at Any)>>
      fs[Abbr ‘ss’]>>
      irule itree_wbisim_refl)>>
   pairarg_tac>>rw[]>>
   pairarg_tac>>gvs[EXISTS_PROD]
   >- (drule itree_wbisim_sym>>strip_tac>>
       drule itree_wbisim_trans>>
       disch_then $ rev_drule>>
       rw[Once itree_wbisim_cases])>>
   first_assum $ irule_at Any)
QED

Theorem dec_simps:
  mrec_sem (h_prog (Dec v a p, s)) ≈
  (case eval (reclock s) a of
   | NONE => Ret (SOME Error,s)
   | SOME x =>
       mrec_sem (h_prog (p,s with locals := s.locals |+ (v,x)) >>=
                        (λ(res,s').
                           Ret
                           (res,
                            s' with locals := res_var s'.locals (v,FLOOKUP s.locals v)))))
Proof
  simp[h_prog_def,h_prog_rule_dec_def]>>
  CASE_TAC>>gvs[]>>
  simp[mrec_sem_simps]>- simp[Once itreeTauTheory.itree_wbisim_cases]>>
  irule itreeTauTheory.itree_wbisim_refl
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
      rename1 ‘itree_semantics_beh(unclock t)’ >>
      rpt $ pop_assum MP_TAC >>
      MAP_EVERY qid_spec_tac [‘s'’,‘r’,‘t’,‘prog’] >>
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
      >- (cheat)
      >~ [‘ExtCall’]
      >- (gvs[evaluate_def,AllCaseEqs(),
              itree_semantics_beh_def,
              h_prog_def,
              h_prog_rule_ext_call_def,
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
      >~ [‘ShMem’]
      >- (gvs[evaluate_def,AllCaseEqs(),
              itree_semantics_beh_def,
              h_prog_def,
              h_prog_rule_sh_mem_def,
              h_prog_rule_sh_mem_op_def,
              h_prog_rule_sh_mem_load_def,
              h_prog_rule_sh_mem_store_def,
              oneline sh_mem_op_def,
              sh_mem_load_def,
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
          TRY(rename1 ‘Error’ >>
              rw[ELIM_UNCURRY] >>
              metis_tac[SELECT_REFL,FST,SND,PAIR]) >>
          rw[ELIM_UNCURRY,
             itree_wbisim_tau_eqn,
             query_oracle_def,
             itree_wbisim_neq,
             ffiTheory.call_FFI_def,
             empty_locals_defs,
             set_var_def,
             panSemTheory.set_var_def
            ]
         ) >>
      gvs[evaluate_def,itree_semantics_beh_simps,panPropsTheory.eval_upd_clock_eq,
          AllCaseEqs()] >>
      gvs[dec_clock_def, empty_locals_def, panSemTheory.empty_locals_def]
     )
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
