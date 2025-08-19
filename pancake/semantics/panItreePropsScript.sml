(*
    Props for Pancake ITree semantics and correspondence proof.
*)
Theory panItreeProps
Ancestors
  itreeTau panItreeSem panLang panSem alignment[qualified]
  misc[qualified] (* for read_bytearray *)
  wordLang[qualified] (* for word_op and word_sh *)
  ffi[qualified]
Libs
  preamble


val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;
Overload "case" = “itree_CASE”;

Theorem itree_eq_imp_wbisim:
  t = t' ⇒ t ≈ t'
Proof
  metis_tac [itree_wbisim_refl]
QED

Theorem itree_bind_thm_wbisim:
  t ≈ Ret r ⇒ t >>= k ≈ k r
Proof
  disch_tac >>
  irule itree_wbisim_trans>>
  irule_at Any itree_bind_resp_t_wbisim >>
  pop_assum $ irule_at Any>>
  metis_tac [itree_bind_thm,itree_wbisim_refl]
QED

Theorem wbisim_Ret_eq:
  Ret r ≈ Ret r' ⇔ r = r'
Proof
  EQ_TAC >>
  rw [Once itree_wbisim_cases]
QED

(** h_prog **)

Theorem h_prog_not_Tau:
  ∀prog s t. h_prog (prog, s) ≠ Tau t
Proof
  Induct >> rpt strip_tac >> spose_not_then strip_assume_tac >>
  gvs[h_prog_def,
     h_prog_dec_def,
     h_prog_return_def,
     h_prog_raise_def,
     h_prog_ext_call_def,
     h_prog_call_def,
     h_prog_deccall_def,
     h_prog_while_def,
     h_prog_cond_def,
     h_prog_seq_def,
     h_prog_store_def,
     h_prog_store_32_def,
     h_prog_store_byte_def,
     oneline h_prog_assign_def,
     oneline h_prog_sh_mem_load_def,
     oneline h_prog_sh_mem_store_def,
     AllCaseEqs()
     ] >>
  gvs[Once itree_iter_thm] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[])
QED

Theorem wbisim_Ret_unique:
  X ≈ Ret x ∧ X ≈ Ret y ⇒ x = y
Proof
  strip_tac>>
  drule itree_wbisim_sym>>strip_tac>>
  drule itree_wbisim_trans>>
  disch_then $ rev_drule>>
  simp[Once itree_wbisim_cases]
QED

(* FUNPOW Tau *)

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

Theorem FUNPOW_Tau_eq_elim[simp]:
  FUNPOW Tau n t = FUNPOW Tau n t' ⇔
  t = t'
Proof
  simp[FUNPOW_eq_elim]
QED

(* itree_bind *)

Theorem mrec_sem_monad_law:
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
      wbisim_Ret_eq
     ] >>
  metis_tac[]
QED

(* spin *)

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

(* nonret *)

Theorem nonret_trans:
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
      gvs[ltree_lift_cases,wbisim_Ret_eq]
      >- (qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin] >> metis_tac[])
      >- (Cases_on ‘a’ >> gvs[ltree_lift_cases,UNCURRY_eq_pair,PULL_EXISTS] >>
          pairarg_tac >>
          gvs[] >>
          qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin] >>
          metis_tac[]))
  >- (qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin])
QED
