(*
  Structural facts about the individual core proof steps of the PB checker
*)
Theory npbc_check_step
Ancestors
  pbc npbc npbc_check
Libs
  preamble

val _ = numLib.temp_prefer_num();

(* conf_valid', weakened by an escape predicate on the source model *)
Definition conf_valid_esc_def:
  conf_valid_esc C D pres po obj esc ⇔
    ∀p.
      satisfies p C ⇒
      (∃p'.
           (∀x. x ∈ pres ⇒ p x = p' x) ∧
           satisfies p' (C ∪ D) ∧
           po p' p ∧
           eval_obj obj p' ≤ eval_obj obj p) ∨
      esc p
End

Theorem conf_valid_esc_F:
  conf_valid_esc C D pres po obj (λp. F) ⇔
  conf_valid' C D pres po obj
Proof
  rw[conf_valid_esc_def,conf_valid'_def]
QED

Theorem dominance_conf_valid_esc:
  transitive po ∧
  finite_support po z ∧ FINITE z ∧
  (∀x. x ∈ pres ⇒ w x = NONE) ∧
  C ∪ D ∪ {not c} ⊨ C ⇂ w ∧
  sat_strict_ord (C ∪ D ∪ {not c}) po w ∧
  (case obj of
   | NONE => T
   | SOME obj => C ∪ D ∪ {not c} ⊨ {obj_constraint w obj}) ∧
  (∀x y. esc x ∧ po x y ⇒ esc y) ∧
  conf_valid_esc C D pres po obj esc ⇒
  conf_valid_esc C (D ∪ {c}) pres po obj esc
Proof
  rw[conf_valid_esc_def]>>
  CCONTR_TAC>>
  gs[]>>
  fs[METIS_PROVE [] ``(A ∨ ¬B) ⇔ (¬A ⇒ ¬B)``]>>
  qabbrev_tac`s =
  {p |
   satisfies p C ∧ ¬esc p ∧
   ∀p'. (∀x. x ∈ pres ⇒ p x = p' x) ∧
        po p' p ∧ eval_obj obj p' ≤ eval_obj obj p ⇒
        ¬satisfies p' (C ∪ D ∪ {c})}`>>
  `s <> {}` by (
    rw[Abbr`s`,EXTENSION]>>
    metis_tac[])>>
  rename1`satisfies pold C`>>
  `∃p. p ∈ s ∧
    ∀p'. p' ∈ s ∧ po p' p ⇒ po p p'` by
    (match_mp_tac FINITE_support_find_min>>
    fs[])>>
  qpat_x_assum`s ≠ _ ` kall_tac>>
  `satisfies p C ∧ ¬esc p ∧
  ∀p'.
    (∀x. x ∈ pres ⇒ p x = p' x) ∧
    po p' p ∧ eval_obj obj p' ≤ eval_obj obj p ⇒
    (¬satisfies p' C ∨ ¬satisfies p' D)
      ∨ ¬satisfies_npbc p' c` by fs[Abbr`s`]>>
  last_x_assum drule>>strip_tac>>
  gvs[]>>
  `~satisfies_npbc p' c` by metis_tac[]>>
  fs[sat_strict_ord_def,sat_ord_def,not_thm]>>
  last_x_assum drule_all>>
  strip_tac>>
  qabbrev_tac`p'' = assign w p'`>>
  `po p'' p` by
    metis_tac[relationTheory.transitive_def]>>
  `¬po p p''` by
    metis_tac[relationTheory.transitive_def]>>
  `satisfies p'' C` by (
    fs[sat_implies_def,Abbr`p''`]>>
    fs[satisfies_def,PULL_EXISTS,subst_thm,not_thm])>>
  `p'' ∉ s` by metis_tac[]>>
  ‘eval_obj obj p'' ≤ eval_obj obj p'’ by
    (Cases_on ‘obj’ >- fs [eval_obj_def]
     \\ gvs [sat_implies_def,Abbr‘p''’]
     \\ rewrite_tac [GSYM satisfies_npbc_obj_constraint]
     \\ first_x_assum irule \\ fs [not_thm]) >>
  gs[Abbr`s`]
  >- metis_tac[]>>
  rename1`satisfies_npbc pprime c`>>
  `po pprime p` by
    metis_tac[transitive_def]>>
  `!x. x ∈ pres ⇒ (p' x = pprime x)` by
    gvs[Abbr`p''`,assign_def]>>
  metis_tac[integerTheory.INT_LE_TRANS]
QED

Theorem good_aspo_dominance_esc:
  fresh_aux as fml c obj w ∧
  good_aspo (((f,g,us,vs,as),xs)) ∧
  (∀x. x ∈ pres ⇒ w x = NONE) ∧
  C ⊆ fml ∧
  (∀w.
    satisfies w C ⇒
    (∃w'.
      (∀x. x ∈ pres ⇒ w x = w' x) ∧
      satisfies w' fml ∧
      po_of_aspo ((f,g,us,vs,as),xs) w' w ∧
      eval_obj obj w' ≤ eval_obj obj w) ∨ esc w) ∧
  (∀x y. esc x ∧ po_of_aspo ((f,g,us,vs,as),xs) x y ⇒ esc y) ∧
  sub_leq =
    (λn.
      case ALOOKUP (ZIP (us,xs)) n of
        SOME (v,b) =>
          SOME (
            mk_bit_lit b
              (case w v of
                NONE => INR (Pos v)
              | SOME res => res))
      | NONE => OPTION_MAP (INR o mk_lit) (ALOOKUP (ZIP (vs, xs)) n)) ∧
  sub_geq =
    (λn.
      case ALOOKUP (ZIP (vs,xs)) n of
        SOME (v,b) =>
          SOME (
            mk_bit_lit b
              (case w v of
                NONE => INR (Pos v)
              | SOME res => res))
      | NONE => OPTION_MAP (INR o mk_lit) (ALOOKUP (ZIP (us, xs)) n)) ∧
  fml ∪ {not c} ∪ (set g) ⇂ sub_leq ⊨ C ⇂ w ∧
  fml ∪ {not c} ∪ (set g) ⇂ sub_leq ⊨ (set f) ⇂ sub_leq ∧
  unsatisfiable (
    fml ∪ {not c} ∪
    (set f) ⇂ sub_geq ∪
    (set g) ⇂ sub_geq
  ) ∧
  (case obj of
    NONE => T
  | SOME obj =>
    fml ∪ {not c} ∪ (set g) ⇂ sub_leq ⊨ {obj_constraint w obj}) ⇒
  (∀w.
    satisfies w C ⇒
    (∃w'.
      (∀x. x ∈ pres ⇒ w x = w' x) ∧
      satisfies_npbc w' c ∧
      satisfies w' fml ∧
      po_of_aspo (((f,g,us,vs,as),xs)) w' w ∧
      eval_obj obj w' ≤ eval_obj obj w) ∨ esc w)
Proof
  rw[]>>
  `conf_valid_esc C (fml DIFF C) pres (po_of_aspo ((f,g,us,vs,as),xs)) obj esc` by (
    fs[conf_valid_esc_def]>>rw[]>>
    last_x_assum drule>>
    rw[]
    >- (
      disj1_tac>>
      pop_assum (irule_at Any)>>
      fs[satisfies_def,SUBSET_DEF])>>
    simp[])>>
  drule_at (Pos last) dominance_conf_valid_esc>>
  `C ∪ (fml DIFF C) = fml` by (
    fs[EXTENSION,SUBSET_DEF]>>
    metis_tac[])>>
  disch_then (drule_at Any)>>
  disch_then (qspecl_then [`set (MAP FST xs)`,`w`,`c`] mp_tac)>>
  simp[finite_support_po_of_aspo]>>
  impl_tac>- (
    fs[good_aspo_def,fresh_aux_def]>>
    CONJ_TAC >- (
      irule_at Any sat_implies_more_left_spec>>
      rpt(first_x_assum (irule_at Any))>>
      qexists_tac`w`>>simp[]>>
      rw[]
      >- (
        gvs[EXTENSION,npbf_vars_def]>>
        metis_tac[])
      >- (
        CCONTR_TAC>>
        gvs[]>> drule npbf_vars_subst>>
        gvs[SUBSET_DEF,npbf_vars_def]>>
        metis_tac[]))>>
    CONJ_TAC >- (
      irule imp_sat_strict_ord_po_of_aspo>>
      gvs[])>>
    gvs[AllCasePreds()]>>
    irule_at Any sat_implies_more_left_spec>>
    rpt(first_x_assum (irule_at Any))>>
    qexists_tac`w`>>simp[]>>
    rw[]>>
    gvs[EXTENSION,npbf_vars_def]>>
    metis_tac[npbc_vars_obj_constraint])>>
  simp[conf_valid_esc_def]>>
  rw[]>>
  pop_assum drule>>
  rw[]
  >- (
    disj1_tac>>
    pop_assum (irule_at Any)>>
    fs[satisfies_def]>>
    metis_tac[])>>
  simp[]
QED

(* sat_obj_po, weakened by an escape predicate on the source model *)
Definition sat_obj_po_esc_def:
  sat_obj_po_esc pres aspoopt fopt esc s t ⇔
  ∀w.
    satisfies w s ⇒
    (∃w'.
      (∀x. x ∈ pres ⇒ w x = w' x) ∧
      satisfies w' t ∧
      OPTION_ALL (λaspo. (po_of_aspo aspo) w' w) aspoopt ∧
      eval_obj fopt w' ≤ eval_obj fopt w) ∨ esc w
End

Theorem sat_obj_po_imp_esc:
  sat_obj_po pres aspoopt fopt s t ⇒
  sat_obj_po_esc pres aspoopt fopt esc s t
Proof
  rw[sat_obj_po_esc_def,sat_obj_po_def]>>
  metis_tac[]
QED

Theorem sat_obj_po_esc_more:
  sat_obj_po_esc pres ord obj esc A B ∧ A ⊆ C ⇒
  sat_obj_po_esc pres ord obj esc C B
Proof
  rw[sat_obj_po_esc_def]>>
  metis_tac[satisfies_SUBSET]
QED

Theorem sat_obj_po_esc_trans:
  OPTION_ALL good_aspo ord ⇒
  sat_obj_po_esc pres ord obj esc x y ∧
  sat_obj_po pres ord obj y z ⇒
  sat_obj_po_esc pres ord obj esc x z
Proof
  rw[sat_obj_po_esc_def,sat_obj_po_def]>>
  qpat_x_assum`∀w. satisfies w x ⇒ _` drule>>
  rw[]
  >- (
    qpat_x_assum`∀w. satisfies w y ⇒ _` drule>>
    rw[]>>
    disj1_tac>>
    qpat_x_assum`satisfies _ z` (irule_at Any)>>
    rw[]
    >- (Cases_on`ord`>>fs[]>>metis_tac[good_aspo_imp_po_of_aspo_trans])>>
    metis_tac[integerTheory.INT_LE_TRANS])>>
  simp[]
QED

Theorem sat_obj_po_trans_esc:
  OPTION_ALL good_aspo ord ∧
  (∀x y. esc x ∧ OPTION_ALL (λaspo. po_of_aspo aspo x y) ord ⇒ esc y) ⇒
  sat_obj_po pres ord obj x y ∧
  sat_obj_po_esc pres ord obj esc y z ⇒
  sat_obj_po_esc pres ord obj esc x z
Proof
  rw[sat_obj_po_esc_def,sat_obj_po_def]>>
  qpat_x_assum`∀w. satisfies w x ⇒ _` drule>>
  rw[]>>
  qpat_x_assum`∀w. satisfies w y ⇒ _` drule>>
  rw[]
  >- (
    disj1_tac>>
    qpat_x_assum`satisfies _ z` (irule_at Any)>>
    rw[]
    >- (Cases_on`ord`>>fs[]>>metis_tac[good_aspo_imp_po_of_aspo_trans])>>
    metis_tac[integerTheory.INT_LE_TRANS])>>
  disj2_tac>>
  metis_tac[]
QED

Theorem core_only_fml_map_core:
  ∀b. core_only_fml b (map (λ(c,b). (c,T)) fml) = core_only_fml F fml
Proof
  simp[core_only_fml_def,lookup_map,EXTENSION,EQ_IMP_THM,EXISTS_PROD]>>
  rw[]>>
  metis_tac[PAIR]
QED

Theorem core_only_fml_F_insert_same:
  lookup n fml = SOME (c,bb) ⇒
  core_only_fml F (insert n (c,b) fml) = core_only_fml F fml
Proof
  strip_tac>>
  `core_only_fml F (insert n (c,b) fml) = c INSERT core_only_fml F fml` by
    metis_tac[core_only_fml_F_insert_b_same]>>
  `c ∈ core_only_fml F fml` by
    (simp[core_only_fml_def]>>metis_tac[])>>
  simp[ABSORPTION_RWT]
QED

Theorem core_only_fml_T_SUBSET_insert:
  lookup n fml = SOME (c,bb) ⇒
  core_only_fml T fml ⊆ core_only_fml T (insert n (c,T) fml)
Proof
  strip_tac>>
  `core_only_fml T (insert n (c,T) fml) = c INSERT core_only_fml T fml` by
    metis_tac[core_only_fml_T_insert_T_same]>>
  simp[SUBSET_INSERT_RIGHT]
QED

Theorem domain_insert_same:
  lookup n fml = SOME v ⇒
  domain (insert n w fml) = domain fml
Proof
  rw[EXTENSION,domain_lookup,lookup_insert]>>
  rw[]>>metis_tac[]
QED

(* Transferring to the core changes flags, never the constraint set *)
Theorem do_transfer_props:
  ∀ls fml fml'.
  do_transfer fml ls = SOME fml' ⇒
  core_only_fml F fml' = core_only_fml F fml ∧
  core_only_fml T fml ⊆ core_only_fml T fml' ∧
  domain fml' = domain fml
Proof
  Induct>>simp[do_transfer_def]>>
  rpt gen_tac>>
  strip_tac>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  strip_tac>>
  drule core_only_fml_F_insert_same>>
  drule core_only_fml_T_SUBSET_insert>>
  drule domain_insert_same>>
  rpt strip_tac>>
  gvs[]>>
  metis_tac[SUBSET_TRANS]
QED

(* A step that leaves every configuration field but id and tcb alone *)
Definition conf_eq_def:
  conf_eq pc pc' ⇔
    pc'.pres = pc.pres ∧
    pc'.ord = pc.ord ∧
    pc'.obj = pc.obj ∧
    pc'.chk = pc.chk ∧
    pc'.bound = pc.bound ∧
    pc'.dbound = pc.dbound ∧
    pc'.enum = pc.enum ∧
    pc'.orders = pc.orders
End

Theorem check_cstep_strengthentocore_str:
  ∀b fml pc.
  id_ok fml pc.id ∧
  OPTION_ALL good_aspo_subst pc.ord ⇒
  case check_cstep (StrengthenToCore b) fml pc of NONE => T
  | SOME (fml',pc') =>
    pc' = pc with tcb := b ∧
    id_ok fml' pc'.id ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml F fml) (core_only_fml F fml') ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml T fml') (core_only_fml T fml) ∧
    (pc'.tcb ⇒ core_only_fml T fml' ⊨ core_only_fml F fml')
Proof
  rpt gen_tac>>
  strip_tac>>
  simp[check_cstep_def]>>
  drule OPTION_ALL_good_aspo_subst_good_aspo>>
  strip_tac>>
  IF_CASES_TAC>>
  simp[id_ok_map,core_only_fml_map_core,sat_obj_po_refl,sat_implies_refl]>>
  match_mp_tac sat_obj_po_SUBSET>>
  simp[core_only_fml_T_SUBSET_F]
QED

Theorem check_cstep_sstep_str:
  ∀s fml pc.
  id_ok fml pc.id ∧
  OPTION_ALL good_aspo_subst pc.ord ∧
  (pc.tcb ⇒ core_only_fml T fml ⊨ core_only_fml F fml) ⇒
  case check_cstep (Sstep s) fml pc of NONE => T
  | SOME (fml',pc') =>
    conf_eq pc pc' ∧ pc.tcb = pc'.tcb ∧
    pc.id ≤ pc'.id ∧
    id_ok fml' pc'.id ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml F fml) (core_only_fml F fml') ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml T fml') (core_only_fml T fml) ∧
    (pc'.tcb ⇒ core_only_fml T fml' ⊨ core_only_fml F fml')
Proof
  rpt gen_tac>>strip_tac>>
  simp[check_cstep_def]>>
  drule check_sstep_correct>>
  disch_then drule>>
  disch_then drule>>
  disch_then (qspecl_then [`s`,`pc.pres`,`pc.obj`] mp_tac)>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[conf_eq_def]
QED

Theorem check_cstep_transfer_str:
  ∀ls fml pc.
  id_ok fml pc.id ∧
  OPTION_ALL good_aspo_subst pc.ord ∧
  (pc.tcb ⇒ core_only_fml T fml ⊨ core_only_fml F fml) ⇒
  case check_cstep (Transfer ls) fml pc of NONE => T
  | SOME (fml',pc') =>
    conf_eq pc pc' ∧ pc.tcb = pc'.tcb ∧
    pc.id ≤ pc'.id ∧
    id_ok fml' pc'.id ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml F fml) (core_only_fml F fml') ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml T fml') (core_only_fml T fml) ∧
    (pc'.tcb ⇒ core_only_fml T fml' ⊨ core_only_fml F fml')
Proof
  rpt gen_tac>>strip_tac>>
  simp[check_cstep_def]>>
  Cases_on`do_transfer fml ls`>>simp[]>>
  drule do_transfer_props>>
  strip_tac>>
  drule OPTION_ALL_good_aspo_subst_good_aspo>>
  strip_tac>>
  simp[conf_eq_def,sat_obj_po_refl]>>
  CONJ_TAC >- fs[id_ok_def]>>
  CONJ_TAC >- (
    match_mp_tac sat_obj_po_SUBSET>>
    simp[])>>
  strip_tac>>
  gvs[sat_implies_def]>>
  metis_tac[satisfies_SUBSET]
QED

Theorem check_cstep_checkeddelete_str:
  ∀n s pfs idopt fml pc.
  id_ok fml pc.id ∧
  OPTION_ALL good_aspo_subst pc.ord ∧
  (pc.tcb ⇒ core_only_fml T fml ⊨ core_only_fml F fml) ⇒
  case check_cstep (CheckedDelete n s pfs idopt) fml pc of NONE => T
  | SOME (fml',pc') =>
    conf_eq pc pc' ∧ pc.tcb = pc'.tcb ∧
    pc.id ≤ pc'.id ∧
    id_ok fml' pc'.id ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml F fml) (core_only_fml F fml') ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml T fml') (core_only_fml T fml) ∧
    (pc'.tcb ⇒ core_only_fml T fml' ⊨ core_only_fml F fml')
Proof
  rpt gen_tac>>
  strip_tac>>
  simp[check_cstep_def]>>
  every_case_tac>>simp[]>>
  `id_ok (delete n fml) pc.id` by (fs[id_ok_def]>>metis_tac[SUBSET_DEF])>>
  drule check_red_correct>>
  rpt (disch_then (drule_at Any))>>
  impl_tac >- simp[sat_implies_refl]>>
  simp[]>>
  strip_tac>>
  drule OPTION_ALL_good_aspo_subst_good_aspo>>
  strip_tac>>
  `x INSERT core_only_fml T (delete n fml) = core_only_fml T fml` by
    (simp[core_only_fml_def,EXTENSION]>>
    rw[EQ_IMP_THM]
    >- (fs[lookup_core_only_def,AllCaseEqs()]>>metis_tac[])
    >- (fs[lookup_delete]>>metis_tac[])>>
    fs[lookup_core_only_def,AllCaseEqs(),lookup_delete]>>
    Cases_on`n=n'`>>fs[]>>
    metis_tac[])>>
  `sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
    (core_only_fml T (delete n fml)) (core_only_fml T fml)` by
    (every_case_tac>>gvs[]>>
    match_mp_tac (GEN_ALL sat_obj_po_more_2)>>
    qexists_tac`core_only_fml T fml`>>
    simp[sat_obj_po_refl]>>
    gvs[sat_implies_def]>>
    qpat_x_assum`_ = core_only_fml _ _` sym_sub_tac>>
    simp[])>>
  simp[conf_eq_def]>>
  CONJ_TAC >- fs[id_ok_def]>>
  CONJ_TAC >- (match_mp_tac sat_obj_po_SUBSET>>fs[core_only_fml_def,lookup_delete,SUBSET_DEF]>>metis_tac[])>>
  strip_tac>>
  fs[check_tcb_idopt_def]>>
  every_case_tac>>fs[sat_implies_def]>>
  rw[]>>
  qpat_x_assum`_ = core_only_fml _ _` sym_sub_tac>>
  fs[]>>
  `satisfies w (core_only_fml F fml)` by metis_tac[]>>
  pop_assum mp_tac>>
  match_mp_tac satisfies_SUBSET>>
  fs[core_only_fml_def,lookup_delete,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem check_cstep_dom_str:
  ∀p l l0 o' fml pc esc.
  id_ok fml pc.id ∧
  OPTION_ALL good_aspo_subst pc.ord ∧
  (∀aspo. pc.ord = SOME aspo ⇒
    ∀x y. esc x ∧ po_of_aspo (FST aspo) x y ⇒ esc y) ∧
  (pc.tcb ⇒ core_only_fml T fml ⊨ core_only_fml F fml) ∧
  sat_obj_po_esc (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj esc
    (core_only_fml T fml) (core_only_fml F fml) ⇒
  case check_cstep (Dom p l l0 o') fml pc of NONE => T
  | SOME (fml',pc') =>
    conf_eq pc pc' ∧
    pc'.tcb = pc.tcb ∧
    pc.id ≤ pc'.id ∧
    id_ok fml' pc'.id ∧
    (pc'.tcb ⇒ core_only_fml T fml' ⊨ core_only_fml F fml') ∧
    sat_obj_po (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj
      (core_only_fml T fml') (core_only_fml T fml) ∧
    sat_obj_po_esc (pres_set_spt pc.pres) (OPTION_MAP FST pc.ord) pc.obj esc
      (core_only_fml T fml) (core_only_fml F fml')
Proof
  rpt gen_tac>>
  fs[check_cstep_def,check_hash_goals_def]>>
  Cases_on`pc.ord`>>fs[]>>
  pairarg_tac>>gvs[]>>
  TOP_CASE_TAC>>
  pop_assum mp_tac>>
  IF_CASES_TAC>>gvs[]>>
  pairarg_tac>>gvs[]>>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>>
  rw[]>>
  pairarg_tac>>gvs[]>>
  gvs[insert_fml_def]>>
  `id_ok (insert pc.id (not p,F) fml) (pc.id + 1)` by
    fs[id_ok_def]>>
  drule check_scopes_correct>>
  rename1`check_scopes scpfs`>>
  disch_then(qspecl_then [`scpfs`,`F`] mp_tac)>>
  gs[]>> strip_tac>>
  rename1`insert cc (p,_) fml`>>
  fs[good_aspo_subst_def]>>
  `cc ∉ domain fml` by gvs[id_ok_def]>>
  CONJ_TAC >- simp[conf_eq_def]>>
  CONJ_TAC >- gvs[id_ok_def,SUBSET_DEF]>>
  CONJ_TAC >- (
    rw[]>>fs[]>>
    DEP_REWRITE_TAC[core_only_fml_T_insert_T,core_only_fml_F_insert_b]>>
    fs[id_ok_def]>>
    metis_tac[sat_implies_INSERT])>>
  CONJ_TAC >- (
    irule sat_obj_po_SUBSET>>
    simp[]>>
    Cases_on`pc.tcb`
    >- (
      `core_only_fml T (insert cc (p,T) fml) = p INSERT core_only_fml T fml` by
        metis_tac[core_only_fml_T_insert_T]>>
      simp[SUBSET_INSERT_RIGHT])>>
    `core_only_fml T (insert cc (p,F) fml) = core_only_fml T fml` by
      metis_tac[core_only_fml_T_insert_F]>>
    simp[])>>
  `sat_obj_po_esc (pres_set_spt pc.pres) (SOME (FST x)) pc.obj esc
    (core_only_fml T fml)
    (core_only_fml F (insert cc (p,F) fml))` by (
    reverse (every_case_tac)
    >- (
      `sat_obj_po (pres_set_spt pc.pres) (SOME (FST x)) pc.obj
        (core_only_fml F fml)
        (core_only_fml F (insert cc (p,F) fml))` by (
        DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
        CONJ_TAC >- fs[id_ok_def]>>
        match_mp_tac sat_obj_po_insert_contr>>
        fs[id_ok_def,good_aspo_def]>>
        drule check_contradiction_fml_unsat>>
        qpat_x_assum`sat_implies _ _` mp_tac>>
        gvs [good_aspo_imp_po_of_aspo_refl,reflexive_def]>>
        DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
        simp[]>>
        fs[core_only_fml_def]>>
        gs[sat_implies_def,satisfiable_def,unsatisfiable_def]>>
        metis_tac[])>>
      metis_tac[OPTION_ALL_def,sat_obj_po_esc_trans])>>
    simp[sat_obj_po_esc_def]>>
    DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
    CONJ_TAC >- fs[id_ok_def]>>
    simp[satisfies_simp]>>
    simp[GSYM CONJ_ASSOC]>>
    PairCases_on`x`>>
    fs[]>>
    match_mp_tac (GEN_ALL good_aspo_dominance_esc)>>
    simp[]>>
    qexists_tac ‘subst_fun (mk_subst l)’>>fs[]>>
    conj_tac >-
     (drule check_fresh_aspo_fresh
      \\ gvs [fresh_aux_aspo_def]
      \\ disch_then (qspecl_then [‘F’,‘F’] mp_tac)
      \\ gvs [])>>
    CONJ_TAC >-
      metis_tac[check_pres_subst_fun]>>
    CONJ_TAC >-
      metis_tac[core_only_fml_T_SUBSET_F]>>
    CONJ_TAC >-
      gvs[sat_obj_po_esc_def]>>
    CONJ_TAC >-
      metis_tac[]>>
    `pc.id ∉ domain fml` by fs[id_ok_def]>>
    fs[core_only_fml_F_insert_b]>>
    fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]>>
    gvs[dom_subgoals_def,MEM_enumerate_iff,ADD1,AND_IMP_INTRO,PULL_EXISTS]>>
    CONJ_TAC >- (
      (* core constraints*)
      rw[sat_implies_def,satisfies_def]
      \\ gs[PULL_EXISTS,GSYM range_mk_core_fml,range_def,lookup_mk_core_fml]
      \\ Cases_on ‘subst_opt (subst_fun (mk_subst l)) x’ \\ fs []
      THEN1 (
        imp_res_tac subst_opt_NONE
        \\ gvs[lookup_core_only_def,AllCaseEqs()]
        \\ CCONTR_TAC \\ gvs [satisfiable_def,not_thm]
        \\ fs [satisfies_def,range_def,PULL_EXISTS]
        \\ metis_tac[])
      \\ rename1`subst_opt _ _ = SOME yy`
      \\ `MEM (n,yy) (toAList (map_opt (subst_opt (subst_fun (mk_subst l)))
          (mk_core_fml T fml)))` by
          simp[MEM_toAList,lookup_map_opt,lookup_mk_core_fml,lookup_core_only_def]
      \\ drule_all split_goals_checked \\ rw[]
      >- (
        fs[satisfiable_def,not_thm,satisfies_def,range_mk_core_fml]>>
        fs[core_only_fml_def,lookup_core_only_def,AllCaseEqs(),PULL_EXISTS]>>
        drule subst_opt_SOME >>
        rw[]>> metis_tac[not_thm])
      >- (
        fs[unsatisfiable_def,satisfiable_def,not_thm,satisfies_def]>>
        drule subst_opt_SOME >>
        fs[range_def]>>
        rw[]>>
        metis_tac[not_thm,imp_thm])
      \\ drule_all lookup_extract_scoped_pids_l>>rw[]
      \\ drule_all extract_scopes_MEM_INL
      \\ strip_tac
      \\ last_x_assum drule \\ simp []
      \\ disch_then drule \\ simp []
      \\ gvs[unsatisfiable_def,satisfiable_def, MEM_toAList,lookup_map_opt,
             AllCaseEqs(),satisfies_def,core_only_fml_def,FORALL_PROD]
      \\ fs[not_thm,range_def,PULL_EXISTS]
      \\ rw[]
      \\ first_x_assum(qspec_then`w` mp_tac) \\ simp[]
      \\ rename1`lookup i _ = SOME xxx`
      \\ `xxx = c` by (
        gvs[lookup_mk_core_fml]>>
        drule lookup_core_only_T_imp_F>>
        rw[])
      \\ `subst (subst_fun (mk_subst l)) c =
          subst (subst_fun (mk_subst l)) x` by
        metis_tac[subst_opt_SOME]
      \\ strip_tac \\ gvs []
      >- (
        fs[lookup_core_only_def,AllCaseEqs(),PULL_EXISTS]>>
        metis_tac[])
      \\ Cases_on ‘scopt’ \\ gvs [mk_scope_def,extract_scope_val_def]
      \\ gvs [dom_subst_def,neg_dom_subst_def]
      \\ gvs [MEM_MAP,EXISTS_PROD]
      \\ first_x_assum drule
      \\ strip_tac
      \\ gvs [lookup_list_list_insert,good_ord_s_def,vec_lookup_num_man_to_vec])>>
    CONJ_TAC >- (
      (* order constraints *)
      fs[core_only_fml_def]>>
      simp[GSYM LIST_TO_SET_MAP]>>
      rw[sat_implies_EL,EL_MAP]>>
      last_x_assum(qspec_then`n` mp_tac)>>
      ‘n < LENGTH dsubs’ by gvs [neg_dom_subst_def,dom_subst_def]>>
      gvs[dom_subst_def]>>
      PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
      strip_tac
      >- (
        drule_all lookup_extract_scoped_pids_r>>
        rw[]>>
        drule extract_scopes_MEM_INR>>
        disch_then $ drule_then drule>>
        strip_tac>>
        first_x_assum drule >> simp [] >> strip_tac>>
        first_x_assum drule >> simp [] >>
        gvs [neg_dom_subst_def]>>
        simp [EL_APPEND_EQN]>>
        fs[EL_MAP]>>
        strip_tac>>
        drule unsatisfiable_not_sat_implies>>
        gvs[lookup_list_list_insert,good_ord_s_def,vec_lookup_num_man_to_vec]>>
        gvs [mk_scope_def]>>
        Cases_on ‘scopt’>>gvs []>>
        gvs [extract_scope_val_def]
        \\ strip_tac \\ irule weaken
        \\ pop_assum $ irule_at Any
        \\ gvs [SUBSET_DEF])
      >- (
        fs[check_hash_imp_def]
        \\ pop_assum mp_tac
        \\ gvs [neg_dom_subst_def]
        \\ DEP_REWRITE_TAC [EL_APPEND_EQN]
        \\ simp[EL_MAP]
        \\ gvs[lookup_list_list_insert,good_ord_s_def,vec_lookup_num_man_to_vec]
        \\ strip_tac
        \\ match_mp_tac unsatisfiable_not_sat_implies
        \\ irule imp_unsatisfiable
        \\ qmatch_goalsub_abbrev_tac ‘set pp’
        \\ simp [AC UNION_COMM UNION_ASSOC]
        \\ metis_tac[not_not])
      >- (
        gvs [neg_dom_subst_def])
    )>>
    CONJ_TAC >- (
      fs[core_only_fml_def]
      \\ ‘dindex < LENGTH dsubs’ by gvs [dom_subst_def,neg_dom_subst_def]
      \\ ‘∃n spf pf none_or_1.
            MEM (none_or_1,spf) l0 ∧
            MEM (SOME (INR dindex,n),pf) spf ∧
            (none_or_1 ≠ NONE ⇒ none_or_1 = SOME 1)’ by
        (gvs [find_scope_1_def,EXISTS_MEM,EXISTS_PROD]
         \\ first_x_assum $ irule_at $ Pos hd \\ simp []
         \\ rename [‘MEM (x,y) _’] \\ Cases_on ‘x’ \\ gvs []
         \\ rename [‘MEM (SOME x,y) _’] \\ Cases_on ‘x’ \\ gvs []
         \\ rename [‘MEM (SOME (x,_),y) _’] \\ Cases_on ‘x’ \\ gvs []
         \\ first_x_assum $ irule_at $ Pos hd)
      \\ drule extract_scopes_MEM_INR
      \\ disch_then drule_all \\ strip_tac
      \\ fs []
      \\ first_x_assum drule \\ simp []
      \\ first_x_assum drule \\ simp []
      \\ disch_then drule \\ simp []
      \\ gvs[mk_scope_def,AllCaseEqs()]
      \\ gvs[neg_dom_subst_def,lookup_list_list_insert,good_ord_s_def,vec_lookup_num_man_to_vec,range_insert,dom_subst_def]
      \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
      \\ DEP_REWRITE_TAC [EL_APPEND2] \\ gvs []
      \\ strip_tac
      \\ irule unsatisfiable_SUBSET
      \\ pop_assum $ irule_at Any
      \\ gvs [SUBSET_DEF] \\ rw [] \\ gvs []
      \\ gvs [MEM_MAP]
      \\ metis_tac [])>>
    (* objective constraint *)
    fs[core_only_fml_def]>>
    Cases_on`pc.obj`>>simp[]>>
    gvs [neg_dom_subst_def,dom_subst_def]
    \\ Cases_on ‘pc.obj’ \\ gvs []
    \\ last_x_assum (qspec_then`LENGTH x0 + 1` mp_tac)
    \\ DEP_REWRITE_TAC [EL_APPEND2] \\ gvs []>>
    PURE_REWRITE_TAC[METIS_PROVE [] ``((P ⇒ Q) ⇒ R) ⇔ (~P ∨ Q) ⇒ R``]>>
    asm_rewrite_tac []>>
    strip_tac
    >- (
      drule_all lookup_extract_scoped_pids_r>>
      simp[]>>rw[]
      \\ drule extract_scopes_MEM_INR
      \\ disch_then $ drule_then drule
      \\ DEP_REWRITE_TAC [EL_APPEND2]
      \\ simp[]
      \\ strip_tac
      \\ first_x_assum drule \\ simp [] \\ strip_tac
      \\ first_x_assum drule \\ simp [] \\ strip_tac
      \\ drule unsatisfiable_not_sat_implies
      \\ strip_tac
      \\ irule weaken
      \\ pop_assum $ irule_at Any
      \\ gvs [SUBSET_DEF] \\ rw [] \\ gvs []
      \\ Cases_on ‘scopt’ \\ gvs [mk_scope_def]
      \\ gvs [extract_scope_val_def]
      \\ rpt disj2_tac
      \\ pop_assum mp_tac
      \\ gvs [MEM_MAP,lookup_list_list_insert,good_ord_s_def,vec_lookup_num_man_to_vec])
    >- (
        match_mp_tac unsatisfiable_not_sat_implies
        \\ gvs [check_hash_imp_def]
        \\ irule imp_unsatisfiable
        \\ qpat_abbrev_tac ‘ss = set x1 ⇂ _’
        \\ simp [AC UNION_COMM UNION_ASSOC]
        \\ metis_tac[not_not])
    )>>
  `core_only_fml F (insert cc (p,F) fml) =
    core_only_fml F (insert cc (p,pc.tcb) fml)` by
    (Cases_on`pc.tcb`>> simp[]>>
    DEP_REWRITE_TAC[core_only_fml_F_insert_b]>>
    fs[id_ok_def])>>
  fs[]
QED

(* Storing an order touches nothing but the order store, and the order it
  stores is good *)
Theorem check_cstep_storeorder_str:
  id_ok fml pc.id ∧
  EVERY (good_aord_t o SND) pc.orders ∧
  check_cstep (StoreOrder m p l l0 l1 p0) fml pc = SOME (fml',pc') ⇒
  fml' = fml ∧
  pc'.id = pc.id ∧ pc'.ord = pc.ord ∧ pc'.obj = pc.obj ∧
  pc'.pres = pc.pres ∧ pc'.tcb = pc.tcb ∧ pc'.chk = pc.chk ∧
  EVERY (good_aord_t o SND) pc'.orders
Proof
  strip_tac>>
  qspecl_then [`StoreOrder m p l l0 l1 p0`,`fml`,
    `pc with <| chk := F; ord := NONE; tcb := F |>`] mp_tac
    (Q.GENL [`cstep`,`fml`,`pc`] check_cstep_correct)>>
  impl_tac >- simp[valid_conf_def,valid_req_def]>>
  gvs[check_cstep_def,AllCaseEqs()]
QED
