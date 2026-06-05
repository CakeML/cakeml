(*
  Some lemmas about the extended Little Theories syntactic functions.
*)
Theory littleTheoriesSyntaxNewSystem
Ancestors
  toto comparison ternaryComparisons mlstring holSyntaxLib
  holSyntax holSyntaxExtra littleTheoriesSyntax
  littleTheoriesSyntaxOldSystem errorMonad
Libs
  preamble

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad("error");

fun rC q = rename [q] >> Cases_on q >> simp[]

val cpn_distinct = TypeBase.distinct_of “:ordering”
val cpn_nchotomy = TypeBase.nchotomy_of “:ordering”

val strip_d1 = CONV_TAC (REWR_CONV (DECIDE “p ∨ q ⇔ ¬p ⇒ q”)) THEN strip_tac
val strip_d2 = CONV_TAC (REWR_CONV (DECIDE “p ∨ q ⇔ ¬q ⇒ p”)) THEN strip_tac

fun pat_conj q =
    underAIs (fn thm =>
      let val pat = Term q
          val trypat = can (find_term (can (match_term pat))) o concl
      in
        hd (filter trypat (CONJUNCTS thm))
        handle _ => raise ERR "pat_conj" "no matching conjunct"
      end)

Theorem term_ok'_imp_term_ok:
  ∀tm. term_ok' thy tm ⇒ term_ok (thy.ctys,thy.ctms) tm
Proof
  Induct_on ‘tm’ >> rw[term_ok'_def, term_ok_def]
QED

Theorem theory_ok'_is_std_sig_ext:
  ∀thy. theory_ok' thy ⇒ is_std_sig (thy.ctys, thy.ctms)
Proof
  rw[theory_ok'_def, ctys_def, ctms_def, is_std_sig_def]
  >> fs[FLOOKUP_FUNION, AllCaseEqs(), sigof'_def]
QED

Theorem theory_ok_drop_thy:
  ∀es. theory_ok' thy ∧ (∀a. a ∈ es ⇒ term_ok thy.sig a ∧ a has_type Bool) ⇒
       theory_ok (drop_thy es thy)
Proof
  rw[theory_ok'_def, theory_ok_def, drop_thy]
  >> gvs[ctys_def, ctms_def, sigof'_def, FRANGE_FUNION,
         type_ok_weakening, term_ok_weakening, is_std_sig_funion]
  >> metis_tac[term_ok'_imp_term_ok, term_ok_weakening, ctys_def, ctms_def]
QED

Theorem term_ok_imp_term_ok':
  term_ok (thy.ctys, thy.ctms) c ⇒ term_ok' thy c
Proof
  Induct_on ‘c’ >> rw[term_ok'_def, term_ok_def]
QED

Theorem theory_ok_drop_thy_alt:
  ∀es. theory_ok' thy ∧ (∀a. a ∈ es ⇒ term_ok' thy a ∧ a has_type Bool) ⇒
       theory_ok (drop_thy es thy)
Proof
  rw[theory_ok'_def, theory_ok_def, drop_thy]
  >> gvs[ctys_def, ctms_def, sigof'_def, FRANGE_FUNION,
         type_ok_weakening, term_ok_weakening, is_std_sig_funion]
  >> metis_tac[term_ok'_imp_term_ok, ctys_def, ctms_def]
QED

Theorem esubst_has_type_bool_alt:
  ∀tm.
    esubsts_ok (thy.ctys, thy.ctms) σ ∧
    term_ok' thy tm ∧
    theory_ok' thy ∧
    tm has_type Bool ⇒
    esubst σ avds tm has_type Bool
Proof
  rw[] >> irule esubst_has_type_bool
  >> conj_asm1_tac >- simp[]
  >> qexistsl_tac [‘(thy:ethy).axs’, ‘((thy:ethy).ctys, thy.ctms)’]
  >> simp[term_ok'_imp_term_ok]
  >> qspec_then ‘∅’ mp_tac theory_ok_drop_thy_alt
  >> simp[drop_thy]
QED

Theorem ty_esubst_type_ok_id:
  ∀ty σ. type_ok tys ty ∧ DISJOINT (FDOM (FST σ)) (FDOM tys) ⇒ ty_esubst σ ty = ty
Proof
  ho_match_mp_tac type_ind >> rw[]
  >- simp[ty_esubst_def]
  >> Cases_on ‘l’ >> simp[ty_esubst_def]
  >- (CASE_TAC >> gvs[type_ok_def, FLOOKUP_DEF, IN_DISJOINT] >> metis_tac[])
  >> gvs[type_ok_def, EVERY_MEM, MAP_EQ_ID] >> rpt case_tac
  >- (irule $ iffRL MAP_EQ_ID >> metis_tac[])
  >> metis_tac[FDOM_FLOOKUP, IN_DISJOINT]
QED

Theorem ty_esubst_o_f_thy_tms:
  ∀thy. theory_ok' thy ∧ esubsts_ok' thy σ ⇒ ty_esubst σ o_f thy.tms = thy.tms
Proof
  rw[theory_ok'_def] >> Cases_on ‘σ’ >> gvs[esubsts_ok'_def]
  >> rw[fmap_eq_flookup, FLOOKUP_o_f]
  >> rw[] >> CASE_TAC >> simp[]
  >> irule ty_esubst_type_ok_id
  >> qexists_tac ‘(thy:ethy).tys’ >> simp[]
  >> conj_tac
  >- metis_tac[DISJOINT_SUBSET, DISJOINT_SYM]
  >> first_x_assum irule >> simp[IN_FRANGE_FLOOKUP] >> metis_tac[]
QED

Theorem DISJOINT_FLOOKUP:
  DISJOINT (FDOM f1) (FDOM f2) ∧ FLOOKUP f1 k = SOME v ⇒ FLOOKUP f2 k = NONE
Proof
  rw[] >> imp_res_tac $ iffRL FDOM_FLOOKUP >> irule $ iffRL $ cj 1 flookup_thm >> ASM_SET_TAC[]
QED

Theorem esubsts_ok'_esubsts_ok:
  esubsts_ok' thy σ ∧ theory_ok' thy ⇒ esubsts_ok (thy.ctys, thy.ctms) σ
Proof
  Cases_on ‘σ’ >> rw[esubsts_ok_def, ctys_def, ctms_def]
  >> drule $ iffLR esubsts_ok'_def >> rw[] >> gvs[]
  >> first_x_assum drule >> rw[]
  >> simp[term_ok_def] >> fs[term_ok'_def, ctys_def, ctms_def, esubst_thy_def]
  >> simp[FLOOKUP_o_f, FLOOKUP_FUNION]
  >> gvs[FLOOKUP_FUNION, FLOOKUP_o_f] >> case_tac
  >- metis_tac[FDOM_FLOOKUP, FLOOKUP_FAPPLY, SUBSET_DEF]
  >> fs[theory_ok'_def] >> rw[]
  >- metis_tac[FDOM_FLOOKUP, FLOOKUP_FAPPLY, SUBSET_DEF, IN_DISJOINT]
  >- metis_tac[FDOM_FLOOKUP, FLOOKUP_FAPPLY, SUBSET_DEF, IN_DISJOINT]
  >- (dxrule term_ok'_imp_term_ok >> rw[ctms_def, ctys_def, esubst_sig_def]
      >> qsuff_tac ‘ty_esubst (q,r) o_f thy.tms = thy.tms’ >> simp[o_f_FUNION]
      >> irule ty_esubst_o_f_thy_tms >> simp[theory_ok'_def])
  >> metis_tac[FDOM_FLOOKUP, FLOOKUP_FAPPLY, SUBSET_DEF, IN_DISJOINT]
QED

Theorem esubst_thy_ctys[simp]:
  (esubst_thy σ thy).ctys = thy.ctys
Proof
  rw[esubst_thy_def, ctys_def]
QED

Theorem type_ok_ctys_ty_esubst:
  ∀ty.
    type_ok thy.ctys ty ∧
    esubsts_ok' thy σ ⇒
    type_ok thy.ctys (ty_esubst σ ty)
Proof
  Induct using type_ind >> rw[type_ok_def, ty_esubst_def]
  >> rpt case_tac >> gvs[EVERY_MEM] >> Induct_on ‘l’
  >> rw[type_ok_def, EVERY_MEM] >- metis_tac[]
  >> gvs[MEM_MAP, FORALL_PROD]
  >> namedCases_on ‘σ’ ["σ θ"]
  >> gvs[esubsts_ok'_def] >> last_x_assum $ qspec_then ‘m’ mp_tac
  >> rw[FDOM_FLOOKUP] >> gvs[FLOOKUP_FAPPLY]
  >> irule type_ok_TYPE_SUBST
  >> gvs[EVERY_MEM, MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS]
  >> rw[] >> drule MEM_ZIP_FST >> rw[] >> gvs[MEM_MAP]
QED

Theorem ty_esubst_type_ok':
  theory_ok' thy ∧ esubsts_ok' thy σ ∧ type_ok thy.ctys ty ⇒
  type_ok thy.ctys (ty_esubst σ ty)
Proof
  rw[] >> irule type_ok_ctys_ty_esubst >> simp[]
QED

Theorem esubst_thy_ctms_preserved:
  theory_ok' thy ∧ esubsts_ok' thy (σty, σtm) ∧
  FLOOKUP thy.ctms n = SOME ty0 ∧ n ∉ FDOM σtm ⇒
  FLOOKUP (esubst_thy (σty, σtm) thy).ctms n = SOME (ty_esubst (σty, σtm) ty0)
Proof
  strip_tac
  >> simp[esubst_thy_def, ctms_def, FLOOKUP_FUNION, FLOOKUP_o_f, FLOOKUP_FDIFF]
  >> Cases_on ‘FLOOKUP thy.tms n’
  >- (gvs[ctms_def, FLOOKUP_FUNION])
  >> ‘x = ty0’ by gvs[ctms_def, FLOOKUP_FUNION]
  >> gvs[]
  >> ‘ty_esubst (σty,σtm) ty0 = ty0’ by
       (irule ty_esubst_type_ok_id >> qexists ‘thy.tys’
        >> gvs[theory_ok'_def, esubsts_ok'_def]
        >> conj_tac
        >- metis_tac[DISJOINT_SUBSET, DISJOINT_SYM]
        >> first_x_assum irule >> simp[IN_FRANGE_FLOOKUP] >> metis_tac[])
  >> simp[]
QED

Theorem term_ok'_vsubst_variant:
  term_ok' thy tm ∧ type_ok thy.ctys ty ⇒
  term_ok' thy (VSUBST [(Var x1 ty, Var x2 ty)] tm)
Proof
  rw[]
  >> irule term_ok_imp_term_ok'
  >> irule term_ok_VSUBST
  >> simp[term_ok'_imp_term_ok, term_ok_def]
QED

Theorem esubst_ty0_tm_ok':
  ∀env σ avds tm subst_tm.
    esubst_ty0 env σ avds tm = return subst_tm ∧
    term_ok' thy tm ∧ theory_ok' thy ∧ esubsts_ok' thy σ ∧ esubsts_ok (thy.ctys, thy.ctms) σ ∧
    (∀v1 v2. MEM (v1, v2) env ⇒ ∃n ty. v1 = Var n ty ∧ v2 = Var n (ty_esubst σ ty)) ⇒
    term_ok' (esubst_thy σ thy) (esubst_tm σ subst_tm)
Proof
  recInduct esubst_ty0_ind >> rw[]
  >- (gvs[esubst_ty0_def, AllCaseEqs()]
      >> gvs[esubst_tm_def, term_ok'_def]
      >> irule type_ok_ctys_ty_esubst >> simp[])
  >- (gvs[esubst_ty0_def, esubst_tm_def]
      >> Cases_on ‘σ’ >> rename1 ‘(σ_ty, σ_tm)’
      >> qpat_x_assum ‘term_ok' thy (Const n ty)’ mp_tac
      >> simp[term_ok'_def] >> strip_tac
      >> Cases_on ‘FLOOKUP σ_tm n’
      >- (simp[term_ok'_def]
          >> drule esubst_thy_ctms_preserved
          >> rpt (disch_then drule)
          >> impl_tac >- gvs[FLOOKUP_DEF]
          >> strip_tac >> simp[]
          >> qpat_x_assum ‘ty = TYPE_SUBST _ _’ (assume_tac o GSYM) >> simp[]
          >> conj_tac
          >- (irule type_ok_ctys_ty_esubst >> simp[])
          >> metis_tac[ty_esubst_TYPE_SUBST])
      >> Cases_on ‘x’
      >> rename1 ‘FLOOKUP σ_tm n = SOME (repl, decl_ty)’
      >> drule (GEN_ALL ty_esubst_match_type)
      >> disch_then (qspecl_then [‘ty0’, ‘ty’] mp_tac)
      >> impl_tac >- (simp[] >> metis_tac[])
      >> strip_tac
      >> drule_then strip_assume_tac $ iffLR esubsts_ok'_def
      >> first_x_assum (qspec_then ‘n’ mp_tac)
      >> impl_tac >- metis_tac[FDOM_FLOOKUP]
      >> strip_tac
      >> qpat_x_assum ‘FLOOKUP σ_tm n = SOME _’ (mp_tac o REWRITE_RULE [FLOOKUP_FAPPLY])
      >> strip_tac
      >> qpat_x_assum ‘FDOM σ_tm ⊆ FDOM thy.etms’ (mp_tac o REWRITE_RULE [SUBSET_DEF])
      >> disch_then drule >> strip_tac
      >> qpat_x_assum ‘theory_ok' thy’ (mp_tac o REWRITE_RULE [theory_ok'_def])
      >> strip_tac
      >> qpat_x_assum ‘DISJOINT (FDOM thy.tms) (FDOM thy.etms)’
           (mp_tac o REWRITE_RULE [DISJOINT_ALT'])
      >> disch_then drule >> strip_tac
      >> qpat_x_assum ‘FLOOKUP thy.ctms n = SOME ty0’ mp_tac
      >> simp[ctms_def, FLOOKUP_FUNION, FLOOKUP_DEF] >> strip_tac
      >> gvs[FUNION_DEF]
      >> simp[]
      >> irule term_ok_imp_term_ok'
      >> irule term_ok_INST
      >> conj_tac
      >- (irule (GEN_ALL match_type_type_ok)
          >> first_assum (irule_at Any)
          >> simp[] >> irule type_ok_ctys_ty_esubst >> simp[])
      >> irule term_ok'_imp_term_ok >> simp[])
  >- (gvs[esubst_ty0_def, bind_EQ_return, term_ok'_def]
      >> simp[esubst_tm_def, term_ok'_def]
      >> rpt conj_tac
      >- (irule term_ok_welltyped >> rev_drule term_ok'_imp_term_ok
          >> disch_then $ irule_at Any)
      >- (irule term_ok_welltyped >> last_x_assum kall_tac
          >> rev_drule term_ok'_imp_term_ok >> disch_then $ irule_at Any)
      >> Cases_on ‘σ’ >> rename1 ‘(σty, σtm)’
      >> DEP_REWRITE_TAC[typeof_esubst_tm_esubst_ty0]
      >> conj_tac >> imp_res_tac theory_ok'_is_std_sig_ext
      >- (conj_tac >> rpt $ first_x_assum $ irule_at Any >> simp[term_ok'_imp_term_ok]
          >> rpt strip_tac >> first_x_assum drule >> simp[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS])
      >> imp_res_tac esubsts_ok'_esubsts_ok
      >> imp_res_tac term_ok'_imp_term_ok
      >> ‘typeof t1' = ty_esubst (σty,σtm) (typeof t1)’ by (
        irule typeof_esubst_ty >> rpt $ first_x_assum $ irule_at Any
        >> rpt strip_tac >> first_x_assum drule >> simp[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS])
      >> ‘typeof t2' = ty_esubst (σty,σtm) (typeof t2)’ by (
        irule typeof_esubst_ty >> rpt $ first_x_assum $ irule_at Any
        >> rpt strip_tac >> first_x_assum drule >> simp[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS])
      >> simp[ty_esubst_fun, SF SFY_ss])
  >> gvs[term_ok'_def, esubst_ty0_def, bind_EQ_return, bind_EQ_error, try_eq_return]
  >- (simp[esubst_tm_def, term_ok'_def]
      >> rpt conj_tac
      >- (irule ty_esubst_type_ok' >> metis_tac[])
      >> first_x_assum irule >> simp[] >> metis_tac[])
  >> gvs[AllCaseEqs(), bind_EQ_return]
  >> simp[esubst_tm_def, term_ok'_def]
  >> rw[]
  >- (irule ty_esubst_type_ok' >> metis_tac[])
  >> first_x_assum irule >> qexists ‘body1’
  >> rw[]
  >- metis_tac[]
  >> irule term_ok'_vsubst_variant
  >> simp[]
QED

Theorem esubst_term_ok':
  theory_ok' thy ∧ esubsts_ok' thy σ ∧ term_ok' thy tm ⇒
  term_ok' (esubst_thy σ thy) (esubst σ avds tm)
Proof
  strip_tac
  >> drule_all esubsts_ok'_esubsts_ok >> strip_tac
  >> simp[esubst_def, esubst_ty_def]
  >> ‘∃tm1. esubst_ty0 [] σ avds tm = return tm1’
       by metis_tac[esubst_ty0_always_returns, term_ok'_imp_term_ok]
  >> simp[]
  >> irule esubst_ty0_tm_ok'
  >> simp[] >> metis_tac[MEM]
QED

Theorem theory_ok'_esubst:
  theory_ok' thy ∧ esubsts_ok' thy σ ⇒ theory_ok' (esubst_thy σ thy)
Proof
  rw[theory_ok'_def]
  >- gvs[esubst_thy_def]
  >- (gvs[esubst_thy_def] >> dxrule in_frange_o_f >> rw[]
      >> irule type_ok_ctys_ty_esubst >> metis_tac[])
  >- gvs[esubst_thy_def]
  >- gvs[esubst_thy_def]
  >- (‘(esubst_thy σ thy).axs = IMAGE (esubst σ []) thy.axs’ by rw[esubst_thy_def]
      >> gvs[] >> irule esubst_term_ok' >> simp[theory_ok'_def] >> metis_tac[])
  >- (‘(esubst_thy σ thy).axs = IMAGE (esubst σ []) thy.axs’ by rw[esubst_thy_def]
      >> gvs[] >> irule esubst_has_type_bool_alt >> first_assum drule
      >> gvs[] >> rw[] >> qexists ‘thy’ >> rw[theory_ok'_def]
      >> irule esubsts_ok'_esubsts_ok >> simp[theory_ok'_def])
  >- (‘(esubst_thy σ thy).eaxs = IMAGE (esubst σ []) thy.eaxs’ by rw[esubst_thy_def]
      >> gvs[]
      >> irule esubst_term_ok' >> simp[theory_ok'_def] >> metis_tac[])
  >- (‘(esubst_thy σ thy).eaxs = IMAGE (esubst σ []) thy.eaxs’ by rw[esubst_thy_def]
      >> gvs[esubst_thy_def] >> irule esubst_has_type_bool_alt >> simp[]
      >> qexists ‘thy’ >> rw[theory_ok'_def]
      >> irule esubsts_ok'_esubsts_ok >> simp[theory_ok'_def])
  >- gvs[esubst_thy_def, sigof'_def]
QED

Theorem proves'_imp_theory_ok':
  ∀thy h es c. (thy, es, h) |-' c ⇒ theory_ok' thy
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[theory_ok'_esubst]
QED

Theorem term_ok_term_ok'_weakening:
  term_ok thy.sig p ⇒ term_ok' thy p
Proof
  rw[] >> irule term_ok_imp_term_ok'
  >> gvs[sigof'_def, ctms_def, ctys_def, term_ok_weakening]
QED

Theorem drop_thy_weakening:
  (drop_thy B thy', h) |- c ∧ B ⊆ A
  ∧ (∀ax. ax ∈ A ⇒ term_ok (thy'.ctys, thy'.ctms) ax ∧ ax has_type Bool)
  ⇒ (drop_thy A thy', h) |- c
Proof
  rw[drop_thy] >> irule axiom_weakening >> rw[]
  >> drule proves_imp_theory_ok >> rw[theory_ok_def, ctms_def, ctys_def]
  >> gvs[ctys_def, ctms_def] >> first_assum $ irule_at Any >> ASM_SET_TAC[]
QED

val contrapos_tac = CONV_TAC (REWR_CONV (DECIDE “p ⇒ q ⇔ ¬q ⇒ ¬p”)) THEN strip_tac

Theorem axioms_ok_no_var_collapse:
  axioms_ok thy axs ∧ esubsts_ok' thy σ ⇒ ∀ax. ax ∈ axs ⇒ no_var_collapse σ ax
Proof
  rw[axioms_ok_def]
QED

Theorem proves_esubst_drop_thy:
  (drop_thy es thy, h) |- c ∧
  theory_ok' thy ∧
  esubsts_ok' thy σ ∧
  axioms_ok thy thy.axs ∧
  (∀ax. ax ∈ es ⇒ no_var_collapse σ ax) ⇒
  (drop_thy (IMAGE (esubst σ []) es) (esubst_thy σ thy),
   term_image (esubst σ []) h) |- esubst σ (FLAT (MAP tm_names h)) c
Proof
  rw[drop_thy] >> drule_at (Pat ‘_ |- _’) proves_substitutable
  >> disch_then $ qspec_then ‘σ’ mp_tac >> impl_tac
  >- (conj_tac >- metis_tac[proves_theory_ok]
      >> conj_tac >- metis_tac[esubsts_ok'_esubsts_ok]
      >> fs[theory_ok'_def] >> imp_res_tac axioms_ok_no_var_collapse
      >> rw[] >> res_tac >> first_x_assum irule)
  >> simp[ctms_def, ctys_def, esubst_thy_def, esubst_sig_def]
  >> qsuff_tac ‘ty_esubst σ o_f thy.tms = thy.tms’
  >- (rw[o_f_FUNION] >> irule axiom_weakening >> first_x_assum $ irule_at Any)
  >> irule ty_esubst_o_f_thy_tms >> simp[]
QED

Theorem theory_ok'_lift_thy[simp]:
  theory_ok thy ⇒
  theory_ok' (lift_thy thy)
Proof
  rw[theory_ok_def, theory_ok'_def, axioms_ok_def]
  >> first_assum irule >> Cases_on ‘σ’ >> fs[esubsts_ok_def, esubsts_ok'_def]
  >> rpt strip_tac >> first_x_assum drule >> simp[term_ok_def, term_ok'_def]
  >> rw[] >> fs[term_ok_def, term_ok'_def, FLOOKUP_o_f] >> every_case_tac
  >> fs[esubst_thy_def, lift_thy_def, ctms_def, ctys_def]
  >> drule $ iffLR FDOM_F_FEMPTY1 >> rw[] >> ASM_SET_TAC[FRANGE_FEMPTY]
QED

Theorem proves_imp_proves'_subset_axs:
  ∀thy h c.
    (thy, h) |- c ⇒
    ∀thy'.
      tysof thy = thy'.ctys ∧
      tmsof thy = thy'.ctms ∧
      axsof thy ⊆ thy'.axs ∧
      theory_ok' thy' ⇒
      (thy', ∅, h) |-' c
Proof
  Induct_on ‘$|-’ >> rw[] >> res_tac
  >- (irule proves'_ABS >> gvs[])
  >- (irule proves'_ASSUME >> simp[] >> irule term_ok_imp_term_ok' >> Cases_on ‘sigof thy’ >> gvs[])
  >- (irule proves'_BETA >> Cases_on ‘sigof thy’ >> gvs[]
      >> irule term_ok_imp_term_ok' >> simp[])
  >- (drule_at_then Any rev_drule proves'_DEDUCT_ANTISYM >> simp[])
  >- (metis_tac[proves'_EQ_MP, UNION_EMPTY])
  >- (irule proves'_INST >> simp[] >> rw[]
      >> Cases_on ‘sigof thy’ >> gvs[]
      >> first_x_assum drule >> rw[]
      >> rpt $ first_x_assum $ irule_at Any
      >> simp[term_ok_imp_term_ok'])
  >- (irule proves'_INST_TYPE >> gvs[])
  >- (drule_at_then Any rev_drule proves'_MK_COMB >> simp[])
  >- (irule proves'_REFL >> simp[] >> irule term_ok_imp_term_ok' >> Cases_on ‘sigof thy’ >> gvs[])
  >> irule proves'_axioms >> gvs[SUBSET_DEF]
QED

Theorem proves_imp_proves':
  ∀thy' h c.
    (thy', h) |- c ⇒
    (lift_thy thy', {}, h) |-' c
Proof
  rpt strip_tac >> irule proves_imp_proves'_subset_axs
  >> first_assum $ irule_at Any >> simp[ctys_def, ctms_def]
  >> drule proves_theory_ok >> simp[theory_ok'_lift_thy]
QED

Theorem proves'_imp_proves:
  ∀thy' c h used_eaxs.
    (thy', used_eaxs, h) |-' c ⇒ (drop_thy used_eaxs thy', h) |- c
Proof
  Induct_on ‘$|-'’ >> rw[]
  >- (irule proves_ABS >> rw[])
  >- (irule proves_ASSUME >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_BETA >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_DEDUCT_ANTISYM >> conj_tac >> irule drop_thy_weakening
      >> imp_res_tac proves_theory_ok >> gvs[theory_ok_def, drop_thy]
      >> (conj_tac >- metis_tac[term_ok'_imp_term_ok]
          >> metis_tac[SUBSET_UNION]))
  >- (irule proves_EQ_MP
      >> imp_res_tac proves_theory_ok >> gvs[theory_ok_def, drop_thy]
      >> first_x_assum $ irule_at Any >> simp[]
      >> conj_tac >> irule axiom_weakening >> simp[DISJ_IMP_THM]
      >> first_x_assum $ irule_at Any >> simp[SUBSET_DEF])
  >- (irule proves_INST >> rw[] >> first_x_assum drule
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_INST_TYPE >> rw[] >> first_x_assum drule
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_MK_COMB >> rw[]
      >> imp_res_tac proves_theory_ok >> gvs[theory_ok_def, drop_thy]
      >> irule axiom_weakening >> simp[DISJ_IMP_THM]
      >> first_x_assum $ irule_at Any >> simp[SUBSET_DEF])
  >- (irule proves_REFL >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_axioms >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok]
      >> metis_tac[axsof_drop_thy, SUBSET_DEF])
  >- (Cases_on ‘c ∈ thy.axs’ >> gvs[drop_thy]
      >- (rw[thy_axs_diff_alt, UNION_COMM] >> irule axiom_weakening
          >> drule proves'_imp_theory_ok' >> rw[]
          >> gvs[theory_ok'_def, term_ok'_imp_term_ok, term_ok_term_ok'_weakening]
          >> imp_res_tac proves_theory_ok >> gvs[theory_ok_def, drop_thy]
          >> first_x_assum $ irule_at Any >> simp[SUBSET_DEF])
      >- (rw[thy_axs_diff]
          >> qspecl_then [‘((thy.ctys, thy.ctms), thy.axs ∪ es1)’,
                          ‘((thy.ctys, thy.ctms), thy.axs ∪ es2)’,
                          ‘h2’, ‘c’, ‘c'’]
                         assume_tac axioms_eliminable
          >> gvs[]))
  >- (drule proves'_imp_theory_ok' >> strip_tac
      >> irule proves_esubst_drop_thy >> metis_tac[])
  >- (irule proves_axioms >> rw[]
      >- (irule theory_ok_drop_thy_alt >> gvs[theory_ok'_def])
      >> rw[drop_thy])
QED

Theorem extends'_ind:
  ∀P. (∀upd ctxt. upd updates' ctxt ∧ P ctxt ⇒ P (upd::ctxt)) ⇒
    ∀ctxt1 ctxt2. ctxt2 extends' ctxt1 ⇒ P ctxt1 ⇒ P ctxt2
Proof
  gen_tac >> strip_tac >>
  simp[extends'_def] >>
  CONV_TAC SWAP_FORALL_CONV >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >> first_x_assum match_mp_tac >>
  rw[]
QED

Theorem SUBMAP_FUNION_mono:
  f1 ⊑ f2 ∧ DISJOINT (FDOM f2) (FDOM g) ⇒ f1 ⊌ g ⊑ f2 ⊌ g
Proof
  rw[SUBMAP_DEF, FUNION_DEF, FDOM_FUNION, FAPPLY_FUPDATE_THM] >>
  metis_tac[IN_DISJOINT]
QED

Theorem SUBMAP_FUNION_mono_r:
  g1 ⊑ g2 ⇒ f ⊌ g1 ⊑ f ⊌ g2
Proof
  rw[SUBMAP_DEF, FUNION_DEF, FDOM_FUNION] >> metis_tac[]
QED

Theorem term_ok'_eq:
  ∀tm.
    thy1.ctys = thy2.ctys ∧ thy1.ctms = thy2.ctms ⇒
    (term_ok' thy1 tm ⇔ term_ok' thy2 tm)
Proof
  Induct >> rw[term_ok'_def]
QED

Theorem type_ok_ctys_subset:
  ∀ty.
    thy1.ctys ⊑ thy2.ctys ∧
    type_ok thy1.ctys ty ⇒
    type_ok thy2.ctys ty
Proof
  Induct using type_ind >> rw[type_ok_def]
  >> fs[EVERY_MEM]
  >> drule FLOOKUP_SUBMAP >> simp[]
QED

Theorem term_ok'_ctms_ctys_subset:
  ∀tm.
    thy1.ctys ⊑ thy2.ctys ∧
    thy1.ctms ⊑ thy2.ctms ⇒
    term_ok' thy1 tm ⇒
    term_ok' thy2 tm
Proof
  Induct >> rw[term_ok'_def]
  >> drule_all type_ok_ctys_subset >> rw[]
  >> metis_tac[FLOOKUP_SUBMAP]
QED

Theorem type_ok_FUPDATE_fresh:
  ∀tys name a ty.
    type_ok tys ty ∧ name ∉ FDOM tys ⇒
    type_ok (tys |+ (name, a)) ty
Proof
  ntac 3 gen_tac >> Induct using type_ind >> rw[type_ok_def]
  >> fs[EVERY_MEM, FLOOKUP_FUPDATE] >> case_tac >> fs[FDOM_FLOOKUP]
QED

Theorem term_ok'_tms_FUNION_fresh:
  ∀thy alist p.
    term_ok' thy p ∧
    (∀s. MEM s (MAP FST alist) ⇒ s ∉ FDOM thy.tms) ∧
    (∀s. MEM s (MAP FST alist) ⇒ s ∉ FDOM thy.etms) ⇒
    term_ok' (thy with tms := alist_to_fmap alist ⊌ thy.tms) p
Proof
  rw[] >> irule term_ok'_ctms_ctys_subset
  >> first_x_assum $ irule_at Any
  >> rw[ctys_def, ctms_def, FUNION_ASSOC]
  >> rw[SUBMAP_DEF, FUNION_DEF, FDOM_FUNION, FDOM_alist_to_fmap]
  >> simp[] >> rpt (IF_CASES_TAC >> gvs[]) >> res_tac
QED

Theorem proves'_theory_ok':
  ∀thy es h c. (thy,es,h) |-' c ⇒ theory_ok' thy
Proof
  Induct_on ‘$|-'’ >> rw[theory_ok'_esubst]
QED

Theorem term_ok'_welltyped:
  ∀thy t. term_ok' thy t ⇒ welltyped t
Proof
  rpt strip_tac >> dxrule term_ok'_imp_term_ok >> simp[term_ok_welltyped, SF SFY_ss]
QED

Theorem term_ok'_type_ok:
  ∀sig t. theory_ok' thy ∧ term_ok' thy t ⇒ type_ok thy.ctys (typeof t)
Proof
  rpt strip_tac >> dxrule term_ok'_imp_term_ok
  >> strip_tac >> dxrule_at Any term_ok_type_ok
  >> simp[theory_ok'_is_std_sig_ext]
QED

Theorem term_ok'_equation:
  theory_ok' thy ⇒
  (term_ok' thy (s === t) ⇔
     term_ok' thy s ∧ term_ok' thy t ∧ typeof t = typeof s)
Proof
  rw[EQ_IMP_THM, equation_def, term_ok'_def, sigof'_def,
     is_std_sig_def, ctms_def, ctys_def, FLOOKUP_FUNION]
  >> simp[type_ok_def, FLOOKUP_FUNION, term_ok'_welltyped, SF SFY_ss]
  >> every_case_tac >> fs[theory_ok'_def, is_std_sig_def, FLOOKUP_FUNION, sigof'_def]
  >> rev_drule_at Any term_ok'_type_ok >> simp[ctys_def, theory_ok'_def, is_std_sig_def, sigof'_def]
  >> strip_tac >> qexists ‘[(typeof s, Tyvar «A»)]’ >> simp[REV_ASSOCD]
QED

Theorem term_ok'_VSUBST:
  ∀sig tm ilist.
    term_ok' thy tm ∧
    (∀s s'.
       MEM (s',s) ilist ⇒
       ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok' thy s') ⇒
    term_ok' thy (VSUBST ilist tm)
Proof
  rw[] >> irule term_ok_imp_term_ok' >> irule term_ok_VSUBST
  >> drule term_ok'_imp_term_ok >> rw[] >> first_x_assum drule >> rw[term_ok'_imp_term_ok]
QED

Theorem term_ok'_INST:
  ∀thy tyin tm.
    term_ok' thy tm ∧ EVERY (type_ok thy.ctys) (MAP FST tyin) ⇒
    term_ok' thy (INST tyin tm)
Proof
  rw[] >> irule term_ok_imp_term_ok' >> irule term_ok_INST
  >> drule term_ok'_imp_term_ok >> rw[] >> first_x_assum drule >> rw[term_ok'_imp_term_ok]
QED

Theorem proves'_term_ok':
  ∀thy h tm. (thy,h) |-' tm ⇒ term_ok' thy tm ∧ tm has_type Bool
Proof
  Induct_on ‘$|-'’ >> rw[] >> imp_res_tac proves'_theory_ok' >> imp_res_tac has_type_typeof
  >> fs[term_ok'_def, EQUATION_HAS_TYPE_BOOL, term_ok'_welltyped, SF SFY_ss, typeof_has_type, term_ok'_equation]
  >> imp_res_tac $ iffLR EQUATION_HAS_TYPE_BOOL
  >- (drule ACONV_TYPE >> simp[term_ok'_welltyped, SF SFY_ss])
  >- (irule term_ok'_VSUBST >> rw[])
  >- (irule VSUBST_HAS_TYPE >> rw[] >> metis_tac[])
  >- (irule term_ok'_INST >> simp[])
  >- (irule INST_HAS_TYPE >> first_x_assum $ irule_at Any >> simp[TYPE_SUBST_Bool])
  >- metis_tac[] >- metis_tac[]
  >- fs[theory_ok'_def] >- fs[theory_ok'_def]
  >- (irule esubst_term_ok' >> simp[])
  >- (irule esubst_has_type_bool_alt >> first_assum $ irule_at Any
      >> simp[esubsts_ok'_esubsts_ok])
  >> fs[theory_ok'_def]
QED

Theorem MAP_FST_MAP[simp]:
  ∀l P. MAP FST (MAP (λ(s,t). (s,P t)) l) = MAP FST l
Proof
  Induct >> simp[MAP, FST] >> Cases >> rw[MAP, FST]
QED

Theorem constspec_conext_well_formed:
  ∀thy eqs prop.
    theory_ok' thy ∧
    (thy, ∅, MAP (λ(s,t). Var s (typeof t) === t) eqs) |-' prop ∧
    EVERY (λt. CLOSED t ∧ ∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t)))
          (MAP SND eqs) ∧
    ALL_DISTINCT (MAP FST eqs) ∧
    (∀x ty. VFREE_IN (Var x ty) prop ⇒
            MEM (x, ty) (MAP (λ(s,t). (s, typeof t)) eqs)) ∧
    (∀s. MEM s (MAP FST eqs) ⇒ s ∉ FDOM thy.tms) ∧
    (∀s. MEM s (MAP FST eqs) ⇒ s ∉ FDOM thy.etms) ∧
    (∀s t. MEM (s,t) eqs ⇒ type_ok thy.tys (typeof t)) ⇒
    let cprop = VSUBST (MAP (λ(s,t). (Const s (typeof t), Var s (typeof t))) eqs)
                       prop in
      let thy'  = thy with tms := alist_to_fmap (MAP (λ(s,t). (s, typeof t)) eqs)
                                                ⊌ thy.tms in
        term_ok' thy' cprop ∧ cprop has_type Bool
Proof
  rw[LET_THM]
  >> drule proves'_term_ok' >> strip_tac
  >- (irule term_ok'_VSUBST >> conj_tac
      >- (rw[MEM_MAP, PULL_EXISTS, FORALL_PROD, term_ok'_def]
          >> simp[ctms_def, ctys_def, FLOOKUP_DEF, FDOM_FUNION, FDOM_alist_to_fmap,
                  FUNION_DEF, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
          >> simp[SF SFY_ss] >> DEP_REWRITE_TAC[type_ok_weakening] >> conj_tac
          >- (first_x_assum drule >> simp[])
          >> qexists‘[]’ >> simp[VSUBST_NIL]
          >> sym_tac >> irule ALOOKUP_SOME_FAPPLY_alist_to_fmap
          >> irule ALOOKUP_ALL_DISTINCT_MEM >> fs[MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
          >> first_x_assum $ irule_at Any >> simp[])
      >> irule term_ok'_tms_FUNION_fresh >> simp[])
  >> irule VSUBST_HAS_TYPE >> rw[] >> fs[MEM_MAP, PULL_EXISTS, FORALL_PROD]
  >> Cases_on ‘y’ >> gvs[]
QED

Theorem typedefn_eq1_well_formed[local]:
  ∀thy name pred abs rep witness.
    theory_ok' thy ∧
    (thy, ∅, []) |-' Comb pred witness ∧
    CLOSED pred ∧
    name ∉ FDOM thy.tys ∧ name ∉ FDOM thy.etys ∧
    abs  ∉ FDOM thy.tms ∧ abs  ∉ FDOM thy.etms ∧
    rep  ∉ FDOM thy.tms ∧ rep  ∉ FDOM thy.etms ∧
    abs ≠ rep ∧
    type_ok thy.tys (typeof witness) ⇒
    let abs_type =
        Tyapp name (MAP Tyvar
                        (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
      let rep_type = domain (typeof pred) in
        let thy' = thy with
                       <| tys := thy.tys |+ (name, LENGTH (tvars pred));
                          tms := thy.tms |+ (abs, Fun rep_type abs_type)
                                    |+ (rep, Fun abs_type rep_type) |> in
          let eq1 = Comb (Const abs (Fun rep_type abs_type))
                         (Comb (Const rep (Fun abs_type rep_type))
                               (Var (strlit "a") abs_type))
                         === Var (strlit "a") abs_type in
            term_ok' thy' eq1 ∧ eq1 has_type Bool
Proof
  rw[LET_THM] >> drule proves'_term_ok' >> strip_tac
  >> gvs[term_ok'_def]
  >> drule theory_ok'_is_std_sig_ext >> rw[is_std_sig_def, ctms_def, ctys_def]
  >> simp[equation_def, term_ok'_def, typeof_def, codomain_def,
          EQUATION_HAS_TYPE_BOOL, has_type_cases,
          ctms_def, ctys_def, FUNION_FUPDATE_1, FLOOKUP_FUPDATE, FLOOKUP_FUNION,
          type_ok_def, FDOM_FUPDATE, FDOM_FUNION, EVERY_MAP, EVERY_MEM]
  >> rpt (IF_CASES_TAC >> gvs[FDOM_FUNION, FLOOKUP_DEF])
  >> qmatch_goalsub_abbrev_tac ‘Tyapp name tvs’
  >> rw[type_ok_FUPDATE_fresh, FDOM_FUNION, type_ok_weakening]
  >> qexists ‘[(Tyapp name tvs, Tyvar «A»)]’ >> simp[REV_ASSOCD_def]
QED

Theorem typedefn_eq2_well_formed[local]:
  ∀thy name pred abs rep witness.
    theory_ok' thy ∧
    (thy, ∅, []) |-' Comb pred witness ∧
    CLOSED pred ∧
    name ∉ FDOM thy.tys ∧ name ∉ FDOM thy.etys ∧
    abs  ∉ FDOM thy.tms ∧ abs  ∉ FDOM thy.etms ∧
    rep  ∉ FDOM thy.tms ∧ rep  ∉ FDOM thy.etms ∧
    abs ≠ rep ∧
    type_ok thy.tys (typeof witness) ⇒
    let abs_type =
        Tyapp name (MAP Tyvar
                        (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
      let rep_type = domain (typeof pred) in
        let thy' = thy with
                       <| tys := thy.tys |+ (name, LENGTH (tvars pred));
                          tms := thy.tms |+ (abs, Fun rep_type abs_type)
                                    |+ (rep, Fun abs_type rep_type) |> in
          let eq2 = Comb pred (Var (strlit "r") rep_type)
                         === (Comb (Const rep (Fun abs_type rep_type))
                                   (Comb (Const abs (Fun rep_type abs_type))
                                         (Var (strlit "r") rep_type))
                                   === Var (strlit "r") rep_type) in
            term_ok' thy' eq2 ∧ eq2 has_type Bool
Proof
  rw[LET_THM] >> drule proves'_term_ok' >> strip_tac
  >> gvs[term_ok'_def]
  >> imp_res_tac WELLTYPED_LEMMA >> gvs[typeof_def, codomain_def]
  >> drule theory_ok'_is_std_sig_ext >> rw[is_std_sig_def, ctms_def, ctys_def]
  >> simp[equation_def, term_ok'_def, typeof_def, codomain_def,
          EQUATION_HAS_TYPE_BOOL, has_type_cases,
          ctms_def, ctys_def, FUNION_FUPDATE_1, FLOOKUP_FUPDATE, FLOOKUP_FUNION,
          type_ok_def, FDOM_FUPDATE, FDOM_FUNION, EVERY_MAP, EVERY_MEM]
  >> rpt (IF_CASES_TAC >> gvs[FDOM_FUNION, FLOOKUP_DEF])
  >> rw[type_ok_FUPDATE_fresh, FDOM_FUNION, type_ok_weakening]
  >> TRY (qexists ‘[(Bool, Tyvar «A»)]’ >> simp[REV_ASSOCD_def] >> NO_TAC)
  >> TRY (qexists ‘[(typeof witness, Tyvar «A»)]’ >> simp[REV_ASSOCD_def] >> NO_TAC)
  >> irule term_ok'_ctms_ctys_subset >> first_x_assum $ irule_at Any
  >> rw[ctys_def, ctms_def, FUNION_FUPDATE_1]
  >> rw[SUBMAP_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM, FDOM_FUNION]
  >> metis_tac[FDOM_FUPDATE, IN_INSERT]
QED

Theorem updates'_theory_ok':
  ∀upd ctxt. upd updates' ctxt ⇒ theory_ok' (ethyof ctxt) ⇒ theory_ok' (ethyof (upd::ctxt))
Proof
  Induct_on ‘$updates'’ >> rw[]
  >> fs[conexts_of_upd'_def, theory_ok'_def, ctys_def, ctms_def, sigof'_def]
  >- suspend "NewAxiom"
  >- suspend "NewConst"
  >- suspend "ConstSpec"
  >- suspend "NewType"
  >- suspend "TypeDefn"
  >- suspend "NewEliminableType"
  >- suspend "NewEliminableConst"
  >- suspend "NewEliminableAxiom"
QED

Resume updates'_theory_ok'[NewAxiom]:
  rw[] >> simp[]
  >- (irule term_ok_imp_term_ok' >> simp[ctys_def, ctms_def]
      >> metis_tac[term_ok_weakening])
  >> first_x_assum drule >> strip_tac >> irule $ iffLR term_ok'_eq
  >> first_x_assum $ irule_at Any >> simp[ctms_def, ctys_def]
QED

Resume updates'_theory_ok'[NewConst]:
  rw[] >> simp[]
  >- (last_x_assum irule >> metis_tac[FRANGE_DOMSUB_SUBSET, SUBSET_DEF])
  >> fs[is_std_sig_def, term_ok'_def]
  >- (irule term_ok'_ctms_ctys_subset
      >> first_x_assum drule >> strip_tac >> first_x_assum $ irule_at Any
      >> simp[ctys_def, ctms_def, SUBMAP_FUNION_mono])
  >- (irule term_ok'_ctms_ctys_subset
      >> first_x_assum drule >> strip_tac >> first_x_assum $ irule_at Any
      >> simp[ctys_def, ctms_def, SUBMAP_FUNION_mono])
  >> simp[FLOOKUP_FUPDATE] >> every_case_tac >> drule ALOOKUP_MEM
  >> fs[MEM_MAP]
QED

Resume updates'_theory_ok'[ConstSpec]:
  rw[] >> simp[]
  >- (gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FUNION, AllCaseEqs()]
      >- (first_x_assum irule >> simp[IN_FRANGE_FLOOKUP] >> metis_tac[])
      >> gvs[ALOOKUP_MAP] >> drule ALOOKUP_MEM >> rw[] >> first_x_assum drule >> simp[])
  >- rw[MAP_MAP_o, o_DEF, LAMBDA_PROD, DISJOINT_ALT, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
  >- (qmatch_asmsub_abbrev_tac ‘(thy_orig, ∅, _) |-' prop’ >> rev_drule proves'_theory_ok'
      >> strip_tac >> irule $ iffLR term_ok'_eq >> drule constspec_conext_well_formed
      >> disch_then drule >> impl_tac
      >- (rw[MEM_MAP, EXISTS_PROD, PULL_EXISTS]
          >> fs[MEM_MAP, FST, EXISTS_PROD, PULL_EXISTS, FORALL_PROD]
          >> rpt $ first_x_assum drule >> unabbrev_all_tac
          >> rw[FDOM_alist_to_fmap, MEM_MAP, FORALL_PROD])
      >> rw[LET_THM] >> first_x_assum $ irule_at Any >> simp[ctms_def, ctys_def]
      >> unabbrev_all_tac >> rw[FDOM_alist_to_fmap, MEM_MAP, FORALL_PROD])
  >- (irule VSUBST_HAS_TYPE >> rw[MEM_MAP, FORALL_PROD, LAMBDA_PROD, EXISTS_PROD]
      >> rev_dxrule proves'_term_ok' >> simp[])
  >- (first_x_assum drule >> strip_tac
      >> irule term_ok'_ctms_ctys_subset >> first_x_assum $ irule_at Any
      >> simp[ctms_def, ctys_def, FUNION_ASSOC]
      >> simp[FDOM_alist_to_fmap, FDOM_FUNION, IN_DISJOINT, MEM_MAP, FORALL_PROD]
      >> REWRITE_TAC[GSYM FUNION_ASSOC]
      >> irule $ cj 2 SUBMAP_FUNION_ID
      >> rw[FDOM_alist_to_fmap, FDOM_FUNION, IN_DISJOINT, MEM_MAP, FORALL_PROD]
      >> metis_tac[MEM_MAP, FST, PAIR])
  >- (first_x_assum drule >> strip_tac
      >> irule term_ok'_ctms_ctys_subset >> first_x_assum $ irule_at Any
      >> simp[ctms_def, ctys_def, FUNION_ASSOC]
      >> simp[FDOM_alist_to_fmap, FDOM_FUNION, IN_DISJOINT, MEM_MAP, FORALL_PROD]
      >> REWRITE_TAC[GSYM FUNION_ASSOC]
      >> irule $ cj 2 SUBMAP_FUNION_ID
      >> rw[FDOM_alist_to_fmap, FDOM_FUNION, IN_DISJOINT, MEM_MAP, FORALL_PROD]
      >> metis_tac[MEM_MAP, FST, PAIR])
  >> irule is_std_sig_extend >> first_x_assum $ irule_at Any >> simp[]
  >> irule $ cj 2 SUBMAP_FUNION_ID
  >> simp[FDOM_alist_to_fmap, IN_DISJOINT, MEM_MAP, FORALL_PROD]
  >> metis_tac[MEM_MAP, FST, PAIR]
QED

Resume updates'_theory_ok'[NewType]:
  rw[] >> simp[FUNION_FUPDATE_1, type_ok_FUPDATE_fresh]
  >- (irule term_ok'_ctms_ctys_subset
      >> first_x_assum drule >> strip_tac >> first_x_assum $ irule_at Any
      >> simp[ctys_def, ctms_def, SUBMAP_FUNION_mono])
  >- (irule term_ok'_ctms_ctys_subset
      >> first_x_assum drule >> strip_tac >> first_x_assum $ irule_at Any
      >> simp[ctys_def, ctms_def, SUBMAP_FUNION_mono])
  >> irule is_std_sig_extend >> first_x_assum $ irule_at Any >> simp[]
QED

Resume updates'_theory_ok'[TypeDefn]:
  qabbrev_tac
    ‘abs_type = Tyapp name (MAP Tyvar (MAP implode
                            (STRING_SORT (MAP explode (tvars pred)))))’ >>
  qabbrev_tac ‘rep_type = domain (typeof pred)’ >>
  qabbrev_tac ‘abs_ty   = Fun rep_type abs_type’ >>
  qabbrev_tac ‘rep_ty   = Fun abs_type rep_type’ >>
  qabbrev_tac ‘thy_orig =
     <|tms := tmsof' ctxt; tys := tysof' ctxt; axs := axsof' ctxt;
       etms := etmsof ctxt; etys := etysof ctxt; eaxs := eaxsof ctxt|>’
  >> drule proves'_theory_ok' >> strip_tac
  >> drule_then (drule_then drule) typedefn_eq1_well_formed
  >> disch_then $ qspecl_then [‘name’, ‘abs’, ‘rep’] mp_tac >> impl_tac
  >- (unabbrev_all_tac >> simp[FDOM_alist_to_fmap, MEM_MAP, FORALL_PROD])
  >> drule_then (drule_then drule) typedefn_eq2_well_formed
  >> disch_then $ qspecl_then [‘name’, ‘abs’, ‘rep’] mp_tac >> impl_tac
  >- (unabbrev_all_tac >> fs[FDOM_alist_to_fmap, MEM_MAP, FORALL_PROD])
  >> rw[LET_THM]
  >- (simp[Abbr ‘abs_ty’, type_ok_def] >> conj_tac
      >- (‘is_std_sig ((tysof' ctxt)⟨name ↦ LENGTH (tvars pred)⟩, tmsof' ctxt)’
            suffices_by simp[is_std_sig_def]
          >> irule is_std_sig_extend >> first_x_assum $ irule_at Any >> simp[])
      >> conj_tac
      >- (‘typeof witness = domain (typeof pred)’ by (
           drule proves'_imp_proves >> simp[] >> strip_tac
           >> drule proves_term_ok >> simp[term_ok_def, term_ok_clauses]
           >> rw[]
           >> imp_res_tac WELLTYPED_LEMMA >> fs[])
          >> simp[Abbr ‘rep_type’]
          >> ‘type_ok (tysof' ctxt) (domain (typeof pred))’ by metis_tac[]
          >> irule type_ok_FUPDATE_fresh >> simp[])
      >- simp[Abbr ‘abs_type’, type_ok_def, FLOOKUP_UPDATE,
              EVERY_MAP, LENGTH_MAP, STRING_SORT_def])
  >- (fs[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE]
      >> Cases_on ‘k = rep’ >> gvs[]
      >- (simp[Abbr ‘rep_ty’, type_ok_def] >> rpt conj_tac
          >- (‘is_std_sig ((tysof' ctxt)⟨name ↦ LENGTH (tvars pred)⟩, tmsof' ctxt)’
                suffices_by simp[is_std_sig_def]
              >> irule is_std_sig_extend >> first_x_assum $ irule_at Any >> simp[])
          >- simp[Abbr ‘abs_type’, type_ok_def, FLOOKUP_UPDATE,
                  EVERY_MAP, LENGTH_MAP, STRING_SORT_def]
          >> ‘typeof witness = domain (typeof pred)’ by (
            drule proves'_imp_proves >> simp[] >> strip_tac
            >> drule proves_term_ok >> simp[term_ok_def, term_ok_clauses]
            >> rw[] >> imp_res_tac WELLTYPED_LEMMA >> fs[])
          >> simp[Abbr ‘rep_type’]
          >- (‘type_ok (tysof' ctxt) (domain (typeof pred))’ by metis_tac[]
              >> irule type_ok_FUPDATE_fresh >> simp[] >> metis_tac[])
          >> irule type_ok_FUPDATE_fresh >> simp[] >> metis_tac[])
      >- (irule type_ok_FUPDATE_fresh >> simp[] >> metis_tac[IN_FRANGE_FLOOKUP]))
  >- (first_x_assum drule >> strip_tac >> simp[FUNION_FUPDATE_1]
      >> irule type_ok_FUPDATE_fresh >> simp[FDOM_FUNION])
  >- (irule $ iffRL term_ok'_eq >> first_x_assum $ irule_at Any >> simp[ctms_def, ctys_def]
      >> unabbrev_all_tac >> simp[FUPDATE_COMMUTES])
  >- (irule $ iffRL EQUATION_HAS_TYPE_BOOL >> simp[welltyped_comb]
      >> unabbrev_all_tac >> simp[])
  >- (irule $ iffRL term_ok'_eq >> first_x_assum $ irule_at Any >> simp[ctms_def, ctys_def]
      >> unabbrev_all_tac >> simp[FUPDATE_COMMUTES])
  >- (irule $ iffRL EQUATION_HAS_TYPE_BOOL >> simp[welltyped_comb]
      >> unabbrev_all_tac >> imp_res_tac $ iffLR EQUATION_HAS_TYPE_BOOL
      >> fs[welltyped_comb, typeof_def] >> metis_tac[])
  >- (first_x_assum drule >> strip_tac
      >> irule term_ok'_ctms_ctys_subset >> first_x_assum $ irule_at Any
      >> unabbrev_all_tac >> simp[ctms_def, ctys_def, FUNION_FUPDATE_1]
      >> simp[SUBMAP_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> rw[] >> simp[])
  >- (first_x_assum drule >> simp[])
  >- (first_x_assum drule >> strip_tac
      >> irule term_ok'_ctms_ctys_subset >> first_x_assum $ irule_at Any
      >> unabbrev_all_tac >> simp[ctms_def, ctys_def, FUNION_FUPDATE_1]
      >> simp[SUBMAP_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> rw[] >> simp[])
  >> irule is_std_sig_extend >> first_x_assum $ irule_at Any
  >> rw[SUBMAP_DEF, FAPPLY_FUPDATE_THM, AllCaseEqs(), FDOM_alist_to_fmap, MEM_MAP]
  >> disj2_tac >> metis_tac[MEM_MAP]
QED

Resume updates'_theory_ok'[NewEliminableType]:
  rw[] >> simp[FUNION_FUPDATE_1, FUNION_FUPDATE_2, type_ok_FUPDATE_fresh]
  >- (irule term_ok'_ctms_ctys_subset
      >> first_x_assum drule >> strip_tac >> first_x_assum $ irule_at Any
      >> simp[ctys_def, ctms_def, SUBMAP_FUNION_mono_r])
  >- (irule term_ok'_ctms_ctys_subset
      >> first_x_assum drule >> strip_tac >> first_x_assum $ irule_at Any
      >> simp[ctys_def, ctms_def, SUBMAP_FUNION_mono_r])
  >> metis_tac[FRANGE_DOMSUB_SUBSET, SUBSET_TRANS]
QED

Resume updates'_theory_ok'[NewEliminableConst]:
  rw[] >> simp[FUNION_FUPDATE_1, FUNION_FUPDATE_2, type_ok_FUPDATE_fresh]
  >- (first_x_assum irule >> metis_tac[FRANGE_DOMSUB_SUBSET, SUBSET_DEF])
  >> irule term_ok'_ctms_ctys_subset
  >> first_x_assum drule >> strip_tac >> first_x_assum $ irule_at Any
  >> simp[ctys_def, ctms_def, SUBMAP_FUNION_mono_r]
QED

Resume updates'_theory_ok'[NewEliminableAxiom]:
  rw[] >> simp[FUNION_FUPDATE_1, FUNION_FUPDATE_2, type_ok_FUPDATE_fresh]
  >> irule term_ok'_ctms_ctys_subset >> res_tac >> first_x_assum $ irule_at Any
  >> simp[ctys_def, ctms_def, SUBMAP_FUNION_mono_r]
QED

Finalise updates'_theory_ok'

Theorem extends'_theory_ok':
  ∀ctxt1 ctxt2. ctxt2 extends' ctxt1 ⇒ theory_ok' (ethyof ctxt1) ⇒ theory_ok' (ethyof ctxt2)
Proof
  ho_match_mp_tac extends'_ind >> metis_tac[updates'_theory_ok']
QED

Theorem init_theory_ok':
  theory_ok' (ethyof init_ectxt)
Proof
  rw[theory_ok'_def,init_ectxt_def,type_ok_def,FLOOKUP_UPDATE,conexts_of_upd'_def] >>
  rw[is_std_sig_def, FLOOKUP_UPDATE, sigof'_def, axioms_ok_def]
QED

Definition lift_upd_def:
  lift_upd ((NewAxiom p):update) = (NewAxiom p:update') ∧
  lift_upd (NewConst n ty) = NewConst n ty ∧
  lift_upd (ConstSpec eqs p) = ConstSpec eqs p ∧
  lift_upd (NewType n a) = NewType n a ∧
  lift_upd (TypeDefn n p a r) = TypeDefn n p a r
End

Overload lift_ctxt = “MAP lift_upd”

Definition drop_upd_def:
  drop_upd ((NewAxiom p):update') = SOME (NewAxiom p:update) ∧
  drop_upd (NewConst n ty) = SOME (NewConst n ty) ∧
  drop_upd (ConstSpec eqs p) = SOME (ConstSpec eqs p) ∧
  drop_upd (NewType n a) = SOME (NewType n a) ∧
  drop_upd (TypeDefn n p a r) = SOME (TypeDefn n p a r) ∧
  drop_upd (NewEliminableType n a) = SOME (NewType n a) ∧
  drop_upd (NewEliminableConst n ty) = SOME (NewConst n ty) ∧
  drop_upd (NewEliminableAxiom n) = NONE
End

Overload drop_ctxt = “list$mapPartial drop_upd”

Theorem tysof'_lift_ctxt[simp]:
  tysof' (lift_ctxt ctxt) = tysof ctxt
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> fs[lift_upd_def]
QED

Theorem tmsof'_lift_ctxt[simp]:
  tmsof' (lift_ctxt ctxt) = tmsof ctxt
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> fs[lift_upd_def]
QED

Theorem etysof_lift_ctxt[simp]:
  etysof (lift_ctxt ctxt) = FEMPTY
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> simp[lift_upd_def]
QED

Theorem etmsof_lift_ctxt[simp]:
  etmsof (lift_ctxt ctxt) = FEMPTY
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> simp[lift_upd_def]
QED

Theorem eaxsof_lift_ctxt[simp]:
  eaxsof (lift_ctxt ctxt) = ∅
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> fs[lift_upd_def, eaxexts_of_upd'_def]
QED

Theorem axsof_lift_ctxt[simp]:
  axsof' (lift_ctxt ctxt) = axsof ctxt
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> fs[lift_upd_def, conexts_of_upd'_def, conexts_of_upd_def]
QED

Theorem ethyof_lift_ctxt[simp]:
  ethyof (lift_ctxt ctxt) = lift_thy (thyof ctxt)
Proof
  simp[lift_thy_def]
QED

Theorem tysof_drop_ctxt[simp]:
  theory_ok' (ethyof ctxt) ⇒
  tysof (drop_ctxt ctxt) = (ethyof ctxt).ctys
Proof
  strip_tac
  >> dxrule_then (mp_tac o pat_conj ‘DISJOINT (FDOM thy.tys) _’) $ iffLR theory_ok'_def
  >> Induct_on ‘ctxt’ >- simp[ctys_def]
  >> Cases >> fs[listTheory.mapPartial_def, drop_upd_def, ctys_def, ctms_def]
  >> rw[FUNION_FUPDATE_1, FUNION_FUPDATE_2]
QED

Theorem tmsof_drop_ctxt[simp]:
  theory_ok' (ethyof ctxt) ⇒
  tmsof (drop_ctxt ctxt) = (ethyof ctxt).ctms
Proof
  strip_tac
  >> dxrule_then (mp_tac o pat_conj ‘DISJOINT (FDOM thy.tms) _’) $ iffLR theory_ok'_def
  >> Induct_on ‘ctxt’ >- simp[ctms_def]
  >> Cases >> fs[listTheory.mapPartial_def, drop_upd_def, ctys_def, ctms_def]
  >> rw[FUNION_FUPDATE_1, FUNION_FUPDATE_2, FUNION_ASSOC]
QED

Theorem axsof_drop_ctxt[simp]:
  axsof (drop_ctxt ctxt) = axsof' ctxt
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases
  >> fs[listTheory.mapPartial_def, drop_upd_def, conexts_of_upd_def, conexts_of_upd'_def]
  >> SET_TAC[]
QED

Theorem thyof_drop_ctxt[simp]:
  theory_ok' (ethyof ctxt) ⇒ thyof (drop_ctxt ctxt) = drop_thy ∅ (ethyof ctxt)
Proof
  rw[drop_thy, ctms_def, ctys_def]
QED

Theorem drop_thy_lift_thy[simp]:
  drop_thy ∅ (lift_thy thy) = thy
Proof
  rw[drop_thy, lift_thy_def]
QED

Theorem sigof_drop_ctxt[simp]:
  theory_ok' (ethyof ctxt) ⇒ sigof (drop_ctxt ctxt) = ((ethyof ctxt).ctys, (ethyof ctxt).ctms)
Proof
  simp[]
QED

Theorem const_list_lift_ctxt:
  const_list' (lift_ctxt ctxt) = const_list ctxt
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> simp[lift_upd_def]
QED

Theorem econst_list_lift_ctxt[simp]:
  econst_list (lift_ctxt ctxt) = []
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> simp[lift_upd_def]
QED

Theorem type_list_lift_ctxt[simp]:
  type_list' (lift_ctxt ctxt) = type_list ctxt
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> simp[lift_upd_def]
QED

Theorem etype_list_lift_ctxt[simp]:
  etype_list (lift_ctxt ctxt) = []
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> simp[lift_upd_def]
QED

Theorem lift_update_updates:
  ∀upd ctxt.
    upd updates ctxt ⇔ lift_upd upd updates' lift_ctxt ctxt
Proof
  Cases >> rw[lift_upd_def, updates_cases, Once updates'_cases, const_list_lift_ctxt]
  >- (iff_tac >> rw[] >- (irule proves_imp_proves' >> simp[])
      >> fs[const_list_lift_ctxt, EVERY_MEM, MEM_MAP] >> simp[SF SFY_ss]
      >- (fs[FST, EXISTS_PROD] >> drule proves_theory_ok >> strip_tac
          >> dxrule theory_ok_sig >> dxrule proves_term_ok >> rw[EVERY_MEM]
          >> fs[MEM_MAP] >> first_x_assum $ qspec_then ‘Var s (typeof t') === t'’ mp_tac
          >> impl_tac >- (first_x_assum $ irule_at Any >> simp[])
          >> simp[term_ok_equation])
      >> drule proves'_imp_proves >> simp[])
  >> iff_tac >> rw[]
  >- (drule proves_imp_proves' >> disch_then $ irule_at Any >> simp[]
      >> drule proves_theory_ok >> strip_tac >> dxrule theory_ok_sig
      >> dxrule proves_term_ok >> rw[EVERY_MEM]
      >> drule_all term_ok_type_ok >> simp[])
  >> drule proves'_imp_proves >> simp[]
  >> disch_then $ irule_at Any >> simp[]
QED

Theorem lift_ctxt_extends_init_ectxt:
  ∀ctxt. ctxt extends init_ctxt ⇒ lift_ctxt ctxt extends' init_ectxt
Proof
  rw[extends_def, extends'_def]
  >> qsuff_tac ‘∀c1 c2.
                  RTC (λc2 c1. ∃upd. c2 = upd::c1 ∧ upd updates c1) c1 c2 ⇒
                  RTC (λc2 c1. ∃upd. c2 = upd::c1 ∧ upd updates' c1)
                      (lift_ctxt c1) (lift_ctxt c2)’
  >- (gvs[init_ctxt_def, init_ectxt_def, lift_upd_def] >> disch_then drule >> simp[lift_upd_def])
  >> ho_match_mp_tac RTC_INDUCT >> rw[]
  >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES))
  >> qexists_tac ‘lift_ctxt c1'’ >> simp[]
  >> irule $ iffLR lift_update_updates >> simp[]
QED

Theorem MEM_const_list_drop_ctxt:
  MEM x (MAP FST (const_list (drop_ctxt ctxt))) ⇔
  MEM x (MAP FST (const_list' ctxt)) ∨ MEM x (MAP FST (econst_list ctxt))
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> rw[drop_upd_def] >> gvs[EQ_IMP_THM, DISJ_IMP_THM]
QED

Theorem MEM_type_list_drop_ctxt:
  MEM x (MAP FST (type_list (drop_ctxt ctxt))) ⇔
  MEM x (MAP FST (type_list' ctxt)) ∨ MEM x (MAP FST (etype_list ctxt))
Proof
  Induct_on ‘ctxt’ >> simp[] >> Cases >> rw[drop_upd_def] >> gvs[EQ_IMP_THM, DISJ_IMP_THM]
QED

Theorem drop_upd_updates:
  upd updates' ctxt ∧
    theory_ok' (ethyof ctxt) ∧
    drop_upd upd = SOME x ⇒
    x updates (drop_ctxt ctxt)
Proof
  strip_tac >> Cases_on ‘upd’ >> gvs[drop_upd_def]
  >> gvs[Once updates'_cases]
  >- (irule $ pat_conj ‘ConstSpec _ _ updates _’ updates_rules >> drule proves'_imp_proves
      >> simp[] >> gvs[MEM_const_list_drop_ctxt])
  >- (irule $ pat_conj ‘TypeDefn _ _ _ _ updates _’ updates_rules >> drule proves'_imp_proves
      >> simp[drop_thy, ctms_def, ctys_def] >> disch_then $ irule_at Any
      >> assume_tac $ GEN_ALL $ CONTRAPOS $ iffLR $ MEM_type_list_drop_ctxt
      >> gvs[MEM_const_list_drop_ctxt])
  >- (irule $ pat_conj ‘NewType _ _ updates _’ updates_rules >> gvs[MEM_type_list_drop_ctxt])
  >- (irule $ pat_conj ‘NewType _ _ updates _’ updates_rules >> gvs[MEM_type_list_drop_ctxt])
  >- (irule $ pat_conj ‘NewConst _ _ updates _’ updates_rules
      >> simp[ctys_def, ctms_def, type_ok_weakening]
      >> gvs[MEM_const_list_drop_ctxt])
  >- (irule $ pat_conj ‘NewConst _ _ updates _’ updates_rules
      >> simp[ctys_def, ctms_def, type_ok_weakening]
      >> gvs[MEM_const_list_drop_ctxt])
  >> irule $ pat_conj ‘NewAxiom _ updates _’ updates_rules >> simp[ctms_def, ctys_def]
  >> irule term_ok_weakening >> simp[]
QED

Theorem drop_thy_extends_init_ctxt:
  ∀ctxt'. ctxt' extends' init_ectxt ⇒ drop_ctxt ctxt' extends init_ctxt
Proof
  rw[extends_def, extends'_def]
  >> qsuff_tac
‘∀c1 c2.
   RTC (λc2 c1. ∃upd. c2 = upd::c1 ∧ upd updates' c1) c1 c2 ⇒
   theory_ok' (ethyof c2) ⇒
   theory_ok' (ethyof c1) ∧
   RTC (λc2 c1. ∃upd. c2 = upd::c1 ∧ upd updates c1)
       (drop_ctxt c1) (drop_ctxt c2)’
  >- (disch_then drule >> simp[init_theory_ok']
      >> rw[init_ectxt_def, init_ctxt_def, listTheory.mapPartial_def, drop_upd_def])
  >> ho_match_mp_tac RTC_INDUCT >> rw[]
  >> rpt $ first_x_assum drule >> strip_tac
  >- (drule updates'_theory_ok' >> simp[])
  >> Cases_on ‘drop_upd upd’ >> gvs[listTheory.mapPartial_def]
  >> irule (CONJUNCT2 (SPEC_ALL RTC_RULES))
  >> qexists_tac ‘drop_ctxt c1'’ >> simp[]
  >> irule drop_upd_updates >> first_x_assum $ irule_at Any >> simp[]
QED

(* main two theorems: the two systems are equivalent *)
Theorem lift_ctxt_extends_extends':
  ∀h c.
    ctxt extends init_ctxt ⇒
    ((thyof ctxt, h) |- c ⇔ (ethyof (lift_ctxt ctxt), ∅, h) |-' c)
Proof
  rpt strip_tac >> iff_tac >> rw[]
  >- (drule proves_imp_proves' >> simp[lift_ctxt_extends_init_ectxt, lift_thy_def])
  >> drule proves'_imp_proves >> simp[drop_thy, ctms_def, ctys_def]
QED

Theorem drop_ctxt_extends_extends':
  ∀h c.
    ctxt extends' init_ectxt ⇒
    ((ethyof ctxt, ∅, h) |-' c ⇔ (thyof (drop_ctxt ctxt), h) |- c)
Proof
  rpt strip_tac >> iff_tac >> rw[]
  >- (drule proves'_imp_proves >> simp[drop_thy, ctms_def, ctys_def]
      >> drule extends'_theory_ok' >> simp[init_theory_ok']
      >> fs[ctms_def, ctys_def])
  >> irule proves_imp_proves'_subset_axs >> simp[]
  >> simp[drop_thy_extends_init_ctxt]
  >> first_x_assum $ irule_at Any
  >> drule extends'_theory_ok'
  >> rw[init_theory_ok', ctys_def, ctms_def]
QED

(* the rest of these theorems are to show that the elim_inst preconditions
   are actually satisfied by normal use *)
Theorem init_axioms_ok:
  axioms_ok (ethyof init_ectxt) (axsof' init_ectxt) ∧
  axioms_ok (ethyof init_ectxt) (eaxsof init_ectxt)
Proof
  rw[axioms_ok_def, init_ectxt_def, conexts_of_upd'_def]
QED

Theorem type_ok_basic_types:
  ∀ty.
    type_ok thy.tys ty ∧ esubsts_ok' thy σ ∧ theory_ok' thy ⇒
    ty_esubst σ ty = ty
Proof
  Induct using type_ind >> simp[type_ok_def, ty_esubst_def] >> fs[EVERY_MEM, theory_ok'_def]
  >> rw[] >> Cases_on ‘l’ >> rw[ty_esubst_def] >> every_case_tac >> fs[]
  >- (Cases_on ‘σ’ >> fs[esubsts_ok'_def] >> rpt $ dxrule DISJOINT_FLOOKUP
      >> disch_then drule >> simp[] >> pop_assum mp_tac >> fs[FLOOKUP_DEF, SUBSET_DEF])
  >- (irule $ iffRL MAP_EQ_ID >> rw[])
  >> Cases_on ‘σ’ >> fs[esubsts_ok'_def] >> rpt $ dxrule DISJOINT_FLOOKUP
  >> disch_then drule >> simp[] >> pop_assum mp_tac >> fs[FLOOKUP_DEF, SUBSET_DEF]
QED

Theorem term_ok_no_var_collapse:
  ∀thy σ p.
    term_ok (thy.tys, thy.tms) p ∧
    theory_ok' thy ∧
    esubsts_ok' thy σ ⇒
    no_var_collapse σ p
Proof
  rw[no_var_collapse] >> imp_res_tac term_ok_VFREE_IN
  >> gvs[term_ok_def] >> imp_res_tac type_ok_basic_types >> gvs[]
QED

Definition no_dup_vars_def:
  no_dup_vars p ⇔
    ∀x ty1 ty2.
      VFREE_IN (Var x ty1) p ∧ VFREE_IN (Var x ty2) p ⇒ ty1 = ty2
End

Theorem no_dup_vars_no_var_collapse:
  no_dup_vars p ⇒ no_var_collapse σ p
Proof
  rw[no_dup_vars_def, no_var_collapse] >> metis_tac[]
QED

Theorem REV_ASSOCD_VSUBST_const_no_free_vars:
  ∀l y ty u uty.
    MEM (y,ty) (MAP (λ(s,t). (s,typeof t)) l) ⇒
    ¬VFREE_IN (Var u uty)
      (REV_ASSOCD (Var y ty)
        (MAP (λ(s,t). (Const s (typeof t),Var s (typeof t))) l)
        (Var y ty))
Proof
  Induct >> simp[FORALL_PROD, REV_ASSOCD]
  >> rw[] >> gvs[VFREE_IN_def]
QED

Theorem updates'_axioms_wf:
  ∀upd ctxt.
    upd updates' ctxt ⇒
    theory_ok' (ethyof ctxt) ∧
    (∀p. p ∈ (ethyof ctxt).axs ⇒
         no_dup_vars p ∨ term_ok ((ethyof ctxt).tys, (ethyof ctxt).tms) p) ∧
    (∀p. p ∈ (ethyof ctxt).eaxs ⇒ no_dup_vars p) ⇒
    (∀p. p ∈ (ethyof (upd::ctxt)).axs ⇒
         no_dup_vars p ∨ term_ok ((ethyof (upd::ctxt)).tys, (ethyof (upd::ctxt)).tms) p) ∧
    (∀p. p ∈ (ethyof (upd::ctxt)).eaxs ⇒ no_dup_vars p)
Proof
  Induct_on ‘$updates'’ >> rw[]
  >> fs[conexts_of_upd'_def, eaxexts_of_upd'_def, axexts_of_upd'_def, conexts_of_upd'_def]
  >- (first_x_assum drule >> rw[] >> simp[] >> disj2_tac >> irule term_ok_extend
      >> first_x_assum $ irule_at Any >> simp[])
  >- (gvs[no_dup_vars_def] >> imp_res_tac proves'_term_ok' >> imp_res_tac term_ok'_welltyped
      >> gvs[VFREE_IN_VSUBST] >> res_tac >> metis_tac[REV_ASSOCD_VSUBST_const_no_free_vars])
  >- (first_x_assum drule >> rw[] >> simp[] >> disj2_tac >> irule term_ok_extend
      >> first_x_assum $ irule_at Any >> simp[] >> irule $ cj 2 SUBMAP_FUNION_ID
      >> fs[DISJOINT_DEF, EXTENSION, MAP_MAP_o, o_DEF, LAMBDA_PROD]
      >> metis_tac[])
  >- (first_x_assum drule >> rw[] >> simp[] >> disj2_tac >> irule term_ok_extend
      >> first_x_assum $ irule_at Any >> simp[])
  >- (disj1_tac >> rw[no_dup_vars_def, equation_def, VFREE_IN_def]
      >> gvs[CLOSED_def, VFREE_IN_def])
  >- (disj1_tac >> rw[no_dup_vars_def, equation_def, VFREE_IN_def]
      >> gvs[CLOSED_def, VFREE_IN_def])
  >- (first_x_assum drule >> rw[] >> simp[] >> disj2_tac >> irule term_ok_extend
      >> first_x_assum $ irule_at Any >> rw[SUBMAP_DEF, FLOOKUP_UPDATE]
      >> metis_tac[FAPPLY_FUPDATE_THM])
  >> simp[no_dup_vars_def] >> gvs[]
QED

Theorem extends'_axioms_wf:
  ∀ctxt1 ctxt2.
    ctxt2 extends' ctxt1 ⇒
    theory_ok' (ethyof ctxt1) ∧
    (∀p. p ∈ (ethyof ctxt1).axs ⇒
       no_dup_vars p ∨ term_ok ((ethyof ctxt1).tys, (ethyof ctxt1).tms) p) ∧
    (∀p. p ∈ (ethyof ctxt1).eaxs ⇒ no_dup_vars p) ⇒
    theory_ok' (ethyof ctxt2) ∧
    (∀p. p ∈ (ethyof ctxt2).axs ⇒
       no_dup_vars p ∨ term_ok ((ethyof ctxt2).tys, (ethyof ctxt2).tms) p) ∧
    (∀p. p ∈ (ethyof ctxt2).eaxs ⇒ no_dup_vars p)
Proof
  ho_match_mp_tac extends'_ind
  >> metis_tac[updates'_axioms_wf, updates'_theory_ok']
QED

Theorem eaxsof_init_ectxt[simp]:
  eaxsof init_ectxt = ∅
Proof
  simp[eaxexts_of_upd'_def, init_ectxt_def]
QED

Theorem axsof_init_ectxt[simp]:
  axsof' init_ectxt = ∅
Proof
  simp[conexts_of_upd'_def, init_ectxt_def]
QED

Theorem axioms_ok_nil[simp]:
  axioms_ok thy ∅
Proof
  rw[axioms_ok_def]
QED

Theorem extends'_init_axioms_ok:
  ∀ctxt. ctxt extends' init_ectxt ⇒
    axioms_ok (ethyof ctxt) (ethyof ctxt).axs ∧
    axioms_ok (ethyof ctxt) (ethyof ctxt).eaxs
Proof
  rw[]
  >> imp_res_tac extends'_axioms_wf
  >> imp_res_tac extends'_theory_ok'
  >> gvs[init_theory_ok', init_ectxt_def, conexts_of_upd'_def, eaxexts_of_upd'_def]
  >> rw[axioms_ok_def] >> rpt strip_tac >> res_tac
  >- metis_tac[no_dup_vars_no_var_collapse]
  >- (first_x_assum drule >> strip_tac
      >- metis_tac[no_dup_vars_no_var_collapse]
      >> irule term_ok_no_var_collapse >> rpt $ first_x_assum $ irule_at Any
      >> simp[])
  >> metis_tac[no_dup_vars_no_var_collapse]
QED
