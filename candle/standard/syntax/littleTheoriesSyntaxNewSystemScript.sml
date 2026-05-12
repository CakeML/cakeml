(*
  Some lemmas about the extended Little Theories syntactic functions.
*)
open preamble totoTheory comparisonTheory ternaryComparisonsTheory mlstringTheory
              holSyntaxLibTheory holSyntaxTheory errorMonadTheory
              littleTheoriesSyntaxTheory holSyntaxExtraTheory
              littleTheoriesSyntaxOldSystemTheory

val _ = new_theory"littleTheoriesSyntaxNewSystem"

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad("error");


fun rC q = rename [q] >> Cases_on q >> simp[]

val cpn_distinct = TypeBase.distinct_of “:ordering”
val cpn_nchotomy = TypeBase.nchotomy_of “:ordering”

val strip_d1 = CONV_TAC (REWR_CONV (DECIDE “p ∨ q ⇔ ¬p ⇒ q”)) THEN strip_tac
val strip_d2 = CONV_TAC (REWR_CONV (DECIDE “p ∨ q ⇔ ¬q ⇒ p”)) THEN strip_tac


Theorem term_ok'_imp_term_ok:
  ∀tm. term_ok' thy tm ⇒ term_ok (thy.ctys,thy.ctms) tm
Proof
  Induct_on ‘tm’ >> rw[term_ok'_def, term_ok_def]
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
  >> qexistsl_tac [`(thy:ethy).axs`, `((thy:ethy).ctys, thy.ctms)`]
  >> simp[term_ok'_imp_term_ok]
  >> qspec_then `{}` mp_tac theory_ok_drop_thy_alt
  >> simp[drop_thy]
QED

Theorem ty_esubst_type_ok:
  ∀ty.
    type_ok thy.ctys ty ∧
    esubsts_ok (thy.ctys, thy.ctms) σ ⇒
    type_ok thy.ctys (ty_esubst σ ty)
Proof
  Induct_on ‘ty’ using type_ind >> rw[ctys_def]
  >> Cases_on ‘σ’
  >> rw[type_ok_def, ty_esubst_def]
  >> gvs[EVERY_MEM]
  >> Cases_on ‘l’ >> rw[type_ok_def, ty_esubst_def]
  >- (rC ‘FLOOKUP q m’
      >> gvs[type_ok_def, esubsts_total_def, esubsts_ok_def]
      >> first_x_assum $ qspec_then ‘x’ mp_tac
      >> impl_tac
      >- simp[IN_FRANGE_FLOOKUP, SF SFY_ss]
      >> rw[sigof'_def, type_ok_weakening])
  >> gvs[type_ok_def, EVERY_MEM, MEM_MAP, SF SFY_ss, ctys_def]
  >> metis_tac[]
QED

Theorem ty_esubst_type_ok_id:
  ∀ty σ. type_ok tys ty ∧ DISJOINT (FDOM (FST σ)) (FDOM tys) ⇒ ty_esubst σ ty = ty
Proof
  ho_match_mp_tac type_ind >> rw[]
  >- simp[ty_esubst_def]
  >> Cases_on `l : type list` >> simp[ty_esubst_def]
  >- (CASE_TAC >> gvs[type_ok_def, FLOOKUP_DEF, IN_DISJOINT] >> metis_tac[])
  >> gvs[type_ok_def, EVERY_MEM, MAP_EQ_ID] >> metis_tac[]
QED

Theorem VFREE_IN_esubst_iff:
  esubsts_ok sig σ ∧ term_ok sig tm ⇒
  (VFREE_IN (Var u uty) (esubst σ [] tm) ⇔
   ∃oty. VFREE_IN (Var u oty) tm ∧ uty = ty_esubst σ oty)
Proof
  rw[esubst_def, esubst_ty_def]
  >> `∃tm1. esubst_ty0 [] σ [] tm = return tm1`
    by metis_tac[esubst_ty0_always_returns]
  >> simp[]
  >> `VFREE_IN (Var u uty) (esubst_tm σ tm1) ⇔ VFREE_IN (Var u uty) tm1`
    by metis_tac[VFREE_IN_esubst_tm]
  >> simp[]
  >> irule esubst_ty0_all_free
  >> rpt $ first_assum $ irule_at Any >> simp[MEM]
QED

Theorem axioms_ok_esubst:
  axioms_ok axs ∧ (∀p. p ∈ axs ⇒ term_ok sig p) ∧ esubsts_ok sig σ ⇒
  axioms_ok (IMAGE (esubst σ []) axs)
Proof
  rw[axioms_ok_def, PULL_EXISTS]
  >> `∀u uty. VFREE_IN (Var u uty) (esubst σ [] x) ⇔
              ∃oty. VFREE_IN (Var u oty) x ∧ uty = ty_esubst σ oty`
    by (irule VFREE_IN_esubst_iff >> metis_tac[])
  >> gvs[] >> metis_tac[]
QED

Theorem DISJOINT_FLOOKUP:
  DISJOINT (FDOM f1) (FDOM f2) ∧ FLOOKUP f1 k = SOME v ⇒ FLOOKUP f2 k = NONE
Proof
  rw[] >> imp_res_tac $ iffRL FDOM_FLOOKUP >> irule $ iffRL $ cj 1 flookup_thm >> ASM_SET_TAC[]
QED

Theorem SUBMAP_FUNION_mono_r':
  g1 ⊑ g2 ⇒ f ⊌ g1 ⊑ f ⊌ g2
Proof
  rw[SUBMAP_DEF, FUNION_DEF, FDOM_FUNION] >> metis_tac[]
QED

Theorem esubsts_ok'_esubsts_ok:
  esubsts_ok' thy σ ∧ theory_ok' thy ⇒ esubsts_ok (thy.ctys, thy.ctms) σ
Proof
  Cases_on `σ` >> rename1`(σ,θ)` >> rw[esubsts_ok'_def, esubsts_ok_def, theory_ok'_def]
  >- (first_x_assum drule >> simp[ctms_def, FLOOKUP_FUNION] >> CASE_TAC >> rw[]
      >> drule_all DISJOINT_FLOOKUP >> simp[])
  >> first_x_assum drule >> rw[] >> gvs[term_ok_def, term_ok'_def]
  >> gvs[ctys_def, type_ok_weakening, ctms_def, esubst_thy_def, FLOOKUP_FUNION]
  >> qexists `ty0` >> gvs[monomorphic_type_subst] >> rw[FLOOKUP_o_f]
  >> gvs[ctys_def, type_ok_weakening, ctms_def, esubst_thy_def, FLOOKUP_FUNION, AllCaseEqs(),
         FLOOKUP_o_f]
  >> gvs[FLOOKUP_o_f, FLOOKUP_FUNION, AllCaseEqs()]
  >- (gvs[FLOOKUP_FDIFF] >> metis_tac[])
  >- (irule ty_esubst_type_ok_id >> qexists_tac `(thy:ethy).tys` >> simp[]
      >> conj_tac >- metis_tac[DISJOINT_SUBSET, DISJOINT_SYM]
      >> first_x_assum irule >> simp[IN_FRANGE_FLOOKUP] >> metis_tac[])
  >> `(thy.tys ⊌ FDIFF thy.etys (FDOM σ)) ⊑ (thy.tys ⊌ thy.etys)` by
       (irule SUBMAP_FUNION_mono_r' >> simp[FDIFF_def, SUBMAP_DRESTRICT])
  >> imp_res_tac type_ok_extend
  >> rw[] >> metis_tac[]
QED

Theorem type_ok_restrict_nullary:
  ∀ty. type_ok (tys ⊌ etys) ty ∧
       DISJOINT (FDOM tys) (FDOM etys) ∧
       FRANGE etys ⊆ {0} ∧
       DISJOINT ss (nullary_ops_of ty) ∧
       ss ⊆ FDOM etys ⇒
       type_ok (tys ⊌ FDIFF etys ss) ty
Proof
  ho_match_mp_tac type_ind >> rw[]
  >- simp[type_ok_def]
  >> rpt strip_tac
  >> Cases_on `l` >> gvs[type_ok_def, nullary_ops_of_def]
  >- (gvs[FLOOKUP_FUNION, AllCaseEqs()]
      >> simp[FLOOKUP_FDIFF])
  >> simp[type_ok_def] >> rpt conj_tac
  >- (gvs[type_ok_def, FLOOKUP_FUNION, AllCaseEqs()]
      >> `SUC (LENGTH t) ∈ FRANGE etys`
           by (simp[IN_FRANGE_FLOOKUP] >> metis_tac[])
      >> fs[SUBSET_DEF] >> res_tac >> fs[])
  >- (rpt strip_tac >> first_x_assum irule
      >> gvs[IN_DISJOINT] >> metis_tac[])
  >> simp[EVERY_MEM] >> rpt strip_tac
  >> gvs[EVERY_MEM]
  >> first_x_assum drule >> strip_tac
  >> first_x_assum irule
  >> gvs[IN_DISJOINT, MEM_MAP] >> metis_tac[]
QED

Theorem esubsts_ok'_frange_type_ok:                                                    
  theory_ok' thy ∧ esubsts_ok' thy (σty, σtm) ∧ ty ∈ FRANGE σty ⇒
  type_ok (esubst_thy (σty, σtm) thy).ctys ty
Proof
  rw[theory_ok'_def, esubsts_ok'_def, ctys_def, esubst_thy_def] >> res_tac
  >> irule type_ok_restrict_nullary >> simp[]
QED

Theorem ty_esubst_type_ok':
  theory_ok' thy ∧ esubsts_ok' thy σ ∧ type_ok thy.ctys ty ⇒
  type_ok (esubst_thy σ thy).ctys (ty_esubst σ ty)
Proof
  strip_tac
  >> drule_all esubsts_ok'_esubsts_ok >> strip_tac
  >> ntac 2 (pop_assum mp_tac) >> qid_spec_tac `ty`
  >> Induct_on `ty` using type_ind >> rw[]
  >- simp[ty_esubst_def, type_ok_def]
  >> Cases_on `σ` >> rename1 `(σty, σtm)`
  >> Cases_on `l`
  >- (rw[ty_esubst_def] >> CASE_TAC
      >- (rw[type_ok_def, esubst_thy_def, ctys_def, FLOOKUP_FUNION]
          >> gvs[type_ok_def, ctys_def, FLOOKUP_FUNION, AllCaseEqs()]
          >> gvs[esubsts_ok_def, SUBSET_DEF, FDOM_FLOOKUP, FLOOKUP_FDIFF])
      >> rename1 `FLOOKUP σty m = SOME x`
      >> gvs[esubst_thy_def, ctys_def, esubsts_ok_def]
      >> drule_then drule esubsts_ok'_frange_type_ok >> disch_then $ qspec_then ‘x’ mp_tac
      >> simp[IN_FRANGE_FLOOKUP, SF SFY_ss, esubst_thy_def, ctys_def])
  >> `FLOOKUP thy.tys m = SOME (SUC (LENGTH t))`
       by (gvs[type_ok_def, ctys_def, FLOOKUP_FUNION, AllCaseEqs()]
           >> `SUC (LENGTH t) ∈ FRANGE thy.etys`
                by (simp[IN_FRANGE_FLOOKUP] >> metis_tac[])
           >> fs[theory_ok'_def, SUBSET_DEF] >> res_tac >> gvs[])
  >> rw[ty_esubst_def, type_ok_def, EVERY_MEM, MEM_MAP, PULL_EXISTS]
  >- simp[esubst_thy_def, ctys_def, FLOOKUP_FUNION, FDOM_FLOOKUP]
  >> first_x_assum (irule o BETA_RULE o REWRITE_RULE [EVERY_MEM]) >> simp[]
  >> gvs[type_ok_def, ctys_def, EVERY_MEM]
QED

Theorem esubst_thy_ctms_preserved:
  theory_ok' thy ∧ esubsts_ok' thy (σty, σtm) ∧
  FLOOKUP thy.ctms n = SOME ty0 ∧ n ∉ FDOM σtm ⇒
  FLOOKUP (esubst_thy (σty, σtm) thy).ctms n = SOME (ty_esubst (σty, σtm) ty0)
Proof
  strip_tac
  >> simp[esubst_thy_def, ctms_def, FLOOKUP_FUNION, FLOOKUP_o_f, FLOOKUP_FDIFF]
  >> Cases_on `FLOOKUP thy.tms n`
  >- (gvs[ctms_def, FLOOKUP_FUNION])
  >> `x = ty0` by gvs[ctms_def, FLOOKUP_FUNION]
  >> gvs[]
  >> `ty_esubst (σty,σtm) ty0 = ty0` by
       (irule ty_esubst_type_ok_id >> qexists `thy.tys`
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
  (* Var *)
  >- (gvs[esubst_ty0_def, AllCaseEqs()]
      >> simp[esubst_tm_def, term_ok'_def]
      >> irule ty_esubst_type_ok' >> gvs[term_ok'_def] >> metis_tac[])
  (* Const *)
  >- (gvs[esubst_ty0_def, term_ok'_def]
      >> Cases_on `σ` >> rename1 `(σty, σtm)`
      >> simp[esubst_tm_def]
      >> Cases_on `FLOOKUP σtm n`
      >- (simp[term_ok'_def]
          >> qexists `ty_esubst (σty, σtm) ty0`
          >> rpt conj_tac
          >- (irule esubst_thy_ctms_preserved >> simp[]
              >> strip_tac >> gvs[FDOM_FLOOKUP])
          >- (irule ty_esubst_type_ok' >> metis_tac[])
          >> metis_tac[ty_esubst_TYPE_SUBST])
      >> (rename1 `FLOOKUP σtm n = SOME repl`
          >> gvs[esubsts_ok'_def]
          >> `repl ∈ FRANGE σtm` by (simp[IN_FRANGE_FLOOKUP] >> metis_tac[])
          >> res_tac >> gvs[]))
  (* Comb *)
  >- (gvs[esubst_ty0_def, bind_EQ_return, term_ok'_def]
      >> simp[esubst_tm_def, term_ok'_def]
      >> rpt conj_tac
      >- metis_tac[term_ok'_imp_term_ok, term_ok_welltyped]
      >- metis_tac[term_ok'_imp_term_ok, term_ok_welltyped]
      >> Cases_on `σ` >> rename1 `(σty, σtm)`
      >> metis_tac[typeof_esubst_ty, typeof_esubst_tm_esubst_ty0,
                   term_ok'_imp_term_ok, ty_esubst_fun])
  (* Abs *)
  >> gvs[term_ok'_def, esubst_ty0_def, bind_EQ_return, bind_EQ_error, try_eq_return]
  >- (simp[esubst_tm_def, term_ok'_def]
      >> rpt conj_tac
      >- (irule ty_esubst_type_ok' >> metis_tac[])
      >> first_x_assum irule >> simp[] >> metis_tac[])
  >> gvs[AllCaseEqs(), bind_EQ_return]
  >> simp[esubst_tm_def, term_ok'_def]
  >> rw[]
  >- (irule ty_esubst_type_ok' >> metis_tac[])
  >> first_x_assum irule >> qexists `body1`
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
  >> `∃tm1. esubst_ty0 [] σ avds tm = return tm1`
       by metis_tac[esubst_ty0_always_returns, term_ok'_imp_term_ok]
  >> simp[]
  >> irule esubst_ty0_tm_ok'
  >> simp[] >> metis_tac[MEM]
QED

Theorem frange_esubst_thy_etms:
  ty ∈ FRANGE (esubst_thy σ thy).etms ⇒
  ∃ty0. ty = ty_esubst σ ty0 ∧ ty0 ∈ FRANGE thy.etms
Proof
  simp[esubst_thy_def, IN_FRANGE_FLOOKUP, FLOOKUP_o_f, FLOOKUP_FDIFF]
  >> strip_tac >> every_case_tac >> gvs[]
  >> simp[IN_FRANGE_FLOOKUP] >> metis_tac[]
QED

Theorem theory_ok'_esubst:
  theory_ok' thy ∧ esubsts_ok' thy σ ⇒ theory_ok' (esubst_thy σ thy)
Proof
  strip_tac
  >> simp[theory_ok'_def, sigof'_def]
  >> rpt conj_tac
  >- (simp[esubst_thy_def] >> gvs[theory_ok'_def])
  >- (rw[] >> drule frange_esubst_thy_etms >> strip_tac >> gvs[]
      >> irule ty_esubst_type_ok' >> simp[]
      >> gvs[theory_ok'_def])
  >- (simp[esubst_thy_def] >> gvs[theory_ok'_def, FDIFF_def, FDOM_DRESTRICT] >> ASM_SET_TAC[])
  >- (simp[esubst_thy_def] >> gvs[theory_ok'_def, FDIFF_def, FDOM_DRESTRICT] >> ASM_SET_TAC[])
  >- (rpt strip_tac
      >> `∃x. p = esubst σ [] x ∧ x ∈ thy.axs` by (fs[esubst_thy_def] >> metis_tac[])
      >> gvs[]
      >> drule_all esubsts_ok'_esubsts_ok >> strip_tac
      >- (irule esubst_term_ok' >> gvs[theory_ok'_def])
      >> irule esubst_has_type_bool_alt
         >> first_assum $ irule_at Any >> gvs[theory_ok'_def])
  >- (rpt strip_tac
      >> `∃x. p = esubst σ [] x ∧ x ∈ thy.eaxs` by (fs[esubst_thy_def] >> metis_tac[])
      >> gvs[]
      >> drule_all esubsts_ok'_esubsts_ok >> strip_tac
      >- (irule esubst_term_ok' >> gvs[theory_ok'_def])
      >> irule esubst_has_type_bool_alt
         >> first_assum $ irule_at Any >> gvs[theory_ok'_def])
  >- (simp[esubst_thy_def] >> gvs[theory_ok'_def, sigof'_def])
  >- (drule_all esubsts_ok'_esubsts_ok >> strip_tac
      >> simp[esubst_thy_def]
      >> irule axioms_ok_esubst >> first_assum $ irule_at Any
      >> gvs[theory_ok'_def] >> metis_tac[term_ok'_imp_term_ok])
  >- (drule_all esubsts_ok'_esubsts_ok >> strip_tac
      >> simp[esubst_thy_def]
      >> irule axioms_ok_esubst >> first_assum $ irule_at Any
      >> gvs[theory_ok'_def] >> metis_tac[term_ok'_imp_term_ok])
  >> simp[esubst_thy_def]
  >> simp[FDIFF_def] >> metis_tac[theory_ok'_def, SUBSET_TRANS, FRANGE_DRESTRICT_SUBSET]
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

Theorem ty_esubst_o_f_thy_tms:
  ∀thy. theory_ok' thy ∧ esubsts_ok' thy σ ⇒ ty_esubst σ o_f thy.tms = thy.tms
Proof
  rw[theory_ok'_def] >> Cases_on `σ` >> gvs[esubsts_ok'_def]
  >> simp[fmap_eq_flookup, FLOOKUP_o_f]
  >> rw[] >> CASE_TAC >> simp[]
  >> irule ty_esubst_type_ok_id
  >> qexists_tac `(thy:ethy).tys` >> simp[]
  >> conj_tac
  >- metis_tac[DISJOINT_SUBSET, DISJOINT_SYM]
  >> first_x_assum irule >> simp[IN_FRANGE_FLOOKUP] >> metis_tac[]
QED

Theorem axioms_ok_no_var_collapse:
  axioms_ok axs ⇒ ∀σ ax. ax ∈ axs ⇒ no_var_collapse σ ax
Proof
  rw[axioms_ok_def, no_var_collapse] >> res_tac
QED

Theorem proves_esubst_drop_thy:
  (drop_thy es thy, h) |- c ∧
  theory_ok' thy ∧
  esubsts_ok' thy σ ∧
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
  >> cheat
QED

Theorem proves_imp_proves':
  ∀thy' h c. (thy', h) |- c ⇒
    axioms_ok (axsof thy') ⇒ (lift_thy thy', {}, h) |-' c
Proof
  Induct_on `$|-` >> rw[] >> fs[]
  >- (irule proves'_ABS >> simp[])
  >- (irule proves'_ASSUME >> simp[term_ok_imp_term_ok'])
  >- (irule proves'_BETA >> simp[term_ok_imp_term_ok'])
  >- (rev_drule_then drule proves'_DEDUCT_ANTISYM >> simp[])
  >- (drule_all proves'_EQ_MP >> simp[])
  >- (irule proves'_INST >> simp[]
      >> first_x_assum $ irule_at Any >> rw[]
      >> first_x_assum drule >> rw[]
      >> irule term_ok_imp_term_ok' >> simp[])
  >- (irule proves'_INST_TYPE >> simp[])
  >- (rev_drule_then drule proves'_MK_COMB >> simp[])
  >- (irule proves'_REFL >> simp[term_ok_imp_term_ok'])
  >> irule proves'_axioms >> simp[]
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
  >- (
    drule proves'_imp_theory_ok' >> strip_tac
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

Theorem REV_ASSOCD_const_subst:
  ∀l y ty d.
    MEM (y, ty) (MAP (λ(s,t). (s, typeof t)) l) ⇒
    ∃nm. REV_ASSOCD (Var y ty)
           (MAP (λ(s,t'). (Const s (typeof t'), Var s (typeof t'))) l) d
         = Const nm ty
Proof
  Induct >> rw[REV_ASSOCD] >> PairCases_on `h` >> fs[REV_ASSOCD]
  >> Cases_on `h0 = y ∧ typeof h1 = ty` >> fs[]
  >> first_x_assum drule >> rw[]
QED

Theorem extends_axioms_ok:
  ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ axioms_ok (axsof ctxt1) ⇒ axioms_ok (axsof ctxt2)
Proof
  ho_match_mp_tac extends_ind >> Cases >> rw[axioms_ok_def] >> res_tac >> gvs[conexts_of_upd_def]
  >- (gvs[conexts_of_upd_def, VFREE_IN_def, Once updates_cases] >> ntac 2 $ pop_assum mp_tac
      >> DEP_REWRITE_TAC[VFREE_IN_VSUBST] >> rw[]
      >- (dxrule proves_term_ok >> simp[EVERY_MEM, term_ok_welltyped, SF SFY_ss])
      >> res_tac >> rev_dxrule REV_ASSOCD_const_subst >> disch_then $ qspec_then ‘Var y' ty'’ mp_tac
      >> rw[] >> fs[VFREE_IN_def])
  >> gvs[VFREE_IN_def, equation_def, Once updates_cases, CLOSED_def]
QED

Theorem init_axioms_ok:
  axioms_ok (axsof init_ctxt)
Proof
  simp[EVAL ``axsof init_ctxt``, axioms_ok_def]
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

Theorem term_ok'_sig_eq:
  ∀tm thy1 thy2. thy1.ctys = thy2.ctys ∧ thy1.ctms = thy2.ctms ⇒
       (term_ok' thy1 tm ⇔ term_ok' thy2 tm)
Proof
  Induct_on `tm` >> simp[term_ok'_def] >> metis_tac[]
QED

Theorem term_ok'_extend:
  ∀tm thy1 thy2. thy1.ctys ⊑ thy2.ctys ∧ thy1.ctms ⊑ thy2.ctms ∧
       term_ok' thy1 tm ⇒ term_ok' thy2 tm
Proof
  Induct_on `tm` >> rw[term_ok'_def] >>
  metis_tac[type_ok_extend, SUBMAP_FLOOKUP_EQN]
QED

Theorem theory_ok'_ax_ext:
  theory_ok'
  <|tms := tms; tys := tys; axs := axs;
    etms := etms; etys := etys; eaxs := eaxs|> ∧
  (∀p. p ∈ axs1 ⇒ term_ok (tys, tms) p ∧ p has_type Bool) ∧
  axioms_ok axs1 ⇒
  theory_ok'
  <|tms := tms; tys := tys; axs := axs1;
    etms := etms; etys := etys; eaxs := eaxs|>
Proof
  strip_tac >> fs[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  rpt conj_tac >> rpt strip_tac >> res_tac
  >- (irule term_ok_term_ok'_weakening >> simp[sigof'_def])
  >- (irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def, SUBMAP_REFL])
QED

Theorem theory_ok'_tms_extend:
  theory_ok' <|tms := tms; tys := tys; axs := axs; etms := etms; etys := etys; eaxs := eaxs|> ∧
  type_ok tys ty ∧ name ∉ FDOM tms ∧ name ∉ FDOM etms ⇒
  theory_ok' <|tms := tms |+ (name, ty); tys := tys; axs := axs; etms := etms; etys := etys; eaxs := eaxs|>
Proof
  strip_tac >> fs[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  `tms ⊌ etms ⊑ (tms |+ (name,ty)) ⊌ etms` by (
    irule SUBMAP_FUNION_mono >>
    simp[SUBMAP_FUPDATE_EXTENDED, FDOM_FUPDATE, DISJOINT_INSERT]) >>
  rw[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (gvs[FRANGE_FLOOKUP, FLOOKUP_UPDATE, AllCaseEqs()] >> res_tac)
  >- (metis_tac[IN_FRANGE_DOMSUB_suff])
  >- (res_tac >> irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def])
  >- (res_tac >> irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def])
  >- (irule is_std_sig_extend >>
      metis_tac[SUBMAP_REFL, SUBMAP_FUPDATE_EXTENDED])
QED

Theorem theory_ok'_tys_extend:
  theory_ok' <|tms := tms; tys := tys; axs := axs; etms := etms; etys := etys; eaxs := eaxs|> ∧
  name ∉ FDOM tys ∧ name ∉ FDOM etys ⇒
  theory_ok' <|tms := tms; tys := tys |+ (name, arity); axs := axs; etms := etms; etys := etys; eaxs := eaxs|>
Proof
  strip_tac >> fs[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  `tys ⊌ etys ⊑ (tys |+ (name,arity)) ⊌ etys` by (
    irule SUBMAP_FUNION_mono >>
    simp[SUBMAP_FUPDATE_EXTENDED, FDOM_FUPDATE, DISJOINT_INSERT]) >>
  rw[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (res_tac >> irule type_ok_extend >> first_assum (irule_at Any) >>
      simp[SUBMAP_FUPDATE_EXTENDED])
  >- (res_tac >> irule type_ok_extend >> first_assum (irule_at Any) >> simp[])
  >- (res_tac >> irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def])
  >- (res_tac >> irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def])
  >- (irule is_std_sig_extend >>
      metis_tac[SUBMAP_REFL, SUBMAP_FUPDATE_EXTENDED])
QED

Theorem theory_ok'_etys_extend:
  theory_ok' <|tms := tms; tys := tys; axs := axs; etms := etms; etys := etys; eaxs := eaxs|> ∧
  name ∉ FDOM tys ∧ name ∉ FDOM etys ∧ arity = 0 ⇒
  theory_ok' <|tms := tms; tys := tys; axs := axs; etms := etms; etys := etys |+ (name, arity); eaxs := eaxs|>
Proof
  strip_tac >> gvs[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  `tys ⊌ etys ⊑ tys ⊌ (etys |+ (name,0))` by (
    irule SUBMAP_FUNION_mono_r >> simp[SUBMAP_FUPDATE_EXTENDED]) >>
  rw[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (res_tac >> irule type_ok_extend >> first_assum (irule_at Any) >> simp[])
  >- (res_tac >> irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def, SUBMAP_REFL])
  >- (res_tac >> irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def, SUBMAP_REFL])
  >> gvs[DOMSUB_NOT_IN_DOM, FRANGE_FUPDATE_DOMSUB, SUBSET_DEF]
QED

Theorem theory_ok'_etms_extend:
  theory_ok' <|tms := tms; tys := tys; axs := axs; etms := etms; etys := etys; eaxs := eaxs|> ∧
  type_ok (tys ⊌ etys) ty ∧ name ∉ FDOM tms ∧ name ∉ FDOM etms ⇒
  theory_ok' <|tms := tms; tys := tys; axs := axs; etms := etms |+ (name, ty); etys := etys; eaxs := eaxs|>
Proof
  strip_tac >> fs[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  `tms ⊌ etms ⊑ tms ⊌ (etms |+ (name,ty))` by (
    irule SUBMAP_FUNION_mono_r >> simp[SUBMAP_FUPDATE_EXTENDED]) >>
  rw[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (gvs[FRANGE_FLOOKUP, FLOOKUP_UPDATE, AllCaseEqs()] >> res_tac)
  >- (metis_tac[IN_FRANGE_DOMSUB_suff])
  >- (res_tac >> irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def])
  >- (res_tac >> irule term_ok'_extend >>
      qexists_tac `<|tms := tms; tys := tys; axs := axs;
                     etms := etms; etys := etys; eaxs := eaxs|>` >>
      simp[ctys_def, ctms_def])
QED

Theorem theory_ok'_conservative_extend:
  theory_ok' <|tms := tms; tys := tys; axs := axs; etms := etms; etys := etys; eaxs := eaxs|> ∧
  tys ⊑ tys2 ∧ tms ⊑ tms2 ∧
  DISJOINT (FDOM tys2) (FDOM etys) ∧
  DISJOINT (FDOM tms2) (FDOM etms) ∧
  (∀ty. ty ∈ FRANGE tms2 ⇒ type_ok tys2 ty) ∧
  (∀p. p ∈ axs2 ⇒
    term_ok' <|tms := tms2; tys := tys2; axs := axs2; etms := etms; etys := etys; eaxs := eaxs|> p ∧
    p has_type Bool) ∧
  is_std_sig (tys2, tms2) ∧
  axioms_ok axs2 ⇒
  theory_ok' <|tms := tms2; tys := tys2; axs := axs2; etms := etms; etys := etys; eaxs := eaxs|>
Proof
  strip_tac >>
  `tys ⊌ etys ⊑ tys2 ⊌ etys ∧ tms ⊌ etms ⊑ tms2 ⊌ etms` by (
    rw[SUBMAP_FLOOKUP_EQN, FLOOKUP_FUNION, AllCaseEqs()] >>
    metis_tac[SUBMAP_FLOOKUP_EQN, IN_DISJOINT, FLOOKUP_DEF]
  ) >>
  gvs[theory_ok'_def, sigof'_def, ctys_def, ctms_def] >>
  rpt conj_tac >> rpt strip_tac
  >- (irule type_ok_extend >> qexists_tac `tys ⊌ etys` >> simp[] >> res_tac)
  >- (rpt strip_tac >> res_tac >> irule term_ok'_extend >>
      first_assum (irule_at (Pat `term_ok' _ _`)) >>
      simp[ctys_def, ctms_def])
QED

Theorem updates_theory_ok':
  upd updates' ctxt ⇒
    theory_ok' (ethyof ctxt) ⇒ theory_ok' (ethyof (upd::ctxt))
Proof
  Induct_on `$updates'` >> rw[conexts_of_upd'_def]
  (* NewAxiom: only axs changes, prop is CLOSED *)
  >- (fs[theory_ok'_def, axioms_ok_def, CLOSED_def]
      >> rpt conj_tac >> rpt strip_tac >> gvs[sigof'_def]
      >> TRY (res_tac >> gvs[ctys_def, ctms_def])
      >> irule (iffRL term_ok'_sig_eq)
      >> qexists_tac `<|tms := tmsof ctxt; tys := tysof ctxt; axs := axsof' ctxt;
                        etms := etmsof ctxt; etys := etysof ctxt; eaxs := eaxsof' ctxt|>`
      >> simp[ctys_def, ctms_def]
      >> res_tac >> simp[])
  (* NewConst: tms gets a new entry *)
  >- (irule theory_ok'_tms_extend >> simp[])
  (* ConstSpec *)
  >- (irule theory_ok'_conservative_extend >> cheat)
  (* NewType: tys gets a new entry *)
  >- (irule theory_ok'_tys_extend >> simp[])
  (* TypeDefn *)
  >- (irule theory_ok'_conservative_extend >> cheat)
  (* NewEliminableType: only etys changes *)
  >- (irule theory_ok'_etys_extend >> simp[])
  (* NewEliminableConst: only etms changes *)
  >- (irule theory_ok'_etms_extend >> simp[])
  (* NewEliminableAxiom: only eaxs changes *)
  >- (fs[theory_ok'_def, axioms_ok_def]
      >> rpt conj_tac >> rpt strip_tac >> gvs[sigof'_def]
      >> TRY (res_tac >> gvs[ctys_def, ctms_def])
      >> irule (iffRL term_ok'_sig_eq)
      >> qexists_tac `<|tms := tmsof ctxt; tys := tysof ctxt; axs := axsof' ctxt;
                        etms := etmsof ctxt; etys := etysof ctxt; eaxs := eaxsof' ctxt|>`
      >> simp[ctys_def, ctms_def]
      >> res_tac >> simp[])
QED

Theorem extends_theory_ok':
  ctxt2 extends' ctxt1 ⇒ theory_ok' (ethyof ctxt1) ⇒ theory_ok' (ethyof ctxt2)
Proof
  MATCH_MP_TAC (SPEC ``\x:update' list. theory_ok' (ethyof x)`` extends'_ind |> SIMP_RULE std_ss []) >>
  metis_tac[updates_theory_ok']
QED


val _ = export_theory();
