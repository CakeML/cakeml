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

val cpn_distinct = TypeBase.distinct_of ``:ordering``
val cpn_nchotomy = TypeBase.nchotomy_of ``:ordering``

val strip_d1 = CONV_TAC (REWR_CONV (DECIDE “p ∨ q ⇔ ¬p ⇒ q”)) THEN strip_tac
val strip_d2 = CONV_TAC (REWR_CONV (DECIDE “p ∨ q ⇔ ¬q ⇒ p”)) THEN strip_tac


Theorem term_ok'_imp_term_ok:
  ∀tm. term_ok' thy tm ⇒ term_ok (thy.ctys,thy.ctms) tm
Proof
  Induct_on ‘tm’ >> rw[term_ok'_def, term_ok_def]
QED


Theorem esubst_has_type_bool_alt:
  ∀tm.
    esubsts_ok (thy.ctys, thy.ctms) σ ∧
    term_ok' thy tm ∧
    theory_ok' thy ∧
    tm has_type Bool ⇒
    esubst σ avds tm has_type Bool
Proof
  rpt strip_tac >> irule esubst_has_type_bool
  >> rw[] >> first_x_assum $ irule_at Any
  >> simp[term_ok'_imp_term_ok]
  >> qexists ‘thy.axs’
  >> gvs[theory_ok_def, theory_ok'_def, ctys_def, ctms_def]
  >> rw[FRANGE_FUNION]
  >> metis_tac[is_std_sig_funion, sigof'_def,
               term_ok_weakening, type_ok_weakening]
QED


Theorem proves_imp_proves':
  ∀h. (thy, h) |- c ⇒ (lift_thy thy, {}, h) |-' c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves'_ABS >> rw[])
  >- (irule proves'_ASSUME >> rw[])
  >- (irule proves'_BETA >> rw[])
  >- (dxrule_all_then (ACCEPT_TAC o SRULE[]) proves'_DEDUCT_ANTISYM)
  >- (dxrule_all proves'_EQ_MP >> rw[])
  >- (irule proves'_INST >> rw[])
  >- (irule proves'_INST_TYPE >> rw[])
  >- (drule_all welltyped_comb >> strip_tac
      >> dxrule_all proves'_MK_COMB >> simp[])
  >- (irule proves'_REFL >> rw[])
  >- (irule proves'_axioms >> rw[])
QED


Theorem theory_ok_drop_thy:
  ∀es. theory_ok' thy ∧ (∀a. a ∈ es ⇒ term_ok thy.sig a ∧ a has_type Bool) ⇒
       theory_ok (drop_thy es thy)
Proof
  rw[theory_ok'_def, theory_ok_def, drop_thy]
  >> gvs[ctys_def, ctms_def, sigof'_def, FRANGE_FUNION,
         type_ok_weakening, term_ok_weakening, is_std_sig_funion]
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

Theorem theory_ok'_esubst:
  theory_ok' thy ∧ esubsts_ok' thy σ ⇒ theory_ok' (esubst_thy σ thy)
Proof
  cheat
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

Theorem DISJOINT_FLOOKUP:
  DISJOINT (FDOM f1) (FDOM f2) ∧ FLOOKUP f1 k = SOME v ⇒ FLOOKUP f2 k = NONE
Proof
  rw[] >> imp_res_tac $ iffRL FDOM_FLOOKUP >> irule $ iffRL $ cj 1 flookup_thm >> ASM_SET_TAC[]
QED

Theorem esubsts_ok'_esubsts_ok:
  esubsts_ok' thy σ ∧ theory_ok' thy ⇒ esubsts_ok (thy.ctys, thy.ctms) σ
Proof
  Cases_on ‘σ’ >> rename1‘(σ,θ)’ >> rw[esubsts_ok'_def, esubsts_ok_def, theory_ok'_def]
  >- (first_x_assum drule >> simp[ctms_def, FLOOKUP_FUNION] >> CASE_TAC >> rw[]
      >> drule_all DISJOINT_FLOOKUP >> simp[])
  >> first_x_assum drule >> rw[] >> gvs[term_ok_def, term_ok'_def]
  >> gvs[ctys_def, type_ok_weakening, ctms_def, esubst_thy_def, FLOOKUP_FUNION]
  >> qexists ‘ty0’ >> gvs[monomorphic_type_subst] >> rw[FLOOKUP_o_f]
  >> gvs[ctys_def, type_ok_weakening, ctms_def, esubst_thy_def, FLOOKUP_FUNION, AllCaseEqs()]
  >> cheat
QED

val contrapos_tac = CONV_TAC (REWR_CONV (DECIDE “p ⇒ q ⇔ ¬q ⇒ ¬p”)) THEN strip_tac

Theorem ty_esubst_o_f_thy_tms:
  ∀thy. theory_ok' thy ∧ esubsts_ok' thy σ ⇒ ty_esubst σ o_f thy.tms = thy.tms
Proof
  cheat
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
          >> first_x_assum $ irule_at Any >> simp[]))
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
  >- (gvs[drop_thy] >> drule proves_theory_ok >> drule esubsts_ok'_esubsts_ok >> rw[]
      >> ‘∀tm. MEM tm h ∨ tm = c ⇒ no_var_collapse σ tm’ by metis_tac[]
      >> drule_all proves_substitutable >> rw[esubst_thy_def, esubst_sig_def, ctms_def, ctys_def, o_f_FUNION]
      >> gvs[ty_esubst_o_f_thy_tms] >> imp_res_tac proves_theory_ok >> irule axiom_weakening
      >> first_x_assum $ irule_at Any >> gvs[theory_ok'_def] >> rw[SUBSET_DEF, DISJ_IMP_THM]
      >> cheat)
  >- (irule proves_axioms >> rw[]
      >- (irule theory_ok_drop_thy_alt >> gvs[theory_ok'_def])
      >> rw[drop_thy])
QED


val _ = export_theory();
