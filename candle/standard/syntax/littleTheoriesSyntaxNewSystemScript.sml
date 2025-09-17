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


Theorem proves_imp_theory_ok':
  ∀thy h es c. (thy, es, h) |-' c ⇒ theory_ok' thy
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[]
QED


Theorem proves'_imp_theory_ok:
  ∀thy es h c. (thy, es, h) |-' c ⇒ theory_ok' thy
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[]
QED

Theorem term_ok_term_ok'_weakening:
  term_ok thy.sig p ⇒ term_ok' thy p
Proof
  rw[] >> irule term_ok_imp_term_ok'
  >> gvs[sigof'_def, ctms_def, ctys_def, term_ok_weakening]
QED
(*
Theorem esubst_thy_ctys[simp]:
  (esubst_thy σ thy).ctys = thy.tys
Proof
  Cases_on ‘σ’ >> simp[esubst_thy_def, ctys_def]
QED*)

(*Theorem term_ok'_esubst:
  ∀tm.
    esubsts_ok (thy.ctys, thy.ctms) σ ∧
    esubsts_total thy σ ∧
    term_ok' thy tm ⇒
    term_ok' (esubst_thy σ thy) (esubst σ avds tm)
Proof
  Cases_on ‘σ’ >> rename [‘esubst (σ, θ) _ _’]
  >> Induct_on ‘tm’ >> rw[] >> gvs[term_ok'_def, esubst_def]
  >- (rw[esubst_tm_def, term_ok'_def]
      >> irule ty_esubst_type_ok >> simp[esubsts_ok_def]
      >> rw[] >> metis_tac[])
  >- (rw[esubst_tm_def, term_ok'_def] >> rC ‘FLOOKUP θ tmnm’
      >> gvs[ctms_def, FLOOKUP_FUNION]
      >> rC ‘FLOOKUP thy.tms tmnm’ >> simp[term_ok'_def]
      >> gvs[ctms_def, FLOOKUP_FUNION]
      >> last_assum $ qspec_then ‘tmnm’ mp_tac
      >> rw[]
      >- (irule ty_esubst_type_ok >> simp[esubsts_ok_def]
          >> cheat)
      >- spec_impl ‘ty0’ >> simp[ctys_def, FLOOKUP_FUNION])
QED*)
(*
Theorem used_eaxs_ok:
  ∀thy used_eaxs h c.
    (thy, used_eaxs, h) |-' c
    ⇒ ∀e. e ∈ used_eaxs ⇒ term_ok' thy e ∧ e has_type Bool
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[]
  >> gvs[theory_ok'_def, term_ok_term_ok'_weakening, term_ok'_esubst]
  >> first_x_assum drule >> gvs[esubst_has_type_bool_alt, SF SFY_ss]
QED*)



Theorem drop_thy_weakening:
  (drop_thy B thy', h) |- c ∧ B ⊆ A
  ∧ (∀ax. ax ∈ A ⇒ term_ok (thy'.ctys, thy'.ctms) ax ∧ ax has_type Bool)
  ⇒ (drop_thy A thy', h) |- c
Proof
  rw[drop_thy] >> irule axiom_weakening >> rw[]
  >> drule proves_imp_theory_ok >> rw[theory_ok_def, ctms_def, ctys_def]
  >> gvs[ctys_def, ctms_def] >> first_assum $ irule_at Any >> ASM_SET_TAC[]
QED

Theorem esubsts_ok_weakening:
  esubsts_total thy σ ∧
  esubsts_ok (thy.tys, thy.tms) σ ⇒
  esubsts_ok (thy.ctys, thy.ctms) σ
Proof
  Cases_on ‘σ’ >> rw[esubsts_total_def, esubsts_ok_def, ctms_def, ctys_def]
  >- (first_x_assum $ drule o iffRL >> rw[] >> first_x_assum drule
      >> rw[] >> rw[FLOOKUP_FUNION])
  >> rw[type_ok_weakening, term_ok_weakening]
QED

Theorem esubst_ty_identity:
  term_ok thy.sig tm ∧
  theory_ok' thy ∧
  esubsts_ok (thy.ctys, thy.ctms) σ ∧
  esubsts_total thy σ ⇒
  esubst_ty σ [] tm = tm
Proof
  cheat
QED

Theorem esubst_tm_identity:
  term_ok thy.sig tm ∧
  theory_ok' thy ∧
  esubsts_ok (thy.ctys, thy.ctms) σ ∧
  esubsts_total thy σ ⇒
  esubst_tm σ tm = tm
Proof
  Induct_on ‘tm’ >> rw[esubst_tm_def] >> gvs[]
  >> CASE_TAC >> Cases_on ‘σ’ >> gvs[esubsts_ok_def, sigof'_def, theory_ok'_def]
  >> first_x_assum $ qspec_then ‘m’ assume_tac >> rw[] >> gvs[TO_FLOOKUP]
  >> gvs[monomorphic_type_subst] >> rC ‘x = Const m ty0’
  >> Cases_on ‘ty_esubst (q,r) ty0 = ty0’ >> rw[] >> gvs[]
  >> cheat
QED

Theorem esubst_identity:
  term_ok thy.sig tm ∧
  theory_ok' thy ∧
  esubsts_ok (thy.ctys, thy.ctms) σ ∧
  esubsts_total thy σ ⇒
  esubst σ [] tm = tm
Proof
  rw[esubst_def] >> metis_tac[esubst_ty_identity, esubst_tm_identity]
QED

Theorem esubst_axs_fixed:
  theory_ok' thy ∧
  esubsts_ok (thy.ctys, thy.ctms) σ ∧
  esubsts_total thy σ ⇒
  IMAGE (esubst σ []) thy.axs = thy.axs
Proof
  Cases_on ‘σ’ >> rename [‘esubsts_total thy (σ, θ)’]
  >> rw[EXTENSION, EQ_IMP_THM, esubsts_ok_def, esubsts_total_def, theory_ok'_def]
  >> first_assum drule
  >> rpt strip_tac
  >> drule esubst_identity
  >> strip_tac >> first_x_assum $ qspec_then ‘(σ, θ)’ mp_tac
  >> impl_tac
  >> rw[theory_ok'_def, esubsts_ok_def, esubsts_total_def]
  >> metis_tac[]
QED
(*
Theorem proves'_imp_proves:
  ∀thy' c h used_eaxs.
    (thy', used_eaxs, h) |-' c ⇒ (drop_thy used_eaxs thy', h) |- c
Proof
  Induct_on ‘$|-'’ >> rw[]
  >- (irule proves_ABS >> rw[])
  >- (irule proves_ASSUME >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_BETA >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_DEDUCT_ANTISYM
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_EQ_MP
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_INST >> rw[] >> first_x_assum drule
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_INST_TYPE >> rw[] >> first_x_assum drule
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_MK_COMB >> rw[]
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_REFL >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_axioms >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok]
      >> metis_tac[axsof_drop_thy, SUBSET_DEF])
  >- (Cases_on ‘c ∈ thy.axs’ >> gvs[drop_thy]
      >- (rw[thy_axs_diff_alt, UNION_COMM] >> irule axiom_weakening
          >> drule proves'_imp_theory_ok >> rw[]
          >> gvs[theory_ok'_def, used_eaxs_ok, term_ok'_imp_term_ok, term_ok_term_ok'_weakening]
          >> rpt $ dxrule used_eaxs_ok >> rw[term_ok'_imp_term_ok]
          >> qexists ‘thy.axs ∪ es2’ >> rw[] >> SET_TAC[])
      >- (rw[thy_axs_diff]
          >> qspecl_then [‘((thy.ctys, thy.ctms), thy.axs ∪ es1)’,
                          ‘((thy.ctys, thy.ctms), thy.axs ∪ es2)’,
                          ‘h2’, ‘c’, ‘c'’]
                         assume_tac axioms_eliminable
          >> gvs[]))
  >- (gvs[drop_thy] >> drule esubsts_ok_weakening >> rw[] >> gvs[sigof'_def]
      >> drule proves_theory_ok >> rw[]
      >> drule_all proves_substitutable >> rw[] >> gvs[EVERY_MEM]
      >> drule_all esubst_axs_fixed >> rw[] >> gvs[])
  >- (irule proves_axioms >> rw[]
      >- (irule theory_ok_drop_thy_alt >> gvs[theory_ok'_def])
      >> rw[drop_thy])
QED
*)
