(*
  Defines the HOL inference system.
*)
open preamble holSyntaxLibTheory mlstringTheory totoTheory holSyntaxTheory

val _ = new_theory "littleTheoriesSyntax"

(* A theory is a signature together with a set of axioms. It is well-formed if
   the types of the constants are all ok, the axioms are all ok terms of type
   bool, and the signature is standard. *)

Type thy' = ``:(sig # term set) # (sig # term set)``
Datatype: ethy = <| tms: mlstring |-> type;
                    tys: mlstring |-> num;
                    axs: term set;
                    etms: mlstring |-> type;
                    etys: mlstring |-> num;
                    eaxs: term set |>
End


Definition ctys_def:
  ctys thy = thy.tys ⊌ thy.etys
End

val _ = add_record_field ("ctys", “ctys”)

Definition ctms_def:
  ctms thy = thy.tms ⊌ thy.etms
End

val _ = add_record_field ("ctms", “ctms”)

Definition sigof'_def:
  sigof' thy = (thy.tys, thy.tms)
End

val _ = add_record_field ("sig", “sigof'”)


(* Standard signature includes the minimal type operators and constants *)

(* term_ok' has to check if types are valid through both the types and
 eliminable types *)
Definition term_ok'_def:
  (term_ok' thy' (Var x ty) ⇔ type_ok thy'.ctys ty) ∧
  (term_ok' thy' (Const name ty) ⇔
     ∃ty0. FLOOKUP thy'.ctms name = SOME ty0 ∧
           type_ok thy'.ctys ty ∧
           is_instance ty0 ty) ∧
  (term_ok' thy' (Comb tm1 tm2) ⇔
     term_ok' thy' tm1 ∧
     term_ok' thy' tm2 ∧
     welltyped (Comb tm1 tm2)) ∧
  (term_ok' thy' (Abs v tm) ⇔
     ∃x ty.
       v = Var x ty ∧
       type_ok thy'.ctys ty ∧
       term_ok' thy' tm)
End

Definition theory_ok'_def:
  theory_ok' (thy:ethy) ⇔
    (∀ty. ty ∈ FRANGE thy.tms ⇒ type_ok thy.tys ty) ∧
    (∀ty. ty ∈ FRANGE thy.etms ⇒ type_ok thy.ctys ty) ∧
    DISJOINT (FDOM thy.tys) (FDOM thy.etys) ∧
    DISJOINT (FDOM thy.tms) (FDOM thy.etms) ∧
    (∀p. p ∈ thy.axs ⇒ term_ok thy.sig p ∧ p has_type Bool) ∧
    (∀p. p ∈ thy.eaxs ⇒
         term_ok' thy p ∧ p has_type Bool) ∧
    is_std_sig thy.sig
End

(* Sequents provable from a theory *)

val _ = Parse.add_infix("|-'",450,Parse.NONASSOC)

Inductive proves':
[~ABS:]
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok thy.ctys ty ∧
   (thy, es, h) |-' l === r
   ⇒ (thy, es, h) |-' (Abs (Var x ty) l) === (Abs (Var x ty) r))

[~ASSUME:]
  (theory_ok' thy ∧ p has_type Bool ∧ term_ok' thy p
   ⇒ (thy, es, [p]) |-' p)

[~BETA:]
  (theory_ok' thy ∧ type_ok thy.ctys ty
   ∧ term_ok' thy t
   ⇒ (thy, es, []) |-' Comb (Abs (Var x ty) t) (Var x ty) === t)

[~DEDUCT_ANTISYM:]
  ((thy, es, h1) |-' c1 ∧
   (thy, es, h2) |-' c2
   ⇒ (thy, es, term_union (term_remove c2 h1)
                          (term_remove c1 h2))
     |-' c1 === c2)

[~EQ_MP:]
  ((thy, es, h1) |-' p === q ∧
   (thy, es, h2) |-' p' ∧ ACONV p p'
   ⇒ (thy, es, term_union h1 h2) |-' q)

[~INST:]
  ((∀s s'. MEM (s',s) ilist ⇒
           ∃x ty. (s = Var x ty) ∧ s' has_type ty
                  ∧ term_ok' thy s') ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (VSUBST ilist) h) |-' VSUBST ilist c)

[~INST_TYPE:]
  ((EVERY (type_ok thy.ctys) (MAP FST tyin)) ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (INST tyin) h) |-' INST tyin c)

[~MK_COMB:]
  ((thy, es, h1) |-' l1 === r1 ∧
   (thy, es, h2) |-' l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, es, term_union h1 h2) |-' Comb l1 l2 === Comb r1 r2)

[~REFL:]
  (theory_ok' thy ∧ term_ok' thy t
   ⇒ (thy, es, []) |-' t === t)

[~axioms:]
  (theory_ok' thy ∧ c ∈ thy.axs
   ⇒ (thy, es, []) |-' c)

[~elim_discharge:]
  (thy, es1, []) |-' c1 ∧ (thy, es2, h2) |-' c2
⇒ (thy, term_union (term_remove c1 es2) es1, h2) |-' c2

(* have to define SUBST and SUBSTL first
[~elim_inst:]
  (thy, es1, h1) |-' c
⇒ (thy, SUBSTL es sigma, SUBSTL es h1) |-' SUBST c sigma
 *)

[~elim_axioms:]
  (theory_ok' thy ∧ c ∈ thy.eaxs
   ⇒ (thy, [c], []) |-' c)
End

Definition lift_thy_def:
  lift_thy (thy:thy) = <| tms := tmsof thy;
                    tys := tysof thy;
                    etms := FEMPTY;
                    etys := FEMPTY;
                    axs := axsof thy;
                    eaxs := {} |>
End

Theorem tmsof_lift_thy[simp]:
  (lift_thy thy).tms = tmsof thy
Proof
  simp[lift_thy_def]
QED

Theorem tysof_lift_thy[simp]:
  (lift_thy thy).tys = tysof thy
Proof
  simp[lift_thy_def]
QED

Theorem axsof_lift_thy[simp]:
  (lift_thy thy).axs = axsof thy
Proof
  simp[lift_thy_def]
QED

Theorem eaxsof_lift_thy[simp]:
  (lift_thy thy).eaxs = {}
Proof
  simp[lift_thy_def]
QED

Theorem etmsof_lift_thy[simp]:
  (lift_thy thy).etms = FEMPTY
Proof
  simp[lift_thy_def]
QED

Theorem etysof_lift_thy[simp]:
  (lift_thy thy).etys = FEMPTY
Proof
  simp[lift_thy_def]
QED

Theorem sigof_lift_thy[simp]:
  (lift_thy thy).sig = sigof thy
Proof
  simp[lift_thy_def, sigof'_def]
QED

Theorem ctys_lift_thy[simp]:
  (lift_thy thy).ctys = tysof thy
Proof
  simp[lift_thy_def, ctys_def]
QED

Theorem ctms_lift_thy[simp]:
  (lift_thy thy).ctms = tmsof thy
Proof
  simp[lift_thy_def, ctms_def]
QED

Theorem theory_ok'_lift_thy[simp]:
  theory_ok' (lift_thy thy) ⇔ theory_ok thy
Proof
  rw[theory_ok_def, theory_ok'_def, lift_thy_def]
QED

        
Theorem term_ok'_lift_thy[simp]:
  term_ok' (lift_thy thy) tm ⇔ term_ok (sigof thy) tm
Proof
  Induct_on ‘tm’
  >> rw[term_ok_def, term_ok'_def, lift_thy_def]
QED
        
Theorem proves_imp_proves':
 ∀h. (thy, h) |- c ⇒ (lift_thy thy, [], h) |-' c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves'_ABS >> rw[])
  >- (irule proves'_ASSUME >> rw[])
  >- (irule proves'_BETA >> rw[])
  >- (irule proves'_DEDUCT_ANTISYM >> rw[])
  >- (irule proves'_EQ_MP >> metis_tac[])
  >- (irule proves'_INST >> rw[])
  >- (irule proves'_INST_TYPE >> rw[])
  >- (irule proves'_MK_COMB >> rw[])
  >- (irule proves'_REFL >> rw[])
  >- (irule proves'_axioms >> rw[])
QED

Definition consts_of:
  (consts_of (Var _ _) = {}) ∧
  (consts_of (Const n ty) = {(n, ty)}) ∧
  (consts_of (Comb s t) = consts_of s UNION consts_of t) ∧
  (consts_of (Abs _ body) = consts_of body)
End

Definition tyconsts_of:
  (tyconsts_of (Tyvar n) = {}) ∧
  (tyconsts_of (Tyapp n ts) = n INSERT (FOLDR (λx acc. tyconsts_of x ∪ acc) {} ts))
Termination
  WF_REL_TAC ‘measure type_size’
End

Theorem tyconsts_foldr_rw[simp]:
  FOLDR (λx acc. tyconsts_of x ∪ acc) {} l
  = BIGUNION (IMAGE tyconsts_of (set l))
Proof
  Induct_on ‘l’ >> rw[]
QED

Definition tyconsts_of_tm[simp]:
  (tyconsts_of_tm (Var _ ty) = tyconsts_of ty) ∧
  (tyconsts_of_tm (Const n ty) = tyconsts_of ty) ∧
  (tyconsts_of_tm (Comb s t) = tyconsts_of_tm s ∪ tyconsts_of_tm t) ∧
  (tyconsts_of_tm (Abs v body) = tyconsts_of_tm v ∪ tyconsts_of_tm body)
End

Definition tyconsts_of_tml[simp]:
  (tyconsts_of_tml [] = {}) ∧
  (tyconsts_of_tml (x::xs) = tyconsts_of_tm x ∪ tyconsts_of_tml xs)
End

Definition tyconsts_of_tms[simp]:
  tyconsts_of_tms A = BIGUNION (IMAGE tyconsts_of_tm A)
End

Definition remove_tysig_def:
  remove_tysig ty (tys, tms) = (tys \\ ty, tms)
End

Theorem type_ind =
  TypeBase.induction_of``:holSyntax$type``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE std_ss [EVERY_DEF]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

Theorem flookup_tysof_remove_tysig:
  FLOOKUP (tysof (remove_tysig n sig)) m =
  (if m = n then NONE else FLOOKUP (tysof sig) m)
Proof
  rw[] >> Cases_on ‘sig’ >> rw[remove_tysig_def, FLOOKUP_DEF, DOMSUB_FAPPLY_NEQ]
QED

Theorem flookup_tmsof_remove_tysig:
  FLOOKUP (tmsof (remove_tysig n sig)) m = FLOOKUP (tmsof sig) m
Proof
  rw[] >> Cases_on ‘sig’ >> rw[remove_tysig_def]
QED

Theorem notin_foldr_tyconsts:
  tyn ∉ FOLDR (λx acc. tyconsts_of x ∪ acc) ∅ l
  ⇒ ∀ty. MEM ty l ⇒ tyn ∉ tyconsts_of ty
Proof
  rw[] >> metis_tac[]
QED

Theorem remove_tysig_type_ok_alt:
  tyn ∉ tyconsts_of ty ∧ type_ok (tysof sig) ty
  ⇒ type_ok (tysof (remove_tysig tyn sig)) ty
Proof
  Induct_on ‘ty’ using type_ind >> gvs[type_ok_def]
  >> rw[] >> gvs[tyconsts_of]
  >- rw[flookup_tysof_remove_tysig]
  >> gvs[EVERY_MEM] >> drule notin_foldr_tyconsts
  >> metis_tac[]
QED

Theorem remove_tysig_term_ok_alt:
  tyn ∉ tyconsts_of_tm tm ∧ term_ok sig tm
  ⇒ term_ok (remove_tysig tyn sig) tm
Proof
  Induct_on ‘tm’
  >> rw[tyconsts_of_tm, term_ok_def, type_ok_def, remove_tysig_type_ok_alt]
  >- (Induct_on ‘TYPE_SUBST i ty0’ using type_ind
      >> rw[flookup_tmsof_remove_tysig, remove_tysig_type_ok_alt]
      >> metis_tac[])
  >- (Induct_on ‘ty’ using type_ind
      >> rw[type_ok_def, tyconsts_of, flookup_tysof_remove_tysig]
      >> gvs[EVERY_MEM] >> drule notin_foldr_tyconsts >> rw[]
      >> irule remove_tysig_type_ok_alt >> rw[])
QED

Theorem in_frange_cases:
  ty ∈ FRANGE (tmsof (remove_tysig tyn sig)) ∧ tyn ∉ tyconsts_of ty
  ⇒ ty ∈ FRANGE (tmsof sig)
Proof
  Cases_on ‘sig’ >> Cases_on ‘ty’ >> rw[tyconsts_of, remove_tysig_def]
QED

Theorem frange_remove_tysig_subset:
  FRANGE (tmsof (remove_tysig tyn sig)) ⊆ FRANGE (tmsof sig)
Proof
  rw[] >> Cases_on ‘sig’ >> rw[remove_tysig_def]
QED

Theorem forall_subset:
  ∀P s1 s2. (∀x. x ∈ s1 ⇒ P x) ∧ s2 ⊆ s1 ⇒ (∀x. x ∈ s2 ⇒ P x)
Proof
  metis_tac[SUBSET_DEF]
QED

Theorem remove_tysig_theory_ok:
  theory_ok (sig, axs) ∧ tyn ∉ tyconsts_of_tms axs
  ∧ (∀ty. ty ∈ FRANGE (tmsof sig) ⇒ tyn ∉ tyconsts_of ty)
  ∧ is_std_sig (remove_tysig tyn sig)
  ⇒ theory_ok (remove_tysig tyn sig, axs)
Proof
  gvs[theory_ok_def] >> rw[]
  >- (irule remove_tysig_type_ok_alt >> gvs[] >> rw[]
      >> first_assum irule >> irule in_frange_cases >> qexists ‘tyn’
      >> rw[frange_remove_tysig_subset]
      >> qspecl_then [‘λty. tyn ∉ tyconsts_of ty’,
                      ‘FRANGE (tmsof sig)’,
                      ‘FRANGE (tmsof (remove_tysig tyn sig))’]
                     assume_tac forall_subset
      >> gvs[frange_remove_tysig_subset])
  >- (first_x_assum drule_all >> rw[] >> irule remove_tysig_term_ok_alt
      >> rw[] >> metis_tac[])
QED

Theorem tyconsts_of_term_union:
  tyn ∉ tyconsts_of_tml (term_union h1 h2) ⇒
  tyn ∉ tyconsts_of_tml h1 ∧ tyn ∉ tyconsts_of_tml h2
Proof
  cheat
QED

Theorem tyconsts_of_term_remove:
  tyn ∉ tyconsts_of_tm c ∧ tyn ∉ tyconsts_of_tml (term_remove c h)
  ⇒ tyn ∉ tyconsts_of_tml h
Proof
  cheat
QED

Theorem tyconsts_of_codomain:
  ∀t. tyconsts_of (codomain t) ⊆ tyconsts_of t
Proof
  cheat
QED

Theorem notin_tyconsts_typeof:
  tyn ≠ «fun» ∧ tyn ∉ tyconsts_of_tm tm  ⇒ tyn ∉ tyconsts_of (typeof tm)
Proof
  Induct_on ‘tm’ >> rw[tyconsts_of_tm, typeof_def, tyconsts_of]
  >> gvs[] >> metis_tac[tyconsts_of_codomain, SUBSET_DEF]
QED

Theorem tyn_notin_mk_comb:
  tyn ∉ tyconsts_of_tm (Comb l1 l2 === Comb r1 r2)
  ⇒ tyn ∉ tyconsts_of_tm (l1 === r1) ∧ tyn ∉ tyconsts_of_tm (l2 === r2)
Proof
  rw[equation_def, tyconsts_of_tm, tyconsts_of, notin_tyconsts_typeof]
  >> metis_tac[tyconsts_of_codomain, notin_tyconsts_typeof, SUBSET_DEF]
QED

(*Theorem strip_redun_ty_consts:
  ∀sig axs h c tyn.
    ((sig, axs), h) |- c
    ∧ tyn ∉ tyconsts_of_tm c
    ∧ tyn ∉ tyconsts_of_tms axs
    ∧ (∀ty. ty ∈ FRANGE (tmsof sig) ⇒ tyn ∉ tyconsts_of ty)
    ∧ tyn ∉ tyconsts_of_tml h
    ∧ is_std_sig (remove_tysig tyn sig)
    ⇒ ((remove_tysig tyn sig, axs), h) |- c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves_ABS >> gvs[equation_def, tyconsts_of_tm, tyconsts_of]
      >> rw[remove_tysig_type_ok_alt])
  >- (irule proves_ASSUME >> gvs[] >> rw[remove_tysig_type_ok_alt,
                                         remove_tysig_term_ok_alt,
                                         remove_tysig_theory_ok])
  >- (irule proves_BETA >> gvs[equation_def, tyconsts_of_tm, tyconsts_of]
      >> rw[remove_tysig_type_ok_alt, remove_tysig_term_ok_alt,
            remove_tysig_theory_ok])
  >- (irule proves_DEDUCT_ANTISYM >> rw[]
      >> gvs[equation_def, tyconsts_of_tm, tyconsts_of]
      >> dxrule_at Any tyconsts_of_term_union >> rw[]
      >> metis_tac[tyconsts_of_term_remove])
  >- (irule proves_EQ_MP >> qexistsl [‘p’, ‘c’] >> rw[]
      >- cheat
      >- metis_tac[tyconsts_of_term_union]
      >> cheat)
  >- (irule proves_INST >> cheat)
  >- (irule proves_INST_TYPE >> cheat)
  >- (irule proves_MK_COMB >> metis_tac[tyn_notin_mk_comb, tyconsts_of_term_union])
  >- (irule proves_REFL >> rw[]
      >- (irule remove_tysig_theory_ok >> rw[])
      >- (irule remove_tysig_term_ok_alt
          >> gvs[equation_def, tyconsts_of_tm, tyconsts_of]))
  >- (irule proves_axioms >> gvs[remove_tysig_theory_ok])
QED*)

Theorem var_vfree_in:
  EVERY ($¬ ∘ VFREE_IN (Var x ty')) h ⇒ ¬(MEM (Var x ty') h)
Proof
  Induct_on ‘h’ >> rw[] >> Cases_on ‘h'’ >> gvs[VFREE_IN_def]
QED

(*Theorem strip_redun_tm_consts:
  ∀thy h. (thy, h) |- c ∧ tm ∉ tmset c ∧ tm ∉ tmsetl h
          ∧ tm ∉ tmsets (axsof thy)
          ⇒ (remove_tmsig tm thy, h) |- c
Proof
  cheat
QED*)

Theorem proves_theory_ok:
  ∀thy h c. (thy, h) |- c ⇒ theory_ok thy
Proof
  Induct_on ‘$|-’ >> rw[] >> rw[]
QED

Theorem proves_theory_ok_ext:
  theory_ok thy1 ∧ (thy2, h) |- c ∧ sigof thy1 = sigof thy2
  ⇒ theory_ok (sigof thy1, axsof thy1 DIFF {c1} ∪ axsof thy2)
Proof
  rw[] >> drule proves_theory_ok >> gvs[theory_ok_def] >> metis_tac[]
QED

Theorem axiom_weakening:
  ∀axs h. ((sig, axs), h) |- c
          ∧ (∀p. p ∈ A ⇒ term_ok sig p ∧ p has_type Bool)
          ⇒ ((sig, A UNION axs), h) |- c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves_ABS >> rw[] >> gvs[])
  >- (irule proves_ASSUME >> rw[] >> gvs[theory_ok_def] >> metis_tac[])
  >- (irule proves_BETA >> rw[] >> gvs[theory_ok_def] >> metis_tac[])
  >- (irule proves_DEDUCT_ANTISYM >> rw[])
  >- (irule proves_EQ_MP >> metis_tac[])
  >- (irule proves_INST >> rw[] >> gvs[])
  >- (irule proves_INST_TYPE >> rw[] >> gvs[])
  >- (irule proves_MK_COMB >> rw[] >> gvs[])
  >- (irule proves_REFL >> rw[theory_ok_def, type_ok_def]
      >> gvs[theory_ok_def, type_ok_def])
  >- (irule proves_axioms >> rw[theory_ok_def, type_ok_def]
      >> gvs[theory_ok_def, type_ok_def])
QED

Theorem axioms_eliminable:
  ∀thy1 thy2 h2 c1 c2. (thy2, h2) |- c2 ∧ (thy1, []) |- c1
  ∧ sigof thy1 = sigof thy2
  ⇒ ((sigof thy1, (axsof thy2 DIFF {c1}) UNION axsof thy1), h2) |- c2
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves_ABS >> rw[])
  >- (irule proves_ASSUME >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (irule proves_BETA >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (irule proves_DEDUCT_ANTISYM >> rw[])
  >- (irule proves_EQ_MP >> rw[] >> metis_tac[])
  >- (irule proves_INST >> rw[])
  >- (irule proves_INST_TYPE >> rw[])
  >- (irule proves_MK_COMB >> rw[])
  >- (irule proves_REFL >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (Cases_on ‘c1 = c2’
      >- (rw[] >> irule axiom_weakening >> gvs[theory_ok_def]
          >> Cases_on ‘thy’ >> gvs[])
      >- (irule proves_axioms >> rw[] >> metis_tac[proves_theory_ok_ext]))
QED

Definition insert_sig_def:
  insert_sig thy'
  = (((tys ⊌ thy'.etys, tms ⊌ thy'.etms), axs):thy)
End

Theorem insert_sig_type_ok:
  type_ok (tysof (sigof (thy,esig,eaxs)) ⊌
                 tysof (elimsigof (thy,esig,eaxs))) ty
  ⇔ type_ok (tysof (sigof (insert_sig esig thy))) ty
Proof
  Cases_on ‘thy’ >> Cases_on ‘esig’ >> Cases_on ‘q’
  >> rw[insert_sig_def]
QED

Theorem is_std_sig_ext:
  is_std_sig (p, q) ⇒ is_std_sig (p ⊌ p', q ⊌ q')
Proof
  Induct_on ‘p’ >> rw[is_std_sig_def] >> gvs[is_std_sig_def]
  >> Cases_on ‘FLOOKUP f1 k’ >> rw[FLOOKUP_FUNION]
QED

Theorem every_monotonic_rw:
  ∀P Q. EVERY (λa. P a ⇒ Q a) l ∧ EVERY (λa. P a) l ⇒
        EVERY (λa. Q a) l
Proof
  Induct_on ‘l’ >> rw[] >> metis_tac[]
QED

Theorem type_ok_ext:
  ∀ty. type_ok p ty ⇒ type_ok (FUNION p q) ty
Proof
  ho_match_mp_tac type_ind >> rw[type_ok_def, FLOOKUP_FUNION]
  >> metis_tac[every_monotonic_rw]
QED

Theorem every_type_ok_ext:
  EVERY (λa. type_ok p a) l ⇒ EVERY (λa. type_ok (p ⊌ p') a) l
Proof
  metis_tac[type_ok_ext, EVERY_MONOTONIC]
QED

Theorem term_ok_ext:
  term_ok (p, q) c ⇒ term_ok (FUNION p p', FUNION q q') c
Proof
  Induct_on ‘c’ >> rw[term_ok_def] >> gvs[term_ok_def]
  >> rw[type_ok_ext] >> qexists ‘ty0’ >> rw[FLOOKUP_FUNION]
  >> metis_tac[]
QED

Theorem insert_sig_theory_ok:
  theory_ok' (thy,esig,eaxs) ⇒ theory_ok (insert_sig esig thy)
Proof
  Cases_on ‘esig’ >> Cases_on ‘thy’ >> Cases_on ‘q'’
  >> rw[theory_ok_def, insert_sig_def] >> gvs[theory_ok'_def]
  >- (drule_all IN_FRANGE_FUNION_suff >> rw[])
  >- rw[term_ok_ext]
  >- rw[is_std_sig_ext]
QED

Theorem term_ok'_imp_insert_sig:
  term_ok' (sigof (thy',esig,eaxs)) (elimsigof (thy',esig,eaxs)) c
  ⇒ term_ok (sigof (insert_sig esig thy')) c
Proof
  Induct_on ‘c’ >> Cases_on ‘thy'’ >> rw[term_ok_def] >> gvs[term_ok'_def]
  >> Cases_on ‘esig’ >> Cases_on ‘q’ >> rw[insert_sig_def] >> gvs[] >> metis_tac[]
QED

Theorem insert_sig_every_type_ok:
  EVERY (type_ok (tysof (sigof (thy',esig,eaxs)) ⊌
                        tysof (elimsigof (thy',esig,eaxs)))) (MAP FST tyin)
  ⇒ EVERY (type_ok (tysof (insert_sig esig thy'))) (MAP FST tyin)
Proof
  match_mp_tac EVERY_MONOTONIC >> rw[insert_sig_type_ok]
QED

Theorem insert_sig_axsof:
  c ∈ axsof (thy, esig, eaxs) ⇒ c ∈ axsof (insert_sig esig thy)
Proof
  Cases_on ‘thy’ >> rw[] >> Cases_on ‘q’ >> Cases_on ‘q'’ >> Cases_on ‘esig’
  >> rw[insert_sig_def]
QED

Definition insert_eaxs:
  insert_eaxs eaxs (thy:thy):thy = (sigof thy, (axsof thy) UNION eaxs)
End

Theorem sigof_insert_sig[simp]:
  sigof (insert_sig esig thy) = (tysof thy ⊌ FST esig, tmsof thy ⊌ SND esig)
Proof
  PairCases_on ‘thy’ >> Cases_on ‘esig’ >> rw[insert_sig_def]
QED

Theorem axsof_insert_sig[simp]:
  axsof (insert_sig esig thy) = axsof thy
Proof
  PairCases_on ‘thy’ >> Cases_on ‘esig’ >> rw[insert_sig_def]
QED

Definition drop_thy:
  drop_thy used_eaxs thy' : thy = ((thy'.ctys, thy'.ctms), thy'.axs UNION used_eaxs)
End

Theorem sigof_drop_thy[simp]:
  sigof (drop_thy (set es) thy) = (thy.ctys, thy.ctms)
Proof
  rw[drop_thy]
QED

Theorem theory_ok_drop_thy[simp]:
  theory_ok' thy ⇒ theory_ok (drop_thy (set es) thy)
Proof
  rw[theory_ok'_def, theory_ok_def, drop_thy] >> gvs[ctys_def, ctms_def]
QED
        

Theorem proves'_imp_proves:
  ∀thy' c h used_eaxs.
    (thy', used_eaxs, h) |-' c ⇒ (drop_thy (set used_eaxs) thy', h) |- c
Proof
  Induct_on ‘$|-'’ >> rw[]
  >- (irule proves_ABS >> rw[])
  >- (irule proves_ASSUME >> rw[])
  >- (irule proves_BETA >> rw[] >> metis_tac[
          insert_sig_theory_ok, term_ok'_imp_insert_sig, insert_sig_type_ok])
  >- (irule proves_DEDUCT_ANTISYM >> rw[])
  >- (irule proves_EQ_MP >> metis_tac[])
  >- (irule proves_INST >> metis_tac[term_ok'_imp_insert_sig])
  >- (irule proves_INST_TYPE >> metis_tac[insert_sig_every_type_ok])
  >- (irule proves_MK_COMB >> rw[])
  >- (irule proves_REFL >> rw[]
      >> metis_tac[insert_sig_theory_ok, term_ok'_imp_insert_sig])
  >- (irule proves_axioms >> rw[] >> metis_tac[insert_sig_theory_ok, insert_sig_axsof])
  >- cheat
QED


(* A context is a sequence of updates *)

Datatype:
  update'
  (* Definition of new constants by specification
     ConstSpec witnesses proposition *)
  = ConstSpec ((mlstring # term) list) term
  (* Definition of a new type operator
     TypeDefn name predicate abs_name rep_name *)
  | TypeDefn mlstring term mlstring mlstring
  (* NewType name arity *)
  | NewType mlstring num
  (* NewEliminableType name arity *)
  | NewEliminableType mlstring num
  (* NewConst name type *)
  | NewConst mlstring type
  (* NewEliminableConst name type *)
  | NewEliminableConst mlstring type
  (* NewAxiom proposition *)
  | NewAxiom term
  (* NewEliminableAxiom proposition *)
  | NewEliminableAxiom term
End

(* Projecting out pieces of the context *)

(* Types and constants introduced by an update *)
Definition types_of_upd_def:
  (types_of_upd' (ConstSpec _ _) = []) ∧
  (types_of_upd' (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_upd' (NewType name arity) = [(name,arity)]) ∧
  (types_of_upd' _ = [])
End

Definition consts_of_upd_def:
  (consts_of_upd' (ConstSpec eqs prop) = MAP (λ(s,t). (s, typeof t)) eqs) ∧
  (consts_of_upd' (TypeDefn name pred abs rep) =
     let rep_type = domain (typeof pred) in
     let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
       [(abs, Fun rep_type abs_type);
        (rep, Fun abs_type rep_type)]) ∧
  (consts_of_upd' (NewConst name type) = [(name,type)]) ∧
  (consts_of_upd' _ = [])
End

Overload type_list = ``λctxt. FLAT (MAP types_of_upd ctxt)``
Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``
Overload const_list = ``λctxt. FLAT (MAP consts_of_upd ctxt)``
Overload tmsof = ``λctxt. alist_to_fmap (const_list ctxt)``

(* From this we can recover a signature *)
Overload sigof = ``λctxt:update list. (tysof ctxt, tmsof ctxt)``

  (* Axioms: we divide them into axiomatic extensions and conservative
     extensions, we will prove that the latter preserve consistency *)
Definition axexts_of_upd_def:
  axexts_of_upd (NewAxiom prop) = [prop] ∧
  axexts_of_upd _ = []
End

Definition conexts_of_upd_def:
  (conexts_of_upd (ConstSpec eqs prop) =
    let ilist = MAP (λ(s,t). let ty = typeof t in (Const s ty,Var s ty)) eqs in
      [VSUBST ilist prop]) ∧
  (conexts_of_upd (TypeDefn name pred abs_name rep_name) =
    let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
    let rep_type = domain (typeof pred) in
    let abs = Const abs_name (Fun rep_type abs_type) in
    let rep = Const rep_name (Fun abs_type rep_type) in
    let a = Var (strlit "a") abs_type in
    let r = Var (strlit "r") rep_type in
      [Comb abs (Comb rep a) === a;
       Comb pred r === (Comb rep (Comb abs r) === r)]) ∧
  (conexts_of_upd _ = [])
End

Overload axexts = ``λctxt. FLAT (MAP axexts_of_upd ctxt)``
Overload conexts = ``λctxt. FLAT (MAP conexts_of_upd ctxt)``

Overload axioms_of_upd = ``λupd. axexts_of_upd upd ++ conexts_of_upd upd``
Overload axiom_list = ``λctxt. FLAT (MAP axioms_of_upd ctxt)``
Overload axsof = ``λctxt. set (axiom_list ctxt)``

val _ = export_rewrites["types_of_upd_def","consts_of_upd_def","axexts_of_upd_def"]

(* Now we can recover the theory associated with a context *)
Overload thyof = ``λctxt:update list. (sigof ctxt, axsof ctxt)``

(* Principles for extending the context *)

val _ = Parse.add_infix("updates",450,Parse.NONASSOC)

val _ = hide "abs";

Inductive updates':
  (* new_axiom *)
  (prop has_type Bool ∧
   term_ok (sigof ctxt) prop
   ⇒ (NewAxiom prop) updates' ctxt) ∧

  (* new_constant *)
  (name ∉ (FDOM (tmsof ctxt)) ∧
   type_ok (tysof ctxt) ty
   ⇒ (NewConst name ty) updates' ctxt) ∧

  (* new_specification *)
  ((thyof ctxt, MAP (λ(s,t). Var s (typeof t) === t) eqs) |- prop ∧
   EVERY
     (λt. CLOSED t ∧
          (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))))
     (MAP SND eqs) ∧
   (∀x ty. VFREE_IN (Var x ty) prop ⇒
             MEM (x,ty) (MAP (λ(s,t). (s,typeof t)) eqs)) ∧
   (∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (tmsof ctxt))) ∧
   ALL_DISTINCT (MAP FST eqs)
   ⇒ (ConstSpec eqs prop) updates' ctxt) ∧

  (* new_type *)
  (name ∉ (FDOM (tysof ctxt))
   ⇒ (NewType name arity) updates' ctxt) ∧

  (* new_type_definition *)
  (((thyof ctxt, empty_elims), [], []) |- Comb pred witness ∧
   CLOSED pred ∧
   name ∉ (FDOM (tysof ctxt)) ∧
   abs ∉ (FDOM (tmsof ctxt)) ∧
   rep ∉ (FDOM (tmsof ctxt)) ∧
   abs ≠ rep
   ⇒ (TypeDefn name pred abs rep) updates' ctxt)
End

Definition extends'_def:
  extends' ⇔ RTC (λctxt2 ctxt1. ∃upd. ctxt2 = upd::ctxt1 ∧ upd updates' ctxt1)
End
val _ = Parse.add_infix("extends'",450,Parse.NONASSOC)

(* Initial theory context *)

Definition init_ctxt_def:
  init_ctxt = [NewConst (strlit "=") (Fun (Tyvar(strlit "A")) (Fun (Tyvar(strlit "A")) Bool))
              ;NewType (strlit "bool") 0
              ;NewType (strlit "fun") 2]
End

val _ = export_theory()
