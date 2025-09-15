(*
  Some lemmas about the extended Little Theories syntactic functions.
*)
open preamble totoTheory comparisonTheory ternaryComparisonsTheory mlstringTheory
              holSyntaxLibTheory holSyntaxTheory errorMonadTheory
              littleTheoriesSyntaxTheory holSyntaxExtraTheory

val _ = new_theory"littleTheoriesSyntaxExtra"

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad("error");

val cpn_distinct = TypeBase.distinct_of ``:ordering``
val cpn_nchotomy = TypeBase.nchotomy_of ``:ordering``

val strip_d1 = CONV_TAC (REWR_CONV (DECIDE “p ∨ q ⇔ ¬p ⇒ q”)) THEN strip_tac
val strip_d2 = CONV_TAC (REWR_CONV (DECIDE “p ∨ q ⇔ ¬q ⇒ p”)) THEN strip_tac

Theorem esubst_ty_var[simp]:
  esubst_ty σ avds (Var n ty) =
  Var n (ty_esubst σ ty)
Proof
  rw[esubst_ty_def, esubst_ty0_def, REV_ASSOCD_def]
QED

Theorem esubst_ty_const[simp]:
  esubst_ty σ avds (Const n ty) =
  Const n (ty_esubst σ ty)
Proof
  rw[esubst_ty_def, esubst_ty0_def, REV_ASSOCD_def]
QED

Theorem REV_ASSOCD_NEQ_DEFAULT:
  REV_ASSOCD t2 σ d ≠ d ⇒
  ∃t1. MEM (t1, t2) σ ∧ t1 ≠ d
Proof
  Induct_on ‘σ’ >> rw[REV_ASSOCD_def] >> Cases_on ‘h’ >> gvs[]
  >> dsimp[] >> metis_tac[]
QED

Theorem try_eq_error:
  try m f = error e ⇔ ∃e1. m = error e1 ∧ f e1 = error e
Proof
  Cases_on ‘m’ >> rw[EQ_IMP_THM, try_def]
QED

Theorem try_eq_return:
  try m f = return v ⇔ m = return v ∨ ∃e. m = error e ∧ f e = return v
Proof
  Cases_on ‘m’ >> rw[EQ_IMP_THM, try_def]
QED

Theorem term_ok_rev_assocd:
  term_ok sig (REV_ASSOCD t1 env t2) ⇔
  (∃p t s. env = p ++ [(t, t1)] ++ s ∧ (∀e d. MEM (e, d) p ⇒ d ≠ t1)
           ∧ term_ok sig t)
  ∨ (∀e d. MEM (e, d) env ⇒ d ≠ t1) ∧ term_ok sig t2
Proof
  Induct_on ‘env’ >> rw[REV_ASSOCD_def]
  >> rename [‘h::env = _ ++ _ ++ _’] >> Cases_on ‘h’ >> gvs[]
  >- (iff_tac >> strip_tac
      >- (DISJ1_TAC >> qexists ‘[]’ >> simp[])
      >- (Cases_on ‘p’ >> gvs[])
      >- (metis_tac[]))
  >- (rw[EQ_IMP_THM] >> simp[FORALL_AND_THM]
      >- (qexistsl [‘(q,r)::p’] >> simp[])
      >- (Cases_on ‘p’ >> gvs[] >> metis_tac[]))
QED

Theorem has_type_var[simp] = hd (CONJUNCTS has_type_rules)
Theorem has_type_const[simp] = hd $ tl (CONJUNCTS has_type_rules)

Theorem rev_assocd_neq_mem:
  REV_ASSOCD x l d ≠ d ⇒ MEM (REV_ASSOCD x l d, x) l
Proof
  metis_tac[REV_ASSOCD_MEM]
QED

Theorem neq_error:
  (∀e. x ≠ error e) ⇔ ∃v. x = return v
Proof
  Cases_on ‘x’ >> rw[]
QED

Theorem vsubst_has_type:
  ∀ilist. t has_type τ ∧ vsubst_tys_ok ilist ⇒ (VSUBST ilist t) has_type τ
Proof
  Induct_on ‘_ has_type _’ >> rw[]
  >> gvs[VSUBST_def]
  >- (gvs[vsubst_tys_ok_def]
      >> Cases_on ‘REV_ASSOCD (Var n τ) ilist (Var n τ) = Var n τ’
      >- rw[has_type_rules]
      >- (drule_then assume_tac rev_assocd_neq_mem
          >> first_x_assum drule >> rw[]))
  >- metis_tac[has_type_rules]
  >> rw[]
  >> (irule (last $ CONJUNCTS has_type_rules) >> first_x_assum irule
      >> gvs[vsubst_tys_ok_def, DISJ_IMP_THM, FORALL_AND_THM,
             MEM_FILTER, has_type_rules])
QED

Theorem welltyped_comb_vsubst:
  welltyped (Comb x y) ∧ vsubst_tys_ok lst
  ⇒ welltyped (Comb (VSUBST lst x) (VSUBST lst y))
Proof
  rw[welltyped_def] >> drule_all vsubst_has_type >> rw[VSUBST_def]
  >> metis_tac[vsubst_has_type, WELLTYPED_LEMMA]
QED

Theorem vsubst_tys_ok_cons[simp]:
  vsubst_tys_ok (x::xs) ⇔
    vsubst_tys_ok xs ∧ ∃n ty s'. x = (s', Var n ty) ∧ s' has_type ty
Proof
  rw[vsubst_tys_ok_def, DISJ_IMP_THM, FORALL_AND_THM, EQ_IMP_THM]
  >> Cases_on ‘x’ >> gvs[]
QED

Theorem vsubst_tys_ok_filter[simp]:
  vsubst_tys_ok lst ⇒ vsubst_tys_ok (FILTER P lst)
Proof
  rw[vsubst_tys_ok_def, MEM_FILTER]
QED

Theorem term_ok_vsubst_alt:
  ∀x lst.
    EVERY (λp. term_ok sig (FST p)) lst ∧ term_ok sig x ∧ vsubst_tys_ok lst
    ⇒ term_ok sig (VSUBST lst x)
Proof
  rw[term_ok_VSUBST, vsubst_tys_ok_def, EVERY_MEM]
  >> irule term_ok_VSUBST >> rw[] >> rpt $ first_x_assum drule
  >> rw[]
QED

Theorem vsubst_tys_ok_nil[simp]:
  vsubst_tys_ok []
Proof
  rw[vsubst_tys_ok_def]
QED

Theorem VSUBST_nil[simp]:
  ∀tm. VSUBST [] tm = tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, REV_ASSOCD_def]
QED

Theorem VSUBST_nil_eta[simp]:
  VSUBST [] = λp. p
Proof
  metis_tac[VSUBST_nil]
QED

Theorem term_ok_vsubst_variant:
  ∀tm x1 x2 ty.
       term_ok sig tm
       ∧ type_ok (tysof sig) ty
       ⇒ term_ok sig (VSUBST [(Var x1 ty,
                               Var x2 ty)] tm)
Proof
  rw[] >> irule term_ok_VSUBST >> rw[term_ok_def]
QED

Theorem term_var_ok:
  ∀n sig ty. type_ok (tysof sig) ty ⇒ term_ok sig (Var n ty)
Proof
  rw[term_ok_def]
QED

Theorem VFREE_IN_VSUBST_OTHER_VAR:
  ∀tm ilist.
    term_ok sig tm
    ∧ (∀v1 v2. MEM (v1, v2) ilist ⇒
               ∃n1 t1 n2 t2. v1 = Var n1 t1 ∧ v2 = Var n2 t2 ∧ v1 ≠ v)
    ∧ VFREE_IN v (VSUBST ilist tm) ⇒ VFREE_IN v tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, VFREE_IN_def, term_ok_def]
  >- (Cases_on ‘REV_ASSOCD (Var m t) ilist (Var m t) = Var m t’ >> gvs[]
      >> drule rev_assocd_neq_mem >> rw[]
      >> first_x_assum drule >> rw[] >> gvs[])
  >- metis_tac[]
  >- metis_tac[]
  >- (gvs[dest_var_def, term_ok_def, EXISTS_MEM, MEM_FILTER]
      >> ‘∃en1 ety1 en2 ety2. e = (Var en1 ety1, Var en2 ety2)’ by metis_tac[PAIR]
      >> gvs[] >> strip_tac >> gvs[] >> first_x_assum drule >> rw[])
  >- (gvs[dest_var_def, term_ok_def, EXISTS_MEM, MEM_FILTER]
      >> ‘∃en1 ety1 en2 ety2. e = (Var en1 ety1, Var en2 ety2)’ by metis_tac[PAIR]
      >> gvs[] >> first_x_assum irule >> first_assum $ irule_at Any
      >> simp[MEM_FILTER] >> rw[] >> gvs[])
  >- (gvs[EVERY_MEM, MEM_FILTER, FORALL_PROD] >> first_x_assum irule
      >> first_x_assum $ irule_at Any >> simp[MEM_FILTER])
QED


Theorem VFREE_IN_tm_names:
  ∀tm n ty. VFREE_IN (Var n ty) tm ⇒ MEM n (tm_names tm)
Proof
  Induct_on ‘tm’ >> simp[VFREE_IN_def] >> metis_tac[]
QED

Theorem nvar_aux_never_mem:
  ∀nms n. ¬MEM (nvar_aux nms n) nms
Proof
  recInduct nvar_aux_ind >> rw[] >> simp[Once nvar_aux] >> rw[]
QED

Theorem NVARIANT_THM:
  ∀ty t n avds. ¬VFREE_IN (Var (NVARIANT n avds t) ty) t
Proof
  metis_tac[NVARIANT, VFREE_IN_tm_names, nvar_aux_never_mem, MEM_APPEND]
QED

Theorem NVARIANT_MEM:
  ∀tm n avds. ¬MEM (NVARIANT n avds tm) (tm_names tm ++ avds)
Proof
  metis_tac[nvar_aux_never_mem, NVARIANT]
QED

Theorem NVARIANT_NAMES_THM:
  ∀tm n avds. ¬MEM (NVARIANT n avds tm) (tm_names tm)
Proof
  metis_tac[NVARIANT_MEM, MEM_APPEND]
QED

Theorem NVARIANT_AVDS_THM:
  ∀tm n avds. ¬MEM (NVARIANT n avds tm) avds
Proof
  metis_tac[NVARIANT_MEM, MEM_APPEND]
QED

Theorem FVs_VFREE_in:
  ∀tm n ty.
    term_ok sig tm ⇒
    (VFREE_IN (Var n ty) tm ⇔ (n, ty) ∈ FVs tm)
Proof
  Induct_on ‘tm’ >> rw[VFREE_IN_def, FVs_def, term_ok_def]
  >> gvs[term_ok_def, FVs_def] >> metis_tac[]
QED

Theorem FVs_VFREER_in:
  ∀tm n ty.
    (n, ty) ∈ FVs tm ⇒ VFREE_IN (Var n ty) tm
Proof
  Induct_on ‘tm’ >> rw[VFREE_IN_def, FVs_def, term_ok_def]
  >> gvs[term_ok_def, FVs_def] >> strip_tac >> gvs[]
QED


Theorem sublist_map:
  ∀xs. (∀x. MEM x xs ⇒ MEM x ys) ⇒ (∀x. MEM x (MAP f xs) ⇒ MEM x (MAP f ys))
Proof
  Induct_on ‘xs’ >> rw[] >> rw[MEM_MAP_f]
QED

Theorem exists_free_in_ilist:
  ∀ilist x ty tm'.
    EXISTS (λ(s', s). VFREE_IN (Var x ty) s' ∧ VFREE_IN s tm') ilist
    ∧ (∀p. MEM p ilist ⇒ ∃n1 t1 n2 t2. p = (Var n1 t1, Var n2 t2))
    ⇒ (x, ty) ∈ BIGUNION (set (MAP (λp. FVs (FST p)) ilist))
Proof
  rw[EXISTS_MEM, MEM_MAP]
  >> first_x_assum $ drule_then assume_tac
  >> first_x_assum $ irule_at Any >> gvs[]
QED

Theorem fvs_vsubst:
  ∀tm ilist.
    term_ok sig tm
    ∧ (∀p. MEM p ilist ⇒ ∃n1 t1 n2 t2. p = (Var n1 t1, Var n2 t2))
    ⇒ FVs (VSUBST ilist tm) ⊆ FVs tm ∪ BIGUNION (set (MAP (λp. FVs (FST p)) ilist))
Proof
  Induct_on ‘tm’ >> simp[VSUBST_def, FVs_def, term_ok_def]
  >- (rpt gen_tac >> Cases_on ‘REV_ASSOCD (Var m t) ilist (Var m t) = Var m t’
      >- simp[FVs_def]
      >- (drule rev_assocd_neq_mem >> simp[Once MEM_SPLIT_APPEND_first]
          >> rw[] >> qabbrev_tac ‘V = REV_ASSOCD (Var m t) ilist (Var m t)’
          >> rw[] >> SET_TAC[]))
  >- ASM_SET_TAC[]
  >> rw[AllCaseEqs(), PULL_EXISTS]
  >> gvs[]
  >> qabbrev_tac ‘nv = VARIANT (VSUBST (FILTER (λ(s',s). s ≠ Var x ty) ilist)
                                       tm') (explode x) ty’
  >> qabbrev_tac ‘ilist' = FILTER (λ(s',s). s ≠ Var x ty) ilist’
  >> qabbrev_tac ‘subst_tm = VSUBST ((Var nv ty,Var x ty)::ilist') tm'’
  >> first_assum $ qspec_then ‘(Var nv ty, Var x ty)::ilist'’ assume_tac
  >> ‘∀p. p = (Var nv ty,Var x ty) ∨ MEM p ilist'
          ⇒ ∃n1 t1 n2 t2. p = (Var n1 t1,Var n2 t2)’
    by metis_tac[MEM_FILTER, Abbr‘ilist'’]
  >> gvs[]
  >> first_x_assum drule >> rw[]
  >> ‘∀p. MEM p (MAP (λp. FVs (FST p)) ilist')
          ⇒ MEM p (MAP (λp. FVs (FST p)) ilist)’
    by metis_tac[MEM_FILTER, sublist_map]
  >> ‘BIGUNION (set (MAP (λp. FVs (FST p)) ilist'))
      ⊆ BIGUNION (set (MAP (λp. FVs (FST p)) ilist))’
    by ASM_SET_TAC[SUBSET_BIGUNION]
  >> qabbrev_tac ‘target_vars = BIGUNION (set (MAP (λp. FVs (FST p)) ilist))’
  >> qabbrev_tac ‘target_vars' = BIGUNION (set (MAP (λp. FVs (FST p)) ilist'))’
  >> ‘∀p. MEM p ilist' ⇒ ∃n1 t1 n2 t2. p = (Var n1 t1,Var n2 t2)’ by metis_tac[]
  >- (Cases_on ‘(x, ty) ∈ target_vars’
      >- ASM_SET_TAC[]
      >> drule_all exists_free_in_ilist
      >> strip_tac
      >> ASM_SET_TAC[])
  >> ASM_SET_TAC[]
QED

Theorem variant_name_self:
  ∀tm x ty.
    ¬VFREE_IN (Var x ty) tm
    ⇔ VARIANT tm (explode x) ty = x
Proof
  rw[VARIANT_def, EQ_IMP_THM]
  >> qspecl_then [‘tm’, ‘explode x’, ‘ty’] assume_tac VARIANT_PRIMES_def >> gvs[]
  >> first_x_assum $ qspec_then ‘0’ assume_tac >> gvs[]
QED

Theorem rev_assocd_default_cases:
  ∀x l d. REV_ASSOCD x l d = d ⇒ MEM (d, x) l ∨ ¬∃y. MEM (y, x) l
Proof
  Induct_on ‘l’ >> rw[REV_ASSOCD_def] >> Cases_on ‘h’ >> gvs[]
QED

Theorem NVARIANT_esubst_ty0:
  ∀tm subst_tm n ty avds.
    (∀n. MEM n (tm_names tm) ⇒ MEM n (tm_names subst_tm))
    ∧ term_ok sig tm
    ⇒ ¬VFREE_IN (Var (NVARIANT n avds subst_tm) ty) tm
Proof
  rw[]
  >> qspecl_then [‘subst_tm’, ‘n’, ‘avds’] assume_tac NVARIANT_NAMES_THM
  (*>> first_x_assum $ CONV_TAC CONTRAPOS_CONV*)
  >> ‘¬MEM (NVARIANT n avds subst_tm) (tm_names tm)’ by metis_tac[]
  >> ‘∀tm n ty. ¬MEM n (tm_names tm) ⇒ ¬VFREE_IN (Var n ty) tm’ suffices_by metis_tac[]
  >> rw[]
  >> Induct_on ‘tm'’
  >> rw[VFREE_IN_def, tm_names_def]
QED

Theorem NVARIANT_esubst_ty0_alt:
  ∀tm subst_tm n ty avds.
    (∀n. MEM n (tm_names tm) ⇒ MEM n (tm_names subst_tm))
    ∧ term_ok sig tm
    ⇒ (NVARIANT n avds subst_tm, ty) ∉ FVs tm
Proof
  metis_tac[NVARIANT_esubst_ty0, FVs_VFREE_in]
QED

fun rC q = rename [q] >> Cases_on q >> simp[]

Theorem rev_assocd_different_default:
  ∀l k d1 d2.
    REV_ASSOCD k l d1 = d1
    ∧ REV_ASSOCD k l d2 = d2
    ∧ d1 ≠ d2
    ⇒ ∀v. ¬MEM (v, k) l
Proof
  Induct_on ‘l’ >> rw[]
  >> rename [‘h::t’] >> Cases_on ‘h’
  >> gvs[REV_ASSOCD_def, AllCaseEqs()]
  >> first_x_assum drule_all
  >> rpt strip_tac
  >> gvs[]
QED

Theorem REV_ASSOCD_EQ_DEFAULT_i = REV_ASSOCD_NEQ_DEFAULT
                                    |> CONV_RULE CONTRAPOS_CONV |> SRULE[]

Theorem VSUBST_NOT_FREE:
  ∀tm ilist.
    term_ok sig tm ∧
    (∀v k. MEM (v, k) ilist ⇒ ∃n ty. k = Var n ty ∧ (n, ty) ∉ FVs tm) ⇒
    VSUBST ilist tm = tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, term_ok_def]
  >- (irule REV_ASSOCD_EQ_DEFAULT_i >> metis_tac[TypeBase.one_one_of “:term”])
  >- metis_tac[]
  >- metis_tac[]
  >> gvs[]
  >- (gvs[EXISTS_MEM, MEM_FILTER, FVs_VFREE_in, SF SFY_ss]
      >> Cases_on ‘e’ >> gvs[] >> rename [‘MEM (v, k) ilist’]
      >> first_assum drule >> rw[]
      >> gvs[FVs_VFREE_in, SF SFY_ss])
  >> first_x_assum irule
  >> simp[MEM_FILTER]
  >> metis_tac[]
QED

Theorem free_names_comb[simp]:
  ∀t1 t2. free_names (Comb t1 t2) = free_names t1 ∪ free_names t2
Proof
  simp[free_names] >> SET_TAC[]
QED


Theorem alist_to_fm_FILTER:
  ∀ilist k.
    alist_to_fm (FILTER (λ(s',s). s ≠ k) ilist) = alist_to_fm ilist \\ k
Proof
  Induct_on ‘ilist’ >> simp[FORALL_PROD]
  >> rw[] >> simp[DOMSUB_FUPDATE_NEQ]
QED


Theorem FLOOKUP_alist_to_fm_NONE:
  ∀ilist k. FLOOKUP (alist_to_fm ilist) k = NONE ⇒ REV_ASSOCD k ilist d = d
Proof
  Induct_on ‘ilist’
  >> simp[alist_to_fm_def, REV_ASSOCD_def, FORALL_PROD, FLOOKUP_SIMP, AllCaseEqs()]
QED

Theorem ALL_DISTINCT_MAP_SND:
  ∀ilist v k.
    ALL_DISTINCT (MAP SND ilist) ∧
    MEM (v, k) ilist ⇒
    FLOOKUP (alist_to_fm ilist) k = SOME v
Proof
  Induct_on ‘ilist’ >> simp[FORALL_PROD, MEM_MAP]
  >> rw[FLOOKUP_SIMP]
  >- metis_tac[]
QED

Theorem FLOOKUP_alist_to_fm_MEM:
  ∀ilist v k.
    FLOOKUP (alist_to_fm ilist) k = SOME v ⇒
    MEM (v, k) ilist
Proof
  Induct_on ‘ilist’ >> simp[FORALL_PROD, MEM_MAP, FLOOKUP_SIMP] >> rw[]
QED

Theorem VSUBST_VSUBSTfm:
  ∀tm ilist.
    ALL_DISTINCT (MAP SND ilist) ∧
    term_ok sig tm ⇒
    VSUBST ilist tm = VSUBSTfm (alist_to_fm ilist) tm
Proof
  Induct_on ‘tm’ >> simp[VSUBST_def, VSUBSTfm, term_ok_def]
  >- (simp[AllCaseEqs(), FLOOKUP_alist_to_fm_NONE, SF CONJ_ss]
      >> rw[] >> Cases_on ‘FLOOKUP (alist_to_fm ilist) (Var m t)’ >> rw[]
      >> Induct_on ‘ilist’
      >> simp[alist_to_fm_def, REV_ASSOCD_def, FORALL_PROD, FLOOKUP_SIMP, AllCaseEqs()]
      >> metis_tac[])
  >> gvs[MEM_FILTER, EXISTS_MEM, EXISTS_PROD, PULL_EXISTS, alist_to_fm_FILTER,
                     FILTER_ALL_DISTINCT, MAP_SND_FILTER_NEQ]
  >> simp[DOMSUB_FLOOKUP_THM] >> rw[] >> gvs[]
  >- (drule_all_then assume_tac ALL_DISTINCT_MAP_SND
      >> first_x_assum drule >> simp[] >> metis_tac[])
  >- (drule_all_then assume_tac ALL_DISTINCT_MAP_SND
      >> first_x_assum drule >> simp[] >> metis_tac[])
  >> drule_then assume_tac FLOOKUP_alist_to_fm_MEM
  >> first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem exists_free_in_fm_map:
  ∀tm fm x ty.
    term_ok sig tm ∧
    (∃k v. FLOOKUP fm k = SOME v ∧ VFREE_IN (Var x ty) v ∧ VFREE_IN k tm) ∧
    (∀v. v ∈ FRANGE fm ⇒ ∃n ty. v = Var n ty) ∧
    (∀v. v ∈ FDOM fm ⇒ ∃n ty. v = Var n ty) ⇒
    (x, ty) ∈ BIGUNION { FVs t | ∃n ty'. (n, ty') ∈ FVs tm ∧ FLOOKUP fm (Var n ty') = SOME t }
Proof
  rw[FDOM_FLOOKUP, FRANGE_FLOOKUP]
  >> first_x_assum $ qspec_then ‘k’ assume_tac
  >> first_x_assum $ qspec_then ‘v’ assume_tac
  >> gvs[PULL_EXISTS]
  >> first_x_assum $ qspec_then ‘Var n ty'’ assume_tac
  >> rw[]
  >> qexists ‘Var x ty’
  >> rw[FVs_def]
  >> qexistsl [‘n’, ‘ty'’]
  >> rw[FVs_def, FVs_VFREE_in]
  >> metis_tac[FVs_VFREE_in, VFREE_IN_def]
QED

Theorem FLOOKUP_FUPDATE:
  FLOOKUP (fm |+ (k, v)) k1 =
  if k1 = k then SOME v
  else FLOOKUP fm k1
Proof
  rw[FLOOKUP_SIMP]
QED

Theorem FVs_VSUBSTfm_in_FVs_DOMSUB:
  (∀fm'.
     (∀v. v ∈ FRANGE fm' ⇒ ∃n ty. v = Var n ty) ∧
     (∀v. v ∈ FDOM  fm' ⇒ ∃n ty. v = Var n ty) ⇒
     ∀x'.
       x' ∈ FVs (VSUBSTfm fm' (Var x ty)) ⇔
       x' ∈ (if Var x ty ∈ FDOM fm' then ∅ else {(x,ty)}) ∨
       ∃s t.
         x' ∈ s ∧ (∀u. u ∈ s ⇔ u ∈ FVs t) ∧
         FLOOKUP fm' (Var x ty) = SOME t) ∧

  (∀fm'.
     (∀v. v ∈ FRANGE fm' ⇒ ∃n ty. v = Var n ty) ∧
     (∀v. v ∈ FDOM  fm' ⇒ ∃n ty. v = Var n ty) ⇒
     ∀x. x ∈ FVs (VSUBSTfm fm' tm') ⇔
         x ∈ FVs tm' ∧ (∀n ty'. x ≠ (n,ty') ∨ Var n ty' ∉ FDOM fm') ∨
         ∃s t n ty'.
           x ∈ s ∧ (∀u. u ∈ s ⇔ u ∈ FVs t) ∧ (n,ty') ∈ FVs tm' ∧
           FLOOKUP fm' (Var n ty') = SOME t) ∧

  (∀k w.
     FLOOKUP (fm \\ Var x ty) k ≠ SOME w ∨ ¬VFREE_IN (Var x ty) w ∨
     ¬VFREE_IN k tm') ∧

  type_ok (tysof sig) ty ∧ term_ok sig tm' ∧
  (∀v. v ∈ FRANGE fm ⇒ ∃n ty. v = Var n ty) ∧
  (∀v. v ∈ FDOM  fm ⇒ ∃n ty. v = Var n ty) ∧
  (∀u. u ∈ s ⇔ u = (n',ty'')) ∧
  (n,ty') ∈ FVs tm' ∧ ty' ≠ ty ∧
  FLOOKUP fm (Var n ty') = SOME (Var n' ty'')
  ⇒
  (n',ty'') ∈ FVs (VSUBSTfm (fm \\ Var x ty) tm')
Proof
  rw[]
  >> qspecl_then [‘Var x ty’, ‘fm’, ‘λp. ∃n ty. p = Var n ty’]
                 assume_tac (GEN_ALL IN_FRANGE_DOMSUB_suff) >> gvs[]
  >> ‘∀v. v ∈ FDOM  (fm \\ Var x ty) ⇒ ∃n ty. v = Var n ty’ by simp[]
  >> first_x_assum $ drule_all >> rw[]
  >> Cases_on ‘(n',ty'') ∈ FVs tm' ∧ (Var n' ty'' ∉ FDOM fm ∨ n' = x ∧ ty'' = ty)’
  >> rw[]
  >> qexistsl [‘s’, ‘Var n' ty''’, ‘n’, ‘ty'’] >> rw[FVs_def]
  >> Cases_on ‘n = x’ >> rw[]
  >- (Cases_on ‘ty = ty'’ >- gvs[]
      >> ‘Var n ty ≠ Var n ty'’ by simp[]
      >> drule_then (qspec_then ‘fm’ assume_tac) DOMSUB_FLOOKUP_NEQ
      >> simp[])
  >> ‘Var x ty ≠ Var n ty'’ by simp[]
  >> drule_then (qspec_then ‘fm’ assume_tac) DOMSUB_FLOOKUP_NEQ
  >> simp[]
QED

Theorem VSUBSTfm_FVs:
  ∀tm fm.
    term_ok sig tm ∧
    (∀v. v ∈ FRANGE fm ⇒ ∃n ty. v = Var n ty) ∧
    (∀v. v ∈ FDOM fm ⇒ ∃n ty. v = Var n ty) ⇒
    FVs (VSUBSTfm fm tm) =
    (FVs tm DIFF { (n, ty) | Var n ty ∈ FDOM fm })
    ∪ BIGUNION { FVs t | ∃n ty. (n, ty) ∈ FVs tm ∧ FLOOKUP fm (Var n ty) = SOME t }
Proof
  Induct_on ‘tm’ >> simp[VSUBSTfm, FVs_def, term_ok_def]
  >- (rpt gen_tac
      >> Cases_on ‘FLOOKUP fm (Var m t)’
      >> gvs[FDOM_FLOOKUP]
      >> SET_TAC[])
  >- SET_TAC[]
  >> rw[] >> gvs[term_ok_def]
  >- (qabbrev_tac ‘Xv = VARIANT (VSUBSTfm (fm \\ Var x ty) tm') (explode x) ty’
      >> first_assum $ qspec_then ‘fm |+ (Var x ty,Var Xv ty)’ assume_tac
      >> qspecl_then [‘Var x ty’, ‘fm’, ‘λp. ∃n ty. p = Var n ty’]
                     assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
      >> gvs[PULL_EXISTS, FORALL_AND_THM, DISJ_IMP_THM, EXTENSION, FLOOKUP_SIMP,
             DIFF_UNION, FRANGE_DOMSUB_SUBSET] >> rw[]
      >> Cases_on ‘x' = (x, ty)’ >> rw[]
      >- (iff_tac >> rw[]
          >- (qexistsl [‘s’, ‘t’] >> rw[]
              >> Cases_on ‘x = n ∧ ty = ty'’ >> rw[] >> gvs[]
              >> metis_tac[])
          >- (qexistsl [‘s’, ‘t’] >> rw[]
              >> Cases_on ‘x = n ∧ ty = ty'’ >> rw[] >> gvs[]
              >> metis_tac[])
          >> strip_tac >> gvs[Abbr‘Xv’]
          >> Cases_on ‘(x, ty) ∈ FVs (VSUBSTfm (fm \\ Var x ty) tm')’
          >- (drule FVs_VFREER_in >> rw[]
              >> irule $ iffRL variant_name_self >> simp[])
          >> ‘(∀v. v ∈ FDOM (fm \\ Var x ty) ⇒ ∃n ty. v = Var n ty)’
            by simp[] >> gvs[]
          >> first_x_assum $ drule_then (qspec_then ‘(x, ty)’ assume_tac)
          >> first_x_assum $ qspecl_then [‘s’, ‘t’, ‘n’, ‘ty'’] assume_tac
          >> ‘Var x ty ≠ Var n ty'’ by simp[]
          >> metis_tac[DOMSUB_FLOOKUP_NEQ])
      >> iff_tac >> rw[] >> gvs[]
      >- (Cases_on ‘x' ∈ FVs tm' ∧
                    (∀n ty'. x' = (n,ty') ⇒ Var n ty' ∉ FDOM fm)’
          >> gvs[] >> rw[]
          >> qexistsl [‘s’, ‘t’] >> rw[]
          >> Cases_on ‘n = x ∧ ty = ty'’ >> rw[] >> gvs[]
          >> metis_tac[])
      >- (strip_tac >> gvs[]
          >> ‘(∀v. v ∈ FDOM (fm \\ Var x ty) ⇒ ∃n ty. v = Var n ty)’
            by simp[]
          >> first_x_assum $ drule_all_then (qspec_then ‘(Xv, ty)’ assume_tac)
          >> gvs[] >> metis_tac[VARIANT_THM, FVs_VFREER_in])
      >- (Cases_on ‘x' ∈ FVs tm' ∧
                    (∀n ty'. x' = (n,ty') ⇒ Var n ty' ∉ FDOM fm)’
          >> gvs[] >> rw[]
          >> qexistsl [‘s’, ‘t’] >> rw[]
          >> Cases_on ‘n = x ∧ ty = ty'’ >> rw[] >> gvs[]
          >> metis_tac[])
      >> strip_tac >> gvs[]
      >> ‘(∀v. v ∈ FDOM (fm \\ Var x ty) ⇒ ∃n ty. v = Var n ty)’
        by simp[]
      >> first_x_assum $ drule_all_then (qspec_then ‘(Xv, ty)’ assume_tac)
      >> gvs[]
      >> ‘FLOOKUP (fm \\ Var x ty) (Var n ty') = SOME t’
        by simp[DOMSUB_FLOOKUP_NEQ]
      >> ‘(Xv, ty) ∈ s’ by simp[]
      >> ‘(Xv,ty) ∈ FVs (VSUBSTfm (fm \\ Var x ty) tm')’ by metis_tac[]
      >> metis_tac[VARIANT_THM, FVs_VFREER_in])
  >> gvs[PULL_EXISTS, FORALL_AND_THM, DISJ_IMP_THM, EXTENSION, FLOOKUP_SIMP,
         DIFF_UNION] >> rw[]
  >> iff_tac >> gvs[] >> rw[]
  >- (first_x_assum $ qspec_then ‘fm \\ Var x ty’ assume_tac >> gvs[]
      >> qspecl_then [‘Var x ty’, ‘fm’, ‘λp. ∃n ty. p = Var n ty’]
                     assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
      >> gvs[]
      >- metis_tac[]
      >> Cases_on ‘x' ∈ FVs tm' ∧ (∀n ty'. x' = (n,ty') ⇒ Var n ty' ∉ FDOM fm)’
      >> gvs[FDOM_FLOOKUP]
      >> qexistsl [‘s’, ‘t’, ‘n’, ‘ty'’] >> gvs[] >> rw[]
      >- (strip_tac >> qpat_x_assum ‘ty' = ty’ SUBST_ALL_TAC
          >> gvs[FLOOKUP_SIMP])
      >- gvs[DOMSUB_FLOOKUP_THM]
      >- (strip_tac >> qpat_x_assum ‘ty' = ty’ SUBST_ALL_TAC
          >> gvs[FLOOKUP_SIMP])
      >- gvs[DOMSUB_FLOOKUP_THM])
  >- (first_x_assum $ qspec_then ‘fm \\ Var x ty’ assume_tac >> gvs[]
      >> qspecl_then [‘Var x ty’, ‘fm’, ‘λp. ∃n ty. p = Var n ty’]
                     assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
      >> gvs[])
  >> gvs[]
  >- (first_x_assum $ qspec_then ‘fm \\ Var x ty’ assume_tac >> gvs[]
      >> qspecl_then [‘Var x ty’, ‘fm’, ‘λp. ∃n ty. p = Var n ty’]
                     assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
      >> gvs[]
      >> disj2_tac
      >> qexistsl [‘s’, ‘t’, ‘n’, ‘ty'’]
      >> ‘Var n ty' ≠ Var x ty’ by simp[]
      >> metis_tac[DOMSUB_FLOOKUP_THM])
  >> ‘t ∈ FRANGE fm’ by metis_tac[IN_FRANGE_FLOOKUP]
  >> first_assum dxrule >> rw[]
  >> PairCases_on ‘x'’ >> rw[]
  >> gvs[FVs_def]
  >> ‘Var n ty' ≠ Var n' ty’ by simp[]
  >> ‘FLOOKUP (fm \\ Var n' ty) (Var n ty') = SOME (Var n' ty'')’
    by metis_tac[DOMSUB_FLOOKUP_NEQ]
  >> first_x_assum drule
  >> rw[] >> strip_tac
  >> gvs[]
  >> metis_tac[FVs_VFREE_in]
QED

Theorem FVs_VSUBST_CASES:
  ∀tm x ty1 a b ty.
    term_ok sig tm ⇒
    ((x, ty1) ∈ FVs (VSUBST [(Var a ty, Var b ty)] tm) ⇔
       (x = a ∧ ty1 = ty ∧ (b, ty) ∈ FVs tm) ∨
       ((x, ty1) ∈ FVs tm ∧ (x ≠ b ∨ ty1 ≠ ty)))
Proof
  simp[VSUBST_VSUBSTfm, SF SFY_ss, VSUBSTfm_FVs, PULL_EXISTS, FLOOKUP_SIMP]
  >> metis_tac[]
QED

Theorem FVs_VSUBST_PRESERVED_VAR:
  ∀tm n n1 n2 ty ty1.
    term_ok sig tm ∧
    (n, ty) ∈ FVs tm ∧
    ty ≠ ty1 ⇒
    (n, ty) ∈ FVs (VSUBST [(Var n2 ty1, Var n1 ty1)] tm)
Proof
  metis_tac[FVs_VSUBST_CASES]
QED

Theorem FVs_VSUBST_SUBSTITUTED_VAR:
  ∀tm n oldN ty.
    term_ok sig tm ∧
    (n, ty) ∈ FVs tm ⇒
    (n, ty) ∈ FVs (VSUBST [(Var n ty, Var oldN ty)] tm)
Proof
  metis_tac[FVs_VSUBST_CASES]
QED

Theorem FVs_in_tm_names:
  ∀tm n ty. (n, ty) ∈ FVs tm ⇒ MEM n (tm_names tm)
Proof
  Induct_on ‘tm’ >> rw[FVs_def, tm_names_def]
  >> rpt $ first_x_assum drule >> simp[]
QED

Theorem tm_names_vsubst:
  ∀tm n m ty1 ty2.
    term_ok sig tm ∧
    (n, ty1) ∈ FVs tm ∧
    ty1 ≠ ty2 ∧
    MEM n (tm_names tm) ⇒
    MEM n (tm_names (VSUBST [(Var m ty2, Var n ty2)] tm))
Proof
  rw[]
  >> ‘ALL_DISTINCT (MAP SND [(Var m ty2, Var n ty2)])’ by simp[]
  >> dxrule_then drule VSUBST_VSUBSTfm >> rw[]
  >> ‘(n, ty1) ∈ FVs (VSUBSTfm (FEMPTY |+ (Var n ty2,Var m ty2)) tm)’
    suffices_by metis_tac[FVs_in_tm_names]
  >> qspecl_then [‘tm’, ‘FEMPTY |+ (Var n ty2, Var m ty2)’]
                 assume_tac VSUBSTfm_FVs >> gvs[]
QED

Theorem alist_to_fm_FDOM_MEM:
  ∀k ilist.
    k ∈ FDOM (alist_to_fm ilist) ⇒
    ∃v. MEM (v, k) ilist
Proof
  Induct_on ‘ilist’ >> rw[]
  >> PairCases_on ‘h’ >> gvs[]
  >> metis_tac[]
QED

Theorem alist_to_fm_FRANGE_MEM:
  ∀v ilist.
    v ∈ FRANGE (alist_to_fm ilist) ⇒
    ∃k. MEM (v, k) ilist
Proof
  Induct_on ‘ilist’ >> rw[]
  >> PairCases_on ‘h’ >> gvs[]
  >- metis_tac[]
  >> Cases_on ‘v ∈ FRANGE (alist_to_fm ilist)’ >> gvs[]
  >> metis_tac[SUBSET_DEF, FRANGE_DOMSUB_SUBSET]
QED

Theorem FLOOKUP_fm_DOMSUB_FUPDATE:
  ∀fm k v k1 v1.
    FLOOKUP (fm \\ k1) k = SOME v ⇒
    FLOOKUP (fm |+ (k1, v1)) k = SOME v
Proof
  rw[] >> Cases_on ‘k1 = k’ >> gvs[FLOOKUP_SIMP]
  >> drule DOMSUB_FLOOKUP_NEQ >> rw[] >> gvs[]
QED

Theorem tm_names_VSUBSTfm_fupdate:
  ∀fm tm' n nV ty k w.
    n ≠ nV ∧
    type_ok (tysof sig) ty ∧
    term_ok sig tm' ∧
    (∀v. v ∈ FDOM fm ⇒ ∃x ty. v = Var x ty ∧ x ≠ n) ∧
    (∀v. v ∈ FRANGE fm ⇒ ∃n ty. v = Var n ty) ∧
    (∀v. v ∈ FRANGE fm ⇒ term_ok sig v) ∧
    FLOOKUP (fm \\ Var n ty) k = SOME w ∧
    VFREE_IN (Var n ty) w ∧
    VFREE_IN k tm' ⇒
    MEM n (tm_names (VSUBSTfm (fm |+ (Var n ty,Var nV ty)) tm'))
Proof
  rw[]
  >> irule FVs_in_tm_names
  >> qspecl_then [‘tm'’, ‘fm |+ (Var n ty, Var nV ty)’]
                 assume_tac VSUBSTfm_FVs
  >> gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS]
  >> qspecl_then [‘Var n ty’, ‘fm’, ‘λp. ∃n ty. p = Var n ty’]
                 assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
  >> ‘∀v. v ∈ FDOM fm ⇒ ∃n ty. v = Var n ty’ by metis_tac[FORALL_AND_THM]
  >> gvs[]
  >> rw[]
  >> ‘FLOOKUP (fm |+ (Var n ty, Var nV ty)) k = SOME w’
    by metis_tac[FLOOKUP_fm_DOMSUB_FUPDATE]
  >> ‘k ∈ FDOM (fm \\ Var n ty)’ by simp[FDOM_FLOOKUP]
  >> ‘FDOM (fm \\ Var n ty) ⊆ FDOM fm’
    by metis_tac[SUBMAP_FDOM_SUBSET, SUBMAP_DOMSUB]
  >> ‘k ∈ FDOM (fm \\ Var n ty)’ by metis_tac[FDOM_FLOOKUP]
  >> ‘k ∈ FDOM fm’ by metis_tac[SUBSET_DEF]
  >> first_x_assum drule >> gvs[] >> rw[]
  >> drule_then (drule o iffLR) FVs_VFREE_in >> rw[]
  >> qexists ‘ty’ >> rw[]
  >> qexists ‘FVs w’ >> rw[]
  >> qspecl_then [‘Var n ty’, ‘fm’, ‘λp. term_ok sig p’]
                 assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
  >> gvs[]
  >> ‘w ∈ FRANGE (fm \\ Var n ty)’ by metis_tac[IN_FRANGE_FLOOKUP]
  >> first_x_assum drule >> rw[]
  >> metis_tac[FVs_VFREE_in]
QED

Theorem tm_names_vsubstfm_different_name:
  ∀tm fm n.
    term_ok sig tm ∧
    (∀v. v ∈ FDOM fm ⇒ ∃x ty. v = Var x ty ∧ x ≠ n) ∧
    (∀v. v ∈ FRANGE fm ⇒ ∃n ty. v = Var n ty) ∧
    (∀v. v ∈ FRANGE fm ⇒ term_ok sig v) ∧
    MEM n (tm_names tm) ⇒
    MEM n (tm_names (VSUBSTfm fm tm))
Proof
  Induct_on ‘tm’ >> rw[VSUBSTfm]
  >- (rC ‘FLOOKUP fm (Var m t)’
      >> ‘Var m t ∈ FDOM fm’ by metis_tac[FDOM_FLOOKUP]
      >> first_x_assum drule >> gvs[])
  >> gvs[term_ok_def]
  >- (qabbrev_tac ‘nV = VARIANT (VSUBSTfm (fm \\ Var n ty) tm')
                                   (explode n) ty’
      >> Cases_on ‘n = nV’ >> rw[]
      >> metis_tac[tm_names_VSUBSTfm_fupdate])
  >- (qabbrev_tac ‘nV = VARIANT (VSUBSTfm (fm \\ Var x ty) tm') (explode x) ty’
      >> Cases_on ‘x = n’
      >> Cases_on ‘n = nV’ >> gvs[]
      >- metis_tac[tm_names_VSUBSTfm_fupdate]
      >> first_x_assum irule
      >> rw[term_ok_def] >> gvs[term_ok_def]
      >> first_x_assum irule
      >> metis_tac[FRANGE_DOMSUB_SUBSET, SUBSET_DEF])
  >> qspecl_then [‘Var x ty’, ‘fm’, ‘λp. ∃n ty. p = Var n ty’]
                 assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
  >> qspecl_then [‘Var x ty’, ‘fm’, ‘λp. term_ok sig p’]
                 assume_tac $ GEN_ALL IN_FRANGE_DOMSUB_suff
  >> gvs[term_ok_def]
QED

Theorem tm_names_vsubst_different_name:
  ∀tm ilist n.
    term_ok sig tm ∧
    (∀v. MEM v ilist ⇒ ∃x1 x2 ty. v = (Var x1 ty, Var x2 ty) ∧
                                  n ≠ x2 ∧ term_ok sig (Var x1 ty)) ∧
    ALL_DISTINCT (MAP SND ilist) ∧
    MEM n (tm_names tm) ⇒
    MEM n (tm_names (VSUBST ilist tm))
Proof
  rw[] >> drule_all VSUBST_VSUBSTfm >> gvs[] >> rw[]
  >> irule tm_names_vsubstfm_different_name >> rw[]
  >- (drule alist_to_fm_FDOM_MEM >> rw[]
      >> first_x_assum drule >> rw[])
  >- (drule alist_to_fm_FRANGE_MEM >> rw[]
      >> first_x_assum drule >> rw[])
  >> first_x_assum $ irule_at Any
  >> rw[term_ok_def]
  >> drule alist_to_fm_FRANGE_MEM >> rw[]
  >> first_x_assum drule >> rw[] >> gvs[term_ok_def]
QED


Theorem has_type_comb:
  Comb t1 t2 has_type ty ⇔
    ∃dty. t1 has_type Fun dty ty ∧
          t2 has_type dty
Proof
  simp[Once has_type_cases]
QED

Theorem has_type_typeof:
  ∀a b.
    a has_type b ⇒ typeof a = b
Proof
  Induct_on ‘$has_type’ >> rw[]
QED

Theorem ty_esubst_fun[simp]:
  esubsts_ok sig σ ⇒
  ty_esubst σ (Fun ty1 ty2) = Fun (ty_esubst σ ty1) (ty_esubst σ ty2)
Proof
  Cases_on ‘σ’ >> rw[esubsts_ok_def, ty_esubst_def]
QED

Theorem codomain_ty_esubst:
  ∀tm.
    esubsts_ok sig σ ∧
    tm has_type Fun dty ty ⇒
    codomain (ty_esubst σ (typeof tm)) = ty_esubst σ (codomain (typeof tm))
Proof
  rw[] >> drule has_type_typeof
  >> metis_tac[codomain_def, ty_esubst_fun]
QED

Theorem typeof_vsubst:
  ∀tm ilist.
    term_ok sig tm ∧
    (∀v1 v2. MEM (v1, v2) ilist ⇒ ∃n1 n2 ty. v1 = Var n1 ty ∧ v2 = Var n2 ty) ⇒
    typeof (VSUBST ilist tm) = typeof tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, term_ok_def]
  >- (qspecl_then [‘ilist’, ‘Var m t’, ‘Var m t’] strip_assume_tac REV_ASSOCD_MEM
      >- (first_x_assum drule >> simp[PULL_EXISTS])
      >> simp[])
  >- (gvs[] >> first_x_assum irule >> rw[MEM_FILTER] >> first_x_assum drule >> rw[])
  >> first_x_assum irule >> rw[MEM_FILTER]
QED

Theorem VFREE_IN_VSUBST_OUT:
  ∀tm ilist.
    term_ok sig tm ∧
    (∀v1 v2. MEM (v1, v2) ilist ⇒ ∃n1 n2 ty. v1 = Var n1 ty ∧ v2 = Var n2 ty) ∧
    (∃vin. MEM (vin, Var n ty) ilist) ∧
    (∀vout vin. MEM (vin, vout) ilist ⇒ vin ≠ Var n ty) ⇒
    ¬VFREE_IN (Var n ty) (VSUBST ilist tm)
Proof
  Induct_on ‘tm’
  >> rw[VFREE_IN_def, VSUBST_def] >> gvs[term_ok_def]
  >- (Cases_on ‘REV_ASSOCD (Var m t) ilist (Var m t) = Var m t’
      >> rw[]
      >- (drule rev_assocd_default_cases >> rw[]
          >> metis_tac[])
      >> qspecl_then [‘ilist’, ‘Var m t’, ‘Var m t’] mp_tac REV_ASSOCD_MEM
      >> rw[] >> first_x_assum drule >> rw[] >> gvs[] >> rw[]
      >> metis_tac[])
  >- (first_x_assum irule >> gvs[term_ok_def, SF SFY_ss])
  >- (first_x_assum irule >> gvs[term_ok_def, SF SFY_ss])
  >- (gvs[] >> strip_d1 >> first_x_assum irule >> rw[MEM_FILTER]
      >> metis_tac[])
  >> strip_d1 >> gvs[]
  >> first_x_assum irule
  >> simp[MEM_FILTER] >> metis_tac[]
QED

Theorem VSUBST_ID:
  ∀tm ilist.
    term_ok sig tm ∧
    (∀v1 v2. MEM (v1, v2) ilist ⇒ v1 = v2 ∧ ∃n ty. v1 = Var n ty) ⇒
    VSUBST ilist tm = tm
Proof
  Induct_on ‘tm’ >> rw[]
  >- metis_tac[VSUBST_def, REV_ASSOCD_MEM]
  >- rw[VSUBST_def]
  >- (gvs[EXISTS_MEM, EXISTS_PROD, term_ok_def]
      >> rpt $ first_x_assum drule
      >> rw[VSUBST_def])
  >> rw[VSUBST_def, MEM_FILTER, term_ok_def]
  >> gvs[VSUBST_def, MEM_FILTER, VFREE_IN_def, EXISTS_MEM, EXISTS_PROD,
         EVERY_MEM, FORALL_PROD, term_ok_def]
  >> metis_tac[VFREE_IN_def, MEM_FILTER]
QED

Theorem esubst_ty0_impossible1:
  ∀env σ avds tm.
    esubsts_ok sig σ ∧
    (∀k v. MEM (v, k) env ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    term_ok sig tm ⇒
    (∀e. esubst_ty0 env σ avds tm = error e ⇒
       ∃n typ1 typ2.
         (n, typ1) ∈ FVs tm ∧
         ty_esubst σ typ1 = ty_esubst σ typ2 ∧
         typ1 ≠ typ2 ∧
         REV_ASSOCD (Var n (ty_esubst σ typ1)) env (Var n typ1) = Var n typ2 ∧
         e = Var n (ty_esubst σ typ1)) ∧
    (∀n typ1 typ2.
       (n, typ1) ∈ FVs tm ∧
       ty_esubst σ typ1 = ty_esubst σ typ2 ∧
       typ1 ≠ typ2 ∧
       REV_ASSOCD (Var n (ty_esubst σ typ1)) env (Var n typ1) = Var n typ2
       ⇒ ∃e. esubst_ty0 env σ avds tm = error e) ∧
    (∀subst_tm. esubst_ty0 env σ avds tm = return subst_tm ⇒
                typeof subst_tm = ty_esubst σ (typeof tm) ∧
                (∀n. MEM n (tm_names tm) ⇒ MEM n (tm_names subst_tm)))
Proof
  recInduct esubst_ty0_ind >> REWRITE_TAC[esubst_ty0_def] >> rpt strip_tac
  >- (gvs[AllCaseEqs()]
      >> drule rev_assocd_neq_mem >> rw[]
      >> first_x_assum drule >> rw[]
      >> metis_tac[])
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- gvs[LET_THM, AllCaseEqs()]
  >- (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
      >> metis_tac[TypeBase.nchotomy_of “:(α, β) error”])
  >- (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
      >> metis_tac[TypeBase.nchotomy_of “:(α, β) error”])
  >- (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
      >> metis_tac[TypeBase.nchotomy_of “:(α, β) error”])
  >- (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs(),
          welltyped_def, has_type_comb, ty_esubst_def]
      >> metis_tac[codomain_ty_esubst])
  >- gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()]
  >- (with_flag (Cond_rewr.stack_limit, 0)
                (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()])
      >- (gvs[DISJ_IMP_THM, FORALL_AND_THM, REV_ASSOCD_def, AllCaseEqs()]
          >> first_assum $ irule_at (Pat ‘_ ∈ FVs body’)
          >> simp[] >> rpt strip_tac >> gvs[])
      >- gvs[REV_ASSOCD_def]
      >> gvs[DISJ_IMP_THM, FORALL_AND_THM, REV_ASSOCD_def, AllCaseEqs(), neq_error]
      >> gvs[term_ok_vsubst_variant]
      >> last_x_assum $ qspec_then ‘body1’ assume_tac
      >> gvs[]
      >> metis_tac[FVs_VSUBST_CASES, NVARIANT_esubst_ty0_alt])
  >- (with_flag (Cond_rewr.stack_limit, 0)
                (gvs[bind_EQ_error, bind_EQ_return, term_ok_def, try_eq_error, AllCaseEqs()])
      >> gvs[DISJ_IMP_THM, term_ok_vsubst_variant]
      >> gvs[neq_error, REV_ASSOCD_def, term_ok_vsubst_variant,
             PULL_EXISTS, DISJ_IMP_THM, AllCaseEqs(), term_ok_def]
      >> rename [‘esubst_ty0 [] σ avds body = return subst_tm’]
      >> last_x_assum $ qspec_then ‘subst_tm’ assume_tac
      >> Cases_on ‘n = x’
      >- (Cases_on ‘ty_esubst σ ty = ty_esubst σ typ1’
          >> metis_tac[FVs_VSUBST_PRESERVED_VAR, NVARIANT_esubst_ty0_alt])
      >> gvs[]
      >> metis_tac[FVs_VSUBST_CASES, NVARIANT_esubst_ty0_alt])
  >> with_flag (Cond_rewr.stack_limit, 0) (gvs[bind_EQ_error, bind_EQ_return,
                                               term_ok_def, try_eq_error, AllCaseEqs(),
                                               try_eq_return])
  >> gvs[DISJ_IMP_THM, term_ok_vsubst_variant]
  >> gvs[neq_error, REV_ASSOCD_def, term_ok_vsubst_variant,
         PULL_EXISTS, DISJ_IMP_THM, AllCaseEqs(), term_ok_def]
  >- rw[ty_esubst_def]
  >- (rw[ty_esubst_def] >> rename [‘typeof body2 = ty_esubst σ (typeof body) (*g*)’]
      >> first_x_assum (drule o cj 3) >> rw[] >> simp[typeof_vsubst, SF SFY_ss])
  >- (rC ‘n = NVARIANT n avds body1’ >> rw[]
      >> last_x_assum $ qspec_then ‘body1’ assume_tac >> rw[]
      >> drule FVs_in_tm_names >> rw[]
      >> first_x_assum (irule_at Any o cj 2)
      >> drule_all tm_names_vsubst
      >> metis_tac[])
  >- (rC ‘n = NVARIANT x avds body1’ >> rw[]
      >> last_x_assum $ qspec_then ‘body1’ assume_tac >> rw[]
      >> gvs[term_ok_vsubst_variant]
      >> first_x_assum drule >> rw[]
      >> first_x_assum irule
      >> first_x_assum $ qspec_then ‘x’ assume_tac >> rw[]
      >> qspecl_then [‘body’, ‘x’, ‘x’, ‘NVARIANT x avds body1’, ‘typ1’, ‘ty’]
                     assume_tac FVs_VSUBST_PRESERVED_VAR >> gvs[]
      >> ‘MEM x (tm_names body)’ by metis_tac[FVs_in_tm_names]
      >> Cases_on ‘n = x’
      >- metis_tac[tm_names_vsubst]
      >> qspecl_then [‘body’, ‘[(Var (NVARIANT x avds body1) ty,Var x ty)]’, ‘n’]
                     assume_tac tm_names_vsubst_different_name
      >> gvs[term_ok_def])
QED

Theorem esubst_ty0_always_returns:
  ∀σ tm.
    esubsts_ok sig σ ∧
    term_ok sig tm ⇒
    ∃v. esubst_ty0 [] σ avds tm = return v
Proof
  rpt gen_tac
  >> qspec_then ‘[]’ assume_tac esubst_ty0_impossible1
  >> gvs[REV_ASSOCD_def, neq_error]
QED


Theorem esubst_comb[simp]:
  ∀t1 t2.
    esubsts_ok sig σ ∧
    term_ok sig t1 ∧ term_ok sig t2 ⇒
    esubst σ avds (Comb t1 t2) = Comb (esubst σ avds t1) (esubst σ avds t2)
Proof
  rw[]
  >> ‘∃v1. esubst_ty0 [] σ avds t1 = return v1’
    by metis_tac[esubst_ty0_always_returns]
  >> ‘∃v2. esubst_ty0 [] σ avds t2 = return v2’
    by metis_tac[esubst_ty0_always_returns]
  >> rw[esubst_def, esubst_ty_def, esubst_ty0_def, bind_EQ_return, esubst_tm_def]
QED

Theorem esubst_ty_comb[simp]:
  ∀t1 t2.
    esubsts_ok sig σ ∧
    term_ok sig t1 ∧ term_ok sig t2 ⇒
    esubst_ty σ avds (Comb t1 t2) = Comb (esubst_ty σ avds t1) (esubst_ty σ avds t2)
Proof
  rw[]
  >> ‘∃v1. esubst_ty0 [] σ avds t1 = return v1’ by metis_tac[esubst_ty0_always_returns]
  >> ‘∃v2. esubst_ty0 [] σ avds t2 = return v2’ by metis_tac[esubst_ty0_always_returns]
  >> rw[esubst_ty_def, esubst_ty0_def, bind_EQ_return]
QED

Theorem typeof_esubst_ty:
  ∀tm tm1.
    esubsts_ok sig (σ,θ) ∧
    term_ok sig tm ∧
    (∀k v. MEM (v,k) env ⇒ ∃n ty. k = Var n (ty_esubst (σ, θ) ty) ∧ v = Var n ty) ∧
    esubst_ty0 env (σ,θ) avds tm = return tm1 ⇒
    typeof tm1 = ty_esubst (σ,θ) (typeof tm)
Proof
  rw[] >> drule_all esubst_ty0_impossible1
  >> metis_tac[]
QED

Theorem LIST_INSERT_EQ_NIL[simp]:
  LIST_INSERT h xs ≠ []
Proof
  rw[LIST_INSERT_def] >> strip_tac >> gvs[]
QED

Theorem LIST_UNION_EQ_NIL[simp]:
  ∀xs ys. LIST_UNION xs ys = [] ⇔ xs = [] ∧ ys = []
Proof
  Induct_on ‘xs’ >> rw[]
  >> simp[LIST_UNION_def]
QED

Theorem monomorphic_type_subst:
  ∀ty i. is_monomorphic ty ⇒ TYPE_SUBST i ty = ty
Proof
  Induct_on ‘ty’ using type_ind >> rw[TYPE_SUBST_def] >> gvs[tyvars_def]
  >> gvs[EVERY_MEM]
  >> Induct_on ‘l’ >> rw[]
QED

Theorem typeof_has_type:
  ∀tm. welltyped tm ⇒ (tm has_type typ ⇔ typeof tm = typ)
Proof
  simp[welltyped_def] >> Induct_on ‘$has_type’ >> rw[]
  >- gvs[Once has_type_cases]
  >- gvs[Once has_type_cases]
  >> rw[codomain_def, Once has_type_cases, EQ_IMP_THM]
  >> metis_tac[has_type_typeof, codomain_def, typeof_def, has_type_cases]
QED

Theorem esubsts_ok_type_ok:
  ∀ty.
    esubsts_ok sig σ ∧
    type_ok (tysof sig) ty ⇒
    type_ok (tysof sig) (ty_esubst σ ty)
Proof
  Cases_on ‘σ’ >> rw[esubsts_ok_def]
  >> Induct_on ‘ty’ using type_ind
  >> rw[ty_esubst_def]
  >> Induct_on ‘l’
  >> rw[ty_esubst_def]
  >- (rC ‘FLOOKUP tys tyn’ >> first_x_assum irule
      >> metis_tac[IN_FRANGE_FLOOKUP])
  >> gvs[type_ok_def, EVERY_MEM, MEM_MAP]
  >> metis_tac[]
QED

Theorem REV_ASSOCD_MAP:
  ∀l. REV_ASSOCD x (MAP (λ(v, k). (f v, k)) l) d =
      if ∃v0. MEM (v0, x) l then f (REV_ASSOCD x l d) else d
Proof
  Induct_on ‘l’ >> csimp[REV_ASSOCD_def, AllCaseEqs(), FORALL_PROD]
  >> rw[]
  >> rename [‘k1 = k0 ∨ k1 ≠ k0 ∧ _’]
  >> Cases_on ‘k1 = k0’
  >> simp[]
  >> metis_tac[]
QED

Theorem ty_esubst_TYPE_SUBST:
  ∀ty i. esubsts_ok (tys, tms) σ ∧
         type_ok tys (TYPE_SUBST i ty) ⇒
         is_instance (ty_esubst σ ty) (ty_esubst σ (TYPE_SUBST i ty))
Proof
  rpt strip_tac
  >> qexists ‘MAP (λ(v, k). (ty_esubst σ v, k)) i’
  >> Induct_on ‘ty’ using type_ind
  >- (rw[ty_esubst_def, TYPE_SUBST_def, REV_ASSOCD_MAP]
      >> Cases_on ‘REV_ASSOCD (Tyvar m) i (Tyvar m) = Tyvar m’
      >> simp[ty_esubst_def]
      >> drule rev_assocd_neq_mem
      >> metis_tac[])
  >> Cases_on ‘l’
  >- (Cases_on ‘σ’ >> rename [‘(σ, θ)’] >> gvs[esubsts_ok_def]
      >> rw[ty_esubst_def, TYPE_SUBST_def]
      >> CASE_TAC >> simp[TYPE_SUBST_def]
      >> gvs[type_ok_def] >> first_x_assum drule
      >> rw[monomorphic_type_subst])
  >> gvs[EVERY_MEM] >> rw[]
  >> ‘type_ok tys (TYPE_SUBST i h)’ by gvs[type_ok_def]
  >> gvs[type_ok_def, EVERY_MEM]
  >> ‘∀ty. MEM ty t ⇒ type_ok tys (TYPE_SUBST i ty)’
    by metis_tac[MEM_MAP]
  >> simp[TYPE_SUBST_def, ty_esubst_def, MAP_MAP_o, MAP_CONG]
QED

Theorem term_ok_var[simp]:
  term_ok sig (Var x ty) ⇔ type_ok (tysof sig) ty
Proof
  simp[term_ok_def]
QED

Theorem term_ok_comb[simp]:
  term_ok sig (Comb tm1 tm2) ⇔
    term_ok sig tm1 ∧ term_ok sig tm2 ∧ welltyped (Comb tm1 tm2)
Proof
  simp[term_ok_def]
QED

Theorem term_ok_abs[simp]:
  term_ok sig (Abs v tm) ⇔
    ∃x ty. v = Var x ty ∧ type_ok (tysof sig) ty ∧ term_ok sig tm
Proof
  simp[term_ok_def]
QED

Theorem esubst_ty0_term_ok:
  ∀env σ avds tm subst_tm.
    esubst_ty0 env σ avds tm = return subst_tm ∧
    term_ok sig tm ∧
    esubsts_ok sig σ ∧
    (∀v1 v2. MEM (v1, v2) env ⇒ ∃n ty. v1 = Var n ty ∧ v2 = Var n (ty_esubst σ ty)) ⇒
    term_ok (esubst_sig σ sig) subst_tm
Proof
  Cases_on ‘sig’ >> rename [‘esubst_sig _ (tys, tms)’]
  >> recInduct esubst_ty0_ind >> rw[esubst_sig_def]
  >- (gvs[esubst_ty0_def, AllCaseEqs(), esubsts_ok_def]
      >> drule esubsts_ok_type_ok >> simp[])
  >- (gvs[esubst_ty0_def, FLOOKUP_o_f, term_ok_def] >> conj_tac
      >- (drule esubsts_ok_type_ok >> simp[])
      >> metis_tac[ty_esubst_TYPE_SUBST])
  >- (gvs[esubst_ty0_def, FLOOKUP_o_f, bind_EQ_return]
      >> qspecl_then [‘(tys, tms)’, ‘env’, ‘σ’, ‘avds’, ‘t1’] mp_tac
                     $ GEN_ALL esubst_ty0_impossible1
      >> impl_tac >> simp[DISJ_IMP_THM, FORALL_AND_THM]
      >- metis_tac[]
      >> rw[]
      >- metis_tac[term_ok_welltyped]
      >- metis_tac[term_ok_welltyped]
      >> rw[ty_esubst_def]
      >> qspecl_then [‘(tys, tms)’, ‘env’, ‘σ’, ‘avds’, ‘t2’] mp_tac
                     $ GEN_ALL esubst_ty0_impossible1
      >> impl_tac >> simp[DISJ_IMP_THM, FORALL_AND_THM]
      >> metis_tac[])
  >> gvs[term_ok_def, esubst_ty0_def, bind_EQ_return, bind_EQ_error, try_eq_return]
  >- (rw[]
      >- (qspecl_then [‘σ’, ‘(tys, tms)’, ‘ty’] mp_tac
                      $ GEN_ALL esubsts_ok_type_ok
          >> simp[])
      >> first_x_assum irule >> metis_tac[])
  >> gvs[AllCaseEqs(), bind_EQ_return]
  >> rw[]
  >- (qspecl_then [‘σ’, ‘(tys, tms)’, ‘ty’] mp_tac
                  $ GEN_ALL esubsts_ok_type_ok
      >> simp[])
  >> first_x_assum irule >> qexists ‘body1’
  >> rw[]
  >- metis_tac[]
  >> irule term_ok_vsubst_variant
  >> simp[]
QED

Theorem esubst_ty_bool:
  ∀tm.
    term_ok sig tm ∧
    esubsts_ok sig σ ∧
    tm has_type Bool ⇒
    esubst_ty σ avds tm has_type Bool
Proof
  rw[] >> qspecl_then [‘[]’, ‘σ’, ‘avds’, ‘tm’] mp_tac esubst_ty0_impossible1
  >> impl_tac >> simp[]
  >> rw[esubst_ty_def] >> CASE_TAC
  >> drule term_ok_welltyped >> strip_tac
  >> gvs[]
  >- (drule esubst_ty0_term_ok >> rw[]
      >> first_x_assum $ qspec_then ‘sig’ mp_tac >> impl_tac >> rw[]
      >> dxrule term_ok_welltyped >> rw[typeof_has_type]
      >> drule has_type_typeof >> rw[]
      >> Cases_on ‘σ’ >> rename [‘ty_esubst (σ, θ) _ = _’]
      >> rw[ty_esubst_def] >> gvs[FDOM_FLOOKUP, esubsts_ok_def]
      >> CASE_TAC >> metis_tac[])
  >> drule_all esubst_ty0_always_returns >> simp[]
  >> rw[] >> first_x_assum $ qspec_then ‘avds’ assume_tac >> gvs[]
QED

Theorem const_has_type_eq:
  Const n ty has_type typ ⇒ ty = typ
Proof
  Induct_on ‘$has_type’ >> rw[]
QED

Theorem esubst_ty0_ty_esubst:
  ∀tm env.
    esubst_ty0 env σ avds tm = return subst_tm ∧
    esubsts_ok sig σ ∧
    (∀k v. MEM (v,k) env ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    term_ok sig tm ⇒
    typeof subst_tm = ty_esubst σ (typeof tm)
Proof
  rpt strip_tac >> drule_all $ cj 3 esubst_ty0_impossible1
  >> simp[]
QED

Theorem esubst_ty0_env_type_invariant:
  ∀tm ty tm1 tm2 env1 env2.
    term_ok sig tm ∧
    esubsts_ok sig σ ∧
    (∀k v. MEM (v,k) env1 ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    (∀k v. MEM (v,k) env2 ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    esubst_ty0 env1 σ avds tm = return tm1 ∧
    esubst_ty0 env2 σ avds tm = return tm2 ⇒
    typeof tm1 = typeof tm2
Proof
  rpt strip_tac >> rpt $ dxrule_then drule_all esubst_ty0_ty_esubst
  >> simp[]
QED

Theorem sizeof_esubst_ty0:
  ∀env σ avds tm subst_tm sig.
    term_ok sig tm ∧
    (∀k v. MEM (v,k) env ⇒ ∃n1 ty1 n2 ty2. k = Var n1 ty1 ∧ v = Var n2 ty2) ∧
    esubst_ty0 env σ avds tm = return subst_tm ⇒
    sizeof tm = sizeof subst_tm
Proof
  recInduct esubst_ty0_ind >> rw[]
  >> gvs[esubst_ty0_def, AllCaseEqs()]
  >> gvs[bind_EQ_return, bind_EQ_error]
  >> gvs[AllCaseEqs(), try_eq_return, bind_EQ_return, bind_EQ_error]
  >> rpt $ first_x_assum (qspec_then ‘sig’ assume_tac) >> gvs[]
  >- (first_x_assum irule >> simp[DISJ_IMP_THM, FORALL_AND_THM])
  >> last_x_assum $ qspecl_then [‘body1’, ‘body''’, ‘sig’] mp_tac
  >> impl_tac
  >- simp[term_ok_vsubst_variant, DISJ_IMP_THM, FORALL_AND_THM]
  >> rw[SIZEOF_VSUBST]
QED

Theorem tysof_esubst_sig[simp]:
  tysof (esubst_sig σ sig) = tysof sig
Proof
  Cases_on ‘σ’ >> Cases_on ‘sig’ >> simp[esubst_sig_def]
QED

Theorem tmsof_esubst_sig[simp]:
  tmsof (esubst_sig σ sig) = ty_esubst σ o_f tmsof sig
Proof
  Cases_on ‘σ’ >> Cases_on ‘sig’ >> simp[esubst_sig_def]
QED

Theorem typeof_esubst_tm_esubst_ty0:
  ∀tm ty subst_tm env sig.
    term_ok sig tm ∧
    esubsts_ok sig σ ∧
    (∀k v. MEM (v,k) env ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    esubst_ty0 env σ avds tm = return subst_tm ⇒
    typeof (esubst_tm σ subst_tm) = typeof subst_tm
Proof
  Cases_on ‘σ’ >> rename [‘(σ, θ)’]
  >> completeInduct_on ‘sizeof tm’
  >> Cases_on ‘tm’ >> rw[]
  >- gvs[esubst_def, esubst_tm_def, esubst_ty0_def, AllCaseEqs()]
  >- (gvs[esubst_def, esubst_tm_def, esubst_ty0_def,
          AllCaseEqs(), term_ok_def]
      >> rC ‘FLOOKUP θ m’ >> gvs[esubsts_ok_def]
      >> first_x_assum $ qspec_then ‘m’ mp_tac >> rw[FDOM_FLOOKUP]
      >> gvs[FDOM_FLOOKUP] >> rw[esubst_tm_def]
      >> gvs[TO_FLOOKUP] >> rw[monomorphic_type_subst])
  >- (gvs[esubst_ty0_def, bind_EQ_return]
      >> first_assum $ qspec_then ‘sizeof t1'’ mp_tac
      >> impl_tac
      >- (‘sizeof t = sizeof t1'’ suffices_by simp[]
          >> irule sizeof_esubst_ty0
          >> metis_tac[DISJ_IMP_THM, FORALL_AND_THM])
      >> rw[]
      >> first_x_assum $ qspec_then ‘t’ mp_tac >> impl_tac
      >- (sym_tac >> irule sizeof_esubst_ty0 >> metis_tac[])
      >> rw[esubst_tm_def]
      >> ‘typeof (esubst_tm (σ,θ) t1') = typeof t1'’ suffices_by simp[]
      >> first_x_assum irule >> metis_tac[])
  >> gvs[esubst_ty0_def, try_eq_return, AllCaseEqs(), bind_EQ_error,
         bind_EQ_return] >> rw[esubst_tm_def]
  >- (first_x_assum irule >> first_x_assum $ irule_at Any
      >> simp[DISJ_IMP_THM, FORALL_AND_THM, SF SFY_ss])
  >> first_x_assum irule >> first_x_assum $ irule_at Any
  >> simp[DISJ_IMP_THM, FORALL_AND_THM]
  >> first_x_assum $ irule_at Any
  >> simp[term_ok_vsubst_variant, SIZEOF_VSUBST]
QED

val spec_impl = fn v => first_x_assum $ qspec_then v mp_tac >> impl_tac

Theorem FOLDR_LIST_UNION_CONG:
  (∀x. MEM x l ⇒ f x = g x) ⇒
  FOLDR (λx acc. LIST_UNION (f x) acc) b l =
  FOLDR (λx acc. LIST_UNION (g x) acc) b l
Proof
  Induct_on ‘l’ >> simp[]
QED

Theorem ty_esubst_preserves_tyvars:
  ∀ty. esubsts_ok sig σ ∧
       type_ok (tysof sig) ty ⇒
       tyvars ty = tyvars (ty_esubst σ ty)
Proof
  Induct_on ‘ty’ using type_ind
  >> rw[ty_esubst_def]
  >> Cases_on ‘l’
  >> gvs[ty_esubst_def, EVERY_MEM, type_ok_def]
  >- (rC ‘FLOOKUP (FST σ) m’ >> simp[tyvars_def]
      >> Cases_on ‘σ’ >> gvs[esubsts_ok_def]
      >> first_x_assum irule >> metis_tac[])
  >> simp[tyvars_def, FOLDR_MAP]
  >> CONG_TAC $ SOME 1 >> simp[FOLDR_LIST_UNION_CONG]
QED

Theorem is_monomorphic_ty_esubst:
  ∀ty. esubsts_ok sig σ ∧ type_ok (tysof sig) ty ⇒
       (is_monomorphic ty ⇔ is_monomorphic (ty_esubst σ ty))
Proof
  rpt strip_tac >> drule_all ty_esubst_preserves_tyvars >> simp[]
QED

Theorem typeof_esubst_tm:
  ∀tm.
    esubsts_ok sig (σ, θ) ∧
    theory_ok (sig, axs) ∧
    term_ok (esubst_sig (σ,θ) sig) tm ⇒
    typeof (esubst_tm (σ,θ) tm) = typeof tm
Proof
  Induct_on ‘tm’ >> rw[esubst_tm_def]
  >- (rC ‘FLOOKUP σ m’ >> gvs[term_ok_def, FLOOKUP_o_f, esubsts_ok_def]
      >> first_assum $ qspec_then ‘m’ mp_tac
      >> impl_tac >- simp[FDOM_FLOOKUP] >> rw[]
      >> gvs[FDOM_FLOOKUP, monomorphic_type_subst, TO_FLOOKUP, AllCaseEqs()]
      >> rw[] >> rename [‘(σ, θ)’]
      >> sym_tac >> irule monomorphic_type_subst
      >> irule $ iffLR is_monomorphic_ty_esubst >> simp[]
      >> qexists ‘sig’ >> strip_tac
      >- (rw[esubsts_ok_def] >> metis_tac[FDOM_FLOOKUP, IN_FRANGE_FLOOKUP])
      >> gvs[theory_ok_def, IN_FRANGE_FLOOKUP]
      >> first_x_assum irule >> metis_tac[])
  >> metis_tac[]
QED

Theorem esubst_tm_preserves_term_ok:
  ∀tm. theory_ok (sig, axs) ∧
       esubsts_ok sig σ ∧
       term_ok (esubst_sig σ sig) tm ⇒
       term_ok (esubst_sig σ sig) (esubst_tm σ tm)
Proof
  Cases_on ‘σ’ >> rename [‘(σ, θ)’]
  >> Induct_on ‘tm’ >> rw[esubst_tm_def]
  >- (rC ‘FLOOKUP θ m’
      >> gvs[esubsts_ok_def, term_ok_def]
      >> gvs[TO_FLOOKUP] >> first_x_assum $ qspec_then ‘x’ mp_tac
      >> impl_tac >> metis_tac[])
  >- (gvs[term_ok_def, esubst_tm_def] >> rw[]
      >> metis_tac[term_ok_welltyped])
  >- (gvs[term_ok_def, esubst_tm_def] >> rw[]
      >> metis_tac[term_ok_welltyped])
  >> metis_tac[typeof_esubst_tm]
QED

Theorem esubst_term_ok:
  theory_ok (sig, axs) ∧
  term_ok sig tm ∧
  esubsts_ok sig σ ⇒
  term_ok (esubst_sig σ sig) (esubst σ avds tm)
Proof
  rw[esubst_def, esubst_ty_def]
  >> ‘∃tm1. esubst_ty0 [] σ avds tm = return tm1’
    by metis_tac[esubst_ty0_always_returns]
  >> drule esubst_ty0_term_ok
  >> rw[] >> spec_impl ‘sig’ >> simp[]
  >> metis_tac[esubst_tm_preserves_term_ok]
QED

Theorem esubst_has_type:
  ∀tm.
    theory_ok (sig, axs) ∧
    esubst_ty σ avds tm has_type ty ∧
    term_ok sig tm ∧
    esubsts_ok sig σ ⇒
    esubst σ avds tm has_type ty
Proof
  rw[esubst_def, esubst_ty_def]
  >> ‘∃subst_tm. esubst_ty0 [] σ avds tm = return subst_tm’
    by metis_tac[esubst_ty0_always_returns]
  >> rw[] >> gvs[]
  >> drule typeof_esubst_tm_esubst_ty0
  >> rw[]
  >> first_x_assum $ qspecl_then [‘σ’, ‘avds’, ‘subst_tm’, ‘[]’] mp_tac
  >> rw[] >> drule term_ok_welltyped >> dxrule has_type_typeof
  >> rw[] >> gvs[] >> drule typeof_has_type >> rw[]
  >> drule esubst_ty0_term_ok >> rw[]
  >> spec_impl ‘sig’ >> rw[]
  >> dxrule term_ok_welltyped >> rw[]
  >> drule typeof_has_type >> rw[]
  >> first_x_assum $ qspec_then ‘typeof (esubst_tm σ subst_tm)’ assume_tac
  >> drule esubst_term_ok >> rw[esubst_tm_def]
  >> first_x_assum $ qspecl_then [‘σ’, ‘tm’, ‘avds’] mp_tac
  >> rw[] >> gvs[esubst_def, esubst_ty_def]
  >> drule term_ok_welltyped
  >> metis_tac[typeof_has_type]
QED

Theorem esubst_has_type_bool:
  ∀tm.
    tm has_type Bool ∧
    esubsts_ok sig σ ∧
    theory_ok (sig, axs) ∧
    term_ok sig tm ⇒
    esubst σ avds tm has_type Bool
Proof
  rw[] >> irule esubst_has_type >> strip_tac
  >- (irule esubst_ty_bool >> simp[SF SFY_ss])
  >> simp[SF SFY_ss]
QED

Theorem term_ok'_imp_term_ok:
  ∀tm. term_ok' thy tm ⇒ term_ok (thy.ctys,thy.ctms) tm
Proof
  Induct_on ‘tm’ >> rw[term_ok'_def, term_ok_def]
QED
        
Theorem is_std_sig_funion:
  is_std_sig (tys, tms) ⇒ is_std_sig (tys ⊌ tys1, tms ⊌ tms1)
Proof
  rw[is_std_sig_def, FLOOKUP_FUNION]
QED

Theorem type_ok_weakening:
  ∀ty. type_ok ts1 ty ⇒ type_ok (ts1 ⊌ ts2) ty
Proof
  Induct_on ‘ty’ using type_ind >> gvs[type_ok_def, FLOOKUP_FUNION, EVERY_MEM]
QED

Theorem term_ok_weakening:
  ∀tm. term_ok (tys, tms) tm ⇒ term_ok (tys ⊌ tys1, tms ⊌ tms1) tm
Proof
  Induct_on ‘tm’ >> rw[term_ok_def, type_ok_weakening]
  >> qexists ‘ty0’ >> rw[FLOOKUP_FUNION, type_ok_weakening] >> metis_tac[]
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

Theorem welltyped_comb:
  welltyped l1 ∧
  welltyped l2 ∧
  typeof l1 = Fun (typeof l2) rty ⇒
  welltyped (Comb l1 l2)
Proof
  rw[welltyped_def]
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

Theorem proves_imp_theory_ok:
  ∀thy h. (thy, h) |- c ⇒ theory_ok thy
Proof
  Induct_on ‘$|-’ >> rw[] >> rw[]
QED

Theorem axiom_weakening:
  ∀A B h. ((sig, A), h) |- c
          ∧ (∀p. p ∈ B ⇒ term_ok sig p ∧ p has_type Bool)
          ∧ A ⊆ B
          ⇒ ((sig, B), h) |- c
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
      >> gvs[theory_ok_def, type_ok_def, SUBSET_DEF])
QED

Theorem axioms_eliminable:
  ∀thy1 thy2 h2 c1 c2.
    (thy2, h2) |- c2 ∧ (thy1, []) |- c1
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
      >- (rw[] >> irule axiom_weakening >> rw[]
          >> gvs[theory_ok_def] >> drule proves_imp_theory_ok >> rw[theory_ok_def]
          >> qexists ‘axsof thy1’ >> rw[] >> Cases_on ‘thy1’ >> gvs[])
      >- (irule proves_axioms >> rw[] >> metis_tac[proves_theory_ok_ext]))
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

Theorem FAPPLY_IN_FRANGE:
  ∀m. x ∈ FDOM m ⇒ m ' x ∈ FRANGE m
Proof
  Induct_on ‘m’ >> rw[]
  >> gvs[FAPPLY_FUPDATE]
  >> rename [‘m |+ (k, v)’]
  >> Cases_on ‘(m |+ (k, v)) ' x = v’ >> rw[]
  >> ‘k ≠ x’ by metis_tac[]
  >> qspecl_then [‘m |+ (k, v)’, ‘k’, ‘x’] assume_tac DOMSUB_FAPPLY_NEQ
  >> rw[] >> gvs[DOMSUB_NOT_IN_DOM]
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

Theorem ty_esubst_type_ok_alt:
  ∀ty.
    type_ok (tysof sig) ty ∧
    esubsts_ok sig σ ⇒
    type_ok (tysof sig) (ty_esubst σ ty)
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

Theorem thy_axs_diff:
  c ∉ a ⇒
  a ∪ (b DIFF {c} ∪ d) = ((a ∪ b) DIFF {c}) ∪ (a ∪ d)
Proof
  rw[UNION_DEF, EXTENSION, EQ_IMP_THM] >> metis_tac[]
QED

Theorem thy_axs_diff_alt:
  c ∈ a ⇒
  a ∪ (b DIFF {c} ∪ d) = a ∪ b ∪ d
Proof
  rw[UNION_DEF, EXTENSION, EQ_IMP_THM] >> metis_tac[]
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

val _ = temp_set_fixity "|n-" (Infix(NONASSOC, 450));

Inductive nproves:
[~ABS:]
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok (tysof thy) ty ∧
   (thy, h, n) |n- l === r
   ⇒ (thy, h, n + 1) |n- (Abs (Var x ty) l) === (Abs (Var x ty) r))

[~ASSUME:]
  (theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
   ⇒ (thy, [p], 0) |n- p)

[~BETA:]
  (theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t
   ⇒ (thy, [], 0) |n- Comb (Abs (Var x ty) t) (Var x ty) === t)

[~DEDUCT_ANTISYM:]
  ((thy, h1, n) |n- c1 ∧
   (thy, h2, m) |n- c2
   ⇒ (thy, term_union (term_remove c2 h1)
                      (term_remove c1 h2),
      n + m + 1)
   |n- c1 === c2)

[~EQ_MP:]
  ((thy, h1, n) |n- p === q ∧
   (thy, h2, m) |n- p' ∧ ACONV p p'
   ⇒ (thy, term_union h1 h2, n + m + 1) |n- q)

[~INST:]
  ((∀s s'. MEM (s',s) ilist ⇒
             ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
   (thy, h, n) |n- c
   ⇒ (thy, term_image (VSUBST ilist) h, n + 1) |n- VSUBST ilist c)

[~INST_TYPE:]
  ((EVERY (type_ok (tysof thy)) (MAP FST tyin)) ∧
   (thy, h, n) |n- c
   ⇒ (thy, term_image (INST tyin) h, n + 1) |n- INST tyin c)

[~MK_COMB:]
  ((thy, h1, n) |n- l1 === r1 ∧
   (thy, h2, m) |n- l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, term_union h1 h2, n + m + 1) |n- Comb l1 l2 === Comb r1 r2)

[~REFL:]
  (theory_ok thy ∧ term_ok (sigof thy) t
   ⇒ (thy, [], 0) |n- t === t)

[~axioms:]
  (theory_ok thy ∧ c ∈ (axsof thy)
   ⇒ (thy, [], 0:num) |n- c)
End

Theorem nproves_proves:
  ∀thy hs c. (thy, hs) |- c ⇔ ∃n. (thy, hs, n) |n- c
Proof
  simp[EQ_IMP_THM, FORALL_AND_THM]
  >> conj_tac
  >- (Induct_on ‘$|-’ >> rw[]
      >> gvs[EVERY_MEM, EXISTS_MEM]
      >> metis_tac[SRULE [EVERY_MEM] nproves_rules])
  >> Induct_on ‘$|n-’ >> rw[]
  >> gvs[EVERY_MEM, EXISTS_MEM]
  >> metis_tac[SRULE [EVERY_MEM] proves_rules]
QED

Theorem FAPPLY_FLOOKUP:
  ∀f. FLOOKUP f k = SOME v ⇒ f ' k = v
Proof
  Induct_on ‘f’ >> rw[FAPPLY_FUPDATE_THM]
  >> Cases_on ‘k = x’ >> gvs[FLOOKUP_SIMP]
QED

Theorem term_image_id:
  ∀lst. term_image (λp. p) lst = lst
Proof
  Induct_on ‘lst’ >> rw[term_image_def]
QED

Theorem esubst_equation_has_type:
  ∀l r.
    is_std_sig sig ∧
    esubsts_ok sig σ ∧
    term_ok sig (l === r) ⇒
    esubst σ avds (l === r) has_type Bool
Proof
  cheat >> rpt strip_tac >> irule esubst_has_type_bool
  >> simp[EQUATION_HAS_TYPE_BOOL] >> strip_tac
  >> metis_tac[term_ok_equation, term_ok_welltyped]
QED

Theorem tysig_frange_type_ok:
  ∀ty.
    (∀t. t ∈ FRANGE σ ⇒ type_ok sig t) ∧
    type_ok sig ty ⇒
    type_ok sig (ty_esubst (σ, θ) ty)
Proof
  Induct_on ‘ty’ using type_ind
  >> rw[ty_esubst_def]
  >> gvs[EVERY_MEM, type_ok_def, ty_esubst_def]
  >> Cases_on ‘l’
  >> gvs[ty_esubst_def, type_ok_def]
  >- (rC ‘FLOOKUP σ m’ >> rw[type_ok_def] >> first_x_assum irule
      >> gvs[FRANGE_FLOOKUP, SF SFY_ss])
  >> rw[EVERY_MEM, MEM_MAP] >> last_x_assum irule
  >> gvs[]
QED

Theorem nproves_term_ok:
  ∀tm. ((sig, axs), h, n) |n- tm ⇒ term_ok sig tm
Proof
  rw[] >> mp_tac proves_term_ok >> rw[]
  >> first_x_assum $ qspecl_then [‘((sig, axs), h)’, ‘tm’] mp_tac
  >> impl_tac >> rw[]
  >> metis_tac[nproves_proves]
QED

Theorem term_union_left_nil[simp]:
  ∀h. term_union [] h = h
Proof
  Induct_on ‘h’ >> rw[Once term_union_def]
QED

Theorem nproves_theory_ok:
  ∀thy h n c. (thy, h, n) |n- c ⇒ theory_ok thy
Proof
  Induct_on ‘$|n-’ >> rw[] >> rw[]
QED

Theorem nproves_ACONV_concl:
  ∀thy h n c c'.
    (thy,h,n) |n- c ∧ welltyped c' ∧ ACONV c c' ⇒
    (thy,h,n+1) |n- c'
Proof
  rw[]
  >> qspecl_then [‘c'’, ‘thy’] mp_tac nproves_REFL
  >> imp_res_tac nproves_theory_ok
  >> imp_res_tac nproves_term_ok >> fs[]
  >> imp_res_tac term_ok_aconv >> rw[] >> gvs[SF SFY_ss]
  >> first_x_assum $ qspecl_then [‘c’, ‘sigof thy’] mp_tac >> impl_tac
  >> Cases_on ‘thy’ >> gvs[]
  >- metis_tac[nproves_term_ok]
  >> rw[] >> gvs[]
  >> rename [‘((sig, axs), h, n + 1)’]
  >> drule nproves_EQ_MP >> rw[]
  >> first_x_assum $ qspecl_then [‘h’, ‘n’, ‘c’] assume_tac
  >> gvs[ACONV_SYM]
QED

Theorem ACONV_equation_r:
  welltyped a ∧ welltyped c ⇒
  (ACONV a (c === c) ⇔
     ∃b d. a = b === d ∧ ACONV c b ∧ ACONV c d
           ∧ welltyped b ∧ welltyped d)
Proof
  rw[ACONV_def, equation_def]
  >> simp[SimpLHS, Once RACONV_cases]
  >> simp[SimpLHS, Once RACONV_cases]
  >> simp[PULL_EXISTS]
  >> simp[SimpLHS, Once RACONV_cases]
  >> simp[GSYM ACONV_def]
  >> iff_tac >> rw[]
  >- (gvs[welltyped_def] >> metis_tac[ACONV_SYM])
  >- (gvs[ACONV_SYM, welltyped_def] >> irule ACONV_TYPE
      >> simp[welltyped_def, ACONV_SYM] >> metis_tac[])
QED

Theorem nproves_addAssum:
  ∀thy h c a n.
    (thy, h, n) |n- c ∧
    term_ok (sigof thy) a ∧
    a has_type Bool ⇒
    ∃m. m ≤ n + 3 ∧ (thy, term_union [a] h, m) |n- c
Proof
  rw[] >> drule_then assume_tac nproves_theory_ok
  >> Cases_on ‘ACONV a (c === c)’
  >- (drule_at (Pos last) nproves_ASSUME
      >> rw[]
      >> drule_then assume_tac term_ok_welltyped
      >> ‘welltyped c’ by metis_tac[PAIR, FST, nproves_term_ok, term_ok_welltyped]
      >> gvs[ACONV_equation_r]
      >> drule nproves_EQ_MP >> disch_then rev_drule
      >> rw[ACONV_SYM] >> irule_at Any nproves_ACONV_concl
      >> first_assum $ irule_at Any >> simp[ACONV_SYM])
  >> drule_at (Pos last) nproves_ASSUME >> rw[]
  >> ‘term_ok (sigof thy) c’ by metis_tac[nproves_term_ok, FST, PAIR]
  >> qspecl_then [‘c’, ‘thy’] mp_tac nproves_REFL
  >> rw[]
  >> qspecl_then [‘a’, ‘c === c’] (FREEZE_THEN drule_all) nproves_DEDUCT_ANTISYM
  >> rw[]
  >> drule nproves_EQ_MP >> disch_then (resolve_then Any mp_tac ACONV_REFL)
  >> disch_then drule
  >> ‘term_remove (c === c) [a] = [a]’
    by (simp[Once term_remove_def, GSYM ACONV_eq_orda, AllCaseEqs()]
        >> metis_tac[ACONV_SYM])
  >> rw[]
  >> gvs[cj 2 term_union_thm]
  >> drule nproves_EQ_MP >> disch_then (resolve_then Any mp_tac ACONV_REFL)
  >> disch_then drule >> disch_then $ irule_at Any
  >> simp[]
QED
        
Theorem nproves_ACONV_lemma:
  ∀thy c hyps' pfx hyps n.
    (thy, pfx ++ hyps, n) |n- c ∧
    hypset_ok (pfx ++ hyps') ∧
    EVERY (λx. EXISTS (ACONV x) hyps') hyps ∧
    EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) hyps' ⇒
    ∃m. m ≤ n + LENGTH hyps' * 3 ∧ (thy, pfx ++ hyps', m) |n- c
Proof
  ntac 2 gen_tac >> Induct >> rw[] >> rw[]
  >> imp_res_tac nproves_term_ok >> fs[hypset_ok_cons]
  >- (first_x_assum $ irule_at Any >> simp[])
  >> Cases_on ‘EXISTS (ACONV h) hyps’
  >- cheat
  >> qspecl_then [‘thy’, ‘pfx ++ hyps’, ‘c’, ‘h’] mp_tac nproves_addAssum
  >> imp_res_tac WELLTYPED_LEMMA >> simp[]
  >> qspecl_then [‘pfx’, ‘h’, ‘hyps’] mp_tac term_union_insert
  >> impl_tac >> gvs[EVERY_MEM, EXISTS_MEM]
  >- (conj_tac >> rw[]
      >- (qpat_x_assum ‘hypset_ok (_ ++ _::_)’ mp_tac
          >> simp[hypset_ok_el_less,MEM_EL,PULL_EXISTS]
          >> fs[MEM_EL, PULL_EXISTS]
          >> disch_then $ qspecl_then [‘n'’, ‘LENGTH pfx’] mp_tac
          >> rw[EL_APPEND1, EL_APPEND2])
      >> last_x_assum $ qspec_then ‘z’ mp_tac >> simp[]
      >> strip_tac >- metis_tac[ACONV_SYM]
      >> fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM] >> rw[] >> fs[]
      >> metis_tac[ACONV_SYM,alpha_lt_trans_ACONV])
  >> 
  >> rw[] 
  >> qexists ‘m’
  >> first_x_assum $ qspecl_then [‘pfx’, ‘hyps’, ‘h::hyps'’, ‘n’] mp_tac
  >> rw[]
  >- first_x_assum drule >> rw[] 

  disch_then SUBST1_TAC >> strip_tac >>
  first_x_assum(qspecl_then[`h1++[h]`,`h''`]mp_tac) >>
  impl_tac >- (
    conj_tac >- metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] >>
    conj_tac >- (
      imp_res_tac proves_term_ok >> fs[] >>
      metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
    qpat_x_assum`EVERY P1 X`kall_tac >>
    qpat_x_assum`EVERY P1 X`kall_tac >>
    fs[EVERY_MEM,EXISTS_MEM] >>
    metis_tac[ACONV_SYM] ) >>
  metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC]
QED

Theorem nproves_ACONV:
  ∀thy h' c' h c n.
    (thy,h,n) |n- c ∧ welltyped c' ∧ ACONV c c' ∧ hypset_ok h' ∧
    EVERY (λx. EXISTS (ACONV x) h') h ∧
    EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) h' ⇒
    (thy,h',n+1) |n- c'
Proof
  rw[]
  >> drule_at (Pos $ el 2) nproves_EQ_MP
  >> rw[] >> dxrule_then assume_tac ACONV_SYM
  >> first_x_assum $ drule_at Any
  >> rw[]
  >> qspecl_then [‘c'’, ‘thy’] mp_tac nproves_REFL
  >> rw[]
  >> drule nproves_theory_ok >> rw[] >> gvs[]
  >> ‘term_ok (sigof thy) c’ by metis_tac[FST, nproves_term_ok, PAIR]
  >> ‘term_ok (sigof thy) c'’ by metis_tac[term_ok_aconv, ACONV_SYM]
  >> gvs[]
  >> first_x_assum drule

        
  >- (irule  >> rw[]
      >- metis_tac[proves_theory_ok]
      >> drule proves_term_ok >> rw[EVERY_MEM])
  >> cheat
QED

Theorem esubst_ty_abs_avoids:
  ∀x ty body avds.
    esubsts_ok sig σ ∧
    term_ok sig (Abs (Var x ty) body) ⇒
    ∃x1 body1.
      esubst_ty σ avds (Abs (Var x ty) body) = Abs (Var x1 (ty_esubst σ ty)) body1 ∧
      (x1 = x ∨ ¬MEM x1 avds) ∧
      term_ok (esubst_sig σ sig) (Abs (Var x1 (ty_esubst σ ty)) body1)
Proof
  rw[esubst_def, esubst_tm_def, esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds (Abs (Var x ty) body) = return v’
    by metis_tac[esubst_ty0_always_returns, term_ok_def]
  >> rw[]
  >> gvs[esubst_ty0_def, try_eq_return, bind_EQ_error,
         bind_EQ_return, AllCaseEqs(), NVARIANT_AVDS_THM]
  >> cheat
QED

Theorem esubst_ty_abs_avoids_full:
  ∀x ty body avds.
    esubsts_ok sig σ ∧
    term_ok sig (Abs (Var x ty) body) ⇒
    ∃x1 body1 subst_body.
      esubst_ty0 [] σ avds body = return subst_body ∧
      esubst_ty σ avds (Abs (Var x ty) body) = Abs (Var x1 (ty_esubst σ ty)) body1 ∧
      (x1 = x ∨ ¬MEM x1 (tm_names subst_body ++ avds)) ∧
      term_ok sig (Abs (Var x1 (ty_esubst σ ty)) body1)
Proof
  rw[esubst_def, esubst_tm_def, esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds (Abs (Var x ty) body) = return v’
    by metis_tac[esubst_ty0_always_returns, term_ok_def]
  >> rw[]
  >> gvs[esubst_ty0_def, try_eq_return, bind_EQ_error,
         bind_EQ_return, AllCaseEqs(), NVARIANT_AVDS_THM]
  >> ‘∃v. esubst_ty0 [] σ avds body = return v’
    by metis_tac[esubst_ty0_always_returns, term_ok_def]
  >> simp[esubsts_ok_type_ok]
  >- (irule esubst_ty0_term_ok >> first_x_assum $ irule_at Any >> simp[])
  >> rw[]
  >- (Cases_on ‘MEM x (tm_names body1)’
      >> rw[NVARIANT_NAMES_THM])
  >> irule esubst_ty0_term_ok >> first_x_assum $ irule_at Any
  >> simp[]
QED

Theorem esubst_ty0_abs_nvariant:
  ∀x ty body subst_body body1.
    esubst_ty0 [] σ avds (Abs (Var x ty) body) = return (Abs (Var x1 (ty_esubst σ ty)) body1) ∧
    esubst_ty0 [] σ avds body = return subst_body ⇒
    (x1 = x ∨ ¬MEM x1 (tm_names subst_body))
Proof
  rw[esubst_ty0_def, try_eq_return, bind_EQ_error,
      bind_EQ_return, AllCaseEqs()] >> gvs[]
  >> metis_tac[NVARIANT_NAMES_THM]
QED

Theorem esubst_ty_abs_nvariant:
  ∀x ty body subst_body body1.
    esubsts_ok sig σ ∧
    term_ok sig (Abs (Var x ty) body) ∧
    esubst_ty σ avds (Abs (Var x ty) body) = Abs (Var x1 (ty_esubst σ ty)) body1 ∧
    esubst_ty0 [] σ avds body = return subst_body ⇒
    (x1 = x ∨ ¬MEM x1 (tm_names subst_body))
Proof
  rw[esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds (Abs (Var x ty) body) = return v’
    by metis_tac[esubst_ty0_always_returns, term_ok_def, neq_error]
  >> gvs[] >> irule esubst_ty0_abs_nvariant >> metis_tac[]
QED

Theorem equation_equality:
  l1 === r1 = l2 === r2 ⇒ l1 = l2 ∧ r1 = r2
Proof
  rw[equation_def]
QED

Theorem ACONV_equation:
  welltyped l ∧ welltyped l1 ∧
  welltyped r ∧ welltyped r1 ∧
  ACONV l l1 ∧ ACONV r r1 ⇒
  ACONV (l === r) (l1 === r1)
Proof
  rw[equation_def]
  >> drule ACONV_TYPE >> rev_drule ACONV_TYPE
  >> rw[ACONV_def] >> gvs[ACONV_def]
  >> rpt (irule $ cj 3 RACONV_rules >> rw[])
  >> metis_tac[RACONV_rules]
QED


Definition db_esubst_ty_def:
  db_esubst_ty (σ:(mlstring |-> type) # (mlstring |-> term)) (dbVar x ty) =
  dbVar x (ty_esubst σ ty) ∧
  db_esubst_ty σ (dbBound n) = dbBound n ∧
  db_esubst_ty σ (dbConst x ty) = dbConst x (ty_esubst σ ty) ∧
  db_esubst_ty σ (dbComb t1 t2) = dbComb (db_esubst_ty σ t1) (db_esubst_ty σ t2) ∧
  db_esubst_ty σ (dbAbs ty t) = dbAbs (ty_esubst σ ty) (db_esubst_ty σ t)
End

Definition db_esubst_tm_def:
  db_esubst_tm σ (dbVar x ty) = dbVar x ty ∧
  db_esubst_tm σ (dbBound n) = dbBound n ∧
  db_esubst_tm σ (dbConst x ty) = (case FLOOKUP (SND σ) x of
                                    NONE => dbConst x ty
                                  | SOME tm => db tm) ∧
  db_esubst_tm σ (dbComb t1 t2) = dbComb (db_esubst_tm σ t1) (db_esubst_tm σ t2) ∧
  db_esubst_tm σ (dbAbs ty t) = dbAbs ty (db_esubst_tm σ t)
End

Definition db_esubst_def:
  db_esubst σ tm = db_esubst_tm σ (db_esubst_ty σ tm)
End

Theorem db_esubst_ty_bind:
  ∀tm v n σ.
    (∀ty.
       dbVFREE_IN (dbVar (FST v) ty) tm ∧
       ty_esubst σ ty = ty_esubst σ (SND v) ⇒
       ty = SND v) ⇒
    db_esubst_ty σ (bind v n tm) =
    bind (FST v, ty_esubst σ (SND v)) n (db_esubst_ty σ tm)
Proof
  Induct_on ‘tm’ >> rw[]
  >- gvs[db_esubst_ty_def]
  >- (gvs[db_esubst_ty_def, AllCaseEqs()] >> rw[]
      >> Cases_on ‘v’ >> gvs[])
  >- gvs[db_esubst_ty_def]
  >- gvs[db_esubst_ty_def]
  >- (Cases_on ‘v’
      >> REWRITE_TAC[db_esubst_ty_def, bind_def]
      >> first_x_assum $ qspecl_then [‘(q, r)’, ‘n’, ‘σ’] mp_tac
      >> impl_tac
      >- metis_tac[]
      >> first_x_assum $ qspecl_then [‘(q, r)’, ‘n’, ‘σ’] mp_tac
      >> impl_tac
      >- metis_tac[]
      >> rpt DISCH_TAC
      >> ASM_REWRITE_TAC[])
  >> gvs[db_esubst_ty_def]
QED

Theorem db_esubst_ty_thm:
  ∀tm env subst_tm avds.
    esubsts_ok sig σ ∧
    term_ok sig tm ∧
    welltyped tm ∧
    (∀k v. MEM (v,k) env ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    esubst_ty0 env σ avds tm = return subst_tm ⇒
    db subst_tm = db_esubst_ty σ (db tm)
Proof
  completeInduct_on ‘sizeof tm’ >> Cases >> simp[]
  >> rw[esubst_ty0_def, AllCaseEqs(), db_esubst_ty_def]
  >- (gvs[bind_EQ_return]
      >> rename [‘typeof t1 = Fun (typeof t2) rty’]
      >> first_assum $ qspec_then ‘sizeof t1’ mp_tac
      >> first_x_assum $ qspec_then ‘sizeof t2’ mp_tac
      >> rw[] >> gvs[]
      >> metis_tac[])
  >> gvs[try_eq_return, bind_EQ_return, bind_EQ_error]
  >> rename [‘sizeof tm’, ‘db body’]
  >- (first_x_assum $ qspec_then ‘sizeof tm’ mp_tac >> impl_tac
      >> rw[]
      >> first_x_assum $ qspec_then ‘tm’ mp_tac >> impl_tac
      >- simp[]
      >> rw[]
      >> first_x_assum $ qspecl_then [‘(Var n ty,Var n (ty_esubst σ ty))::env’,
                                      ‘body’, ‘avds’] mp_tac
      >> impl_tac
      >- gvs[DISJ_IMP_THM, FORALL_AND_THM]
      >> rw[]
      >> qspecl_then [‘db tm’, ‘(n, ty)’, ‘0’, ‘σ’] mp_tac db_esubst_ty_bind
      >> impl_tac
      >- (qspecl_then [‘(Var n ty,Var n (ty_esubst σ ty))::env’, ‘σ’, ‘avds’, ‘tm’]
                     mp_tac esubst_ty0_impossible1
          >> rw[] >> gvs[DISJ_IMP_THM, FORALL_AND_THM]
          >> first_x_assum $ qspecl_then [‘n’, ‘ty_esubst σ ty'’] mp_tac
          >> ‘dbVar n ty' = db (Var n ty')’ by simp[db_def]
          >> qpat_x_assum ‘dbVar _ _ = db _’ SUBST_ALL_TAC
          >> drule_all $ iffLR dbVFREE_IN_VFREE_IN >> rw[]
          >> first_x_assum drule >> rw[] >> gvs[REV_ASSOCD_def]
          >> metis_tac[FVs_VFREE_in])
      >> rw[])
  >> gvs[AllCaseEqs(), bind_EQ_return]
  >> first_x_assum $ qspec_then ‘sizeof $ VSUBST [(Var (NVARIANT n avds body1) ty,
                                          Var n ty)] tm’
                   mp_tac >> impl_tac
  >> rw[SIZEOF_VSUBST]
  >> first_x_assum $ qspec_then ‘VSUBST [(Var (NVARIANT n avds body1) ty,
                                          Var n ty)] tm’
                   mp_tac >> impl_tac
  >> rw[SIZEOF_VSUBST]
  >> first_x_assum $ qspecl_then
                   [‘((Var (NVARIANT n avds body1) ty,
                       Var (NVARIANT n avds body1) (ty_esubst σ ty))::env)’,
                    ‘body''’, ‘avds’] mp_tac
  >> impl_tac
  >> gvs[DISJ_IMP_THM, FORALL_AND_THM, VSUBST_WELLTYPED, term_ok_VSUBST]
  >> rw[]
  >> qspecl_then [‘tm’, ‘[(Var (NVARIANT n avds body1) ty,Var n ty)]’] mp_tac VSUBST_dbVSUBST
  >> impl_tac >> simp[] >> rw[]
  >> sym_tac
  >> qspecl_then [‘db tm’, ‘(NVARIANT n avds body1, ty)’, ‘(n, ty)’, ‘0’, ‘[]’]
                 mp_tac bind_dbVSUBST_cons
  >> impl_tac >> rw[]
  >- (strip_tac >> drule $ iffLR dbVFREE_IN_bind
      >> rw[] >> rC ‘NVARIANT n avds body1 = n’
      >> cheat)
  >> cheat

(* [bind_dbVSUBST_cons, dbVFREE_IN_bind, dbVFREE_IN_VFREE_IN, esubst_ty0_impossible1,
   SIZEOF_VSUBST, VSUBST_WELLTYPED, db_esubst_ty_bind] *)
QED

Theorem db_esubst_thm:
  ∀tm env subst_tm avds.
    term_ok sig tm ∧
    welltyped tm ⇒
    db (esubst σ avds tm) = db_esubst σ (db tm)
Proof
  cheat
QED

Theorem esubst_ty_welltyped:
  ∀tm avds. term_ok sig tm ⇒ welltyped (esubst_ty σ avds tm)
Proof
  cheat
QED

Theorem esubst_ty_avds_aconv:
  ∀tm. term_ok sig tm ∧
       welltyped tm ∧
       esubsts_ok sig σ ⇒
       ACONV (esubst_ty σ avds1 tm) (esubst_ty σ avds2 tm)
Proof
  rw[]
  >> qspecl_then [‘tm’, ‘avds1’] assume_tac esubst_ty_welltyped
  >> qspecl_then [‘tm’, ‘avds2’] assume_tac esubst_ty_welltyped
  >> ‘∃v1. esubst_ty0 [] σ avds1 tm = return v1’
    by metis_tac[esubst_ty0_always_returns]
  >> ‘∃v2. esubst_ty0 [] σ avds2 tm = return v2’
    by metis_tac[esubst_ty0_always_returns]
  >> qspecl_then [‘tm’, ‘[]’, ‘v1’, ‘avds1’] assume_tac db_esubst_ty_thm
  >> qspecl_then [‘tm’, ‘[]’, ‘v2’, ‘avds2’] assume_tac db_esubst_ty_thm
  >> qspecl_then [‘v1’, ‘v2’] mp_tac ACONV_db
  >> rw[] >> gvs[] >> rw[esubst_ty_def] >> first_x_assum irule
  >> gvs[esubst_ty_def]
QED

Theorem RACONV_SYM_simple[simp]:
  RACONV [] (x, x)
Proof
  metis_tac[RACONV_REFL, EVERY_MEM, MEM]
QED


(* safe; esubst_tm can only change consts *)
Theorem esubst_tm_aconv:
  ACONV tm1 tm2 ⇒
  ACONV (esubst_tm σ tm1) (esubst_tm σ tm2)
Proof
  cheat
QED

Theorem esubst_avds_aconv:
  ∀tm. term_ok sig tm ∧
       welltyped tm ∧
       esubsts_ok sig σ ⇒
       ACONV (esubst σ avds1 tm) (esubst σ avds2 tm)
Proof
  rw[esubst_def, esubst_tm_def] >> irule esubst_tm_aconv
  >> irule esubst_ty_avds_aconv >> gvs[SF SFY_ss]
QED

(* avoids_names set into esubst_ty0 and feed inot variant.. notj ust tm_names
 so you never hit anything in*)

Theorem esubst_equation:
  esubst σ avds (tm1 === tm2) = esubst σ avds tm1 === esubst σ avds tm2
Proof
  cheat
QED

Theorem esubst_tm_abs[simp]:
  ∀v body. esubst_tm σ (Abs v body) = Abs v (esubst_tm σ body)
Proof
  rw[esubst_tm_def]
QED

Theorem esubst_avds_identity[simp]:
  esubst σ (tm_names c) c = esubst σ [] c
Proof
  cheat (* NVARIANT uses tm_names c ++ avds and only ever checks membership *)
QED

Theorem term_ok_esubst:
  theory_ok (sig, axs) ∧
  term_ok sig c ∧
  esubsts_ok sig σ ⇒
  term_ok sig (esubst σ avds tm)
Proof
  cheat
QED

Theorem theory_ok_esubst_axs:
  theory_ok (sig, axs) ∧
  esubsts_ok sig σ ⇒
  theory_ok (sig, IMAGE (esubst σ avds) axs)
Proof
  cheat
QED

Theorem esubst_ty0_env_aconv_alt:
  ∀subst_tm1 subst_tm2 env1 env2.
    esubsts_ok sig σ ∧
    term_ok sig tm1 ∧
    term_ok sig tm2 ∧
    theory_ok (thy, axs) ∧
    (∀s s'. MEM (s,s') env1 ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (ty_esubst σ ty)) ∧
    (∀s s'. MEM (s,s') env2 ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (ty_esubst σ ty)) ∧
    welltyped subst_tm1 ∧ welltyped subst_tm2 ∧
    ACONV tm1 tm2 ∧
    esubst_ty0 env1 σ avds tm1 = return subst_tm1 ∧
    esubst_ty0 env2 σ avds tm2 = return subst_tm2 ⇒
    ACONV subst_tm1 subst_tm2
Proof
  rw[]
  >> ‘welltyped tm1 ∧ welltyped tm2’ by metis_tac[term_ok_welltyped] >> rw[]
  >> dxrule_all_then (irule o iffRL) ACONV_db
  >> rpt $ dxrule db_esubst_ty_thm >> rw[]
  >> first_assum $ qspecl_then [‘tm2’, ‘env2’, ‘subst_tm2’, ‘avds’] assume_tac
  >> first_x_assum $ qspecl_then [‘tm1’, ‘env1’, ‘subst_tm1’, ‘avds’] assume_tac
  >> gvs[] >> metis_tac[ACONV_db]
QED

Theorem esubst_ty0_env_aconv:
  ∀tm subst_tm1 subst_tm2 env1 env2.
    esubsts_ok sig σ ∧
    term_ok sig tm ∧
    theory_ok (thy, axs) ∧
    (∀k v. MEM (v,k) env1 ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    (∀k v. MEM (v,k) env2 ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    welltyped subst_tm1 ∧ welltyped subst_tm2 ∧
    esubst_ty0 env1 σ avds tm = return subst_tm1 ∧
    esubst_ty0 env2 σ avds tm = return subst_tm2 ⇒
    ACONV subst_tm1 subst_tm2
Proof
  rw[]
  >> drule term_ok_welltyped >> rw[]
  >> dxrule_all_then (irule o iffRL) ACONV_db
  >> rpt $ dxrule db_esubst_ty_thm >> rw[]
  >> first_assum $ qspecl_then [‘tm’, ‘env1’, ‘subst_tm1’, ‘avds’] assume_tac
  >> first_x_assum $ qspecl_then [‘tm’, ‘env2’, ‘subst_tm2’, ‘avds’] assume_tac
  >> gvs[DISJ_IMP_THM] >> metis_tac[]
QED

Theorem esubst_ty_abs_body_aconv:
  ∀v v1 body body1 env avds.
    theory_ok (sig, axs) ∧
    esubsts_ok sig σ ∧
    term_ok sig (Abs v body) ∧
    welltyped (Abs v1 body1) ∧
    (∀k v. MEM (v,k) env ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    esubst_ty0 env σ avds (Abs v body) = return (Abs v1 body1) ⇒
    ACONV (esubst_ty σ avds body) body1
Proof
  rpt strip_tac >> drule term_ok_welltyped >> strip_tac
  >> drule_all db_esubst_ty_thm >> rw[]
  >> irule $ iffRL ACONV_db
  >> rw[] >> gvs[term_ok_def]
  >- metis_tac[term_ok_welltyped, esubsts_ok_esubst_ty_term_ok]
  >> rw[esubst_ty_def]
  >> ‘∃subst_body. esubst_ty0 [] σ avds body = return subst_body’
    by metis_tac[esubst_ty0_always_returns]
  >> rw[] >> gvs[db_esubst_ty_def]
  >> drule_at Any db_esubst_ty_thm >> simp[] >> rw[]
  >> first_x_assum $ qspec_then ‘sig’ mp_tac >> impl_tac
  >> simp[] >> rw[]
  >> cheat
QED

Theorem esubst_ty_abs_body_aconv_simple:
  ∀v v1 body body1 avds.
    theory_ok (sig, axs) ∧
    esubsts_ok sig σ ∧
    term_ok sig (Abs v body) ∧
    welltyped (Abs v1 body1) ∧
    esubst_ty σ avds (Abs v body) = Abs v1 body1 ⇒
    ACONV (esubst_ty σ avds body) body1
Proof
  rw[] >> qspecl_then [‘Var x ty’, ‘Var n ty'’, ‘body’, ‘body1’, ‘[]’, ‘avds’]
                      mp_tac esubst_ty_abs_body_aconv
  >> impl_tac
  >> rw[] >> gvs[esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds (Abs (Var x ty) body) = return v’
    by metis_tac[term_ok_def, esubst_ty0_always_returns]
  >> gvs[]
QED

Theorem ACONV_ABS:
  ∀x ty t1 t2.
    welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 ⇒
    ACONV (Abs (Var x ty) t1) (Abs (Var x ty) t2)
Proof
  rpt strip_tac
  >> irule o iffRL $ ACONV_db
  >> rw[] >> metis_tac[ACONV_db]
QED

Triviality esubst_BETA_db_eq:
  theory_ok (sig, axs) ∧
  type_ok (tysof sig) ty ∧
  term_ok sig t ∧
  esubsts_ok sig σ ∧
  esubst σ [] (Comb (Abs (Var x ty) t) t) =
  Comb (esubst σ [] (Abs (Var x ty) t)) (esubst σ [] t) ∧
  esubst_ty σ [] (Abs (Var x ty) t) =
  Abs (Var x1 (ty_esubst σ ty)) body1 ⇒
  db (Comb (Abs (Var x1 (ty_esubst σ ty)) (esubst_tm σ body1))
           (Var x (ty_esubst σ ty)) === esubst_tm σ (esubst_ty σ [] t)) =
  db (Comb (Abs (Var x1 (ty_esubst σ ty)) (esubst_tm σ body1))
           (Var x1 (ty_esubst σ ty)) === esubst_tm σ body1)
Proof
  rw[equation_def]
  >> cheat
QED

Triviality esubst_abs_typeof_eq:
  esubst_ty σ [] (Abs (Var x ty) t) =
  Abs (Var x1 (ty_esubst σ ty)) body1 ⇒
  typeof (esubst_tm σ (esubst_ty σ [] t)) =
  typeof (esubst_tm σ body1)
Proof
  cheat
QED

Theorem nproves_substitutable_ABS:
  (∀m. m < n + 1 ⇒
       ∀h' c.
         ((sig,axs),h',m) |n- c ⇒
         ((sig,IMAGE (esubst σ []) axs),MAP (esubst σ []) h',m) |n-
         esubst σ (FLAT (MAP tm_names h')) c) ∧
  theory_ok (sig, axs) ∧
  EVERY ($¬ ∘ VFREE_IN (Var x ty)) h ∧
  type_ok (tysof sig) ty ∧
  ((sig,axs),h,n) |n- l === r ∧
  esubsts_ok sig σ ⇒
  ((sig,IMAGE (esubst σ []) axs),MAP (esubst σ []) h,n + 1) |n-
  esubst σ (FLAT (MAP tm_names h)) (Abs (Var x ty) l === Abs (Var x ty) r)
Proof
  rw[]
  >> qabbrev_tac ‘avds=FLAT (MAP tm_names h)’
  >> first_x_assum $ qspec_then ‘n’ mp_tac >> impl_tac >> simp[]
  >> rw[]
  >> first_x_assum $ drule_then strip_assume_tac
  >> gvs[esubst_equation]
  >> drule_at Any nproves_ABS >> rw[]
  >> rev_drule nproves_term_ok
  >> drule theory_ok_sig
  >> rw[term_ok_equation]
  >> ‘term_ok sig (Abs (Var x ty) l)’ by simp[term_ok_def]
  >> drule_then dxrule esubst_ty_abs_avoids
  >> ‘term_ok sig (Abs (Var x ty) r)’ by simp[term_ok_def]
  >> drule_then dxrule esubst_ty_abs_avoids
  >> rw[esubst_def, esubst_tm_def]
  >> rpt $ first_x_assum (qspec_then ‘avds’ assume_tac) >> gvs[]
  >> rw[]
  >- (irule nproves_ABS >> rw[esubsts_ok_type_ok]
      >- cheat
      >> qspecl_then [‘Var x ty’, ‘Var x (ty_esubst σ ty)’, ‘l’, ‘body1’, ‘avds’]
                     mp_tac esubst_ty_abs_body_aconv_simple
      >> impl_tac
      >- (simp[term_ok_def] >> irule term_ok_welltyped >> cheat)
      >> qspecl_then [‘Var x ty’, ‘Var x (ty_esubst σ ty)’, ‘r’, ‘body1'’, ‘avds’]
                     mp_tac esubst_ty_abs_body_aconv_simple
      >> impl_tac
      >- (simp[term_ok_def] >> irule term_ok_welltyped >> cheat)
      >> rw[]
      >> rpt $ dxrule esubst_tm_aconv
      >> qspecl_then [‘esubst σ avds r’, ‘esubst_tm σ body1'’,
                      ‘esubst σ avds l’, ‘esubst_tm σ body1’] mp_tac $
                     GEN_ALL ACONV_equation
      >> impl_tac
      >- (cheat)
      >> rw[]
      >> irule nproves_ACONV >> rw[]
      >- cheat
      >- (irule term_ok_welltyped >> gvs[theory_ok_def]
          >> qexists ‘sig’ >> drule_then (irule o iffRL) term_ok_equation
          >> cheat)
      >- (rw[EVERY_MEM, MEM_MAP] >> cheat)
      >> first_x_assum $ irule_at Any >> rw[ACONV_SYM]
      >> rw[EVERY_MEM, MEM_MAP, EXISTS_MEM]
      >> metis_tac[ACONV_REFL])
  >- (first_x_assum $ qspecl_then [‘ty_esubst σ ty’, ‘x’] mp_tac >> impl_tac
      >> rw[ty_esubst_type_ok_alt]
      >- cheat
      >> drule_then irule nproves_ACONV >> rw[]
      >- cheat
      >- cheat
      >- (irule ACONV_equation >> rw[]
          >- cheat
          >- cheat
          >- cheat
          >- cheat
          >- (irule ACONV_ABS
              >> rw[] >- cheat >- cheat
              >> rw[esubst_def] >> irule esubst_tm_aconv
              >> irule esubst_ty_abs_body_aconv_simple
              >> rpt $ first_x_assum (irule_at Any)
              >> rw[term_ok_def]
              >- cheat)
          >> cheat)
      >> cheat)
  >- cheat
  >> cheat
QED

Theorem nproves_substitutable_BETA:
  theory_ok (sig,axs) ∧
  type_ok (tysof sig) ty ∧
  term_ok sig t ∧
  esubsts_ok sig σ ⇒
  ((sig,IMAGE (esubst σ []) axs),[],0) |n-
  esubst σ [] (Comb (Abs (Var x ty) t) (Var x ty) === t)
Proof
  rw[esubst_equation]
  >> ‘term_ok sig $ Abs (Var x ty) t’ by simp[term_ok_def]
  >> drule esubst_comb >> rw[]
  >> first_x_assum $ qspecl_then [‘[]’, ‘Abs (Var x ty) t’, ‘t’] mp_tac
  >> rw[] >> rw[esubst_def]
  >> qspecl_then [‘x’, ‘ty’, ‘t’, ‘[]’] mp_tac esubst_ty_abs_avoids_full
  >> impl_tac
  >- simp[]
  >> rw[] >> gvs[esubst_tm_def]
  >> irule nproves_ACONV >> simp[]
  >> rw[]
  >- (irule term_ok_welltyped >> qexists ‘sig’ >> rw[term_ok_def]
      >> irule o iffRL $ term_ok_equation >> drule theory_ok_sig >> rw[]
      >> metis_tac[esubsts_ok_esubst_tm_term_ok, esubsts_ok_esubst_ty_term_ok,
                   term_ok_welltyped, esubst_abs_typeof_eq, esubst_def])
  >- (irule_at Any $ iffRL ACONV_db
      >> qexists ‘Comb (Abs (Var x1 (ty_esubst σ ty)) (esubst_tm σ body1))
                  (Var x (ty_esubst σ ty)) === esubst_tm σ body1’
      >> rw[]
      >- (irule term_ok_welltyped >> qexists ‘sig’ >> rw[term_ok_def]
          >> irule o iffRL $ term_ok_equation >> drule theory_ok_sig >> rw[]
          >> metis_tac[esubsts_ok_esubst_tm_term_ok, esubsts_ok_esubst_ty_term_ok,
                       term_ok_welltyped, esubst_abs_typeof_eq, esubst_def])
      >- (irule term_ok_welltyped >> qexists ‘sig’ >> rw[term_ok_def]
          >> irule o iffRL $ term_ok_equation >> drule theory_ok_sig >> rw[]
          >> metis_tac[esubsts_ok_esubst_tm_term_ok, esubsts_ok_esubst_ty_term_ok,
                       term_ok_welltyped, esubst_abs_typeof_eq, esubst_def])
      >> cheat)
  >- (irule term_ok_welltyped >> qexists ‘sig’ >> rw[term_ok_def]
      >> irule o iffRL $ term_ok_equation
      >> drule theory_ok_sig >> strip_tac >> gvs[]
      >> rw[]
      >- (gvs[esubst_def] >> irule esubst_abs_typeof_eq >> rw[]
          >> gvs[esubsts_ok_esubst_tm_term_ok, term_ok_welltyped]
          >> metis_tac[esubsts_ok_esubst_tm_term_ok, term_ok_welltyped,
                       esubsts_ok_esubst_ty_term_ok])
      >- simp[esubsts_ok_esubst_tm_term_ok]
      >- metis_tac[esubsts_ok_esubst_tm_term_ok, term_ok_welltyped]
      >> irule esubsts_ok_esubst_tm_term_ok
      >> simp[] >> irule esubst_ty0_term_ok
      >> qexistsl [‘[]’, ‘[]’, ‘t’, ‘σ’] >> rw[esubst_ty_def]
      >> CASE_TAC >> metis_tac[esubst_ty0_always_returns, neq_error])
  >- (rw[equation_def] >- cheat)
  >> cheat
QED

Theorem nproves_substitutable_DEDUCT_ANTISYM:
  (∀m'.
     m' < m + (n + 1) ⇒
     ∀h c.
       ((sig,axs),h,m') |n- c ⇒
       ((sig,IMAGE (esubst σ []) axs),MAP (esubst σ []) h,m') |n-
       esubst σ (FLAT (MAP tm_names h)) c) ∧
  theory_ok (sig, axs) ∧
  ((sig, axs), h1, n) |n- c1 ∧
  ((sig, axs), h2, m) |n- c2 ∧
  esubsts_ok sig σ ⇒
  ((sig,IMAGE (esubst σ []) axs),
        MAP (esubst σ [])
            (term_union (term_remove c2 h1) (term_remove c1 h2)),m + (n + 1))
  |n-
   esubst σ (FLAT (MAP tm_names
                       (term_union (term_remove c2 h1) (term_remove c1 h2))))
          (c1 === c2)
Proof
  rw[esubst_equation]
  >> first_assum $ qspec_then ‘n’ mp_tac >> impl_tac
  >- simp[]
  >> strip_tac
  >> first_x_assum $ qspecl_then [‘h1’, ‘c1’] mp_tac >> impl_tac >- simp[]
  >> strip_tac
  >> first_x_assum $ qspec_then ‘m’ mp_tac >> impl_tac
  >- simp[]
  >> strip_tac
  >> first_x_assum $ qspecl_then [‘h2’, ‘c2’] mp_tac >> impl_tac >- simp[]
  >> rw[]
  >> qabbrev_tac ‘avds1=(FLAT (MAP tm_names (term_union (term_remove c2 h1) (term_remove c1 h2))))’
  >> qabbrev_tac ‘avds2=FLAT (MAP tm_names h1)’
  >> qabbrev_tac ‘avds3=FLAT (MAP tm_names h2)’
  >> qabbrev_tac ‘axs'=IMAGE (esubst σ []) axs’
  >> qspecl_then [‘esubst σ avds2 c1’, ‘esubst σ avds3 c2’,
                  ‘MAP (esubst σ []) h1’, ‘MAP (esubst σ []) h2’,
                  ‘m’, ‘n’,
                  ‘(sig,axs')’] mp_tac nproves_DEDUCT_ANTISYM
  >> rw[]
  >> irule nproves_ACONV
  >> rw[]
  >- cheat (* hypset ok after esubst mapping :( *)
  >- cheat
  >- (rw[EVERY_MEM] >> cheat)
  >> first_x_assum $ irule_at Any >> rw[]
  >- (irule ACONV_equation >> rw[]
      >- cheat >- cheat >- cheat >- cheat
      >> irule esubst_avds_aconv
      >> metis_tac[term_ok_welltyped, nproves_term_ok])
  >> rw[EVERY_MEM, EXISTS_MEM]
  >> cheat
QED

Theorem nproves_substitutable:
  ∀h c n.
    theory_ok (sig, axs) ∧
    ((sig, axs), h, n:num) |n- c ∧
    esubsts_ok sig σ ⇒
    ((sig, IMAGE (esubst σ []) axs), MAP (esubst σ []) h, 2*n)
    |n- esubst σ (FLAT (MAP tm_names h)) c
Proof
  completeInduct_on ‘n’
  >> simp[Once nproves_cases, SimpL “$==>”]
  >> rw[] >> gvs[]
  >- simp[nproves_substitutable_ABS]
  >- (irule nproves_ASSUME >> rw[]
      >> metis_tac[esubst_has_type_bool, theory_ok_esubst_axs,
                   term_ok_esubst])
  >- simp[nproves_substitutable_BETA]
  >- simp[nproves_substitutable_DEDUCT_ANTISYM]
  >- (rename [‘n + 1’] >> first_assum $ qspec_then ‘n’ mp_tac >> impl_tac
      >- simp[] >> strip_tac >> first_x_assum $ qspecl_then [‘h1’, ‘p === c’] mp_tac
      >- simp[] >> strip_tac >> first_x_assum drule >> strip_tac
      >> first_x_assum $ qspec_then ‘m’ mp_tac >> impl_tac >> rw[]
      >> first_x_assum $ qspecl_then [‘h2’, ‘p'’] mp_tac
      >> rw[] >> gvs[esubst_equation] >> irule nproves_EQ_MP)
  >- cheat
  >- cheat
  >- cheat
  >- (rw[esubst_equation] >> irule nproves_REFL >> rw[]
      >> metis_tac[theory_ok_esubst_axs, term_ok_esubst])
  >- (irule nproves_axioms >> rw[]
      >> irule theory_ok_esubst_axs >> rw[])
QED

Theorem proves_substitutable:
  ∀sig axs h c.
    theory_ok (sig,axs) ∧
    ((sig, axs), h) |- c ∧
    esubsts_ok sig σ ⇒
    ((sig, IMAGE (esubst σ []) axs), MAP (esubst σ []) h)
    |- esubst σ (FLAT (MAP tm_names h)) c
Proof
  rw[] >> qspecl_then [‘h’, ‘c’] mp_tac nproves_substitutable
  >> rw[] >> metis_tac[nproves_proves]
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

val _ = export_theory()
