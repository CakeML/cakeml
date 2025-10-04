(*
  Some lemmas about the extended Little Theories syntactic functions.
*)
open preamble totoTheory comparisonTheory ternaryComparisonsTheory mlstringTheory
              holSyntaxLibTheory holSyntaxTheory errorMonadTheory
              littleTheoriesSyntaxTheory holSyntaxExtraTheory

val _ = new_theory"littleTheoriesSyntaxOldSystem"

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

Theorem esubst_ty0_preserves_fvs:
  ∀env σ avds tm subst_tm.
    esubsts_ok sig σ ∧
    term_ok sig tm ∧
    (∀k v. MEM (v, k) env ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    esubst_ty0 env σ avds tm = return subst_tm ⇒
    (∀n ty. (n, ty) ∈ FVs tm ∧
            ¬(∃v. MEM (v, Var n (ty_esubst σ ty)) env) ⇒
            (n, ty_esubst σ ty) ∈ FVs subst_tm)
Proof
  recInduct esubst_ty0_ind >> rpt strip_tac
  >- gvs[esubst_ty0_def, AllCaseEqs()]
  >- gvs[esubst_ty0_def, AllCaseEqs()]
  >- gvs[esubst_ty0_def, AllCaseEqs(), bind_EQ_return, term_ok_def]
  >> gvs[term_ok_def]
  >> gvs[esubst_ty0_def, AllCaseEqs(), bind_EQ_return, try_eq_return, bind_EQ_error]
  >- (last_x_assum kall_tac >> conj_tac
      >- (first_x_assum irule >> simp[DISJ_IMP_THM, FORALL_AND_THM]
          >> rpt strip_tac >> gvs[]
          >> qspec_then ‘(Var n ty',Var n (ty_esubst σ ty'))::env’
                        mp_tac esubst_ty0_impossible1
          >> disch_then $ drule_then mp_tac o cj 2
          >> disch_then $ qspecl_then [‘avds’, ‘body’, ‘n’, ‘ty’, ‘ty'’] mp_tac
          >> impl_tac
          >- gvs[DISJ_IMP_THM, FORALL_AND_THM, REV_ASSOCD_def]
          >> metis_tac[neq_error])
      >> rpt strip_tac >> gvs[]
      >> qspec_then ‘(Var n ty',Var n (ty_esubst σ ty'))::env’
                    mp_tac esubst_ty0_impossible1
      >> disch_then $ drule_then mp_tac o cj 2
      >> disch_then $ qspecl_then [‘avds’, ‘body’, ‘n’, ‘ty’, ‘ty'’] mp_tac
      >> impl_tac
      >- gvs[DISJ_IMP_THM, FORALL_AND_THM, REV_ASSOCD_def]
      >> metis_tac[neq_error])
  >> last_x_assum mp_tac >> disch_then $ qspecl_then [‘body1’, ‘body''’] mp_tac
  >> impl_tac >- simp[DISJ_IMP_THM, FORALL_AND_THM, term_ok_vsubst_variant]
  >> disch_then $ qspecl_then [‘n’, ‘ty’] mp_tac >> impl_tac
  >- (simp[] >> conj_tac
      >- metis_tac[FVs_VSUBST_CASES]
      >> strip_tac >> first_x_assum drule
      >> metis_tac[NVARIANT_NAMES_THM, FVs_in_tm_names])
  >> strip_tac >> first_x_assum drule
  >> metis_tac[NVARIANT_NAMES_THM, FVs_in_tm_names]
QED

Theorem esubst_ty0_preserves_vfree_in:
  ∀env σ avds tm subst_tm.
    esubsts_ok sig σ ∧
    term_ok sig tm ∧
    (∀k v. MEM (v, k) env ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
    esubst_ty0 env σ avds tm = return subst_tm ⇒
    (∀n ty. VFREE_IN (Var n ty) tm ∧
            ¬(∃v. MEM (v, Var n (ty_esubst σ ty)) env) ⇒
            VFREE_IN (Var n (ty_esubst σ ty)) subst_tm)
Proof
  rw[] >> qsuff_tac ‘(n,ty_esubst σ ty) ∈ FVs subst_tm’
  >- metis_tac[FVs_VFREER_in]
  >> irule esubst_ty0_preserves_fvs >> metis_tac[FVs_VFREE_in]
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
  >- (rC ‘FLOOKUP tys tyn’ >> metis_tac[IN_FRANGE_FLOOKUP])
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

Triviality ty_esubst_TYPE_SUBST_aux:
  ∀ty i. esubsts_ok (tys, tms) σ ∧
         type_ok tys (TYPE_SUBST i ty) ⇒
         ty_esubst σ (TYPE_SUBST i ty) =
         TYPE_SUBST (MAP (λ(v,k). (ty_esubst σ v,k)) i) (ty_esubst σ ty)
Proof
  Induct_on ‘ty’ using type_ind
  >- (rw[ty_esubst_def, TYPE_SUBST_def, REV_ASSOCD_MAP]
      >> Cases_on ‘REV_ASSOCD (Tyvar m) i (Tyvar m) = Tyvar m’
      >> simp[ty_esubst_def]
      >> drule rev_assocd_neq_mem
      >> metis_tac[])
  >> Cases_on ‘l’
  >- (Cases_on ‘σ’ >> rename [‘(σ, θ)’] >> gvs[esubsts_ok_def]
      >> rw[ty_esubst_def, TYPE_SUBST_def]
      >> CASE_TAC >> simp[TYPE_SUBST_def]
      >> gvs[type_ok_def]
      >> metis_tac[monomorphic_type_subst, IN_FRANGE_FLOOKUP])
  >> gvs[EVERY_MEM] >> rw[]
  >> ‘type_ok tys (TYPE_SUBST i h)’ by gvs[type_ok_def]
  >> gvs[type_ok_def, EVERY_MEM]
  >> ‘∀ty. MEM ty t ⇒ type_ok tys (TYPE_SUBST i ty)’
    by metis_tac[MEM_MAP]
  >> simp[TYPE_SUBST_def, ty_esubst_def, MAP_MAP_o, MAP_CONG]
QED

Theorem ty_esubst_TYPE_SUBST:
  ∀ty i. esubsts_ok (tys, tms) σ ∧
         type_ok tys (TYPE_SUBST i ty) ⇒
         is_instance (ty_esubst σ ty) (ty_esubst σ (TYPE_SUBST i ty))
Proof
  rpt strip_tac
  >> qexists ‘MAP (λ(v, k). (ty_esubst σ v, k)) i’
  >> metis_tac[ty_esubst_TYPE_SUBST_aux]
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

Theorem esubst_ty_term_ok:
  ∀σ avds tm subst_tm.
    term_ok sig tm ∧
    esubsts_ok sig σ ⇒
    term_ok (esubst_sig σ sig) (esubst_ty σ avds tm)
Proof
  rw[esubst_ty_def]
  >> ‘∃tm1. esubst_ty0 [] σ avds tm = return tm1’ by metis_tac[esubst_ty0_always_returns]
  >> simp[] >> metis_tac[MEM, esubst_ty0_term_ok]
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
      >> metis_tac[IN_FRANGE_FLOOKUP])
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

Theorem welltyped_comb:
  welltyped l1 ∧
  welltyped l2 ∧
  typeof l1 = Fun (typeof l2) rty ⇒
  welltyped (Comb l1 l2)
Proof
  rw[welltyped_def]
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
    theory_ok (sig, axs) ∧
    esubsts_ok sig σ ∧
    term_ok sig (l === r) ⇒
    esubst σ avds (l === r) has_type Bool
Proof
  rpt strip_tac >> irule esubst_has_type_bool
  >> simp[EQUATION_HAS_TYPE_BOOL] >> rw[]
  >> drule_then assume_tac theory_ok_sig
  >> drule $ iffLR term_ok_equation >> rw[]
  >> first_x_assum drule
  >- gvs[equation_def, term_ok_def]
  >- gvs[equation_def, term_ok_def]
  >> metis_tac[]
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

Theorem nproves_ACONV_concl1:
  ∀thy h n c c'.
    (thy,h,n-1) |n- c ∧ welltyped c' ∧ ACONV c c' ∧ n > 0 ⇒
    (thy,h,n) |n- c'
Proof
  rw[] >> drule_all nproves_ACONV_concl >> simp[]
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

Theorem EL_APPEND_LE:
  ∀n pfx lst. n < LENGTH pfx ⇒ EL n (pfx ++ lst) = EL n pfx
Proof
  Induct_on ‘n’ >> rw[]
  >> Cases_on ‘pfx’ >> gvs[LENGTH]
QED

Triviality PRE_plus_one[simp]:
  ∀k. PRE (k + 1) = k
Proof
  simp[]
QED

Triviality nproves_term_ok1:
  ∀thyh c.
    thyh |n- c ⇒
    hypset_ok (FST (SND thyh)) ∧
    EVERY (λp. term_ok (sigof (FST thyh)) p ∧ p has_type Bool)
          (c::(FST (SND thyh)))
Proof
  ntac 3 strip_tac >> PairCases_on ‘thyh’
  >> rename [‘(thy,hyps,n)’]
  >> Cases_on ‘∃n. (thy,hyps,n) |n- c’
  >- (qspecl_then [‘thy’, ‘hyps’, ‘c’] mp_tac $ iffRL nproves_proves
      >> strip_tac >> first_x_assum drule >> strip_tac >> drule proves_term_ok
      >> rw[])
  >> metis_tac[nproves_proves]
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
  >> imp_res_tac nproves_term_ok1 >> fs[hypset_ok_cons]
  >- (first_x_assum $ irule_at Any >> simp[])
  >> Cases_on ‘EXISTS (ACONV h) hyps’
  >- (‘∃h0 hr. hyps = h0::hr ∧ ACONV h h0’ by (
       Cases_on ‘hyps’ >> simp[] >> fs[ACONV_SYM, EXISTS_MEM]
       >> ‘alpha_lt h' e'’ by fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM]
       >> ‘alpha_lt h e’ by fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM]
       >> ‘alpha_lt e e'’ by metis_tac[alpha_lt_trans_ACONV,ACONV_SYM]
       >> ‘alpha_lt h e'’ by metis_tac[transitive_alpha_lt,transitive_def]
       >> fs[alpha_lt_def,ACONV_eq_orda] >> metis_tac[])
      >> rw[]
      >> qspecl_then [‘thy’, ‘pfx++h0::hr’, ‘c’, ‘h’] mp_tac nproves_addAssum
      >> imp_res_tac WELLTYPED_LEMMA >> simp[]
      >> qspecl_then [‘pfx’, ‘h’, ‘h0’, ‘hr’] mp_tac term_union_replace
      >> impl_tac
      >- (simp[EVERY_MEM, MEM_EL, PULL_EXISTS]
          >> rpt $ qpat_x_assum ‘EVERY P (X::Y)’ kall_tac >> rw[]
          >> fs[hypset_ok_el_less]
          >- (first_x_assum $ qspecl_then[‘n'’, ‘LENGTH pfx’] mp_tac
              >> simp[EL_LENGTH_APPEND_rwt, EL_CONS, EL_APPEND1, EL_APPEND2]
              >> metis_tac[ACONV_SYM, alpha_lt_trans_ACONV])
          >> first_x_assum $ qspecl_then
                           [‘LENGTH pfx’, ‘LENGTH pfx + SUC n'’] mp_tac
          >> simp[EL_LENGTH_APPEND_rwt, EL_CONS, EL_APPEND1, EL_APPEND2]
          >> metis_tac[ACONV_SYM, alpha_lt_trans_ACONV])
      >> disch_then SUBST1_TAC >> strip_tac
      >> first_x_assum $ qspecl_then [‘pfx ++ [h]’, ‘hr’] mp_tac
      >> first_x_assum drule
      >> ‘h::hr=[h]++hr’ by simp[] >> first_x_assum SUBST_ALL_TAC
      >> simp[APPEND_ASSOC] >> ntac 2 strip_tac
      >> first_x_assum drule
      >> impl_tac
      >- (conj_tac >- metis_tac[CONS_APPEND,APPEND_ASSOC]
          >> qpat_x_assum ‘EVERY P1 X’ kall_tac
          >> qmatch_assum_abbrev_tac ‘EVERY P (h0::hr)’
          >> qpat_x_assum ‘EXISTS X (h0::hr)’ kall_tac
          >> fs[EVERY_MEM] >> rw[]
          >> ‘P x’ by res_tac >> pop_assum mp_tac
          >> qpat_x_assum ‘P h0’ kall_tac
          >> simp_tac std_ss [Abbr‘P’]
          >> strip_tac
          >> fs[hypset_ok_el_less,MEM_EL,PULL_EXISTS]
          >> first_x_assum $ qspecl_then[‘LENGTH pfx’, ‘LENGTH pfx + SUC n'’] mp_tac
          >> simp[EL_APPEND2] >> strip_tac
          >> ‘ACONV h0 x’ by metis_tac[ACONV_TRANS,ACONV_SYM]
          >> rfs[ACONV_eq_orda,alpha_lt_def])
      >> rw[] >> qexists ‘m'’ >> simp[] >> metis_tac[CONS_APPEND, APPEND_ASSOC])
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
  >> qspecl_then [‘thy’,‘pfx ++ hyps’,‘c’,‘h’,‘n’] mp_tac nproves_addAssum
  >> rw[] >> first_x_assum $ qspec_then ‘n’ assume_tac >> gvs[]
  >> qspecl_then [‘pfx’, ‘h’, ‘hyps’] mp_tac term_union_insert
  >> impl_tac
  >- (fs[EVERY_MEM,EXISTS_MEM]
      >> conj_tac
      >- (rw[] >> qpat_x_assum ‘hypset_ok (pfx ++ h::hyps')’ mp_tac
          >> simp[hypset_ok_el_less,MEM_EL,PULL_EXISTS]
          >> fs[MEM_EL,PULL_EXISTS]
          >> disch_then $ qspecl_then[‘n'’, ‘LENGTH pfx’] mp_tac
          >> simp[EL_APPEND2, EL_APPEND1])
      >> rw[] >> last_x_assum $ qspec_then ‘z’ mp_tac >> simp[]
      >> strip_tac >- metis_tac[ACONV_SYM]
      >> fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM] >> rw[] >> fs[]
      >> metis_tac[ACONV_SYM,alpha_lt_trans_ACONV])
  >> disch_then SUBST1_TAC
  >> first_x_assum (qspec_then ‘pfx ++ [h]’ mp_tac)
  >> disch_then (qspec_then ‘hyps’ mp_tac)
  >> disch_then (qspec_then ‘m'’ mp_tac)
  >> impl_tac >> simp[APPEND_ASSOC_CONS]
  >- metis_tac[ACONV_SYM]
  >> strip_tac >> first_x_assum $ irule_at Any >> simp[]
QED

Theorem nproves_ACONV:
  ∀thy h' c' h c n.
    (thy,h,n) |n- c ∧ welltyped c' ∧ ACONV c c' ∧ hypset_ok h' ∧
    EVERY (λx. EXISTS (ACONV x) h') h ∧
    EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) h' ⇒
    ∃m. m ≤ n + (LENGTH h' * 3) + 1 ∧ (thy, h', m) |n- c'
Proof
  rw[]
  >> qspecl_then [‘thy’, ‘c’, ‘h'’, ‘[]’, ‘h’, ‘n’] mp_tac nproves_ACONV_lemma
  >> simp[]
  >> rw[] >> qexists ‘m + 1’ >> simp[]
  >> metis_tac[nproves_ACONV_concl]
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
  >- (simp[ty_esubst_type_ok_alt] >> irule esubst_ty0_term_ok
      >> simp[] >> first_x_assum $ irule_at Any >> simp[])
  >> simp[ty_esubst_type_ok_alt] >> irule esubst_ty0_term_ok
  >> simp[] >> first_x_assum $ irule_at Any
  >> simp[term_ok_vsubst_variant]
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

val contrapos_tac = CONV_TAC (REWR_CONV (DECIDE “p ⇒ q ⇔ ¬q ⇒ ¬p”)) THEN strip_tac

Theorem esubst_ty0_var_type_thm:
  ∀n tm env.
    welltyped tm ∧ (sizeof tm = n) ∧ term_ok sig tm ∧
    esubsts_ok sig σ ∧
    (∀s s'. MEM (s,s') env ⇒
            ∃x ty. (s = Var x ty) ∧
                   (s' = Var x (ty_esubst σ ty)))
    ⇒ (∃x ty. (esubst_ty0 env σ avds tm = error (Var x (ty_esubst σ ty))) ∧
              VFREE_IN (Var x ty) tm ∧
              REV_ASSOCD (Var x (ty_esubst σ ty))
                         env (Var x ty) ≠ Var x ty)
      ∨ (∀x ty. VFREE_IN (Var x ty) tm
                ⇒ REV_ASSOCD (Var x (ty_esubst σ ty))
                             env (Var x ty) = Var x ty) ∧
        (∃tm'. esubst_ty0 env σ avds tm = return tm' ∧
               tm' has_type (ty_esubst σ (typeof tm)) ∧
               (∀u uty. VFREE_IN (Var u uty) tm' ⇔
                          ∃oty. VFREE_IN (Var u oty) tm ∧
                                uty = ty_esubst σ oty))
Proof
  gen_tac >> completeInduct_on ‘n’ >>
  Induct >> simp[Once esubst_ty0_def] >>
  TRY (
    simp[Once esubst_ty0_def] >>
    simp[Once has_type_cases] >>
    NO_TAC )
  >- (
    pop_assum kall_tac >> rw[] >>
    simp[Once esubst_ty0_def] >>
    simp[Once has_type_cases] >>
    metis_tac[] )
  >- (rpt gen_tac >> strip_tac >>
      fs[] >> BasicProvers.VAR_EQ_TAC >>
      fsrw_tac[ARITH_ss][] >>
      simp[Once esubst_ty0_def, bind_EQ_return, bind_EQ_error] >>
      first_assum(qspec_then‘sizeof tm’mp_tac) >>
      first_x_assum(qspec_then‘sizeof tm'’ mp_tac) >> simp[] >>
      disch_then(qspecl_then[‘tm'’, ‘env’]mp_tac) >> simp[] >>
      qmatch_abbrev_tac‘P ⇒ Q’ >> strip_tac >>
      qunabbrev_tac‘Q’ >>
      disch_then(qspecl_then[‘tm’,‘env’]mp_tac) >>
      simp[] >>
      qunabbrev_tac‘P’ >>
      reverse (strip_tac >> fs[])
      >- (simp[Once has_type_cases] >> gvs[ty_esubst_def] >> metis_tac[])
      >> metis_tac[])
  >> rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >>
    BasicProvers.VAR_EQ_TAC >> qmatch_assum_rename_tac`welltyped tm` >>
    fsrw_tac[ARITH_ss][] >>
    Q.PAT_ABBREV_TAC`env' = X::env` >>
    ‘∃v. esubst_ty0 [] σ avds tm = return v’ by metis_tac[esubst_ty0_always_returns]
    >> gvs[]
    >> qabbrev_tac ‘env' = (Var (NVARIANT n' avds v) ty,
                            Var (NVARIANT n' avds v) (ty_esubst σ ty))::env’
    >> qabbrev_tac ‘tm' = VSUBST [(Var (NVARIANT n' avds v) ty,Var n' ty)] tm’
    >> ‘sizeof tm' = sizeof tm’ by simp[Abbr`tm'`,SIZEOF_VSUBST] >>
    `welltyped tm'` by (
      simp[Abbr`tm'`] >>
      match_mp_tac VSUBST_WELLTYPED >>
      simp[] >> simp[Once has_type_cases] ) >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    simp[Once esubst_ty0_def] >>
    disch_then(fn th =>
      qspecl_then[`tm`,`env'`]mp_tac th >>
      qspecl_then[`tm'`,`env''`]mp_tac th >>
      qspecl_then[`tm`,`[]`]mp_tac th) >> simp[] >>
    qmatch_abbrev_tac`a ⇒ b` >> strip_tac >> qunabbrev_tac`b` >>
    qmatch_abbrev_tac`(p ⇒ q) ⇒ r` >>
    `p` by (
      unabbrev_all_tac >> rw[] >> metis_tac[term_ok_vsubst_variant]) >>
    simp[] >> map_every qunabbrev_tac[`p`,`q`,`r`] >> pop_assum kall_tac >>
    qmatch_abbrev_tac`x ⇒ (p ⇒ q) ⇒ r` >>
    `p` by (
      unabbrev_all_tac >> rw[] >> metis_tac[]) >>
    simp[] >> map_every qunabbrev_tac[`x`,`p`,`q`,`r`] >> pop_assum kall_tac >>
    qunabbrev_tac`a` >> fs[]
    >>
    strip_tac >> fs[] >- (
      strip_tac >> fs[] >- (
        rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
        rw[] >> fs[] >>
        BasicProvers.EVERY_CASE_TAC >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[]
        >- metis_tac[NVARIANT_THM]
        >> simp[try_def, AllCaseEqs()] >> metis_tac[NVARIANT_THM]) >>
      rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
      simp[Once has_type_cases] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      rw[] >> fs[] >>
      metis_tac[NVARIANT_THM,term_11]) >>
  strip_tac >> fs[]

  >- (simp[try_def, AllCaseEqs()]
      >> Cases_on ‘x = n'’
      >- (Cases_on ‘ty_esubst σ ty' = ty_esubst σ ty’
          >> simp[Once has_type_cases, ty_esubst_def]
          >> rw[]
          >- (qsuff_tac ‘VFREE_IN (Var x' ty'') tm'’
              >- (gvs[Abbr‘env''’, REV_ASSOCD, AllCaseEqs()]
                  >> qpat_x_assum ‘∀x ty. _ ⇒ _’ mp_tac
                  >> metis_tac[NVARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED])
              >> simp[Abbr‘tm'’] >> ‘Var x' ty'' ≠ Var n' ty’ by simp[]
              >> irule $ iffRL VFREE_IN_VSUBST >> simp[REV_ASSOCD, AllCaseEqs()]
              >> metis_tac[VFREE_IN_def])
          >- (gvs[Abbr‘tm'’]
              >> qspecl_then [‘tm’, ‘[(Var (NVARIANT n' avds v) ty,Var n' ty)]’]
                             mp_tac typeof_vsubst >> impl_tac
              >- simp[] >> metis_tac[])
          >- (rw[EQ_IMP_THM] >> gvs[Abbr‘tm'’]
              >- (qexists ‘oty’ >> rw[]
                  >- (strip_tac >> gvs[]
                      >> pop_assum mp_tac >> simp[]
                      >> irule VFREE_IN_VSUBST_OUT >> simp[SF SFY_ss])
                  >> irule VFREE_IN_VSUBST_OTHER_VAR >> strip_tac
                  >> first_x_assum $ irule_at Any >> simp[SF SFY_ss]
                  >> rpt strip_tac >> gvs[])
              >- (strip_tac >> gvs[]
                  >> metis_tac[NVARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED])
              >> qexists ‘oty’ >> rw[] >> irule $ iffRL VFREE_IN_VSUBST
              >> simp[REV_ASSOCD, AllCaseEqs()] >> metis_tac[VFREE_IN_def])
          >- (first_x_assum $ irule_at Any >> simp[] >> gvs[Abbr‘env'’, REV_ASSOCD]
              >> metis_tac[NVARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED]))
      >- (gvs[Abbr‘env'’, REV_ASSOCD]
          >> metis_tac[NVARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED]))
    >- (simp[try_def, AllCaseEqs()] >> gvs[] >> rw[] >> fs[]
        >> rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST]
        >> BasicProvers.EVERY_CASE_TAC >> fs[]
        >- (metis_tac[NVARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED])
        >- simp[Once has_type_cases, ty_esubst_def]
        >- metis_tac[NVARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED])
QED

Theorem esubst_ty0_has_type_thm:
  ∀env σ avds tm subst_tm.
    term_ok sig tm ∧ esubsts_ok sig σ ∧
    (∀s s'.
       MEM (s,s') env ⇒
       ∃x ty. s = Var x ty ∧ s' = Var x (ty_esubst σ ty)) ∧
    esubst_ty0 env σ avds tm = return subst_tm ⇒
    (∀x ty.
       VFREE_IN (Var x ty) tm ⇒
       REV_ASSOCD (Var x (ty_esubst σ ty)) env (Var x ty) = Var x ty)
Proof
  rw[] >> qspecl_then [‘sizeof tm’, ‘tm’, ‘env’] mp_tac esubst_ty0_var_type_thm
  >> impl_tac >- metis_tac[term_ok_welltyped]
  >> rw[]
QED

Theorem esubst_ty0_all_free:
  ∀env σ avds tm subst_tm.
    term_ok sig tm ∧ esubsts_ok sig σ ∧
    (∀s s'.
       MEM (s,s') env ⇒
       ∃x ty. s = Var x ty ∧ s' = Var x (ty_esubst σ ty)) ∧
    esubst_ty0 env σ avds tm = return subst_tm ⇒
    (∀u uty.
       VFREE_IN (Var u uty) subst_tm ⇔
         ∃oty. VFREE_IN (Var u oty) tm ∧ uty = ty_esubst σ oty)
Proof
  rw[] >> qspecl_then [‘sizeof tm’, ‘tm’, ‘env’] mp_tac esubst_ty0_var_type_thm
  >> impl_tac >- metis_tac[term_ok_welltyped]
  >> rw[]
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
  >> gvs[try_eq_return, bind_EQ_return, bind_EQ_error, AllCaseEqs()]
  >> rename [‘sizeof tm’, ‘db subst_tm’]
  >- (qspecl_then [‘db tm’, ‘(n, ty)’, ‘0’, ‘σ’] mp_tac db_esubst_ty_bind
      >> impl_tac
      >- (qx_gen_tac ‘ty2’ >> qspecl_then [‘tm’, ‘Var n ty2’] mp_tac dbVFREE_IN_VFREE_IN
          >> rw[]
          >> drule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) esubst_ty0_has_type_thm
          >> disch_then $ drule_at (Pat ‘VFREE_IN _ _’)
          >> disch_then drule >> impl_tac
          >- (simp[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[])
          >> rw[REV_ASSOCD])
      >> rw[] >> sym_tac
      >> qsuff_tac ‘db subst_tm = db_esubst_ty σ (db tm)’
      >- simp[]
      >> first_x_assum irule >> simp[]
      >> qexistsl [‘avds’, ‘(Var n ty,Var n (ty_esubst σ ty))::env’]
      >> gvs[DISJ_IMP_THM, FORALL_AND_THM])
  >> qabbrev_tac ‘Nv = NVARIANT n avds body1’
  >> qabbrev_tac ‘tv = VSUBST [(Var Nv ty,Var n ty)] tm’
  >> qspecl_then [‘db tm’, ‘(Nv, ty)’, ‘(n, ty)’, ‘0’, ‘[]’] mp_tac bind_dbVSUBST_cons
  >> impl_tac
  >- (simp[dbVFREE_IN_bind] >> first_x_assum $ qspec_then ‘sizeof tm’ mp_tac
      >> simp[] >> disch_then $ qspec_then ‘tm’ mp_tac >> simp[]
      >> ‘∃v. esubst_ty0 [] σ avds tm = return v’ by metis_tac[esubst_ty0_always_returns]
      >> disch_then $ qspecl_then [‘[]’, ‘v’, ‘avds’] mp_tac >> rw[]
      >> qspecl_then [‘tm’, ‘Var Nv ty’] mp_tac dbVFREE_IN_VFREE_IN
      >> rw[] >> drule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) esubst_ty0_has_type_thm
      >> disch_then $ drule_then drule >> simp[REV_ASSOCD]
      >> qspecl_then [‘ty_esubst σ ty’, ‘body1’, ‘n’, ‘avds’]
                     mp_tac NVARIANT_THM >> gvs[Abbr‘Nv’]
      >> CONV_TAC CONTRAPOS_CONV >> simp[]
      >> drule_at (Pat ‘esubst_ty0 _ _ _ _ = return _’) esubst_ty0_all_free
      >> disch_then drule >> simp[] >> metis_tac[])
  >> simp[] >> disch_then $ strip_assume_tac o SYM >> simp[]
  >> qspecl_then[‘db tv’, ‘(Nv, ty)’, ‘0’, ‘σ’] mp_tac db_esubst_ty_bind
  >> impl_tac
  >- (qspecl_then [‘db tv’, ‘(Nv, ty)’, ‘0’, ‘σ’] mp_tac db_esubst_ty_bind
      >> impl_tac
      >- (qx_gen_tac ‘ty2’ >> qspecl_then [‘tv’, ‘Var Nv ty2’] mp_tac dbVFREE_IN_VFREE_IN
          >> rw[]
          >> drule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) esubst_ty0_has_type_thm
          >> disch_then $ qspecl_then [‘sig’, ‘Nv’, ‘ty2’] mp_tac
          >> impl_tac
          >- (simp[DISJ_IMP_THM, FORALL_AND_THM, Abbr‘tv’]
              >> conj_tac >- metis_tac[term_ok_vsubst_variant]
              >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[VSUBST_WELLTYPED])
          >> rw[REV_ASSOCD])
      >> rw[] >> sym_tac
      >> qsuff_tac ‘db subst_tm = db_esubst_ty σ (db tv)’
      >- (rw[] >> drule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) esubst_ty0_has_type_thm
          >> disch_then $ qspecl_then [‘sig’, ‘Nv’, ‘ty'’] mp_tac >> impl_tac
          >- (simp[Abbr‘tv’, term_ok_vsubst_variant, FORALL_AND_THM, DISJ_IMP_THM]
              >> conj_tac >- metis_tac[]
              >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[VSUBST_WELLTYPED])
          >> simp[REV_ASSOCD])
      >> first_x_assum irule
      >> simp[Abbr‘tv’, VSUBST_WELLTYPED, SIZEOF_VSUBST, term_ok_vsubst_variant]
      >> first_x_assum $ irule_at Any >> gvs[DISJ_IMP_THM, FORALL_AND_THM])
  >> qspecl_then [‘tm’, ‘[Var Nv ty,Var n ty]’] mp_tac VSUBST_dbVSUBST
  >> impl_tac >- simp[]
  >> rw[]
  >> last_x_assum $ qspec_then ‘sizeof tv’ mp_tac >> impl_tac
  >- simp[SIZEOF_VSUBST, Abbr‘tv’]
  >> disch_then $ qspec_then ‘tv’ mp_tac >> simp[]
  >> disch_then $ qspecl_then [‘(Var Nv ty, Var Nv (ty_esubst σ ty))::env’,
                               ‘subst_tm’, ‘avds’] mp_tac
  >> impl_tac
  >- (simp[Abbr‘tv’, DISJ_IMP_THM, FORALL_AND_THM]
      >> metis_tac[term_ok_vsubst_variant, term_ok_welltyped])
  >> gvs[Abbr‘tv’]
QED

Theorem esubst_ty_welltyped:
  ∀tm avds. term_ok sig tm ∧ esubsts_ok sig σ ⇒ welltyped (esubst_ty σ avds tm)
Proof
  rpt strip_tac >> simp[esubst_ty_def] >> CASE_TAC
  >- (drule esubst_ty0_term_ok >> disch_then drule >> simp[]
      >> metis_tac[term_ok_welltyped])
  >> metis_tac[esubst_ty0_always_returns, neq_error]
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

Theorem RACONV_REFL_simple[simp]:
  RACONV [] (x, x)
Proof
  metis_tac[RACONV_REFL, EVERY_MEM, MEM]
QED

Definition only_esubsts_consts_def:
  only_esubsts_consts θ ⇔ ∀tm. tm ∈ FRANGE θ ⇒ ∃n ty. tm = Const n ty
End

Theorem esubsts_ok_only_esubsts_consts:
  esubsts_ok sig σ ⇒ only_esubsts_consts (SND σ)
Proof
  Cases_on ‘σ’ >> rw[esubsts_ok_def, only_esubsts_consts_def]
QED

Triviality esubst_tm_const:
  esubsts_ok sig σ ∧ FLOOKUP (SND σ) k = SOME v ⇒
  term_ok (esubst_sig σ sig) v ∧
  ∃n ty. v = Const n ty
Proof
  Cases_on ‘σ’ >> rename [‘σ, θ’] >> rw[esubsts_ok_def]
  >> metis_tac[IN_FRANGE_FLOOKUP]
QED

Theorem db_esubst_tm_bind:
  ∀tm n. only_esubsts_consts (SND σ) ⇒
         bind v n (db_esubst_tm σ tm) = db_esubst_tm σ (bind v n tm)
Proof
  Induct_on ‘tm’ >> rw[bind_def, db_esubst_tm_def]
  >> CASE_TAC >> simp[bind_def] >> Cases_on ‘σ’
  >> gvs[only_esubsts_consts_def, IN_FRANGE_FLOOKUP]
  >> qpat_x_assum ‘∀tm. _ ⇒ _’ mp_tac >> disch_then $ qspec_then ‘x’ mp_tac
  >> simp[SF SFY_ss] >> rw[] >> rw[bind_def, db_def]
QED

Theorem db_esubst_tm_thm:
  ∀tm.
    only_esubsts_consts (SND σ) ∧
    term_ok sig tm ⇒
    db (esubst_tm σ tm) = db_esubst_tm σ (db tm)
Proof
  Induct_on ‘tm’ >> rw[esubst_tm_def, db_esubst_tm_def]
  >- (CASE_TAC >> simp[db_def])
  >> simp[] >> metis_tac[db_esubst_tm_bind]
QED

Theorem esubst_tm_RACONV:
  ∀tm1 tm2 env.
    esubsts_ok sig σ ∧
    term_ok sig tm1 ∧
    term_ok sig tm2 ∧
    RACONV env (tm1, tm2) ⇒
    RACONV env (esubst_tm σ tm1, esubst_tm σ tm2)
Proof
  Induct_on ‘tm1’ >> Induct_on ‘tm2’ >> rw[]
  >> gvs[esubst_tm_def, ACONV_def, RACONV]
  >> CASE_TAC >> drule esubst_tm_const
  >> simp[RACONV] >> rw[] >> first_x_assum drule
  >> rw[] >> simp[RACONV]
QED


Theorem esubst_tm_ACONV:
  ∀tm1 tm2 env.
    esubsts_ok sig σ ∧
    term_ok sig tm1 ∧
    term_ok sig tm2 ∧
    ACONV tm1 tm2 ⇒
    ACONV (esubst_tm σ tm1) (esubst_tm σ tm2)
Proof
  metis_tac[ACONV_def, esubst_tm_RACONV]
QED

Theorem esubst_ty0_type = cj 1 $ cj 3 esubst_ty0_impossible1

Theorem esubst_equation:
  esubsts_ok sig σ ∧ term_ok sig tm1 ∧ term_ok sig tm2 ⇒
  esubst σ avds (tm1 === tm2) = esubst σ avds tm1 === esubst σ avds tm2
Proof
  rw[equation_def, esubst_def, esubst_tm_def, esubst_ty_def]
  >> rpt CASE_TAC
  >> gvs[esubst_ty0_def, ty_esubst_def, esubst_tm_def, AllCaseEqs()]
  >- (Cases_on ‘σ’ >> drule $ cj 1 (iffLR esubsts_ok_def)
      >> drule $ cj 2 (iffLR esubsts_ok_def) >> simp[FDOM_FLOOKUP] >> rw[]
      >- metis_tac[TypeBase.nchotomy_of “:α option”]
      >- (qspecl_then [‘[]’, ‘(q, r)’, ‘avds’, ‘tm1’] mp_tac esubst_ty0_type >> simp[]
          >> strip_tac >> rev_drule typeof_esubst_tm_esubst_ty0
          >> disch_then $ qspecl_then [‘(q, r)’, ‘avds’, ‘ty’, ‘a'’, ‘[]’] mp_tac
          >> simp[])
      >- (qspecl_then [‘[]’, ‘(q, r)’, ‘avds’, ‘tm1’] mp_tac esubst_ty0_type >> simp[]
          >> strip_tac >> rev_drule typeof_esubst_tm_esubst_ty0
          >> disch_then $ qspecl_then [‘(q, r)’, ‘avds’, ‘ty’, ‘a'’, ‘[]’] mp_tac
          >> simp[])
      >- metis_tac[TypeBase.nchotomy_of “:α option”])
  >> metis_tac[esubst_ty0_always_returns, neq_error]
QED

Theorem esubst_tm_abs[simp]:
  ∀v body. esubst_tm σ (Abs v body) = Abs v (esubst_tm σ body)
Proof
  rw[esubst_tm_def]
QED

Theorem in_frange_o_f:
  x ∈ FRANGE (f o_f fm) ⇒ ∃y. y ∈ FRANGE fm ∧ x = f y
Proof
  rw[GSYM IMAGE_FRANGE] >> metis_tac[]
QED

Theorem theory_ok_esubst_axs:
  theory_ok (sig, axs) ∧
  esubsts_ok sig σ ⇒
  theory_ok (esubst_sig σ sig, IMAGE (esubst σ avds) axs)
Proof
  Cases_on ‘sig’ >> Cases_on ‘σ’
  >> rename [‘esubsts_ok (tys, tms) (σ, θ)’] >> rw[esubst_sig_def]
  >> drule $ iffLR theory_ok_def
  >> drule $ iffLR esubsts_ok_def >> rw[]
  >> simp[theory_ok_def] >> rw[]
  >- (dxrule in_frange_o_f >> strip_tac >> first_x_assum drule >> gvs[]
      >> metis_tac[esubsts_ok_type_ok, PAIR, FST])
  >- (first_x_assum drule >> strip_tac >> drule_all esubst_term_ok
      >> simp[esubst_sig_def])
  >- (irule esubst_has_type_bool >> metis_tac[])
  >> gvs[is_std_sig_def] >> simp[FLOOKUP_o_f, ty_esubst_def]
  >> CASE_TAC >> drule theory_ok_sig >> simp[is_std_sig_def]
  >> metis_tac[FDOM_FLOOKUP]
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

Theorem ACONV_ABS:
  ∀x ty t1 t2.
    welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 ⇒
    ACONV (Abs (Var x ty) t1) (Abs (Var x ty) t2)
Proof
  rpt strip_tac
  >> irule o iffRL $ ACONV_db
  >> rw[] >> metis_tac[ACONV_db]
QED

Theorem esubst_welltyped:
  ∀tm avds. theory_ok (sig, axs) ∧
            term_ok sig tm ∧
            esubsts_ok sig σ ⇒
            welltyped (esubst σ avds tm)
Proof
  rw[esubst_def, esubst_ty_def]
  >> ‘∃tm1. esubst_ty0 [] σ avds tm = return tm1’
    by metis_tac[esubst_ty0_always_returns]
  >> drule_then drule esubst_ty0_term_ok >> rw[]
  >> drule_all esubst_tm_preserves_term_ok
  >> metis_tac[term_ok_welltyped]
QED

Theorem replace_binder_ACONV:
  ∀body.
    term_ok sig (Abs (Var x ty) body) ∧
    ¬VFREE_IN (Var y ty) body ⇒
    ACONV
    (Abs (Var x ty) body)
    (Abs (Var y ty) (VSUBST [(Var y ty,Var x ty)] body))
Proof
  rw[] >> irule $ iffRL ACONV_db >> rw[]
  >- metis_tac[term_ok_welltyped]
  >- (irule VSUBST_WELLTYPED >> simp[] >> metis_tac[term_ok_welltyped])
  >> Cases_on ‘x = y’
  >- (gvs[]
      >> ‘VSUBST [(Var x ty,Var x ty)] body = body’ by (irule VSUBST_ID >> simp[SF SFY_ss])
      >> simp[])
  >> qspecl_then [‘db body’, ‘(y, ty)’, ‘(x, ty)’, ‘0’, ‘[]’] mp_tac bind_dbVSUBST_cons
  >> rw[] >> sym_tac
  >> qsuff_tac ‘db (VSUBST [(Var y ty,Var x ty)] body) =
                dbVSUBST [(dbVar y ty,dbVar x ty)] (db body)’
  >> rw[]
  >- (first_x_assum irule >> drule_then assume_tac term_ok_welltyped
      >> drule_at Any dbVFREE_IN_VFREE_IN
      >> disch_then $ qspec_then ‘Var y ty’ (mp_tac o iffLR)
      >> simp[] >> contrapos_tac >> gvs[] >> metis_tac[dbVFREE_IN_bind])
  >> qspecl_then [‘body’, ‘[Var y ty, Var x ty]’] mp_tac VSUBST_dbVSUBST
  >> rw[] >> metis_tac[term_ok_welltyped]
QED

Theorem ty_esubst_unchanged:
  ∀ty. DISJOINT (FDOM σ) (nullary_ops_of ty) ⇒
       ty_esubst (σ, θ) ty = ty
Proof
  Induct_on ‘ty’ using type_ind >> rw[ty_esubst_def]
  >> Cases_on ‘l’ >> rw[ty_esubst_def, AllCaseEqs()]
  >- (gvs[nullary_ops_of_def, flookup_thm])
  >- (gvs[nullary_ops_of_def, flookup_thm, MEM_MAP, PULL_EXISTS, EVERY_MEM]
      >> metis_tac[DISJOINT_SYM])
  >> gvs[nullary_ops_of_def, flookup_thm, MEM_MAP, PULL_EXISTS, EVERY_MEM]
  >> rw[MAP_EQ_ID] >> metis_tac[DISJOINT_SYM]
QED

Theorem ty_esubst_idempotent:
  ∀ty. esubsts_ok sig σ ⇒ ty_esubst σ (ty_esubst σ ty) = ty_esubst σ ty
Proof
  Induct_on ‘ty’ using type_ind >> rw[ty_esubst_def]
  >> Cases_on ‘l’ >> rw[ty_esubst_def]
  >- (CASE_TAC >> rw[ty_esubst_def]
      >> Cases_on ‘σ’ >> gvs[esubsts_ok_def, PULL_EXISTS]
      >> first_x_assum $ qspec_then ‘x’ mp_tac >> simp[FRANGE_FLOOKUP]
      >> rw[PULL_EXISTS] >> first_x_assum drule >> rw[]
      >> metis_tac[ty_esubst_unchanged])
  >- (gvs[EVERY_MEM])
  >> gvs[MAP_MAP_o, EVERY_MEM, combinTheory.o_DEF]
  >> irule MAP_CONG >> simp[]
QED


Theorem esubsts_ok_esubst_sig:
  theory_ok (sig, axs) ∧
  esubsts_ok sig σ ⇒
  esubsts_ok (esubst_sig σ sig) σ
Proof
  Cases_on ‘σ’ >> Cases_on ‘sig’ >> rename [‘esubsts_ok (tys, tms) (σ, θ)’]
  >> rw[]
  >> drule $ iffLR esubsts_ok_def
  >> rw[esubst_sig_def, FLOOKUP_o_f, AllCaseEqs(), PULL_EXISTS]
  >> simp[esubsts_ok_def, PULL_EXISTS] >> rw[]
  >- (simp[FLOOKUP_o_f, AllCaseEqs(), PULL_EXISTS]
      >> simp[ty_esubst_idempotent, SF SFY_ss]
      >> simp[flookup_thm] >> first_x_assum drule
      >> rw[] >> gvs[flookup_thm]
      >- (irule $ iffLR is_monomorphic_ty_esubst >> simp[]
          >> first_assum $ irule_at Any >> simp[]
          >> gvs[IN_FRANGE, PULL_EXISTS, theory_ok_def]))
  >> first_x_assum drule >> simp[PULL_EXISTS] >> rw[]
  >> rw[esubst_sig_def]
  >> ‘ty_esubst (σ,θ) ∘ ty_esubst (σ,θ) = ty_esubst (σ,θ)’
        suffices_by simp[]
  >> simp[FUN_EQ_THM] >> irule ty_esubst_idempotent
  >> metis_tac[]
QED

Theorem esubst_ACONV:
  ∀tm1 tm2.
    theory_ok (sig, axs) ∧
    esubsts_ok sig σ ∧
    term_ok sig tm1 ∧
    term_ok sig tm2 ∧
    ACONV tm1 tm2 ⇒
    ACONV (esubst σ avds tm1) (esubst σ avds tm2)
Proof
  rw[esubst_def] >> irule esubst_tm_ACONV >> rw[]
  >- (irule $ iffRL ACONV_db >> rpt conj_tac
      >- metis_tac[esubst_ty_welltyped]
      >- metis_tac[esubst_ty_welltyped]
      >> gvs[esubst_ty_def]
      >> ‘∃v. esubst_ty0 [] σ avds tm1 = return v’
        by metis_tac[esubst_ty0_always_returns]
      >> ‘∃v. esubst_ty0 [] σ avds tm2 = return v’
        by metis_tac[esubst_ty0_always_returns]
      >> gvs[]
      >> dxrule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) db_esubst_ty_thm
      >> dxrule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) db_esubst_ty_thm
      >> simp[] >> rpt $ disch_then (drule_then strip_assume_tac) >> gvs[]
      >> imp_res_tac term_ok_welltyped >> gvs[]
      >> metis_tac[ACONV_db])
  >> gvs[esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds tm1 = return v’
    by metis_tac[esubst_ty0_always_returns]
  >> ‘∃v. esubst_ty0 [] σ avds tm2 = return v’
    by metis_tac[esubst_ty0_always_returns]
  >> gvs[]
  >> rpt $ dxrule esubst_ty0_term_ok
  >> simp[] >> rpt $ disch_then $ drule_all_then assume_tac
  >> first_assum $ irule_at Any >> simp[]
  >> irule esubsts_ok_esubst_sig >> metis_tac[]
QED

Triviality esubst_binder_fresh_on_hyps:
  ∀h1 y hyps.
    MEM h1 hyps ∧
    ¬MEM y (FLAT (MAP tm_names hyps)) ⇒
    ¬VFREE_IN (Var y ty) h1
Proof
  rw[] >> qsuff_tac ‘¬MEM y (tm_names h1)’
  >- metis_tac[VFREE_IN_tm_names]
  >> metis_tac[MEM_FLAT, MEM_MAP]
QED

Theorem esubst_ty0_abs_avds_binder:
  ∀σ avds sig x y ty l.
    term_ok sig l ∧
    type_ok (tysof sig) ty ∧
    esubsts_ok sig σ ∧
    ¬MEM y (tm_names l) ⇒
    ∃body1. esubst_ty0 [(Var y ty, Var y (ty_esubst σ ty))] σ avds
                       (VSUBST [(Var y ty, Var x ty)] l) = return body1
Proof
  rw[esubst_ty0_def, bind_EQ_error, bind_EQ_return, try_eq_return, AllCaseEqs()]
  >> irule $ iffLR neq_error >> rw[] >> strip_tac
  >> dxrule_at Any $ cj 1 esubst_ty0_impossible1 >> simp[]
  >> first_x_assum $ irule_at Any >> simp[term_ok_vsubst_variant]
  >> rw[] >> gvs[REV_ASSOCD, AllCaseEqs()] >> strip_d1
  >> gvs[] >> CCONTR_TAC >> drule_all $ iffLR FVs_VSUBST_CASES
  >> simp[] >> metis_tac[FVs_in_tm_names]
QED

Theorem esubst_has_type1:
  theory_ok (sig, axs) ∧
  esubsts_ok sig σ ∧
  term_ok sig tm ∧
  tm has_type ty ⇒
  esubst σ avds tm has_type ty_esubst σ ty
Proof
  rw[] >> irule esubst_has_type >> rw[]
  >> simp[SF SFY_ss, esubst_ty_def]
  >> ‘∃tm1. esubst_ty0 [] σ avds tm = return tm1’
    by metis_tac[esubst_ty0_always_returns]
  >> simp[] >> drule_then drule esubst_ty0_ty_esubst >> rw[]
  >> drule has_type_typeof >> rw[] >> irule $ iffRL typeof_has_type
  >> simp[] >> drule esubst_ty0_term_ok >> simp[]
  >> disch_then drule >> metis_tac[term_ok_welltyped]
QED

Theorem FILTER_empty[simp]:
  FILTER (λp. ¬MEM p lst) lst = []
Proof
  Induct_on ‘lst’ >> simp[GSYM FILTER_FILTER]
QED

Theorem nproves_set_n_zero:
  (thy, h, 0) |n- c ⇒ (thy, h, n) |n- c
Proof
  Induct_on ‘n’ >> rw[ADD1] >> gvs[]
  >> rev_drule_at Any nproves_INST
  >> disch_then $ qspec_then ‘[]’ mp_tac
  >> simp[term_image_id]
QED

Theorem VSUBST_equation:
  a has_type ty ∧
  (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
  VSUBST ilist (a === b) = VSUBST ilist a === VSUBST ilist b
Proof
  rw[equation_def, VSUBST_def] >> drule_all VSUBST_HAS_TYPE
  >> metis_tac[has_type_typeof]
QED

Theorem VSUBST_sing_var[simp]:
  VSUBST [z, y] (Var x ty) = if Var x ty = y then z else Var x ty
Proof
  rw[VSUBST_def, REV_ASSOCD]
QED

        (*
Theorem esubst_INST_comm:
  ∀tm.
    theory_ok (sig, axs) ∧
    EVERY (type_ok (tysof sig)) (MAP FST tyin) ∧
    esubsts_ok sig σ ∧ term_ok sig tm ⇒
    esubst σ avds (INST tyin tm) =
    INST (MAP (λ(ty, a). (ty_esubst σ ty, a)) tyin) (esubst σ avds tm)
Proof
  Induct_on ‘tm’ >> rw[INST_def, INST_CORE_def, esubst_def, esubst_tm_def, REV_ASSOCD]
  >- (Cases_on ‘sig’ >> gvs[] >> irule ty_esubst_TYPE_SUBST_aux
      >> first_x_assum $ irule_at Any >> irule type_ok_TYPE_SUBST
      >> simp[])
  >- (Cases_on ‘sig’ >> rC ‘FLOOKUP (SND σ) m’ >> simp[INST_CORE_def]
      >- (irule ty_esubst_TYPE_SUBST_aux >> first_x_assum $ irule_at Any
          >> irule type_ok_TYPE_SUBST >> gvs[term_ok_def])
      >> drule esubsts_ok_only_esubsts_consts >> strip_tac
      >> gvs[only_esubsts_consts_def, FRANGE_FLOOKUP]
      >> first_x_assum $ qspec_then ‘x’ mp_tac >> impl_tac
      >- metis_tac[] >> rw[INST_CORE_def] >> rw[INST_CORE_def]
      >> sym_tac >> irule monomorphic_type_subst
      >> gvs[term_ok_def] >> Cases_on ‘σ’ >> rename [‘esubsts_ok (tys, tms) (σ, θ)’]
      >> drule $ iffLR esubsts_ok_def >> rw[] >> first_x_assum $ qspec_then ‘m’ mp_tac
      >> simp[FDOM_FLOOKUP] >> rw[] >> gvs[]
      >> ‘typeof (θ ' m) = ty’ by metis_tac[FAPPLY_FLOOKUP, typeof_def]
      >> gvs[] >> irule $ iffLR is_monomorphic_ty_esubst >> simp[]
      >> first_x_assum $ irule_at Any >> simp[] >> gvs[theory_ok_def]
      >> first_x_assum irule >> metis_tac[IN_FRANGE_FLOOKUP])
  >> cheat
QED*)

Theorem ACONV_COMB:
  ACONV (Comb a b) (Comb x y) ⇔ ACONV a x ∧ ACONV b y
Proof
  rw[ACONV_def, RACONV]
QED

Theorem nproves_ABS':
  ∀h l n r thy ty x.
    0 < n ∧
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (tysof thy) ty ∧
    (thy,h,n - 1) |n- l === r ⇒
    (thy,h,n) |n- Abs (Var x ty) l === Abs (Var x ty) r
Proof
  Cases_on ‘n’ >> simp[ADD1] >> rw[]
  >> irule nproves_ABS >> simp[]
QED

Triviality NVARIANT_SUBLIST_AVDS:
  Abbrev(y = NVARIANT n avds tm) ∧
  (∀n. MEM n tgt ⇒ MEM n avds) ⇒
  ¬MEM y tgt
Proof
  rpt strip_tac >> first_x_assum drule >> simp[Abbr‘y’, NVARIANT_AVDS_THM]
QED

Theorem esubst_ty_has_type:
  ∀tm avds. term_ok sig tm ∧ esubsts_ok sig σ ⇒
            esubst_ty σ avds tm has_type ty_esubst σ (typeof tm)
Proof
  rpt strip_tac >> simp[esubst_ty_def] >> CASE_TAC
  >- (drule esubst_ty0_ty_esubst >> rw[] >> irule $ iffRL typeof_has_type
      >> rw[] >> drule esubst_ty0_term_ok >> disch_then drule >> simp[]
      >> metis_tac[term_ok_welltyped])
  >> metis_tac[esubst_ty0_always_returns, neq_error]
QED

Triviality nproves_esubst_ty0_empty_env:
  esubst_ty0 [(Var y ty,Var y (ty_esubst σ ty))] σ avds tm = return tm1 ∧
  esubst_ty0 [] σ avds tm = return tm2 ∧
  term_ok sig tm ∧ esubsts_ok sig σ ∧ theory_ok (sig, axs) ∧
  (thy, h, n) |n- tm1 ⇒
  (thy, h, n + 1) |n- tm2
Proof
  rw[] >> irule nproves_ACONV_concl >> conj_tac
  >- (drule_all esubst_ty_welltyped >> simp[esubst_ty_def]
      >> disch_then $ qspec_then ‘avds’ mp_tac >> simp[])
  >> first_x_assum $ irule_at Any >> irule esubst_ty0_env_aconv
  >> simp[SF SFY_ss] >> rw[]
  >- (rpt $ dxrule_then drule esubst_ty0_term_ok >> simp[] >> metis_tac[term_ok_welltyped])
  >- (rpt $ dxrule_then drule esubst_ty0_term_ok >> simp[] >> metis_tac[term_ok_welltyped])
  >> rpt $ first_x_assum $ irule_at Any >> simp[]
QED

Theorem term_image_sing[simp]:
  term_image f [x] = [f x]
Proof
  rw[Once term_image_def] >> simp[term_union_def]
QED

Theorem esubst_var[simp]:
  esubst σ avds (Var x ty) = Var x (ty_esubst σ ty)
Proof
  simp[esubst_def, esubst_ty_def, esubst_tm_def]
QED

Theorem VFREE_IN_esubst_tm:
  esubsts_ok sig σ ⇒ 
  (VFREE_IN (Var x ty) (esubst_tm σ tm) ⇔ VFREE_IN (Var x ty) tm)
Proof
  Induct_on ‘tm’ >> simp[esubst_tm_def] >> rw[] >> CASE_TAC
  >> simp[VFREE_IN_def] >> dxrule esubsts_ok_only_esubsts_consts
  >> simp[only_esubsts_consts_def] >> simp[FRANGE_FLOOKUP]
  >> disch_then $ qspec_then ‘x'’ mp_tac >> simp[SF SFY_ss] >> rw[]
  >> simp[VFREE_IN_def]
QED

Theorem VFREE_IN_esubst:
  esubsts_ok sig σ ∧
  theory_ok (sig, axs) ∧
  term_ok sig tm ∧
  VFREE_IN (Var x ty) tm ⇒
  VFREE_IN (Var x (ty_esubst σ ty)) (esubst σ [] tm)
Proof
  rw[esubst_def, esubst_tm_def, esubst_ty_def]
  >> ‘∃tm1. esubst_ty0 [] σ [] tm = return tm1’ by metis_tac[esubst_ty0_always_returns]
  >> simp[] >> irule $ iffRL VFREE_IN_esubst_tm >> conj_tac
  >- (drule_then drule esubst_ty0_all_free
      >> disch_then $ drule_at Any >> simp[]
      >> metis_tac[])
  >> drule esubst_ty0_term_ok >> simp[]
  >> disch_then drule_all >> drule_all esubsts_ok_esubst_sig
  >> simp[SF SFY_ss]
QED

Triviality VSUBST_NOT_FREE_VAR:
  term_ok sig tm ∧
  ¬VFREE_IN (Var x ty) tm ⇒
  VSUBST [(y, Var x ty)] tm = tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def] >> gvs[]
QED

Theorem term_image_VSUBST_VFREE:
  EVERY ($¬ ∘ VFREE_IN (Var x (ty_esubst σ ty))) hσ ∧
  EVERY (term_ok sig) hσ ⇒
  term_image
  (VSUBST [(Var y (ty_esubst σ ty),Var x (ty_esubst σ ty))]) hσ = hσ
Proof
  Induct_on ‘hσ’ >> rw[] >> gvs[EVERY_MEM]
  >> simp[Once term_image_def] >> CASE_TAC
  >> drule_at Any VSUBST_NOT_FREE_VAR >> metis_tac[]
QED

Triviality MAP_db_esubst_ty:
  ∀tm ilist.
    esubsts_ok sig σ ∧ term_ok sig tm ∧ welltyped tm ∧
    (∀t1 t2. MEM (t1, t2) ilist ⇒ term_ok sig t1 ∧ term_ok sig t2) ∧
    Abbrev (ilistdb = MAP (λ(x,y). (db x,db y)) ilist) ⇒
    MAP ((λ(x,y). (db x,db y))
         ∘ (λ(v,k). (esubst_ty σ avds v,esubst_ty σ avds k))) ilist =
    MAP (λ(x,y). (db_esubst_ty σ x, db_esubst_ty σ y)) ilistdb
Proof
  rw[] >> gvs[Abbr‘ilistdb’] >> rw[] >> Induct_on ‘ilist’
  >> rw[]
  >- (Cases_on ‘h’ >> rw[esubst_ty_def]
      >> ‘∃qσ. esubst_ty0 [] σ avds q = return qσ’
        by metis_tac[esubst_ty0_always_returns]
      >> ‘∃rσ. esubst_ty0 [] σ avds r = return rσ’
        by metis_tac[esubst_ty0_always_returns]
      >> gvs[] >> dxrule_at_then (Pos last) drule db_esubst_ty_thm >> impl_tac
      >- (qspecl_then [‘sig’,‘r’] mp_tac term_ok_welltyped >> gvs[])
      >> gvs[] >> dxrule_at_then (Pos last) drule db_esubst_ty_thm >> impl_tac
      >- (qspecl_then [‘sig’,‘q’] mp_tac term_ok_welltyped >> gvs[])
      >> rw[] >> metis_tac[term_ok_welltyped])
  >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >> first_x_assum drule
  >> rw[]
QED
(*
Theorem db_esubst_ty_esubst_tm_VSUBST_comm:
  ∀dbtm ilistdb.
    esubsts_ok sig σ ∧
    (∀s s'. MEM (s',s) ilistdb ⇒
            ∃x y ty. s = dbVar x ty ∧ s' = dbVar y ty ∧ type_ok (tysof sig) ty) ⇒
    dbVSUBST (MAP (λ(x,y). (db_esubst_ty σ x,db_esubst_ty σ y)) ilistdb)
             (db_esubst_tm σ (db_esubst_ty σ dbtm)) =
    db_esubst_tm σ (db_esubst_ty σ (dbVSUBST ilistdb dbtm))
Proof
  Induct_on ‘dbtm’ >> rw[db_esubst_ty_def, db_esubst_tm_def, dbVSUBST_def]
  >- (Induct_on ‘ilistdb’ >> rw[REV_ASSOCD, db_esubst_ty_def, db_esubst_tm_def]
      >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >> Cases_on ‘h’ >> gvs[]
      >> simp[REV_ASSOCD, AllCaseEqs()] >> rw[]
      >> simp[db_esubst_ty_def, db_esubst_tm_def]
      >> gvs[REV_ASSOCD, db_esubst_ty_def]
      >> cheat)
  >> cheat
QED

Theorem db_esubst_ty_esubst_tm_VSUBST_comm_singleton:
  ∀dbtm.
    esubsts_ok sig σ ∧ x ≠ y ⇒
    dbVSUBST [(dbVar y (ty_esubst σ ty), dbVar x (ty_esubst σ ty))]
             (db_esubst_tm σ (db_esubst_ty σ dbtm)) =
    db_esubst_tm σ (db_esubst_ty σ (dbVSUBST [(dbVar y ty, dbVar x ty)] dbtm))
Proof
  Induct_on ‘dbtm’ >> rw[db_esubst_ty_def, db_esubst_tm_def]
  >> rw[REV_ASSOCD, db_esubst_tm_def, db_esubst_ty_def] >> gvs[] >> cheat
QED
  *)
(*
Theorem esubst_ty_esubst_tm_VSUBST_comm:
  term_ok sig tm ∧ theory_ok (sig, axs) ∧ esubsts_ok sig σ ∧
  (∀s s'. MEM (s',s) ilist ⇒
          ∃x y ty. s = Var x ty ∧ s' = Var y ty ∧ type_ok (tysof sig) ty) ∧
  (∀k v. MEM (v, k) env1 ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
  (∀k v. MEM (v, k) env2 ⇒ ∃n ty. k = Var n (ty_esubst σ ty) ∧ v = Var n ty) ∧
  esubst_ty0 env1 σ avds tm = return subst_tm ∧
  esubst_ty0 env2 σ avds (VSUBST ilist tm) = return vsubst_tm ⇒
  ACONV (VSUBST (MAP (λ(v, k). (esubst_ty σ avds v, esubst_ty σ avds k)) ilist)
                (esubst_tm σ subst_tm)) (esubst_tm σ vsubst_tm)
Proof
  rpt strip_tac >> irule $ iffRL ACONV_db >> conj_tac
  >- (irule VSUBST_WELLTYPED >> rw[DISJ_IMP_THM, FORALL_AND_THM]
      >- (gvs[MEM_MAP] >> Cases_on ‘y’ >> gvs[] >> first_x_assum drule
          >> rw[] >> simp[])
      >> irule term_ok_welltyped
      >> rev_drule esubst_ty0_term_ok >> disch_then $ drule_then drule
      >> metis_tac[esubst_tm_preserves_term_ok]) >> conj_tac
  >- (irule term_ok_welltyped >> drule esubst_ty0_term_ok
      >> disch_then $ drule_at Any >> impl_tac
      >- metis_tac[term_ok_VSUBST, has_type_var, term_ok_def]
      >> drule term_ok_VSUBST >> disch_then $ qspec_then ‘ilist’ mp_tac >> impl_tac
      >- (rw[] >> first_x_assum drule >> rw[])
      >> metis_tac[esubst_tm_preserves_term_ok])
  >> drule_then assume_tac esubsts_ok_only_esubsts_consts
  >> drule_at_then (Pos last) drule db_esubst_ty_thm >> simp[]
  >> rev_drule_at_then (Pos last) drule db_esubst_ty_thm >> simp[]
  >> drule term_ok_welltyped >> simp[term_ok_VSUBST, has_type_var]
  >> rw[] >> drule term_ok_VSUBST >> disch_then $ qspec_then ‘ilist’ mp_tac
  >> impl_tac >- metis_tac[has_type_var, term_ok_def] >> strip_tac
  >> drule term_ok_welltyped >> strip_tac >> first_x_assum drule >> strip_tac
  >> simp[db_esubst_tm_thm] >> drule_all db_esubst_tm_thm >> rw[]
  >> qabbrev_tac ‘ilistσ=MAP (λ(v,k). (esubst_ty σ avds v,esubst_ty σ avds k)) ilist’
  >> qspecl_then [‘esubst_tm σ subst_tm’, ‘ilistσ’] mp_tac VSUBST_dbVSUBST >> impl_tac
  >- (conj_tac >- (irule term_ok_welltyped >> qexists ‘esubst_sig σ sig’
                   >> irule esubst_tm_preserves_term_ok >> simp[SF SFY_ss]
                   >> metis_tac[esubst_ty0_term_ok])
      >> simp[] >> rw[MEM_MAP, Abbr‘ilistσ’] >> Cases_on ‘y’ >> gvs[]
      >- (irule esubst_ty_welltyped >> first_x_assum $ irule_at Any
          >> first_x_assum drule >> rw[] >> simp[term_ok_def])
      >> first_x_assum drule >> rw[] >> simp[term_ok_def])
  >> rw[]
  >> qspecl_then [‘σ’, ‘esubst_sig σ sig’, ‘subst_tm’] mp_tac $
                 GEN_ALL db_esubst_tm_thm >> impl_tac
  >- (simp[] >> irule esubst_ty0_term_ok >> simp[]
      >> first_x_assum $ irule_at (Pat ‘esubst_ty0 _ _ _ _ = _’)
      >> simp[] >> metis_tac[]) >> rw[]
  >> qspecl_then [‘σ’, ‘esubst_sig σ sig’, ‘vsubst_tm’] mp_tac $
                 GEN_ALL db_esubst_tm_thm >> impl_tac
  >- (simp[] >> irule esubst_ty0_term_ok >> simp[]
      >> first_x_assum $ irule_at (Pat ‘esubst_ty0 _ _ _ _ = _’)
      >> simp[] >> metis_tac[])
  >> rw[] >> qspecl_then [‘tm’, ‘ilist’] mp_tac VSUBST_dbVSUBST >> impl_tac
  >- metis_tac[welltyped_def, has_type_var, term_ok_def]
  >> rw[Abbr‘ilistσ’] >> simp[MAP_MAP_o]
  >> qabbrev_tac ‘ilistdb=MAP (λ(x,y). (db x,db y)) ilist’
  >> drule_at (Pos last) MAP_db_esubst_ty
  >> disch_then $ drule_then drule >> simp[] >> impl_tac
  >- metis_tac[term_ok_def] >> disch_then $ qspec_then ‘avds’ mp_tac
  >> rw[] >> irule db_esubst_ty_esubst_tm_VSUBST_comm
  >> simp[Abbr‘ilistdb’] >> qexists ‘sig’ >> simp[MEM_MAP]
  >> rw[] >> Cases_on ‘y’ >> gvs[] >> metis_tac[db_def, term_ok_def]
QED*)

Theorem esubst_tm_has_type_ty0:
  term_ok sig tm ∧ esubsts_ok sig σ ∧ theory_ok (sig, axs) ∧
  esubst_ty0 [] σ avds tm = return tmσ ⇒
  esubst_tm σ tmσ has_type ty_esubst σ (typeof tm)
Proof
  rpt strip_tac >> irule $ iffRL typeof_has_type >> conj_tac
  >- (drule esubst_ty0_term_ok >> disch_then $ drule_then drule
      >> rw[] >> irule term_ok_welltyped >> drule_all esubst_tm_preserves_term_ok
      >> simp[SF SFY_ss])
  >> drule_at (Pos last) typeof_esubst_tm_esubst_ty0 >> disch_then $ drule_then drule
  >> rw[] >> Cases_on ‘σ’ >> drule_at (Pos last) typeof_esubst_ty
  >> disch_then $ drule_then drule >> simp[]
QED

Triviality typeof_esubst_tm_VSUBST_esubst_ty0:
  term_ok sig l ∧
  term_ok sig r ∧
  typeof l = typeof r ∧
  type_ok (tysof sig) ty ∧
  esubst_ty0 [(Var y ty,Var y (ty_esubst σ ty))] σ avds
             (VSUBST [(Var y ty,Var x ty)] l) = return l1 ∧
  esubst_ty0 [(Var y ty,Var y (ty_esubst σ ty))] σ avds
             (VSUBST [(Var y ty,Var x ty)] r) = return r1 ∧
  esubsts_ok sig σ ⇒
  typeof (esubst_tm σ l1) = typeof (esubst_tm σ r1)
Proof
  rpt strip_tac
  >> drule_at (Pos last) typeof_esubst_tm_esubst_ty0
  >> rev_drule_at (Pos last) typeof_esubst_tm_esubst_ty0
  >> simp[]
  >> rpt (disch_then $ drule_at Any
          >> simp[term_ok_vsubst_variant, SF SFY_ss]
          >> strip_tac)
  >> qspec_then ‘[(Var y ty,Var y (ty_esubst σ ty))]’ mp_tac esubst_ty0_type
  >> disch_then drule >> disch_then $ drule_at (Pos last)
  >> qspec_then ‘[(Var y ty,Var y (ty_esubst σ ty))]’ mp_tac esubst_ty0_type
  >> disch_then drule >> disch_then $ rev_drule_at (Pos last)
  >> simp[term_ok_vsubst_variant] >> rw[] >> CONG_TAC (SOME 1)
  >> rpt $ dxrule typeof_vsubst >> simp[]
QED

Theorem nproves_le:
  ∀n m. n ≤ m ∧ (thy, h, n) |n- c ⇒ (thy, h, m) |n- c
Proof
  Induct_on ‘m’ >> rw[]
  >- (irule nproves_set_n_zero >> simp[])
  >> first_x_assum $ qspec_then ‘n’ mp_tac
  >> rw[] >> Cases_on ‘n = m + 1’ >> gvs[ADD1]
  >> drule_at (Pos last) nproves_INST
  >> disch_then $ qspec_then ‘[]’ mp_tac >> simp[term_image_id]
QED

Triviality LENGTH_term_union_sing_aux[simp]:
  LENGTH (term_union [f h] t) = LENGTH t ∨
  LENGTH (term_union [f h] t) = LENGTH t + 1
Proof
  Induct_on ‘t’ >> simp[term_union_thm]
  >> Cases_on ‘orda [] (f h) h'’
  >> gvs[term_union_thm]
QED

Theorem term_image_LENGTH:
  ∀ts. LENGTH (term_image f ts) ≤ LENGTH ts
Proof
  Induct_on ‘ts’ >> simp[Once term_image_def] >> rw[]
  >> simp[Once term_union_def] >> CASE_TAC >> rw[]
  >> gvs[]
  >> qspecl_then [‘t’, ‘h’, ‘f’] mp_tac $ GEN_ALL LENGTH_term_union_sing_aux
  >> strip_tac >> pop_assum SUBST1_TAC >> gvs[]
QED

Theorem nproves_ACONVi:
  ∀thy h' c' h c m.
       (thy,h,m - 3 * LENGTH h' - 1) |n- c ∧ m > 3 * LENGTH h' + 1 ∧
       welltyped c' ∧ ACONV c c' ∧ hypset_ok h' ∧
       EVERY (λx. EXISTS (ACONV x) h') h ∧
       EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) h' ⇒
                  (thy,h',m) |n- c'
Proof
  rpt strip_tac >> drule_all nproves_ACONV >> rw[]
  >> ‘m' ≤ m’ suffices_by metis_tac[nproves_le]
  >> gvs[]
QED

Triviality VARIANT_EQ_aux:
  ∀xs v n.
    xs = [tm1] ∧ v = Var n typ ∧
    (∀x ty. VFREE_IN (Var x ty) tm1 ⇔ VFREE_IN (Var x ty) tm2) ⇒
    variant xs v = variant [tm2] (Var n typ)
Proof
  ho_match_mp_tac variant_ind >> rw[]
  >> ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
  >> rw[] >> gvs[]
  >- (qsuff_tac ‘variant [tm2] (Var n typ) = variant [tm2] (Var (n ^ «'») typ)’
      >> rw[]
      >> ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
      >> metis_tac[vfree_in_thm])
  >> ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
  >> metis_tac[vfree_in_thm]
QED 
        
Theorem VARIANT_EQ:
  ∀tm1 tm2.
    (∀x ty. VFREE_IN (Var x ty) tm1 ⇔ VFREE_IN (Var x ty) tm2) ⇒
    VARIANT tm1 n typ = VARIANT tm2 n typ
Proof
  rw[] >> ‘∀n m ty. Var n ty = Var m ty ⇒ n = m’ by simp[]
  >> first_x_assum irule >> qexists ‘typ’
  >> ‘variant [tm1] (Var (implode n) typ) = variant [tm2] (Var (implode n) typ)’ suffices_by
    simp[variant_vsubst_thm, implode_explode]
  >> metis_tac[VARIANT_EQ_aux]
QED

Theorem esubst_tm_VSUBST_comm:
  ∀tm ilist.
    term_ok sig tm ∧ esubsts_ok sig σ ∧ 
    (∀v k. MEM (v, k) ilist ⇒ ∃n m ty. v = Var n ty ∧ k = Var m ty) ⇒ 
    esubst_tm σ (VSUBST ilist tm) = VSUBST ilist (esubst_tm σ tm)
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, esubst_tm_def, term_ok_def]
  >- (qsuff_tac ‘∃k typ. REV_ASSOCD (Var m t) ilist (Var m t) = Var k typ’
      >> rw[] >- metis_tac[esubst_tm_def]
      >> Cases_on ‘REV_ASSOCD (Var m t) ilist (Var m t) = Var m t’ >> simp[]
      >> dxrule rev_assocd_neq_mem >> rw[] >> metis_tac[])
  >- (rpt CASE_TAC >> simp[VSUBST_def] >> dxrule esubsts_ok_only_esubsts_consts
      >> rw[only_esubsts_consts_def] >> gvs[FRANGE_FLOOKUP] >> metis_tac[VSUBST_def])
  >> gvs[term_ok_def, MEM_FILTER]
  >> gvs[EXISTS_MEM, EVERY_MEM, FORALL_PROD, MEM_FILTER] >> rw[] >> Cases_on ‘e’ >> gvs[]
  >- (Cases_on ‘e'’ >> gvs[] >> irule VARIANT_EQ >> rw[EQ_IMP_THM]
      >> qabbrev_tac ‘ilist' = FILTER (λ(s',s). s ≠ Var x ty) ilist’
      >> first_x_assum $ qspec_then ‘ilist'’ mp_tac >> impl_tac
      >> simp[MEM_FILTER, DISJ_IMP_THM, FORALL_AND_THM, Abbr‘ilist'’]
      >> rw[] >> gvs[] >> qpat_x_assum ‘VFREE_IN _ _’ mp_tac >> pop_assum mp_tac
      >> disch_then $ SUBST1_TAC o GSYM >> simp[VFREE_IN_esubst_tm, SF SFY_ss])
  >- (Cases_on ‘e'’ >> gvs[]
      >> qabbrev_tac ‘ilist' = FILTER (λ(s',s). s ≠ Var x ty) ilist’
      >> qabbrev_tac ‘z = (VARIANT (VSUBST ilist' tm') (explode x) ty)’
      >> first_assum $ qspec_then ‘(Var z ty,Var x ty)::ilist'’ mp_tac >> impl_tac
      >- (rw[] >> metis_tac[MEM_FILTER]) >> strip_tac
      >> ‘z = VARIANT (VSUBST ilist' (esubst_tm σ tm')) (explode x) ty’ suffices_by simp[]
      >> simp[Abbr‘z’] >> first_x_assum $ qspec_then ‘ilist'’ mp_tac >> impl_tac
      >- simp[MEM_FILTER, DISJ_IMP_THM, FORALL_AND_THM, Abbr‘ilist'’]
      >> disch_then $ SUBST1_TAC o GSYM >> irule VARIANT_EQ >> rw[VFREE_IN_esubst_tm, SF SFY_ss])
  >> metis_tac[VFREE_IN_esubst_tm]
QED

Triviality ilist_ok_REV_ASSOCD_var:
  (∀v k. MEM (v,k) ilist ⇒ ∃n m ty. v = Var n ty ∧ k = Var m ty) ⇒
  ∃m typ. REV_ASSOCD (Var x ty) ilist (Var x ty) = Var m typ
Proof
  rw[] >> qspecl_then [‘ilist’, ‘Var x ty’, ‘Var x ty’] mp_tac REV_ASSOCD_MEM
  >> rw[] >> metis_tac[]
QED

Theorem esubst_ty0_VSUBST_comm:
  ∀env σ avds tm ilist tσ vtσ.
    term_ok sig tm ∧
    esubsts_ok sig σ ∧
    (∀v k. MEM (v,k) ilist ⇒ ∃n m ty. v = Var n ty ∧ k = Var m ty) ∧
    (∀v k. MEM (v,k) env ⇒ ∃n ty. v = Var n ty ∧ k = Var n (ty_esubst σ ty)) ∧
    (¬∃k1 v1 k2 v2. MEM (v1, k1) ilist ∧ MEM (v2, k2) ilist ∧
                    k1 ≠ k2 ∧ esubst_ty σ avds k1 = esubst_ty σ avds k2) ∧
    esubst_ty0 env σ avds tm = return tσ ∧
    esubst_ty0 env σ avds (VSUBST ilist tm) = return vtσ ⇒
    ACONV vtσ (VSUBST (MAP (λ(v, k). (esubst_ty σ avds v, esubst_ty σ avds k)) ilist) tσ)
Proof
  recInduct esubst_ty0_ind >> rw[] >> gvs[esubst_ty0_def, term_ok_def, VSUBST_def, AllCaseEqs()]
  >- (drule ilist_ok_REV_ASSOCD_var >> disch_then $ qspecl_then [‘n’, ‘ty’] mp_tac >> rw[]
      >> gvs[esubst_ty0_def, AllCaseEqs()] >> ‘∀a b. a = b ⇒ ACONV a b’ by simp[ACONV_REFL]
      >> first_x_assum irule >> Induct_on ‘ilist’
      >> rw[REV_ASSOCD] >> Cases_on ‘h’ >> gvs[DISJ_IMP_THM, FORALL_AND_THM]
      >> gvs[REV_ASSOCD, AllCaseEqs()] >> strip_d1 >> gvs[] >> rw[] >> cheat)
  >> gvs[bind_EQ_error, bind_EQ_return, try_eq_return, AllCaseEqs()]
  >> cheat
QED
        
Theorem esubst_VSUBST_comm:
  ∀env σ avds ilist tm tm1 tm2.
    esubst_ty0 env σ avds (VSUBST ilist tm) = return tm1 ∧
    esubst_ty0 [] σ avds tm = return tm2 ∧
    term_ok sig tm ∧
    (∀v k. MEM (v, k) env ⇒ ∃n ty. v = Var n ty ∧ k = Var n (ty_esubst σ ty)) ∧
    (∀v k. MEM (v, k) ilist ⇒ ∃n m ty. v = Var n ty ∧ k = Var m ty) ⇒ 
    esubst_tm σ tm1 =
    VSUBST (MAP (λ(v, k). (esubst_ty σ avds v, esubst_ty σ avds k)) ilist) tm2
Proof
  completeInduct_on ‘sizeof tm’ >> Cases_on ‘tm’ >> rw[VSUBST_def]
  >> gvs[esubst_ty0_def, esubst_tm_def, REV_ASSOCD]
  >> cheat
QED
        
Theorem simple_esubst_Abs:
  term_ok sig (Abs (Var x ty) t) ∧
  theory_ok (sig,axs) ∧
  esubsts_ok sig σ ⇒
  ∃y body.
    esubst σ avds (Abs (Var x ty) t) =
    Abs (Var y (ty_esubst σ ty))
        (VSUBST [(Var y (ty_esubst σ ty), Var x (ty_esubst σ ty))] t)
Proof
  rw[esubst_def, esubst_tm_def, esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds (Abs (Var x ty) t) = return v’
    by metis_tac[esubst_ty0_always_returns, term_ok_def]
  >> ‘∃v. esubst_ty0 [] σ avds t = return v’
    by metis_tac[esubst_ty0_always_returns, term_ok_def]
  >> simp[]
  >> gvs[esubst_ty0_def, try_eq_return, bind_EQ_return, bind_EQ_error, AllCaseEqs()]
  >- (rev_drule esubst_ty0_term_ok >> disch_then $ drule_then drule >> rw[]
      >> drule_all esubst_tm_preserves_term_ok >> strip_tac
      >> qexists ‘esubst_tm σ body'’
      >> dxrule VSUBST_ID >> rw[])
  >> qexists ‘esubst_tm σ v'’
  >> cheat
QED
       
Theorem nproves_substitutable:
  ∀h c n.
    theory_ok (sig, axs) ∧
    ((sig, axs), h, n:num) |n- c ∧
    safe_sequent_esubst σ c h ∧
    esubsts_ok sig σ ⇒
    ((esubst_sig σ sig, IMAGE (esubst σ []) axs),
                        term_image (esubst σ []) h,
                        100 * n + 100 * (LENGTH h * n) + 100)
    |n- esubst σ (FLAT (MAP tm_names h)) c
Proof
  completeInduct_on ‘n’
  >> simp[Once nproves_cases, SimpL “$==>”]
  >> rw[] >> gvs[]
  (* ABS *)
  >- (rw[] >> imp_res_tac nproves_term_ok
      >> ‘term_ok sig l’ by (dxrule theory_ok_sig >> simp[] >> metis_tac[term_ok_equation])
      >> ‘term_ok sig r’ by (dxrule theory_ok_sig >> simp[] >> metis_tac[term_ok_equation])
      >> qabbrev_tac ‘avds=FLAT (MAP tm_names h)’
      >> qspecl_then [‘σ’, ‘Abs (Var x ty) r’, ‘Abs (Var x ty) l’, ‘sig’, ‘avds’] mp_tac $
                     GEN_ALL esubst_equation
      >> simp[] >> disch_then SUBST_ALL_TAC >> rw[]

      (* esubst can make the binders asymmetrical, prove an ACONV version to the goal instead *)
      >> irule nproves_ACONV_concl1 >> rw[]

      (* the new terms are still well-typed *)
      >- (irule $ iffRL welltyped_equation
          >> irule $ iffRL EQUATION_HAS_TYPE_BOOL >> rw[]
          >- (irule esubst_welltyped >> simp[SF SFY_ss])
          >- (irule esubst_welltyped >> simp[SF SFY_ss])
          >> rw[esubst_def, esubst_tm_def, esubst_ty_def]
          >> ‘∃l1. esubst_ty0 [] σ avds (Abs (Var x ty) l) = return l1’
            by metis_tac[esubst_ty0_always_returns, term_ok_def]
          >> ‘∃r1. esubst_ty0 [] σ avds (Abs (Var x ty) r) = return r1’
            by metis_tac[esubst_ty0_always_returns, term_ok_def]
          >> gvs[] >> rev_drule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) typeof_esubst_tm_esubst_ty0
          >> rw[] >> drule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) typeof_esubst_tm_esubst_ty0
          >> rw[] >> rpt $ first_x_assum (qspec_then ‘sig’ mp_tac) >> rw[]
          >> ntac 2 $ dxrule_at Any esubst_ty0_type >> simp[ty_esubst_def] >> rw[]
          >> rpt $ first_x_assum drule >> rw[] >> dxrule theory_ok_sig >> rw[] >> gvs[]
          >> dxrule_all $ iffLR term_ok_equation >> simp[])

      (* binders get renamed based on the esubst_ty0 env=[] call, so look at this first *)
      >> ‘∃l1. esubst_ty0 [] σ avds (Abs (Var x ty) l) = return l1’
        by metis_tac[esubst_ty0_always_returns, term_ok_def]
      >> ‘∃r1. esubst_ty0 [] σ avds (Abs (Var x ty) r) = return r1’
        by metis_tac[esubst_ty0_always_returns, term_ok_def]
      >> gvs[]

      (* pick a new ACONV goal *)
      >> qabbrev_tac ‘y = NVARIANT x (FLAT (MAP tm_names (term_image (esubst σ []) h)))
                                   (l1 === r1)’
      >> qexists ‘esubst σ avds (Abs (Var y ty) (VSUBST [Var y ty, Var x ty] l)) ===
                  esubst σ avds (Abs (Var y ty) (VSUBST [Var y ty, Var x ty] r))’
      >> rw[]
      >> ‘¬MEM y (tm_names (l1 === r1))’ by metis_tac[NVARIANT_NAMES_THM]
      >> ‘¬MEM y (tm_names l1)’ by gvs[tm_names_def, equation_def, APPEND]
      >> ‘¬MEM y (tm_names r1)’ by gvs[tm_names_def, equation_def, APPEND]

      >> ‘¬VFREE_IN (Var y ty) l’ by (qspecl_then [‘[]’, ‘σ’, ‘avds’, ‘Abs (Var x ty) l’]
                                                  mp_tac $ cj 3 esubst_ty0_impossible1
                                      >> rw[] >> metis_tac[VFREE_IN_tm_names])
      >> ‘¬VFREE_IN (Var y ty) r’ by (qspecl_then [‘[]’, ‘σ’, ‘avds’, ‘Abs (Var x ty) r’]
                                                  mp_tac $ cj 3 esubst_ty0_impossible1
                                      >> rw[] >> metis_tac[VFREE_IN_tm_names])

      (* new binder is actually ACONV *)
      >- (irule ACONV_equation >> rw[]
          >- (irule esubst_welltyped >> simp[SF SFY_ss] >> metis_tac[term_ok_vsubst_variant])
          >- (irule esubst_welltyped >> simp[SF SFY_ss] >> metis_tac[term_ok_vsubst_variant])
          >- (irule esubst_welltyped >> simp[SF SFY_ss] >> metis_tac[term_ok_vsubst_variant])
          >- (irule esubst_welltyped >> simp[SF SFY_ss] >> metis_tac[term_ok_vsubst_variant])
          >> (irule esubst_ACONV >> conj_tac
              >- (irule ACONV_SYM >> irule replace_binder_ACONV >> metis_tac[term_ok_def])
              >- metis_tac[term_ok_vsubst_variant, term_ok_def]))

      (* we can prove the new binder version *)
      (* first, push the subst down *)
      >> simp[esubst_def, esubst_ty_def]
      >> ‘term_ok sig (Abs (Var y ty) (VSUBST [(Var y ty,Var x ty)] l))’
        by metis_tac[term_ok_def, term_ok_vsubst_variant]
      >> ‘∃v. esubst_ty0 [] σ avds (Abs (Var y ty) (VSUBST [(Var y ty,Var x ty)] l)) = return v’
        by metis_tac[esubst_ty0_always_returns]
      >> ‘term_ok sig (Abs (Var y ty) (VSUBST [(Var y ty,Var x ty)] r))’
        by metis_tac[term_ok_def, term_ok_vsubst_variant]
      >> ‘∃v. esubst_ty0 [] σ avds (Abs (Var y ty) (VSUBST [(Var y ty,Var x ty)] r)) = return v’
        by metis_tac[esubst_ty0_always_returns]
      >> simp[]


      >> ‘¬MEM y (tm_names l)’ by (qspecl_then [‘[]’, ‘σ’, ‘avds’, ‘Abs (Var x ty) l’] mp_tac $
                                               cj 3 esubst_ty0_impossible1
                                   >> rw[] >> strip_tac >> gvs[])
      >> drule_all esubst_ty0_abs_avds_binder
      >> disch_then $ qspecl_then [‘avds’, ‘x’] strip_assume_tac
      >> ‘¬MEM y (tm_names r)’ by (qspecl_then [‘[]’, ‘σ’, ‘avds’, ‘Abs (Var x ty) r’] mp_tac $
                                               cj 3 esubst_ty0_impossible1
                                   >> rw[] >> strip_tac >> gvs[])
      >> drule_all esubst_ty0_abs_avds_binder
      >> disch_then $ qspecl_then [‘avds’, ‘x’] strip_assume_tac
      >> gvs[esubst_ty0_def, try_eq_return, AllCaseEqs(), bind_EQ_error, bind_EQ_return]

      >- (irule nproves_ABS' >> rw[]
          >- (simp[EVERY_MEM] >> rpt strip_tac
              >> drule VFREE_IN_tm_names >> simp[]
              >> drule_then irule NVARIANT_SUBLIST_AVDS
              >> rw[] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS]
              >> metis_tac[])
          >- metis_tac[ty_esubst_type_ok_alt]
          >> last_x_assum $ qspec_then ‘n'’ mp_tac >> simp[]
          >> disch_then drule >> simp[esubst_equation, SF SFY_ss, esubst_def]
          >> strip_tac >> rename1 ‘esubst_tm σ l1 === esubst_tm σ r1’
          >> qabbrev_tac ‘thyσ = (esubst_sig σ sig,IMAGE (esubst σ []) axs)’
          >> qabbrev_tac ‘hσ = term_image (esubst σ []) h’
          >> gvs[esubst_ty_def]
          >> ‘∃lσ. esubst_ty0 [] σ avds l = return lσ’ by metis_tac[esubst_ty0_always_returns]
          >> ‘∃rσ. esubst_ty0 [] σ avds r = return rσ’ by metis_tac[esubst_ty0_always_returns]
          >> gvs[]

          (* reprove esubst_tm σ lσ === esubst_tm σ rσ but avoid x in hyps *)
          >> qabbrev_tac ‘hσ1 = term_image (esubst σ [x]) h’
          >> drule_at Any nproves_ACONV
          >> disch_then $ qspecl_then [‘hσ1’, ‘esubst_tm σ lσ === esubst_tm σ rσ’] mp_tac
          >> impl_tac
          >- (simp[] >> cheat)
          >> rw[]

          (* apply the VSUBST, but this is around the wrong way---need to commute. *)
          >> drule_at Any nproves_INST
          >> disch_then $ qspec_then ‘[(Var y (ty_esubst σ ty), Var x (ty_esubst σ ty))]’ mp_tac
          >> simp[] >> impl_tac
          >- gvs[ty_esubst_type_ok_alt, Abbr‘thyσ’]
          >> simp[]
          >> ‘term_image
              (VSUBST [(Var y (ty_esubst σ ty),Var x (ty_esubst σ ty))]) hσ1 = hσ1’
            by cheat
          >> rw[]
          >> ‘esubst_tm σ lσ has_type ty_esubst σ (typeof l)’
            by metis_tac[esubst_tm_has_type_ty0]
          >> drule VSUBST_equation >> rw[SF SFY_ss, has_type_var]
          >> irule nproves_ACONV_concl1 >> rw[]
          >- (irule $ iffRL welltyped_equation >> irule $ iffRL EQUATION_HAS_TYPE_BOOL
              >> rw[]
              >- (‘term_ok (esubst_sig σ sig) l1’
                    by (irule esubst_ty0_term_ok >> simp[]
                        >> first_x_assum $ irule_at Any >> simp[term_ok_vsubst_variant])
                  >> metis_tac[term_ok_welltyped, esubst_tm_preserves_term_ok])
              >- (‘term_ok (esubst_sig σ sig) r1’
                    by (irule esubst_ty0_term_ok >> simp[]
                        >> first_x_assum $ irule_at Any >> simp[term_ok_vsubst_variant])
                  >> metis_tac[term_ok_welltyped, esubst_tm_preserves_term_ok])
              >> irule typeof_esubst_tm_VSUBST_esubst_ty0 >> simp[SF SFY_ss]
              >> rpt $ first_x_assum (irule_at Any)
              >> rev_drule_at (Pos last) (iffLR term_ok_equation)
              >> drule theory_ok_sig >> simp[])
          >> qexists ‘VSUBST [(Var y (ty_esubst σ ty),Var x (ty_esubst σ ty))]
                      (esubst_tm σ lσ) ===
                      VSUBST [(Var y (ty_esubst σ ty),Var x (ty_esubst σ ty))]
                      (esubst_tm σ rσ)’ >> conj_tac
          >- (irule ACONV_equation >> rw[]
              >- cheat >- cheat >- cheat >- cheat
              >- rpt (dxrule_at (Pos last) esubst_ty_esubst_tm_VSUBST_comm
                      >> simp[] >> disch_then $ drule_at (Pos last) >> simp[]
                      >> disch_then drule_all >> simp[])
              >- (dxrule_at (Pos last) esubst_ty_esubst_tm_VSUBST_comm
                  >> simp[] >> disch_then $ drule_at (Pos last) >> simp[]
                  >> disch_then drule_all >> simp[]))
          >> ntac 2 $ pop_assum kall_tac >> pop_assum mp_tac
          >> ‘esubst_tm σ lσ has_type ty_esubst σ (typeof l)’
            by metis_tac[esubst_tm_has_type_ty0]
          >> drule VSUBST_equation >> rw[SF SFY_ss, has_type_var]
          >> drule nproves_ACONV
          >> disch_then $ qspecl_then [‘hσ’, ‘VSUBST [(Var y (ty_esubst σ ty),
                                                       Var x (ty_esubst σ ty))]
                                              (esubst_tm σ lσ) ===
                                              VSUBST [(Var y (ty_esubst σ ty),
                                                       Var x (ty_esubst σ ty))]
                                              (esubst_tm σ rσ)’] mp_tac
          >> simp[ACONV_REFL] >> impl_tac
          >- cheat
          >> rw[]
          >> irule nproves_le >> first_x_assum $ irule_at Any
          >> simp[]
          >> ‘LENGTH hσ ≤ LENGTH h’ by simp[term_image_LENGTH, Abbr‘hσ’]
          >> ‘LENGTH hσ1 ≤ LENGTH h’ by simp[term_image_LENGTH, Abbr‘hσ1’]
          >> rpt $ qpat_x_assum ‘_ ≥ _’ mp_tac
          >> rpt $ qpat_x_assum ‘_ ≤ _’ mp_tac >> rpt $ pop_assum kall_tac
          >> rw[])

      >- (irule nproves_ABS' >> rw[]
          >- (simp[EVERY_MEM] >> rpt strip_tac
              >> drule VFREE_IN_tm_names >> simp[]
              >> drule_then irule NVARIANT_SUBLIST_AVDS
              >> rw[] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS]
              >> metis_tac[])
          >- metis_tac[ty_esubst_type_ok_alt]
          >> last_x_assum $ qspec_then ‘n'’ mp_tac >> simp[]
          >> disch_then drule >> simp[esubst_equation, SF SFY_ss, esubst_def]
          >> strip_tac >> rename1 ‘esubst_tm σ l1 === esubst_tm σ r1’
          >> qabbrev_tac ‘thyσ = (esubst_sig σ sig,IMAGE (esubst σ []) axs)’
          >> qabbrev_tac ‘hσ = term_image (esubst σ []) h’
          >> gvs[esubst_ty_def]
          >> ‘∃lσ. esubst_ty0 [] σ avds l = return lσ’ by metis_tac[esubst_ty0_always_returns]
          >> ‘∃rσ. esubst_ty0 [] σ avds r = return rσ’ by metis_tac[esubst_ty0_always_returns]
          >> gvs[]
          (* apply the VSUBST, but this is around the wrong way---need to commute. *)
          >> drule_at Any nproves_INST
          >> disch_then $ qspec_then ‘[(Var y (ty_esubst σ ty), Var x (ty_esubst σ ty))]’ mp_tac
          >> simp[] >> impl_tac
          >- gvs[ty_esubst_type_ok_alt, Abbr‘thyσ’]
          >> simp[]
          >> ‘EVERY ($¬ ∘ VFREE_IN (Var x (ty_esubst σ ty))) hσ’ by cheat
          >> simp[term_image_VSUBST_VFREE]
          >> ‘esubst_tm σ lσ has_type ty_esubst σ (typeof l)’ by cheat
          >> drule VSUBST_equation >> rw[SF SFY_ss, has_type_var]
          >> irule nproves_ACONV_concl1 >> rw[]
          >- cheat
          >> qexists ‘VSUBST [(Var y (ty_esubst σ ty),Var x (ty_esubst σ ty))]
                      (esubst_tm σ body1'') ===
                      VSUBST [(Var y (ty_esubst σ ty),Var x (ty_esubst σ ty))]
                      (esubst_tm σ rσ)’ >> conj_tac
          >- (irule ACONV_equation >> rw[] >- cheat >- cheat >- cheat >- cheat
              >- rpt (dxrule_at (Pos last) esubst_ty_esubst_tm_VSUBST_comm
                      >> simp[] >> disch_then $ drule_at (Pos last) >> simp[]
                      >> disch_then drule_all >> simp[])
              >- (dxrule_at (Pos last) esubst_ty_esubst_tm_VSUBST_comm
                  >> simp[] >> disch_then $ drule_at (Pos last) >> simp[]
                  >> disch_then drule_all >> simp[]))
          >> ‘4 * n' + (3 * LENGTH h + 13) = 3 * LENGTH h + (4 * (n' + 1) + 9)’
            suffices_by metis_tac[] >> gvs[])

      >-  (irule nproves_ABS' >> rw[]
          >- (simp[EVERY_MEM] >> rpt strip_tac
              >> drule VFREE_IN_tm_names >> simp[]
              >> drule_then irule NVARIANT_SUBLIST_AVDS
              >> rw[] >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS]
              >> metis_tac[])
          >- metis_tac[ty_esubst_type_ok_alt]
          >> last_x_assum $ qspec_then ‘n'’ mp_tac >> simp[]
          >> disch_then drule >> simp[esubst_equation, SF SFY_ss, esubst_def]
          >> strip_tac >> rename1 ‘esubst_tm σ l1 === esubst_tm σ r1’
          >> qabbrev_tac ‘thyσ = (esubst_sig σ sig,IMAGE (esubst σ []) axs)’
          >> qabbrev_tac ‘hσ = term_image (esubst σ []) h’
          >> gvs[esubst_ty_def]
          >> ‘∃lσ. esubst_ty0 [] σ avds l = return lσ’ by metis_tac[esubst_ty0_always_returns]
          >> ‘∃rσ. esubst_ty0 [] σ avds r = return rσ’ by metis_tac[esubst_ty0_always_returns]
          >> gvs[]
          (* apply the VSUBST, but this is around the wrong way---need to commute. *)
          >> drule_at Any nproves_INST
          >> disch_then $ qspec_then ‘[(Var y (ty_esubst σ ty), Var x (ty_esubst σ ty))]’ mp_tac
          >> simp[] >> impl_tac
          >- gvs[ty_esubst_type_ok_alt, Abbr‘thyσ’]
          >> simp[]
          >> ‘EVERY ($¬ ∘ VFREE_IN (Var x (ty_esubst σ ty))) hσ’ by cheat
          >> simp[term_image_VSUBST_VFREE]
          >> ‘esubst_tm σ lσ has_type ty_esubst σ (typeof l)’ by cheat
          >> drule VSUBST_equation >> rw[SF SFY_ss, has_type_var]
          >> irule nproves_ACONV_concl1 >> rw[]
          >- cheat
          >> qexists ‘VSUBST [(Var y (ty_esubst σ ty),Var x (ty_esubst σ ty))]
                      (esubst_tm σ lσ) ===
                      VSUBST [(Var y (ty_esubst σ ty),Var x (ty_esubst σ ty))]
                      (esubst_tm σ body1'')’ >> conj_tac
          >- (irule ACONV_equation >> rw[] >- cheat >- cheat >- cheat >- cheat
              >- rpt (dxrule_at (Pos last) esubst_ty_esubst_tm_VSUBST_comm
                      >> simp[] >> disch_then $ drule_at (Pos last) >> simp[]
                      >> disch_then drule_all >> simp[])
              >- (dxrule_at (Pos last) esubst_ty_esubst_tm_VSUBST_comm
                  >> simp[] >> disch_then $ drule_at (Pos last) >> simp[]
                  >> disch_then drule_all >> simp[]))
          >> ‘4 * n' + (3 * LENGTH h + 13) = 3 * LENGTH h + (4 * (n' + 1) + 9)’
            suffices_by metis_tac[] >> simp[])
      >> cheat)
  (* ASSUME *)
  >- (irule nproves_ACONV_concl1 >> simp[] >> conj_tac
      >- simp[SF SFY_ss, esubst_welltyped]
      >> qexists ‘esubst σ [] c’ >> conj_tac
      >- (simp[esubst_def] >> irule esubst_tm_ACONV
          >> simp[SF SFY_ss, esubst_ty_avds_aconv, term_ok_welltyped]
          >> drule_all esubst_ty_term_ok >> strip_tac >> drule_all esubsts_ok_esubst_sig
          >> strip_tac >> first_x_assum $ irule_at Any >> metis_tac[])
      >> irule nproves_set_n_zero >> irule nproves_ASSUME >> rw[]
      >> simp[theory_ok_esubst_axs, esubst_has_type_bool, SF SFY_ss, esubst_term_ok])
  (* BETA *)
  >- (drule theory_ok_esubst_axs >> disch_then drule >> strip_tac
      >> first_x_assum $ qspec_then ‘[]’ assume_tac
      >> drule nproves_BETA >> simp[]
      >> disch_then $ qspecl_then [‘esubst σ [] t’, ‘ty_esubst σ ty’, ‘x’] mp_tac
      >> impl_tac >- simp[esubst_term_ok, SF SFY_ss, ty_esubst_type_ok_alt] >> rw[]
      >> ‘term_ok sig $ Comb (Abs (Var x ty) t) (Var x ty)’
        by simp[term_ok_def, term_ok_welltyped, SF SFY_ss]
      >> drule_then dxrule esubst_equation >> disch_then drule
      >> disch_then $ qspec_then ‘[]’ SUBST1_TAC
      >> simp[esubst_comb, term_ok_def, SF SFY_ss]
      >> ‘term_ok sig (Abs (Var x ty) t)’ by simp[term_ok_def]
      >> dxrule simple_esubst_Abs
      >> disch_then $ drule_then drule
      >> disch_then $ qspec_then ‘[]’ mp_tac
      >> rw[] >> pop_assum mp_tac >> disch_then SUBST_ALL_TAC >> rw[]
      >> irule nproves_ACONV_concl1 >> simp[] >> conj_tac
      >- (irule $ iffRL welltyped_equation >> irule $ iffRL EQUATION_HAS_TYPE_BOOL
          >> rw[typeof_def]
          >- (irule VSUBST_WELLTYPED >> simp[] >> cheat))
      >> qexists ‘Comb (Abs (Var x (ty_esubst σ ty)) (esubst σ [] t))
                  (Var x (ty_esubst σ ty)) === esubst σ [] t’ >> conj_tac
      >- (irule ACONV_equation >> simp[]
          >> ‘welltyped (esubst σ [] t)’ by cheat >> simp[] >> conj_tac
          >- cheat
          >> qpat_x_assum ‘ACONV _ _’ mp_tac
          >> simp[ACONV_def, RACONV]
          >> Induct_on ‘’))
  (* DEDUCT_ANTISYM *)
  >- (rename [‘n + 1’] >> first_assum $ qspec_then ‘m’ mp_tac
      >> first_x_assum $ qspec_then ‘n’ mp_tac >> simp[]
      >> rpt (disch_then $ drule_then strip_assume_tac)
      >> dxrule_at_then (Pos last) dxrule nproves_DEDUCT_ANTISYM >> rw[]
      >> irule nproves_ACONVi >> rw[]
      >- (ntac 2 $ rev_dxrule nproves_term_ok1
          >>  simp[EVERY_MEM, hypset_ok_term_image, hypset_ok_term_union, hypset_ok_term_remove])
      >- cheat
      >- ‘100 *
        (LENGTH (term_union (term_remove c2 h1) (term_remove c1 h2)) *
         (m + (n + 1))) + (100 * (m + (n + 1)) + 100) >
        3 *
        LENGTH
          (
             (term_union (term_remove c2 h1) (term_remove c1 h2))) + 1’ suffices_by metis_tac[term_image_LENGTH]
  (* EQ_MP *)
  >- (qabbrev_tac ‘thyσ = (esubst_sig σ sig,IMAGE (esubst σ []) axs)’
      >> first_assum $ qspec_then ‘m’ mp_tac >> cheat)
  (* INST *)
      >- (drule_at (Pos last) nproves_INST >> disch_then $ qspec_then ‘ilist’ mp_tac
          >> impl_tac >- (simp[] >> metis_tac[]) >> rw[]
          >> )
  (* INST_TYPE *)
  >- cheat
  (* MK_COMB *)
  >- cheat
  (* REFL *)
  >- (irule nproves_set_n_zero
      >> simp[esubst_equation, SF SFY_ss]
      >> irule nproves_REFL >> rw[]
      >> metis_tac[theory_ok_esubst_axs, esubst_term_ok])
  (* axiom *)
  >- (irule nproves_set_n_zero >> irule nproves_axioms >> rw[]
      >> irule theory_ok_esubst_axs >> rw[])
QED
(*
Theorem ACONV_esubst_env:
  esubsts_ok sig σ ∧ term_ok sig tm ∧ theory_ok (thy,axs) ⇒
  ACONV (esubst σ avds1 tm) (esubst σ avds2 tm)
Proof
  cheat
QED

Theorem esubst_typeof_eq:
  esubsts_ok sig σ ∧ term_ok sig c1 ∧ term_ok sig c2 ⇒
  (typeof (esubst σ avds1 c1) = typeof (esubst σ avds2 c2) ⇔
     typeof c1 = typeof c2)
Proof
  cheat
QED
        *)(*
Theorem welltyped_esubst_equation:
  term_ok sig tm1 ∧ term_ok sig tm2 ∧ esubsts_ok sig σ ∧ theory_ok (sig, axs) ∧
  typeof tm1 = typeof tm2 ⇒
  welltyped (esubst σ avds tm1 === esubst σ avds tm2)
Proof
  rw[] >> irule $ iffRL welltyped_equation >> irule $ iffRL EQUATION_HAS_TYPE_BOOL
  >> rw[] >> TRY (irule esubst_welltyped >> metis_tac[])
  >> irule $ iffRL esubst_typeof_eq >> metis_tac[]
QED*)
  (*
Theorem proves_substitutable:
  ∀sig axs h c.
    theory_ok (sig,axs) ∧
    ((sig, axs), h) |- c ∧
    esubsts_ok sig σ ⇒
    ((esubst_sig σ sig, IMAGE (esubst σ []) axs), term_image (esubst σ []) h)
    |- esubst σ (FLAT (MAP tm_names h)) c
Proof
  Induct_on ‘$|-’ >> rw[] >> gvs[]
  >- cheat
  >- (irule proves_ACONV >> simp[] >> conj_tac
      >- simp[SF SFY_ss, esubst_welltyped] >> conj_tac
      >- simp[esubst_term_ok, SF SFY_ss, esubst_has_type_bool]
      >> qexistsl [‘esubst σ [] c’, ‘[esubst σ [] c]’] >> conj_tac
      >- (simp[esubst_def] >> irule esubst_tm_ACONV
          >> simp[SF SFY_ss, esubst_ty_avds_aconv, term_ok_welltyped]
          >> drule_all esubst_ty_term_ok >> strip_tac >> drule_all esubsts_ok_esubst_sig
          >> strip_tac >> first_x_assum $ irule_at Any >> metis_tac[]) >> conj_tac
      >- simp[EVERY_MEM, ACONV_REFL]
      >> irule proves_ASSUME
      >> simp[theory_ok_esubst_axs, esubst_has_type_bool, SF SFY_ss, esubst_term_ok])
  >- cheat
  >- (drule_then assume_tac theory_ok_sig
      >> ‘term_ok sig c’ by (rev_dxrule proves_term_ok >> simp[EVERY_MEM])
      >> ‘term_ok sig c'’ by (rpt $ rev_dxrule proves_term_ok >> simp[EVERY_MEM])
      >> gvs[] >> gvs[esubst_equation, SF SFY_ss, term_ok_def]
      >> dxrule_at (Pos last) proves_DEDUCT_ANTISYM >> disch_then dxrule >> rw[]
      >> irule proves_ACONV >> rw[]
      >- (irule hypset_ok_term_image >> irule hypset_ok_term_union
          >> conj_tac >> irule hypset_ok_term_remove >> metis_tac[proves_term_ok, SND])
      >> ‘hypset_ok h1’ by (rev_dxrule proves_term_ok >> simp[])
      >> ‘hypset_ok h2’ by (rpt $ rev_dxrule proves_term_ok >> simp[])
      >- (irule welltyped_esubst_equation >> simp[SF SFY_ss] >> dxrule proves_term_ok
          >> rw[] >> dxrule $ iffLR EQUATION_HAS_TYPE_BOOL
          >> rw[] >> metis_tac[esubst_typeof_eq])
      >- (simp[EVERY_MEM] >> rw[] >> dxrule proves_term_ok >> rw[]
          >> gvs[EVERY_MEM]
          >> ‘term_ok (esubst_sig σ sig) x ∧ x has_type Bool’ suffices_by simp[]
          >> ntac 4 $ pop_assum kall_tac >> dxrule MEM_term_image_imp
          >> strip_tac >> dxrule MEM_term_union_imp >> strip_tac
          >> dxrule MEM_term_remove_imp >> strip_tac >> first_x_assum drule
          >> strip_tac >> qpat_x_assum ‘x = _’ SUBST_ALL_TAC >> rpt $ dxrule proves_term_ok
          >> rw[] >> gvs[EVERY_MEM] >> metis_tac[esubst_term_ok, esubst_has_type_bool])
      >> first_x_assum $ irule_at (Pos last) >> rw[]
      >- (irule ACONV_equation >> rw[]
          >> TRY (irule term_ok_welltyped >> metis_tac[esubst_term_ok, SF SFY_ss])
          >> metis_tac[ACONV_esubst_env])
      >> rw[EVERY_MEM, EXISTS_MEM] >> dxrule MEM_term_union_imp >> rw[]
      >- (dxrule MEM_term_remove_imp >> strip_tac
          >> drule hypset_ok_term_image >> rw[] >> gvs[] >> pop_assum kall_tac
          >> dxrule MEM_term_image_imp >> rw[] >> irule MEM_term_image
          >> conj_tac >- (irule hypset_ok_term_union >> conj_tac
                          >> irule hypset_ok_term_remove >> simp[])
          >> irule MEM_term_union_first >> rw[]
          >> irule MEM_term_remove >> simp[] >> gvs[hypset_ok_term_image]
          >> qpat_x_assum ‘¬ACONV _ _’ mp_tac >> contrapos_tac >> gvs[]
          >> drule_at (Pos last) esubst_ACONV >> disch_then $ drule_then drule
          >> simp[] >> disch_then $ qspec_then ‘[]’ mp_tac >> impl_tac
          >- (irule term_ok_aconv
              >- (rpt $ dxrule proves_term_ok >> rw[]
                  >> gvs[EVERY_MEM] >> first_x_assum drule
                  >> simp[welltyped_def, SF SFY_ss])
              >> first_x_assum $ irule_at Any >> metis_tac[])
          >> metis_tac[ACONV_TRANS, ACONV_esubst_env])
      >- (dxrule MEM_term_remove_imp >> strip_tac >> gvs[hypset_ok_term_image]
          >> dxrule MEM_term_image_imp >> rw[]
          >> Cases_on ‘ACONV c x'’
          >- (dxrule esubst_ACONV >> disch_then $ drule_then rev_dxrule
              >> disch_then $ drule_at (Pos last) >> rw[]
              >> first_x_assum $ qspec_then ‘[]’ mp_tac
              >> qsuff_tac‘term_ok sig x'’ >> rw[]
              >- (‘ACONV (esubst σ [] c) (esubst σ (FLAT (MAP tm_names h1)) c)’
                    by (irule ACONV_esubst_env >> simp[SF SFY_ss]
                        >> first_x_assum $ irule_at Any >> drule proves_theory_ok
                        >> rw[] >> first_x_assum $ irule_at Any
                        >> rev_dxrule proves_term_ok >> rw[EVERY_MEM])
                  >> metis_tac[ACONV_TRANS, ACONV_SYM])
              >> dxrule proves_term_ok >> rw[EVERY_MEM])
          >> drule_all MEM_term_remove >> rw[]
          >> qspecl_then [‘term_remove c' h1’, ‘term_remove c h2’] mp_tac MEM_term_union
          >> simp[hypset_ok_term_remove] >> disch_then $ qspec_then ‘x'’ mp_tac >> rw[]
          >> dxrule MEM_term_image >> simp[hypset_ok_term_remove]
          >> disch_then $ qspec_then ‘esubst σ []’ mp_tac >> rw[]
          >> qexists ‘y'’ >> simp[] >> qpat_x_assum ‘ACONV x' y’ assume_tac
          >> dxrule_at (Pos last) esubst_ACONV >> disch_then $ drule_then drule
          >> impl_tac
          >- (conj_tac
              >- (rpt $ dxrule proves_term_ok >> simp[EVERY_MEM] >> rw[]
                  >> dxrule MEM_term_remove_imp >> rw[] >> gvs[])
              >> cheat)
          >> metis_tac[ACONV_TRANS, ACONV_esubst_env, ACONV_SYM, esubst_ACONV]))
  >- cheat
  >- cheat
  >- (dxrule_at (Pos last) proves_DEDUCT_ANTISYM >> disch_then dxrule
      >> rw[]
      >> ‘term_ok sig c’ by (rev_dxrule proves_term_ok >> simp[EVERY_MEM])
      >> ‘term_ok sig c'’ by (rpt $ rev_dxrule proves_term_ok >> simp[EVERY_MEM])
      >> gvs[] >> drule_then assume_tac theory_ok_sig >> gvs[]
      >> gvs[esubst_equation, SF SFY_ss, term_ok_def]
      >> irule proves_ACONV >> rw[]
      >- (irule hypset_ok_term_image >> irule hypset_ok_term_union
          >> conj_tac >> irule hypset_ok_term_remove >> cheat))
QED
  *)

Theorem vsubst_names_safe_sequent_esubst:
  (∀s s'.
     MEM (s',s) ilist ⇒
     ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok (sigof (sig,axs)) s') ∧
  safe_sequent_esubst σ (VSUBST ilist c) (term_image (VSUBST ilist) h) ⇒
  safe_sequent_esubst σ c h
Proof
  cheat
QED
  
Theorem safe_sequent_esubst_weakening:
  ∀c hs c1 hs1.
    safe_sequent_esubst σ c1 hs1 ∧
    term_ok sig c ∧ EVERY (term_ok sig) hs ∧
    term_ok sig c1 ∧ EVERY (term_ok sig) hs1 ∧
    FVs c ⊆ FVs c1 ∧
    BIGUNION (set (MAP FVs hs)) ⊆ BIGUNION (set (MAP FVs hs1)) ⇒
    safe_sequent_esubst σ c hs
Proof
  rw[safe_sequent_esubst_def] >> gvs[EXTENSION, SUBSET_DEF]
  >- (first_x_assum irule >> rw[] >> gvs[FORALL_PROD, EXISTS_PROD]
      >> drule_all $ iffLR FVs_VFREE_in >> rev_drule_all $ iffLR FVs_VFREE_in
      >> rw[] >> rpt $ first_assum dxrule >> metis_tac[FVs_VFREE_in])
  >- (first_x_assum irule >> rw[] >> gvs[FORALL_PROD, EXISTS_PROD]
      >> drule_all $ iffLR FVs_VFREE_in >> strip_tac >> first_x_assum drule
      >> rw[] >> qexists ‘n’ >> conj_tac >- metis_tac[FVs_VFREE_in]
      >> disj2_tac >> gvs[EXISTS_MEM, FVs_VFREE_in, MEM_MAP, EVERY_MEM]
      >> first_x_assum $ qspecl_then [‘n’, ‘ty2’] mp_tac >> impl_tac
      >- (qexists ‘FVs e’ >> conj_tac >> metis_tac[FVs_VFREE_in])
      >> rw[] >> metis_tac[FVs_VFREE_in])
  >> (first_x_assum irule >> rw[]
      >> gvs[FORALL_PROD, EXISTS_PROD, EVERY_MEM, EXISTS_MEM, MEM_MAP]
      >> qexists ‘n’ >> conj_tac
      >- (disj2_tac >> first_x_assum $ qspecl_then [‘n’, ‘ty1’] mp_tac >> impl_tac
          >- (qexists ‘FVs e’ >> conj_tac >> metis_tac[FVs_VFREE_in])
          >> rw[] >> metis_tac[FVs_VFREE_in])
      >> rw[] >> metis_tac[FVs_VFREE_in])
QED

Theorem safe_sequent_esubst_VSUBST:
  term_ok sig c ∧ EVERY (term_ok sig) h ∧
  (∀s s'. MEM (s',s) ilist ⇒
          ∃x ty. s = Var x ty ∧ s' has_type ty ∧
                 term_ok (sigof (sig,axs)) s') ⇒
  (safe_sequent_esubst σ (VSUBST ilist c) (term_image (VSUBST ilist) h) ⇔
     safe_sequent_esubst σ c h)
Proof
  cheat
QED

(* INST only changes type variables *)
Theorem safe_sequent_esubst_INST:
  term_ok sig c ∧ EVERY (type_ok (tysof sig)) (MAP FST tyin) ∧ esubsts_ok sig σ ∧
  (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
  safe_sequent_esubst σ (INST tyin c) (term_image (INST tyin) h) ⇒
  safe_sequent_esubst σ c h
Proof
  rw[safe_sequent_esubst_def] >> Cases_on ‘t’ >> Cases_on ‘t'’
  >> rename [‘SND (x, ty) ≠ SND (n, typ)’] >> gvs[]
  >> Induct_on ‘ty’ using type_ind >> simp[ty_esubst_def]
  >> Induct_on ‘typ’ using type_ind >> simp[ty_esubst_def]
  >> first_x_assum irule
  >- (rw[] >> simp[MEM_MAP] >> qexists ‘t’ >> simp[] >> gvs[INST_def]
      >> qspecl_then [‘sizeof c’, ‘c’, ‘[]’, ‘tyin’] mp_tac INST_CORE_HAS_TYPE
      >> simp[] >> strip_tac >> gvs[term_ok_welltyped, SF SFY_ss]
      >- metis_tac[INST_CORE_NIL_IS_RESULT, IS_RESULT_IMP, term_ok_welltyped, SF SFY_ss]
      >- (Cases_on ‘t’  >> gvs[REV_ASSOCD] >> rename1 ‘(n, ty) ∈ FVs c’
          >> first_x_assum $ qspecl_then [‘n’, ‘ty’] (mp_tac o iffRL) >> rw[]
          >> disj1_tac >> irule $ iffLR FVs_VFREE_in >> first_x_assum $ irule_at Any
          >> simp[SF SFY_ss]
          >> qspecl_then [‘sig’, ‘[]’, ‘tyin’, ‘c’] mp_tac term_ok_INST_CORE >> rw[]
          >> qexistsl[‘sig’,‘ty’] >> simp[] >> drule_all $ iffRL FVs_VFREE_in >> rw[]
          >> sym_tac >> irule monomorphic_type_subst))
QED 
        
Theorem proves_substitutable:
  ∀sig axs h c.
    theory_ok (sig,axs) ∧
    ((sig, axs), h) |- c ∧
    esubsts_ok sig σ ∧
    safe_sequent_esubst σ c h ⇒
    ((esubst_sig σ sig, IMAGE (esubst σ []) axs), term_image (esubst σ []) h)
    |- esubst σ (FLAT (MAP tm_names h)) c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- cheat
  >- (irule proves_ACONV >> simp[] >> gvs[] >> conj_tac
      >- simp[SF SFY_ss, esubst_welltyped] >> conj_tac
      >- simp[esubst_term_ok, SF SFY_ss, esubst_has_type_bool]
      >> qexistsl [‘esubst σ [] c’, ‘[esubst σ [] c]’] >> conj_tac
      >- (simp[esubst_def] >> irule esubst_tm_ACONV
          >> simp[SF SFY_ss, esubst_ty_avds_aconv, term_ok_welltyped]
          >> drule_all esubst_ty_term_ok >> strip_tac >> drule_all esubsts_ok_esubst_sig
          >> strip_tac >> first_x_assum $ irule_at Any >> metis_tac[]) >> conj_tac
      >- simp[EVERY_MEM, ACONV_REFL]
      >> irule proves_ASSUME
      >> simp[theory_ok_esubst_axs, esubst_has_type_bool, SF SFY_ss, esubst_term_ok])
  >- cheat
  >- cheat
  >- cheat
  >- (gvs[] >> dxrule_at (Pos last) $ iffLR safe_sequent_esubst_VSUBST
      >> disch_then $ qspecl_then [‘sig’, ‘axs’] mp_tac >> impl_tac
      >- (gvs[] >> dxrule proves_term_ok >> simp[EVERY_MEM])
      >> rw[] >> first_x_assum drule >> strip_tac >> drule_at (Pos last) proves_INST
      >> qabbrev_tac ‘ilistσ = MAP (λ(v,k). (esubst_ty σ [] v,esubst_ty σ [] k)) ilist’
      >> disch_then $ qspec_then ‘ilistσ’ mp_tac >> impl_tac
      >- (rw[Abbr‘ilistσ’, MEM_MAP] >> Cases_on ‘y’ >> gvs[]
          >> first_x_assum drule >> rw[] >> rw[SF SFY_ss]
          >> gvs[esubst_ty_def, esubst_ty0_def] >> CASE_TAC
          >- (irule $ iffRL typeof_has_type
              >> drule esubst_ty0_term_ok >> simp[] >> disch_then drule
              >> simp[term_ok_welltyped, SF SFY_ss] >> strip_tac
              >> qsuff_tac ‘ty = typeof q’ >> rw[]
              >- (irule esubst_ty0_type >> rw[] >> first_x_assum $ irule_at Any
                  >> simp[])
              >> metis_tac[has_type_typeof])
          >- metis_tac[esubst_ty0_always_returns, neq_error]
          >- (irule esubst_ty0_term_ok >> simp[] >> first_x_assum $ irule_at Any
              >> simp[])
          >> metis_tac[esubst_ty0_always_returns, neq_error])
      >> rw[] >> cheat (* esubst vsubst commute lemma *))
  >- ()

     
  rw[] >> qspecl_then [‘h’, ‘c’] mp_tac nproves_substitutable
  >> rw[] >> metis_tac[nproves_proves]
QED

val _ = export_theory()
