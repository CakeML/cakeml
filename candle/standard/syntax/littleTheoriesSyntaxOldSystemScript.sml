(*
  Some lemmas about the extended Little Theories syntactic functions.
*)
open preamble totoTheory comparisonTheory ternaryComparisonsTheory mlstringTheory
              holSyntaxLibTheory holSyntaxTheory errorMonadTheory
              littleTheoriesSyntaxTheory holSyntaxExtraTheory

val _ = new_theory"littleTheoriesSyntaxOldSystem"

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad("error");

val cpn_distinct = TypeBase.distinct_of “:ordering”
val cpn_nchotomy = TypeBase.nchotomy_of “:ordering”

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

Theorem typeof_vsubst1:
  ∀tm ilist.
    term_ok sig tm ∧
    (∀v1 v2. MEM (v1, v2) ilist ⇒ ∃n1 n2 ty. v1 has_type ty ∧ v2 = Var n2 ty) ⇒
    typeof (VSUBST ilist tm) = typeof tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, term_ok_def]
  >- (qspecl_then [‘ilist’, ‘Var m t’, ‘Var m t’] strip_assume_tac REV_ASSOCD_MEM
      >- (first_x_assum drule >> simp[PULL_EXISTS, has_type_typeof])
      >> simp[])
  >- (gvs[] >> first_x_assum irule >> rw[MEM_FILTER] >> first_x_assum drule
      >> rw[has_type_typeof])
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

Theorem ty_esubst_TYPE_SUBST_comm:
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
  >> metis_tac[ty_esubst_TYPE_SUBST_comm]
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

Definition simple_esubst_def:
  simple_esubst (σ:(mlstring |-> type) # (mlstring |-> term)) (Var x ty) =
  Var x (ty_esubst σ ty) ∧
  simple_esubst σ (Const x ty) = Const x (ty_esubst σ ty) ∧
  simple_esubst σ (Comb e1 e2) = Comb (simple_esubst σ e1) (simple_esubst σ e2) ∧
  simple_esubst σ (Abs v body) = Abs (simple_esubst σ v) (simple_esubst σ body)
End

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
    BasicProvers.VAR_EQ_TAC >> qmatch_assum_rename_tac‘welltyped tm’ >>
    fsrw_tac[ARITH_ss][] >>
    Q.PAT_ABBREV_TAC‘env' = X::env’ >>
    ‘∃v. esubst_ty0 [] σ avds tm = return v’ by metis_tac[esubst_ty0_always_returns]
    >> gvs[]
    >> qabbrev_tac ‘env' = (Var (NVARIANT n' avds v) ty,
                            Var (NVARIANT n' avds v) (ty_esubst σ ty))::env’
    >> qabbrev_tac ‘tm' = VSUBST [(Var (NVARIANT n' avds v) ty,Var n' ty)] tm’
    >> ‘sizeof tm' = sizeof tm’ by simp[Abbr‘tm'’,SIZEOF_VSUBST] >>
    ‘welltyped tm'’ by (
      simp[Abbr‘tm'’] >>
      match_mp_tac VSUBST_WELLTYPED >>
      simp[] >> simp[Once has_type_cases] ) >>
    first_x_assum(qspec_then‘sizeof tm’mp_tac) >> simp[] >>
    simp[Once esubst_ty0_def] >>
    disch_then(fn th =>
      qspecl_then[‘tm’,‘env'’]mp_tac th >>
      qspecl_then[‘tm'’,‘env''’]mp_tac th >>
      qspecl_then[‘tm’,‘[]’]mp_tac th) >> simp[] >>
    qmatch_abbrev_tac‘a ⇒ b’ >> strip_tac >> qunabbrev_tac‘b’ >>
    qmatch_abbrev_tac‘(p ⇒ q) ⇒ r’ >>
    ‘p’ by (
      unabbrev_all_tac >> rw[] >> metis_tac[term_ok_vsubst_variant]) >>
    simp[] >> map_every qunabbrev_tac[‘p’,‘q’,‘r’] >> pop_assum kall_tac >>
    qmatch_abbrev_tac‘x ⇒ (p ⇒ q) ⇒ r’ >>
    ‘p’ by (
      unabbrev_all_tac >> rw[] >> metis_tac[]) >>
    simp[] >> map_every qunabbrev_tac[‘x’,‘p’,‘q’,‘r’] >> pop_assum kall_tac >>
    qunabbrev_tac‘a’ >> fs[]
    >>
    strip_tac >> fs[] >- (
      strip_tac >> fs[] >- (
        rfs[Abbr‘env''’,Abbr‘env'’,REV_ASSOCD,Abbr‘tm'’,VFREE_IN_VSUBST] >>
        rw[] >> fs[] >>
        BasicProvers.EVERY_CASE_TAC >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[]
        >- metis_tac[NVARIANT_THM]
        >> simp[try_def, AllCaseEqs()] >> metis_tac[NVARIANT_THM]) >>
      rfs[Abbr‘env''’,Abbr‘env'’,REV_ASSOCD,Abbr‘tm'’,VFREE_IN_VSUBST] >>
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
        >> rfs[Abbr‘env''’,Abbr‘env'’,REV_ASSOCD,Abbr‘tm'’,VFREE_IN_VSUBST]
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
  Cases_on ‘σ’ >> rw[esubsts_ok_def, only_esubsts_consts_def] >> metis_tac[]
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
  ∀tm v n σ. only_esubsts_consts (SND σ) ⇒
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

Theorem db_esubst_thm:
  ∀tm avds.
    esubsts_ok sig σ ∧ term_ok sig tm ⇒
    db (esubst σ avds tm) = db_esubst σ (db tm)
Proof
  rw[db_esubst_def, esubst_def, esubst_ty_def] >> imp_res_tac term_ok_welltyped
  >> ‘∃tm1. esubst_ty0 [] σ avds tm = return tm1’ by metis_tac[esubst_ty0_always_returns]
  >> simp[] >> drule_then (drule_then drule) db_esubst_ty_thm >> disch_then $ drule_at Any
  >> simp[] >> disch_then $ SUBST1_TAC o GSYM >> irule db_esubst_tm_thm
  >> simp[esubsts_ok_only_esubsts_consts, SF SFY_ss] >> drule esubst_ty0_term_ok
  >> simp[] >> metis_tac[]
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

Theorem ACONV_EQ:
  ∀x y. x = y ⇒ ACONV x y
Proof
  rw[ACONV_def]
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
    ACONV (esubst σ avds1 tm1) (esubst σ avds2 tm2)
Proof
  rw[esubst_def] >> irule esubst_tm_ACONV >> rw[]
  >- (irule $ iffRL ACONV_db >> rpt conj_tac
      >- metis_tac[esubst_ty_welltyped]
      >- metis_tac[esubst_ty_welltyped]
      >> gvs[esubst_ty_def]
      >> ‘∃v. esubst_ty0 [] σ avds1 tm1 = return v’
        by metis_tac[esubst_ty0_always_returns]
      >> ‘∃v. esubst_ty0 [] σ avds2 tm2 = return v’
        by metis_tac[esubst_ty0_always_returns]
      >> gvs[]
      >> dxrule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) db_esubst_ty_thm
      >> dxrule_at (Pat ‘esubst_ty0 _ _ _ _ = _’) db_esubst_ty_thm
      >> simp[] >> rpt $ disch_then (drule_then strip_assume_tac) >> gvs[]
      >> imp_res_tac term_ok_welltyped >> gvs[]
      >> metis_tac[ACONV_db])
  >> gvs[esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds1 tm1 = return v’
    by metis_tac[esubst_ty0_always_returns]
  >> ‘∃v. esubst_ty0 [] σ avds2 tm2 = return v’
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
  term_ok sig a ∧
  (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
  VSUBST ilist (a === b) = VSUBST ilist a === VSUBST ilist b
Proof
  rw[equation_def, VSUBST_def] >> drule term_ok_welltyped
  >> rw[welltyped_def] >> drule_all VSUBST_HAS_TYPE
  >> metis_tac[has_type_typeof, term_ok_welltyped, welltyped_def]
QED

Theorem VSUBST_sing_var[simp]:
  VSUBST [z, y] (Var x ty) = if Var x ty = y then z else Var x ty
Proof
  rw[VSUBST_def, REV_ASSOCD]
QED

Theorem INST_COMB:
  welltyped e1 ∧ welltyped e2 ⇒
  INST tyin (Comb e1 e2) = Comb (INST tyin e1) (INST tyin e2)
Proof
  rw[INST_def, INST_CORE_def, AllCaseEqs()] >> rpt CASE_TAC
  >> metis_tac[INST_CORE_NIL_IS_RESULT, NOT_IS_CLASH_IS_RESULT]
QED

Theorem ACONV_COMB:
  ACONV (Comb a b) (Comb x y) ⇔ ACONV a x ∧ ACONV b y
Proof
  rw[ACONV_def, RACONV]
QED

val refl_aconv_tac = ‘∀a b. a = b ⇒ ACONV a b’ by simp[ACONV_REFL] >> first_x_assum irule

Definition vtys_ok_def:
  (vtys_ok (sig:SIG) (dbVar n ty) ⇔ type_ok (tysof sig) ty) ∧
  (vtys_ok sig (dbConst n ty) ⇔ type_ok (tysof sig) ty) ∧
  (vtys_ok sig (dbBound n) ⇔ T) ∧
  (vtys_ok sig (dbAbs v body) ⇔ type_ok (tysof sig) v ∧ vtys_ok sig body) ∧
  (vtys_ok sig (dbComb e1 e2) ⇔ vtys_ok sig e1 ∧ vtys_ok sig e2)
End

val dbrws = [dbINST_def, db_esubst_def, db_esubst_tm_def, db_esubst_ty_def,
             term_ok_def, db_def, vtys_ok_def, dbVSUBST_def]

Theorem db_esubst_dbINST_comm:
  ∀dbtm tyin.
    EVERY (type_ok (tysof sig)) (MAP FST tyin) ∧
    esubsts_ok sig σ ∧ vtys_ok sig dbtm ⇒
    db_esubst σ (dbINST tyin dbtm) =
    dbINST (MAP (λ(ty,a). (ty_esubst σ ty,a)) tyin) (db_esubst σ dbtm)
Proof
  Induct_on ‘dbtm’ >> rw[]
  >> gvs dbrws
  >- (irule ty_esubst_TYPE_SUBST_comm >> Cases_on ‘sig’ >> gvs[]
      >> first_x_assum $ irule_at Any >> irule type_ok_TYPE_SUBST >> rw[])
  >- (rpt CASE_TAC >> gvs dbrws
      >- (irule ty_esubst_TYPE_SUBST_comm >> Cases_on ‘sig’
          >> first_x_assum $ irule_at Any >> irule type_ok_TYPE_SUBST >> gvs[])
      >> Cases_on ‘σ’ >> rename1 ‘esubsts_ok sig (σ,θ)’ >> gvs[esubsts_ok_def]
      >> first_x_assum $ qspec_then ‘x’ mp_tac >> impl_tac >- metis_tac[FRANGE_FLOOKUP]
      >> rw[] >> rw[db_def, dbINST_def, monomorphic_type_subst])
  >> first_x_assum drule >> rw[] >> irule ty_esubst_TYPE_SUBST_comm
  >> Cases_on ‘sig’ >> gvs[] >> first_x_assum $ irule_at Any
  >> irule type_ok_TYPE_SUBST >> simp[]
QED

Definition FVL_def:
  FVL (Var n ty) = [(n, ty)] ∧
  FVL (Const n ty) = [] ∧
  FVL (Comb e1 e2) = FVL e1 ++ FVL e2 ∧
  FVL (Abs v body) = FILTER (λtm. ¬MEM tm (FVL v)) (FVL body)
End

Definition alist_dedup_keys_def:
  alist_dedup_keys [] = [] ∧
  alist_dedup_keys ((v,k)::t) = (v,k)::FILTER (λ(v1,k1). k1 ≠ k) (alist_dedup_keys t)
End

Definition esubst_ilist_def:
  esubst_ilist ilist σ avds tm =
  alist_dedup_keys $
  MAP (λ(n,ty).
         (esubst σ avds (REV_ASSOCD (Var n ty) ilist (Var n ty)),
          esubst σ avds (Var n ty)))
      (FVL tm)
End

Definition dbFVL_def:
  dbFVL (dbVar n ty) = [(n, ty)] ∧
  dbFVL (dbConst n ty) = [] ∧
  dbFVL (dbBound n) = [] ∧
  dbFVL (dbComb e1 e2) = dbFVL e1 ++ dbFVL e2 ∧
  dbFVL (dbAbs v body) = dbFVL body
End

Definition dbFVs_def:
  dbFVs (dbVar n ty) = {(n, ty)} ∧
  dbFVs (dbConst n ty) = {} ∧
  dbFVs (dbBound n) = {} ∧
  dbFVs (dbComb e1 e2) = dbFVs e1 ∪ dbFVs e2 ∧
  dbFVs (dbAbs v body) = dbFVs body
End

Definition db_esubst_ilist_def:
  db_esubst_ilist ilist σ dbtm =
  alist_dedup_keys $
  MAP (λ(n,ty).
         (db_esubst σ (REV_ASSOCD (dbVar n ty) ilist (dbVar n ty)),
          db_esubst σ (dbVar n ty)))
      (dbFVL dbtm)
End

Theorem db_esubst_ilist_const[simp]:
  db_esubst_ilist ilist σ (dbConst m t) = []
Proof
  rw[db_esubst_ilist_def, dbFVL_def, alist_dedup_keys_def]
QED

Theorem db_esubst_ty_VFREE_IN:
  esubsts_ok sig σ ⇒
  ∀u uty.
    dbVFREE_IN (dbVar u uty) (db_esubst_ty σ tm) ⇔
      ∃oty. dbVFREE_IN (dbVar u oty) tm ∧ uty = ty_esubst σ oty
Proof
  Induct_on ‘tm’ >> rw[db_esubst_ty_def, dbVFREE_IN_def, EQ_IMP_THM]
  >> metis_tac[dbVFREE_IN_def]
QED

Definition no_dbvar_collapse:
  no_dbvar_collapse σ tm ⇔
    ∀x ty1 ty2. dbVFREE_IN (dbVar x ty1) tm ∧ dbVFREE_IN (dbVar x ty2) tm ∧ ty1 ≠ ty2 ⇒
                ty_esubst σ ty1 ≠ ty_esubst σ ty2
End

Theorem no_dbvar_collapse_comb:
  no_dbvar_collapse σ (dbComb dbtm1 dbtm2) ⇒
  no_dbvar_collapse σ dbtm1 ∧ no_dbvar_collapse σ dbtm2
Proof
  rw[no_dbvar_collapse] >> metis_tac[]
QED

Theorem no_dbvar_collapse_abs:
  no_dbvar_collapse σ (dbAbs ty t) ⇒ no_dbvar_collapse σ t
Proof
  rw[no_dbvar_collapse] >> metis_tac[]
QED

Theorem no_var_collapse_no_dbvar_collapse:
  welltyped tm ∧ no_var_collapse σ tm ⇒ no_dbvar_collapse σ (db tm)
Proof
  Induct_on ‘tm’ >> rw[no_var_collapse, no_dbvar_collapse]
  >- (first_x_assum irule >> simp[] >> qexists ‘x’ >> rw[]
      >> disj1_tac >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[])
  >- (first_x_assum irule >> simp[] >> qexists ‘x’ >> rw[]
      >- (disj1_tac >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[])
      >> disj2_tac >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[])
  >- (first_x_assum irule >> simp[] >> qexists ‘x’ >> rw[]
      >- (disj2_tac >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[])
      >> disj1_tac >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[])
  >- (first_x_assum irule >> simp[] >> qexists ‘x’ >> rw[]
      >> disj2_tac >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[])
  >> first_x_assum irule >> simp[] >> gvs[dbVFREE_IN_bind]
  >> qexists ‘x’ >> rw[] >> irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[]
QED

Definition no_combined_collapse:
  no_combined_collapse σ ilist dbtm ⇔
    ∀x ty1 ty2.
      (dbVFREE_IN (dbVar x ty1) dbtm ∨ (∃v1. MEM (v1, dbVar x ty1) ilist)) ∧
      (∃v2. MEM (v2, dbVar x ty2) ilist) ∧
      ty1 ≠ ty2 ⇒
      ty_esubst σ ty1 ≠ ty_esubst σ ty2
End

Theorem no_combined_collapse_comb:
  no_combined_collapse σ ilist (dbComb dbtm1 dbtm2) ⇒
  no_combined_collapse σ ilist dbtm1 ∧ no_combined_collapse σ ilist dbtm2
Proof
  rw[no_combined_collapse] >> metis_tac[]
QED

Theorem no_combined_collapse_abs:
  no_combined_collapse σ ilist (dbAbs ty t) ⇒ no_combined_collapse σ ilist t
Proof
  rw[no_combined_collapse] >> metis_tac[]
QED

Theorem no_dbvar_collapse_no_combined_collapse:
  no_dbvar_collapse σ dbtm ∧
  (∀s2 s. MEM (s2,s) ilist ⇒ ∃x ty. s = dbVar x ty ∧ dbVFREE_IN s dbtm) ⇒
  no_combined_collapse σ ilist dbtm
Proof
  rw[no_dbvar_collapse, no_combined_collapse]
  >> Cases_on ‘∃v1. MEM (v1, dbVar x ty1) ilist’
  >- (first_x_assum drule >> rw[] >> first_x_assum drule_all >> simp[])
  >- (first_x_assum drule >> rw[] >> first_x_assum drule_all >> simp[])
  >> gvs[] >> first_assum dxrule >> first_x_assum dxrule >> rw[]
  >> first_x_assum drule_all >> simp[]
QED

Theorem db_esubst_ty_REV_ASSOCD_comm_gen:
  ∀ilist x ty d.
    (∀ty'. (∃v'. MEM (v', dbVar x ty') ilist) ∧ ty' ≠ ty ⇒
           ty_esubst σ ty' ≠ ty_esubst σ ty) ∧
    (∀s2 s. MEM (s2,s) ilist ⇒ ∃x ty. s = dbVar x ty) ⇒
    db_esubst_ty σ (REV_ASSOCD (dbVar x ty) ilist d) =
    REV_ASSOCD (dbVar x (ty_esubst σ ty))
               (MAP (λ(v,k). (db_esubst_ty σ v, db_esubst_ty σ k)) ilist)
               (db_esubst_ty σ d)
Proof
  Induct >> rw[REV_ASSOCD] >> Cases_on ‘h’ >> gvs[DISJ_IMP_THM, REV_ASSOCD, AllCaseEqs()]
  >> rw[] >> gvs[db_esubst_ty_def, REV_ASSOCD] >> disj2_tac >> conj_tac
  >- (first_x_assum $ qspecl_then [‘q’, ‘r’] mp_tac >> rw[] >> rw[db_esubst_ty_def])
  >> metis_tac[]
QED

Theorem db_esubst_ty_REV_ASSOCD_comm:
  ∀ilist x ty.
    (∀ty'. (∃v'. MEM (v', dbVar x ty') ilist) ∧ ty' ≠ ty ⇒
           ty_esubst σ ty' ≠ ty_esubst σ ty) ∧
    (∀s2 s. MEM (s2,s) ilist ⇒ ∃x ty. s = dbVar x ty) ⇒
    db_esubst_ty σ (REV_ASSOCD (dbVar x ty) ilist (dbVar x ty)) =
    REV_ASSOCD (dbVar x (ty_esubst σ ty))
               (MAP (λ(v,k). (db_esubst_ty σ v, db_esubst_ty σ k)) ilist)
               (dbVar x (ty_esubst σ ty))
Proof
  rw[] >> drule_all db_esubst_ty_REV_ASSOCD_comm_gen >> simp[SF SFY_ss, db_esubst_ty_def]
QED

Theorem db_esubst_ty_dbVSUBST_comm:
  ∀dbtm ilist.
    no_combined_collapse σ ilist dbtm ∧
    (∀s2 s. MEM (s2,s) ilist ⇒ ∃x ty. s = dbVar x ty) ⇒
    db_esubst_ty σ (dbVSUBST ilist dbtm) =
    dbVSUBST (MAP (λ(v,k). (db_esubst_ty σ v, db_esubst_ty σ k)) ilist)
             (db_esubst_ty σ dbtm)
Proof
  Induct_on ‘dbtm’ >> rw[db_esubst_ty_def]
  >- (irule db_esubst_ty_REV_ASSOCD_comm >> rw[]
      >> gvs[no_combined_collapse] >> metis_tac[])
  >- (first_x_assum irule >> rw[] >> metis_tac[no_combined_collapse_comb])
  >- (first_x_assum irule >> rw[] >> metis_tac[no_combined_collapse_comb])
  >> drule no_combined_collapse_abs >> strip_tac >> metis_tac[]
QED

Theorem db_esubst_tm_dbVSUBST_comm_aux:
  ∀ilist.
    (∀s2 s. MEM (s2,s) ilist ⇒ ∃x ty. s = dbVar x ty ∧ vtys_ok sig s2) ∧
    esubsts_ok sig σ ⇒
    db_esubst_tm σ (REV_ASSOCD (dbVar m t) ilist (dbVar m t)) =
    REV_ASSOCD (dbVar m t) (MAP (λ(v,k). (db_esubst_tm σ v,k)) ilist)
               (dbVar m t)
Proof
  Induct_on ‘ilist’ >> rw[REV_ASSOCD, db_esubst_tm_def]
  >> Cases_on ‘h’ >> gvs[DISJ_IMP_THM, REV_ASSOCD, AllCaseEqs()]
  >> rw[]
QED

Theorem db_esubst_tm_dbVSUBST_comm:
  ∀dbtm ilist.
    (∀s2 s. MEM (s2,s) ilist ⇒ ∃x ty. s = dbVar x ty ∧ vtys_ok sig s2) ∧
    esubsts_ok sig σ ⇒
    db_esubst_tm σ (dbVSUBST ilist dbtm) =
    dbVSUBST (MAP (λ(v,k). (db_esubst_tm σ v, k)) ilist)
             (db_esubst_tm σ dbtm)
Proof
  Induct_on ‘dbtm’ >> rw[db_esubst_tm_def, AllCaseEqs()]
  >- metis_tac[db_esubst_tm_dbVSUBST_comm_aux] >> case_tac
  >> Cases_on ‘σ’ >> gvs[esubsts_ok_def] >> gvs[TO_FLOOKUP]
  >> qsuff_tac ‘∃n typ. x = Const n typ’ >> rw[]
  >> metis_tac[dbVSUBST_def, db_def]
QED

Theorem vtys_ok_esubst_ty:
  ∀dbtm. esubsts_ok sig σ ∧ vtys_ok sig dbtm ⇒ vtys_ok sig (db_esubst_ty σ dbtm)
Proof
  Induct_on ‘dbtm’ >> rw[db_esubst_ty_def, vtys_ok_def]
  >> metis_tac[esubsts_ok_type_ok]
QED

Theorem db_esubst_dbVSUBST_comm:
  ∀dbtm ilist.
    esubsts_ok sig σ ∧
    no_combined_collapse σ ilist dbtm ∧
    (∀s2 s. MEM (s2,s) ilist ⇒ ∃x ty. s = dbVar x ty ∧ vtys_ok sig s2) ⇒
    db_esubst σ (dbVSUBST ilist dbtm) =
    dbVSUBST (MAP (λ(v,k). (db_esubst σ v, db_esubst_ty σ k)) ilist)
             (db_esubst σ dbtm)
Proof
  rw[db_esubst_def]
  >> drule db_esubst_ty_dbVSUBST_comm
  >> impl_tac
  >- metis_tac[]
  >> rw[]
  >> drule_at (Pos last) db_esubst_tm_dbVSUBST_comm
  >> disch_then $ qspecl_then
                [‘db_esubst_ty σ dbtm’,
                 ‘MAP (λ(v,k). (db_esubst_ty σ v, db_esubst_ty σ k)) ilist’] mp_tac
  >> impl_tac
  >- (rw[MEM_MAP] >> Cases_on ‘y’ >> gvs[] >> first_x_assum drule >> rw[]
      >> simp[db_esubst_ty_def, vtys_ok_esubst_ty])
  >> gvs[MAP_MAP_o, FORALL_PROD, o_DEF] >> rw[]
  >> cong_tac $ SOME 2 >> simp[]
QED

Theorem vtys_ok_bind:
  ∀n. vtys_ok sig dbtm ∧ type_ok (tysof sig) ty ⇒
      vtys_ok sig (bind (x,ty) n dbtm)
Proof
  Induct_on ‘dbtm’ >> rw[vtys_ok_def]
QED

Theorem term_ok_db_vtys_ok:
  term_ok sig tm ⇒ vtys_ok sig (db tm)
Proof
  Induct_on ‘tm’ >> rw[]
  >> gvs[db_def, vtys_ok_def, term_ok_def, typeof_def, vtys_ok_bind]
QED

Theorem esubst_INST_comm:
  ∀tm.
    theory_ok (sig, axs) ∧
    EVERY (type_ok (tysof sig)) (MAP FST tyin) ∧
    esubsts_ok sig σ ∧ term_ok sig tm ⇒
    ACONV (esubst σ avds1 (INST tyin tm))
          (INST (MAP (λ(ty, a). (ty_esubst σ ty, a)) tyin) (esubst σ avds2 tm))
Proof
  rpt strip_tac >> irule $ iffRL ACONV_db >> rpt conj_tac
  >- (irule esubst_welltyped >> ntac 2 $ first_x_assum $ irule_at (Pos hd)
      >> irule term_ok_INST >> simp[])
  >- (irule INST_WELLTYPED >> irule esubst_welltyped >> simp[] >> metis_tac[])
  >> qabbrev_tac ‘tyinσ = MAP (λ(ty,a). (ty_esubst σ ty,a)) tyin’
  >> qspecl_then [‘INST tyin tm’, ‘avds1’] mp_tac db_esubst_thm >> impl_tac
  >- metis_tac[term_ok_INST] >> rw[]
  >> qspecl_then [‘tm’, ‘tyin’] mp_tac INST_dbINST >> rw[term_ok_welltyped, SF SFY_ss]
  >> qspecl_then [‘esubst σ avds2 tm’, ‘tyinσ’] mp_tac INST_dbINST >> impl_tac
  >- (irule esubst_welltyped >> metis_tac[]) >> rw[]
  >> qspecl_then [‘tm’, ‘avds2’] mp_tac db_esubst_thm >> rw[Abbr‘tyinσ’]
  >> irule db_esubst_dbINST_comm >> metis_tac[term_ok_db_vtys_ok]
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

Triviality ilist_ok_REV_ASSOCD_var:
  (∀v k. MEM (v,k) ilist ⇒ ∃n m ty. v = Var n ty ∧ k = Var m ty) ⇒
  ∃m typ. REV_ASSOCD (Var x ty) ilist (Var x ty) = Var m typ
Proof
  rw[] >> qspecl_then [‘ilist’, ‘Var x ty’, ‘Var x ty’] mp_tac REV_ASSOCD_MEM
  >> rw[] >> metis_tac[]
QED

Theorem simple_esubst_Abs:
  term_ok sig (Abs (Var x ty) t) ∧
  theory_ok (sig,axs) ∧
  esubsts_ok sig σ ⇒
  ∃y body.
    esubst σ avds (Abs (Var x ty) t) =
    Abs (Var y (ty_esubst σ ty)) body ∧
    ACONV body (esubst σ avds (VSUBST [(Var y ty, Var x ty)] t)) ∧
    (x = y ∨ ¬MEM y avds) ∧
    term_ok (esubst_sig σ sig) body
Proof
  rw[esubst_def, esubst_tm_def, esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds (Abs (Var x ty) t) = return v’
    by metis_tac[esubst_ty0_always_returns, term_ok_def]
  >> ‘∃v. esubst_ty0 [] σ avds t = return v’
    by metis_tac[esubst_ty0_always_returns, term_ok_def]
  >> simp[]
  >> gvs[esubst_ty0_def, try_eq_return, bind_EQ_return, bind_EQ_error, AllCaseEqs()]
  >> conj_tac
  >- (irule esubst_tm_ACONV >> drule_all_then strip_assume_tac esubsts_ok_esubst_sig
      >> first_assum $ irule_at Any >> rpt CASE_TAC
      >> gvs[VSUBST_ID, MEM, SF SFY_ss]
      >> ‘term_ok (esubst_sig σ sig) a’
        by (irule esubst_ty0_term_ok >> simp[] >> rpt $ first_x_assum $ irule_at (Pos last)
            >> simp[])
      >> ‘term_ok (esubst_sig σ sig) body'’
        by (irule esubst_ty0_term_ok >> simp[] >> rpt $ first_x_assum $ irule_at (Pos last)
            >> simp[])
      >> simp[] >> irule esubst_ty0_env_aconv >> simp[SF SFY_ss, term_ok_welltyped]
      >> rpt $ last_x_assum $ irule_at (Pos last) >> simp[])
  >- (irule esubst_tm_preserves_term_ok >> simp[SF SFY_ss]
      >> rpt $ dxrule esubst_ty0_term_ok >> simp[SF SFY_ss])
  >- (irule esubst_tm_ACONV >> drule_all_then strip_assume_tac esubsts_ok_esubst_sig
      >> first_assum $ irule_at Any >> rpt CASE_TAC
      >> gvs[VSUBST_ID, MEM, SF SFY_ss]
      >- (‘term_ok (esubst_sig σ sig) a’
            by (irule esubst_ty0_term_ok >> simp[]
                >> rpt $ first_x_assum $ irule_at (Pos (hd o tl)) >> simp[]
                >> metis_tac[term_ok_vsubst_variant])
          >> ‘term_ok (esubst_sig σ sig) body''’
            by (irule esubst_ty0_term_ok >> simp[]
                >> rpt $ first_x_assum $ irule_at (Pos (hd o tl)) >> simp[]
                >> metis_tac[term_ok_vsubst_variant])
          >> simp[] >> irule esubst_ty0_env_aconv >> simp[SF SFY_ss, term_ok_welltyped]
          >> rpt $ last_x_assum $ irule_at (Pos (fn lst => el (length lst - 1) lst))
          >> simp[] >> metis_tac[term_ok_vsubst_variant])
      >> pop_assum mp_tac >> contrapos_tac >> qid_spec_tac ‘e’ >> simp[neq_error, SF SFY_ss]
      >> irule esubst_ty0_always_returns >> metis_tac[term_ok_vsubst_variant])
  >> simp[NVARIANT_AVDS_THM]
  >> irule esubst_tm_preserves_term_ok >> simp[SF SFY_ss]
  >> rpt $ dxrule esubst_ty0_term_ok >> simp[SF SFY_ss]
  >> rpt (disch_then $ drule_at Any >> strip_tac) >> gvs[term_ok_vsubst_variant]
QED

Theorem ACONV_esubst_env:
  esubsts_ok sig σ ∧ term_ok sig tm ∧ theory_ok (sig, axs) ⇒
  ACONV (esubst σ avds1 tm) (esubst σ avds2 tm)
Proof
  rw[esubst_def] >> irule esubst_tm_ACONV >> conj_tac
  >- (irule esubst_ty_avds_aconv >> imp_res_tac term_ok_welltyped >> simp[SF SFY_ss])
  >> drule_all esubsts_ok_esubst_sig >> rw[SF SFY_ss]
  >> metis_tac[esubst_ty_term_ok]
QED

Theorem proves_ACONV_concl:
  ∀thy h n c c'.
    (thy,h) |- c ∧ welltyped c' ∧ ACONV c c' ⇒ (thy,h) |- c'
Proof
  rw[] >> irule proves_ACONV >> rw[]
  >> drule proves_term_ok >> rw[EVERY_MEM]
  >> first_x_assum $ irule_at (Pos hd) >> rw[EXISTS_MEM]
  >> first_x_assum $ irule_at (Pos last) >> rw[]
  >> first_x_assum $ irule_at (Pos hd) >> simp[]
QED

Theorem ACONV_esubst_avds:
  ∀tm.
    term_ok sig tm ∧ welltyped tm ∧ esubsts_ok sig σ ∧ theory_ok (sig, axs) ⇒
    ACONV (esubst σ avds1 tm) (esubst σ avds2 tm)
Proof
  rw[esubst_def] >> irule esubst_tm_ACONV >> simp[SF SFY_ss, esubst_ty_avds_aconv]
  >> drule_all esubsts_ok_esubst_sig >> rw[SF SFY_ss] >> first_x_assum $ irule_at (Pos hd)
  >> conj_tac >> irule esubst_ty_term_ok >> simp[]
QED

Theorem esubst_avds_type:
  ∀tm. theory_ok (sig,axs) ∧ term_ok sig tm ∧ esubsts_ok sig σ ⇒
       typeof (esubst σ avds1 tm) = typeof (esubst σ avds2 tm)
Proof
  rpt strip_tac >> irule ACONV_TYPE >> simp[esubst_welltyped, term_ok_welltyped, SF SFY_ss]
  >> irule ACONV_esubst_avds >> simp[term_ok_welltyped, SF SFY_ss]
QED

Theorem esubst_VSUBST_has_type:
  term_ok sig c ∧
  c has_type Bool ∧
  theory_ok (sig, axs) ∧
  esubsts_ok sig σ ∧
  (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s') ⇒
  esubst σ avds (VSUBST ilist c) has_type Bool
Proof
  rpt strip_tac >> irule esubst_has_type_bool >> conj_tac
  >- (irule VSUBST_HAS_TYPE >> metis_tac[])
  >> rpt $ first_assum $ irule_at Any >> irule term_ok_VSUBST >> metis_tac[]
QED

Theorem esubst_VSUBST_term_ok:
  term_ok sig c ∧
  theory_ok (sig, axs) ∧
  esubsts_ok sig σ ∧
  (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s') ⇒
  term_ok (esubst_sig σ sig) (esubst σ avds (VSUBST ilist c))
Proof
  rpt strip_tac >> irule esubst_term_ok >> rw[SF SFY_ss]
  >> irule term_ok_VSUBST >> metis_tac[]
QED

Theorem esubst_VSUBST_welltyped:
  term_ok sig c ∧ theory_ok (sig, axs) ∧ esubsts_ok sig σ ∧
  (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s') ⇒
  welltyped (esubst σ avds (VSUBST ilist c))
Proof
  rpt strip_tac >> irule term_ok_welltyped >> drule_all esubst_VSUBST_term_ok
  >> simp[SF SFY_ss]
QED

Theorem typeof_esubst:
  term_ok sig tm ∧ esubsts_ok sig σ ∧ theory_ok (sig, axs) ⇒
  typeof (esubst σ avds tm) = ty_esubst σ (typeof tm)
Proof
  rw[esubst_def, esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ avds tm = return v’ by metis_tac[esubst_ty0_always_returns]
  >> Cases_on ‘σ’ >> simp[] >> drule_at (Pos last) typeof_esubst_ty >> simp[]
  >> disch_then drule_all >> rw[] >> pop_assum $ SUBST1_TAC o GSYM
  >> irule typeof_esubst_tm >> rpt $ first_assum $ irule_at Any
  >> drule esubst_ty0_term_ok >> simp[]
QED

Theorem theory_ok_esubst_VSUBST[simp]:
  theory_ok (sig,axs) ∧ esubsts_ok sig σ ∧
  (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s') ⇒
  theory_ok (esubst_sig σ sig,IMAGE (esubst σ [] ∘ VSUBST ilist) axs)
Proof
  rpt strip_tac >> drule $ iffLR theory_ok_def >> rw[] >> rw[theory_ok_def]
  >- (dxrule in_frange_o_f >> rw[] >> irule ty_esubst_type_ok_alt >> simp[])
  >- (irule esubst_VSUBST_term_ok >> metis_tac[])
  >- (irule esubst_VSUBST_has_type >> metis_tac[])
  >> metis_tac[esubst_sig_is_std_sig]
QED

Theorem esubst_VSUBST_ACONV:
  (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s') ∧
  ACONV tm1 tm2 ∧ term_ok sig tm1 ∧ term_ok sig tm2 ∧
  theory_ok (sig,axs) ∧ esubsts_ok sig σ ⇒
  ACONV (esubst σ avds1 (VSUBST ilist tm1)) (esubst σ avds2 (VSUBST ilist tm2))
Proof
  rw[] >> irule esubst_ACONV >> rw[SF SFY_ss]
  >- (irule ACONV_VSUBST >> rw[term_ok_welltyped, SF SFY_ss] >> first_x_assum drule
      >> rw[])
  >> rpt $ first_assum $ irule_at Any >> conj_tac >> irule term_ok_VSUBST
  >> rw[] >> first_x_assum drule >> rw[]
QED

Theorem term_image_thm:
  (term_image f [] = []) ∧
  term_image f (h::t) =
  if f h = h ∧ term_image f t = t then h::t
  else term_union [f h] (term_image f t)
Proof
  rw[] >> simp[Once term_image_def, SimpLHS]
QED

Theorem nproves_hypset_ok:
  (thy,h,n) |n- tm ⇒ hypset_ok h
Proof
  rw[] >> dxrule nproves_term_ok1 >> rw[]
QED

Theorem db_esubst_ty_thm1:
  ∀tm avds.
    esubsts_ok sig σ ∧ term_ok sig tm ⇒
    db (esubst_ty σ avds tm) = db_esubst_ty σ (db tm)
Proof
  rw[] >> qspecl_then [‘tm’, ‘[]’] mp_tac db_esubst_ty_thm
  >> simp[term_ok_welltyped, SF SFY_ss] >> drule_all esubst_ty0_always_returns
  >> disch_then $ qspec_then ‘avds’ mp_tac >> strip_tac
  >> disch_then drule >> rw[esubst_ty_def]
QED

Theorem term_ok_has_type_type_ok:
  ∀tm. theory_ok (sig,axs) ∧ term_ok sig tm ∧ tm has_type ty ⇒
       type_ok (tysof sig) ty
Proof
  Induct_on ‘$has_type’
  >> rw[term_ok_def, type_ok_def, theory_ok_def, is_std_sig_def]
QED

Theorem esubst_VSUBST_comm:
  ∀tm.
    theory_ok (sig, axs) ∧ esubsts_ok sig σ ∧ term_ok sig tm ∧
    no_var_collapse σ tm ∧
    (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧
                                      term_ok sig s' ∧ VFREE_IN s tm) ⇒
    ACONV (VSUBST (MAP (λ(s',s). (esubst σ [] s', esubst_ty σ [] s)) ilist) (esubst σ avds tm))
          (esubst σ avds' (VSUBST ilist tm))
Proof
  rw[] >> irule $ iffRL ACONV_db >> rw[]
  >- (irule VSUBST_WELLTYPED >> rw[MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
      >- (first_x_assum drule >> rw[] >> rw[] >> irule esubst_has_type1
          >> metis_tac[])
      >> irule esubst_welltyped >> simp[SF SFY_ss])
  >- metis_tac[esubst_VSUBST_welltyped]
  >> qpat_abbrev_tac ‘ilist1 = MAP _ ilist’
  >> qspecl_then [‘esubst σ avds tm’, ‘ilist1’] mp_tac VSUBST_dbVSUBST
  >> impl_tac
  >- (conj_tac >- metis_tac[esubst_welltyped]
      >> rw[Abbr‘ilist1’, MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
      >- metis_tac[esubst_welltyped]
      >> first_x_assum drule >> rw[] >> rw[] >> irule esubst_has_type1
      >> metis_tac[])
  >> rw[Abbr‘ilist1’] >> gvs[MAP_MAP_o]
  >> ‘MAP ((λ(x,y). (db x,db y)) ∘ (λ(s',s). (esubst σ [] s',esubst_ty σ [] s))) ilist =
      MAP (λ(s',s). (db_esubst σ (db s'), db_esubst_ty σ (db s))) ilist’
    by (simp[UNCURRY, MAP_MAP_o, o_DEF, LAMBDA_PROD]
        >> irule MAP_CONG >> rw[] >> rename1 ‘MEM x ilist’
        >> Cases_on ‘x’ >> rw[]
        >- metis_tac[db_esubst_thm]
        >> irule db_esubst_ty_thm1 >> first_x_assum drule >> rw[]
        >> first_x_assum $ irule_at Any >> simp[term_ok_def]
        >> irule term_ok_has_type_type_ok >> metis_tac[])
  >> first_x_assum SUBST1_TAC
  >> ‘db (esubst σ avds tm) = db_esubst σ (db tm)’ by metis_tac[db_esubst_thm]
  >> first_x_assum SUBST1_TAC
  >> ‘db (esubst σ avds' (VSUBST ilist tm)) =
      db_esubst σ (dbVSUBST (MAP (λ(x,y). (db x,db y)) ilist) (db tm))’
    by (qsuff_tac ‘dbVSUBST (MAP (λ(x,y). (db x,db y)) ilist) (db tm) = db (VSUBST ilist tm)’
        >> rw[] >- metis_tac[db_esubst_thm, term_ok_VSUBST]
        >> sym_tac >> irule VSUBST_dbVSUBST >> simp[term_ok_welltyped, SF SFY_ss]
        >> rw[] >> first_x_assum drule >> metis_tac[term_ok_welltyped])
  >> first_x_assum SUBST1_TAC
  >> qpat_abbrev_tac ‘ilistdb = MAP (λ(x,y). (db x, db y)) ilist’
  >> qspecl_then [‘db tm’, ‘ilistdb’] mp_tac db_esubst_dbVSUBST_comm
  >> impl_tac
  >- (simp[SF SFY_ss, MEM_MAP, Abbr‘ilistdb’] >> conj_tac
      >- (irule no_dbvar_collapse_no_combined_collapse >> rw[]
          >> gvs[MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
          >> metis_tac[db_def, dbVFREE_IN_VFREE_IN, term_ok_welltyped,
                       no_var_collapse_no_dbvar_collapse])
      >> rw[LAMBDA_PROD, EXISTS_PROD] >> first_x_assum drule
      >> rw[] >> rw[db_def, term_ok_db_vtys_ok])
  >> rw[Abbr‘ilistdb’, MAP_MAP_o] >> cong_tac $ SOME 1
  >> qid_spec_tac ‘ilist’ >> Induct >> simp[UNCURRY]
QED



Theorem VSUBST_FILTER_VFREE:
  ∀tm ilist.
    term_ok sig tm ⇒
    VSUBST ilist tm = VSUBST (FILTER (λ(s',s). VFREE_IN s tm) ilist) tm
Proof
  Induct_on ‘tm’ >> rw[]
  >~ [‘Abs v body’]
  >- (‘∀P Q (l:(term#term)list). EXISTS P (FILTER Q l) = EXISTS (λx. P x ∧ Q x) l’
        by (gen_tac >> gen_tac >> Induct_on ‘l’ >> rw [] >> metis_tac[])
      >> qabbrev_tac ‘il1 = FILTER (λ(s',s). s ≠ v) ilist’
      >> qabbrev_tac ‘il2 = FILTER (λ(s',s). s ≠ v ∧ VFREE_IN s body) ilist’
      >> ‘FILTER (λ(s',s). s ≠ v) (FILTER (λ(s',s). v ≠ s ∧ VFREE_IN s body) ilist) = il2’
        by simp [Abbr‘il2’, FILTER_FILTER, LAMBDA_PROD, SF CONJ_ss]
      >> ‘VSUBST il1 body = VSUBST il2 body’
        by (qpat_assum ‘∀ilist. term_ok sig body ⇒ _’ mp_tac
            >> disch_then $ qspec_then ‘il1’ mp_tac
            >> qpat_x_assum ‘∀ilist. term_ok sig body ⇒ _’ mp_tac
            >> disch_then $ qspec_then ‘il2’ mp_tac >> simp[]
            >> gvs [Abbr‘il1’, Abbr‘il2’, FILTER_FILTER, LAMBDA_PROD, SF CONJ_ss])
      >> ‘EXISTS (λ(s',s). VFREE_IN v s' ∧ VFREE_IN s body) il1
          = EXISTS (λ(s',s). VFREE_IN v s' ∧ VFREE_IN s body) il2’
        by (simp [Abbr‘il1’, Abbr‘il2’, LAMBDA_PROD, SF CONJ_ss]
            >> metis_tac [])
      >> ‘∀z. VSUBST ((z,v)::il1) body = VSUBST ((z,v)::il2) body’
        by (gen_tac >> qpat_assum ‘∀ilist. term_ok sig body ⇒ _’ $ qspec_then ‘(z,v)::il1’ mp_tac
            >> disch_then drule
            >> qpat_x_assum ‘∀ilist. term_ok sig body ⇒ _’ $ qspec_then ‘(z,v)::il2’ mp_tac
            >> disch_then drule >> ntac 2 strip_tac
            >> ‘FILTER (λ(s',s). VFREE_IN s body) ((z,v)::il1) =
                FILTER (λ(s',s). VFREE_IN s body) ((z,v)::il2)’
              by simp [Abbr‘il1’, Abbr‘il2’, SF CONJ_ss, FILTER_FILTER, LAMBDA_PROD]
            >> metis_tac[])
      >> ‘FILTER (λ(s',s). v ≠ s ∧ VFREE_IN s body) ilist = il2’
        by (simp[Abbr‘il2’] >> cong_tac $ SOME 1 >> simp[SF ETA_ss] >> metis_tac[])
      >> first_x_assum SUBST_ALL_TAC >> first_x_assum drule >> rw[]
      >> last_x_assum kall_tac >> REWRITE_TAC[VSUBST_thm] >> LET_ELIM_TAC
      >> qsuff_tac ‘ilist' = il2’
      >- (disch_then SUBST_ALL_TAC >> ‘ilist'' = il1’ by metis_tac[] >> first_x_assum SUBST_ALL_TAC
          >> qsuff_tac ‘z = z'’ >- metis_tac[]
          >> simp[Abbr‘z’, Abbr‘z'’, variant_vsubst_thm] >> qpat_x_assum ‘(x,ty') = (x',ty'')’ mp_tac
          >> simp[])
      >> simp[Abbr‘ilist'’, Abbr‘il2’])
  >> REWRITE_TAC[VSUBST_def, REV_ASSOCD_FILTER, LET_THM]
  >> cong_tac $ SOME 1
  >- (‘VSUBST (FILTER (λ(s',s). VFREE_IN s tm ∨ VFREE_IN s tm') ilist) tm
       = VSUBST (FILTER (λ(s',s). VFREE_IN s tm) ilist) tm’
        by (rpt $ first_x_assum $ qspec_then ‘FILTER (λ(s',s). VFREE_IN s tm ∨ VFREE_IN s tm') ilist’ mp_tac
            >> rpt (disch_then drule >> strip_tac) >> gvs[FILTER_FILTER, LAMBDA_PROD, SF CONJ_ss]
            >> metis_tac[])
      >> metis_tac[])
  >> ‘VSUBST (FILTER (λ(s',s). VFREE_IN s tm ∨ VFREE_IN s tm') ilist) tm'
      = VSUBST (FILTER (λ(s',s). VFREE_IN s tm') ilist) tm'’
    by (rpt $ first_x_assum $ qspec_then ‘FILTER (λ(s',s). VFREE_IN s tm ∨ VFREE_IN s tm') ilist’ mp_tac
        >> rpt (disch_then drule >> strip_tac) >> gvs[FILTER_FILTER, LAMBDA_PROD, SF CONJ_ss])
  >> metis_tac[]
QED

Theorem REV_ASSOCD_APPEND:
  ∀l1 l2 k d.
    REV_ASSOCD k (l1 ++ l2) d = REV_ASSOCD k l1 (REV_ASSOCD k l2 d)
Proof
  Induct_on ‘l1’ >> simp[FORALL_PROD, REV_ASSOCD_def]
QED

Theorem dbVSUBST_comp:
  ∀t l1 l2.
    dbVSUBST l2 (dbVSUBST l1 t) =
    dbVSUBST (MAP (λ(v,k). (dbVSUBST l2 v, k)) l1 ++
               FILTER (λ(v,k). ¬MEM k (MAP SND l1)) l2) t
Proof
  Induct >> simp[dbVSUBST_def, REV_ASSOCD_APPEND, REV_ASSOCD_MAP,
                 REV_ASSOCD_FILTER, MEM_MAP, EXISTS_PROD, FORALL_PROD]
  >> rw[] >> simp[dbVSUBST_def]
  >> qspecl_then [‘l1’, ‘dbVar m t’, ‘dbVar m t’] mp_tac REV_ASSOCD_MEM
  >> rw[] >> gvs[]
QED

Theorem VSUBST_VSUBST_ACONV:
  ∀tm.
    term_ok sig tm ∧
    (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s') ∧
    (∀s s'. MEM (s',s) ilist' ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s') ⇒
    ACONV (VSUBST (MAP (λ(s',s). (VSUBST ilist' s', s)) ilist ++
                   FILTER (λ(s',s). ¬MEM s (MAP SND ilist)) ilist') tm)
          (VSUBST ilist' (VSUBST ilist tm))
Proof
  rpt strip_tac
  >> imp_res_tac term_ok_welltyped
  >> ‘∀v k. MEM (v,k) ilist ⇒ welltyped v ∧ ∃x ty. k = Var x ty’ by
       (rw[] >> metis_tac[term_ok_welltyped])
  >> ‘∀v k. MEM (v,k) ilist' ⇒ welltyped v ∧ ∃x ty. k = Var x ty’ by
       (rw[] >> metis_tac[term_ok_welltyped])
  >> ‘∀v k. MEM (v,k) (MAP (λ(s',s). (VSUBST ilist' s', s)) ilist ++
                       FILTER (λ(s',s). ¬MEM s (MAP SND ilist)) ilist') ⇒
            welltyped v ∧ ∃x ty. k = Var x ty’ by
       (rw[MEM_APPEND, MEM_MAP, MEM_FILTER, FORALL_PROD, EXISTS_PROD, PULL_EXISTS]
        >> first_x_assum drule >> rw[] >> metis_tac[VSUBST_WELLTYPED])
  >> irule $ iffRL ACONV_db >> rw[]
  >- (irule VSUBST_WELLTYPED >> rw[]
      >> gvs[MEM_MAP, FORALL_PROD, LAMBDA_PROD, EXISTS_PROD, MEM_FILTER]
      >> metis_tac[VSUBST_HAS_TYPE])
  >- metis_tac[VSUBST_WELLTYPED]
  >> ‘db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm)’ by
       rw[VSUBST_dbVSUBST, SF SFY_ss]
  >> ‘db (VSUBST ilist' (VSUBST ilist tm)) =
      dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist')
               (dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm))’ by
       metis_tac[VSUBST_dbVSUBST, VSUBST_WELLTYPED]
  >> ‘db (VSUBST (MAP (λ(s',s). (VSUBST ilist' s', s)) ilist ++
                  FILTER (λ(s',s). ¬MEM s (MAP SND ilist)) ilist') tm) =
      dbVSUBST (MAP (λ(x,y). (db x, db y)) (MAP (λ(s',s). (VSUBST ilist' s', s)) ilist ++
                                              FILTER (λ(s',s). ¬MEM s (MAP SND ilist)) ilist')) (db tm)’ by
       rw[VSUBST_dbVSUBST, SF SFY_ss]
  >> gvs[]
  >> rw[Once dbVSUBST_comp]
  >> cong_tac $ SOME 1
  >> ‘MAP (λ(x,y). (db x,db y)) (MAP (λ(s',s). (VSUBST ilist' s',s)) ilist) =
      MAP (λ(v,k). (dbVSUBST (MAP (λ(x,y). (db x,db y)) ilist') v,k))
          (MAP (λ(x,y). (db x,db y)) ilist)’ by
    (rw[MAP_MAP_o, o_DEF, LAMBDA_PROD] >> irule MAP_CONG >> rw[LAMBDA_PROD, FORALL_PROD, EXISTS_PROD]
                   >> Cases_on ‘x’ >> rw[] >> irule VSUBST_dbVSUBST >> metis_tac[])
  >> ‘MAP (λ(x,y). (db x,db y)) (FILTER (λ(s',s). ¬MEM s (MAP SND ilist)) ilist') =
      FILTER (λ(v,k). ¬MEM k (MAP SND (MAP (λ(x,y). (db x,db y)) ilist)))
             (MAP (λ(x,y). (db x,db y)) ilist')’ by
    (rw[FILTER_MAP] >> cong_tac $ SOME 1 >> rw[LAMBDA_PROD, o_DEF, SF ETA_ss]
     >> qid_spec_tac ‘ilist'’ >> Induct >> rw[] >> Cases_on ‘h’ >> gvs[MEM_MAP]
     >- (Cases_on ‘y'’ >> gvs[] >> last_assum drule >> strip_tac >> qpat_x_assum ‘MEM _ _’ mp_tac >> simp[]
         >> gvs[] >> first_x_assum irule >> gvs[] >> qpat_x_assum ‘db _ = dbVar _ _’ mp_tac
         >> qid_spec_tac ‘r’ >> Induct_on ‘r’ >> rw[db_def])
     >> Cases_on ‘y’ >> gvs[] >> last_assum drule >> strip_tac >> qpat_x_assum ‘MEM _ _’ mp_tac >> simp[]
     >> gvs[] >> first_x_assum irule >> gvs[] >> qpat_x_assum ‘db _ = dbVar _ _’ mp_tac
     >> qid_spec_tac ‘r’ >> Induct_on ‘r’ >> rw[db_def])
  >> rw[]
QED

(* Substitution steps: a list of VSUBST and INST_TYPE operations to apply *)
Datatype:
  subst_step = VStep ((term # term) list) | TStep ((type # type) list)
End

Definition apply_steps_def:
  apply_steps [] c = c ∧
  apply_steps (VStep ilist :: rest) c = VSUBST ilist (apply_steps rest c) ∧
  apply_steps (TStep tyin :: rest) c = INST tyin (apply_steps rest c)
End

Definition steps_ok_def:
  steps_ok sig [] = T ∧
  steps_ok sig (VStep ilist :: rest) =
    ((∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s') ∧
     steps_ok sig rest) ∧
  steps_ok sig (TStep tyin :: rest) =
    (EVERY (type_ok (FST sig)) (MAP FST tyin) ∧ steps_ok sig rest)
End

Theorem apply_steps_append:
  ∀s1 s2 c. apply_steps (s1 ++ s2) c = apply_steps s1 (apply_steps s2 c)
Proof
  Induct >> rw[apply_steps_def] >> Cases_on ‘h’ >> rw[apply_steps_def]
QED

Theorem steps_ok_append:
  ∀s1 s2 sig. steps_ok sig (s1 ++ s2) ⇔ steps_ok sig s1 ∧ steps_ok sig s2
Proof
  Induct >> rw[steps_ok_def] >> Cases_on ‘h’ >> rw[steps_ok_def] >> metis_tac[]
QED

Theorem apply_steps_welltyped:
  ∀steps c sig.
    welltyped c ∧ steps_ok sig steps ⇒
    welltyped (apply_steps steps c)
Proof
  recInduct apply_steps_ind >> rw[apply_steps_def]
  >- (irule VSUBST_WELLTYPED >> metis_tac[steps_ok_def])
  >> irule INST_WELLTYPED >> metis_tac[steps_ok_def]
QED

Theorem apply_steps_term_ok:
  ∀steps c sig.
    term_ok sig c ∧ steps_ok sig steps ⇒
    term_ok sig (apply_steps steps c)
Proof
  recInduct apply_steps_ind >> rw[apply_steps_def]
  >> metis_tac[steps_ok_def, term_ok_INST, term_ok_VSUBST]
QED

Theorem apply_steps_has_type_Bool:
  ∀steps c sig.
    c has_type Bool ∧ steps_ok sig steps ⇒
    apply_steps steps c has_type Bool
Proof
  recInduct apply_steps_ind >> rw[apply_steps_def, steps_ok_def]
  >- (irule VSUBST_HAS_TYPE >> rw[] >> metis_tac[])
  >> irule INST_HAS_TYPE >> metis_tac[TYPE_SUBST_Bool]
QED

Definition unique_varnames_def:
  unique_varnames tm ⇔
    ∀x ty1 ty2. VFREE_IN (Var x ty1) tm ∧ VFREE_IN (Var x ty2) tm ⇒ ty1 = ty2
End

Theorem unique_varnames_no_var_collapse:
  unique_varnames tm ⇒ no_var_collapse σ tm
Proof
  rw[unique_varnames_def, no_var_collapse] >> metis_tac[]
QED

Theorem unique_varnames_INST:
  ∀tm tyin. welltyped tm ∧ unique_varnames tm ⇒ unique_varnames (INST tyin tm)
Proof
  rw[INST_def] >> imp_res_tac INST_CORE_NIL_IS_RESULT
  >> ‘∃subst_tm. INST_CORE [] tyin tm = Result subst_tm’ by simp[IS_RESULT_IMP_Result]
  >> drule INST_CORE_HAS_TYPE >> disch_then $ qspec_then ‘sizeof tm’ mp_tac
  >> disch_then $ qspecl_then [‘[]’, ‘tyin’] mp_tac >> rw[unique_varnames_def]
  >> metis_tac[unique_varnames_def]
QED

Theorem unique_varnames_abs:
  ∀body.
    welltyped body ∧
    unique_varnames (Abs (Var x ty) body) ∧ ¬MEM z (tm_names body) ⇒
    unique_varnames (VSUBST [(Var z ty, Var x ty)] body)
Proof
  rpt strip_tac >> REWRITE_TAC[unique_varnames_def]
  >> rpt gen_tac >> strip_tac
  >> ntac 2 (pop_assum mp_tac)
  >> simp[VFREE_IN_VSUBST, REV_ASSOCD_def, COND_RAND, VFREE_IN_def]
  >> rpt strip_tac
  >> Cases_on ‘x = y ∧ ty = ty'’ >> Cases_on ‘x = y' ∧ ty = ty''’
  >> gvs[]
  >> TRY (imp_res_tac VFREE_IN_tm_names >> gvs[] >> NO_TAC)
  >> ‘VFREE_IN (Var x' ty') (Abs (Var x ty) body)’ by simp[VFREE_IN_def]
  >> ‘VFREE_IN (Var x' ty'') (Abs (Var x ty) body)’ by simp[VFREE_IN_def]
  >> metis_tac[unique_varnames_def]
QED

Definition pick_names_def:
  pick_names c avds [] = [] ∧
  pick_names c avds ((x,ty)::rest) =
    let n = NVARIANT x avds c in
    (Var n ty, Var x ty) :: pick_names c (n :: avds) rest
End

Theorem pick_names_form:
  ∀vars c avds s' s.
    MEM (s',s) (pick_names c avds vars) ⇒
    ∃x ty n. s = Var x ty ∧ s' = Var n ty ∧ MEM (x,ty) vars
Proof
  Induct >> rw[pick_names_def] >> Cases_on ‘h’ >> gvs[pick_names_def, LET_THM]
  >> metis_tac[]
QED

Theorem pick_names_fresh:
  ∀vars c avds n ty x ty'.
    MEM (Var n ty, Var x ty') (pick_names c avds vars) ⇒
    ¬MEM n (tm_names c) ∧ ty = ty'
Proof
  Induct >> simp[pick_names_def]
  >> rpt gen_tac >> Cases_on ‘h’ >> simp[pick_names_def, LET_THM]
  >> strip_tac >> gvs[] >> metis_tac[NVARIANT_NAMES_THM]
QED

Theorem pick_names_targets_not_in_avds:
  ∀vars c avds n ty s.
    MEM (Var n ty, s) (pick_names c avds vars) ⇒ ¬MEM n avds
Proof
  Induct >> simp[pick_names_def]
  >> rpt gen_tac >> Cases_on ‘h’ >> simp[pick_names_def, LET_THM]
  >> strip_tac >> gvs[]
  >- metis_tac[NVARIANT_MEM, MEM_APPEND]
  >> first_x_assum drule >> simp[MEM]
QED

Theorem pick_names_targets_inj:
  ∀vars c avds n ty1 s1 ty2 s2.
    MEM (Var n ty1, s1) (pick_names c avds vars) ∧
    MEM (Var n ty2, s2) (pick_names c avds vars) ⇒
    ty1 = ty2 ∧ s1 = s2
Proof
  Induct >> simp[pick_names_def]
  >> rpt gen_tac >> Cases_on ‘h’ >> simp[pick_names_def, LET_THM]
  >> strip_tac >> gvs[]
  >> metis_tac[pick_names_targets_not_in_avds, MEM]
QED

Theorem pick_names_sources_inj:
  ∀vars c avds.
    ALL_DISTINCT vars ⇒
    ∀t1 t2 x ty.
      MEM (t1, Var x ty) (pick_names c avds vars) ∧
      MEM (t2, Var x ty) (pick_names c avds vars) ⇒
      t1 = t2
Proof
  Induct >> rw[pick_names_def, MEM] >> Cases_on ‘h’ >> gvs[pick_names_def]
  >> drule pick_names_form >> gvs[] >> metis_tac[]
QED

Theorem pick_names_sources:
  ∀vars c avds x ty.
    MEM (x,ty) vars ⇒ ∃n. MEM (Var n ty, Var x ty) (pick_names c avds vars)
Proof
  Induct >> simp[pick_names_def]
  >> rpt gen_tac >> Cases_on ‘h’ >> simp[pick_names_def, LET_THM]
  >> strip_tac >> gvs[]
  >- (qexists ‘NVARIANT q avds c’ >> simp[])
  >> first_x_assum drule >> rw[] >> metis_tac[]
QED

Theorem pick_names_REV_ASSOCD:
  ∀vars c avds y ty d.
    MEM (y, ty) vars ⇒
    ∃n. REV_ASSOCD (Var y ty) (pick_names c avds vars) d = Var n ty ∧
        MEM (Var n ty, Var y ty) (pick_names c avds vars)
Proof
  Induct >> simp[pick_names_def]
  >> rpt gen_tac >> Cases_on ‘h’ >> simp[pick_names_def, LET_THM]
  >> strip_tac >> gvs[REV_ASSOCD_def]
  >> Cases_on ‘Var q r = Var y ty’ >> gvs[]
  >> first_x_assum drule >> rw[] >> metis_tac[]
QED

Theorem rename_to_unique_varnames:
  ∀c.
    term_ok sig c ⇒
    ∃ilist_r.
      unique_varnames (VSUBST ilist_r c) ∧
      (∀t s. MEM (t,s) ilist_r ⇒ ∃x ty y. s = Var x ty ∧ t = Var y ty ∧
                                            term_ok sig t ∧ VFREE_IN s c) ∧
      (∀nm ty1 v1 ty2 v2. MEM (Var nm ty1,v1) ilist_r ∧ MEM (Var nm ty2,v2) ilist_r ⇒
                          ty1 = ty2 ∧ v1 = v2) ∧
      (∀nm ty0 v. MEM (Var nm ty0,v) ilist_r ⇒ ¬VFREE_IN (Var nm ty0) c) ∧
      (∀t1 t2 s. MEM (t1, s) ilist_r ∧ MEM (t2, s) ilist_r ⇒ t1 = t2)
Proof
  rw[] >> imp_res_tac term_ok_welltyped
  >> qabbrev_tac ‘fv_set = {(x,ty) | VFREE_IN (Var x ty) c}’
  >> ‘FINITE fv_set’ by simp[Abbr‘fv_set’, FINITE_VFREE_IN_2]
  >> qabbrev_tac ‘vars = SET_TO_LIST fv_set’
  >> ‘set vars = fv_set’ by simp[Abbr‘vars’, SET_TO_LIST_INV]
  >> ‘ALL_DISTINCT vars’ by simp[Abbr‘vars’, ALL_DISTINCT_SET_TO_LIST]
  >> ‘∀y t. VFREE_IN (Var y t) c ⇒ MEM (y,t) vars’
    by (rpt strip_tac >> ‘(y,t) ∈ fv_set’ by simp[Abbr‘fv_set’] >> gvs[])
  >> qexists ‘pick_names c [] vars’ >> rw[]
  >- (rw[unique_varnames_def] >> rpt strip_tac
      >> ‘∃y1 t1. VFREE_IN (Var y1 t1) c ∧
                  VFREE_IN (Var x ty1)
                           (REV_ASSOCD (Var y1 t1) (pick_names c [] vars) (Var y1 t1))’
        by metis_tac[VFREE_IN_VSUBST]
      >> ‘∃y2 t2. VFREE_IN (Var y2 t2) c ∧
                  VFREE_IN (Var x ty2)
                           (REV_ASSOCD (Var y2 t2) (pick_names c [] vars) (Var y2 t2))’
        by metis_tac[VFREE_IN_VSUBST]
      >> ‘MEM (y1,t1) vars’ by metis_tac[]
      >> ‘MEM (y2,t2) vars’ by metis_tac[]
      >> ‘∃n1. REV_ASSOCD (Var y1 t1) (pick_names c [] vars) (Var y1 t1) = Var n1 t1 ∧
               MEM (Var n1 t1, Var y1 t1) (pick_names c [] vars)’
        by metis_tac[pick_names_REV_ASSOCD]
      >> ‘∃n2. REV_ASSOCD (Var y2 t2) (pick_names c [] vars) (Var y2 t2) = Var n2 t2 ∧
               MEM (Var n2 t2, Var y2 t2) (pick_names c [] vars)’
        by metis_tac[pick_names_REV_ASSOCD]
      >> gvs[VFREE_IN_def]
      >> metis_tac[pick_names_targets_inj])
  >- (rw[] >> drule pick_names_form >> strip_tac >> gvs[]
      >> gvs[EXTENSION] >> first_x_assum $ drule o iffRL >> rw[]
      >> unabbrev_all_tac >> drule_all term_ok_VFREE_IN
      >> rw[term_ok_def])
  >- metis_tac[pick_names_targets_inj]
  >- metis_tac[pick_names_targets_inj]
  >- (rw[] >> drule pick_names_form >> strip_tac >> gvs[]
      >> drule pick_names_fresh >> strip_tac
      >> metis_tac[VFREE_IN_tm_names])
  >> irule pick_names_sources_inj >> first_x_assum $ irule_at Any >> metis_tac[pick_names_form]
QED

val ilist_r_thms = [MEM_MAP, LAMBDA_PROD, EXISTS_PROD, FORALL_PROD, SWAP_def, MEM_FILTER]


Theorem INST_equation:
  term_ok sig a ∧ term_ok sig b ∧
  EVERY (type_ok (tysof sig)) (MAP FST tyin) ⇒
  INST tyin (a === b) = INST tyin a === INST tyin b
Proof
  rw[equation_def] >> imp_res_tac term_ok_welltyped
  >> simp[INST_COMB, INST_def, INST_CORE_def]
  >> drule INST_CORE_HAS_TYPE >> disch_then $ qspec_then ‘sizeof a’ mp_tac
  >> disch_then $ qspecl_then [‘[]’, ‘tyin’] mp_tac >> rw[]
  >> gvs[REV_ASSOCD, has_type_typeof]
QED

Theorem apply_steps_equation:
  ∀stps.
    term_ok sig x ∧ term_ok sig y ∧ steps_ok sig stps ⇒
    apply_steps stps (x === y) = apply_steps stps x === apply_steps stps y
Proof
  Induct >> simp[apply_steps_def] >> Cases >> rw[apply_steps_def] >> gvs[steps_ok_def]
  >> DEP_REWRITE_TAC[VSUBST_equation, INST_equation]
  >> simp[apply_steps_term_ok, SF SFY_ss] >> metis_tac[]
QED

val eqn_dist_tac =
DEP_REWRITE_TAC [apply_steps_equation,
                 esubst_equation,
                 VSUBST_equation,
                 INST_equation]
>> simp[apply_steps_term_ok, SF SFY_ss]

Theorem REV_ASSOCD_UNIQUE_MEM:
  ∀l. MEM (a, k) l ∧ (∀v. MEM (v, k) l ⇒ v = a) ⇒ REV_ASSOCD k l d = a
Proof
  Induct >> rw[REV_ASSOCD_def] >> gvs[]
QED

Theorem VSUBST_inverse_ACONV:
  ∀c ilist_r.
    term_ok sig c ∧
    (∀t s. MEM (t,s) ilist_r ⇒ ∃x ty y. s = Var x ty ∧ t = Var y ty ∧
                                          term_ok sig t ∧ VFREE_IN s c) ∧
    (∀n ty1 s1 ty2 s2. MEM (Var n ty1,s1) ilist_r ∧ MEM (Var n ty2,s2) ilist_r ⇒
                        ty1 = ty2 ∧ s1 = s2) ∧
    (∀n ty s. MEM (Var n ty,s) ilist_r ⇒ ¬VFREE_IN (Var n ty) c) ⇒
    ACONV c (VSUBST (MAP SWAP ilist_r) (VSUBST ilist_r c))
Proof
  rw[]
  >> irule ACONV_TRANS >> drule VSUBST_VSUBST_ACONV
  >> disch_then $ qspecl_then [‘MAP SWAP ilist_r’, ‘ilist_r’] mp_tac
  >> impl_tac
  >- (rw ilist_r_thms >> first_x_assum drule >> rw[] >> gvs[term_ok_def])
  >> disch_then $ irule_at Any
  >> irule $ iffRL ACONV_db >> rw[SF SFY_ss, term_ok_welltyped]
  >- (irule VSUBST_WELLTYPED >> rw ilist_r_thms
      >- (first_assum drule >> strip_tac >> first_x_assum $ irule_at Any
          >> qpat_x_assum ‘_ = Var _ _’ SUBST1_TAC >> irule VSUBST_HAS_TYPE
          >> simp[has_type_var] >> rw ilist_r_thms >> first_x_assum drule >> rw[])
      >- (rpt $ first_x_assum drule >> rw[])
      >> simp[term_ok_welltyped, SF SFY_ss])
  >> qspec_then ‘db c’ mp_tac dbVSUBST_nil >> disch_then (SUBST1_TAC o GSYM)
  >> qpat_abbrev_tac ‘ilist1 = MAP _ _ ++ _’
  >> ‘∀k v. MEM (v,k) ilist1 ⇒ welltyped v ∧ ∃x ty. k = Var x ty’
    by (unabbrev_all_tac >> rw ilist_r_thms >> first_assum drule >> rw[]
        >- (irule VSUBST_WELLTYPED >> rw ilist_r_thms >> first_x_assum drule >> rw[welltyped_def]
            >> first_x_assum drule >> rw[welltyped_def, has_type_var, SF SFY_ss])
        >> first_x_assum drule >> rpt $ rw[welltyped_def, has_type_var, SF SFY_ss])
  >> imp_res_tac term_ok_welltyped >> drule_all VSUBST_dbVSUBST
  >> disch_then SUBST1_TAC >> irule dbVSUBST_frees >> rw[REV_ASSOCD]
  >> gvs[Abbr‘ilist1’, MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM]
  >> rw[REV_ASSOCD_APPEND, MAP_APPEND]
  >> simp[Once (GSYM REV_ASSOCD_APPEND), Once EQ_SYM_EQ]
  >> irule REV_ASSOCD_EQ_DEFAULT_i
  >> gvs[MEM_APPEND, MEM_MAP, LAMBDA_PROD, EXISTS_PROD, SWAP_def, MEM_FILTER]
  >> rw[] >> strip_d1 >> gvs[]
  >- (first_x_assum drule >> rw[VSUBST_def, db_def]
      >> ‘REV_ASSOCD (Var y ty) (MAP SWAP ilist_r) (Var y ty) = Var x ty’
        by (irule REV_ASSOCD_UNIQUE_MEM
            >> conj_tac
            >- (simp[MEM_MAP, EXISTS_PROD, SWAP_def] >> metis_tac[])
            >> rw[MEM_MAP, EXISTS_PROD, SWAP_def] >> res_tac >> gvs[])
      >> gvs[] >> rw[VSUBST_def, db_def])
  >> metis_tac[dbVFREE_IN_VFREE_IN, db_def]
QED

Theorem VFREE_IN_VSUBST_UNIQUE_MEM:
  ∀n ty sx sty tm ilist.
    welltyped tm ∧
    VFREE_IN (Var sx sty) tm ∧
    MEM (Var n ty, Var sx sty) ilist ∧
    (∀v'. MEM (v', Var sx sty) ilist ⇒ v' = Var n ty) ⇒
    VFREE_IN (Var n ty) (VSUBST ilist tm)
Proof
  rw[VFREE_IN_VSUBST]
  >> qexistsl [‘sx’, ‘sty’] >> simp[]
  >> drule_all REV_ASSOCD_UNIQUE_MEM >> rw[VFREE_IN_def]
QED

Theorem apply_steps_3layer:
  ∀steps c.
    term_ok sig c ∧ steps_ok sig steps ⇒
    ∃ilist_r tyin ilist_f.
      ACONV (apply_steps steps c) (VSUBST ilist_f (INST tyin (VSUBST ilist_r c))) ∧
      unique_varnames (VSUBST ilist_r c) ∧
      (∀t s. MEM (t,s) ilist_r ⇒ ∃x ty y. s = Var x ty ∧ t = Var y ty ∧
                                           term_ok sig t ∧ VFREE_IN s c) ∧
      (∀t s. MEM (t,s) ilist_f ⇒ ∃x ty. s = Var x ty ∧ t has_type ty ∧
                                         term_ok sig t ∧
                                         VFREE_IN s (INST tyin (VSUBST ilist_r c))) ∧
      EVERY (type_ok (FST sig)) (MAP FST tyin) ∧
      (∀nm ty0 v. MEM (Var nm ty0,v) ilist_r ⇒ ¬VFREE_IN (Var nm ty0) c)
Proof
  Induct >> rw[apply_steps_def]
  >- (drule rename_to_unique_varnames >> strip_tac
      >> imp_res_tac term_ok_welltyped
      >> ‘welltyped (VSUBST ilist_r c)’ by (
        irule VSUBST_WELLTYPED >> rw[] >> first_x_assum drule >> rw[] >> rpt $ first_x_assum drule
        >> rw[])
      >> qexistsl [‘ilist_r’, ‘[]’, ‘MAP SWAP ilist_r’]
      >> simp[INST_nil]
      >> rw[MEM_MAP]
      >- (irule VSUBST_inverse_ACONV >> simp[] >> metis_tac[])
      >> TRY (Cases_on ‘y’ >> gvs[SWAP_def]
              >> first_assum drule >> strip_tac >> gvs[]
              >> rpt $ first_x_assum drule >> rw[] >> gvs[term_ok_def]
              >> irule VFREE_IN_VSUBST_UNIQUE_MEM >> rw[] >> metis_tac[])
      >> metis_tac[])
  >> Cases_on ‘h’ >> rw[apply_steps_def, steps_ok_def]
  >- suspend "VStep"
  >> suspend "TStep"
QED

Resume apply_steps_3layer[VStep]:
  gvs[steps_ok_def]
  >> first_x_assum drule >> rw[]
  >> qexistsl [‘ilist_r’,
                ‘tyin’, ‘MAP (λ(t,s). (VSUBST l t, s)) ilist_f ++
               FILTER (λ(t,s). VFREE_IN s (INST tyin (VSUBST ilist_r c)) ∧
                               ¬MEM s (MAP SND ilist_f)) l’]
  >> ‘term_ok sig (VSUBST ilist_r c)’ by
       (irule term_ok_VSUBST >> rw[] >> first_x_assum drule >> rw[])
  >> ‘term_ok sig (INST tyin (VSUBST ilist_r c))’ by
       (irule term_ok_INST >> rw[])
  >> qabbrev_tac ‘tm = INST tyin (VSUBST ilist_r c)’
  >> rw[]
  >- (irule ACONV_TRANS
      >> qexists ‘VSUBST l (VSUBST ilist_f tm)’
      >> rw[]
      >- (irule ACONV_VSUBST >> rw[]
          >- (first_x_assum drule >> rw[] >> metis_tac[EVERY_MEM, FST])
          >- (irule apply_steps_welltyped >> metis_tac[term_ok_welltyped])
          >> irule VSUBST_WELLTYPED >> rw[]
          >> metis_tac[term_ok_welltyped])
      >> irule ACONV_TRANS
      >> qexists ‘VSUBST (MAP (λ(t,s). (VSUBST l t,s)) ilist_f ++
                          FILTER (λ(t,s). ¬MEM s (MAP SND ilist_f)) l) tm’
      >> rw[]
      >- (irule ACONV_SYM >> irule VSUBST_VSUBST_ACONV >> rw[] >> first_x_assum $ irule_at Any
          >> rw[] >> first_x_assum drule >> rw[])
      >> ‘∀il. VSUBST il tm = VSUBST (FILTER (λ(t,s). VFREE_IN s tm) il) tm’
        by metis_tac[VSUBST_FILTER_VFREE]
      >> first_assum (qspec_then
                      ‘MAP (λ(t,s). (VSUBST l t,s)) ilist_f ++
                       FILTER (λ(t,s). ¬MEM s (MAP SND ilist_f)) l’
                      SUBST1_TAC)
      >> first_x_assum (qspec_then
                        ‘MAP (λ(t,s). (VSUBST l t,s)) ilist_f ++
                         FILTER (λ(t,s). VFREE_IN s tm ∧ ¬MEM s (MAP SND ilist_f)) l’
                        SUBST1_TAC)
      >> refl_aconv_tac
      >> simp[FILTER_APPEND, FILTER_FILTER, LAMBDA_PROD, SF CONJ_ss])
  >> gvs[MEM_APPEND, MEM_MAP, MEM_FILTER, LAMBDA_PROD, EXISTS_PROD]
  >> first_x_assum drule >> rw[term_ok_VSUBST]
  >> irule VSUBST_HAS_TYPE >> metis_tac[]
QED

Theorem REV_ASSOCD_dbINST:
  ∀ilistdb x ty tyin.
    (∀t ty'. MEM (t, dbVar x ty') ilistdb ⇒ ty' = ty) ⇒
    dbINST tyin (REV_ASSOCD (dbVar x ty) ilistdb (dbVar x ty)) =
    REV_ASSOCD (dbVar x (TYPE_SUBST tyin ty))
               (MAP (λ(t,s). (dbINST tyin t, dbINST tyin s)) ilistdb)
               (dbVar x (TYPE_SUBST tyin ty))
Proof
  Induct >> rw[REV_ASSOCD_def, dbINST_def]
  >> Cases_on ‘h’ >> simp[REV_ASSOCD_def]
  >- gvs[dbINST_def]
  >- (Cases_on ‘r’ >> gvs[dbINST_def]
      >> first_x_assum (qspecl_then [‘q’, ‘t'’] mp_tac) >> simp[])
  >> first_x_assum irule >> rw[] >> res_tac
QED

Theorem dbINST_dbVSUBST_comm:
  ∀dbtm ilistdb tyin.
    (∀x ty1 ty2. dbVFREE_IN (dbVar x ty1) dbtm ∧
                 dbVFREE_IN (dbVar x ty2) dbtm ⇒ ty1 = ty2) ∧
    (∀t x ty. MEM (t, dbVar x ty) ilistdb ⇒ dbVFREE_IN (dbVar x ty) dbtm) ⇒
    dbINST tyin (dbVSUBST ilistdb dbtm) =
    dbVSUBST (MAP (λ(t,s). (dbINST tyin t, dbINST tyin s)) ilistdb)
             (dbINST tyin dbtm)
Proof
  ‘∀dbtm ilistdb tyin.
    (∀x ty. dbVFREE_IN (dbVar x ty) dbtm ⇒
      ∀ty'. (∃t. MEM (t, dbVar x ty') ilistdb) ⇒ ty' = ty) ⇒
    dbINST tyin (dbVSUBST ilistdb dbtm) =
    dbVSUBST (MAP (λ(t,s). (dbINST tyin t, dbINST tyin s)) ilistdb)
             (dbINST tyin dbtm)’ suffices_by (
    rw[] >> first_x_assum irule >> rw[] >> res_tac >> metis_tac[])
  >> Induct >> rw[dbVSUBST_def, dbINST_def, dbVFREE_IN_def]
  >- (irule REV_ASSOCD_dbINST >> rw[] >> metis_tac[])
  >- (first_x_assum irule >> rw[] >> metis_tac[])
  >- (first_x_assum irule >> rw[] >> metis_tac[])
  >> first_x_assum irule >> rw[] >> metis_tac[]
QED

Theorem INST_VSUBST_ACONV:
  ∀tm ilist tyin.
    welltyped tm ∧ unique_varnames tm ∧
    (∀t s. MEM (t,s) ilist ⇒ ∃x ty. s = Var x ty ∧ t has_type ty ∧ VFREE_IN s tm) ⇒
    ACONV (INST tyin (VSUBST ilist tm))
          (VSUBST (MAP (λ(t,s). (INST tyin t, INST tyin s)) ilist) (INST tyin tm))
Proof
  rw[]
  >> ‘∀v k. MEM (v,k) ilist ⇒ welltyped v ∧ ∃x ty. k = Var x ty’
    by (rpt strip_tac >> res_tac >> gvs[welltyped_def] >> metis_tac[])
  >> ‘welltyped (VSUBST ilist tm)’
    by (irule VSUBST_WELLTYPED >> rw[] >> res_tac >> metis_tac[])
  >> irule $ iffRL ACONV_db >> rpt conj_tac
  >- simp[INST_WELLTYPED]
  >- (irule VSUBST_WELLTYPED >> rw[MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
      >- (first_x_assum drule >> rw[]
          >> qexistsl [‘x’, ‘TYPE_SUBST tyin ty’]
          >> rw[]
          >- simp[INST_def, INST_CORE_def, LET_THM, REV_ASSOCD_def, RESULT_def]
          >> irule INST_HAS_TYPE >> first_x_assum drule >> rw[]
          >> first_x_assum $ irule_at Any >> simp[])
      >> simp[INST_WELLTYPED])
  >> simp[INST_dbINST]
  >> ‘db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm)’
    by (irule VSUBST_dbVSUBST >> simp[] >> metis_tac[])
  >> pop_assum SUBST1_TAC
  >> qspecl_then [‘INST tyin tm’,
                  ‘MAP (λ(t,s). (INST tyin t, INST tyin s)) ilist’] mp_tac VSUBST_dbVSUBST
  >> impl_tac
  >- (simp[INST_WELLTYPED, MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
      >> rw[] >> first_x_assum drule >> rw[] >- metis_tac[INST_WELLTYPED]
      >> simp[INST_def, INST_CORE_def, LET_THM, REV_ASSOCD_def, RESULT_def])
  >> disch_then SUBST1_TAC
  >> simp[INST_dbINST]
  >> ‘MAP (λ(x,y). (db x, db y))
      (MAP (λ(t,s). (INST tyin t, INST tyin s)) ilist) =
      MAP (λ(t,s). (dbINST tyin t, dbINST tyin s))
          (MAP (λ(x,y). (db x, db y)) ilist)’
    by (simp[MAP_MAP_o, o_DEF, LAMBDA_PROD]
        >> irule MAP_CONG >> rw[] >> Cases_on ‘x’ >> rw[]
        >> ‘welltyped q’ by (first_x_assum drule >> rw[] >> metis_tac[welltyped_def])
        >> simp[INST_dbINST] >> first_x_assum drule >> rpt $ rw[INST_dbINST, dbINST_def])
  >> pop_assum SUBST1_TAC
  >> irule dbINST_dbVSUBST_comm >> rw[]
  >> gvs[MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
  >- (last_x_assum drule >> rw[]
      >> irule $ iffRL dbVFREE_IN_VFREE_IN
      >> simp[])
  >> irule $ iffLR unique_varnames_def
  >> imp_res_tac $ iffLR dbVFREE_IN_VFREE_IN
  >> metis_tac[db_def]
QED

Theorem VFREE_IN_INST_imp:
  ∀tm x ty tyin.
    welltyped tm ∧ VFREE_IN (Var x ty) tm ⇒
    VFREE_IN (Var x (TYPE_SUBST tyin ty)) (INST tyin tm)
Proof
  rw[INST_def] >> drule INST_CORE_HAS_TYPE
  >> disch_then $ qspecl_then [‘sizeof tm’, ‘[]’, ‘tyin’] mp_tac
  >> rw[] >> drule INST_CORE_NIL_IS_RESULT >> disch_then $ qspec_then ‘tyin’ mp_tac
  >> rw[] >> metis_tac[]
QED

Theorem dbINST_compose:
  ∀dbtm tyin1 tyin2.
    dbINST tyin1 (dbINST tyin2 dbtm) =
    dbINST (MAP (λ(ty,a). (TYPE_SUBST tyin1 ty, a)) tyin2 ++ tyin1) dbtm
Proof
  Induct >> rw[dbINST_def]
  >> qspecl_then [‘tyin2’, ‘t’, ‘tyin1’] mp_tac TYPE_SUBST_compose
  >> rw[FUN_EQ_THM, pairTheory.PAIR_MAP]
  >> cong_tac NONE >> Cases_on ‘x’ >> simp[]
QED

Theorem INST_compose_ACONV:
  ∀c tyin1 tyin2.
    welltyped c ⇒
    ACONV (INST tyin1 (INST tyin2 c))
          (INST (MAP (λ(ty,a). (TYPE_SUBST tyin1 ty, a)) tyin2 ++ tyin1) c)
Proof
  rw[]
  >> ‘welltyped (INST tyin2 c)’ by metis_tac[INST_WELLTYPED]
  >> ‘welltyped (INST tyin1 (INST tyin2 c))’
    by (irule INST_WELLTYPED >> simp[INST_WELLTYPED])
  >> ‘welltyped (INST (MAP (λ(ty,a). (TYPE_SUBST tyin1 ty, a)) tyin2 ++ tyin1) c)’
    by metis_tac[INST_WELLTYPED]
  >> rw[ACONV_db, INST_dbINST, dbINST_compose]
QED

Resume apply_steps_3layer[TStep]:
  gvs[steps_ok_def]
  >> first_x_assum drule >> rw[]
  >> qexistsl [‘ilist_r’,
               ‘MAP (λ(ty,a). (TYPE_SUBST l ty, a)) tyin ++ l’,
               ‘MAP (λ(t,s). (INST l t, INST l s)) ilist_f’]
  >> ‘term_ok sig (VSUBST ilist_r c)’ by
       (irule term_ok_VSUBST >> rw[] >> first_x_assum drule >> rw[])
  >> ‘welltyped (VSUBST ilist_r c)’ by metis_tac[term_ok_welltyped]
  >> ‘term_ok sig (INST tyin (VSUBST ilist_r c))’ by
       (irule term_ok_INST >> rw[])
  >> qabbrev_tac ‘tm = INST tyin (VSUBST ilist_r c)’
  >> ‘unique_varnames tm’ by
       (unabbrev_all_tac >> irule unique_varnames_INST >> simp[])
  >> ‘welltyped tm’ by metis_tac[term_ok_welltyped] >> rw[]
  >- (‘ACONV (INST l (apply_steps steps' c)) (INST l (VSUBST ilist_f tm))’
        by (irule ACONV_INST >> rw[apply_steps_welltyped, term_ok_welltyped, SF SFY_ss]
            >> irule VSUBST_WELLTYPED >> rw[] >> metis_tac[])
      >> ‘ACONV (INST l (VSUBST ilist_f tm))
          (VSUBST (MAP (λ(t,s). (INST l t, INST l s)) ilist_f) (INST l tm))’
        by (irule INST_VSUBST_ACONV >> rw[] >> metis_tac[])
      >> ‘ACONV (VSUBST (MAP (λ(t,s). (INST l t,INST l s)) ilist_f) (INST l tm))
          (VSUBST (MAP (λ(t,s). (INST l t,INST l s)) ilist_f)
                  (INST (MAP (λ(ty,a). (TYPE_SUBST l ty,a)) tyin ++ l)
                        (VSUBST ilist_r c)))’
        by (irule ACONV_VSUBST >> rw[MEM_MAP]
            >- (Cases_on ‘y’ >> gvs[] >> first_assum drule
                >> rw[INST_def, INST_CORE_def, REV_ASSOCD]
                >> ‘∃q'. INST_CORE [] l q = Result q'’
                  by metis_tac[INST_CORE_NIL_IS_RESULT, IS_RESULT_IMP_Result, term_ok_welltyped]
                >> gvs[] >> first_x_assum drule >> rw[]
                >> qspecl_then [‘sizeof q’, ‘q’, ‘[]’, ‘l’] mp_tac INST_CORE_HAS_TYPE
                >> impl_tac >- simp[term_ok_welltyped, SF SFY_ss]
                >> rw[] >> first_x_assum $ irule_at Any
                >> simp[INST_CORE_def, AllCaseEqs(), REV_ASSOCD]
                >> metis_tac[has_type_typeof])
            >- (irule INST_WELLTYPED >> simp[])
            >- (irule INST_WELLTYPED >> simp[])
            >> unabbrev_all_tac >> irule INST_compose_ACONV >> rw[VSUBST_WELLTYPED])
      >> metis_tac[ACONV_TRANS])
  >> gvs[MAP_APPEND, EVERY_APPEND, EVERY_MAP, LAMBDA_PROD]
  >> gvs ilist_r_thms
  >- (first_x_assum drule >> rw[] >> drule INST_HAS_TYPE >> disch_then $ qspec_then ‘l’ mp_tac
      >> rw[] >> first_x_assum $ irule_at Any >> drule term_ok_INST
      >> disch_then $ qspec_then ‘l’ mp_tac >> rw[EVERY_MAP, LAMBDA_PROD]
      >> qexists ‘x’ >> rw[]
      >> ‘INST l (Var x ty) = Var x (TYPE_SUBST l ty)’
        by simp[INST_def, INST_CORE_def, AllCaseEqs(), REV_ASSOCD]
      >> simp[] >> metis_tac[INST_compose_ACONV, VFREE_IN_ACONV, VFREE_IN_INST_imp])
  >- (rw[EVERY_MEM] >> Cases_on ‘e’ >> simp[] >> irule type_ok_TYPE_SUBST >> rw[]
      >> rw[EVERY_MEM, MEM_MAP] >> gvs[EVERY_MEM] >> rpt $ first_x_assum drule >> rw[]
      >> Cases_on ‘y’ >> gvs[])
  >> metis_tac[]
QED

Finalise apply_steps_3layer

Triviality esubst_Abs_bv_fresh:
  esubsts_ok sig σ ∧ theory_ok (sig,axs) ∧
  term_ok sig (Abs (Var x ty) t) ∧
  esubst σ [] (Abs (Var x ty) t) = Abs (Var z (ty_esubst σ ty)) body ⇒
  z = x ∨ ¬VFREE_IN (Var z ty) t
Proof
  rw[esubst_def, esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ [] (Abs (Var x ty) t) = return v’
    by (mp_tac (esubst_ty0_always_returns
                |> INST [“avds:mlstring list” |-> “[]:mlstring list”]
                |> Q.SPECL [‘σ’, ‘Abs (Var x ty) t’])
        >> simp[term_ok_def])
  >> ‘∃subst_body. esubst_ty0 [] σ [] t = return subst_body’
    by (mp_tac (esubst_ty0_always_returns
                |> INST [“avds:mlstring list” |-> “[]:mlstring list”]
                |> Q.SPECL [‘σ’, ‘t’])
        >> simp[])
  >> gvs[esubst_tm_abs]
  >> Cases_on ‘z = x’ >> simp[]
  >> strip_tac
  >> gvs[esubst_ty0_def, try_eq_return, bind_EQ_return, bind_EQ_error, AllCaseEqs()]
  >> drule_all VFREE_IN_esubst >> gvs[esubst_def, esubst_ty_def]
  >> strip_tac
  >> ‘VFREE_IN (Var (NVARIANT x [] subst_body) (ty_esubst σ ty)) subst_body’
    by metis_tac[VFREE_IN_esubst_tm]
  >> imp_res_tac VFREE_IN_tm_names
  >> metis_tac[NVARIANT_NAMES_THM]
QED

(* If esubst preserves the bound variable name (z), then the only
   pre-image type for z under esubst is the original bound type. *)
Triviality esubst_Abs_bv_type_injective:
  esubsts_ok sig σ ∧ theory_ok (sig,axs) ∧
  term_ok sig (Abs (Var x ty) t) ∧
  esubst σ [] (Abs (Var x ty) t) = Abs (Var z (ty_esubst σ ty)) body ⇒
  ∀oty. VFREE_IN (Var z oty) t ∧ ty_esubst σ oty = ty_esubst σ ty ⇒ oty = ty
Proof
  rw[esubst_def, esubst_ty_def]
  >> ‘∃v. esubst_ty0 [] σ [] (Abs (Var x ty) t) = return v’
    by (mp_tac (esubst_ty0_always_returns
                |> INST [“avds:mlstring list” |-> “[]:mlstring list”]
                |> Q.SPECL [‘σ’, ‘Abs (Var x ty) t’])
        >> simp[term_ok_def])
  >> ‘∃subst_body. esubst_ty0 [] σ [] t = return subst_body’
    by (mp_tac (esubst_ty0_always_returns
                |> INST [“avds:mlstring list” |-> “[]:mlstring list”]
                |> Q.SPECL [‘σ’, ‘t’])
        >> simp[])
  >> gvs[esubst_tm_abs]
  >> Cases_on ‘z = x’
  >- (gvs[esubst_ty0_def, try_eq_return, bind_EQ_return, bind_EQ_error, AllCaseEqs()]
      >> rpt strip_tac
      (* Subgoal 1: first try succeeded — use esubst_ty0_impossible1 *)
      >- (Cases_on ‘oty = ty’ >> simp[]
          >> qspec_then ‘[(Var x ty, Var x (ty_esubst σ ty))]’
               mp_tac esubst_ty0_impossible1
          >> disch_then $ drule_then mp_tac o cj 2
          >> disch_then $ qspecl_then [‘[]’, ‘t’, ‘x’, ‘oty’, ‘ty’] mp_tac
          >> impl_tac
          >- (gvs[DISJ_IMP_THM, FORALL_AND_THM, REV_ASSOCD_def, term_ok_def]
              >> irule $ iffLR FVs_VFREE_in >> simp[term_ok_def, SF SFY_ss])
          >> metis_tac[neq_error])
      (* Subgoal 2: NVARIANT x = x — contradiction via tm_names *)
      >> drule_all VFREE_IN_esubst >> gvs[esubst_def, esubst_ty_def]
      >> strip_tac
      >> ‘VFREE_IN (Var x (ty_esubst σ oty)) subst_body’
        by metis_tac[VFREE_IN_esubst_tm]
      >> imp_res_tac VFREE_IN_tm_names
      >> metis_tac[NVARIANT_NAMES_THM])
  >> gvs[esubst_ty0_def, try_eq_return, bind_EQ_return, bind_EQ_error, AllCaseEqs()]
  >> drule_all VFREE_IN_esubst >> gvs[esubst_def, esubst_ty_def]
  >> strip_tac
  >> ‘VFREE_IN (Var (NVARIANT x [] subst_body) (ty_esubst σ oty)) subst_body’
    by metis_tac[VFREE_IN_esubst_tm]
  >> imp_res_tac VFREE_IN_tm_names
  >> metis_tac[NVARIANT_NAMES_THM]
QED

(* If Var x ty is not free in tm, and x has no other type oty in tm
   such that ty_esubst σ maps oty to ty_esubst σ ty, then
   Var x (ty_esubst σ ty) is not free in esubst σ [] tm. *)
Theorem esubst_not_VFREE_IN:
  esubsts_ok sig σ ∧ term_ok sig tm ∧
  ¬VFREE_IN (Var x ty) tm ∧
  (∀oty. VFREE_IN (Var x oty) tm ∧ ty_esubst σ oty = ty_esubst σ ty ⇒ oty = ty) ⇒
  ¬VFREE_IN (Var x (ty_esubst σ ty)) (esubst σ [] tm)
Proof
  strip_tac >> strip_tac
  >> ‘∃tm1. esubst_ty0 [] σ [] tm = return tm1’
    by metis_tac[esubst_ty0_always_returns]
  >> gvs[esubst_def, esubst_ty_def]
  >> ‘VFREE_IN (Var x (ty_esubst σ ty)) tm1’
    by metis_tac[VFREE_IN_esubst_tm]
  >> drule_then drule esubst_ty0_all_free
  >> disch_then $ drule_at Any >> simp[]
  >> metis_tac[]
QED

Theorem unique_varnames_comb:
  ∀x y. unique_varnames (Comb x y) ⇒ unique_varnames x ∧ unique_varnames y
Proof
  rw[unique_varnames_def] >> metis_tac[]
QED

Theorem unique_varnames_equation:
  ∀x y. unique_varnames (x === y) ⇒ unique_varnames x ∧ unique_varnames y
Proof
  rw[equation_def] >> metis_tac[unique_varnames_comb]
QED

(* Commuting a single-variable VSUBST with esubst, handling both
   the case where the variable is free (uses esubst_VSUBST_comm)
   and the case where it is not (both VSUBSTs are identity). *)
Theorem esubst_single_VSUBST_ACONV:
  theory_ok (sig, axs) ∧ esubsts_ok sig σ ∧ term_ok sig tm ∧
  type_ok (tysof sig) ty ∧
  no_var_collapse σ tm ∧
  (∀oty. VFREE_IN (Var z oty) tm ∧ ty_esubst σ oty = ty_esubst σ ty ⇒ oty = ty) ⇒
  ACONV (VSUBST [(Var vn (ty_esubst σ ty), Var z (ty_esubst σ ty))] (esubst σ [] tm))
        (esubst σ [] (VSUBST [(Var vn ty, Var z ty)] tm))
Proof
  rw[]
  >> Cases_on ‘VFREE_IN (Var z ty) tm’
  >- (‘MAP (λ(s',s). (esubst σ [] s',esubst_ty σ [] s)) [(Var vn ty,Var z ty)]
        = [(Var vn (ty_esubst σ ty), Var z (ty_esubst σ ty))]’
      by simp[esubst_var]
      >> pop_assum (fn th => REWRITE_TAC[GSYM th])
      >> irule esubst_VSUBST_comm >> rw[MEM]
      >> simp[term_ok_def, has_type_var] >> metis_tac[])
  >> ‘VSUBST [(Var vn ty,Var z ty)] tm = tm’
    by (irule VSUBST_NOT_FREE_VAR >> simp[SF SFY_ss])
  >> gvs[]
  >> ‘¬VFREE_IN (Var z (ty_esubst σ ty)) (esubst σ [] tm)’
    by (irule esubst_not_VFREE_IN >> simp[SF SFY_ss])
  >> ‘VSUBST [(Var vn (ty_esubst σ ty),Var z (ty_esubst σ ty))] (esubst σ [] tm)
      = esubst σ [] tm’
    by (irule VSUBST_NOT_FREE_VAR >> simp[SF SFY_ss]
        >> metis_tac[esubst_term_ok])
  >> simp[ACONV_REFL]
QED

(* Splitting a VSUBST: filtering out the bound variable mapping and
   re-adding it separately gives ACONV to the original VSUBST.
   This is the key VSUBST lemma for the beta case. *)
Theorem VSUBST_split_bv_ACONV:
  welltyped t ∧
  (∀t' s. MEM (t',s) ilist ⇒ welltyped t' ∧ (∃x' ty' y. s = Var x' ty' ∧ t' = Var y ty')) ∧
  (∀nm ty0 v. MEM (Var nm ty0,v) ilist ⇒ ¬VFREE_IN (Var nm ty0) t) ∧
  ¬EXISTS (λ(s',s). VFREE_IN (Var x ty) s' ∧ VFREE_IN s t)
          (FILTER (λ(s',s). s ≠ Var x ty) ilist) ⇒
  ACONV (VSUBST [(VSUBST ilist (Var x ty), Var x ty)]
         (VSUBST (FILTER (λ(s',s). s ≠ Var x ty) ilist) t))
        (VSUBST ilist t)
Proof
  rpt strip_tac
  >> ‘∀s1 s2. MEM (s1,s2) ilist ⇒ ∃a b. s2 = Var a b ∧ s1 has_type b’
       by (rw[] >> res_tac >> gvs[has_type_rules])
  >> ‘∀s1 s2. MEM (s1,s2) (FILTER (λ(s1,s2). s2 ≠ Var x ty) ilist) ⇒
              ∃a b. s2 = Var a b ∧ s1 has_type b’
       by (rw[MEM_FILTER] >> res_tac)
  >> ‘∀k v. MEM (v,k) ilist ⇒ welltyped v ∧ (∃a b. k = Var a b)’
       by (rw[] >> res_tac >> gvs[])
  >> ‘∀k v. MEM (v,k) (FILTER (λ(s1,s2). s2 ≠ Var x ty) ilist) ⇒
            welltyped v ∧ (∃a b. k = Var a b)’
       by (rw[MEM_FILTER] >> res_tac >> gvs[])
  >> ‘welltyped (VSUBST (FILTER (λ(s1,s2). s2 ≠ Var x ty) ilist) t)’
       by (irule VSUBST_WELLTYPED >> rw[] >> res_tac >> gvs[])
  >> ‘welltyped (VSUBST ilist t)’
       by (irule VSUBST_WELLTYPED >> rw[] >> res_tac >> gvs[])
  >> ‘VSUBST ilist (Var x ty) has_type ty’
       by (irule VSUBST_HAS_TYPE >> simp[has_type_rules])
  >> ‘db (VSUBST ilist t) =
      dbVSUBST (MAP (λ(p,q). (db p, db q)) ilist) (db t)’
       by rw[VSUBST_dbVSUBST, SF SFY_ss]
  >> ‘db (VSUBST (FILTER (λ(s1,s2). s2 ≠ Var x ty) ilist) t) =
      dbVSUBST (MAP (λ(p,q). (db p, db q))
                     (FILTER (λ(s1,s2). s2 ≠ Var x ty) ilist)) (db t)’
       by rw[VSUBST_dbVSUBST, MEM_FILTER, SF SFY_ss]
  >> ‘welltyped (VSUBST ilist (Var x ty))’ by metis_tac[welltyped_def]
  >> irule $ iffRL ACONV_db >> rw[]
  >- (irule VSUBST_WELLTYPED >> simp[])
  >> rw[VSUBST_dbVSUBST, SF SFY_ss]
  >> ‘¬MEM (dbVar x ty)
          (MAP SND (FILTER (λ(p,q). q ≠ dbVar x ty)
                           (MAP (λ(p,q). (db p, db q)) ilist)))’
       by simp[MEM_MAP, MEM_FILTER, EXISTS_PROD, FORALL_PROD]
  >> rw[Once dbVSUBST_comp, MAP_db_FILTER_neq]
  >> irule dbVSUBST_frees
  >> gen_tac >> strip_tac
  >> Cases_on ‘k = dbVar x ty’
  >- simp[REV_ASSOCD_APPEND, REV_ASSOCD_def, REV_ASSOCD_MAP,
          MEM_MAP, MEM_FILTER, EXISTS_PROD, FORALL_PROD]
  >> simp[REV_ASSOCD_APPEND, REV_ASSOCD_def, REV_ASSOCD_MAP,
          REV_ASSOCD_FILTER, MEM_MAP, MEM_FILTER, EXISTS_PROD, FORALL_PROD]
  >> IF_CASES_TAC >> gvs[]
  >- (
    ‘∃x'' ty''. p_2 = Var x'' ty''’ by metis_tac[]
    >> gvs[]
    >> qspecl_then [‘ilist’, ‘x''’, ‘ty''’] mp_tac REV_ASSOCD_MAP_db
    >> impl_tac >- metis_tac[]
    >> strip_tac >> gvs[]
    >> ‘VFREE_IN (Var x'' ty'') t’ by (
         irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[db_def]
       )
    >> ‘Var x'' ty'' ≠ Var x ty’ by (strip_tac >> gvs[db_def])
    >> ‘∃rv_nm rv_ty. REV_ASSOCD (Var x'' ty'') ilist (Var x'' ty'') = Var rv_nm rv_ty’ by (
         qspecl_then [‘ilist’, ‘Var x'' ty''’, ‘Var x'' ty''’]
           strip_assume_tac REV_ASSOCD_MEM
         >> gvs[] >> res_tac >> gvs[]
       )
    >> ‘¬(rv_nm = x ∧ rv_ty = ty)’ by (
         strip_tac >> gvs[]
         >> qspecl_then [‘ilist’, ‘Var x'' ty''’, ‘Var x'' ty''’]
              strip_assume_tac REV_ASSOCD_MEM
         >> gvs[]
         >> qpat_x_assum ‘EVERY _ _’ mp_tac
         >> simp[EVERY_MEM, MEM_FILTER, FORALL_PROD, EXISTS_MEM]
         >> first_x_assum $ irule_at Any >> rw[]
       )
    >> gvs[db_def, dbVSUBST_def, REV_ASSOCD_def] >> rw[]
  )
  >> qspecl_then [‘MAP (λ(p,q). (db p,db q)) ilist’, ‘k’, ‘k’]
       strip_assume_tac REV_ASSOCD_MEM
  >- (gvs[MEM_MAP, FORALL_PROD, EXISTS_PROD] >> res_tac)
  >> gvs[]
QED

Theorem beta_esubst_inner_derivable:
  theory_ok (sig, axs) ∧ esubsts_ok sig σ ∧
  (∀ax. ax ∈ axs ⇒ no_var_collapse σ ax) ∧
  type_ok (tysof sig) ty ∧ term_ok sig t ∧
  unique_varnames (VSUBST ilist_r (Comb (Abs (Var x ty) t) (Var x ty) === t)) ∧
  (∀t' s. MEM (t',s) ilist_r ⇒
    ∃x' ty' y. s = Var x' ty' ∧ t' = Var y ty' ∧
    term_ok sig t' ∧
    VFREE_IN s (Comb (Abs (Var x ty) t) (Var x ty) === t)) ∧
  (∀nm ty0 v. MEM (Var nm ty0,v) ilist_r ⇒
    ¬VFREE_IN (Var nm ty0) (Comb (Abs (Var x ty) t) (Var x ty) === t)) ⇒
  ((esubst_sig σ sig, IMAGE (esubst σ []) axs), []) |-
    esubst σ [] (VSUBST ilist_r (Comb (Abs (Var x ty) t) (Var x ty) === t))
Proof
  rw[] >> qabbrev_tac ‘ty' = ty_esubst σ ty’
  >> drule_all theory_ok_esubst_axs >> disch_then $ qspec_then ‘[]’ assume_tac
  >> ‘type_ok (tysof sig) ty'’
    by (simp[Abbr‘ty'’] >> irule esubsts_ok_type_ok >> simp[])
  (* term_ok for VSUBST'd subterms *)
  >> ‘term_ok sig (VSUBST ilist_r (Abs (Var x ty) t))’
    by (irule term_ok_VSUBST >> simp[term_ok_def]
        >> rw[] >> first_x_assum drule >> rw[])
  >> ‘term_ok sig (VSUBST ilist_r t)’
    by (irule term_ok_VSUBST >> simp[]
        >> rw[] >> first_x_assum drule >> rw[])
  (* VSUBST'd abs is Abs (Var xn ty) body_v *)
  >> ‘∃xn body_v. VSUBST ilist_r (Abs (Var x ty) t) = Abs (Var xn ty) body_v’
    by (simp[VSUBST_def, LET_THM] >> rw[] >> metis_tac[])
  (* Apply simple_esubst_Abs to get z, body_e *)
  >> ‘∃z body_e.
        esubst σ [] (Abs (Var xn ty) body_v) = Abs (Var z ty') body_e ∧
        ACONV body_e (esubst σ [] (VSUBST [(Var z ty, Var xn ty)] body_v)) ∧
        term_ok (esubst_sig σ sig) body_e’
    by (‘term_ok sig (Abs (Var xn ty) body_v)’ by metis_tac[]
        >> drule_all simple_esubst_Abs >> rw[Abbr‘ty'’] >> metis_tac[])
  (* VSUBST'd var is Var vn ty for some vn *)
  >> ‘∃vn. VSUBST ilist_r (Var x ty) = Var vn ty’
    by (simp[VSUBST_def]
        >> qspecl_then [‘ilist_r’, ‘Var x ty’, ‘Var x ty’] mp_tac REV_ASSOCD_MEM
        >> rw[] >> res_tac >> gvs[])
  (* term_ok for the full beta equation *)
  >> ‘term_ok sig (Comb (Abs (Var x ty) t) (Var x ty) === t)’
    by (‘is_std_sig sig’ by gvs[theory_ok_def]
        >> rw[term_ok_clauses, term_ok_def, typeof_def, codomain_def]
        >> imp_res_tac term_ok_welltyped >> simp[WELLTYPED_LEMMA])
  (* proves_BETA in esubst'd theory *)
  >> ‘((esubst_sig σ sig, IMAGE (esubst σ []) axs), []) |-
      Comb (Abs (Var z ty') body_e) (Var z ty') === body_e’
    by (irule proves_BETA >> simp[])
  (* proves_INST: substitute Var z ty' -> Var vn ty' to match argument *)
  >> drule_at Any proves_INST
  >> disch_then $ qspec_then ‘[(Var vn ty', Var z ty')]’ mp_tac
  >> impl_tac
  >- (rw[MEM] >> simp[term_ok_def])
  >> rw[term_image_thm]
  (* Use proves_ACONV_concl to match with target *)
  >> irule proves_ACONV_concl >> first_x_assum $ irule_at Any
  >> conj_tac
  >- (irule esubst_VSUBST_welltyped >> qexistsl [‘axs’, ‘sig’] >> rw[]
      >> first_x_assum drule >> strip_tac >> gvs[has_type_var])
  (* Decompose both sides using equation structure *)
  >> ‘VSUBST [(Var vn ty', Var z ty')]
      (Comb (Abs (Var z ty') body_e) (Var z ty') === body_e)
      = (Comb (Abs (Var z ty') body_e) (Var vn ty')
             === VSUBST [(Var vn ty', Var z ty')] body_e)’
    by (DEP_REWRITE_TAC[GEN_ALL VSUBST_equation]
        >> simp[term_ok_welltyped, SF SFY_ss, VSUBST_def] >> rev_dxrule esubsts_ok_type_ok
        >> rw[] >> res_tac >> first_x_assum $ irule_at Any >> simp[])
  >> ‘esubst σ [] (VSUBST ilist_r (Comb (Abs (Var x ty) t) (Var x ty) === t))
      = (Comb (Abs (Var z ty') body_e) (Var vn ty')
             === esubst σ [] (VSUBST ilist_r t))’
    by (eqn_dist_tac >> simp[VSUBST_def] >> DEP_REWRITE_TAC[esubst_comb] >> rw[]
        >> gvs[term_ok_def, term_ok_welltyped, SF SFY_ss]
        >> first_x_assum drule >> rw[has_type_var])
  >> pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC
  >> irule ACONV_equation >> rw[]
  >> simp[SF SFY_ss, term_ok_welltyped, VSUBST_WELLTYPED]
  >- (irule esubst_VSUBST_welltyped >> ntac 2 $ first_x_assum $ irule_at (Pos last)
      >> metis_tac[PULL_EXISTS, FORALL_AND_THM, DISJ_IMP_THM, has_type_var])
  >> irule ACONV_TRANS
  >> qexists ‘esubst σ [] (VSUBST [(Var vn ty, Var xn ty)] body_v)’
  >> conj_tac
  >- suspend "sg1"
  >> suspend "sg2"
QED

Resume beta_esubst_inner_derivable[sg1]:
  irule ACONV_TRANS
  >> qexists ‘VSUBST [(Var vn ty', Var z ty')] (esubst σ [] (VSUBST [(Var z ty, Var xn ty)] body_v))’
  >> conj_tac
  >- (irule ACONV_VSUBST >> rw[MEM]
      >> simp[term_ok_welltyped, SF SFY_ss]
      >> irule esubst_VSUBST_welltyped
      >> gvs[] >> metis_tac[term_ok_def])
  >> ‘term_ok sig (VSUBST [(Var z ty, Var xn ty)] body_v)’
    by (irule term_ok_VSUBST >> rw[MEM]
        >> gvs[term_ok_def, has_type_var])
  >> irule ACONV_TRANS
  >> qexists ‘esubst σ [] (VSUBST [(Var vn ty, Var z ty)] (VSUBST [(Var z ty, Var xn ty)] body_v))’
  >> rw[]
  >- (Cases_on ‘z = xn’ >- suspend "sg1_a" >- suspend "sg1_b")
  >> irule esubst_ACONV >> simp[SF SFY_ss]
  >> conj_tac
  >- suspend "sg1_vsubst_trans"
  >> last_x_assum $ irule_at (Pos hd) >> simp[]
  >> conj_tac >> irule term_ok_VSUBST >> rw[] >> metis_tac[term_ok_def]
QED

Theorem REV_ASSOCD_ID:
  ∀ilist.
    (∀k v. MEM (v,k) ilist ⇒ x = v) ⇒
    REV_ASSOCD x ilist x = x
Proof
  Induct >> simp[REV_ASSOCD] >> Cases >> rw[REV_ASSOCD] >> metis_tac[]
QED

Resume beta_esubst_inner_derivable[sg1_a]:
  pop_assum SUBST_ALL_TAC
  >> ‘term_ok sig (Abs (Var xn ty) body_v)’ by (
    qpat_x_assum ‘VSUBST _ (Abs _ _) = Abs _ body_v’
                 (fn th => REWRITE_TAC [GSYM th])
    >> first_x_assum ACCEPT_TAC)
  >> ‘term_ok sig body_v’ by gvs[term_ok_def]
  >> ‘VSUBST [(Var xn ty,Var xn ty)] body_v = body_v’
    by (irule VSUBST_ID >> simp[MEM, SF SFY_ss])
  >> gvs[]
  >> ‘unique_varnames (Abs (Var xn ty) body_v)’ by (
    rw[unique_varnames_def] >> rpt strip_tac
    >> qpat_x_assum ‘unique_varnames _’ (mp_tac o REWRITE_RULE [unique_varnames_def])
    >> disch_then $ qspecl_then [‘x'’, ‘ty1’, ‘ty2’] mp_tac
    >> simp[] >> disch_then irule
    >> conj_tac >> (
      ‘VFREE_IN (Var x' ty1) (Comb (Abs (Var xn ty) body_v) (Var vn ty))
       ∨ VFREE_IN (Var x' ty2) (Comb (Abs (Var xn ty) body_v) (Var vn ty))’
         by simp[VFREE_IN_def]
      >> simp[equation_def, VSUBST_def, VFREE_IN_def, typeof_def, codomain_def]))
  >> ‘∀oty. VFREE_IN (Var xn oty) body_v ∧ ty_esubst σ oty = ty_esubst σ ty ⇒ oty = ty’ by (
    ‘esubst σ [] (Abs (Var xn ty) body_v) = Abs (Var xn (ty_esubst σ ty)) body_e’
       by gvs[markerTheory.Abbrev_def]
    >> rpt strip_tac
    >> irule esubst_Abs_bv_type_injective
    >> rpt $ last_x_assum $ irule_at Any >> simp[])
  >> ‘no_var_collapse σ body_v’
    by (rw[no_var_collapse] >> Cases_on ‘x = xn’
        >> qpat_x_assum ‘unique_varnames _’ mp_tac >> simp[unique_varnames_def]
        >> disch_then $ qspecl_then [‘x'’, ‘ty1’, ‘ty2’] mp_tac >> metis_tac[])
  >> simp[Abbr‘ty'’]
  >> irule esubst_single_VSUBST_ACONV >> simp[SF SFY_ss]
QED

Resume beta_esubst_inner_derivable[sg1_b]:
  ‘term_ok sig (Abs (Var xn ty) body_v)’ by (
    qpat_x_assum ‘VSUBST _ (Abs _ _) = Abs _ body_v’
                 (fn th => REWRITE_TAC [GSYM th])
    >> first_x_assum ACCEPT_TAC)
  >> ‘term_ok sig body_v’ by gvs[term_ok_def]
  >> ‘esubst σ [] (Abs (Var xn ty) body_v) = Abs (Var z (ty_esubst σ ty)) body_e’
    by gvs[markerTheory.Abbrev_def]
  >> ‘¬VFREE_IN (Var z ty) body_v’
    by metis_tac[esubst_Abs_bv_fresh]
  >> ‘∀oty. VFREE_IN (Var z oty) body_v ∧ ty_esubst σ oty = ty_esubst σ ty ⇒ oty = ty’ by (
    rpt strip_tac >> irule esubst_Abs_bv_type_injective
    >> rpt $ last_x_assum $ irule_at Any >> simp[])
  >> ‘unique_varnames (Abs (Var xn ty) body_v)’ by (
    ‘is_std_sig sig’ by gvs[theory_ok_def]
    >> ‘term_ok sig (Comb (Abs (Var x ty) t) (Var x ty))’ by gvs[term_ok_equation]
    >> ‘VSUBST ilist_r (Comb (Abs (Var x ty) t) (Var x ty) === t) =
        Comb (Abs (Var xn ty) body_v) (Var vn ty) === VSUBST ilist_r t’ by (
      drule_at (Pos hd) VSUBST_equation
      >> disch_then (qspecl_then [‘ilist_r’, ‘t’] mp_tac)
      >> impl_tac >- (rw[] >> res_tac >> gvs[has_type_var])
      >> rw[] >> simp[Once VSUBST_def] >> gvs[])
    >> qpat_x_assum ‘unique_varnames _’ mp_tac >> pop_assum (fn th => REWRITE_TAC [th])
    >> metis_tac[unique_varnames_equation, unique_varnames_comb])
  >> Cases_on ‘VFREE_IN (Var xn ty) body_v’
  >- (‘no_var_collapse σ (VSUBST [(Var z ty,Var xn ty)] body_v)’ by (
        ‘welltyped body_v’ by metis_tac[term_ok_welltyped]
        >> rw[no_var_collapse] >> rpt strip_tac
        >> ntac 2 (qpat_x_assum ‘VFREE_IN _ (VSUBST _ _)’ mp_tac)
        >> simp[VFREE_IN_VSUBST, REV_ASSOCD_def, VFREE_IN_def]
        >> rpt strip_tac >> gvs[]
        >> every_case_tac >> gvs[] >> rw[]
        >- metis_tac[unique_varnames_def, VFREE_IN_def]
        >- metis_tac[unique_varnames_def, VFREE_IN_def]
        >> Cases_on ‘xn = x'’ >> gvs[]
        >> strip_tac >> drule $ iffLR unique_varnames_def
        >> disch_then $ qspecl_then [‘x'’, ‘ty''’, ‘ty'³'’] mp_tac >> simp[VFREE_IN_def])
      >> ‘VFREE_IN (Var z ty) (VSUBST [(Var z ty,Var xn ty)] body_v)’ by (
        ‘welltyped body_v’ by metis_tac[term_ok_welltyped]
        >> simp[VFREE_IN_VSUBST, REV_ASSOCD_def, VFREE_IN_def]
        >> first_x_assum $ irule_at Any >> rw[])
      >> simp[Abbr‘ty'’]
      >> ‘MAP (λ(s',s). (esubst σ [] s',esubst_ty σ [] s)) [(Var vn ty,Var z ty)]
          = [(Var vn (ty_esubst σ ty), Var z (ty_esubst σ ty))]’
        by simp[esubst_var]
      >> pop_assum (fn th => REWRITE_TAC[GSYM th])
      >> irule esubst_VSUBST_comm >> rw[MEM]
      >> simp[term_ok_def, has_type_var] >> metis_tac[])
  >> ‘VSUBST [(Var z ty,Var xn ty)] body_v = body_v’
    by (irule VSUBST_NOT_FREE_VAR >> simp[SF SFY_ss])
  >> ‘VSUBST [(Var vn ty,Var z ty)] body_v = body_v’
    by (irule VSUBST_NOT_FREE_VAR >> simp[SF SFY_ss])
  >> gvs[]
  >> ‘¬VFREE_IN (Var z (ty_esubst σ ty)) (esubst σ [] body_v)’
    by (irule esubst_not_VFREE_IN >> simp[SF SFY_ss])
  >> simp[Abbr‘ty'’]
  >> ‘VSUBST [(Var vn (ty_esubst σ ty),Var z (ty_esubst σ ty))] (esubst σ [] body_v)
      = esubst σ [] body_v’
    by (irule VSUBST_NOT_FREE_VAR >> simp[] >> dxrule_at Any esubst_term_ok >> metis_tac[])
  >> simp[ACONV_REFL]
QED

Resume beta_esubst_inner_derivable[sg1_vsubst_trans]:
  ‘term_ok sig (Abs (Var xn ty) body_v)’ by gvs[]
  >> ‘term_ok sig body_v’ by gvs[term_ok_def]
  >> Cases_on ‘z = xn’
  >- (‘VSUBST [(Var xn ty,Var xn ty)] body_v = body_v’
        by (irule VSUBST_ID >> simp[MEM, SF SFY_ss])
      >> gvs[])
  >> ‘esubst σ [] (Abs (Var xn ty) body_v) = Abs (Var z (ty_esubst σ ty)) body_e’
    by gvs[markerTheory.Abbrev_def]
  >> ‘¬VFREE_IN (Var z ty) body_v’
    by metis_tac[esubst_Abs_bv_fresh]
  >> irule ACONV_TRANS
  >> drule VSUBST_VSUBST_ACONV
  >> disch_then $ qspecl_then [‘[(Var vn ty,Var z ty)]’, ‘[(Var z ty,Var xn ty)]’] mp_tac
  >> simp[] >> strip_tac >> drule ACONV_SYM >> disch_then $ irule_at Any >> rw[]
  >> ‘VSUBST [(Var vn ty,Var xn ty); (Var vn ty,Var z ty)] body_v
      = VSUBST [(Var vn ty,Var xn ty)] body_v’
    by (qpat_x_assum ‘term_ok sig body_v’
          (fn th => ONCE_REWRITE_TAC [MATCH_MP VSUBST_FILTER_VFREE th])
        >> simp[])
  >> simp[ACONV_REFL]
QED

Resume beta_esubst_inner_derivable[sg2]:
  (* Property 4 implies no capture avoidance: xn = x *)
  ‘¬EXISTS (λ(s',s). VFREE_IN (Var x ty) s' ∧ VFREE_IN s t)
           (FILTER (λ(s',s). s ≠ Var x ty) ilist_r)’
    by (strip_tac >> gvs[EXISTS_MEM, MEM_FILTER]
        >> PairCases_on ‘e’ >> gvs[]
        >> res_tac >> gvs[VFREE_IN_def]
        >> res_tac >> gvs[VFREE_IN_def, equation_def])
  >> ‘xn = x ∧ body_v = VSUBST (FILTER (λ(s',s). s ≠ Var x ty) ilist_r) t’
    by (qpat_x_assum ‘VSUBST ilist_r (Abs _ _) = _’ mp_tac
        >> simp[VSUBST_def, LET_THM] >> rw[])
  >> gvs[]
  >> ‘term_ok sig (VSUBST [(Var vn ty,Var x ty)]
        (VSUBST (FILTER (λ(s',s). s ≠ Var x ty) ilist_r) t))’
    by (irule term_ok_VSUBST >> rw[MEM]
        >> simp[has_type_var]
        >> ‘term_ok sig (Var vn ty)’
          by (‘term_ok sig (VSUBST ilist_r (Var x ty))’
                by (irule term_ok_VSUBST >> simp[] >> rw[]
                    >> first_x_assum drule >> rw[])
              >> gvs[])
        >> gvs[term_ok_def])
  >> irule esubst_ACONV >> simp[SF SFY_ss]
  >> ‘Var vn ty = VSUBST ilist_r (Var x ty)’ by gvs[]
  >> pop_assum (fn th => ONCE_REWRITE_TAC[th])
  >> irule VSUBST_split_bv_ACONV
  >> imp_res_tac term_ok_welltyped >> simp[SF SFY_ss]
  >> rpt strip_tac >> res_tac
  >> gvs[term_ok_welltyped, equation_def, VFREE_IN_def, typeof_def, codomain_def]
QED

Finalise beta_esubst_inner_derivable

(* esubst commutes past VSUBST ∘ INST up to ACONV, combining
   esubst_INST_comm and esubst_VSUBST_comm into one result. *)
Theorem esubst_INST_VSUBST_ACONV:
  theory_ok (sig, axs) ∧ esubsts_ok sig σ ∧
  term_ok sig t ∧ unique_varnames t ∧
  EVERY (type_ok (tysof sig)) (MAP FST tyin) ∧
  (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧
                                      term_ok sig s' ∧
                                      VFREE_IN s (INST tyin t)) ⇒
  ACONV (VSUBST (MAP (λ(s',s). (esubst σ [] s', esubst_ty σ [] s)) ilist)
                (INST (MAP (λ(ty,a). (ty_esubst σ ty, a)) tyin)
                      (esubst σ [] t)))
        (esubst σ [] (VSUBST ilist (INST tyin t)))
Proof
  rw[]
  >> irule ACONV_TRANS
  >> qexists ‘VSUBST (MAP (λ(s',s). (esubst σ [] s', esubst_ty σ [] s)) ilist)
                      (esubst σ [] (INST tyin t))’
  >> reverse conj_tac
  >- (irule esubst_VSUBST_comm >> rw[]
      >- (irule unique_varnames_no_var_collapse
          >> irule unique_varnames_INST >> simp[term_ok_welltyped, SF SFY_ss])
      >- (qexistsl [‘axs’, ‘sig’] >> simp[SF SFY_ss]
          >> irule term_ok_INST >> simp[])
      >> rw[] >> rpt $ first_x_assum $ irule_at Any >> rw[]
      >> first_x_assum drule >> rw[SF SFY_ss])
  >> irule ACONV_VSUBST >> rw[]
  >- (gvs[MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >> first_x_assum drule >> rw[]
      >> simp[esubst_ty_def] >> irule esubst_has_type1 >> metis_tac[])
  >- (irule INST_WELLTYPED >> metis_tac[esubst_welltyped])
  >- metis_tac[esubst_welltyped, term_ok_INST]
  >> irule ACONV_SYM >> irule esubst_INST_comm
  >> simp[EVERY_MEM, SF SFY_ss]
  >> qexistsl [‘axs’, ‘sig’] >> gvs[EVERY_MEM]
QED

(* If we can derive esubst σ [] t, then we can push through INST_TYPE and INST
   to derive esubst σ [] (VSUBST ilist (INST tyin t)). *)
Theorem derives_esubst_INST_VSUBST:
  theory_ok (sig, axs) ∧ esubsts_ok sig σ ∧
  term_ok sig t ∧ unique_varnames t ∧
  EVERY (type_ok (tysof sig)) (MAP FST tyin) ∧
  (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧
                                      term_ok sig s' ∧
                                      VFREE_IN s (INST tyin t)) ∧
  ((esubst_sig σ sig, IMAGE (esubst σ []) axs), []) |- esubst σ [] t ⇒
  ((esubst_sig σ sig, IMAGE (esubst σ []) axs), []) |-
    esubst σ [] (VSUBST ilist (INST tyin t))
Proof
  rw[]
  >> drule_at Any proves_INST_TYPE
  >> disch_then $ qspec_then ‘MAP (λ(ty,a). (ty_esubst σ ty, a)) tyin’ mp_tac
  >> impl_tac
  >- (simp[EVERY_MAP, EVERY_MEM]
      >> rw[] >> pairarg_tac >> simp[]
      >> irule esubsts_ok_type_ok >> simp[EVERY_MEM]
      >> gvs[EVERY_MEM, MEM_MAP] >> first_x_assum irule
      >> metis_tac[EXISTS_PROD, FST])
  >> rw[term_image_thm]
  >> drule_at Any proves_INST
  >> disch_then $ qspec_then ‘MAP (λ(s',s). (esubst σ [] s', esubst_ty σ [] s)) ilist’ mp_tac
  >> impl_tac >> rw[]
  >- (gvs[MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
      >> first_x_assum drule >> rw[] >> simp[]
      >> conj_tac >- (irule esubst_has_type1 >> simp[SF SFY_ss])
      >> irule esubst_term_ok >> simp[SF SFY_ss])
  >> rw[term_image_thm]
  >> irule proves_ACONV_concl >> first_x_assum $ irule_at Any >> rw[]
  >- metis_tac[esubst_welltyped, term_ok_VSUBST, term_ok_INST]
  >> irule esubst_INST_VSUBST_ACONV >> rw[]
  >> qexistsl [‘axs’, ‘sig’] >> simp[SF SFY_ss]
QED

(* Beta case: full result combining 3-layer decomposition with inner derivability.
   Uses apply_steps_3layer, commutes esubst past outer two layers
   (via derives_esubst_INST_VSUBST), then uses beta_esubst_inner_derivable
   for the inner layer. *)
Theorem beta_steps_esubst_derivable:
  ∀steps.
    theory_ok (sig, axs) ∧ esubsts_ok sig σ ∧
    (∀ax. ax ∈ axs ⇒ no_var_collapse σ ax) ∧
    type_ok (tysof sig) ty ∧ term_ok sig t ∧
    steps_ok sig steps ⇒
    ((esubst_sig σ sig, IMAGE (esubst σ []) axs), []) |-
      esubst σ [] (apply_steps steps (Comb (Abs (Var x ty) t) (Var x ty) === t))
Proof
  rw[]
  >> qabbrev_tac ‘c = Comb (Abs (Var x ty) t) (Var x ty) === t’
  >> ‘term_ok sig c’
    by (‘is_std_sig sig’ by gvs[theory_ok_def]
        >> simp[Abbr‘c’, term_ok_clauses, term_ok_def, typeof_def, codomain_def]
        >> imp_res_tac term_ok_welltyped >> simp[WELLTYPED_LEMMA])
  >> drule_all apply_steps_3layer >> rw[]
  >> ‘term_ok sig (VSUBST ilist_r c)’
    by (irule term_ok_VSUBST >> rw[] >> first_x_assum drule >> rw[])
  (* Inner layer: use beta_esubst_inner_derivable *)
  >> ‘((esubst_sig σ sig,IMAGE (esubst σ []) axs),[]) |-
       esubst σ [] (VSUBST ilist_r c)’
    by (unabbrev_all_tac >> irule beta_esubst_inner_derivable >> rw[] >> metis_tac[])
  (* Outer layers: use derives_esubst_INST_VSUBST *)
  >> ‘((esubst_sig σ sig,IMAGE (esubst σ []) axs),[]) |-
       esubst σ [] (VSUBST ilist_f (INST tyin (VSUBST ilist_r c)))’
    by (irule derives_esubst_INST_VSUBST >> rpt conj_tac >> first_x_assum ACCEPT_TAC)
  (* Bridge ACONV from apply_steps_3layer *)
  >> ‘term_ok sig (INST tyin (VSUBST ilist_r c))’
    by (irule term_ok_INST >> simp[EVERY_MEM])
  >> ‘term_ok sig (VSUBST ilist_f (INST tyin (VSUBST ilist_r c)))’
    by (irule term_ok_VSUBST >> rw[] >> first_x_assum drule
        >> strip_tac >> metis_tac[])
  >> irule proves_ACONV_concl >> first_x_assum $ irule_at Any
  >> conj_tac
  >- (irule esubst_welltyped >> qexistsl [‘axs’, ‘sig’]
      >> simp[apply_steps_term_ok, SF SFY_ss])
  >> irule esubst_ACONV >> conj_tac
  >- (irule ACONV_SYM >> first_x_assum ACCEPT_TAC)
  >> qexistsl [‘axs’, ‘sig’] >> simp[apply_steps_term_ok, SF SFY_ss]
QED

Theorem axiom_steps_derivable:
  ∀stps c.
    theory_ok (sig,axs) ∧
    c ∈ axs ∧
    no_var_collapse σ c ∧
    esubsts_ok sig σ ∧
    steps_ok sig stps ⇒
    ((esubst_sig σ sig, IMAGE (esubst σ []) axs), []) |-
      esubst σ [] (apply_steps stps c)
Proof
  rw[]
  >> ‘term_ok sig c’ by gvs[theory_ok_def]
  >> drule_all apply_steps_3layer >> rw[]
  >> drule_all theory_ok_esubst_axs >> disch_then $ qspec_then ‘[]’ mp_tac >> rw[]
  >> ‘term_ok sig (VSUBST ilist_r c)’
    by (irule term_ok_VSUBST >> rw[] >> first_x_assum drule >> rw[])
  >> ‘term_ok sig (INST tyin (VSUBST ilist_r c))’
     by (irule term_ok_INST >> simp[EVERY_MEM])
  >> ‘term_ok sig (VSUBST ilist_f (INST tyin (VSUBST ilist_r c)))’
    by (irule term_ok_VSUBST >> rw[] >> first_x_assum drule >> rw[])
  >> rev_drule_all apply_steps_term_ok >> rw[]
  >> qspecl_then [‘esubst σ [] c’, ‘(esubst_sig σ sig, IMAGE (esubst σ []) axs)’]
                 mp_tac proves_axioms
  >> rw[theory_ok_esubst_axs]
  >> drule_at Any proves_INST
  >> disch_then $ qspec_then ‘MAP (λ(s',s). (esubst σ [] s', esubst_ty σ [] s)) ilist_r’ mp_tac
  >> impl_tac
  >- (rw[MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
      >> first_x_assum drule >> rw[] >> simp[]
      >> irule esubsts_ok_type_ok >> simp[] >> gvs[term_ok_def])
  >> rw[term_image_thm]
  >> drule_at Any proves_INST_TYPE
  >> disch_then $ qspec_then ‘MAP (λ(ty,a). (ty_esubst σ ty, a)) tyin’ mp_tac
  >> impl_tac
  >- (simp[EVERY_MAP, EVERY_MEM]
      >> rw[] >> Cases_on ‘x’ >> simp[]
      >> irule esubsts_ok_type_ok >> simp[EVERY_MEM]
      >> gvs[EVERY_MEM, MEM_MAP] >> first_x_assum irule
      >> metis_tac[EXISTS_PROD, FST])
  >> rw[term_image_thm]
  >> drule_at Any proves_INST
  >> disch_then $ qspec_then ‘MAP (λ(s',s). (esubst σ [] s', esubst_ty σ [] s)) ilist_f’ mp_tac
  >> impl_tac >> rw[]
  >- (gvs ilist_r_thms
      >> first_x_assum drule >> rw[] >> simp[]
      >> conj_tac >- (irule esubst_has_type1 >> simp[SF SFY_ss])
      >> irule esubst_term_ok >> simp[SF SFY_ss])
  >> irule proves_ACONV_concl >> first_x_assum $ irule_at Any >> rw[]
  >- (irule esubst_welltyped >> simp[SF SFY_ss])
  >> irule ACONV_TRANS
  >> qexists ‘esubst σ [] (VSUBST ilist_f (INST tyin (VSUBST ilist_r c)))’
  >> reverse conj_tac
  >- (irule esubst_ACONV >> simp[SF SFY_ss] >> irule ACONV_SYM >> simp[])
  >> irule ACONV_TRANS
  >> qexists ‘VSUBST (MAP (λ(s',s). (esubst σ [] s',esubst_ty σ [] s)) ilist_f)
              (esubst σ [] (INST tyin (VSUBST ilist_r c)))’
  >> reverse conj_tac
  >- (irule esubst_VSUBST_comm >> rw[]
      >- (irule unique_varnames_no_var_collapse
          >> irule unique_varnames_INST >> simp[term_ok_welltyped, SF SFY_ss])
      >> rw[] >> rpt $ first_x_assum $ irule_at Any >> rw[]
      >> first_x_assum drule >> rw[SF SFY_ss])
  >> irule ACONV_VSUBST >> rw[]
  >- (gvs[MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >> first_x_assum drule >> rw[]
      >> simp[esubst_ty_def] >> irule esubst_has_type1 >> metis_tac[])
  >- (irule INST_WELLTYPED >> irule VSUBST_WELLTYPED
      >> simp[MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
      >> rw[]
      >- (first_x_assum drule >> rw[] >> rw[esubst_ty_var, esubst_var])
      >> irule esubst_welltyped >> metis_tac[])
  >- (irule esubst_welltyped >> simp[SF SFY_ss])
  >> irule ACONV_TRANS
  >> qexists ‘INST (MAP (λ(ty,a). (ty_esubst σ ty,a)) tyin)
              (esubst σ [] (VSUBST ilist_r c))’
  >> rw[]
  >- (irule ACONV_INST >> rw[]
      >- (irule VSUBST_WELLTYPED >> simp[MEM_MAP, LAMBDA_PROD, EXISTS_PROD]
          >> rw[]
          >- (first_x_assum drule >> rw[] >> rw[esubst_ty_var, esubst_var])
          >> irule esubst_welltyped >> simp[SF SFY_ss])
      >- (irule esubst_welltyped >> simp[SF SFY_ss])
      >> irule esubst_VSUBST_comm >> rw[]
      >> rw[] >> qexistsl [‘axs’, ‘sig’] >> rw[] >> first_x_assum drule >> rw[])
  >> irule ACONV_SYM >> irule esubst_INST_comm >> simp[EVERY_MEM, SF SFY_ss]
  >> rpt $ first_x_assum $ irule_at Any >> rw[MEM_MAP] >> Cases_on ‘y’ >> gvs[EVERY_MEM]
  >> first_x_assum irule >> simp[MEM_MAP] >> metis_tac[FST]
QED

val term_ok_equation_imp1 = Q.prove(
  ‘is_std_sig s0 ⇒ term_ok s0 (a0 === b0) ⇒ term_ok s0 a0’,
  rw[term_ok_clauses])

val term_ok_Abs_intro = Q.prove(
  ‘type_ok (tysof s0) ty0 ∧ term_ok s0 bd0 ⇒ term_ok s0 (Abs (Var nm0 ty0) bd0)’,
  rw[term_ok_def])

val equation_comb_abs_arg_has_type = Q.prove(
  ‘is_std_sig s0 ∧ term_ok s0 (Comb (Abs (Var nm0 ty0) bd0) arg0 === rhs0) ⇒
   arg0 has_type ty0’,
  strip_tac >> gvs[term_ok_clauses] >> gvs[typeof_def] >> simp[Once (GSYM WELLTYPED)])

val blast_term_validation =
DEP_REWRITE_TAC[esubst_welltyped, VSUBST_WELLTYPED, INST_WELLTYPED, esubst_term_ok,
                apply_steps_welltyped, apply_steps_term_ok, term_ok_VSUBST]
>> simp[term_ok_def, apply_steps_term_ok, term_ok_welltyped, SF SFY_ss,
        welltyped_comb, welltyped_equation, EQUATION_HAS_TYPE_BOOL]

Theorem apply_steps_comb:
  ∀stps.
    term_ok sig x ∧ term_ok sig y ∧ steps_ok sig stps ⇒
    apply_steps stps (Comb x y) =
    Comb (apply_steps stps x) (apply_steps stps y)
Proof
  Induct >> simp[apply_steps_def] >> Cases >> rw[] >> gvs[apply_steps_def, steps_ok_def]
  >> simp[VSUBST_def, INST_COMB, apply_steps_welltyped, term_ok_welltyped, SF SFY_ss]
QED

Theorem apply_steps_Abs:
  ∀stps n0 ty0 abs_bd.
    steps_ok sig stps ⇒ welltyped abs_bd ⇒
    ∃n2 ty2 bd2. apply_steps stps (Abs (Var n0 ty0) abs_bd) = Abs (Var n2 ty2) bd2 ∧
                  welltyped bd2
Proof
  Induct >> rw[apply_steps_def]
  >> Cases_on ‘h’ >> rw[apply_steps_def] >> gvs[steps_ok_def]
  (* VStep case *)
  >- (first_x_assum (qspecl_then [‘n0’, ‘ty0’, ‘abs_bd’] mp_tac) >> simp[]
      >> strip_tac >> gvs[]
      >> simp[VSUBST_def, LET_THM] >> rw[]
      >> irule VSUBST_WELLTYPED >> simp[MEM_FILTER, has_type_var]
      >> rpt strip_tac >> gvs[MEM_FILTER] >> res_tac >> simp[])
  (* TStep case *)
  >> first_x_assum (qspecl_then [‘n0’, ‘ty0’, ‘abs_bd’] mp_tac) >> simp[]
  >> strip_tac >> gvs[]
  >> ‘welltyped (Abs (Var n2 ty2) bd2)’ by simp[WELLTYPED_CLAUSES]
  >> drule_then (qspec_then ‘l’ mp_tac) INST_dbINST
  >> simp[db_def, dbINST_def] >> strip_tac
  >> ‘welltyped (INST l (Abs (Var n2 ty2) bd2))’
      by (irule INST_WELLTYPED >> simp[])
  >> Cases_on ‘INST l (Abs (Var n2 ty2) bd2)’ >> gvs[db_def]
  >> gvs[WELLTYPED_CLAUSES]
  >> metis_tac[]
QED

Theorem REV_ASSOCD_default_eq:
  ∀l x d1 d2. (∃v. MEM (v,x) l) ⇒ REV_ASSOCD x l d1 = REV_ASSOCD x l d2
Proof
  Induct >> simp[REV_ASSOCD, FORALL_PROD] >> rw[]
QED

Theorem VSUBST_Abs_beta_ACONV:
  welltyped bd ∧ welltyped v ∧ v has_type ty ∧
  (∀s s'. MEM (s',s) l ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ welltyped s') ∧
  VSUBST l (Abs (Var n ty) bd) = Abs (Var n' ty') bd' ⇒
  ACONV (VSUBST [(VSUBST l v, Var n' ty')] bd')
        (VSUBST l (VSUBST [(v, Var n ty)] bd))
Proof
  rpt strip_tac
  >> ‘∀k v'. MEM (v',k) l ⇒ welltyped v' ∧ (∃a b. k = Var a b)’
       by (rw[] >> res_tac >> gvs[])
  >> ‘VSUBST l v has_type ty’ by (irule VSUBST_HAS_TYPE >> metis_tac[])
  >> ‘welltyped (VSUBST l v)’ by metis_tac[welltyped_def]
  >> qabbrev_tac ‘l' = FILTER (λ(s',s). s ≠ Var n ty) l’
  >> ‘∀s1 s2. MEM (s1,s2) l' ⇒ ∃a b. s2 = Var a b ∧ s1 has_type b’
       by (rw[Abbr‘l'’, MEM_FILTER] >> res_tac >> gvs[])
  >> ‘∀k v'. MEM (v',k) l' ⇒ welltyped v' ∧ (∃a b. k = Var a b)’
       by (rw[Abbr‘l'’, MEM_FILTER] >> res_tac >> gvs[])
  >> ‘welltyped (VSUBST l' bd)’
       by (irule VSUBST_WELLTYPED >> metis_tac[])
  (* Case split on VSUBST Abs capture condition *)
  >> qpat_x_assum ‘VSUBST l (Abs _ _) = _’ mp_tac
  >> simp[Once VSUBST_def, Abbr‘l'’]
  >> qabbrev_tac ‘l' = FILTER (λ(s',s). s ≠ Var n ty) l’
  >> reverse IF_CASES_TAC >> strip_tac >> gvs[]
  (* ---- No capture case: n' = n, bd' = VSUBST l' bd ---- *)
  >- (
    ‘welltyped (VSUBST [(v, Var n ty)] bd)’ by (
      irule VSUBST_WELLTYPED >> rw[has_type_rules] >> metis_tac[WELLTYPED])
    >> ‘welltyped (VSUBST l (VSUBST [(v, Var n ty)] bd))’ by (
         irule VSUBST_WELLTYPED >> metis_tac[])
    >> irule $ iffRL ACONV_db >> rw[]
    >- (irule VSUBST_WELLTYPED >> simp[])
    >> rw[VSUBST_dbVSUBST, SF SFY_ss]
    >> ‘¬MEM (dbVar n ty)
            (MAP SND (MAP (λ(p,q). (db p, db q)) l'))’
         by (simp[MEM_MAP, EXISTS_PROD, FORALL_PROD]
             >> rpt strip_tac >> res_tac
             >> gvs[db_def, Abbr‘l'’, MEM_FILTER])
    >> rw[Once dbVSUBST_comp, MAP_db_FILTER_neq]
    >> rw[Once dbVSUBST_comp]
    >> irule dbVSUBST_frees
    >> gen_tac >> strip_tac
    >> Cases_on ‘k = dbVar n ty’
    >- (
      simp[REV_ASSOCD_APPEND, REV_ASSOCD_def, REV_ASSOCD_MAP,
           MEM_MAP, EXISTS_PROD, FORALL_PROD]
      >> IF_CASES_TAC >> gvs[]
      >> res_tac >> gvs[Abbr‘l'’, MEM_FILTER])
    >> simp[REV_ASSOCD_APPEND, REV_ASSOCD_def, REV_ASSOCD_MAP,
            MEM_MAP, MEM_FILTER, EXISTS_PROD, FORALL_PROD]
    >> IF_CASES_TAC >> gvs[]
    >- (
      ‘∃x'' ty''. p_2 = Var x'' ty''’ by metis_tac[]
      >> gvs[]
      >> qspecl_then [‘l'’, ‘x''’, ‘ty''’] mp_tac REV_ASSOCD_MAP_db
      >> impl_tac >- metis_tac[]
      >> strip_tac >> gvs[]
      >> ‘VFREE_IN (Var x'' ty'') bd’ by (
           irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[db_def])
      >> qspecl_then [‘l'’, ‘Var x'' ty''’, ‘Var x'' ty''’]
           strip_assume_tac REV_ASSOCD_MEM
      >- (
        ‘welltyped (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty''))’ by (
          first_x_assum drule >> gvs[])
        >> ‘¬VFREE_IN (Var n ty) (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty''))’ by (
          qpat_x_assum ‘EVERY _ _’ mp_tac
          >> rewrite_tac[EVERY_MEM]
          >> disch_then $ qspec_then
               ‘(REV_ASSOCD (Var x'' ty'') l' (Var x'' ty''), Var x'' ty'')’ mp_tac
          >> simp[])
        >> ‘¬dbVFREE_IN (dbVar n ty)
                (db (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty'')))’ by (
             ONCE_REWRITE_TAC[GSYM db_def] >> simp[dbVFREE_IN_VFREE_IN])
        (* dbVSUBST is identity since dbVar n ty not free *)
        >> ‘dbVSUBST [(dbVSUBST (MAP (λ(x,y). (db x,db y)) l) (db v), dbVar n ty)]
              (db (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty'')))
            = db (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty''))’ by (
          CONV_TAC (RHS_CONV (REWR_CONV (GSYM dbVSUBST_nil)))
          >> irule dbVSUBST_frees >> simp[REV_ASSOCD]
          >> rpt strip_tac >> IF_CASES_TAC >> gvs[])
        >> gvs[MAP_db_FILTER_neq, Abbr‘l'’])
      >> gvs[REV_ASSOCD, MAP_db_FILTER_neq, Abbr‘l'’]
      >> IF_CASES_TAC >> gvs[])
    >> qspecl_then [‘MAP (λ(p,q). (db p,db q)) l'’, ‘k’, ‘k’]
         strip_assume_tac REV_ASSOCD_MEM
    >- (gvs[MEM_MAP, FORALL_PROD, EXISTS_PROD] >> res_tac)
    >> simp[REV_ASSOCD_FILTER]
    >> gvs[MAP_db_FILTER_neq, REV_ASSOCD_FILTER, Abbr‘l'’])
  (* ---- Capture case ---- *)
  >> qabbrev_tac ‘z = VARIANT (VSUBST l' bd) (explode n) ty’
  >> ‘¬VFREE_IN (Var z ty) (VSUBST l' bd)’ by simp[Abbr‘z’, VARIANT_THM]
  >> ‘∀k v'. MEM (v',k) ((Var z ty, Var n ty) :: l') ⇒
             welltyped v' ∧ (∃a b. k = Var a b)’ by (
       rw[] >> res_tac >> gvs[])
  >> ‘welltyped (VSUBST ((Var z ty, Var n ty) :: l') bd)’ by (
       irule VSUBST_WELLTYPED >> rw[] >> res_tac >> gvs[])
  >> ‘welltyped (VSUBST [(v, Var n ty)] bd)’ by (
       irule VSUBST_WELLTYPED >> rw[] >> gvs[])
  >> ‘welltyped (VSUBST l (VSUBST [(v, Var n ty)] bd))’ by (
       irule VSUBST_WELLTYPED >> rw[] >> res_tac >> gvs[])
  >> irule $ iffRL ACONV_db >> rw[]
  >- (irule VSUBST_WELLTYPED >> rw[] >> gvs[])
  >> rw[VSUBST_dbVSUBST, SF SFY_ss]
  >> ONCE_REWRITE_TAC[dbVSUBST_comp]
  >> simp[MAP_db_FILTER_neq]
  >> irule dbVSUBST_frees
  >> gen_tac >> strip_tac
  >> Cases_on ‘k = dbVar n ty’
  >- (
    simp[REV_ASSOCD_APPEND, REV_ASSOCD_def, REV_ASSOCD_MAP,
         MEM_MAP, EXISTS_PROD, FORALL_PROD]
    >> IF_CASES_TAC >> gvs[]
    >> res_tac >> gvs[Abbr‘l'’, MEM_FILTER])
  >> simp[REV_ASSOCD_APPEND, REV_ASSOCD_def, REV_ASSOCD_MAP,
          MEM_MAP, MEM_FILTER, EXISTS_PROD, FORALL_PROD]
  >> IF_CASES_TAC >> gvs[]
  >- (
    ‘∃x'' ty''. p_2 = Var x'' ty''’ by metis_tac[]
    >> gvs[]
    >> qspecl_then [‘l'’, ‘x''’, ‘ty''’] mp_tac REV_ASSOCD_MAP_db
    >> impl_tac >- metis_tac[]
    >> strip_tac >> gvs[]
    >> ‘VFREE_IN (Var x'' ty'') bd’ by (
         irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[db_def])
    >> ‘¬VFREE_IN (Var z ty) (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty''))’ by (
         qpat_x_assum ‘¬VFREE_IN (Var z ty) (VSUBST l' bd)’ mp_tac
         >> rw[VFREE_IN_VSUBST] >> metis_tac[])
    >> ‘welltyped (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty''))’ by (
      qspecl_then [‘l'’, ‘Var x'' ty''’, ‘Var x'' ty''’]
        strip_assume_tac REV_ASSOCD_MEM
      >- (first_x_assum drule >> gvs[])
      >> gvs[WELLTYPED_CLAUSES])
    >> ‘¬dbVFREE_IN (dbVar z ty)
            (db (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty'')))’ by
         metis_tac[dbVFREE_IN_VFREE_IN, db_def]
    >> ‘∀d. REV_ASSOCD (dbVar x'' ty'') (MAP (λ(x,y). (db x,db y)) l') d
          = db (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty''))’ by (
      gen_tac
      >> ‘REV_ASSOCD (dbVar x'' ty'') (MAP (λ(x,y). (db x,db y)) l') d
          = REV_ASSOCD (dbVar x'' ty'') (MAP (λ(x,y). (db x,db y)) l')
              (dbVar x'' ty'')’ by (
        irule REV_ASSOCD_default_eq
        >> qexists_tac ‘db p_1’
        >> simp[MEM_MAP, EXISTS_PROD]
        >> metis_tac[db_def])
      >> simp[])
    >> ‘dbVSUBST [(dbVSUBST (MAP (λ(x,y). (db x,db y)) l) (db v), dbVar z ty)]
          (db (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty'')))
        = db (REV_ASSOCD (Var x'' ty'') l' (Var x'' ty''))’ by (
      CONV_TAC (RHS_CONV (REWR_CONV (GSYM dbVSUBST_nil)))
      >> irule dbVSUBST_frees >> simp[REV_ASSOCD]
      >> rpt strip_tac >> IF_CASES_TAC >> gvs[])
    >> gvs[MAP_db_FILTER_neq, Abbr‘l'’])
  >> qspecl_then [‘MAP (λ(p,q). (db p,db q)) l'’, ‘k’, ‘k’]
       strip_assume_tac REV_ASSOCD_MEM
  >- (gvs[MEM_MAP, FORALL_PROD, EXISTS_PROD] >> res_tac)
  >> IF_CASES_TAC
  >> gvs[REV_ASSOCD, REV_ASSOCD_FILTER, MAP_db_FILTER_neq, Abbr‘l'’]
  >> IF_CASES_TAC >> gvs[]
  >> ‘VFREE_IN (Var z ty) bd’ by (
    irule $ iffLR dbVFREE_IN_VFREE_IN >> simp[db_def])
  >> ‘VFREE_IN (Var z ty) (VSUBST (FILTER (λ(s',s). s ≠ Var n ty) l) bd)’ by (
    irule (GEN_ALL (DISCH_ALL (iffRL (UNDISCH (SPEC_ALL VFREE_IN_VSUBST)))))
    >> simp[]
    >> qexistsl_tac [‘z’, ‘ty’] >> simp[VFREE_IN_def]
    >> qspecl_then [‘FILTER (λ(s',s). s ≠ Var n ty) l’, ‘Var z ty’, ‘Var z ty’]
        strip_assume_tac REV_ASSOCD_MEM
    >- metis_tac[db_def]
    >> gvs[VFREE_IN_def])
QED

Definition db_ok_def[simp]:
  db_ok k (dbVar x ty) = T ∧
  db_ok k (dbBound m) = (m < k) ∧
  db_ok k (dbConst x ty) = T ∧
  db_ok k (dbComb t1 t2) = (db_ok k t1 ∧ db_ok k t2) ∧
  db_ok k (dbAbs ty t) = db_ok (k+1) t
End

Definition unbind_def[simp]:
  unbind val k (dbVar x ty) = dbVar x ty ∧
  unbind val k (dbBound m) = (if m = k then val else dbBound m) ∧
  unbind val k (dbConst x ty) = dbConst x ty ∧
  unbind val k (dbComb t1 t2) = dbComb (unbind val k t1) (unbind val k t2) ∧
  unbind val k (dbAbs ty t) = dbAbs ty (unbind val (k+1) t)
End

Theorem db_ok_bind:
  ∀dbt v k. db_ok k dbt ⇒ db_ok (k+1) (bind v k dbt)
Proof
  Induct >> simp[] >> rw[]
QED

Theorem db_ok_db:
  ∀tm. db_ok 0 (db tm)
Proof
  Induct >> simp[]
  >> pop_assum (assume_tac o MATCH_MP db_ok_bind) >> gvs[]
QED

Theorem unbind_bind:
  ∀dbt val x ty k. db_ok k dbt ⇒
    unbind val k (bind (x,ty) k dbt) = dbVSUBST [(val, dbVar x ty)] dbt
Proof
  Induct >> simp[REV_ASSOCD] >> rw[]
QED

Theorem unbind_dbINST:
  ∀dbt val k tyin.
    unbind (dbINST tyin val) k (dbINST tyin dbt) = dbINST tyin (unbind val k dbt)
Proof
  Induct >> simp[] >> rw[]
QED

Theorem unbind_bind_0:
  ∀dbt val x ty. db_ok 0 dbt ⇒
    dbVSUBST [(val, dbVar x ty)] dbt = unbind val 0 (bind (x,ty) 0 dbt)
Proof
  rpt strip_tac >> irule (GSYM unbind_bind) >> simp[]
QED

Theorem INST_Abs_beta_ACONV:
  welltyped bd ∧ welltyped v ∧ v has_type ty ∧
  INST tyin (Abs (Var n ty) bd) = Abs (Var n' ty') bd' ⇒
  ACONV (VSUBST [(INST tyin v, Var n' ty')] bd')
        (INST tyin (VSUBST [(v, Var n ty)] bd))
Proof
  rpt strip_tac
  >> ‘welltyped (Abs (Var n ty) bd)’ by simp[WELLTYPED_CLAUSES]
  >> ‘welltyped (Abs (Var n' ty') bd')’ by metis_tac[INST_WELLTYPED]
  >> ‘welltyped bd'’ by gvs[WELLTYPED_CLAUSES]
  >> ‘ty' = TYPE_SUBST tyin ty’ by (
       ‘db (INST tyin (Abs (Var n ty) bd)) = db (Abs (Var n' ty') bd')’ by simp[]
       >> pop_assum mp_tac >> DEP_REWRITE_TAC[INST_dbINST] >> simp[])
  >> ‘INST tyin v has_type ty'’ by (irule INST_HAS_TYPE >> metis_tac[])
  >> irule $ iffRL ACONV_db >> rpt conj_tac
  >- (irule VSUBST_WELLTYPED >> simp[] >> metis_tac[])
  >- (irule INST_WELLTYPED >> irule VSUBST_WELLTYPED
      >> simp[] >> metis_tac[WELLTYPED])
  >> ‘db (INST tyin (Abs (Var n ty) bd)) = db (Abs (Var n' ty') bd')’ by simp[]
  >> pop_assum mp_tac >> DEP_REWRITE_TAC[INST_dbINST] >> simp[]
  >> strip_tac
  >> ‘welltyped (VSUBST [(v, Var n ty)] bd)’ by
       (irule VSUBST_WELLTYPED >> simp[] >> metis_tac[WELLTYPED])
  >> DEP_REWRITE_TAC[VSUBST_dbVSUBST, INST_dbINST]
  >> simp[INST_WELLTYPED, welltyped_def]
  >> conj_tac >- metis_tac[WELLTYPED]
  >> strip_tac
  >> simp[INST_dbINST]
  >> DEP_REWRITE_TAC[unbind_bind_0]
  >> simp[db_ok_db, GSYM unbind_dbINST]
QED

fun drw thms = DEP_REWRITE_TAC thms >> simp[]

Theorem apply_steps_Abs_has_type:
  ∀stps x x1 ty ty1 t t1.
    steps_ok sig stps ∧ term_ok sig (Abs (Var x ty) t) ∧
    apply_steps stps (Abs (Var x ty) t) = Abs (Var x1 ty1) t1 ⇒
    apply_steps stps (Var x ty) has_type ty1
Proof
  Induct >> simp[apply_steps_def] >> Cases
  >> rw[steps_ok_def, apply_steps_def]
  >> ‘welltyped t’ by metis_tac[term_ok_welltyped, WELLTYPED_CLAUSES]
  >> drule_all apply_steps_Abs
  >> disch_then $ qspecl_then [‘x’, ‘ty’] strip_assume_tac >> gvs[]
  >- (‘ty2 = ty1’ by (
        qpat_x_assum ‘VSUBST _ _ = _’ mp_tac
        >> simp[VSUBST_def, LET_THM] >> rw[])
      >> gvs[]
      >> metis_tac[VSUBST_HAS_TYPE])
  >> ‘welltyped (Abs (Var n2 ty2) bd2)’ by simp[]
  >> drule INST_dbINST >> disch_then (qspec_then ‘l’ assume_tac)
  >> ‘ty1 = TYPE_SUBST l ty2’ by gvs[]
  >> gvs[]
  >> metis_tac[INST_HAS_TYPE]
QED

Theorem apply_steps_Abs_beta:
  ∀stps x ty t n2 ty2 bd2.
    term_ok sig (Abs (Var x ty) t) ∧ steps_ok sig stps ∧
    apply_steps stps (Abs (Var x ty) t) = Abs (Var n2 ty2) bd2 ⇒
    ACONV (VSUBST [(apply_steps stps (Var x ty), Var n2 ty2)] bd2)
          (apply_steps stps t)
Proof
  Induct >> simp[apply_steps_def]
  >- (rw[] >> irule $ iffRL ACONV_db >> rw[]
      >> blast_term_validation >> drw[VSUBST_ID])
  >> Cases >> rw[apply_steps_def] >> gvs[steps_ok_def]
  >> imp_res_tac term_ok_welltyped >> drule_all apply_steps_Abs
  >> disch_then $ qspecl_then [‘x’, ‘ty’] mp_tac >> rw[] >> gvs[]
  >> irule ACONV_TRANS
  >- (irule_at Any VSUBST_Abs_beta_ACONV
      >> first_x_assum $ irule_at (Pat ‘VSUBST l _ = Abs _ _’)
      >> blast_term_validation >> rw[]
      >- (irule apply_steps_Abs_has_type >> metis_tac[term_ok_def])
      >- (first_x_assum drule >> metis_tac[term_ok_welltyped])
      >> irule ACONV_VSUBST >> blast_term_validation >> rw[]
      >- (irule apply_steps_Abs_has_type >> metis_tac[term_ok_def])
      >> metis_tac[])
  >> irule_at Any INST_Abs_beta_ACONV
  >> first_x_assum $ irule_at (Pat ‘INST l _ = Abs _ _’)
  >> blast_term_validation >> rw[]
  >- (irule apply_steps_Abs_has_type >> metis_tac[term_ok_def])
  >> irule ACONV_INST >> blast_term_validation
  >> irule apply_steps_Abs_has_type >> metis_tac[term_ok_def]
QED

Triviality db_esubst_dbAbs[local]:
  db_esubst σ (dbAbs ty body) = dbAbs (ty_esubst σ ty) (db_esubst σ body)
Proof
  REWRITE_TAC[db_esubst_def, db_esubst_ty_def, db_esubst_tm_def]
QED

Triviality unbind_db_esubst_ty[local]:
  ∀dbt val k. unbind (db_esubst_ty σ val) k (db_esubst_ty σ dbt) =
              db_esubst_ty σ (unbind val k dbt)
Proof
  Induct >> simp[db_esubst_ty_def] >> rw[db_esubst_ty_def]
QED

Triviality unbind_db_esubst_tm[local]:
  ∀dbt val k. only_esubsts_consts (SND σ) ⇒
              unbind (db_esubst_tm σ val) k (db_esubst_tm σ dbt) =
              db_esubst_tm σ (unbind val k dbt)
Proof
  Induct >> simp[db_esubst_tm_def] >> rw[db_esubst_tm_def]
  >> CASE_TAC >> simp[] >> Cases_on ‘σ’
  >> gvs[only_esubsts_consts_def, IN_FRANGE_FLOOKUP]
  >> qpat_x_assum ‘∀tm. _ ⇒ _’ mp_tac
  >> disch_then $ qspec_then ‘x’ mp_tac
  >> simp[SF SFY_ss] >> rw[] >> simp[db_def]
QED

Triviality unbind_db_esubst[local]:
  ∀dbt val k. only_esubsts_consts (SND σ) ⇒
              unbind (db_esubst σ val) k (db_esubst σ dbt) =
              db_esubst σ (unbind val k dbt)
Proof
  simp[db_esubst_def] >> rpt strip_tac
  >> DEP_REWRITE_TAC[unbind_db_esubst_tm]
  >> simp[unbind_db_esubst_ty]
QED

Theorem esubst_Abs_beta_ACONV:
  term_ok sig (Abs (Var n ty) bd) ∧
  theory_ok (sig,axs) ∧ esubsts_ok sig σ ∧
  term_ok sig v ∧ v has_type ty ∧
  esubst σ avds (Abs (Var n ty) bd) = Abs (Var n' (ty_esubst σ ty)) bd' ⇒
  ACONV (VSUBST [(esubst σ [] v, Var n' (ty_esubst σ ty))] bd')
        (esubst σ [] (VSUBST [(v, Var n ty)] bd))
Proof
  rpt strip_tac
  >> ‘welltyped (Abs (Var n ty) bd)’ by metis_tac[term_ok_welltyped]
  >> ‘welltyped (Abs (Var n' (ty_esubst σ ty)) bd')’ by metis_tac[esubst_welltyped]
  >> ‘welltyped bd'’ by gvs[WELLTYPED_CLAUSES]
  >> ‘esubst σ [] v has_type ty_esubst σ ty’ by (
       irule esubst_has_type1 >> metis_tac[])
  >> irule $ iffRL ACONV_db >> rpt conj_tac
  >> blast_term_validation >> fs[term_ok_def]
  >> ‘db (esubst σ avds (Abs (Var n ty) bd)) =
      db (Abs (Var n' (ty_esubst σ ty)) bd')’ by simp[]
  >> pop_assum mp_tac
  >> drw[db_esubst_thm] >> rw[db_esubst_dbAbs]
  >- (irule term_ok_VSUBST >> fs[term_ok_def])
  >> ‘welltyped (VSUBST [(v, Var n ty)] bd)’ by (
       irule VSUBST_WELLTYPED >> simp[] >> gvs[WELLTYPED_CLAUSES] >> metis_tac[WELLTYPED])
  >> drw[VSUBST_dbVSUBST, db_esubst_thm]
  >> simp[SF SFY_ss] >> blast_term_validation >> fs[term_ok_welltyped, term_ok_def]
  >> drw[unbind_bind_0] >> simp[db_ok_db]
  >> drw[db_esubst_thm, GSYM unbind_db_esubst]
  >> metis_tac[esubsts_ok_only_esubsts_consts]
QED

Theorem esubst_apply_steps_Abs:
  ∀stps.
    term_ok sig t ∧
    theory_ok (sig,axs) ∧ esubsts_ok sig σ ∧
    type_ok (tysof sig) ty ∧ steps_ok sig stps ⇒
    ∃z ty' body.
      esubst σ avds (apply_steps stps (Abs (Var x ty) t)) = Abs (Var z ty') body ∧
      term_ok (esubst_sig σ sig) body ∧
      type_ok (tysof (esubst_sig σ sig)) ty' ∧
      esubst σ [] (apply_steps stps (Var x ty)) has_type ty' ∧
      ACONV (VSUBST [(esubst σ [] (apply_steps stps (Var x ty)), Var z ty')] body)
            (esubst σ [] (apply_steps stps t))
Proof
  rpt strip_tac
  >> ‘welltyped t’ by metis_tac[term_ok_welltyped]
  >> ‘term_ok sig (Abs (Var x ty) t)’ by simp[term_ok_def]
  >> drule_all apply_steps_Abs
  >> disch_then $ qspecl_then [‘x’, ‘ty’] strip_assume_tac
  >> ‘term_ok sig (Abs (Var n2 ty2) bd2)’ by (
       qpat_x_assum ‘apply_steps _ _ = _’ (SUBST1_TAC o SYM)
       >> irule apply_steps_term_ok >> simp[term_ok_def])
  >> ‘term_ok sig (apply_steps stps (Var x ty))’ by (
       irule apply_steps_term_ok >> simp[term_ok_def])
  >> drule_all apply_steps_Abs_has_type >> strip_tac
  >> qpat_x_assum ‘term_ok _ (Abs (Var x _) _)’ kall_tac
  >> drule_all simple_esubst_Abs
  >> disch_then $ qspec_then ‘avds’ mp_tac >> simp[] >> strip_tac
  >> qexistsl [‘y’, ‘ty_esubst σ ty2’, ‘body’]
  >> fs[tysof_esubst_sig]
  >> rpt conj_tac
  >- (irule ty_esubst_type_ok_alt >> gvs[term_ok_def])
  >- (irule esubst_has_type1 >> simp[SF SFY_ss])
  >- (irule ACONV_TRANS
      >> qexists_tac ‘esubst σ [] (VSUBST [(apply_steps stps (Var x ty), Var n2 ty2)] bd2)’
      >> conj_tac
      >- (irule esubst_Abs_beta_ACONV >> simp[SF SFY_ss])
      >> irule esubst_ACONV >> simp[SF SFY_ss]
      >> conj_tac
      >- (irule apply_steps_Abs_beta >> simp[SF SFY_ss, term_ok_def])
      >> rpt $ first_x_assum $ irule_at (Pos hd)
      >> simp[apply_steps_term_ok, term_ok_VSUBST])
  >- (irule ty_esubst_type_ok_alt >> gvs[term_ok_def])
  >- (irule esubst_has_type1 >> simp[SF SFY_ss])
  >> (irule ACONV_TRANS
      >> qexists_tac ‘esubst σ [] (VSUBST [(apply_steps stps (Var x ty), Var n2 ty2)] bd2)’
      >> conj_tac
      >- (irule esubst_Abs_beta_ACONV >> simp[SF SFY_ss])
      >> irule esubst_ACONV >> simp[SF SFY_ss]
      >> conj_tac
      >- (irule apply_steps_Abs_beta >> simp[SF SFY_ss, term_ok_def])
      >> rpt $ first_x_assum $ irule_at (Pos hd)
      >> simp[apply_steps_term_ok, term_ok_VSUBST])
QED

Theorem proves_substitutable_aux:
  ∀sig axs h c.
     theory_ok (sig,axs) ∧
     ((sig, axs), h) |- c ⇒
     ∀σ steps.
       (∀ax. ax ∈ axs ⇒ no_var_collapse σ ax) ∧
       esubsts_ok sig σ ∧
       steps_ok sig steps ⇒
       ((esubst_sig σ sig, IMAGE (esubst σ []) axs),
        term_image (esubst σ []) (term_image (apply_steps steps) h))
       |- esubst σ (FLAT (MAP tm_names h)) (apply_steps steps c)
Proof
  Induct_on ‘$|-’
  >> rw[] >> gvs[]
  >- suspend "Abs"
  >- suspend "Assume"
  >- suspend "Beta"
  >- suspend "DeductAntisym"
  >- suspend "EQ_MP"
  >- suspend "INST"
  >- suspend "INST_TYPE"
  >- suspend "MK_COMB"
  >- suspend "Refl"
  >- suspend "Axioms"
QED

Theorem proves_esubst_avds:
  ∀thy h σ avds1 avds2 c.
    theory_ok (sig, axs) ∧
    esubsts_ok sig σ ∧
    term_ok sig c ∧
    ((sig, axs), h) |- esubst σ avds1 c ⇒
    ((sig, axs), h) |- esubst σ avds2 c
Proof
  rw[] >> irule proves_ACONV >> drule proves_term_ok >> rw[]
  >- (irule esubst_welltyped >> gvs[EVERY_MEM, SF SFY_ss])
  >> qexistsl [‘esubst σ avds1 c’, ‘h’] >> rw[]
  >- (irule ACONV_esubst_avds >> metis_tac[term_ok_welltyped])
  >> rw[EVERY_MEM, EXISTS_MEM] >> metis_tac[ACONV_REFL]
QED

(* Helper: bind/unbind round-trip for fresh variables *)
Theorem bind_unbind_fresh:
  ∀dbt z ty k.
    ¬dbVFREE_IN (dbVar z ty) dbt ⇒
    bind (z, ty) k (unbind (dbVar z ty) k dbt) = dbt
Proof
  Induct >> simp[bind_def, dbVFREE_IN_def] >> rw[]
QED

(* Helper: dbINST commutes with bind when z has unique type *)
Theorem dbINST_bind_commute:
  ∀dbt z ty k tyin.
    (∀ty'. dbVFREE_IN (dbVar z ty') dbt ⇒ ty' = ty) ⇒
    dbINST tyin (bind (z, ty) k dbt) =
    bind (z, TYPE_SUBST tyin ty) k (dbINST tyin dbt)
Proof
  Induct >> simp[bind_def, dbINST_def, dbVFREE_IN_def]
  >> rpt strip_tac >> Cases_on ‘z = m’ >> gvs[dbINST_def]
QED

Theorem dbVFREE_IN_dbINST:
  ∀dbt z ty' tyin.
    dbVFREE_IN (dbVar z ty') (dbINST tyin dbt) ⇔
    ∃oty. dbVFREE_IN (dbVar z oty) dbt ∧ ty' = TYPE_SUBST tyin oty
Proof
  Induct >> rw[dbINST_def] >> metis_tac[]
QED

(* Alpha-equivalence for apply_steps on Abs:
   apply_steps stps (Abs (Var x ty) t) is ACONV to
   Abs (Var z ty2) (apply_steps stps (t[z/x])) for fresh z.
   Proof by induction on stps:
   - Base: ACONV_db + bind_unbind_fresh
   - VStep: ACONV_VSUBST + z not captured (z fresh for ilist names)
   - TStep: ACONV_INST + dbINST_bind_commute *)
Theorem apply_steps_Abs_alpha:
  ∀stps x ty t z.
    term_ok sig t ∧ steps_ok sig stps ∧
    ¬MEM z (tm_names (Abs (Var x ty) t)) ∧
    type_ok (tysof sig) ty ∧
    EVERY (λstep. case step of
        VStep ilist => EVERY (λ(s',s). ¬MEM z (tm_names s' ++ tm_names s)) ilist
      | TStep _ => T) stps ⇒
    ∃ty2.
      ACONV (apply_steps stps (Abs (Var x ty) t))
            (Abs (Var z ty2) (apply_steps stps (VSUBST [(Var z ty, Var x ty)] t))) ∧
      welltyped (apply_steps stps (VSUBST [(Var z ty, Var x ty)] t)) ∧
      (∀ty'. VFREE_IN (Var z ty')
                      (apply_steps stps (VSUBST [(Var z ty, Var x ty)] t)) ⇒
             ty' = ty2)
Proof
  Induct >> rw[apply_steps_def, steps_ok_def]
  >- (qexists_tac ‘ty’ >> rpt strip_tac
      >- (irule replace_binder_ACONV
          >> rpt strip_tac >> imp_res_tac VFREE_IN_tm_names
          >> simp[SF SFY_ss, term_ok_def])
      >- blast_term_validation
      >> imp_res_tac term_ok_welltyped
      >> drule_then (qspecl_then [‘z’, ‘ty'’, ‘[(Var z ty,Var x ty)]’] mp_tac)
                    VFREE_IN_VSUBST
      >> rw[] >> gvs[REV_ASSOCD, VFREE_IN_def]
      >> every_case_tac >> fs[]
      >> imp_res_tac VFREE_IN_tm_names)
  >> Cases_on ‘h’ >> gvs[apply_steps_def, steps_ok_def]
  >- suspend "vstep_case"
  >> suspend "tstep_case"
QED

Resume apply_steps_Abs_alpha[vstep_case]:
  rename1 ‘VSUBST ilist’
  >> first_x_assum $ qspecl_then [‘x’, ‘ty’, ‘t’, ‘z’] mp_tac
  >> simp[] >> strip_tac
  >> qexists_tac ‘ty2’ >> rpt conj_tac
  (* ACONV *)
  >- suspend "vstep_aconv"
  (* welltyped *)
  >- (irule VSUBST_WELLTYPED >> simp[]
      >> metis_tac[welltyped_def, term_ok_welltyped])
  (* unique type *)
  >> rpt strip_tac
  >> rename1 ‘VFREE_IN (Var z tty) (VSUBST ilist _)’
  >> drule_then (qspecl_then [‘z’, ‘tty’, ‘ilist’] mp_tac)
                VFREE_IN_VSUBST
  >> simp[] >> strip_tac
  >> rename1 ‘VFREE_IN (Var yy tyy) _’
  >> Cases_on ‘yy = z’
  >- (
  gvs[]
  >> qspecl_then [‘ilist’, ‘Var y ty'’, ‘Var y ty'’]
                 strip_assume_tac REV_ASSOCD_MEM
  >- (gvs[EVERY_MEM, FORALL_PROD] >> res_tac
      >> metis_tac[VFREE_IN_tm_names])
  >> gvs[VFREE_IN_def] >> metis_tac[])
  >> qspecl_then [‘ilist’, ‘Var y ty'’, ‘Var y ty'’]
                 strip_assume_tac REV_ASSOCD_MEM
  >- (gvs[EVERY_MEM, FORALL_PROD] >> res_tac
      >> metis_tac[VFREE_IN_tm_names])
  >> gvs[VFREE_IN_def] >> metis_tac[]
QED

Resume apply_steps_Abs_alpha[vstep_aconv]:
  irule ACONV_TRANS
  >> qexists_tac ‘VSUBST ilist (Abs (Var z ty2)
       (apply_steps stps (VSUBST [(Var z ty,Var x ty)] t)))’
  >> conj_tac
  >- (irule ACONV_VSUBST >> simp[WELLTYPED_CLAUSES]
      >> conj_tac >- metis_tac[]
      >> irule apply_steps_welltyped
      >> simp[WELLTYPED_CLAUSES, term_ok_welltyped, SF SFY_ss])
  >> qabbrev_tac ‘body = apply_steps stps (VSUBST [(Var z ty,Var x ty)] t)’
  >> ‘EVERY (λ(s',s). s ≠ Var z ty2) ilist’ by (
       gvs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac
       >> CCONTR_TAC >> gvs[]
       >> res_tac >> gvs[tm_names_def, MEM])
  >> ‘¬EXISTS (λ(s',s). VFREE_IN (Var z ty2) s' ∧ VFREE_IN s body) ilist’ by (
       simp[EXISTS_MEM, FORALL_PROD] >> gvs[EVERY_MEM, FORALL_PROD]
       >> rpt strip_tac >> res_tac >> gvs[tm_names_def, MEM]
       >> metis_tac[VFREE_IN_tm_names])
  >> ‘FILTER (λ(s',s). s ≠ Var z ty2) ilist = ilist’ by (
       irule $ iffRL FILTER_EQ_ID >> simp[])
  >> simp[Once $ last (CONJUNCTS VSUBST_def), ACONV_REFL]
QED

Resume apply_steps_Abs_alpha[tstep_case]:
  rename1 ‘INST tyin’
  >> first_x_assum $ qspecl_then [‘x’, ‘ty’, ‘t’, ‘z’] mp_tac
  >> simp[] >> strip_tac
  >> qexists_tac ‘TYPE_SUBST tyin ty2’ >> rpt conj_tac
  >> qabbrev_tac ‘body = apply_steps stps (VSUBST [(Var z ty,Var x ty)] t)’
  (* ACONV *)
  >- (
  irule ACONV_TRANS
  >> qexists_tac ‘INST tyin (Abs (Var z ty2) body)’
  >> conj_tac
  >- (irule ACONV_INST >> simp[WELLTYPED_CLAUSES]
      >> irule apply_steps_welltyped >> simp[WELLTYPED_CLAUSES, term_ok_welltyped, SF SFY_ss])
  >> irule $ iffRL ACONV_db >> rpt conj_tac
  >- (irule INST_WELLTYPED >> simp[WELLTYPED_CLAUSES])
  >- simp[INST_WELLTYPED, WELLTYPED_CLAUSES]
  >> DEP_REWRITE_TAC[INST_dbINST]
  >> simp[WELLTYPED_CLAUSES, db_def, dbINST_def]
  >> DEP_REWRITE_TAC[INST_dbINST] >> simp[]
  >> irule dbINST_bind_commute
  >> rpt strip_tac
  >> rename1 ‘dbVFREE_IN (dbVar z tyy) _’
  >> ‘welltyped body’ by simp[]
  >> drule dbVFREE_IN_VFREE_IN
  >> disch_then $ qspec_then ‘Var z tyy’ mp_tac
  >> simp[db_def] >> strip_tac
  >> metis_tac[])
  (* welltyped *)
  >- simp[INST_WELLTYPED]
  (* unique type *)
  >> rpt strip_tac
  >> ‘welltyped body’ by simp[]
  >> drule INST_dbINST >> disch_then $ qspec_then ‘tyin’ mp_tac
  >> strip_tac
  >> drule INST_WELLTYPED >> disch_then $ qspec_then ‘tyin’ mp_tac
  >> strip_tac
  >> rename1 ‘VFREE_IN (Var z tty) _’
  >> drule dbVFREE_IN_VFREE_IN
  >> disch_then $ qspec_then ‘Var z tty’ mp_tac
  >> simp[db_def]
  >> ‘db (INST tyin body) = dbINST tyin (db body)’ by simp[]
  >> strip_tac
  >> gvs[dbVFREE_IN_dbINST]
  >> rename1 ‘dbVFREE_IN (dbVar z oty) _’
  >> ‘oty = ty2’ by metis_tac[dbVFREE_IN_VFREE_IN, db_def]
  >> gvs[]
QED

Finalise apply_steps_Abs_alpha

(* Alpha-equivalence for esubst on Abs:
   esubst σ avds (Abs (Var z ty) M) is ACONV to
   Abs (Var z (ty_esubst σ ty)) (esubst σ [] M)
   when z doesn't collide with itself in the body (i.e., z only
   appears in body with type ty, not with any other type).
   This ensures the fast path of esubst_ty0 succeeds for z.
   When z is fresh (as in esubst_apply_steps_Abs_alpha), this holds
   automatically. *)
Theorem esubst_Abs_alpha:
  ∀z ty body.
    term_ok sig (Abs (Var z ty) body) ∧
    theory_ok (sig,axs) ∧ esubsts_ok sig σ ∧
    (∀ty2. VFREE_IN (Var z ty2) body ⇒ ty2 = ty) ⇒
    ACONV (esubst σ avds (Abs (Var z ty) body))
          (Abs (Var z (ty_esubst σ ty)) (esubst σ [] body))
Proof
  rpt strip_tac
  >> `term_ok sig body` by gvs[term_ok_def]
  >> `welltyped body` by metis_tac[term_ok_welltyped]
  >> irule $ iffRL ACONV_db >> rpt conj_tac
  >> blast_term_validation >> fs[term_ok_def]
  >- (irule esubst_welltyped >> simp[SF SFY_ss])
  >> DEP_REWRITE_TAC[db_esubst_thm]
  >> simp[SF SFY_ss, term_ok_def]
  >> simp[db_def, db_esubst_def, db_esubst_ty_def, db_esubst_tm_def]
  >> qspecl_then [`db body`, `(z,ty)`, `0`, `σ`] mp_tac db_esubst_ty_bind
  >> impl_tac
  >- (rpt strip_tac >> gvs[]
      >> `VFREE_IN (Var z ty') body`
           by metis_tac[dbVFREE_IN_VFREE_IN, db_def]
      >> metis_tac[])
  >> disch_then (SUBST1_TAC)
  >> DEP_REWRITE_TAC[GSYM db_esubst_tm_bind]
  >> imp_res_tac esubsts_ok_only_esubsts_consts >> simp[]
QED

(* Combined: esubst/apply_steps on Abs equation is ACONV to
   Abs equation with fresh binder z and esubst/apply_steps of the bodies.
   Follows from apply_steps_Abs_alpha + esubst_ACONV + esubst_Abs_alpha.
   The ∀nms allows the caller to require z avoids additional names
   (e.g. hypothesis names for the proves_ABS application).
   Uses a single z for BOTH l and r (needed because proves_ABS requires
   the same binder variable on both sides). *)
Theorem esubst_apply_steps_Abs_alpha:
  ∀stps nms.
    term_ok sig l ∧ term_ok sig r ∧
    theory_ok (sig,axs) ∧ esubsts_ok sig σ ∧
    type_ok (tysof sig) ty ∧ steps_ok sig stps ⇒
    ∃z ty'.
      ACONV (esubst σ avds (apply_steps stps (Abs (Var x ty) l)))
            (Abs (Var z ty') (esubst σ [] (apply_steps stps (VSUBST [(Var z ty, Var x ty)] l)))) ∧
      ACONV (esubst σ avds (apply_steps stps (Abs (Var x ty) r)))
            (Abs (Var z ty') (esubst σ [] (apply_steps stps (VSUBST [(Var z ty, Var x ty)] r)))) ∧
      ¬MEM z nms ∧
      type_ok (tysof (esubst_sig σ sig)) ty' ∧
      term_ok (esubst_sig σ sig)
              (esubst σ [] (apply_steps stps (VSUBST [(Var z ty, Var x ty)] l))) ∧
      term_ok (esubst_sig σ sig)
              (esubst σ [] (apply_steps stps (VSUBST [(Var z ty, Var x ty)] r)))
Proof
  rpt strip_tac
  >> `welltyped l ∧ welltyped r` by metis_tac[term_ok_welltyped]
  >> `term_ok sig (Abs (Var x ty) l) ∧ term_ok sig (Abs (Var x ty) r)` by
       (simp[term_ok_def] >> metis_tac[theory_ok_sig])
  (* Pick fresh z avoiding nms and step substitution names *)
  >> qabbrev_tac `stpnms = FLAT (MAP (λstep. case step of
       VStep ilist => FLAT (MAP (λ(s',s). tm_names s' ++ tm_names s) ilist)
       | TStep _ => []) stps)`
  >> qexists_tac `NVARIANT x (nms ++ stpnms)
       (Comb (Abs (Var x ty) l) (Abs (Var x ty) r))`
  >> qabbrev_tac `z = NVARIANT x (nms ++ stpnms)
       (Comb (Abs (Var x ty) l) (Abs (Var x ty) r))`
  >> `¬MEM z (tm_names (Abs (Var x ty) l)) ∧
      ¬MEM z (tm_names (Abs (Var x ty) r)) ∧
      ¬MEM z nms ∧ ¬MEM z stpnms`
       by (qspecl_then [`Comb (Abs (Var x ty) l) (Abs (Var x ty) r)`,
                        `x`, `nms ++ stpnms`] mp_tac NVARIANT_MEM
           >> simp[Abbr `z`, MEM_APPEND])
  (* Step freshness: z not in any VStep substitution names *)
  >> `EVERY (λstep. case step of
        VStep ilist => EVERY (λ(s',s). ¬MEM z (tm_names s' ++ tm_names s)) ilist
      | TStep _ => T) stps` by (
    simp[EVERY_MEM] >> rpt strip_tac >> Cases_on `step` >> simp[]
    >> simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac
    >> (CCONTR_TAC >> fs[]
        >> `MEM z (FLAT (MAP (λ(s',s). tm_names s' ++ tm_names s) l'))` by (
             simp[MEM_FLAT, MEM_MAP, EXISTS_PROD] >> metis_tac[MEM_APPEND])
        >> qpat_x_assum `¬MEM z stpnms` mp_tac
        >> simp[Abbr `stpnms`]
        >> once_rewrite_tac[MEM_FLAT] >> simp[MEM_MAP]
        >> qexists_tac `FLAT (MAP (λ(s',s). tm_names s' ++ tm_names s) l')`
        >> simp[]
        >> qexists_tac `VStep l'` >> simp[]))
  (* apply_steps_Abs_alpha for l and r *)
  >> qspecl_then [`stps`, `x`, `ty`, `l`, `z`] mp_tac apply_steps_Abs_alpha
  >> simp[] >> strip_tac
  >> qspecl_then [`stps`, `x`, `ty`, `r`, `z`] mp_tac apply_steps_Abs_alpha
  >> simp[] >> strip_tac
  (* Show ty2 = ty2': binder type depends only on stps and ty, not the body *)
  >> `ty2 = ty2'` by (
    `∃n2l tyl bdl. apply_steps stps (Abs (Var x ty) l) = Abs (Var n2l tyl) bdl ∧
                    welltyped bdl`
      by metis_tac[apply_steps_Abs]
    >> `∃n2r tyr bdr. apply_steps stps (Abs (Var x ty) r) = Abs (Var n2r tyr) bdr ∧
                      welltyped bdr`
      by metis_tac[apply_steps_Abs]
    >> `tyl = tyr` by metis_tac[apply_steps_Abs_has_type, WELLTYPED_LEMMA]
    >> `tyl = ty2` by (
      `typeof (apply_steps stps (Abs (Var x ty) l)) =
       typeof (Abs (Var z ty2)
         (apply_steps stps (VSUBST [(Var z ty,Var x ty)] l)))`
        by (irule ACONV_TYPE >> simp[WELLTYPED_CLAUSES] >> gvs[])
      >> gvs[typeof_def])
    >> `tyr = ty2'` by (
      `typeof (apply_steps stps (Abs (Var x ty) r)) =
       typeof (Abs (Var z ty2')
         (apply_steps stps (VSUBST [(Var z ty,Var x ty)] r)))`
        by (irule ACONV_TYPE >> simp[WELLTYPED_CLAUSES] >> gvs[])
      >> gvs[typeof_def])
    >> simp[] >> fs[])
  >> pop_assum (SUBST_ALL_TAC o GSYM)
  >> qexists_tac `ty_esubst σ ty2`
  >> rpt conj_tac
  (* ACONV for l: ACONV_TRANS with esubst_ACONV + esubst_Abs_alpha *)
  >- (irule ACONV_TRANS
      >> qexists_tac `esubst σ avds (Abs (Var z ty2)
           (apply_steps stps (VSUBST [(Var z ty, Var x ty)] l)))`
      >> conj_tac
      >- (irule esubst_ACONV >> simp[]
          >> qexistsl [`axs`, `sig`] >> simp[]
          >> conj_tac >- (irule apply_steps_term_ok >> simp[])
          >> conj_tac
          >- (drule term_ok_aconv >> simp[] >> disch_then $ qspec_then ‘sig’ mp_tac
              >> blast_term_validation)
          >> irule apply_steps_term_ok >> simp[]
          >> blast_term_validation)
      >> irule esubst_Abs_alpha >> simp[]
      >> qexistsl [`axs`, `sig`] >> simp[]
      >> conj_tac
      >- (drule term_ok_aconv >> simp[] >> disch_then $ qspec_then ‘sig’ mp_tac
          >> blast_term_validation)
      >> irule apply_steps_term_ok >> simp[]
      >> blast_term_validation)
  (* ACONV for r *)
  >- (irule ACONV_TRANS
      >> qexists_tac `esubst σ avds (Abs (Var z ty2)
           (apply_steps stps (VSUBST [(Var z ty, Var x ty)] r)))`
      >> conj_tac
      >- (irule esubst_ACONV >> simp[]
          >> qexistsl [`axs`, `sig`] >> simp[]
          >> conj_tac >- (irule apply_steps_term_ok >> simp[])
          >> conj_tac
          >- (drule term_ok_aconv >> simp[] >> disch_then $ qspec_then ‘sig’ mp_tac
              >> blast_term_validation)
          >> irule apply_steps_term_ok >> simp[]
          >> blast_term_validation)
      >> irule esubst_Abs_alpha >> simp[]
      >> qexistsl [`axs`, `sig`] >> simp[]
      >> conj_tac
      >- (drule term_ok_aconv >> simp[] >> disch_then $ qspec_then ‘sig’ mp_tac
          >> blast_term_validation)
      >> irule apply_steps_term_ok >> simp[]
      >> blast_term_validation)
  >> blast_term_validation
  >> irule ty_esubst_type_ok_alt >> drule term_ok_aconv
  >> simp[] >> disch_then $ qspec_then ‘sig’ mp_tac >> blast_term_validation
QED
        
Triviality term_image_cong:
  ∀ls f g.
    (∀t. MEM t ls ⇒ f t = g t) ⇒ term_image f ls = term_image g ls
Proof
  Induct >- rw[Once term_image_def]
  >> rpt gen_tac >> strip_tac
  >> ONCE_REWRITE_TAC [term_image_def]
  >> SUBGOAL_THEN “term_image f ls = term_image g ls”
       STRIP_ASSUME_TAC
  >- (first_x_assum irule >> rw[])
  >> qsuff_tac ‘f h = g h’ >> rw[]
QED

Triviality apply_steps_typeof_eq:
  ∀stps t1 t2.
    steps_ok sig stps ∧ term_ok sig t1 ∧ term_ok sig t2 ∧
    typeof t1 = typeof t2 ⇒
    typeof (apply_steps stps t1) = typeof (apply_steps stps t2)
Proof
  Induct >> rw[apply_steps_def] >> Cases_on ‘h’
  >> rw[apply_steps_def] >> gvs[steps_ok_def]
  >> drw[typeof_vsubst1] >> blast_term_validation
  >- metis_tac[steps_ok_def]
  >> first_x_assum drule_all >> rw[]
  >> ‘∃typ. apply_steps stps t1 has_type typ ∧ apply_steps stps t2 has_type typ’
    by metis_tac[typeof_has_type, term_ok_welltyped, apply_steps_welltyped]
  >> ntac 2 $ dxrule INST_HAS_TYPE >> rw[] >> metis_tac[WELLTYPED_LEMMA]
QED

Resume proves_substitutable_aux[Abs]:
  rename1 ‘steps_ok _ stps’
  >> eqn_dist_tac >> DEP_REWRITE_TAC[apply_steps_term_ok] >> gvs[term_ok_def]
  >> ‘term_ok sig l ∧ term_ok sig r ∧ hypset_ok h ∧
      (∀p. MEM p h ⇒ term_ok sig p ∧ p has_type Bool)’
    by (dxrule proves_term_ok
        >> simp[EVERY_MEM, term_ok_equation, theory_ok_sig, SF SFY_ss] >> metis_tac[])
  >> simp[]
  (* Get z from alpha lemma (pair version), avoiding hypothesis names *)
  >> rev_drule_then drule_all esubst_apply_steps_Abs_alpha
  >> disch_then $ qspecl_then [‘x’, ‘FLAT (MAP tm_names h)’,
       ‘FLAT (MAP tm_names (term_image (esubst σ []) (term_image (apply_steps stps) h)))’]
     strip_assume_tac
  (* Use IH with VSUBST-last augmented steps stps ++ [VStep ...].
     By apply_steps_append: apply_steps (stps ++ [VStep ilist]) t = apply_steps stps (VSUBST ilist t).
     This matches the alpha theorem body, and crucially VSUBST acts directly on h elements
     (where ¬VFREE_IN (Var x ty)), making it identity via VSUBST_NOT_FREE. *)
  >> first_x_assum $ qspecl_then [‘σ’, ‘stps ++ [VStep [(Var z ty, Var x ty)]]’] mp_tac
  >> simp[apply_steps_append, apply_steps_def, steps_ok_append, steps_ok_def]
  (* Distribute === through esubst/VSUBST/apply_steps so proves_ABS can match *)
  >> eqn_dist_tac >> blast_term_validation >> rw[]
  (* VSUBST is identity on h elements (¬VFREE_IN); rewrite term_image to eliminate VStep.
     After this, IH hypothesis set matches the goal hypothesis set exactly. *)
  >> ‘term_image (apply_steps (stps ++ [VStep [(Var z ty, Var x ty)]])) h =
      term_image (apply_steps stps) h’
    by (irule term_image_cong >> rw[apply_steps_append, apply_steps_def]
        >> ‘VSUBST [(Var z ty, Var x ty)] t = t’ suffices_by rw[]
        >> MATCH_MP_TAC VSUBST_NOT_FREE_VAR >> rw[] >> gvs[EVERY_MEM])
  >> pop_assum (fn th =>
                  RULE_ASSUM_TAC (REWRITE_RULE[th]) >> REWRITE_TAC[th])
  >> blast_term_validation
  (* Move IH proves from goal antecedent into assumptions so drule_at finds it
     (not the original ((sig,axs),h) |- l === r which has the wrong hyp set) *)
  (* Apply proves_ABS to the IH equation (hyps = term_image (esubst σ []) ...) *)
  >> drule_at (Pos last) proves_ABS
  >> disch_then $ qspecl_then [‘ty'’, ‘z’] mp_tac
  >> impl_tac
  >- (rw[]
      (* ¬EXISTS (VFREE_IN (Var z ty’)): z avoids hypothesis names (now matches asm 12) *)
      >> rw[EVERY_MEM, EXISTS_MEM] >> rpt strip_tac
      >> spose_not_then strip_assume_tac
      >> imp_res_tac VFREE_IN_tm_names
      >> gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS]
      >> metis_tac[])
  >> rw[]
  (* Use proves_ACONV to connect to the goal *)
  >> irule proves_ACONV >> first_x_assum $ irule_at Any
  >> rw[] >> ntac 2 blast_term_validation
  >> rw[hypset_ok_term_image]
  >- (drw[typeof_esubst] >> blast_term_validation >> cong_tac $ SOME 1
      >> irule apply_steps_typeof_eq >> blast_term_validation
      >> rev_drule proves_term_ok >> simp[] >> drw[term_ok_equation]
      >> metis_tac[theory_ok_sig, FST])
  >- (rw[EVERY_MEM]
      >> dxrule MEM_term_image_imp >> rw[]
      >> dxrule MEM_term_image_imp >> rw[]
      >> res_tac >> gvs[]
      >> blast_term_validation
      >> DEP_REWRITE_TAC[esubst_has_type_bool, apply_steps_has_type_Bool, apply_steps_term_ok]
      >> simp[term_ok_welltyped, SF SFY_ss])
  (* ACONV of conclusion: chain via ACONV_SYM of alpha theorem + ACONV_esubst_avds.
     irule ACONV_equation creates a single conjunction; rpt conj_tac splits it;
     TRY handles welltyped goals; remaining ACONV goals use transitivity chain. *)
  >- (irule ACONV_equation >> rw[]
      >> blast_term_validation
      >> irule ACONV_TRANS
      >> first_x_assum (irule_at Any o MATCH_MP ACONV_SYM)
      >> irule ACONV_ABS >> blast_term_validation
      >> irule ACONV_esubst_avds >> rw[]
      >> blast_term_validation
      >> (ntac 2 $ first_x_assum $ irule_at Any >> blast_term_validation))
  (* Hypotheses: IH hyps = goal hyps after term_image_cong rewrite *)
  >> rw[EVERY_MEM, EXISTS_MEM] >> metis_tac[ACONV_REFL]
QED

Resume proves_substitutable_aux[Assume]:
  drule_then drule theory_ok_esubst_axs >> disch_then $ qspec_then ‘[]’ mp_tac >> rw[]
  >> drule proves_ASSUME >> disch_then $ qspec_then ‘esubst σ [] (apply_steps steps' c)’ mp_tac
  >> rw[] >> irule proves_ACONV >> rw[] >> blast_term_validation
  >- (irule esubst_has_type_bool >> metis_tac[apply_steps_has_type_Bool, apply_steps_term_ok])
  >> first_x_assum $ irule_at Any >> rw[ACONV_REFL] >> blast_term_validation
  >- (irule esubst_has_type_bool >> metis_tac[apply_steps_has_type_Bool, apply_steps_term_ok])
  >> irule ACONV_esubst_avds >> metis_tac[term_ok_welltyped, apply_steps_term_ok]
QED

Resume proves_substitutable_aux[Beta]:
  rename1 ‘steps_ok _ stps’
  >> eqn_dist_tac >> blast_term_validation
  >> DEP_REWRITE_TAC[apply_steps_comb, esubst_comb]
  >> blast_term_validation >> drule_all esubst_apply_steps_Abs
  >> disch_then $ qspecl_then [‘x’, ‘[]’] mp_tac >> rw[]
  >> drule_all_then (qspec_then‘[]’strip_assume_tac) theory_ok_esubst_axs
  >> drule proves_BETA >> disch_then $ qspecl_then [‘body’, ‘ty'’, ‘z’] mp_tac
  >> rw[]
  >> drule_at (Pos last) proves_INST
  >> disch_then $ qspec_then ‘[(esubst σ [] (apply_steps stps (Var x ty)), Var z ty')]’ mp_tac
  >> impl_tac >- (simp[] >> blast_term_validation) >> rw[]
  >> irule proves_ACONV >> rw[]
  >- (ntac 2 blast_term_validation >> gvs[has_type_typeof]
      >> ‘VSUBST [(esubst σ [] (apply_steps stps (Var x ty)),Var z ty')] body
          has_type typeof body’ by
        (irule VSUBST_HAS_TYPE >> simp[WELLTYPED_LEMMA, term_ok_welltyped]
         >> irule $ iffLR WELLTYPED >> gvs[term_ok_welltyped, SF SFY_ss])
      >> dxrule ACONV_TYPE >> blast_term_validation >> rw[] >> metis_tac[has_type_typeof])
  >> first_x_assum $ irule_at Any >> DEP_REWRITE_TAC[GEN_ALL VSUBST_equation] >> rw[]
  >- (qpat_assum ‘term_ok (esubst_sig _ _) body’ mp_tac >> disch_then $ irule_at Any
      >> simp[SF SFY_ss, term_ok_welltyped])
  >> simp[VSUBST_def] >> irule ACONV_equation >> blast_term_validation >> rw[ACONV_REFL]
  >- (irule esubst_welltyped >> rpt $ last_x_assum $ irule_at Any >> blast_term_validation)
  >> gvs[has_type_typeof]
QED

Resume proves_substitutable_aux[DeductAntisym]:
  rpt $ first_x_assum drule_all
  >> eqn_dist_tac
  >> imp_res_tac proves_term_ok >> gvs[EVERY_MEM]
  >> simp[apply_steps_term_ok]
  >> rpt strip_tac
  >> pop_assum (fn ih2 => pop_assum (fn ih1 =>
       mp_tac (MATCH_MP proves_DEDUCT_ANTISYM (CONJ ih1 ih2))))
  >> rw[]
  >> irule proves_ACONV >> first_x_assum $ irule_at Any
  >> simp[hypset_ok_term_image, hypset_ok_term_union]
  >> rpt conj_tac
  >- suspend "da_welltyped"
  >- suspend "da_every_tok"
  >- suspend "da_aconv"
  >> suspend "da_every_hyp"
QED

Resume proves_substitutable_aux[da_welltyped]:
  ntac 2 blast_term_validation >> drw[typeof_esubst]
  >> blast_term_validation >> cong_tac $ SOME 1
  >> irule apply_steps_typeof_eq >> blast_term_validation
  >> metis_tac[WELLTYPED_LEMMA]
QED

Resume proves_substitutable_aux[da_every_tok]:
  rw[EVERY_MEM] >> dxrule MEM_term_image_imp >> rw[]
  >> dxrule MEM_term_image_imp >> rw[]
  >> dxrule MEM_term_union_imp >> rw[]
  >> dxrule MEM_term_remove_imp >> rw[]
  >> first_x_assum drule >> rw[]
  >> DEP_REWRITE_TAC[esubst_term_ok, esubst_has_type_bool,
                     apply_steps_term_ok, apply_steps_has_type_Bool]
  >> simp[SF SFY_ss, term_ok_welltyped]
  >> metis_tac[]
QED

Resume proves_substitutable_aux[da_aconv]:
  irule ACONV_equation >> blast_term_validation
  >> drw[ACONV_esubst_avds] >> blast_term_validation
QED

Theorem apply_steps_ACONV:
  ∀stps x y.
    steps_ok sig stps ∧
    welltyped x ∧
    welltyped y ∧
    ACONV x y ⇒
    ACONV (apply_steps stps x) (apply_steps stps y)
Proof
  Induct >> rw[apply_steps_def] >> Cases_on ‘h’ >> rw[apply_steps_def] >> gvs[steps_ok_def]
  >- (irule ACONV_VSUBST >> rw[] >> metis_tac[apply_steps_welltyped])
  >> irule ACONV_INST >> rw[] >> metis_tac[apply_steps_welltyped]
QED

Resume proves_substitutable_aux[da_every_hyp]:
  rw[EVERY_MEM, EXISTS_MEM]
  >> dxrule MEM_term_union_imp >> rw[]
  >> dxrule MEM_term_remove_imp >> gvs[hypset_ok_term_image]
  >> strip_tac >> gvs[]
  >> ntac 2 (dxrule MEM_term_image_imp >> strip_tac >> gvs[])
  >> first_x_assum drule >> strip_tac
  >- (
  `¬ACONV c' x` by (
    strip_tac
    >> qsuff_tac `ACONV (esubst σ (FLAT (MAP tm_names h2)) (apply_steps steps' c'))
                  (esubst σ [] (apply_steps steps' x))`
    >- metis_tac[]
    >> irule esubst_ACONV >> simp[SF SFY_ss]
    >> conj_tac >- (irule apply_steps_ACONV >> simp[SF SFY_ss, term_ok_welltyped])
    >> metis_tac[apply_steps_term_ok])
  >> `MEM x (term_remove c' h1)` by (irule MEM_term_remove >> simp[])
  >> `MEM x (term_union (term_remove c' h1) (term_remove c h2))` by (
    irule MEM_term_union_first >> simp[hypset_ok_term_remove])
  >> qspecl_then [`term_union (term_remove c' h1) (term_remove c h2)`,
                  `apply_steps steps'`, `x`] mp_tac MEM_term_image
  >> impl_tac >- simp[hypset_ok_term_union, hypset_ok_term_remove]
  >> strip_tac
  >> `term_ok sig y` by (
    drule_then assume_tac MEM_term_image_imp >> gvs[]
    >> irule apply_steps_term_ok >> simp[]
    >> imp_res_tac MEM_term_union_imp
    >> imp_res_tac MEM_term_remove_imp >> gvs[]
    >> imp_res_tac proves_term_ok >> gvs[EVERY_MEM]
    >> metis_tac[])
  >> qspecl_then [`term_image (apply_steps steps')
                    (term_union (term_remove c' h1) (term_remove c h2))`,
                  `esubst σ []`, `y`] mp_tac MEM_term_image
  >> impl_tac >- simp[hypset_ok_term_image, hypset_ok_term_union, hypset_ok_term_remove]
  >> strip_tac
  >> qexists_tac `y'` >> simp[]
  >> irule ACONV_TRANS >> qexists_tac `esubst σ [] y` >> simp[]
  >> irule esubst_ACONV >> simp[SF SFY_ss]
  >> qexistsl_tac [`axs`, `sig`] >> simp[]
  >> irule apply_steps_term_ok >> simp[])
  >> (
  `¬ACONV c x` by (
    strip_tac
    >> qsuff_tac `ACONV (esubst σ (FLAT (MAP tm_names h1)) (apply_steps steps' c))
                  (esubst σ [] (apply_steps steps' x))`
    >- metis_tac[]
    >> irule esubst_ACONV >> simp[SF SFY_ss]
    >> conj_tac >- (irule apply_steps_ACONV >> simp[SF SFY_ss, term_ok_welltyped])
    >> metis_tac[apply_steps_term_ok])
  >> `MEM x (term_remove c h2)` by (irule MEM_term_remove >> simp[])
  >> qspecl_then [`term_remove c' h1`, `term_remove c h2`, `x`]
                 mp_tac MEM_term_union
  >> impl_tac >- simp[hypset_ok_term_remove]
  >> strip_tac
  >> `term_ok sig y` by (
    imp_res_tac MEM_term_union_imp >> imp_res_tac MEM_term_remove_imp >> gvs[]
    >> imp_res_tac proves_term_ok >> gvs[EVERY_MEM]
    >> metis_tac[])
  >> qspecl_then [`term_union (term_remove c' h1) (term_remove c h2)`,
                  `apply_steps steps'`, `y`] mp_tac MEM_term_image
  >> impl_tac >- simp[hypset_ok_term_union, hypset_ok_term_remove]
  >> strip_tac
  >> `term_ok sig y'` by (
    drule_then assume_tac MEM_term_image_imp >> gvs[]
    >> irule apply_steps_term_ok >> simp[]
    >> imp_res_tac MEM_term_union_imp
    >> imp_res_tac MEM_term_remove_imp >> gvs[]
    >> imp_res_tac proves_term_ok >> gvs[EVERY_MEM]
    >> metis_tac[])
  >> qspecl_then [`term_image (apply_steps steps')
                    (term_union (term_remove c' h1) (term_remove c h2))`,
                  `esubst σ []`, `y'`] mp_tac MEM_term_image
  >> impl_tac >- simp[hypset_ok_term_image, hypset_ok_term_union, hypset_ok_term_remove]
  >> strip_tac
  >> qexists_tac `y''` >> simp[]
  >> irule ACONV_TRANS >> qexists_tac `esubst σ [] y'` >> simp[]
  >> irule ACONV_TRANS >> qexists_tac `esubst σ [] (apply_steps steps' y)` >> simp[]
  >> conj_tac
  >- (irule esubst_ACONV >> simp[SF SFY_ss]
      >> conj_tac >- (irule apply_steps_ACONV >> metis_tac[term_ok_welltyped])
      >> qexistsl_tac [`axs`, `sig`] >> simp[]
      >> conj_tac >- (irule apply_steps_term_ok >> simp[])
      >> irule apply_steps_term_ok >> simp[])
  >> irule esubst_ACONV >> simp[SF SFY_ss]
  >> qexistsl_tac [`axs`, `sig`] >> simp[]
  >> irule apply_steps_term_ok >> simp[])
QED

Resume proves_substitutable_aux[EQ_MP]:
  rpt $ first_x_assum drule_all >> eqn_dist_tac >> imp_res_tac proves_term_ok
  >> gvs[EVERY_MEM] >> drule_at Any $ iffLR term_ok_equation >> impl_tac
  >- metis_tac[theory_ok_sig, FST] >> blast_term_validation >> rw[]
  >> qabbrev_tac ‘thyσ = (esubst_sig σ sig, IMAGE (esubst σ []) axs)’
  >> drule_then drule proves_EQ_MP >> impl_tac >> fs[]
  >- (rw[] >> drule_at (Pos last) $ iffLR term_ok_equation >> dxrule theory_ok_sig >> simp[])
  >- (*(irule esubst_ACONV >> rw[]
      >- (irule apply_steps_ACONV >> blast_term_validation)
      >> first_x_assum $ irule_at Any >> blast_term_validation)
  >> rw[] >> irule proves_ACONV >> first_x_assum $ irule_at Any
  >> blast_term_validation >> simp[hypset_ok_term_image, hypset_ok_term_union]
  >> rw[EVERY_MEM, EXISTS_MEM]
  >- (dxrule MEM_term_image_imp >> rw[] >> dxrule MEM_term_image_imp >> rw[]
      >> rw[Abbr‘thyσ’] >> dxrule MEM_term_union_imp >> rw[]
      >> ntac 2 $ rev_dxrule proves_term_ok >> simp[EVERY_MEM] >> blast_term_validation)
  >- (dxrule MEM_term_image_imp >> rw[] >> dxrule MEM_term_image_imp >> rw[]
      >> rw[Abbr‘thyσ’] >> dxrule MEM_term_union_imp >> rw[]
      >> ntac 2 $ rev_dxrule proves_term_ok >> simp[EVERY_MEM]
      >> irule esubst_has_type_bool >> rpt $ first_x_assum $ irule_at Any
      >> blast_term_validation >> irule apply_steps_has_type_Bool >> metis_tac[])
  >- (irule ACONV_esubst_avds >> rpt $ first_x_assum $ irule_at Any >> blast_term_validation)
  >> dxrule MEM_term_union_imp >> rw[]
  >> dxrule MEM_term_image_imp >> rw[] >> dxrule MEM_term_image_imp >> rw[]
  >- cheat
  >> cheat*)
  >> cheat
QED

Resume proves_substitutable_aux[INST]:
  rename1 ‘steps_ok _ stps’
  >> first_x_assum $ qspecl_then [‘σ’, ‘stps ++ [VStep ilist]’] mp_tac
  >> simp[apply_steps_append, apply_steps_def, steps_ok_append, steps_ok_def]
  >> rw[]
  >> irule proves_ACONV >> first_x_assum $ irule_at Any >> rw[]
  >> dxrule proves_term_ok >> rw[EVERY_MEM, EXISTS_MEM, hypset_ok_term_image]
  >> ‘term_ok sig (VSUBST ilist c)’ by metis_tac[term_ok_VSUBST]
  >> ‘term_ok sig (apply_steps stps (VSUBST ilist c))’ by metis_tac[apply_steps_term_ok]
  >- (irule esubst_welltyped >> simp[SF SFY_ss])
  >- (ntac 2 (dxrule MEM_term_image_imp >> rw[]) >> irule esubst_term_ok >> simp[SF SFY_ss]
      >> irule apply_steps_term_ok >> dxrule MEM_term_image_imp >> rw[] >> irule term_ok_VSUBST
      >> rw[])
  >- (ntac 2 (dxrule MEM_term_image_imp >> rw[]) >> irule esubst_has_type_bool >> simp[SF SFY_ss]
      >> dxrule MEM_term_image_imp >> rw[]
      >- (irule apply_steps_has_type_Bool >> rw[SF SFY_ss]
          >> irule VSUBST_HAS_TYPE >> simp[] >> metis_tac[])
      >> rpt $ first_assum $ irule_at Any >> irule apply_steps_term_ok >> simp[]
      >> irule term_ok_VSUBST >> rw[])
  >- (irule esubst_ACONV >> simp[SF SFY_ss])
  >> rw[EVERY_MEM, EXISTS_MEM]
  >> ntac 2 (dxrule MEM_term_image_imp >> rw[])
  >> gvs[apply_steps_append, apply_steps_def]
  >> rename1 ‘MEM p h’
  >> ‘∃y. MEM y (term_image (VSUBST ilist) h) ∧ ACONV (VSUBST ilist p) y’
    by (irule MEM_term_image >> simp[])
  >> ‘∃y'. MEM y' (term_image (apply_steps stps) (term_image (VSUBST ilist) h)) ∧
           ACONV (apply_steps stps y) y'’
    by (irule MEM_term_image >> simp[hypset_ok_term_image])
  >> ‘∃y''. MEM y'' (term_image (esubst σ [])
                                (term_image (apply_steps stps) (term_image (VSUBST ilist) h))) ∧
            ACONV (esubst σ [] y') y''’
    by (irule MEM_term_image >> simp[hypset_ok_term_image])
  >> qexists ‘y''’ >> simp[]
  >> irule ACONV_TRANS >> qexists ‘esubst σ [] y'’ >> simp[]
  >> ‘ACONV (apply_steps stps (VSUBST ilist p)) y'’
    by (irule ACONV_TRANS >> qexists ‘apply_steps stps y’ >> simp[]
        >> irule apply_steps_ACONV >> rw[]
        >- (irule VSUBST_WELLTYPED >> metis_tac[term_ok_welltyped])
        >> simp[SF SFY_ss]
        >> rpt (dxrule_then assume_tac MEM_term_image_imp >> gvs[])
        >> irule VSUBST_WELLTYPED >> metis_tac[term_ok_welltyped])
  >> ‘term_ok sig (apply_steps stps (VSUBST ilist p))’
    by (irule apply_steps_term_ok >> simp[]
        >> irule term_ok_VSUBST >> rw[])
  >> irule esubst_ACONV >> simp[SF SFY_ss]
  >> rpt $ first_x_assum $ irule_at Any
  >> rpt (dxrule_then assume_tac MEM_term_image_imp >> gvs[])
  >> irule apply_steps_term_ok >> simp[]
  >> irule term_ok_VSUBST >> rw[]
QED

Theorem proves_concl_welltyped:
  thy |- c ⇒ welltyped c
Proof
  rw[] >> dxrule proves_term_ok >> rw[EVERY_MEM]
  >> irule term_ok_welltyped >> metis_tac[]
QED

Resume proves_substitutable_aux[INST_TYPE]:
  rename1 ‘steps_ok _ stps’
  >> first_x_assum $ qspecl_then [‘σ’, ‘stps ++ [TStep tyin]’] mp_tac
  >> simp[apply_steps_append, apply_steps_def, steps_ok_append, steps_ok_def]
  >> rw[]
  >> irule proves_ACONV >> first_x_assum $ irule_at Any >> rw[]
  >> dxrule proves_term_ok >> rw[EVERY_MEM, EXISTS_MEM, hypset_ok_term_image]
  >> ‘term_ok sig (INST tyin c)’ by metis_tac[term_ok_INST]
  >> ‘term_ok sig (apply_steps stps (INST tyin c))’ by metis_tac[apply_steps_term_ok]
  >- (irule esubst_welltyped >> simp[SF SFY_ss])
  >- (ntac 2 (dxrule MEM_term_image_imp >> rw[]) >> irule esubst_term_ok >> simp[SF SFY_ss]
      >> irule apply_steps_term_ok >> dxrule MEM_term_image_imp >> rw[] >> irule term_ok_INST
      >> rw[])
  >- (ntac 2 (dxrule MEM_term_image_imp >> rw[]) >> irule esubst_has_type_bool >> simp[SF SFY_ss]
      >> dxrule MEM_term_image_imp >> rw[]
      >- (irule apply_steps_has_type_Bool >> rw[SF SFY_ss]
          >> irule INST_HAS_TYPE >> metis_tac[TYPE_SUBST_Bool])
      >> rpt $ first_assum $ irule_at Any >> irule apply_steps_term_ok >> simp[]
      >> irule term_ok_INST >> rw[])
  >- (irule esubst_ACONV >> simp[SF SFY_ss])
  >> rw[EVERY_MEM, EXISTS_MEM]
  >> ntac 2 (dxrule MEM_term_image_imp >> rw[])
  >> gvs[apply_steps_append, apply_steps_def]
  >> rename1 ‘MEM p h’
  >> ‘∃y. MEM y (term_image (INST tyin) h) ∧ ACONV (INST tyin p) y’
    by (irule MEM_term_image >> simp[])
  >> ‘∃y'. MEM y' (term_image (apply_steps stps) (term_image (INST tyin) h)) ∧
           ACONV (apply_steps stps y) y'’
    by (irule MEM_term_image >> simp[hypset_ok_term_image])
  >> ‘∃y''. MEM y'' (term_image (esubst σ [])
                                (term_image (apply_steps stps) (term_image (INST tyin) h))) ∧
            ACONV (esubst σ [] y') y''’
    by (irule MEM_term_image >> simp[hypset_ok_term_image])
  >> qexists ‘y''’ >> simp[]
  >> irule ACONV_TRANS >> qexists ‘esubst σ [] y'’ >> simp[]
  >> ‘ACONV (apply_steps stps (INST tyin p)) y'’
    by (irule ACONV_TRANS >> qexists ‘apply_steps stps y’ >> simp[]
        >> irule apply_steps_ACONV >> rw[]
        >- (irule INST_WELLTYPED >> metis_tac[term_ok_welltyped])
        >> simp[SF SFY_ss]
        >> rpt (dxrule_then assume_tac MEM_term_image_imp >> gvs[])
        >> irule INST_WELLTYPED >> metis_tac[term_ok_welltyped])
  >> ‘term_ok sig (apply_steps stps (INST tyin p))’
    by (irule apply_steps_term_ok >> simp[]
        >> irule term_ok_INST >> rw[])
  >> irule esubst_ACONV >> simp[SF SFY_ss]
  >> rpt $ first_x_assum $ irule_at Any
  >> rpt (dxrule_then assume_tac MEM_term_image_imp >> gvs[])
  >> irule apply_steps_term_ok >> simp[]
  >> irule term_ok_INST >> simp[] >> metis_tac[]
QED

Resume proves_substitutable_aux[MK_COMB]:
  rw[] >> eqn_dist_tac >> cheat
QED

Resume proves_substitutable_aux[Refl]:
  eqn_dist_tac
  >> irule proves_REFL >> rw[theory_ok_esubst_axs]
  >> irule esubst_term_ok >> simp[apply_steps_term_ok, SF SFY_ss]
QED

Resume proves_substitutable_aux[Axioms]:
  irule axiom_steps_derivable >> rw[] >> metis_tac[]
QED

Finalise proves_substitutable_aux

Theorem apply_steps_id:
  apply_steps [] = (λp. p)
Proof
  irule EQ_EXT >> simp[apply_steps_def]
QED

Theorem proves_substitutable:
  ∀sig axs h c.
    theory_ok (sig,axs) ∧ ((sig,axs),h) |- c ∧
    esubsts_ok sig σ ∧
    (∀ax. ax ∈ axs ⇒ no_var_collapse σ ax) ⇒
    ((esubst_sig σ sig,IMAGE (esubst σ []) axs),
     term_image (esubst σ []) h) |-
     esubst σ (FLAT (MAP tm_names h)) c
Proof
  rw[] >> drule_at Any proves_substitutable_aux
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘[]’ mp_tac
  >> simp[steps_ok_def, apply_steps_def, SF ETA_ss, apply_steps_id, term_image_id]
QED

val _ = export_theory()
