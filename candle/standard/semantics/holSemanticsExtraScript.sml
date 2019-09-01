(*
  Some lemmas about the semantics.
*)
open preamble holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory setSpecTheory

val _ = new_theory"holSemanticsExtra"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

Theorem is_std_interpretation_is_type:
   is_std_interpretation i ⇒ is_std_type_assignment (FST i)
Proof
  Cases_on`i` >> simp[is_std_interpretation_def]
QED

(* typesem *)

Theorem typesem_inhabited:
   is_set_theory ^mem ⇒
    ∀tyenv δ τ ty.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ ∧
    type_ok tyenv ty
    ⇒
    inhabited (typesem δ τ ty)
Proof
  strip_tac >> gen_tac >> ho_match_mp_tac typesem_ind >>
  simp[typesem_def,is_type_valuation_def,type_ok_def] >>
  rw[is_type_assignment_def,FLOOKUP_DEF] >>
  fs[FEVERY_ALL_FLOOKUP,FLOOKUP_DEF] >>
  first_x_assum(qspec_then`name`mp_tac) >> simp[] >>
  disch_then match_mp_tac >>
  simp[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem typesem_Fun:
   ∀δ τ dom rng.
    is_std_type_assignment δ ⇒
    typesem δ τ (Fun dom rng) =
    Funspace (typesem δ τ dom) (typesem δ τ rng)
Proof
  rw[is_std_type_assignment_def,typesem_def]
QED

Theorem typesem_Bool:
   ∀δ τ.
    is_std_type_assignment δ ⇒
    typesem δ τ Bool = boolset
Proof
  rw[is_std_type_assignment_def,typesem_def]
QED

Theorem typesem_TYPE_SUBST:
   ∀tyin ty δ τ.
      typesem δ τ (TYPE_SUBST tyin ty) =
      typesem δ (λx. typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty
Proof
  ho_match_mp_tac TYPE_SUBST_ind >> simp[typesem_def] >>
  rw[] >> rpt AP_TERM_TAC >>
  simp[MAP_MAP_o,MAP_EQ_f]
QED

Theorem typesem_tyvars:
   ∀δ τ ty τ'.
    (∀x. MEM x (tyvars ty) ⇒ τ' x = τ x) ⇒
    typesem δ τ' ty = typesem δ τ ty
Proof
  ho_match_mp_tac typesem_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,typesem_def] >>
  rw[] >> rpt AP_TERM_TAC >> rw[MAP_EQ_f] >>
  metis_tac[]
QED

Theorem typesem_consts:
   ∀δ τ ty δ'.
    (∀name args. (Tyapp name args) subtype ty ⇒
      δ' name = δ name ∨
      ∃vars. args = MAP Tyvar vars ∧
             δ' name (MAP τ vars) = δ name (MAP τ vars))
    ⇒ typesem δ' τ ty = typesem δ τ ty
Proof
  ho_match_mp_tac typesem_ind >>
  conj_tac >- simp[typesem_def] >>
  rw[] >> simp[typesem_def] >>
  fs[subtype_Tyapp] >>
  first_assum(qspecl_then[`name`,`args`]mp_tac) >>
  impl_tac >- rw[] >> strip_tac >- (
    rw[] >> AP_TERM_TAC >> simp[MAP_EQ_f] >> metis_tac[] ) >>
  simp[MAP_MAP_o,combinTheory.o_DEF,typesem_def,ETA_AX]
QED

(* termsem *)

Theorem termsem_typesem:
   is_set_theory ^mem ⇒
    ∀sig i tm v δ τ tmenv.
      δ = FST i ∧ τ = FST v ∧
      is_valuation (tysof sig) δ v ∧
      is_interpretation sig i ∧
      is_std_type_assignment δ ∧
      term_ok sig tm ∧ tmenv = tmsof sig
      ⇒
      termsem tmenv i v tm <: typesem δ τ (typeof tm)
Proof
  strip_tac >> ntac 2 Cases >> Induct
  >- (
    Cases_on`v`>>
    simp[termsem_def,is_valuation_def,is_term_valuation_def,term_ok_def] )
  >- (
    Cases_on`v`>>
    simp[termsem_def,term_ok_def] >> rw[] >>
    qmatch_abbrev_tac`instance sig ii name ty τ <: X` >>
    qspecl_then[`sig`,`ii`,`name`,`ty`]mp_tac instance_def >>
    rw[Abbr`ty`,Abbr`ii`,Abbr`sig`] >>
    simp[Once typesem_TYPE_SUBST,Abbr`X`,combinTheory.o_DEF] >>
    qmatch_abbrev_tac`X <: typesem δ τi ty0` >>
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP] >>
    first_x_assum (qspecl_then[`name`,`ty0`]mp_tac) >>
    simp[] >> disch_then(qspec_then`λx. if MEM x (tyvars ty0) then τi x else boolset`mp_tac) >>
    simp[Abbr`X`,Abbr`τi`] >>
    impl_tac >- (
      fs[is_type_valuation_def] >>
      reverse(rw[])>-metis_tac[mem_boolset]>>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      fs[is_valuation_def] >> metis_tac[] ) >>
    qmatch_abbrev_tac`a <: b ⇒ a' <: b'` >>
    `a' = a` by (
      unabbrev_all_tac >> rpt AP_TERM_TAC >> simp[MAP_EQ_f] >>
      simp[MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode]) >>
    `b' = b` by (
      unabbrev_all_tac >>
      match_mp_tac typesem_tyvars >> rw[] ) >>
    rw[] )
  >- (
    simp[termsem_def,term_ok_def] >>
    rw[] >> imp_res_tac typesem_Fun >> fs[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    metis_tac[]) >>
  simp[termsem_def,term_ok_def] >>
  rw[] >> imp_res_tac typesem_Fun >> rw[] >>
  simp[termsem_def] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  fs[] >> rw[] >>
  Q.PAT_ABBREV_TAC`vv = (X:'U valuation)` >>
  first_x_assum (qspec_then`vv`mp_tac) >>
  simp[Abbr`vv`] >> disch_then match_mp_tac >>
  Cases_on`v`>> fs[is_valuation_def,is_term_valuation_def] >>
  rw[combinTheory.APPLY_UPDATE_THM] >> rw[]
QED

Theorem termsem_typesem_matchable:
   is_set_theory ^mem ⇒
     ∀sig i tm v δ τ tmenv ty.
       δ = tyaof i ∧ τ = tyvof v ∧ is_valuation (tysof sig) δ v ∧
       is_interpretation sig i ∧ is_std_type_assignment δ ∧
       term_ok sig tm ∧ tmenv = tmsof sig ∧
       ty = typesem δ τ (typeof tm) ⇒
       termsem tmenv i v tm <: ty
Proof
  PROVE_TAC[termsem_typesem]
QED

Theorem termsem_consts:
   ∀tmsig i v tm i'.
      welltyped tm ∧
      (∀name ty. VFREE_IN (Const name ty) tm ⇒
                 instance tmsig i' name ty (tyvof v) =
                 instance tmsig i name ty (tyvof v)) ∧
      (∀t. t subterm tm ⇒
         typesem (tyaof i') (tyvof v) (typeof t) =
         typesem (tyaof i ) (tyvof v) (typeof t))
      ⇒
      termsem tmsig i' v tm = termsem tmsig i v tm
Proof
  Induct_on`tm` >> simp[termsem_def] >> rw[]
  >- (
    fs[subterm_Comb] >>
    metis_tac[]) >>
  simp[termsem_def] >>
  fsrw_tac[boolSimps.DNF_ss][subterm_Abs] >>
  rpt AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

val Equalsem =
  is_std_interpretation_def
  |> SPEC_ALL |> concl |> rhs
  |> strip_conj |> last
  |> strip_comb |> snd |> last

Theorem termsem_Equal:
   is_set_theory ^mem ⇒
    ∀Γ i v ty.
      is_structure Γ i v ∧ type_ok (tysof Γ) ty ⇒
      termsem (tmsof Γ) i v (Equal ty) = ^Equalsem [typesem (FST i) (FST v) ty]
Proof
  rw[termsem_def,LET_THM] >> fs[is_structure_def] >>
  qspecl_then[`tmsof Γ`,`i`,`(strlit "=")`]mp_tac instance_def >> fs[is_std_sig_def]>>
  disch_then(qspec_then`[(ty,Tyvar(strlit "A"))]`mp_tac)>>
  simp[REV_ASSOCD] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`aa = tyvars X` >>
  `aa = [(strlit "A")]` by simp[tyvars_def,Abbr`aa`,LIST_UNION_def,LIST_INSERT_def] >>
  Q.PAT_ABBREV_TAC`tt = typesem (tyaof i) Y o TYPE_SUBST Z o Tyvar` >>
  `is_type_valuation tt` by (
    simp[Abbr`tt`,is_type_valuation_def] >>
    rw[REV_ASSOCD,typesem_def] >- (
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[is_valuation_def,is_interpretation_def] >>
      metis_tac[] ) >>
    fs[is_valuation_def,is_type_valuation_def] ) >>
  qunabbrev_tac`aa` >>
  fs[is_std_interpretation_def,interprets_def] >>
  `MAP implode (STRING_SORT ["A"]) = [strlit "A"]` by
    simp[STRING_SORT_def,INORDER_INSERT_def,mlstringTheory.implode_def] >>
  simp[] >> simp[Abbr`tt`,REV_ASSOCD]
QED

(* equations *)

Theorem termsem_equation:
   is_set_theory ^mem ⇒
    ∀sig i v s t tmenv.
    is_structure sig i v ∧
    term_ok sig (s === t) ∧
    tmenv = tmsof sig
    ⇒ termsem tmenv i v (s === t) = Boolean (termsem tmenv i v s = termsem tmenv i v t)
Proof
  rw[] >>
  `is_std_sig sig ∧ is_std_interpretation i` by fs[is_structure_def] >>
  fs[term_ok_equation] >>
  imp_res_tac term_ok_type_ok >>
  simp[equation_def,termsem_def,termsem_Equal] >>
  imp_res_tac is_std_interpretation_is_type >>
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- metis_tac[is_structure_def,termsem_typesem] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[termsem_typesem,boolean_in_boolset,is_structure_def] ) >>
  unabbrev_all_tac >> simp[]
QED

(* aconv *)

Theorem termsem_raconv:
   ∀env tp. RACONV env tp ⇒
      ∀Γ i v1 v2.
        (FST v1 = FST v2) ∧
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (termsem Γ i v1 (Var x1 ty1) =
             termsem Γ i v2 (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem Γ i v1 (FST tp) = termsem Γ i v2 (SND tp)
Proof
  ho_match_mp_tac RACONV_strongind >>
  rpt conj_tac >> simp[termsem_def] >>
  TRY (metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac`RACONV env1 p1` >>
  qspecl_then[`env1`,`p1`]mp_tac RACONV_TYPE >>
  simp[Abbr`env1`,Abbr`p1`] >> strip_tac >>
  rw[termsem_def] >> fs[] >> rw[] >>
  rw[FUN_EQ_THM] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[ALPHAVARS_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> fs[]
QED

Theorem termsem_aconv:
   ∀Γ i v t1 t2. ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 ⇒ termsem Γ i v t1 = termsem Γ i v t2
Proof
  rw[ACONV_def] >>
  imp_res_tac termsem_raconv >>
  rfs[ALPHAVARS_def] >>
  metis_tac[ACONV_def]
QED

(* semantics only depends on valuation of free variables *)

Theorem termsem_frees:
   ∀Γ i t v1 v2.
      welltyped t ∧ FST v1 = FST v2 ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ SND v1 (x,ty) = SND v2 (x,ty))
      ⇒ termsem Γ i v1 t = termsem Γ i v2 t
Proof
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def] >- metis_tac[] >>
  rw[] >> rw[termsem_def] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum match_mp_tac >>
  rw[combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM] >>
  first_x_assum match_mp_tac >> fs[]
QED

Theorem typesem_frees:
   ∀ty τ1 τ2 δ.
      (∀a. MEM a (tyvars ty) ⇒ τ1 a = τ2 a) ⇒
      typesem δ τ1 ty = typesem δ τ2 ty
Proof
  ho_match_mp_tac type_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,typesem_def,PULL_EXISTS] >>
  rw[] >> rpt AP_TERM_TAC >> simp[MAP_EQ_f] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem termsem_tyfrees:
   ∀Γ i t v1 v2 tmenv.
      term_ok Γ t ∧
      SND v1 = SND v2 ∧
      (∀a. MEM a (tvars t) ⇒ FST v1 a = FST v2 a) ∧
      tmenv = tmsof Γ
      ⇒ termsem tmenv i v1 t = termsem tmenv i v2 t
Proof
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def,tvars_def,term_ok_def] >- (
    rw[] >>
    qmatch_abbrev_tac`instance (tmsof Γ) i name ty τ = X` >>
    qspecl_then[`tmsof Γ`,`i`,`name`,`ty`]mp_tac instance_def >>
    simp[Abbr`ty`,Abbr`X`] >> disch_then kall_tac >>
    rpt AP_TERM_TAC >> simp[FUN_EQ_THM,MAP_EQ_f] >> rw[] >>
    match_mp_tac typesem_frees >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[tyvars_TYPE_SUBST] >>
    fs[MEM_MAP] >>
    metis_tac[mlstringTheory.implode_explode] ) >>
  rw[] >- (res_tac >> PROVE_TAC[]) >>
  rw[termsem_def] >> fs[tvars_def] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d1 = d2 ∧ r1 = r2` by (
    unabbrev_all_tac >> rw[]  >>
    match_mp_tac typesem_tyvars >>
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF,term_ok_welltyped,WELLTYPED] ) >>
  rw[] >> rpt AP_TERM_TAC >>
  unabbrev_all_tac >> rw[FUN_EQ_THM]
QED

(* semantics of substitution *)

Theorem termsem_simple_subst:
   ∀tm ilist.
      welltyped tm ∧
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      ∀Γ i v.
        termsem Γ i v (simple_subst ilist tm) =
        termsem Γ i
          (FST v, SND v =++
                  MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist))
          tm
Proof
  Induct >> simp[termsem_def] >- (
    simp[REV_ASSOCD_ALOOKUP,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >> BasicProvers.CASE_TAC >> rw[termsem_def] >- (
      imp_res_tac ALOOKUP_FAILS >>
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      res_tac >> fs[] >> metis_tac[] ) >>
    rw[GSYM MAP_MAP_o] >>
    qmatch_assum_abbrev_tac`ALOOKUP ls (Var s ty) = SOME x` >>
    Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`s`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
    impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[]) >>
  rw[] >>
  Q.PAT_ABBREV_TAC`il = FILTER X ilist` >>
  qmatch_assum_rename_tac`welltyped tm` >>
  `simple_subst il tm has_type typeof tm` by (
    match_mp_tac (MP_CANON simple_subst_has_type) >>
    imp_res_tac WELLTYPED >>
    fs[Abbr`il`,EVERY_MEM,EVERY_FILTER,FORALL_PROD] >>
    rw[] >> res_tac >> rw[] ) >>
  imp_res_tac WELLTYPED_LEMMA >> rw[] >>
  simp[termsem_def] >>
  rpt AP_TERM_TAC >> simp[FUN_EQ_THM] >> rw[] >>
  qmatch_abbrev_tac `termsem Γ i vv xx = yy` >>
  first_x_assum(qspec_then`il`mp_tac) >>
  impl_tac >- (
    simp[Abbr`il`] >> fs[IN_DISJOINT,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  disch_then(qspecl_then[`Γ`,`i`,`vv`]mp_tac) >>
  rw[Abbr`vv`,Abbr`yy`] >>
  rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
  simp[FUN_EQ_THM,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
  Cases >>
  simp[GSYM MAP_MAP_o] >>
  BasicProvers.CASE_TAC >>
  qmatch_assum_abbrev_tac`ALOOKUP (MAP (dest_var ## f) ls) (z,tyr) = X` >>
  qunabbrev_tac`X` >>
  Q.ISPECL_THEN[`ls`,`f`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
  (impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`,Abbr`il`,MEM_FILTER] >> metis_tac[])) >>
  qmatch_assum_abbrev_tac`Abbrev(il = FILTER P ilist)` >>
  qmatch_assum_abbrev_tac`Abbrev(ls = MAP sw il)` >>
  `ls = FILTER (P o sw) (MAP sw ilist)` by (
    simp[Abbr`ls`,Abbr`il`] >>
    simp[rich_listTheory.FILTER_MAP] >>
    simp[Abbr`P`,Abbr`sw`,combinTheory.o_DEF,UNCURRY,LAMBDA_PROD] ) >>
  qunabbrev_tac`ls` >>
  simp[ALOOKUP_FILTER,Abbr`P`,Abbr`sw`,combinTheory.o_DEF,LAMBDA_PROD] >- (
    rw[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
    qmatch_assum_abbrev_tac`P ⇒ ALOOKUP ls vv = NONE` >>
    Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
    impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[] >> fs[Abbr`P`] ) >>
  simp[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
  rw[Abbr`f`] >>
  qmatch_assum_abbrev_tac`ALOOKUP ls vv = SOME zz` >>
  Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
  (impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[])) >>
  rw[] >> fs[Abbr`zz`] >>
  match_mp_tac termsem_frees >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[Abbr`ls`,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[welltyped_def]
QED

Theorem termsem_VSUBST:
    ∀tm ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      ∀Γ i v.
       termsem Γ i v (VSUBST ilist tm) =
       termsem Γ i (FST v,
                    SND v =++
                    MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist)) tm
Proof
  rw[] >>
  Q.ISPECL_THEN[`{y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (VSUBST ilist tm) (VSUBST ilist fm)` by (
    match_mp_tac ACONV_VSUBST >> metis_tac[] ) >>
  `welltyped (VSUBST ilist tm)` by metis_tac[VSUBST_WELLTYPED] >>
  `welltyped (VSUBST ilist fm)` by metis_tac[VSUBST_WELLTYPED] >>
  `termsem Γ i v (VSUBST ilist tm) = termsem Γ i v (VSUBST ilist fm)` by
    metis_tac[termsem_aconv] >>
  `VSUBST ilist fm = simple_subst ilist fm` by
    metis_tac[VSUBST_simple_subst] >>
  rw[] >>
  metis_tac[termsem_simple_subst,termsem_aconv]
QED

(* semantics of instantiation *)

Theorem termsem_simple_inst:
   ∀Γ tm tyin tmenv.
      welltyped tm ∧ term_ok Γ tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      tmenv = tmsof Γ
      ⇒
      ∀i v.
        termsem tmenv i v (simple_inst tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm
Proof
  Cases >> Induct >> simp[termsem_def,term_ok_def] >- (
    rw[] >> rw[TYPE_SUBST_compose] >>
    qmatch_abbrev_tac`instance sig int name (TYPE_SUBST i2 ty0) t1 =
                      instance sig int name (TYPE_SUBST i1 ty0) t2` >>
    qspecl_then[`sig`,`int`,`name`]mp_tac instance_def >> simp[Abbr`sig`,Abbr`t2`] >>
    disch_then kall_tac >> rpt AP_TERM_TAC >> rw[FUN_EQ_THM,MAP_EQ_f] >> rw[] >>
    rw[Once REV_ASSOCD_ALOOKUP,Abbr`i2`,ALOOKUP_APPEND,MAP_MAP_o,swap_ff] >>
    rw[ff_def,GSYM MAP_MAP_o,ALOOKUP_MAP] >>
    rw[REV_ASSOCD_ALOOKUP] >> BasicProvers.CASE_TAC >> fs[typesem_def] >>
    rw[Once typesem_TYPE_SUBST,REV_ASSOCD_ALOOKUP] )
  >- (
    rw[] >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    metis_tac[] ) >>
  rw[] >> rw[] >> rw[termsem_def] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d2 = d1` by (
    unabbrev_all_tac >>
    simp[Once typesem_TYPE_SUBST] ) >>
  qmatch_assum_rename_tac`welltyped tm` >>
  `r2 = r1` by (
    unabbrev_all_tac >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> rw[] >>
    imp_res_tac WELLTYPED_LEMMA >> rw[] >>
    simp[Once typesem_TYPE_SUBST] ) >>
  rw[] >> rpt AP_TERM_TAC >>
  unabbrev_all_tac >> rw[FUN_EQ_THM] >>
  first_x_assum(qspec_then`tyin`mp_tac) >> simp[] >>
  impl_tac >- ( fs[IN_DISJOINT] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac termsem_frees >>
  rw[] >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem termsem_INST:
   ∀Γ tm tyin tmenv.
      term_ok Γ tm ∧ tmenv = tmsof Γ ⇒
      ∀i v.
        termsem tmenv i v (INST tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm
Proof
  rw[] >> imp_res_tac term_ok_welltyped >>
  Q.ISPECL_THEN[`{x | ∃ty. VFREE_IN (Var x ty) tm}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (INST tyin tm) (INST tyin fm)` by (
    match_mp_tac ACONV_INST >> metis_tac[] ) >>
  `welltyped (INST tyin tm)` by metis_tac[INST_WELLTYPED] >>
  `welltyped (INST tyin fm)` by metis_tac[INST_WELLTYPED] >>
  `termsem tmenv i v (INST tyin tm) = termsem tmenv i v (INST tyin fm)` by
    metis_tac[termsem_aconv] >>
  `{x | ∃ty. VFREE_IN (Var x ty) tm} = {x | ∃ty. VFREE_IN (Var x ty) fm}` by (
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `INST tyin fm = simple_inst tyin fm` by
    metis_tac[INST_simple_inst] >>
  rw[] >>
  metis_tac[SIMP_RULE(srw_ss())[]termsem_simple_inst,termsem_aconv,term_ok_aconv]
QED

(* extending the context doesn't change the semantics *)

Theorem termsem_extend:
   ∀tyenv tmenv tyenv' tmenv' tm.
      tmenv ⊑ tmenv' ∧
      term_ok (tyenv,tmenv) tm ⇒
      ∀i v. termsem tmenv' i v tm =
            termsem tmenv i v tm
Proof
  ntac 4 gen_tac >> Induct >> simp[termsem_def,term_ok_def] >>
  rw[] >> simp[termsem_def] >>
  qmatch_abbrev_tac`X = instance sig int name ty t` >>
  qspecl_then[`sig`,`int`,`name`,`ty`]mp_tac instance_def >>
  fs[Abbr`sig`,Abbr`ty`,Abbr`X`] >>
  disch_then kall_tac >>
  qmatch_abbrev_tac`instance sig int name ty t = X` >>
  qspecl_then[`sig`,`int`,`name`,`ty`]mp_tac instance_def >>
  imp_res_tac FLOOKUP_SUBMAP >>
  fs[Abbr`sig`,Abbr`ty`]
QED

Theorem is_valuation_reduce:
   ∀tyenv tyenv' δ v. tyenv ⊑ tyenv' ∧ is_valuation tyenv' δ v ⇒
    is_valuation tyenv δ v
Proof
  rw[is_valuation_def,is_term_valuation_def] >>
  metis_tac[type_ok_extend]
QED

Theorem satisfies_extend:
   ∀tyenv tmenv tyenv' tmenv' tm i h c.
      tmenv ⊑ tmenv' ∧ tyenv ⊑ tyenv' ∧
      EVERY (term_ok (tyenv,tmenv)) (c::h) ∧
      i satisfies ((tyenv,tmenv),h,c) ⇒
      i satisfies ((tyenv',tmenv'),h,c)
Proof
  rw[satisfies_def] >> fs[EVERY_MEM] >>
  metis_tac[term_ok_extend,termsem_extend,is_valuation_reduce]
QED

(* one interpretation being compatible with another in a signature *)

val equal_on_def = Define`
  equal_on (sig:sig) i i' ⇔
  (∀name. name ∈ FDOM (tysof sig) ⇒ tyaof i' name = tyaof i name) ∧
  (∀name. name ∈ FDOM (tmsof sig) ⇒ tmaof i' name = tmaof i name)`

Theorem equal_on_refl:
   ∀sig i. equal_on sig i i
Proof
  rw[equal_on_def]
QED

Theorem equal_on_sym:
   ∀sig i i'. equal_on sig i i' ⇒ equal_on sig i' i
Proof
  rw[equal_on_def] >> PROVE_TAC[]
QED

Theorem equal_on_trans:
   ∀sig i1 i2 i3. equal_on sig i1 i2 ∧ equal_on sig i2 i3
    ⇒ equal_on sig i1 i3
Proof
  rw[equal_on_def] >> metis_tac[]
QED

Theorem equal_on_interprets:
   ∀sig i1 i2 name args ty m.
      equal_on sig i1 i2 ∧
      tmaof i1 interprets name on args as m ∧
      (FLOOKUP (tmsof sig) name = SOME ty) ∧
      type_ok (tysof sig) ty ∧
      (set (tyvars ty) = set args) ⇒
      tmaof i2 interprets name on args as m
Proof
  rw[equal_on_def,interprets_def] >>
  qsuff_tac`tmaof i2 name = tmaof i1 name` >- metis_tac[] >>
  first_x_assum match_mp_tac >>
  fs[FLOOKUP_DEF]
QED

Theorem equal_on_reduce:
   ∀ls ctxt i i'. equal_on (sigof (ls++ctxt)) i i' ∧
                 DISJOINT (FDOM (tysof ls)) (FDOM (tysof ctxt)) ∧
                 DISJOINT (FDOM (tmsof ls)) (FDOM (tmsof ctxt))
    ⇒ equal_on (sigof ctxt) i i'
Proof
  rw[equal_on_def]
QED

(* semantics only depends on interpretation of things in the term's signature *)

Theorem typesem_sig:
   ∀ty τ δ δ' tyenv. type_ok tyenv ty ∧ (∀name. name ∈ FDOM tyenv ⇒ δ' name = δ name) ⇒
                    typesem δ' τ ty = typesem δ τ ty
Proof
  ho_match_mp_tac type_ind >> simp[typesem_def,type_ok_def] >> rw[] >>
  qmatch_abbrev_tac`δ' name args1 = δ name args2` >>
  `args1 = args2` by (
    unabbrev_all_tac >>
    simp[MAP_EQ_f] >>
    fs[EVERY_MEM] >>
    metis_tac[] ) >>
  simp[] >> AP_THM_TAC >>
  first_x_assum match_mp_tac >>
  fs[FLOOKUP_DEF]
QED

Theorem termsem_sig:
   ∀tm Γ i v i' tmenv.
      is_std_sig Γ ∧ term_ok Γ tm ∧ tmenv = tmsof Γ ∧ equal_on Γ i i'
      ⇒
      termsem tmenv i' v tm = termsem tmenv i v tm
Proof
  REWRITE_TAC[equal_on_def] >>
  Induct >> simp[termsem_def] >- (
    rw[term_ok_def] >>
    imp_res_tac instance_def >>
    qmatch_abbrev_tac`instance tmenv i' s ty τ = X` >>
    qmatch_assum_abbrev_tac`Abbrev(ty = TYPE_SUBST tyin ty0)` >>
    first_x_assum(qspecl_then[`tyin`,`ty`]mp_tac) >>
    simp[Abbr`X`,Abbr`ty`] >> disch_then kall_tac >>
    qmatch_abbrev_tac`f1 x1 = f2 x2` >>
    `x1 = x2` by (
      unabbrev_all_tac >>
      simp[FUN_EQ_THM,MAP_EQ_f] >>
      rw[] >>
      match_mp_tac typesem_sig >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      fs[MEM_MAP,mlstringTheory.implode_explode,FLOOKUP_DEF] >>
      metis_tac[] ) >>
    simp[] >> AP_THM_TAC >>
    unabbrev_all_tac >>
    fs[FLOOKUP_DEF]) >>
  fs[term_ok_def] >- (fs[FORALL_PROD] >> rw[] >> res_tac >> PROVE_TAC[]) >>
  rw[term_ok_def] >>
  simp[termsem_def] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d1 = d2 ∧ r1 = r2` by (
    unabbrev_all_tac >> rw[] >>
    match_mp_tac typesem_sig >>
    metis_tac[term_ok_type_ok] ) >>
  simp[] >> rpt AP_TERM_TAC >> rw[FUN_EQ_THM] >>
  unabbrev_all_tac >> fs[] >>
  fs[FORALL_PROD] >> res_tac >> fs[]
QED

Theorem satisfies_sig:
   ∀i i' sig h c.
    is_std_sig sig ∧
    EVERY (term_ok sig) (c::h) ∧
    equal_on sig i i' ∧
    i satisfies (sig,h,c)
    ⇒
    i' satisfies (sig,h,c)
Proof
  rw[satisfies_def] >>
  qsuff_tac`termsem (tmsof sig) i v c = True` >- metis_tac[termsem_sig] >>
  first_x_assum match_mp_tac >>
  reverse conj_tac >- ( fs[EVERY_MEM] >> metis_tac[termsem_sig] ) >>
  fs[is_valuation_def] >>
  fs[is_term_valuation_def] >>
  metis_tac[typesem_sig,equal_on_def]
QED

(* valuations exist *)

Theorem term_valuation_exists:
   is_set_theory ^mem ⇒
    ∀tyenv δ τ. is_type_valuation τ ∧ is_type_assignment tyenv δ ⇒
      ∃σ. is_valuation tyenv δ (τ,σ)
Proof
  rw[is_valuation_def,is_term_valuation_def] >>
  qexists_tac`λ(x,ty). @v. v <: typesem δ τ ty` >> rw[] >>
  metis_tac[typesem_inhabited]
QED

val is_type_valuation_exists = Q.prove(
  `is_set_theory ^mem ⇒ is_type_valuation (K boolset)`,
  simp[is_type_valuation_def] >> metis_tac[boolean_in_boolset]) |> UNDISCH

Theorem valuation_exists:
   is_set_theory ^mem ⇒
    ∀tyenv δ. is_type_assignment tyenv δ ⇒
      ∃v. is_valuation tyenv δ v
Proof
  rw[is_valuation_def] >>
  qexists_tac`K boolset, λ(x,ty). @v. v <: typesem δ (K boolset) ty` >>
  conj_asm1_tac >- simp[is_type_valuation_exists] >>
  fs[is_term_valuation_def] >> metis_tac[typesem_inhabited]
QED

Theorem extend_valuation_exists:
   is_set_theory ^mem ⇒
    ∀tysig δ v tysig'.
    is_valuation tysig δ v ∧ tysig ⊑ tysig' ∧
    is_type_assignment tysig' δ ⇒
    ∃v'. is_valuation tysig' δ v' ∧
         (tyvof v' = tyvof v) ∧
         (∀x ty. type_ok tysig ty ⇒ (tmvof v (x,ty) = tmvof v' (x,ty)))
Proof
  rw[] >> simp[EXISTS_PROD] >>
  fs[is_valuation_def,is_term_valuation_def] >>
  qexists_tac`λ(x,ty).
    if type_ok tysig ty then tmvof v (x,ty)
    else @m. m <: typesem δ (tyvof v) ty` >>
  rw[] >> metis_tac[typesem_inhabited]
QED

Theorem is_type_valuation_UPDATE_LIST:
   ∀t ls. is_type_valuation t ∧ EVERY (inhabited o SND) ls ⇒
           is_type_valuation (t =++ ls)
Proof
  rw[is_type_valuation_def,APPLY_UPDATE_LIST_ALOOKUP] >>
  BasicProvers.CASE_TAC >> rw[] >> imp_res_tac ALOOKUP_MEM >>
  fs[EVERY_MEM,FORALL_PROD] >> metis_tac[]
QED

(* identity instance *)

Theorem identity_instance:
   ∀tmenv (i:'U interpretation) name ty τ. FLOOKUP tmenv name = SOME ty ⇒
      instance tmenv i name ty = λτ. tmaof i name (MAP τ (MAP implode (STRING_SORT (MAP explode (tyvars ty)))))
Proof
  rw[] >>
  qspecl_then[`tmenv`,`i`,`name`,`ty`,`ty`,`[]`]mp_tac instance_def >>
  rw[FUN_EQ_THM,typesem_def,combinTheory.o_DEF,ETA_AX]
QED

(* special cases of interprets *)

val rwt = MATCH_MP (PROVE[]``P x ⇒ ((∀x. P x ⇒ Q) ⇔ Q)``) is_type_valuation_exists
val interprets_nil = save_thm("interprets_nil",
  interprets_def |> SPEC_ALL |> Q.GEN`vs` |> Q.SPEC`[]`
  |> SIMP_RULE (std_ss++listSimps.LIST_ss) [rwt] |> GEN_ALL)

Theorem interprets_one:
   i interprets name on [v] as f ⇔
    (∀x. inhabited x ⇒ (i name [x] = f [x]))
Proof
  rw[interprets_def,EQ_IMP_THM] >>
  TRY (
    first_x_assum match_mp_tac >>
    fs[is_type_valuation_def] ) >>
  first_x_assum(qspec_then`K x`mp_tac) >>
  simp[] >> disch_then match_mp_tac >>
  rw[is_type_valuation_def] >> metis_tac[]
QED

(* for models, reducing the context *)

Theorem is_type_assignment_reduce:
   ∀tyenv tyenv' δ.
     tyenv ⊑ tyenv' ∧
     is_type_assignment tyenv' δ ⇒
     is_type_assignment tyenv δ
Proof
  rw[is_type_assignment_def] >>
  imp_res_tac FEVERY_SUBMAP
QED

Theorem is_term_assignment_reduce:
   ∀tmenv tmenv' δ γ.
     tmenv ⊑ tmenv' ∧
     is_term_assignment tmenv' δ γ ⇒
     is_term_assignment tmenv δ γ
Proof
   rw[is_term_assignment_def] >>
   imp_res_tac FEVERY_SUBMAP
QED

Theorem is_interpretation_reduce:
   ∀i tyenv tmenv tyenv' tmenv'.
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧
     is_interpretation (tyenv',tmenv') i ⇒
     is_interpretation (tyenv,tmenv) i
Proof
  Cases >> rw[is_interpretation_def] >>
  imp_res_tac is_type_assignment_reduce >>
  imp_res_tac is_term_assignment_reduce
QED

Theorem is_valuation_extend_sig:
   is_set_theory ^mem ⇒
    ∀tyenv tyenv' tyass v.
    is_valuation tyenv tyass v ∧
    is_type_assignment tyenv' tyass ∧
    tyenv ⊑ tyenv' ⇒
    ∃v'.
      (tyvof v' = tyvof v) ∧
      (∀ty. type_ok tyenv ty ⇒ ∀x. tmvof v' (x,ty) = tmvof v (x,ty)) ∧
      is_valuation tyenv' tyass v'
Proof
  rw[is_valuation_def] >>
  fs[is_term_valuation_def] >>
  simp[EXISTS_PROD] >>
  qexists_tac`λp. if type_ok tyenv (SND p) then tmvof v p else @m. m <: typesem tyass (tyvof v) (SND p)` >>
  simp[] >> rw[] >>
  SELECT_ELIM_TAC >> simp[] >>
  match_mp_tac (UNDISCH typesem_inhabited) >>
  metis_tac[]
QED

Theorem satisfies_reduce:
   is_set_theory ^mem ⇒
    ∀i tyenv tmenv tyenv' tmenv' h c.
      is_std_sig (tyenv,tmenv) ∧
      tyenv ⊑ tyenv' ∧
      tmenv ⊑ tmenv' ∧
      EVERY (term_ok (tyenv,tmenv)) (c::h) ∧
      is_type_assignment tyenv' (tyaof i) ∧
      i satisfies ((tyenv',tmenv'),h,c) ⇒
      i satisfies ((tyenv,tmenv),h,c)
Proof
  rw[satisfies_def] >>
  qspecl_then[`tyenv`,`tyenv'`,`tyaof i`,`v`]mp_tac (UNDISCH is_valuation_extend_sig) >>
  simp[] >> strip_tac >>
  first_x_assum(qspec_then`v'`mp_tac) >> simp[] >>
  `∀tm. term_ok (tyenv,tmenv) tm ⇒
     termsem tmenv' i v' tm = termsem tmenv i v tm` by (
    rw[] >>
    match_mp_tac EQ_TRANS >>
    qexists_tac`termsem tmenv' i v tm` >>
    reverse conj_tac >- metis_tac[termsem_extend] >>
    match_mp_tac termsem_frees >>
    imp_res_tac term_ok_welltyped >>
    simp[] >> rw[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac type_ok_types_in >> fs[] >>
    last_x_assum match_mp_tac >>
    imp_res_tac VFREE_IN_types_in >>
    fs[] ) >>
  impl_tac >- ( fs[EVERY_MEM] ) >>
  simp[]
QED

Theorem models_reduce:
   is_set_theory ^mem ⇒
    ∀i tyenv tmenv axs tyenv' tmenv' axs'.
     is_std_sig (tyenv,tmenv) ∧
     tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧ (axs ⊆ axs') ∧
     i models ((tyenv',tmenv'),axs') ∧
     (∀p. p ∈ axs ⇒ (term_ok (tyenv,tmenv)) p)
     ⇒
     i models ((tyenv,tmenv),axs)
Proof
  strip_tac >>
  Cases >> rw[models_def] >>
  imp_res_tac is_interpretation_reduce >>
  fs[SUBSET_DEF] >>
  match_mp_tac(MP_CANON satisfies_reduce) >>
  simp[] >> fs[is_interpretation_def] >>
  metis_tac[]
QED

val _ = export_theory()
