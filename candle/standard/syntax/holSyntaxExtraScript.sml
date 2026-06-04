(*
  Some lemmas about the syntactic functions.
*)
Theory holSyntaxExtra
Ancestors
  toto comparison ternaryComparisons mlstring holSyntaxLib
  holSyntax
Libs
  preamble

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val cpn_distinct = TypeBase.distinct_of ``:ordering``
val cpn_nchotomy = TypeBase.nchotomy_of ``:ordering``

Theorem type_ind =
  TypeBase.induction_of``:holSyntax$type``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE std_ss [EVERY_DEF]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

Theorem type1_size_append:
   ∀l1 l2. type1_size (l1 ++ l2) = type1_size l1 + type1_size l2
Proof
  Induct >> simp[type_size_def]
QED

Theorem extends_ind:
   ∀P. (∀upd ctxt. upd updates ctxt ∧ P ctxt ⇒ P (upd::ctxt)) ⇒
    ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ P ctxt1 ⇒ P ctxt2
Proof
  gen_tac >> strip_tac >>
  simp[extends_def] >>
  CONV_TAC SWAP_FORALL_CONV >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >> first_x_assum match_mp_tac >>
  rw[]
QED

(* deconstructing variables *)

Theorem ALOOKUP_MAP_dest_var:
   ∀ls f x ty.
      EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ls) ⇒
      ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (Var x ty))
Proof
  Induct >> simp[] >> Cases >> simp[EVERY_MEM,EVERY_MAP] >>
  rw[] >> fs[]
QED

(* type substitution *)

Theorem TYPE_SUBST_NIL[simp]:
   ∀ty. TYPE_SUBST [] ty = ty
Proof
  ho_match_mp_tac type_ind >>
  rw[REV_ASSOCD,MAP_EQ_ID] >>
  fs[EVERY_MEM]
QED

Theorem TYPE_SUBST_Bool:
   ∀tyin. TYPE_SUBST tyin Bool = Bool
Proof
rw[TYPE_SUBST_def]
QED

Theorem is_instance_refl[simp]:
   ∀ty. is_instance ty ty
Proof
  rw[] >> qexists_tac`[]` >> rw[]
QED

Theorem swap_ff:
   ∀f g. (λ(x,y). (y,x)) o (f ## g) = (g ## f) o (λ(x,y). (y,x))
Proof
  rw[FUN_EQ_THM,FORALL_PROD]
QED

Theorem ff_def:
   ∀f g. (f ## g) = λ(x,y). (f x, g y)
Proof
  rw[FUN_EQ_THM,FORALL_PROD,PAIR_MAP_THM]
QED

Theorem TYPE_SUBST_compose:
   ∀tyin1 ty tyin2.
    TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
    TYPE_SUBST ((MAP (TYPE_SUBST tyin2 ## I) tyin1) ++ tyin2) ty
Proof
  ho_match_mp_tac TYPE_SUBST_ind >>
  rw[TYPE_SUBST_def,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f] >>
  rw[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
  simp[MAP_MAP_o,swap_ff] >> simp[GSYM MAP_MAP_o] >>
  simp[ff_def,ALOOKUP_MAP] >>
  BasicProvers.CASE_TAC >> simp[TYPE_SUBST_def,REV_ASSOCD_ALOOKUP]
QED

Theorem TYPE_SUBST_tyvars:
   ∀ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ⇔
    ∀x. MEM x (tyvars ty) ⇒
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin  (Tyvar x)
Proof
  ho_match_mp_tac type_ind >>
  simp[tyvars_def] >>
  conj_tac >- metis_tac[] >>
  Induct >> simp[] >>
  gen_tac >> strip_tac >> fs[] >>
  rpt gen_tac >> EQ_TAC >> strip_tac >> fs[] >>
  fs[MEM_LIST_UNION] >> metis_tac[]
QED

(* Welltyped terms *)

Theorem WELLTYPED_LEMMA:
   ∀tm ty. tm has_type ty ⇒ (typeof tm = ty)
Proof
  ho_match_mp_tac has_type_ind >>
  simp[typeof_def,has_type_rules,codomain_def]
QED

Theorem WELLTYPED:
   ∀tm. welltyped tm ⇔ tm has_type (typeof tm)
Proof
  simp[welltyped_def] >> metis_tac[WELLTYPED_LEMMA]
QED

Theorem WELLTYPED_CLAUSES[simp]:
  (!n ty. welltyped(Var n ty)) /\
   (!n ty. welltyped(Const n ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!v t. welltyped (Abs v t) = ∃n ty. v = Var n ty ∧ welltyped t)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[welltyped_def] THEN
  rw[Once has_type_cases] >>
  metis_tac[WELLTYPED,WELLTYPED_LEMMA]
QED

(* Alpha-equivalence *)

Theorem RACONV:
  (RACONV env (Var x1 ty1,Var x2 ty2) <=>
        ALPHAVARS env (Var x1 ty1,Var x2 ty2)) /\
   (RACONV env (Var x1 ty1,Const x2 ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1 ty1,Abs v2 t2) <=> F) /\
   (RACONV env (Const x1 ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Const x1 ty1,Const x2 ty2) <=> (x1 = x2) /\ (ty1 = ty2)) /\
   (RACONV env (Const x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Const x1 ty1,Abs v2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Const x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Abs v2 t2) <=> F) /\
   (RACONV env (Abs v1 t1,Var x2 ty2) <=> F) /\
   (RACONV env (Abs v1 t1,Const x2 ty2) <=> F) /\
   (RACONV env (Abs v1 t1,Comb l2 r2) <=> F) /\
   (RACONV env (Abs v1 t1,Abs v2 t2) <=>
          typeof v1 = typeof v2 /\
          RACONV (CONS (v1,v2) env) (t1,t2))
Proof
  REPEAT CONJ_TAC THEN simp[Once RACONV_cases] >> metis_tac[]
QED

Theorem RACONV_REFL:
   ∀t env. EVERY (UNCURRY $=) env ⇒ RACONV env (t,t)
Proof
  Induct >> simp[RACONV,ALPHAVARS_REFL]
QED

Theorem ACONV_REFL[simp]:
   ∀t. ACONV t t
Proof
  simp[ACONV_def,RACONV_REFL]
QED

Theorem RACONV_TRANS:
   ∀env tp. RACONV env tp ⇒ ∀vs t. LENGTH vs = LENGTH env ∧ RACONV (ZIP(MAP SND env,vs)) (SND tp,t) ⇒ RACONV (ZIP(MAP FST env,vs)) (FST tp, t)
Proof
  ho_match_mp_tac RACONV_ind >> simp[RACONV] >>
  conj_tac >- (
    Induct >- simp[ALPHAVARS_def] >>
    Cases >> simp[ALPHAVARS_def] >>
    rw[] >> Cases_on`vs`>>fs[] >>
    Cases_on`t`>>fs[RACONV]>>
    fs[ALPHAVARS_def] >> rw[] >>
    metis_tac[RACONV] ) >>
  conj_tac >- ( rw[] >> Cases_on`t`>>fs[RACONV] ) >>
  conj_tac >- ( rw[] >> Cases_on`t`>>fs[RACONV] ) >>
  rw[] >>
  Cases_on`t`>>fs[RACONV]>>rw[]>>
  metis_tac[LENGTH,ZIP]
QED

Theorem ACONV_TRANS:
   ∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3
Proof
  rw[ACONV_def] >> imp_res_tac RACONV_TRANS >> fs[LENGTH_NIL]
QED

Theorem RACONV_SYM:
   ∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp)
Proof
  ho_match_mp_tac RACONV_ind >> simp[] >>
  conj_tac >- (
    Induct >> simp[ALPHAVARS_def,RACONV] >>
    Cases >> simp[] >>
    rw[] >> res_tac >> fs[RACONV]) >>
  simp[RACONV]
QED

Theorem ACONV_SYM:
   ∀t1 t2. ACONV t1 t2 ⇒ ACONV t2 t1
Proof
  rw[ACONV_def] >> imp_res_tac RACONV_SYM >> fs[]
QED

Theorem ALPHAVARS_TYPE:
   ∀env s t. ALPHAVARS env (s,t) ∧
              EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped s ∧ welltyped t
              ⇒ typeof s = typeof t
Proof
  Induct >> simp[ALPHAVARS_def,FORALL_PROD] >> rw[] >> rw[]
QED

Theorem RACONV_TYPE:
   ∀env p. RACONV env p
            ⇒ EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped (FST p) ∧ welltyped (SND p)
              ⇒ typeof (FST p) = typeof (SND p)
Proof
  ho_match_mp_tac RACONV_ind >>
  simp[FORALL_PROD,typeof_def,WELLTYPED_CLAUSES] >>
  rw[] >> imp_res_tac ALPHAVARS_TYPE >>
  fs[typeof_def,WELLTYPED_CLAUSES]
QED

Theorem ACONV_TYPE:
   ∀s t. ACONV s t ⇒ welltyped s ∧ welltyped t ⇒ (typeof s = typeof t)
Proof
  rw[ACONV_def] >> imp_res_tac RACONV_TYPE >> fs[]
QED

(* subtypes *)

Inductive subtype1:
  MEM a args ⇒ subtype1 a (Tyapp name args)
End

val _ = Parse.add_infix("subtype",401,Parse.NONASSOC)
Overload subtype =``RTC subtype1``

Theorem subtype_Tyvar[simp] =
  ``ty subtype (Tyvar x)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases]

Theorem subtype_Tyapp =
  ``ty subtype (Tyapp name args)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases]

Theorem subtype_type_ok:
   ∀tysig ty1 ty2. type_ok tysig ty2 ∧ ty1 subtype ty2 ⇒ type_ok tysig ty1
Proof
  gen_tac >>
  (relationTheory.RTC_lifts_invariants
    |> Q.GEN`R` |> Q.ISPEC`inv subtype1`
    |> SIMP_RULE std_ss [relationTheory.inv_MOVES_OUT,relationTheory.inv_DEF]
    |> Q.GEN`P` |> Q.ISPEC`type_ok tysig`
    |> match_mp_tac) >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  CONV_TAC SWAP_FORALL_CONV >> gen_tac >>
  ho_match_mp_tac subtype1_ind >>
  simp[type_ok_def,EVERY_MEM]
QED

(* subterms *)

Inductive subterm1:
  subterm1 t1 (Comb t1 t2) ∧
  subterm1 t2 (Comb t1 t2) ∧
  subterm1 tm (Abs v tm) ∧
  subterm1 v (Abs v tm)
End

val _ = Parse.add_infix("subterm",401,Parse.NONASSOC)
Overload subterm = ``RTC subterm1``
Theorem subterm_Var[simp] =
  ``tm subterm (Var x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]
Theorem subterm_Const[simp] =
  ``tm subterm (Const x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]

Theorem subterm_Comb =
  ``tm subterm (Comb t1 t2)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]
Theorem subterm_Abs =
  ``tm subterm (Abs v t)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]

Theorem subterm_welltyped_helper[local]:
  ∀tm ty. tm has_type ty ⇒ ∀t. t subterm tm ⇒ welltyped t
Proof
  ho_match_mp_tac has_type_strongind >>
  simp[subterm_Comb,subterm_Abs] >> rw[] >>
  rw[] >> imp_res_tac WELLTYPED_LEMMA >> simp[]
QED

Theorem subterm_welltyped =
  METIS_PROVE[subterm_welltyped_helper,welltyped_def]
    ``∀t tm. welltyped tm ∧ t subterm tm ⇒ welltyped t``

(* term ordering *)

Theorem type_lt_thm = Q.prove(
  `(type_lt (Tyvar x1) (Tyvar x2) ⇔ mlstring_lt x1 x2) ∧
    (type_lt (Tyvar _) (Tyapp _ _) ⇔ T) ∧
    (type_lt (Tyapp _ _) (Tyvar _) ⇔ F) ∧
    (type_lt (Tyapp x1 args1) (Tyapp x2 args2) ⇔
       (mlstring_lt LEX LLEX type_lt)
         (x1,args1) (x2,args2))`,
  rw[] >> rw[Once type_lt_cases])
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ

Theorem term_lt_thm = Q.prove(`
  (term_lt (Var x1 ty1) (Var x2 ty2) ⇔
     (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)) ∧
  (term_lt (Var _ _) (Const _ _) ⇔ T) ∧
  (term_lt (Var _ _) (Comb _ _) ⇔ T) ∧
  (term_lt (Var _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Const _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Const x1 ty1) (Const x2 ty2) ⇔
     (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)) ∧
  (term_lt (Const _ _) (Comb _ _) ⇔ T) ∧
  (term_lt (Const _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Comb _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Comb _ _) (Const _ _) ⇔ F) ∧
  (term_lt (Comb s1 s2) (Comb t1 t2) ⇔
     (term_lt LEX term_lt) (s1,s2) (t1,t2)) ∧
  (term_lt (Comb _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Abs _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Abs _ _) (Const _ _) ⇔ F) ∧
  (term_lt (Abs _ _) (Comb _ _) ⇔ F) ∧
  (term_lt (Abs s1 s2) (Abs t1 t2) ⇔
    (term_lt LEX term_lt) (s1,s2) (t1,t2))`,
  rw[] >> rw[Once term_lt_cases])
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ

Theorem type_cmp_refl[simp]:
   type_cmp t t = EQUAL
Proof
  rw[type_cmp_def,TO_of_LinearOrder]
QED

Theorem term_cmp_refl[simp]:
   term_cmp t t = EQUAL
Proof
  rw[term_cmp_def,TO_of_LinearOrder]
QED

Theorem irreflexive_type_lt[local]:
  irreflexive type_lt
Proof
  mp_tac StrongLinearOrder_mlstring_lt >>
  simp[StrongLinearOrder,StrongOrder,irreflexive_def] >>
  strip_tac >> ho_match_mp_tac type_ind >>
  simp[type_lt_thm,LEX_DEF] >>
  Induct >> simp[]
QED

Theorem trichotomous_type_lt[local]:
  trichotomous type_lt
Proof
  mp_tac StrongLinearOrder_mlstring_lt >>
  simp[StrongLinearOrder,trichotomous] >> strip_tac >>
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    gen_tac >> Cases >> simp[type_lt_thm] ) >>
  gen_tac >> strip_tac >> gen_tac >> Cases >> simp[type_lt_thm,LEX_DEF_THM] >>
  first_x_assum(qspecl_then[`m`,`m'`]strip_assume_tac) >> simp[] >>
  fs[StrongOrder,irreflexive_def] >> rw[] >>
  pop_assum mp_tac >>
  qspec_tac(`l'`,`l2`) >>
  Induct_on`l` >>
  Cases_on`l2`>>simp[]>>
  rw[] >> fs[] >>
  metis_tac[]
QED

Theorem transitive_type_lt[local]:
  ∀x y. type_lt x y ⇒ ∀z. type_lt y z ⇒ type_lt x z
Proof
  ho_match_mp_tac type_lt_strongind >>
  rpt conj_tac >> rpt gen_tac >> simp[PULL_FORALL] >>
  Cases_on`z` >> simp[type_lt_thm,LEX_DEF_THM] >-
    metis_tac[StrongLinearOrder_mlstring_lt,StrongLinearOrder,StrongOrder,transitive_def] >>
  strip_tac >- metis_tac[StrongLinearOrder_mlstring_lt,StrongLinearOrder,StrongOrder,transitive_def] >>
  strip_tac >- metis_tac[StrongLinearOrder_mlstring_lt,StrongLinearOrder,StrongOrder,transitive_def] >>
  rw[] >> disj2_tac >>
  fs[LLEX_EL_THM] >>
  qmatch_assum_rename_tac`n2 ≤ LENGTH args2` >>
  Cases_on`n < LENGTH args1`>>fsrw_tac[ARITH_ss][] >- (
    `EL n args1 ≠ EL n args2` by metis_tac[irreflexive_type_lt,irreflexive_def] >>
    Cases_on`n < n2` >> fsrw_tac[ARITH_ss][] >- (
      qexists_tac`n` >> simp[] >>
      conj_tac >- (
        simp[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
        rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
        first_x_assum(qspec_then`x`mp_tac) >>
        simp[rich_listTheory.EL_TAKE] ) >>
      `EL n args2 = EL n l` by (
        rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
        fs[rich_listTheory.EL_TAKE] >>
        first_x_assum(qspec_then`n`mp_tac) >>
        simp[rich_listTheory.EL_TAKE] ) >>
      metis_tac[trichotomous_type_lt,trichotomous] ) >>
    Cases_on`n = n2` >> fs[] >- (
      rw[] >> rfs[] >>
      qexists_tac`n`>>simp[] ) >>
    qexists_tac`n2`>>simp[] >>
    conj_tac >- (
      simp[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
      rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
      last_x_assum(qspec_then`x`mp_tac) >>
      simp[rich_listTheory.EL_TAKE] ) >>
    `EL n2 args1 = EL n2 args2` by (
      rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
      fs[rich_listTheory.EL_TAKE] >>
      last_x_assum(qspec_then`n2`mp_tac) >>
      simp[rich_listTheory.EL_TAKE] ) >>
    Cases_on`n2 < LENGTH args2`>>fs[]>>
    DECIDE_TAC ) >>
  `n = LENGTH args1` by DECIDE_TAC >>
  BasicProvers.VAR_EQ_TAC >> fs[] >>
  Cases_on`n2 ≤ LENGTH args1` >> fs[] >- (
    qexists_tac`n2` >> simp[] >>
    conj_tac >- (
      fs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
      rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
      last_x_assum(qspec_then`x`mp_tac) >>
      simp[rich_listTheory.EL_TAKE] ) >>
    rw[] >>
    `n2 < LENGTH args2` by simp[] >> fs[] >>
    `EL n2 args1 = EL n2 args2` by (
      fs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
      rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
      last_x_assum(qspec_then`n2`mp_tac) >>
      simp[rich_listTheory.EL_TAKE] ) >>
    fs[] ) >>
  qexists_tac`LENGTH args1` >> simp[] >>
  fs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
  rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
  `LENGTH args1 ≤ LENGTH l` by DECIDE_TAC >> simp[] >>
  simp[rich_listTheory.EL_TAKE]
QED

Theorem StrongLinearOrder_type_lt:
   StrongLinearOrder type_lt
Proof
  simp[StrongLinearOrder,StrongOrder,irreflexive_type_lt,trichotomous_type_lt] >>
  metis_tac[transitive_type_lt,transitive_def]
QED

Theorem TotOrd_type_cmp:
   TotOrd type_cmp
Proof
  rw[type_cmp_def] >>
  match_mp_tac TotOrd_TO_of_Strong >>
  ACCEPT_TAC StrongLinearOrder_type_lt
QED

Theorem irreflexive_term_lt[local]:
  irreflexive term_lt
Proof
  mp_tac StrongLinearOrder_mlstring_lt >>
  mp_tac StrongLinearOrder_type_lt >>
  simp[StrongLinearOrder,StrongOrder,irreflexive_def] >>
  ntac 2 strip_tac >> ho_match_mp_tac term_induction >>
  simp[term_lt_thm,LEX_DEF]
QED

Theorem trichotomous_term_lt[local]:
  trichotomous term_lt
Proof
  mp_tac StrongLinearOrder_mlstring_lt >>
  mp_tac StrongLinearOrder_type_lt >>
  simp[StrongLinearOrder,trichotomous] >> ntac 2 strip_tac >>
  ho_match_mp_tac term_induction >>
  rpt conj_tac >> rpt gen_tac >> TRY(strip_tac) >>
  Cases_on`b` >> simp[term_lt_thm,LEX_DEF_THM] >>
  metis_tac[]
QED

Theorem transitive_term_lt[local]:
  ∀x y. term_lt x y ⇒ ∀z. term_lt y z ⇒ term_lt x z
Proof
  ho_match_mp_tac term_lt_strongind >>
  rpt conj_tac >> rpt gen_tac >> simp[PULL_FORALL] >>
  Cases_on`z` >> simp[term_lt_thm,LEX_DEF_THM] >>
  metis_tac[StrongLinearOrder_mlstring_lt,StrongLinearOrder_type_lt,StrongLinearOrder,
            StrongOrder,transitive_def]
QED

Theorem StrongLinearOrder_term_lt:
   StrongLinearOrder term_lt
Proof
  simp[StrongLinearOrder,StrongOrder,irreflexive_term_lt,trichotomous_term_lt] >>
  metis_tac[transitive_term_lt,transitive_def]
QED

Theorem TotOrd_term_cmp:
   TotOrd term_cmp
Proof
  rw[term_cmp_def] >>
  match_mp_tac TotOrd_TO_of_Strong >>
  ACCEPT_TAC StrongLinearOrder_term_lt
QED

Theorem StrongLinearOrder_irreflexive[local]:
  StrongLinearOrder R ⇒ irreflexive R
Proof
  rw[StrongLinearOrder,StrongOrder]
QED

Theorem irreflexive_mlstring_lt[local] = MATCH_MP StrongLinearOrder_irreflexive StrongLinearOrder_mlstring_lt

Theorem LLEX_irreflexive[local]:
  ∀R. irreflexive R ⇒ irreflexive (LLEX R)
Proof
  rw[irreflexive_def] >> Induct_on`x`>>rw[]
QED

Theorem irreflexive_LLEX_type_lt[local] = MATCH_MP LLEX_irreflexive (irreflexive_type_lt)

Theorem type_cmp_thm:
   ∀t1 t2.  type_cmp t1 t2 =
    case (t1,t2) of
    | (Tyvar x1, Tyvar x2) => mlstring$compare x1 x2
    | (Tyvar _, _) => LESS
    | (_, Tyvar _) => GREATER
    | (Tyapp x1 a1, Tyapp x2 a2) => pair_cmp mlstring$compare (list_cmp type_cmp) (x1,a1) (x2,a2)
Proof
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    gen_tac >> Cases >>
    simp[type_cmp_def,TO_of_LinearOrder,type_lt_thm, mlstring_lt_def] >>
    every_case_tac >>
    assume_tac TotOrd_compare >>
    fs [TotOrd] >>
    metis_tac [cpn_distinct, cpn_nchotomy]) >>
  ntac 3 strip_tac >>
  Induct >> simp[] >>
  simp[Once type_cmp_def,TO_of_LinearOrder,type_lt_thm] >>
  simp[MATCH_MP pair_cmp_lexTO
       (CONJ TotOrd_compare (MATCH_MP TotOrd_list_cmp TotOrd_type_cmp))] >>
  simp[type_cmp_def,
       SYM(MATCH_MP TO_of_LinearOrder_LLEX irreflexive_type_lt),
       SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_mlstring_lt irreflexive_LLEX_type_lt))] >>
  simp[TO_of_LinearOrder] >>
  every_case_tac >>
  fs [mlstring_lt_def, TO_of_LinearOrder, lexTO, LEX_DEF] >>
  rw [] >>
  rfs [StrongLinearOrder_of_TO, TO_of_LinearOrder] >>
  rfs [] >>
  fs [] >>
  every_case_tac >>
  fs []
QED

Theorem type_cmp_ind:
   ∀P.
      (∀t1 t2.
        (∀x1 a1 x2 a2 x y.
          t1 = Tyapp x1 a1 ∧
          t2 = Tyapp x2 a2 ∧
          MEM x a1 ∧ MEM y a2 ⇒
          P x y)
        ⇒ P t1 t2)
      ⇒ ∀t1 t2. P t1 t2
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac type_ind >>
  rpt conj_tac >> TRY (gen_tac >> Cases >> rw[] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  ho_match_mp_tac type_ind >> rw[] >>
  first_x_assum match_mp_tac >> simp[] >>
  fs[EVERY_MEM]
QED

Theorem term_cmp_thm:
   ∀t1 t2. term_cmp t1 t2 =
    case (t1,t2) of
    | (Var x1 ty1, Var x2 ty2) => pair_cmp mlstring$compare type_cmp (x1,ty1) (x2,ty2)
    | (Var _ _, _) => LESS
    | (_, Var _ _) => GREATER
    | (Const x1 ty1, Const x2 ty2) => pair_cmp mlstring$compare type_cmp (x1,ty1) (x2,ty2)
    | (Const _ _, _) => LESS
    | (_, Const _ _) => GREATER
    | (Comb s1 t1, Comb s2 t2) => pair_cmp term_cmp term_cmp (s1,t1) (s2,t2)
    | (Comb _ _, _) => LESS
    | (_, Comb _ _) => GREATER
    | (Abs s1 t1, Abs s2 t2) => pair_cmp term_cmp term_cmp (s1,t1) (s2,t2)
    | (Abs _ _, _) => LESS
    | (_, Abs _ _) => GREATER
Proof
  ho_match_mp_tac term_induction >>
  conj_tac >- (
    ntac 2 gen_tac >> Cases >>
    simp[term_cmp_def,TO_of_LinearOrder,term_lt_thm,
         MATCH_MP pair_cmp_lexTO (CONJ TotOrd_compare TotOrd_type_cmp)] >>
    simp[type_cmp_def,TO_of_LinearOrder,
         SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_mlstring_lt
         irreflexive_type_lt))] >>
    every_case_tac >>
    fs [mlstring_lt_def, TO_of_LinearOrder, lexTO, LEX_DEF] >>
    rw [] >>
    rfs [StrongLinearOrder_of_TO, TO_of_LinearOrder] >>
    every_case_tac >>
    fs []) >>
  conj_tac >- (
    ntac 2 gen_tac >> Cases >>
    simp[term_cmp_def,TO_of_LinearOrder,term_lt_thm,
         MATCH_MP pair_cmp_lexTO (CONJ TotOrd_compare TotOrd_type_cmp)] >>
    simp[type_cmp_def,TO_of_LinearOrder,
         SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_mlstring_lt irreflexive_type_lt))] >>
    every_case_tac >>
    fs [mlstring_lt_def, TO_of_LinearOrder, lexTO, LEX_DEF] >>
    rw [] >>
    rfs [StrongLinearOrder_of_TO, TO_of_LinearOrder] >>
    every_case_tac >>
    fs []) >>
  conj_tac >- (
    ntac 2 gen_tac >> strip_tac >>
    Cases >> fs[term_cmp_def,TO_of_LinearOrder,term_lt_thm]>>
    simp[GSYM term_cmp_def,MATCH_MP pair_cmp_lexTO (CONJ TotOrd_term_cmp TotOrd_term_cmp)] >>
    simp[term_cmp_def, TO_of_LinearOrder,
         SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_term_lt irreflexive_term_lt))] ) >>
  ntac 2 gen_tac >> strip_tac >>
  Cases >> fs[term_cmp_def,TO_of_LinearOrder,term_lt_thm]>>
  simp[GSYM term_cmp_def,MATCH_MP pair_cmp_lexTO (CONJ TotOrd_term_cmp TotOrd_term_cmp)] >>
  simp[term_cmp_def, TO_of_LinearOrder,
       SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_term_lt irreflexive_term_lt))]
QED

Theorem term_cmp_ind:
   ∀P.
      (∀t1 t2.
        (∀x1 y1 x2 y2.
          t1 = Comb x1 y1 ∧ t2 = Comb x2 y2 ⇒
            P x1 x2) ∧
        (∀x1 y1 x2 y2.
          t1 = Comb x1 y1 ∧ t2 = Comb x2 y2 ⇒
            P y1 y2) ∧
        (∀x1 y1 x2 y2.
          t1 = Abs x1 y1 ∧ t2 = Abs x2 y2 ⇒
            P x1 x2) ∧
        (∀x1 y1 x2 y2.
          t1 = Abs x1 y1 ∧ t2 = Abs x2 y2 ⇒
            P y1 y2)
        ⇒ P t1 t2)
      ⇒ ∀t1 t2. P t1 t2
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac term_induction >>
  rpt conj_tac >>
  TRY( ntac 2 gen_tac >> Cases >> simp[] >> NO_TAC ) >>
  ntac 3 strip_tac >> Cases >> simp[]
QED

(* alpha ordering *)

Theorem ALPHAVARS_ordav[local]:
  ∀env tp. ALPHAVARS env tp ⇒ ordav env (FST tp) (SND tp) = EQUAL
Proof
  Induct >> rw[ALPHAVARS_def,ordav_def] >>
  Cases_on`h`>>rw[ordav_def] >> fs[] >>
  rfs[term_cmp_def,TO_of_LinearOrder] >>
  ntac 2 (pop_assum mp_tac) >> rw[]
QED

Theorem ordav_ALPHAVARS[local]:
  ∀env t1 t2. ordav env t1 t2 = EQUAL ⇒ ALPHAVARS env (t1,t2)
Proof
  ho_match_mp_tac ordav_ind >>
  rw[ALPHAVARS_def,ordav_def] >>
  fs[term_cmp_def,TO_of_LinearOrder] >>
  rpt(pop_assum mp_tac) >> rw[]
QED

Theorem ALPHAVARS_eq_ordav:
   ∀env t1 t2. ALPHAVARS env (t1,t2) ⇔ ordav env t1 t2 = EQUAL
Proof
  metis_tac[ALPHAVARS_ordav,ordav_ALPHAVARS,pair_CASES,FST,SND]
QED

Theorem RACONV_orda[local]:
  ∀env tp. RACONV env tp ⇒ orda env (FST tp) (SND tp) = EQUAL
Proof
  ho_match_mp_tac RACONV_ind >> rw[ALPHAVARS_eq_ordav]
  >- rw[orda_def] >- rw[orda_def] >- rw[Once orda_def] >>
  rw[Once orda_def]
QED

Theorem orda_RACONV[local]:
  ∀env t1 t2. orda env t1 t2 = EQUAL ⇒ RACONV env (t1,t2)
Proof
  ho_match_mp_tac orda_ind >> rw[] >>
  reverse(Cases_on`t1 ≠ t2 ∨ env ≠ []`) >- (
    fs[RACONV_REFL] ) >>
  qmatch_assum_abbrev_tac`p` >> fs[] >>
  qhdtm_x_assum`orda`mp_tac >>
  simp[Once orda_def] >>
  rw[] >- fs[markerTheory.Abbrev_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  rw[RACONV,ALPHAVARS_eq_ordav] >>
  TRY (
    qhdtm_x_assum`term_cmp`mp_tac >>
    rw[term_cmp_def,TO_of_LinearOrder] >>
    NO_TAC) >> fs[] >>
  qhdtm_x_assum`type_cmp`mp_tac >>
  rw[type_cmp_def,TO_of_LinearOrder]
QED

Theorem RACONV_eq_orda:
   ∀env t1 t2. RACONV env (t1,t2) ⇔ orda env t1 t2 = EQUAL
Proof
  metis_tac[RACONV_orda,orda_RACONV,pair_CASES,FST,SND]
QED

Theorem ACONV_eq_orda:
   ∀t1 t2. ACONV t1 t2 = (orda [] t1 t2 = EQUAL)
Proof
  rw[ACONV_def,RACONV_eq_orda]
QED

Theorem ordav_FILTER:
   ∀env x y. ordav env x y =
      case FILTER (λ(x',y'). x' = x ∨ y' = y) env of
      | [] => term_cmp x y
      | ((x',y')::_) => if x' = x then if y' = y then EQUAL else LESS else GREATER
Proof
  ho_match_mp_tac ordav_ind >> simp[ordav_def] >>
  strip_assume_tac TotOrd_term_cmp >>
  fs[TotOrd] >> rw[]
QED

Theorem ordav_sym:
   ∀env v1 v2. flip_ord (ordav env v1 v2) = ordav (MAP (λ(x,y). (y,x)) env) v2 v1
Proof
  ho_match_mp_tac ordav_ind >> simp[ordav_def] >>
  conj_tac >- metis_tac[invert_comparison_def,TotOrd_term_cmp,TotOrd,cpn_nchotomy,cpn_distinct] >>
  rw[]
QED

Theorem orda_sym:
   ∀env t1 t2. flip_ord (orda env t1 t2) = orda (MAP (λ(x,y). (y,x)) env) t2 t1
Proof
  ho_match_mp_tac orda_ind >>
  rpt gen_tac >> rpt strip_tac >>
  ONCE_REWRITE_TAC[orda_def] >>
  IF_CASES_TAC >- rw[] >>
  qmatch_assum_abbrev_tac`¬p` >> fs[] >>
  IF_CASES_TAC >- fs[Abbr`p`] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >> simp[ordav_sym] >>
  rw[] >> fs[] >>
  metis_tac[invert_comparison_def,TotOrd_type_cmp,TotOrd_term_cmp,
            TotOrd,cpn_nchotomy,cpn_distinct]
QED

Theorem antisymmetric_alpha_lt:
   antisymmetric alpha_lt
Proof
  rw[antisymmetric_def,alpha_lt_def] >>
  qspecl_then[`[]`,`x`,`y`]mp_tac orda_sym >>
  simp[]
QED

Theorem orda_thm[local]:
  ∀env t1 t2. orda env t1 t2 = ^(#3(dest_cond(rhs(concl(SPEC_ALL orda_def)))))
Proof
  rpt gen_tac >>
  CONV_TAC(LAND_CONV(REWR_CONV orda_def)) >>
  reverse IF_CASES_TAC >- rw[] >> rw[] >>
  BasicProvers.CASE_TAC >> rw[ordav_def] >>
  fs[GSYM RACONV_eq_orda,RACONV_REFL]
QED

Theorem ordav_lx_trans[local]:
  ∀t1 t2 t3 env1 env2.
    ordav env1 t1 t2 ≠ GREATER ∧
    ordav env2 t2 t3 ≠ GREATER ∧
    MAP SND env1 = MAP FST env2
    ⇒ ordav (ZIP (MAP FST env1, MAP SND env2)) t1 t3 ≠ GREATER ∧
      (ordav env1 t1 t2 = LESS ∨ ordav env2 t2 t3 = LESS ⇒
       ordav (ZIP (MAP FST env1, MAP SND env2)) t1 t3 = LESS)
Proof
  mp_tac TotOrd_term_cmp >> simp[TotOrd] >> strip_tac >>
  ntac 3 gen_tac >> Induct >> simp[ordav_def] >- (
    metis_tac[cpn_nchotomy,cpn_distinct] ) >>
  Cases >> simp[ordav_def] >>
  Cases >> simp[] >>
  Cases_on`h` >>
  rw[ordav_def] >>
  metis_tac[cpn_nchotomy,cpn_distinct]
QED

Theorem undo_zip_map_fst[local]:
  p::ZIP(MAP FST l1,MAP SND l2) =
    ZIP (MAP FST ((FST p,v2)::l1), MAP SND ((v2,SND p)::l2))
Proof
  Cases_on`p`>>rw[]
QED

Theorem orda_lx_trans[local]:
  ∀env1 t1 t2 env2 t3.
    orda env1 t1 t2 ≠ GREATER ∧
    orda env2 t2 t3 ≠ GREATER ∧
    MAP SND env1 = MAP FST env2
    ⇒ orda (ZIP (MAP FST env1, MAP SND env2)) t1 t3 ≠ GREATER ∧
      (orda env1 t1 t2 = LESS ∨ orda env2 t2 t3 = LESS ⇒
       orda (ZIP (MAP FST env1, MAP SND env2)) t1 t3 = LESS)
Proof
  completeInduct_on`term_size t1 + term_size t2 + term_size t3` >>
  rpt gen_tac >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >> strip_tac >>
  conj_asm2_tac >- (
    qmatch_assum_abbrev_tac`p ⇒ q` >>
    Cases_on`p=T` >- ( fs[Abbr`q`] ) >>
    fs[Abbr`p`] >>
    `orda env1 t1 t2 = EQUAL ∧
     orda env2 t2 t3 = EQUAL` by
    metis_tac[cpn_nchotomy,cpn_distinct] >>
    fs[GSYM RACONV_eq_orda] >>
    qspecl_then[`env1`,`t1,t2`]mp_tac RACONV_TRANS >>
    simp[] >>
    disch_then(qspecl_then[`MAP SND env2`,`t3`]mp_tac) >>
    simp[] >>
    impl_tac >- (
      fs[LIST_EQ_REWRITE,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF] ) >>
    simp[RACONV_eq_orda] ) >>
  qmatch_abbrev_tac`d ⇒ X` >> strip_tac >>
  qunabbrev_tac`X` >>
  ONCE_REWRITE_TAC[orda_thm] >> simp[] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  TRY ( Cases_on`t2`>>fs[Once orda_thm] >> NO_TAC)
  >- (
    qunabbrev_tac`d` >>
    qpat_x_assum`∀x. Y`kall_tac >>
    Cases_on`t2`>>fs[Once orda_thm] >>
    fs[Once orda_thm] >>
    metis_tac[ordav_lx_trans] )
  >- (
    qunabbrev_tac`d` >>
    qpat_x_assum`∀x. Y`kall_tac >>
    Cases_on`t2`>>fs[Once orda_thm] >>
    fs[Once orda_thm] >>
    mp_tac TotOrd_term_cmp >> simp[TotOrd] >> strip_tac >>
    metis_tac[cpn_nchotomy,cpn_distinct] )
  >- (
    Cases_on`t2`>>TRY(fs[Once orda_thm]>>NO_TAC)>>
    qmatch_assum_rename_tac`orda env1 (Comb t1 t2) (Comb t3 t4) ≠ GREATER` >>
    qmatch_assum_rename_tac`orda env2 (Comb t3 t4) (Comb t5 t6) ≠ GREATER` >>
    fs[Q.SPECL[`env`,`Comb a b`,`Comb c d`]orda_thm,LET_THM] >>
    rpt(qpat_x_assum`X ≠ GREATER` mp_tac) >>
    qpat_x_assum`d`mp_tac >>
    simp[Abbr`d`] >> rw[] >> fs[] >> rw[] >>
    fsrw_tac[DNF_ss][] >>
    let
      val tac =
      first_x_assum(fn th =>
        match_mp_tac (MP_CANON th) >>
        simp[term_size_def] >>
        FIRST (map (fn q =>
          qexists_tac q >> simp[] >>
          (fn g as (asl,w) => (Cases_on`^(lhs w)`>>fs[]) g) >>
          NO_TAC)
        [`t1`,`t2`,`t3`,`t4`,`t5`,`t6`]))
    in
      TRY tac >>
      TRY (
        (qsuff_tac`F`>-rw[])>>
        qpat_x_assum`orda (ZIP P) X Y = Z` mp_tac >> simp[] >>
        (fn g as (asl,w) => (qsuff_tac`^(lhs (rand w)) = LESS`>-rw[])g)>>
        tac ) >>
      (qsuff_tac`F`>-rw[])>>
      qpat_x_assum`orda (ZIP P) X Y ≠ Z` mp_tac >> simp[] >>
      fs[GSYM RACONV_eq_orda] >>
      imp_res_tac RACONV_TRANS >> fs[] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
      fs[LIST_EQ_REWRITE]
    end) >>
  Cases_on`t2`>>TRY(fs[Once orda_thm]>>NO_TAC)>>
  qmatch_assum_rename_tac`orda env1 (Abs v1 t1) (Abs v2 t2) ≠ GREATER` >>
  qmatch_assum_rename_tac`orda env2 (Abs v2 t2) (Abs v3 t3) ≠ GREATER` >>
  fs[Q.SPECL[`env`,`Abs a b`,`Abs c d`]orda_thm,LET_THM] >>
  mp_tac TotOrd_type_cmp >>
  simp[TotOrd] >> strip_tac >> fs[] >>
  rpt(qpat_x_assum`X ≠ GREATER` mp_tac) >>
  qpat_x_assum`d`mp_tac >>
  simp[Abbr`d`] >> rw[] >> fs[] >> rw[] >>
  TRY (
    fsrw_tac[DNF_ss][] >>
    REWRITE_TAC[undo_zip_map_fst] >>
    first_x_assum(fn th =>
      match_mp_tac (MP_CANON th) >>
      simp[term_size_def] >>
      FIRST (map (fn q =>
        qexists_tac q >> simp[] >>
        (fn g as (asl,w) => (Cases_on`^(lhs w)`>>fs[]) g) >>
        NO_TAC)
      [`t1`,`t2`,`t3`,`t4`,`t5`,`t6`]))) >>
  metis_tac[cpn_nchotomy,cpn_distinct]
QED

Theorem transitive_alpha_lt:
   transitive alpha_lt
Proof
  rw[transitive_def,alpha_lt_def] >>
  qspecl_then[`[]`,`x`,`y`]mp_tac orda_lx_trans >>
  simp[]
QED

Theorem alpha_lt_trans_ACONV:
   ∀x y z.
    (ACONV x y ∧ alpha_lt y z ⇒ alpha_lt x z) ∧
    (alpha_lt x y ∧ ACONV y z ⇒ alpha_lt x z)
Proof
  rw[alpha_lt_def,ACONV_eq_orda] >>
  qspecl_then[`[]`,`x`,`y`]mp_tac orda_lx_trans >>
  simp[]
QED

Theorem alpha_lt_not_refl[simp]:
   ∀x. ¬alpha_lt x x
Proof
  metis_tac[alpha_lt_def,ACONV_eq_orda,cpn_distinct,ACONV_REFL]
QED

(* VFREE_IN lemmas *)

Theorem VFREE_IN_RACONV:
   ∀env p. RACONV env p
            ⇒ ∀x ty. VFREE_IN (Var x ty) (FST p) ∧
                     ¬(∃y. MEM (Var x ty,y) env) ⇔
                     VFREE_IN (Var x ty) (SND p) ∧
                     ¬(∃y. MEM (y,Var x ty) env)
Proof
  ho_match_mp_tac RACONV_ind >> simp[VFREE_IN_def] >>
  reverse conj_tac >- metis_tac[] >>
  Induct >> simp[ALPHAVARS_def,FORALL_PROD] >> rw[] >> metis_tac[]
QED

Theorem VFREE_IN_ACONV:
   ∀s t x ty. ACONV s t ⇒ (VFREE_IN (Var x ty) s ⇔ VFREE_IN (Var x ty) t)
Proof
  rw[ACONV_def] >> imp_res_tac VFREE_IN_RACONV >> fs[]
QED

Theorem VFREE_IN_subterm:
   ∀t1 t2. VFREE_IN t1 t2 ⇒ t1 subterm t2
Proof
  Induct_on`t2` >> simp[subterm_Comb,subterm_Abs] >>
  metis_tac[]
QED

(* hypset_ok *)

Theorem hypset_ok_nil[simp]:
   hypset_ok []
Proof
rw[hypset_ok_def]
QED

Theorem hypset_ok_sing[simp]:
   ∀p. hypset_ok [p]
Proof
rw[hypset_ok_def]
QED

Theorem hypset_ok_cons:
   hypset_ok (h::hs) ⇔
    EVERY (alpha_lt h) hs ∧ hypset_ok hs
Proof
  rw[hypset_ok_def,MATCH_MP SORTED_EQ transitive_alpha_lt,EVERY_MEM]>>
  metis_tac[]
QED

Theorem hypset_ok_ALL_DISTINCT:
   ∀h. hypset_ok h ⇒ ALL_DISTINCT h
Proof
  simp[hypset_ok_def] >> Induct >>
  simp[MATCH_MP SORTED_EQ transitive_alpha_lt] >>
  rw[] >> strip_tac >> res_tac >> fs[alpha_lt_def] >>
  metis_tac[cpn_distinct,ACONV_REFL,ACONV_eq_orda]
QED

Theorem hypset_ok_eq:
   ∀h1 h2.  hypset_ok h1 ∧ hypset_ok h2 ⇒
            ((h1 = h2) ⇔ (set h1 = set h2))
Proof
  rw[EQ_IMP_THM] >> fs[EXTENSION] >>
  metis_tac[
    hypset_ok_ALL_DISTINCT,PERM_ALL_DISTINCT,
    SORTED_PERM_EQ,hypset_ok_def,
    transitive_alpha_lt, antisymmetric_alpha_lt]
QED

Theorem hypset_ok_append =
  Q.ISPEC`alpha_lt` sortingTheory.SORTED_APPEND_GEN
  |> REWRITE_RULE[GSYM hypset_ok_def]

Theorem hypset_ok_el_less =
  MATCH_MP sortingTheory.SORTED_EL_LESS transitive_alpha_lt
  |> REWRITE_RULE[GSYM hypset_ok_def]

(* term_union lemmas *)

Theorem term_union_idem[simp]:
   ∀ls. term_union ls ls = ls
Proof
  Induct >- simp[term_union_def] >>
  simp[Once term_union_def]
QED

Theorem term_union_thm:
   (∀l2. term_union [] l2 = l2) ∧
    (∀l1. term_union l1 [] = l1) ∧
    (∀h1 t1 h2 t2.
          term_union (h1::t1) (h2::t2) =
          case orda [] h1 h2 of
          | EQUAL =>   h1::term_union t1 t2
          | LESS =>    h1::term_union t1 (h2::t2)
          | GREATER => h2::term_union (h1::t1) t2)
Proof
  rw[] >- rw[term_union_def] >- (
    rw[term_union_def] >>
    BasicProvers.CASE_TAC ) >>
  map_every qid_spec_tac[`h2`,`t2`,`h1`,`t1`] >>
  `∀x. orda [] x x = EQUAL` by (
      rw[GSYM ACONV_eq_orda] ) >>
  Induct >>
  simp[Once term_union_def] >> rw[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[]
QED

Theorem MEM_term_union_imp:
   ∀l1 l2 x. MEM x (term_union l1 l2) ⇒ MEM x l1 ∨ MEM x l2
Proof
  Induct >> simp[term_union_thm] >>
  CONV_TAC(SWAP_FORALL_CONV) >>
  Induct >> simp[term_union_thm] >> rpt gen_tac >>
  BasicProvers.CASE_TAC >> rw[] >> fs[] >>
  res_tac >> fs[]
QED

Theorem hypset_ok_term_union[simp]:
   ∀l1 l2. hypset_ok l1 ∧ hypset_ok l2 ⇒
            hypset_ok (term_union l1 l2)
Proof
  simp[hypset_ok_def] >>
  Induct >- simp[term_union_thm] >> qx_gen_tac`h1` >>
  Induct >- simp[term_union_thm] >> qx_gen_tac`h2` >>
  strip_tac >>
  fs[MATCH_MP SORTED_EQ transitive_alpha_lt] >>
  simp[term_union_thm] >>
  BasicProvers.CASE_TAC >>
  simp[MATCH_MP SORTED_EQ transitive_alpha_lt] >>
  rw[] >> imp_res_tac MEM_term_union_imp >>
  fs[GSYM alpha_lt_def]
  >- metis_tac[transitive_alpha_lt,transitive_def]
  >- (
    fs[alpha_lt_def] >>
    qspecl_then[`[]`,`h1`,`h2`]mp_tac orda_lx_trans >>
    simp[] )
  >- (
    qspecl_then[`[]`,`h1`,`h2`]mp_tac orda_sym >>
    simp[alpha_lt_def] ) >>
  qspecl_then[`[]`,`h1`,`h2`]mp_tac orda_sym >>
  fs[alpha_lt_def] >> disch_then(assume_tac o SYM) >>
  qspecl_then[`[]`,`h2`,`h1`]mp_tac orda_lx_trans >>
  simp[]
QED

Theorem EVERY_term_union:
   EVERY P l1 ∧ EVERY P l2 ⇒ EVERY P (term_union l1 l2)
Proof
  metis_tac[EVERY_MEM,MEM_term_union_imp]
QED

Theorem MEM_term_union:
   ∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ (MEM t h1 ∨ MEM t h2) ⇒
      ∃y. MEM y (term_union h1 h2) ∧ ACONV t y
Proof
  Induct >> simp[term_union_thm] >-
    (metis_tac[ACONV_REFL]) >>
  gen_tac >> Induct >> simp[term_union_thm] >-
    (metis_tac[ACONV_REFL]) >>
  simp[hypset_ok_cons,GSYM AND_IMP_INTRO] >>
  rpt gen_tac >> ntac 4 strip_tac >> fs[] >>
  fs[hypset_ok_cons] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fs[GSYM ACONV_eq_orda] >>
  metis_tac[MEM,ACONV_REFL,ACONV_SYM,hypset_ok_cons]
QED

Theorem term_union_sing_lt[local]:
  ∀ys x. EVERY (λy. alpha_lt x y) ys ⇒ (term_union [x] ys = x::ys)
Proof
  Induct >> simp[term_union_thm] >> rw[] >> fs[] >>
  fs[alpha_lt_def]
QED

Theorem term_union_insert:
   ∀ys x zs.
    EVERY (λy. alpha_lt y x) ys ∧
    EVERY (λz. alpha_lt x z) zs
    ⇒ (term_union [x] (ys ++ zs) = ys ++ x::zs)
Proof
  Induct >> simp[term_union_sing_lt] >> rw[] >>
  simp[term_union_thm] >>
  `orda [] x h = Greater` by (
    fs[alpha_lt_def] >>
    qspecl_then[`[]`,`h`,`x`]mp_tac orda_sym >>
    simp[] ) >>
  simp[]
QED

Theorem term_union_replace:
   ∀ys x x' zs.
    EVERY (λy. alpha_lt y x) ys ∧ ACONV x x' ∧
    EVERY (λz. alpha_lt x z) zs
    ⇒
    term_union [x] (ys ++ x'::zs) = ys ++ x::zs
Proof
  Induct >> rw[term_union_thm,ACONV_eq_orda,alpha_lt_def] >>
  qspecl_then[`[]`,`h`,`x`]mp_tac orda_sym >>
  simp[] >> disch_then(assume_tac o SYM) >> simp[] >>
  fs[GSYM ACONV_eq_orda, GSYM alpha_lt_def]
QED

Theorem MEM_term_union_first:
   ∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ MEM t h1 ⇒ MEM t (term_union h1 h2)
Proof
  Induct >> simp[hypset_ok_cons] >>
  gen_tac >> Induct >> simp[term_union_thm] >>
  rw[hypset_ok_cons] >>
  BasicProvers.CASE_TAC >> rw[] >>
  disj2_tac >>
  first_x_assum match_mp_tac >>
  rw[hypset_ok_cons]
QED

Theorem term_union_insert_mem:
   ∀c h. hypset_ok h ∧ MEM c h ⇒ (term_union [c] h = h)
Proof
  gen_tac >> Induct >> simp[hypset_ok_cons,term_union_thm] >>
  rw[] >> fs[] >- (
    `ACONV c c` by simp[] >> fs[ACONV_eq_orda] ) >>
  fs[EVERY_MEM] >> res_tac >>
  fs[alpha_lt_def] >>
  qspecl_then[`[]`,`h'`,`c`]mp_tac orda_sym >> simp[] >>
  disch_then(assume_tac o SYM) >>
  rw[term_union_thm]
QED

Theorem term_union_insert_remove:
   ∀c h. hypset_ok h ∧ MEM c h ∧ ACONV c' c ⇒ (term_union [c] (term_remove c' h) = h)
Proof
  gen_tac >> Induct >> simp[hypset_ok_cons] >> rw[] >> fs[] >- (
    simp[Once term_remove_def] >>
    fs[ACONV_eq_orda] >>
    Cases_on`h`>>simp[term_union_thm] >> fs[alpha_lt_def] ) >>
  simp[Once term_remove_def] >> fs[EVERY_MEM] >>
  res_tac >>
  imp_res_tac ACONV_SYM >>
  imp_res_tac alpha_lt_trans_ACONV >>
  fs[alpha_lt_def] >>
  qspecl_then[`[]`,`h'`,`c`]mp_tac orda_sym >> simp[] >>
  disch_then(assume_tac o SYM) >>
  qspecl_then[`[]`,`h'`,`c'`]mp_tac orda_sym >> simp[] >>
  disch_then(assume_tac o SYM) >>
  rw[term_union_thm] >>
  match_mp_tac term_union_insert_mem >>
  rw[]
QED

(* term_remove *)

Theorem term_remove_nil[simp]:
   ∀a. term_remove a [] = []
Proof
  rw[Once term_remove_def]
QED

Theorem MEM_term_remove_imp:
   ∀ls x t. MEM t (term_remove x ls) ⇒
      MEM t ls ∧ (hypset_ok ls ⇒ ¬ACONV x t)
Proof
  Induct >> simp[Once term_remove_def] >> rw[] >>
  fs[hypset_ok_def,
     MATCH_MP SORTED_EQ transitive_alpha_lt,
     ACONV_eq_orda,EVERY_MEM,EXISTS_MEM] >>
  res_tac >> fs[] >>
  fs[GSYM ACONV_eq_orda] >>
  fs[alpha_lt_def,ACONV_eq_orda] >>
  qspecl_then[`[]`,`h`,`t`]mp_tac orda_sym >>
  simp[] >> disch_then(assume_tac o SYM) >>
  spose_not_then strip_assume_tac >>
  qspecl_then[`[]`,`x`,`h`]mp_tac orda_lx_trans >>
  simp[] >> qexists_tac`t` >> simp[]
QED

Theorem hypset_ok_term_remove[simp]:
   ∀ls. hypset_ok ls ⇒ ∀t. hypset_ok (term_remove t ls)
Proof
  Induct >> simp[Once term_remove_def] >>
  rw[] >> fs[hypset_ok_def] >> rw[] >>
  fs[MATCH_MP SORTED_EQ transitive_alpha_lt,
     EVERY_MEM,ACONV_eq_orda] >> rw[] >>
  imp_res_tac MEM_term_remove_imp >>
  rfs[hypset_ok_def]
QED

Theorem EVERY_term_remove:
   EVERY P ls ⇒ EVERY P (term_remove t ls)
Proof
  metis_tac[EVERY_MEM,MEM_term_remove_imp]
QED

Theorem MEM_term_remove:
   ∀h x t. MEM t h ∧ ¬ACONV x t ∧ hypset_ok h
    ⇒ MEM t (term_remove x h)
Proof
  Induct >> simp[Once term_remove_def] >>
  simp[hypset_ok_cons] >> rw[EVERY_MEM] >>
  res_tac >> fs[alpha_lt_def,GSYM ACONV_eq_orda]
QED

Theorem term_remove_exists:
   ∀c h. term_remove c h ≠ h ⇒ ∃c'. MEM c' h ∧ ACONV c c'
Proof
  gen_tac >> Induct >> simp[] >>
  simp[Once term_remove_def] >> rw[] >> fs[] >>
  fs[GSYM ACONV_eq_orda] >> metis_tac[]
QED

(* term_image *)

Theorem term_image_nil[simp]:
   term_image f [] = []
Proof
  simp[Once term_image_def]
QED

Theorem MEM_term_image_imp:
   ∀ls f t. MEM t (term_image f ls) ⇒ ∃x. MEM x ls ∧ t = f x
Proof
  Induct >> simp[Once term_image_def] >> rw[] >> fs[] >>
  imp_res_tac MEM_term_union_imp >> fs[] >>
  metis_tac[]
QED

Theorem hypset_ok_term_image:
   ∀ls f. hypset_ok ls ⇒ hypset_ok (term_image f ls)
Proof
  Induct >> simp[Once term_image_def] >> rw[hypset_ok_cons]
QED

Theorem MEM_term_image:
   ∀ls f t. MEM t ls ∧ hypset_ok ls ⇒ ∃y. MEM y (term_image f ls) ∧ ACONV (f t) y
Proof
  Induct >> simp[Once term_image_def] >> rw[hypset_ok_cons] >> rw[] >>
  TRY(metis_tac[ACONV_REFL]) >- metis_tac[MEM_term_union,hypset_ok_sing,MEM,hypset_ok_term_image] >>
  first_x_assum(qspecl_then[`f`,`t`]mp_tac) >> rw[] >>
  metis_tac[MEM_term_union,hypset_ok_sing,hypset_ok_term_image,ACONV_TRANS]
QED

(* VSUBST lemmas *)

Theorem VSUBST_HAS_TYPE:
   ∀tm ty ilist.
      tm has_type ty ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ (VSUBST ilist tm) has_type ty
Proof
  Induct >> simp[VSUBST_def]
  >- (
    map_every qx_gen_tac[`x`,`ty`,`tty`] >>
    Induct >> simp[REV_ASSOCD,FORALL_PROD] >>
    srw_tac[DNF_ss][] >> rw[] >> fs[] >>
    qpat_x_assum`X has_type tty`mp_tac >>
    simp[Once has_type_cases]>>rw[]>>rw[])
  >- (
    simp[Once has_type_cases] >> rw[] >>
    rw[Once has_type_cases] >> metis_tac[] )
  >- (
    map_every qx_gen_tac[`ty`,`ilist`] >>
    simp[Once has_type_cases] >> rw[] >>
    simp[Once has_type_cases] >>
    first_x_assum match_mp_tac >> simp[] >>
    simp[MEM_FILTER] >> rw[] >> TRY(metis_tac[]) >>
    simp[Once has_type_cases])
QED

Theorem VSUBST_WELLTYPED:
   ∀tm ty ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ welltyped (VSUBST ilist tm)
Proof
  metis_tac[VSUBST_HAS_TYPE,welltyped_def]
QED

Theorem VFREE_IN_VSUBST:
   ∀tm u uty ilist.
      welltyped tm ⇒
      (VFREE_IN (Var u uty) (VSUBST ilist tm) ⇔
       ∃y ty. VFREE_IN (Var y ty) tm ∧
              VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty)))
Proof
  Induct >> simp[VFREE_IN_def,VSUBST_def] >- metis_tac[] >>
  map_every qx_gen_tac[`u`,`uty`,`ilist`] >>
  disch_then(qx_choosel_then[`b`,`bty`]strip_assume_tac) >> simp[] >>
  BasicProvers.VAR_EQ_TAC >> qmatch_assum_rename_tac`welltyped tm` >>
  qmatch_abbrev_tac`VFREE_IN vu (if p then Abs (Var vx xty) (VSUBST l1 tm) else Abs (Var x xty) (VSUBST l2 tm)) ⇔ q` >>
  qsuff_tac`VFREE_IN vu (Abs (Var (if p then vx else x) xty) (VSUBST (if p then l1 else l2) tm)) ⇔ q` >- metis_tac[] >>
  simp[VFREE_IN_def,Abbr`vu`] >>
  rw[] >- (
    simp[Abbr`q`,Abbr`l1`,REV_ASSOCD,Abbr`l2`,REV_ASSOCD_FILTER] >>
    EQ_TAC >- (
      rw[] >>
      pop_assum mp_tac >> rw[VFREE_IN_def] >> fs[] >>
      metis_tac[] ) >>
    qmatch_assum_abbrev_tac`Abbrev(vx = VARIANT t xx xty)` >>
    qspecl_then[`t`,`xx`,`xty`]mp_tac VARIANT_THM >> strip_tac >>
    qmatch_assum_abbrev_tac`Abbrev(t = VSUBST ll tm)` >>
    rfs[Abbr`t`] >>
    fs[Abbr`vx`] >> strip_tac >>
    (conj_tac >- (
      spose_not_then strip_assume_tac >>
      first_x_assum(qspecl_then[`y`,`ty`]mp_tac) >>
      simp[Abbr`ll`,REV_ASSOCD_FILTER])) >>
    map_every qexists_tac[`y`,`ty`] >> simp[]) >>
  simp[Abbr`q`,Abbr`l2`,REV_ASSOCD_FILTER,Abbr`l1`,Abbr`vx`] >>
  EQ_TAC >- (
    rw[] >>
    pop_assum mp_tac >> rw[VFREE_IN_def] >> fs[] >>
    metis_tac[] ) >>
  fs[EXISTS_MEM,EVERY_MEM,markerTheory.Abbrev_def,MEM_FILTER,FORALL_PROD] >>
  simp[GSYM LEFT_FORALL_IMP_THM] >>
  rpt gen_tac >>
  Cases_on`∃a. MEM (a,Var y ty) ilist ∧ VFREE_IN (Var x xty) a` >- (
    fs[] >> first_x_assum(qspecl_then[`a`,`Var y ty`]mp_tac) >>
    simp[] >> rw[] >> fs[] >> fs[VFREE_IN_def] ) >> fs[] >>
  Cases_on`VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))`>>simp[] >>
  Cases_on`Var u uty = Var y ty`>- (
    fs[] >> metis_tac[] ) >>
  Q.ISPECL_THEN[`ilist`,`Var y ty`,`Var y ty`]mp_tac REV_ASSOCD_MEM >>
  strip_tac >> fs[] >>
  fs[VFREE_IN_def] >>
  metis_tac[]
QED

Theorem VSUBST_NIL[simp]:
   ∀tm. VSUBST [] tm = tm
Proof
  ho_match_mp_tac term_induction >>
  simp[VSUBST_def,REV_ASSOCD]
QED

(* INST lemmas *)

Theorem INST_CORE_HAS_TYPE:
   ∀n tm env tyin.
      welltyped tm ∧ (sizeof tm = n) ∧
      (∀s s'. MEM (s,s') env ⇒
              ∃x ty. (s = Var x ty) ∧
                     (s' = Var x (TYPE_SUBST tyin ty)))
      ⇒ (∃x ty. (INST_CORE env tyin tm = Clash(Var x (TYPE_SUBST tyin ty))) ∧
                VFREE_IN (Var x ty) tm ∧
                REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                  env (Var x ty) ≠ Var x ty)
      ∨ (∀x ty. VFREE_IN (Var x ty) tm
                ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) = Var x ty) ∧
        (∃tm'. INST_CORE env tyin tm = Result tm' ∧
               tm' has_type (TYPE_SUBST tyin (typeof tm)) ∧
               (∀u uty. VFREE_IN (Var u uty) tm' ⇔
                        ∃oty. VFREE_IN (Var u oty) tm ∧
                              uty = TYPE_SUBST tyin oty))
Proof
  gen_tac >> completeInduct_on`n` >>
  Induct >> simp[Once INST_CORE_def] >>
  TRY (
    simp[Once INST_CORE_def] >>
    simp[Once has_type_cases] >>
    NO_TAC )
  >- (
    pop_assum kall_tac >> rw[] >>
    simp[Once INST_CORE_def] >>
    simp[Once has_type_cases] >>
    metis_tac[] )
  >- (
    rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >>
    fsrw_tac[ARITH_ss][] >>
    simp[Once INST_CORE_def] >>
    first_assum(qspec_then`sizeof tm`mp_tac) >>
    first_x_assum(qspec_then`sizeof tm'`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tm'`,`env`,`tyin`]mp_tac) >> simp[] >>
    qmatch_abbrev_tac`P ⇒ Q` >> strip_tac >>
    qunabbrev_tac`Q` >>
    disch_then(qspecl_then[`tm`,`env`,`tyin`]mp_tac) >>
    simp[] >>
    qunabbrev_tac`P` >>
    reverse (strip_tac >> fs[]) >- (
      simp[Once has_type_cases] >>
      metis_tac[] ) >>
    metis_tac[] )
  >- (
    rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >>
    BasicProvers.VAR_EQ_TAC >> qmatch_assum_rename_tac`welltyped tm` >>
    fsrw_tac[ARITH_ss][] >>
    Q.PAT_ABBREV_TAC`env' = X::env` >>
    Q.PAT_ABBREV_TAC`tm' = VSUBST X tm` >>
    Q.PAT_ABBREV_TAC`env'' = X::env` >>
    `sizeof tm' = sizeof tm` by (
      simp[Abbr`tm'`,SIZEOF_VSUBST] ) >>
    `welltyped tm'` by (
      simp[Abbr`tm'`] >>
      match_mp_tac VSUBST_WELLTYPED >>
      simp[] >> simp[Once has_type_cases] ) >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    simp[Once INST_CORE_def] >>
    disch_then(fn th =>
      qspecl_then[`tm`,`env'`,`tyin`]mp_tac th >>
      qspecl_then[`tm'`,`env''`,`tyin`]mp_tac th >>
      qspecl_then[`tm`,`[]`,`tyin`]mp_tac th) >> simp[] >>
    qmatch_abbrev_tac`a ⇒ b` >> strip_tac >> qunabbrev_tac`b` >>
    qmatch_abbrev_tac`(p ⇒ q) ⇒ r` >>
    `p` by (
      unabbrev_all_tac >> rw[] >> metis_tac[]) >>
    simp[] >> map_every qunabbrev_tac[`p`,`q`,`r`] >> pop_assum kall_tac >>
    qmatch_abbrev_tac`x ⇒ (p ⇒ q) ⇒ r` >>
    `p` by (
      unabbrev_all_tac >> rw[] >> metis_tac[]) >>
    simp[] >> map_every qunabbrev_tac[`x`,`p`,`q`,`r`] >> pop_assum kall_tac >>
    qunabbrev_tac`a` >>
    fs[] >- (
      rw[] >> fs[] >> fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD] ) >>
    strip_tac >> fs[] >- (
      strip_tac >> fs[] >- (
        rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
        rw[] >> fs[] >>
        BasicProvers.EVERY_CASE_TAC >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
        metis_tac[VARIANT_THM] ) >>
      rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
      simp[Once has_type_cases] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      rw[] >> fs[] >>
      metis_tac[VARIANT_THM,term_11]) >>
    strip_tac >> fs[] >- (
      rw[] >> fs[] >>
      rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      simp[Once has_type_cases] >>
      TRY (
        qmatch_assum_abbrev_tac`tz has_type TYPE_SUBST tyin (typeof (VSUBST ez tm))` >>
        `typeof (VSUBST ez tm) = typeof tm` by (
          match_mp_tac WELLTYPED_LEMMA >>
          match_mp_tac VSUBST_HAS_TYPE >>
          conj_tac >- metis_tac[WELLTYPED] >>
          simp[Abbr`ez`] >>
          simp[Once has_type_cases] ) >>
        unabbrev_all_tac >> fs[] >>
        fs[GSYM LEFT_FORALL_IMP_THM] >>
        first_x_assum(qspecl_then[`x'`,`ty''`,`x'`,`ty''`]mp_tac) >>
        simp[] >> BasicProvers.CASE_TAC >> simp[] >> strip_tac >> fs[] >>
        `VFREE_IN (Var x' (TYPE_SUBST tyin ty'')) tm''` by metis_tac[] >>
        metis_tac[VARIANT_THM]) >>
      TRY (
        EQ_TAC >> rw[] >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
        pop_assum mp_tac >> rw[] >> fs[] >>
        TRY (
          qexists_tac`oty`>>simp[] >>
          map_every qexists_tac[`u`,`oty`] >>
          simp[] >> NO_TAC) >>
        metis_tac[VARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED] ) >>
      metis_tac[VARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED] ) >>
    rw[] >> fs[] >>
    rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp[Once has_type_cases] >>
    metis_tac[VARIANT_THM,term_11])
QED

Theorem INST_CORE_NIL_IS_RESULT:
   ∀tyin tm. welltyped tm ⇒ IS_RESULT (INST_CORE [] tyin tm)
Proof
  rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[] >> rw[] >> rw[] >> fs[REV_ASSOCD]
QED

Theorem INST_HAS_TYPE:
   ∀tm ty tyin ty'. tm has_type ty ∧ ty' = TYPE_SUBST tyin ty ⇒ INST tyin tm has_type ty'
Proof
  rw[INST_def] >>
  qspecl_then[`tyin`,`tm`]mp_tac INST_CORE_NIL_IS_RESULT >> rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  `welltyped tm` by metis_tac[welltyped_def] >> fs[] >>
  rw[] >> fs[] >> metis_tac[WELLTYPED_LEMMA]
QED

Theorem INST_WELLTYPED:
   ∀tm tyin.  welltyped tm ⇒ welltyped (INST tyin tm)
Proof
  metis_tac[INST_HAS_TYPE,WELLTYPED_LEMMA,WELLTYPED]
QED

Theorem INST_CORE_NIL:
   ∀env tyin tm. welltyped tm ∧ tyin = [] ∧
      (∀x ty. VFREE_IN (Var x ty) tm ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) = Var x ty) ⇒
      INST_CORE env tyin tm = Result tm
Proof
  ho_match_mp_tac INST_CORE_ind >>
  simp[INST_CORE_def] >>
  rw[] >> fs[] >>
  Q.PAT_ABBREV_TAC`i1 = INST_CORE X [] tm` >>
  `i1 = Result tm` by (
    qunabbrev_tac`i1` >>
    first_x_assum match_mp_tac >>
    simp[holSyntaxLibTheory.REV_ASSOCD] >>
    rw[] >> metis_tac[] ) >>
  simp[]
QED

Theorem INST_nil:
   welltyped tm ⇒ (INST [] tm = tm)
Proof
  rw[INST_def,INST_CORE_def] >>
  qspecl_then[`[]`,`[]`,`tm`]mp_tac INST_CORE_NIL >>
  simp[holSyntaxLibTheory.REV_ASSOCD]
QED

(* tyvars and tvars *)

Theorem tyvars_ALL_DISTINCT[simp]:
   ∀ty. ALL_DISTINCT (tyvars ty)
Proof
  ho_match_mp_tac type_ind >>
  rw[tyvars_def] >>
  Induct_on`l` >> simp[] >>
  rw[ALL_DISTINCT_LIST_UNION]
QED

Theorem tvars_ALL_DISTINCT[simp]:
   ∀tm. ALL_DISTINCT (tvars tm)
Proof
  Induct >> simp[tvars_def,ALL_DISTINCT_LIST_UNION]
QED

Theorem tyvars_TYPE_SUBST:
   ∀ty tyin. set (tyvars (TYPE_SUBST tyin ty)) =
      { v | ∃x. MEM x (tyvars ty) ∧ MEM v (tyvars (REV_ASSOCD (Tyvar x) tyin (Tyvar x))) }
Proof
  ho_match_mp_tac type_ind >> simp[tyvars_def] >>
  simp[EXTENSION,EVERY_MEM,MEM_FOLDR_LIST_UNION,PULL_EXISTS,MEM_MAP] >> rw[] >>
  metis_tac[]
QED

Theorem tyvars_typeof_subset_tvars:
   ∀tm ty. tm has_type ty ⇒ set (tyvars ty) ⊆ set (tvars tm)
Proof
  ho_match_mp_tac has_type_ind >>
  simp[tvars_def] >>
  simp[SUBSET_DEF,MEM_LIST_UNION,tyvars_def] >>
  metis_tac[]
QED

Theorem tyvars_Tyapp_MAP_Tyvar:
   ∀x ls. ALL_DISTINCT ls ⇒ (tyvars (Tyapp x (MAP Tyvar ls)) = LIST_UNION [] ls)
Proof
  simp[tyvars_def] >>
  Induct >> fs[tyvars_def,LIST_UNION_def] >>
  rw[LIST_INSERT_def]
QED

Theorem STRING_SORT_SET_TO_LIST_set_tvars:
   ∀tm. STRING_SORT (MAP explode (SET_TO_LIST (set (tvars tm)))) =
         STRING_SORT (MAP explode (tvars tm))
Proof
  gen_tac >> assume_tac(SPEC_ALL tvars_ALL_DISTINCT) >>
  simp[STRING_SORT_EQ] >>
  match_mp_tac sortingTheory.PERM_MAP >>
  pop_assum mp_tac >>
  REWRITE_TAC[sortingTheory.ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] >>
  simp[sortingTheory.PERM_SYM]
QED

Theorem mlstring_sort_SET_TO_LIST_set_tvars:
   mlstring_sort (SET_TO_LIST (set (tvars tm))) = mlstring_sort (tvars tm)
Proof
  rw[mlstring_sort_def,STRING_SORT_SET_TO_LIST_set_tvars]
QED

(* Equations *)

Theorem EQUATION_HAS_TYPE_BOOL:
   ∀s t. (s === t) has_type Bool
          ⇔ welltyped s ∧ welltyped t ∧ (typeof s = typeof t)
Proof
  rw[equation_def] >> rw[Ntimes has_type_cases 3] >>
  metis_tac[WELLTYPED_LEMMA,WELLTYPED]
QED

Theorem welltyped_equation:
   ∀s t. welltyped (s === t) ⇔ s === t has_type Bool
Proof
  simp[EQUATION_HAS_TYPE_BOOL] >> simp[equation_def]
QED

Theorem typeof_equation:
   welltyped (l === r) ⇒ (typeof (l === r)) = Bool
Proof
  rw[welltyped_equation] >> imp_res_tac WELLTYPED_LEMMA >> rw[]
QED

Theorem vfree_in_equation:
   VFREE_IN v (s === t) ⇔ (v = Equal (typeof s)) ∨ VFREE_IN v s ∨ VFREE_IN v t
Proof
  rw[equation_def,VFREE_IN_def] >> metis_tac[]
QED

Theorem equation_intro:
   (ty = typeof p) ⇒ (Comb (Comb (Equal ty) p) q = p === q)
Proof
  rw[equation_def]
QED

(* type_ok *)

Theorem type_ok_TYPE_SUBST:
   ∀s tyin ty.
      type_ok s ty ∧
      EVERY (type_ok s) (MAP FST tyin)
    ⇒ type_ok s (TYPE_SUBST tyin ty)
Proof
  gen_tac >> ho_match_mp_tac TYPE_SUBST_ind >>
  simp[type_ok_def] >> rw[EVERY_MAP,EVERY_MEM] >>
  fs[FORALL_PROD] >>
  metis_tac[REV_ASSOCD_MEM,type_ok_def]
QED

Theorem type_ok_TYPE_SUBST_imp:
   ∀s tyin ty. type_ok s (TYPE_SUBST tyin ty) ⇒
                ∀x. MEM x (tyvars ty) ⇒ type_ok s (TYPE_SUBST tyin (Tyvar x))
Proof
  gen_tac >> ho_match_mp_tac TYPE_SUBST_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,type_ok_def] >> rw[] >>
  fs[EVERY_MAP,EVERY_MEM] >> metis_tac[]
QED

(* term_ok *)

Theorem term_ok_welltyped:
   ∀sig t. term_ok sig t ⇒ welltyped t
Proof
  Cases >> Induct >> simp[term_ok_def] >> rw[]
QED

Theorem term_ok_type_ok:
   ∀sig t. is_std_sig sig ∧ term_ok sig t
          ⇒ type_ok (FST sig) (typeof t)
Proof
  Cases >> Induct >> simp[term_ok_def] >> rw[] >>
  fs[is_std_sig_def,type_ok_def]
QED

Theorem term_ok_equation:
   is_std_sig sig ⇒
      (term_ok sig (s === t) ⇔
        term_ok sig s ∧ term_ok sig t ∧
        typeof t = typeof s)
Proof
  Cases_on`sig` >> rw[equation_def,term_ok_def] >>
  rw[EQ_IMP_THM] >>
  imp_res_tac term_ok_welltyped >>
  imp_res_tac term_ok_type_ok >>
  fs[is_std_sig_def,type_ok_def] >>
  qexists_tac`[(typeof s,Tyvar «A»)]` >>
  rw[holSyntaxLibTheory.REV_ASSOCD_def]
QED

Theorem term_ok_clauses:
   is_std_sig sig ⇒
    (term_ok sig (Var s ty) ⇔ type_ok (tysof sig) ty) ∧
    (type_ok (tysof sig) (Tyvar a) ⇔ T) ∧
    (type_ok (tysof sig) Bool ⇔ T) ∧
    (type_ok (tysof sig) (Fun ty1 ty2) ⇔ type_ok (tysof sig) ty1 ∧ type_ok (tysof sig) ty2) ∧
    (term_ok sig (Comb t1 t2) ⇔ term_ok sig t1 ∧ term_ok sig t2 ∧ welltyped (Comb t1 t2)) ∧
    (term_ok sig (Equal ty) ⇔ type_ok (tysof sig) ty) ∧
    (term_ok sig (t1 === t2) ⇔ term_ok sig t1 ∧ term_ok sig t2 ∧ typeof t1 = typeof t2) ∧
    (term_ok sig (Abs (Var s ty) t) ⇔ type_ok (tysof sig) ty ∧ term_ok sig t)
Proof
  rw[term_ok_def,type_ok_def,term_ok_equation] >>
  fs[is_std_sig_def] >>
  TRY (
    rw[EQ_IMP_THM] >>
    qexists_tac`[(ty,Tyvar «A»)]` >>
    EVAL_TAC >> NO_TAC) >>
  metis_tac[]
QED

Theorem term_ok_VSUBST:
   ∀sig tm ilist.
    term_ok sig tm ∧
    (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s')
    ⇒
    term_ok sig (VSUBST ilist tm)
Proof
  Cases >> Induct >> simp[VSUBST_def,term_ok_def] >- (
    ntac 2 gen_tac >> Induct >> simp[REV_ASSOCD,term_ok_def] >>
    Cases >> simp[REV_ASSOCD] >> rw[term_ok_def] >> metis_tac[])
  >- (
    rw[] >>
    imp_res_tac VSUBST_WELLTYPED >>
    imp_res_tac WELLTYPED >>
    imp_res_tac VSUBST_HAS_TYPE >>
    metis_tac[WELLTYPED_LEMMA] ) >>
  rw[term_ok_def] >> simp[] >> rw[term_ok_def] >>
  first_x_assum match_mp_tac >>
  rw[term_ok_def,MEM_FILTER] >>
  simp[Once has_type_cases]
QED

Theorem term_ok_INST_CORE:
   ∀sig env tyin tm.
      term_ok sig tm ∧
      EVERY (type_ok (FST sig)) (MAP FST tyin) ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      IS_RESULT (INST_CORE env tyin tm)
      ⇒
      term_ok sig (RESULT (INST_CORE env tyin tm))
Proof
  Cases >> ho_match_mp_tac INST_CORE_ind >>
  simp[term_ok_def,INST_CORE_def] >>
  rw[term_ok_def,type_ok_TYPE_SUBST] >- (
    HINT_EXISTS_TAC >> rw[] >-
      metis_tac[type_ok_TYPE_SUBST] >>
    metis_tac[TYPE_SUBST_compose] ) >>
  Cases_on`INST_CORE env tyin tm`>>fs[] >>
  Cases_on`INST_CORE env tyin tm'`>>fs[] >>
  qspecl_then[`sizeof tm`,`tm`,`env`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  qspecl_then[`sizeof tm'`,`tm'`,`env`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  rw[] >> imp_res_tac WELLTYPED_LEMMA >> simp[] >>
  imp_res_tac term_ok_welltyped >> fs[] >> rw[term_ok_def] >>
  TRY (
    match_mp_tac type_ok_TYPE_SUBST >> rw[] ) >>
  TRY (
    first_x_assum match_mp_tac >>
    conj_tac >>
    TRY (
      match_mp_tac term_ok_VSUBST >>
      rw[] >>
      rw[Once has_type_cases] >>
      rw[term_ok_def] ) >>
    rw[] >>
    metis_tac[] ) >>
  simp[welltyped_def] >> PROVE_TAC[]
QED

Theorem term_ok_INST:
   ∀sig tyin tm.
    term_ok sig tm ∧
    EVERY (type_ok (FST sig)) (MAP FST tyin) ⇒
    term_ok sig (INST tyin tm)
Proof
  rw[INST_def] >>
  metis_tac[INST_CORE_NIL_IS_RESULT,term_ok_welltyped,term_ok_INST_CORE,MEM]
QED

Theorem term_ok_raconv:
   ∀env tp. RACONV env tp ⇒
      ∀sig.
      EVERY (λ(s,s'). welltyped s ∧ welltyped s' ∧ typeof s = typeof s' ∧ type_ok (FST sig) (typeof s)) env ⇒
      term_ok sig (FST tp) ∧ welltyped (SND tp) ⇒ term_ok sig (SND tp)
Proof
  ho_match_mp_tac RACONV_strongind >>
  rw[] >> Cases_on`sig`>>fs[term_ok_def] >- (
    imp_res_tac ALPHAVARS_MEM >> fs[EVERY_MEM,FORALL_PROD] >>
    res_tac >> fs[] >> rw[] ) >>
  rw[] >> fs[]
QED

Theorem term_ok_aconv:
   ∀sig t1 t2. ACONV t1 t2 ∧ term_ok sig t1 ∧ welltyped t2 ⇒ term_ok sig t2
Proof
  rw[ACONV_def] >> imp_res_tac term_ok_raconv >> fs[]
QED

Theorem term_ok_VFREE_IN:
   ∀sig t x. VFREE_IN x t ∧ term_ok sig t ⇒ term_ok sig x
Proof
  gen_tac >> Induct >> simp[term_ok_def] >> metis_tac[]
QED

(* de Bruijn terms, for showing alpha-equivalence respect
   by substitution and instantiation *)

Datatype:
  dbterm =
    dbVar mlstring type
  | dbBound num
  | dbConst mlstring type
  | dbComb dbterm dbterm
  | dbAbs type dbterm
End

(* bind a variable above a de Bruijn term *)

Definition bind_def[simp]:
  (bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) ∧
  bind v n (dbBound m) = dbBound m ∧
  bind v n (dbConst x ty) = dbConst x ty ∧
  bind v n (dbComb t1 t2) = dbComb (bind v n t1) (bind v n t2) ∧
  bind v n (dbAbs ty tm) = dbAbs ty (bind v (n+1) tm)
End

(* conversion into de Bruijn *)

Definition db_def[simp]:
  db (Var x ty) = dbVar x ty ∧
  db (Const x ty) = dbConst x ty ∧
  db (Comb t1 t2) = dbComb (db t1) (db t2) ∧
  db (Abs v tm) = dbAbs (typeof v) (bind (dest_var v) 0 (db tm))
End

(* de Bruijn versions of VSUBST and VFREE_IN *)

Definition dbVSUBST_def[simp]:
  dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty) ∧
  dbVSUBST ilist (dbBound m) = dbBound m ∧
  dbVSUBST ilist (dbConst x ty) = dbConst x ty ∧
  dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2) ∧
  dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t)
End

Definition dbVFREE_IN_def[simp]:
  (dbVFREE_IN v (dbVar x ty) ⇔ dbVar x ty = v) ∧
  (dbVFREE_IN v (dbBound n) ⇔ F) ∧
  (dbVFREE_IN v (dbConst x ty) ⇔ dbConst x ty = v) ∧
  (dbVFREE_IN v (dbComb t1 t2) ⇔ (dbVFREE_IN v t1 ∨ dbVFREE_IN v t2)) ∧
  (dbVFREE_IN v (dbAbs ty t) ⇔ dbVFREE_IN v t)
End

Theorem bind_not_free:
   ∀t n v. ¬dbVFREE_IN (UNCURRY dbVar v) t ⇒ bind v n t = t
Proof
  Induct >> simp[] >> rw[]
QED

Theorem bind_dbVSUBST:
   ∀tm v n ls.
    (UNCURRY dbVar v) ∉ set (MAP SND ls) ∧
    (∀k. dbVFREE_IN k tm ∧ MEM k (MAP SND ls) ⇒
        ¬dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
    ⇒
    bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm)
Proof
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[] >- (
    `REV_ASSOCD (dbVar m t) ls (dbVar m t) = dbVar m t` by (
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[REV_ASSOCD_MEM,MEM_MAP] ) >>
    rw[] ) >>
  Induct_on`ls` >- simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> strip_tac >>
  rw[] >> metis_tac[bind_not_free]
QED

Theorem bind_dbVSUBST_cons:
   ∀tm z x n ls.
    ¬dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
    ⇒
    bind z n (dbVSUBST ((UNCURRY dbVar z,UNCURRY dbVar x)::ls) tm) = dbVSUBST ls (bind x n tm)
Proof
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[REV_ASSOCD] >>fs[] >- (
    Cases_on`z`>>fs[] ) >>
  Cases_on`z`>>fs[] >- (
    Cases_on`x`>>fs[] ) >>
  match_mp_tac bind_not_free >> fs[]
QED

Theorem dbVSUBST_frees:
   ∀tm ls ls'.
    (∀k. dbVFREE_IN k tm ⇒ REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
     ⇒
      dbVSUBST ls tm = dbVSUBST ls' tm
Proof
  Induct >> simp[]
QED

Theorem dbVFREE_IN_bind:
   ∀tm x v n b. dbVFREE_IN x (bind v n tm) ⇔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm
Proof
  Induct >> simp[] >> rw[] >- metis_tac[]
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]>>
    metis_tac[])
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]) >>
  Cases_on`v`>>fs[]>>
  Cases_on`x=dbVar q r`>>fs[]
QED

Theorem dbVFREE_IN_VFREE_IN:
   ∀tm x. welltyped tm ⇒ (dbVFREE_IN (db x) (db tm) ⇔ VFREE_IN x tm)
Proof
  Induct >> simp[VFREE_IN_def] >- (
    ntac 2 gen_tac >> Cases >> simp[VFREE_IN_def] )
  >- (
    ntac 2 gen_tac >> Cases >> simp[VFREE_IN_def] ) >>
  simp[dbVFREE_IN_bind,PULL_EXISTS] >>
  Cases >> simp[] >> metis_tac[]
QED

Theorem MAP_db_FILTER_neq:
   ∀ls z ty. MAP (λ(x,y). (db x, db y)) (FILTER (λ(x,y). y ≠ Var z ty) ls) = FILTER (λ(x,y). y ≠ dbVar z ty) (MAP (λ(x,y). (db x, db y)) ls)
Proof
  Induct >> simp[] >>
  Cases >> simp[] >>
  rw[] >-( Cases_on`r`>>fs[] ) >> fs[]
QED

Theorem REV_ASSOCD_MAP_db:
   ∀ls k ky.
    (∀k v. MEM (v,k) ls ⇒ ∃x ty. k = Var x ty)
    ⇒
    REV_ASSOCD (dbVar k ky) (MAP (λ(x,y). (db x, db y)) ls) (dbVar k ky) = db (REV_ASSOCD (Var k ky) ls (Var k ky))
Proof
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >>
  rw[] >> fs[] >- (
    Cases_on`r`>>fs[]>>rw[] ) >>
  `∃x ty. r = Var x ty` by metis_tac[] >> fs[] >>
  metis_tac[]
QED

Theorem dbVFREE_IN_dbVSUBST:
   ∀tm u uty ilist.
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ⇔
      ∃y ty. dbVFREE_IN (dbVar y ty) tm ∧
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty))
Proof
  Induct >> simp[] >> rw[] >> metis_tac[]
QED

Theorem VSUBST_dbVSUBST:
   ∀tm ilist.
    welltyped tm ∧
    (∀k v. MEM (v,k) ilist ⇒ welltyped v ∧ ∃x ty. k = Var x ty)
    ⇒
    db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm)
Proof
  Induct >- (
    simp[VSUBST_def] >>
    ntac 2 gen_tac >> Induct >>
    simp[REV_ASSOCD] >>
    Cases >> simp[REV_ASSOCD] >>
    strip_tac >>
    qpat_x_assum`p ⇒ qq`mp_tac >>
    impl_tac >- metis_tac[] >> strip_tac >>
    rw[] >> fs[] >>
    Cases_on`r`>>fs[] )
  >- simp[VSUBST_def]
  >- (
    simp[VSUBST_def] >>
    metis_tac[] ) >>
  gen_tac >> simp[GSYM AND_IMP_INTRO] >>
  disch_then(qx_choosel_then[`b`,`bty`]strip_assume_tac) >>
  srw_tac[][VSUBST_def] >>
  reverse(rw[]) >- (
    first_x_assum(qspec_then`ilist'`mp_tac) >>
    impl_tac >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[Abbr`t'`] >>
    qmatch_abbrev_tac`bind v n (dbVSUBST ls tt) = X` >>
    qspecl_then[`tt`,`v`,`n`,`ls`]mp_tac bind_dbVSUBST >>
    impl_tac >- (
      fs[MEM_MAP,EVERY_MEM,EXISTS_PROD,FORALL_PROD,Abbr`ls`,GSYM LEFT_FORALL_IMP_THM,Abbr`ilist'`,MEM_FILTER] >>
      qunabbrev_tac`v` >>
      conj_tac >- (
        gen_tac >> Cases >> simp[] >>
        metis_tac[] ) >>
      qx_gen_tac`k` >> strip_tac >> simp[] >>
      simp[MAP_db_FILTER_neq] >>
      simp[REV_ASSOCD_FILTER] >>
      qmatch_assum_rename_tac`k = db u` >>
      `∃x ty. u = Var x ty` by metis_tac[] >>
      qspecl_then[`ilist`,`x`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
      impl_tac >- metis_tac[] >>
      simp[] >> strip_tac >>
      BasicProvers.CASE_TAC >- (
        qmatch_abbrev_tac`¬dbVFREE_IN (dbVar s t) (db tz)` >>
        qspecl_then[`tz`,`Var s t`]mp_tac dbVFREE_IN_VFREE_IN >>
        impl_tac >- (
          qmatch_assum_abbrev_tac`Abbrev(tz = REV_ASSOCD y l d)` >>
          Q.ISPECL_THEN[`l`,`y`,`d`]mp_tac REV_ASSOCD_MEM >>
          map_every qunabbrev_tac[`y`,`tz`,`d`] >>
          strip_tac >> simp[] >> metis_tac[]) >>
        simp[] >> strip_tac >>
        rpt BasicProvers.VAR_EQ_TAC >>
        spose_not_then strip_assume_tac >>
        metis_tac[REV_ASSOCD_MEM,VFREE_IN_def,dbVFREE_IN_VFREE_IN] ) >>
      fs[] ) >>
    rw[Abbr`ls`,Abbr`ilist'`,Abbr`X`] >>
    match_mp_tac dbVSUBST_frees >>
    simp[MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
    rw[Abbr`v`] >>
    fs[dbVFREE_IN_bind]) >>
  TRY(rw[Abbr`z`] >> NO_TAC) >>
  first_x_assum(qspec_then`ilist''`mp_tac) >>
  impl_tac >- (
    simp[Abbr`ilist''`,Abbr`ilist'`,MEM_FILTER] >>
    metis_tac[WELLTYPED_CLAUSES] ) >>
  qunabbrev_tac`ilist''` >> rw[] >>
  qmatch_abbrev_tac`bind v n (dbVSUBST ((zz,x)::ls) tt) = X` >>
  qmatch_assum_rename_tac`Abbrev(z = Var (VARIANT ta s tb) bty)` >>
  qspecl_then[`tt`,`v`,`(b,tb)`,`n`,`ls`]mp_tac bind_dbVSUBST_cons >>
  simp[Abbr`v`] >>
  impl_tac >- (
    qunabbrev_tac`zz` >>
    simp[Abbr`z`,dbVFREE_IN_dbVSUBST] >>
    Q.PAT_ABBREV_TAC`z = VARIANT ta s tb` >>
    simp[dbVFREE_IN_bind] >>
    rpt gen_tac >>
    qspecl_then[`ilist'`,`y`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
    impl_tac >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`tv = db tu` >>
    qspecl_then[`tu`,`Var z tb`]mp_tac dbVFREE_IN_VFREE_IN >>
    impl_tac >- (
      qmatch_assum_abbrev_tac`Abbrev(tu = REV_ASSOCD c l d)` >>
      Q.ISPECL_THEN[`l`,`c`,`d`]mp_tac REV_ASSOCD_MEM >>
      map_every qunabbrev_tac[`c`,`tu`,`d`,`l`,`ilist'`] >>
      strip_tac >> simp[] >> fs[MEM_FILTER] >> metis_tac[]) >>
    rw[] >>
    qmatch_assum_rename_tac`welltyped tm` >>
    qspecl_then[`tm`,`Var y ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[Abbr`tt`] >>
    spose_not_then strip_assume_tac >>
    qsuff_tac`VFREE_IN (Var z tb) ta`>-
      metis_tac[VARIANT_THM] >>
    simp[Abbr`tu`,Abbr`ta`,VFREE_IN_VSUBST] >>
    metis_tac[] ) >>
  rw[] >>
  simp[Abbr`ls`] >> fs[Abbr`z`,Abbr`zz`,Abbr`X`] >>
  match_mp_tac dbVSUBST_frees >>
  simp[Abbr`ilist'`,MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
  rw[Abbr`x`] >>
  fs[dbVFREE_IN_bind]
QED

(* de Bruijn version of INST *)

Definition dbINST_def[simp]:
  dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbBound n) = dbBound n ∧
  dbINST tyin (dbConst x ty) = dbConst x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2) ∧
  dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)
End

Theorem dbINST_bind:
   ∀tm v n ls.
      (∀ty. dbVFREE_IN (dbVar (FST v) ty) tm ∧ (TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)) ⇒ ty = SND v)
      ⇒ dbINST ls (bind v n tm) = bind (FST v,TYPE_SUBST ls (SND v)) n (dbINST ls tm)
Proof
  Induct >> simp[] >>
  Cases_on`v`>>simp[] >>
  rpt strip_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[]
QED

Theorem dbVSUBST_nil[simp]:
   ∀tm. dbVSUBST [] tm = tm
Proof
  Induct >> simp[REV_ASSOCD]
QED

Theorem INST_CORE_dbINST:
   ∀tm tyin env tmi.
      welltyped tm ∧ (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      INST_CORE env tyin tm = Result tmi ⇒
        db tmi = dbINST tyin (db tm)
Proof
  completeInduct_on`sizeof tm` >> Cases >> simp[] >- (
    strip_tac >>
    simp[INST_CORE_def] >>
    rw[] >> rw[] )
  >- (
    strip_tac >> rw[INST_CORE_def] >> rw[] )
  >- (
    strip_tac >>
    simp[INST_CORE_def] >>
    rw[] >> fs[] >>
    qmatch_assum_rename_tac`typeof t1 = Fun (typeof t2) rty` >>
    first_assum(qspec_then`sizeof t1`mp_tac) >>
    first_x_assum(qspec_then`sizeof t2`mp_tac) >>
    simp[] >>
    disch_then(qspec_then`t2`strip_assume_tac) >>
    disch_then(qspec_then`t1`strip_assume_tac) >>
    rfs[] >>
    Cases_on`INST_CORE env tyin t1` >>fs[] >>
    Cases_on`INST_CORE env tyin t2`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >>
  rpt gen_tac >> simp[GSYM AND_IMP_INTRO] >>
  disch_then(qx_choosel_then[`b`,`bty`]strip_assume_tac) >>
  qmatch_assum_rename_tac`welltyped tm` >>
  simp[INST_CORE_def] >>
  rw[] >> fs[] >>
  qmatch_assum_abbrev_tac`IS_RESULT X` >>
  Cases_on`X`>>
  pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> fs[] >- (
    qmatch_abbrev_tac`bind (x,TYPE_SUBST tyin ty) 0 (db tt) = X` >>
    ntac 3 (pop_assum kall_tac) >>
    qspecl_then[`db tm`,`x,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
    impl_tac >- (
      qx_gen_tac`ty2` >>
      qspecl_then[`tm`,`Var x ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
      rw[] >>
      qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
      qspecl_then[`sizeof tm`,`tm`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
      impl_tac >- (
        simp[Abbr`env'`] >>
        metis_tac[] ) >>
      simp[Abbr`Y`] >>
      simp[Abbr`env'`,REV_ASSOCD] >>
      strip_tac >>
      last_x_assum(qspecl_then[`x`,`ty2`]mp_tac) >>
      simp[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    disch_then(qspec_then`tm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tyin`,`env'`,`tt`]mp_tac) >>
    simp[Abbr`env'`] >>
    impl_tac >- metis_tac[] >>
    rw[] ) >>
  qmatch_abbrev_tac`bind (z,TYPE_SUBST tyin ty) 0 (db tt) = dbINST tyin (bind (x,ty) 0 (db tm))` >>
  ntac 3 (pop_assum kall_tac) >>
  qspecl_then[`db tm`,`z,ty`,`x,ty`,`0`,`[]`]mp_tac bind_dbVSUBST_cons >>
  impl_tac >- (
    simp[] >>
    simp[dbVFREE_IN_bind] >>
    `∃tmi. INST_CORE [] tyin tm = Result tmi` by (
      Cases_on`INST_CORE [] tyin tm`>>simp[] >>
      imp_res_tac INST_CORE_NIL_IS_RESULT >>
      pop_assum(qspec_then`tyin`strip_assume_tac) >>
      rfs[] ) >> fs[] >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    disch_then(qspec_then`tm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tyin`,`[]`,`tmi`]mp_tac) >>
    rw[] >>
    spose_not_then strip_assume_tac >>
    qspecl_then[`tm`,`Var z ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    simp[] >>
    qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    simp[] >> strip_tac >>
    first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
    simp[VARIANT_THM,Abbr`z`] >>
    metis_tac[] ) >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qmatch_assum_abbrev_tac`INST_CORE env' tyin tv = Result tt` >>
  `sizeof tv = sizeof tm` by (
    simp[Abbr`tv`] >>
    match_mp_tac SIZEOF_VSUBST >>
    simp[] ) >>
  first_x_assum(qspec_then`sizeof tv`mp_tac) >> simp[] >>
  disch_then(qspec_then`tv`mp_tac) >> simp[] >>
  disch_then(qspecl_then[`tyin`,`env'`,`tt`]mp_tac) >>
  `welltyped tv` by (
    simp[Abbr`tv`] >>
    match_mp_tac VSUBST_WELLTYPED >>
    simp[] >> simp[Once has_type_cases] ) >>
  impl_tac >- (
    simp[Abbr`env'`] >>
    metis_tac[] ) >>
  rw[] >>
  qspecl_then[`tm`,`[Var z ty,Var x ty]`]mp_tac VSUBST_dbVSUBST >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qspecl_then[`db tv`,`z,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
  impl_tac >- (
    simp[] >>
    qx_gen_tac`ty2` >>
    qspecl_then[`tv`,`Var z ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[] >>
    qspecl_then[`sizeof tv`,`tv`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    impl_tac >- (
      simp[Abbr`env'`] >>
      metis_tac[] ) >>
    simp[] >>
    simp[Abbr`env'`,REV_ASSOCD] >>
    strip_tac >>
    last_x_assum(qspecl_then[`z`,`ty2`]mp_tac) >>
    simp[] ) >>
  simp[]
QED

Theorem INST_dbINST:
   ∀tm tyin.
      welltyped tm ⇒
      db (INST tyin tm) = dbINST tyin (db tm)
Proof
  rw[INST_def] >>
  imp_res_tac INST_CORE_NIL_IS_RESULT >>
  pop_assum(qspec_then`tyin`strip_assume_tac) >>
  Cases_on`INST_CORE [] tyin tm`>>fs[] >>
  qspecl_then[`tm`,`tyin`,`[]`,`a`]mp_tac INST_CORE_dbINST >>
  simp[]
QED

(* conversion into de Bruijn given an environment of already bound variables *)

Definition dbterm_def[simp]:
  (dbterm env (Var s ty) =
     case find_index (s,ty) env 0 of SOME n => dbBound n | NONE => dbVar s ty) ∧
  (dbterm env (Const s ty) = dbConst s ty) ∧
  (dbterm env (Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) ∧
  (dbterm env (Abs v t) = dbAbs (typeof v) (dbterm ((dest_var v)::env) t))
End

Definition bind_list_aux_def[simp]:
  bind_list_aux n [] tm = tm ∧
  bind_list_aux n (v::vs) tm = bind_list_aux (n+1) vs (bind v n tm)
End

Theorem bind_list_aux_clauses:
   (∀env m. bind_list_aux m env (dbBound n) = dbBound n) ∧
    (∀env m. bind_list_aux m env (dbConst x ty) = dbConst x ty) ∧
    (∀env m t1 t2. bind_list_aux m env (dbComb t1 t2) = dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
    (∀env m ty tm. bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m+1) env tm))
Proof
  rpt conj_tac >> Induct >> simp[]
QED

Theorem dbterm_bind:
   ∀tm env. dbterm env tm = bind_list_aux 0 env (db tm)
Proof
  Induct >> simp[bind_list_aux_clauses] >>
  gen_tac >>
  Q.SPEC_TAC(`0n`,`n`) >>
  Induct_on`env` >> simp[find_index_def] >>
  Cases >> simp[] >>
  rw[] >> rw[bind_list_aux_clauses]
QED

Theorem dbterm_db:
   ∀tm. dbterm [] tm = db tm
Proof
  rw[dbterm_bind]
QED

(* alpha-equivalence on de Bruijn terms *)

Theorem dbterm_RACONV:
   ∀t1 env1 t2 env2. welltyped t1 ∧ welltyped t2 ∧ dbterm env1 t1 = dbterm env2 t2 ∧ LENGTH env1 = LENGTH env2 ⇒
      RACONV (ZIP(MAP (UNCURRY Var) env1,MAP (UNCURRY Var) env2)) (t1,t2)
Proof
  Induct >- (
    ntac 3 gen_tac >> simp[] >>
    Cases >> simp[RACONV] >>
    TRY (BasicProvers.CASE_TAC >> simp[] >> NO_TAC) >>
    Induct_on`env1` >- (
      simp[find_index_def,LENGTH_NIL_SYM,ALPHAVARS_def] ) >>
    gen_tac >> Cases >> simp[] >>
    simp[find_index_def,ALPHAVARS_def] >>
    Cases_on`h`>>Cases_on`h'`>>simp[] >>
    simp[Once find_index_shift_0] >>
    simp[Once find_index_shift_0,SimpRHS] >>
    rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[] )
  >- (
    simp[] >> ntac 3 gen_tac >>
    Cases >> simp[RACONV] >>
    gen_tac >> BasicProvers.CASE_TAC >> simp[] )
  >- (
    simp[] >>
    gen_tac >> Cases >> simp[RACONV] >>
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  simp[] >>
  gen_tac >>
  Cases >> simp[RACONV] >- (
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  rw[] >> res_tac >> fs[]
QED

Theorem RACONV_dbterm:
   ∀env tp. RACONV env tp ⇒
    welltyped (FST tp) ∧ welltyped (SND tp) ∧
    (∀vp. MEM vp env ⇒ (∃x ty. (FST vp = Var x ty)) ∧ (∃x ty. (SND vp = Var x ty)))
     ⇒ dbterm (MAP (dest_var o FST) env) (FST tp) = dbterm (MAP (dest_var o SND) env) (SND tp)
Proof
  ho_match_mp_tac RACONV_ind >> rw[] >> rw[] >> fs[PULL_EXISTS] >> rw[] >>
  TRY (
    first_x_assum match_mp_tac >>
    rw[] >> rw[] >> NO_TAC ) >>
  Induct_on`env` >> simp[ALPHAVARS_def] >>
  rw[] >> rw[] >- rw[find_index_def] >> fs[] >>
  simp[find_index_def] >>
  `∃x ty. FST h = Var x ty` by metis_tac[] >>
  `∃y tz. SND h = Var y tz` by metis_tac[] >>
  simp[] >>
  simp[Once find_index_shift_0] >>
  simp[Once find_index_shift_0,SimpRHS] >>
  rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[]
QED

Theorem dbterm_ACONV:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2)
Proof
  rw[ACONV_def,EQ_IMP_THM] >- (
    qspecl_then[`[]`,`t1,t2`]mp_tac RACONV_dbterm >> simp[] ) >>
  qspecl_then[`t1`,`[]`,`t2`,`[]`]mp_tac dbterm_RACONV >>
  simp[]
QED

Theorem ACONV_db:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ db t1 = db t2)
Proof
  metis_tac[dbterm_ACONV,dbterm_db]
QED

(* respect of alpha-equivalence by VSUBST and INST follows *)

Theorem ACONV_VSUBST:
   ∀t1 t2 ilist.
    welltyped t1 ∧ welltyped t2 ∧
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty ∧ v has_type ty) ∧
    ACONV t1 t2 ⇒
    ACONV (VSUBST ilist t1) (VSUBST ilist t2)
Proof
  rw[] >>
  imp_res_tac VSUBST_WELLTYPED >>
  rw[ACONV_db] >>
  metis_tac[ACONV_db,VSUBST_dbVSUBST,welltyped_def]
QED

Theorem ACONV_INST:
   ∀t1 t2 tyin. welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 ⇒ ACONV (INST tyin t1) (INST tyin t2)
Proof
  rw[] >>
  imp_res_tac INST_WELLTYPED >>
  rw[ACONV_db] >> imp_res_tac INST_dbINST >>
  rfs[ACONV_db]
QED

(* list of bound variable names in a term *)

Definition bv_names_def[simp]:
  bv_names (Var _ _) = [] ∧
  bv_names (Const _ _) = [] ∧
  bv_names (Comb s t) = bv_names s ++ bv_names t ∧
  bv_names (Abs v t) = (FST(dest_var v))::bv_names t
End

(* Simpler versions (non-capture-avoiding) of substitution and instantiation.
   We do the semantics proofs on these and then use the fact that it is
   alpha-equivalence respecting, and suitable equivalent term always exists
   (see below). *)

Definition simple_subst_def[simp]:
  (simple_subst ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
  (simple_subst ilist (Const x ty) = Const x ty) ∧
  (simple_subst ilist (Comb t1 t2) = Comb (simple_subst ilist t1) (simple_subst ilist t2)) ∧
  (simple_subst ilist (Abs v tm) =
    Abs v (simple_subst (FILTER (λ(s',s). (s ≠ v)) ilist) tm))
End

Definition simple_inst_def[simp]:
  simple_inst tyin (Var x ty) = Var x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Const x ty) = Const x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Comb s t) = Comb (simple_inst tyin s) (simple_inst tyin t) ∧
  simple_inst tyin (Abs v t) = Abs (simple_inst tyin v) (simple_inst tyin t)
End

Theorem VSUBST_simple_subst:
   ∀tm ilist. DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
               (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty) ∧
               welltyped tm
               ⇒ VSUBST ilist tm = simple_subst ilist tm
Proof
  Induct
  >- simp[VSUBST_def]
  >- simp[VSUBST_def]
  >- (
    simp[VSUBST_def] >> rw[] >>
    first_x_assum match_mp_tac >>
    fs[IN_DISJOINT] >>
    metis_tac[] ) >>
  simp[VSUBST_def] >>
  rpt gen_tac >> strip_tac >>
  BasicProvers.CASE_TAC >- (
    fs[EXISTS_MEM,MEM_FILTER,UNCURRY] >>
    Cases_on`e`>>fs[]>>res_tac>>fs[MEM_MAP,FORALL_PROD,EXISTS_PROD]>>
    metis_tac[VFREE_IN_def]) >>
  first_x_assum match_mp_tac >>
  simp[rich_listTheory.MAP_SND_FILTER_NEQ,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
  fs[MEM_MAP,EXISTS_PROD,IN_DISJOINT] >>
  metis_tac[]
QED

Theorem INST_CORE_simple_inst:
   ∀env tyin tm.
      ALL_DISTINCT (bv_names tm ++ (MAP (FST o dest_var o SND) env)) ∧
      DISJOINT (set(bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty ty'. VFREE_IN (Var x ty) tm ∧ MEM (Var x ty') (MAP FST env) ⇒ ty' = ty) ∧
      welltyped tm
      ⇒ INST_CORE env tyin tm = Result (simple_inst tyin tm)
Proof
  ho_match_mp_tac INST_CORE_ind >>
  conj_tac >- (
    simp[INST_CORE_def] >> rpt gen_tac >> strip_tac >> rw[] >>
    imp_res_tac (REWRITE_RULE[PROVE[]``A ∨ B ⇔ ¬B ⇒ A``]REV_ASSOCD_MEM) >>
    qmatch_assum_abbrev_tac`MEM (p,q) env` >>
    first_x_assum(qspecl_then[`p`,`q`]mp_tac) >>
    simp[Abbr`q`] >> rw[] >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  conj_tac >- simp[INST_CORE_def] >>
  conj_tac >- (
    srw_tac[][INST_CORE_def] >>
    `sres = Result (simple_inst tyin tm)` by (
      first_x_assum match_mp_tac >>
      fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
      metis_tac[] ) >>
    qunabbrev_tac`sres`>>simp[]>>fs[] >>
    `tres = Result (simple_inst tyin tm')` by (
      first_x_assum match_mp_tac >>
      fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
      metis_tac[] ) >>
    unabbrev_all_tac >> simp[] ) >>
  srw_tac[][INST_CORE_def] >>
  fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[] >>rfs[] >>
  `tres = Result (simple_inst tyin tm)` by (
    first_x_assum match_mp_tac >>
    conj_tac >- fs[ALL_DISTINCT_APPEND] >>
    conj_tac >- ( fs[IN_DISJOINT] >> metis_tac[] ) >>
    conj_tac >- metis_tac[] >>
    qx_genl_tac[`u`,`uy`,`uy'`] >>
    reverse(Cases_on`u=x ∧ uy' = ty`) >- (
      simp[] >> strip_tac >> fs[] >>
      TRY(first_x_assum match_mp_tac >> fs[] >> metis_tac[]) >>
      Cases_on`u≠x`>-metis_tac[]>>fs[]>>
      fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
      metis_tac[dest_var_def,FST] ) >>
    fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[dest_var_def,FST] ) >>
  fs[]
QED

Theorem INST_simple_inst:
   ∀tyin tm.
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      welltyped tm
      ⇒
      INST tyin tm = simple_inst tyin tm
Proof
  rw[INST_def] >>
  qspecl_then[`[]`,`tyin`,`tm`]mp_tac INST_CORE_simple_inst >>
  simp[]
QED

Theorem simple_subst_has_type:
   ∀tm ty.
      tm has_type ty ⇒
      ∀subst.
        EVERY (λ(s',s). s' has_type typeof s) subst ⇒
        simple_subst subst tm has_type ty
Proof
  ho_match_mp_tac has_type_ind >>
  simp[] >> rw[] >- (
    simp[REV_ASSOCD_ALOOKUP] >> BasicProvers.CASE_TAC >-
    rw[Once has_type_cases] >> imp_res_tac ALOOKUP_MEM >>
    fs[EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[typeof_def])
  >- ( rw[Once has_type_cases] )
  >- ( rw[Once has_type_cases] >> metis_tac[] ) >>
  rw[Once has_type_cases] >>
  first_x_assum match_mp_tac >>
  fs[EVERY_FILTER,EVERY_MEM]
QED

Theorem simple_inst_has_type:
   ∀tm tyin. welltyped tm ⇒ simple_inst tyin tm has_type (TYPE_SUBST tyin (typeof tm))
Proof
  Induct >> rw[] >> rw[Once has_type_cases] >> fs[] >> metis_tac[]
QED

(* rename bound variables from a source of names *)

Definition rename_bvars_def:
  rename_bvars names env (Var s ty) = (names, Var (REV_ASSOCD (s,ty) env s) ty) ∧
  rename_bvars names env (Const s ty) = (names, Const s ty) ∧
  (rename_bvars names env (Comb t1 t2) =
     let (names,t1) = rename_bvars names env t1 in
     let (names,t2) = rename_bvars names env t2 in
     (names, Comb t1 t2)) ∧
  (rename_bvars [] env (Abs v tm) =
     let (names, tm) = rename_bvars [] env tm in
     (names, Abs v tm)) ∧
  (rename_bvars (s'::names) env (Abs v tm) =
     let (names,tm) = rename_bvars names ((s',dest_var v)::env) tm in
     (names, Abs (Var s' (typeof v)) tm))
End

Theorem FST_rename_bvars:
   ∀names env tm. LENGTH (bv_names tm) ≤ LENGTH names ⇒ (FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names)
Proof
  ho_match_mp_tac (theorem"rename_bvars_ind") >>
  simp[rename_bvars_def] >>
  rw[UNCURRY] >> rw[] >>
  Cases_on`rename_bvars names env tm` >> fs[] >>
  fsrw_tac[ARITH_ss][] >>
  REWRITE_TAC[Once arithmeticTheory.ADD_SYM] >>
  match_mp_tac rich_listTheory.DROP_DROP >>
  simp[]
QED

Theorem rename_bvars_RACONV:
   ∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧
    DISJOINT (set (MAP FST env ++ names)) (set (MAP (FST o SND) env ++ bv_names tm)) ∧
    DISJOINT (set (MAP FST env ++ names)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
    ALL_DISTINCT (MAP FST env ++ names) ∧
    welltyped tm
    ⇒ RACONV (MAP (λ(s',(s,ty)). (Var s ty, Var s' ty)) env) (tm, SND (rename_bvars names env tm))
Proof
  ho_match_mp_tac (theorem"rename_bvars_ind") >>
  simp[rename_bvars_def,RACONV] >>
  conj_tac >- (
    gen_tac >>
    Induct >> simp[ALPHAVARS_def,REV_ASSOCD] >>
    qx_gen_tac`p` >> PairCases_on`p` >>
    simp[] >> rw[] >>
    simp[REV_ASSOCD] >>
    Cases_on`s=p1`>>simp[]>-(
      Cases_on`ty=p2`>>simp[]>>rw[]>>
      fs[IN_DISJOINT,ALL_DISTINCT_APPEND]>>
      metis_tac[]) >>
    Cases_on`REV_ASSOCD (s,ty) env s = p0`>>simp[]>-(
      `REV_ASSOCD (s,ty) env s ≠ s` by PROVE_TAC[] >>
      imp_res_tac (REWRITE_RULE[PROVE[]``A ∨ B ⇔ ¬B ⇒ A``]REV_ASSOCD_MEM) >>
      fs[MEM_MAP,FORALL_PROD] >> metis_tac[] ) >>
    first_x_assum match_mp_tac >>
    fs[IN_DISJOINT,ALL_DISTINCT_APPEND] >>
    metis_tac[] ) >>
  conj_tac >- (
    srw_tac[][UNCURRY] >>
    simp[RACONV] >>
    conj_tac >> first_x_assum (match_mp_tac o MP_CANON) >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    TRY (
      qexists_tac`SND (rename_bvars names env tm)`>>simp[] >>
      qspecl_then[`names`,`env`,`tm`]mp_tac FST_rename_bvars >>
      impl_tac >- DECIDE_TAC >> strip_tac >>
      first_assum (assume_tac o Q.AP_TERM`LENGTH`) >>
      fs[LENGTH_DROP] >>
      `LENGTH (bv_names tm) ≤ LENGTH names` by DECIDE_TAC >>
      conj_tac >- (
        rw[] >> spose_not_then strip_assume_tac >>
        imp_res_tac rich_listTheory.MEM_DROP_IMP >>
        metis_tac[] ) >>
      conj_tac >- (
        rw[] >> spose_not_then strip_assume_tac >>
        imp_res_tac rich_listTheory.MEM_DROP_IMP >>
        metis_tac[] ) >>
      conj_tac >- metis_tac[ALL_DISTINCT_DROP] >>
      rw[] >> spose_not_then strip_assume_tac >>
      imp_res_tac rich_listTheory.MEM_DROP_IMP >>
      metis_tac[]) >>
    metis_tac[]) >>
  rw[UNCURRY] >>
  rw[RACONV] >> fs[] >>
  first_x_assum match_mp_tac >>
  simp[] >>
  fs[IN_DISJOINT,ALL_DISTINCT_APPEND] >>
  rfs[] >> metis_tac[]
QED

Theorem rename_bvars_ACONV:
   ∀names tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧ ALL_DISTINCT names ∧
    DISJOINT (set names) {x | MEM x (bv_names tm) ∨ ∃ty. VFREE_IN (Var x ty) tm} ∧
    welltyped tm
    ⇒
    ACONV tm (SND (rename_bvars names [] tm))
Proof
  rw[ACONV_def] >>
  qspecl_then[`names`,`[]`,`tm`]mp_tac rename_bvars_RACONV >>
  simp[] >> disch_then match_mp_tac >>
  fs[IN_DISJOINT] >> metis_tac[]
QED

Theorem rename_bvars_has_type:
   ∀names env tm ty. tm has_type ty ⇒ SND (rename_bvars names env tm) has_type ty
Proof
  ho_match_mp_tac(theorem"rename_bvars_ind") >>
  srw_tac[][rename_bvars_def] >> rw[] >> fs[]
  >- fs[Once has_type_cases] >>
  qpat_x_assum`X has_type Y`mp_tac >>
  simp[Once has_type_cases] >> strip_tac >>
  simp[Once has_type_cases] >> metis_tac[]
QED

Theorem rename_bvars_welltyped:
   ∀names env tm. welltyped tm ⇒ welltyped (SND (rename_bvars names env tm))
Proof
  metis_tac[rename_bvars_has_type,welltyped_def]
QED

(* appropriate fresh term for using the simple functions above *)

val fresh_def = new_specification("fresh_def",["fresh"],
  IN_INFINITE_NOT_FINITE
  |> Q.ISPECL[`UNIV:string set`,`s:string set`]
  |> REWRITE_RULE[INST_TYPE[alpha|->``:char``]INFINITE_LIST_UNIV,IN_UNIV]
  |> SIMP_RULE(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM]
  |> Q.GEN`s`
  |> SIMP_RULE(srw_ss())[SKOLEM_THM])

Theorem fresh_union:
   FINITE s ∧ FINITE t ⇒ fresh (s ∪ t) ∉ s ∧ fresh (s ∪ t) ∉ t
Proof
  metis_tac[fresh_def,FINITE_UNION,IN_UNION]
QED

Theorem fresh_names_exist:
   ∀s n. FINITE (s:string set) ⇒ ∃names. LENGTH names = n ∧ ALL_DISTINCT names ∧ DISJOINT (set names) s
Proof
  gen_tac >> Induct >> strip_tac
  >- (qexists_tac`[]`>>simp[]) >> rw[] >> fs[] >>
  qexists_tac`fresh (s ∪ set names)::names` >>
  simp[fresh_union]
QED

Theorem bv_names_rename_bvars:
   ∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ⇒
    bv_names (SND (rename_bvars names env tm)) = TAKE (LENGTH (bv_names tm)) names
Proof
  ho_match_mp_tac(theorem"rename_bvars_ind")>>
  simp[rename_bvars_def] >>
  conj_tac >- (
    rw[UNCURRY] >>
    Cases_on`rename_bvars names env tm`>>fs[] >>
    `LENGTH (bv_names tm) ≤ LENGTH names` by DECIDE_TAC >> fs[] >>
    qspecl_then[`names`,`env`,`tm`]mp_tac FST_rename_bvars >>
    rw[] >> fs[] >>
    `LENGTH (bv_names tm') ≤ LENGTH names - LENGTH (bv_names tm)` by DECIDE_TAC >> fs[] >>
    simp[TAKE_SUM] ) >>
  rw[UNCURRY]
QED

(* various rewrites for FINITE sets to make this go through *)

Theorem FINITE_VFREE_IN[simp]:
   ∀tm. FINITE {x | ∃ty. VFREE_IN (Var x ty) tm}
Proof
  Induct >> simp[] >- (
    qmatch_assum_abbrev_tac`FINITE s1` >>
    qpat_x_assum`FINITE s1`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE s2` >>
    strip_tac >>
    qmatch_abbrev_tac`FINITE s3` >>
    qsuff_tac`s3 = s1 ∪ s2` >- metis_tac[FINITE_UNION] >>
    unabbrev_all_tac >> simp[EXTENSION] >> metis_tac[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE a` >>
  qmatch_abbrev_tac`FINITE b` >>
  qsuff_tac`b ⊆ a` >- metis_tac[SUBSET_FINITE] >>
  unabbrev_all_tac >> simp[SUBSET_DEF] >>
  metis_tac[]
QED

Theorem FINITE_VFREE_IN_2[simp]:
   ∀tm. FINITE {(x,ty) | VFREE_IN (Var x ty) tm}
Proof
  Induct >> simp[] >- (
    rw[] >>
    qmatch_abbrev_tac`FINITE x` >>
    qsuff_tac`∃y. x = {y}`>-metis_tac[FINITE_SING] >>
    rw[EXTENSION,Abbr`x`,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] )
  >- (
    qmatch_assum_abbrev_tac`FINITE s1` >>
    qpat_x_assum`FINITE s1`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE s2` >>
    strip_tac >>
    qmatch_abbrev_tac`FINITE s3` >>
    qsuff_tac`s3 = s1 ∪ s2` >- metis_tac[FINITE_UNION] >>
    unabbrev_all_tac >> simp[EXTENSION] >> metis_tac[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE a` >>
  qmatch_abbrev_tac`FINITE b` >>
  qsuff_tac`b ⊆ a` >- metis_tac[SUBSET_FINITE] >>
  unabbrev_all_tac >> simp[SUBSET_DEF] >>
  metis_tac[]
QED

Theorem FINITE_VFREE_IN_list[simp]:
   ∀ls. FINITE {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u ls}
Proof
  Induct >> simp[] >> rw[] >>
  qmatch_assum_abbrev_tac`FINITE s` >>
  qmatch_abbrev_tac`FINITE t` >>
  `t = s ∪ {x | ∃ty. VFREE_IN (Var x ty) h}` by (
    simp[EXTENSION,Abbr`t`,Abbr`s`] >>
    metis_tac[] ) >>
  pop_assum SUBST1_TAC >>
  simp[FINITE_UNION]
QED

Theorem FINITE_MEM_Var[simp]:
   ∀ls. FINITE {(x,ty) | MEM (Var x ty) ls}
Proof
  Induct >> simp[] >>
  Cases >> simp[] >>
  qmatch_assum_abbrev_tac`FINITE P` >>
  qmatch_abbrev_tac`FINITE Q` >>
  `Q = (m,t) INSERT P` by (
    simp[Abbr`P`,Abbr`Q`,EXTENSION] >>
    metis_tac[] ) >>
  pop_assum SUBST1_TAC >>
  simp[FINITE_INSERT]
QED

val fresh_term_def = new_specification("fresh_term_def",["fresh_term"],
  Q.prove(`∃f. ∀s tm. FINITE s ⇒
                     welltyped tm ⇒
                     welltyped (f s tm) ∧
                     ACONV tm (f s tm) ∧
                     ALL_DISTINCT (bv_names (f s tm)) ∧
                     DISJOINT (set (bv_names (f s tm))) s`,
    simp[GSYM SKOLEM_THM] >> rw[RIGHT_EXISTS_IMP_THM] >>
    qspecl_then[`IMAGE explode (s ∪ set (bv_names tm) ∪ {x | ∃ty. VFREE_IN (Var x ty) tm})`,`LENGTH (bv_names tm)`]
      mp_tac fresh_names_exist >> rw[] >>
    qexists_tac`SND (rename_bvars (MAP implode names) [] tm)` >>
    conj_tac >- metis_tac[rename_bvars_welltyped] >>
    conj_tac >- (
      match_mp_tac rename_bvars_ACONV >>
      fs[IN_DISJOINT,MEM_MAP] >>
      Cases >> simp[] >>
      metis_tac[explode_implode] ) >>
    qspecl_then[`MAP implode names`,`[]`,`tm`]mp_tac bv_names_rename_bvars >>
    simp[TAKE_LENGTH_ID_rwt] >>
    fs[IN_DISJOINT,MEM_MAP] >>
    strip_tac >>
    Cases >> simp[] >>
    metis_tac[explode_implode] ))

(* Alternative characterisation of VARIANT, and thereby of VSUBST and INST_CORE.
   Better for evaluation. *)

Definition vfree_in_def:
  vfree_in v tm =
    case tm of
      Abs bv bod => v <> bv /\ vfree_in v bod
    | Comb s t => vfree_in v s \/ vfree_in v t
    | _ => (tm = v)
End

Theorem vfree_in_thm:
   !name ty y. (VFREE_IN (Var name ty) y = vfree_in (Var name ty) y)
Proof
  ntac 2 gen_tac >> Induct >> simp[VFREE_IN_def,Once vfree_in_def] >>
  simp[Once vfree_in_def,SimpRHS] >>
  BasicProvers.CASE_TAC >>
  simp[Q.SPECL[`Var x1 ty1`,`Var x2 ty2`]vfree_in_def] >>
  simp[Q.SPECL[`Var x1 ty1`,`Const x2 ty2`]vfree_in_def] >>
  simp[Q.SPECL[`Var x1 ty1`,`Comb x2 ty2`]vfree_in_def] >>
  simp[Q.SPECL[`Var x1 ty1`,`Abs x2 ty2`]vfree_in_def] >>
  METIS_TAC[]
QED

Definition variant_def:
  variant avoid v =
    if EXISTS (vfree_in v) avoid then
    case v of
       Var s ty => variant avoid (Var(s ^ «'») ty)
    | _ => v else v
Termination
  WF_REL_TAC `measure (\(avoid,v).
     let n = SUM_SET (BIGUNION (set (MAP (λa. {strlen x + 1 | ∃ty. VFREE_IN (Var x ty) a}) avoid))) in
       n - (case v of Var x ty => strlen x | _ => 0))` >>
   gen_tac >> Cases >> srw_tac[][strlen_def,strcat_thm] >>
   qsuff_tac`STRLEN s' < n` >- simp[] >>
   simp[Abbr`n`] >> fs[GSYM vfree_in_thm,EXISTS_MEM] >>
   match_mp_tac SUM_SET_IN_LT >>
   qexists_tac`STRLEN s' + 1` >> simp[MEM_MAP,PULL_EXISTS] >>
   map_every qexists_tac[`e`,`strlit s'`,`ty`] >> simp[] >> rw[] >>
   qmatch_abbrev_tac`FINITE s` >>
   `s = IMAGE (λ(x,ty). strlen x + 1) {(x,ty) | VFREE_IN (Var x ty) a}` by (
     simp[Abbr`s`,pred_setTheory.EXTENSION,PULL_EXISTS,strlen_def] ) >>
   pop_assum SUBST1_TAC >>
   match_mp_tac pred_setTheory.IMAGE_FINITE >>
   simp[]
End

Theorem variant_vsubst_thm =
  prove(
  ``!xs v x name.
      (xs = [x]) /\ (v = (Var name ty)) ==>
      (variant xs (Var name ty) =
       Var (VARIANT x (explode name) ty) ty)``,
  REWRITE_TAC [VARIANT_def] \\ HO_MATCH_MP_TAC variant_ind
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
  \\ MP_TAC (Q.SPECL[`name`,`ty`, `x`] vfree_in_thm) \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [EXISTS_DEF]
  \\ reverse IF_CASES_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`x`,`explode name`,`ty`])
    \\ Cases_on `VARIANT_PRIMES x (explode name) ty`
    THEN1 (FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode])
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode])
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`x`,`explode name`,`ty`])
  \\ Cases_on `VARIANT_PRIMES x (explode name) ty`
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode]
  \\ REPEAT STRIP_TAC
  \\ sg `!m. m < n ==>
         VFREE_IN (Var (name ^ (implode (REPLICATE (SUC m) #"'"))) ty) x`
  THEN1 (REPEAT STRIP_TAC \\ `SUC m < SUC n` by DECIDE_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [rich_listTheory.REPLICATE_GENLIST]
         \\ FULL_SIMP_TAC std_ss [mlstringTheory.strcat_thm,mlstringTheory.explode_implode])
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE_GENLIST,GENLIST_CONS]
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`x`,`explode (name ^ «'»)`,`ty`])
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,mlstringTheory.strcat_thm,explode_implode,explode_thm]
  \\ Cases_on `VARIANT_PRIMES x (STRCAT (explode name) "'") (ty) = n`
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `VARIANT_PRIMES x (STRCAT (explode name) "'") ty < n \/
      n < VARIANT_PRIMES x (STRCAT (explode name) "'") ty` by DECIDE_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [] |> SPEC_ALL

Theorem VSUBST_thm =
  REWRITE_RULE[SYM variant_vsubst_thm] VSUBST_def

Definition subtract_def:
  subtract l1 l2 = FILTER (\t. ~(MEM t l2)) l1
End

Definition insert_def:
  insert x l = if MEM x l then l else x::l
End

Definition itlist_def:
  itlist f l b =
    case l of
      [] => b
    | (h::t) => f h (itlist f t b)
End

Definition union_def:
  union l1 l2 = itlist insert l1 l2
End

Theorem MEM_union:
   !xs ys x. MEM x (union xs ys) <=> MEM x xs \/ MEM x ys
Proof
  Induct \\ FULL_SIMP_TAC std_ss [union_def]
  \\ ONCE_REWRITE_TAC [itlist_def] \\ SRW_TAC [] [insert_def]
  \\ METIS_TAC []
QED

Theorem EXISTS_union:
   !xs ys. EXISTS P (union xs ys) <=> EXISTS P xs \/ EXISTS P ys
Proof
  SIMP_TAC std_ss [EXISTS_MEM,MEM_MAP,MEM_union] \\ METIS_TAC []
QED

Definition frees_def:
  frees tm =
    case tm of
      Var _ _ => [tm]
    | Const _ _ => []
    | Abs bv bod => subtract (frees bod) [bv]
    | Comb s t => union (frees s) (frees t)
End

Theorem MEM_frees_EQ:
   !a x. MEM x (frees a) = ?n ty. (x = Var n ty) /\ MEM (Var n ty) (frees a)
Proof
  Induct \\ SIMP_TAC (srw_ss()) [Once frees_def,MEM_union]
  THEN1 (SIMP_TAC (srw_ss()) [Once frees_def,MEM_union])
  THEN1 (SIMP_TAC (srw_ss()) [Once frees_def,MEM_union])
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC (srw_ss()) [Once frees_def,MEM_union] THEN1 (METIS_TAC [])
  \\ SIMP_TAC (srw_ss()) [subtract_def,MEM_FILTER]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ METIS_TAC []
QED

Theorem variant_inst_thm =
  prove(
  ``!xs v x name a.
      welltyped a ∧
      (xs = frees a) /\
      (v = (Var name ty1)) ==>
      (variant (frees a) (Var name ty1) =
       Var (VARIANT a (explode name) ty1) ty1)``,
  REWRITE_TAC [VARIANT_def] \\ HO_MATCH_MP_TAC variant_ind
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
  \\ sg `EXISTS (vfree_in (Var name ty1)) (frees a) =
      VFREE_IN (Var name ty1) a` THEN1
   (Q.PAT_X_ASSUM `welltyped a` MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `a` \\ SIMP_TAC (srw_ss()) [Once frees_def,Once vfree_in_def]
    THEN1 (REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [EXISTS_union,VFREE_IN_def])
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ BasicProvers.VAR_EQ_TAC
    \\ FULL_SIMP_TAC std_ss [VFREE_IN_def,WELLTYPED_CLAUSES]
    \\ FIRST_X_ASSUM (fn th => FULL_SIMP_TAC std_ss [SYM th])
    \\ FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,subtract_def,MEM_FILTER,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC [MEM_frees_EQ]
    \\ FULL_SIMP_TAC std_ss [term_11,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC [vfree_in_def] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss []
  \\ reverse (Cases_on `VFREE_IN (Var name ty1) a`) THEN1
   (MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`a`,`explode name`,`ty1`])
    \\ Cases_on `VARIANT_PRIMES a (explode name) ty1`
    THEN1 FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode])
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`a`,`explode name`,`ty1`])
  \\ Cases_on `VARIANT_PRIMES a (explode name) ty1`
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.GEN `m` o SIMP_RULE std_ss [] o Q.SPEC `SUC m`)
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`a`,`STRCAT (explode name) "'"`,`ty1`])
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,mlstringTheory.strcat_thm,mlstringTheory.explode_implode,explode_thm]
  \\ Q.ABBREV_TAC `k = VARIANT_PRIMES a (STRCAT (explode name) "'") ty1`
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE_GENLIST,GENLIST_CONS]
  \\ Cases_on `k = n` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `k < n \/ n < k` by DECIDE_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [] |> SPEC_ALL

Theorem INST_CORE_Abs_thm:
   ∀v t env tyin. welltyped (Abs v t) ⇒
   INST_CORE env tyin (Abs v t) =
   (let (x,ty) = dest_var v in
    let ty' = TYPE_SUBST tyin ty in
    let v' = Var x ty' in
    let env' = (v,v')::env in
    let tres = INST_CORE env' tyin t
    in
      if IS_RESULT tres then Result (Abs v' (RESULT tres))
      else
        (let w = CLASH tres
         in
           if w ≠ v' then tres
           else
             (let (x',_) =
               dest_var (variant (frees (RESULT (INST_CORE [] tyin t))) (Var x ty'))
              in
              let t' = VSUBST [(Var x' ty,Var x ty)] t in
              let env'' = (Var x' ty,Var x' ty')::env in
              let tres' = INST_CORE env'' tyin t'
              in
                if IS_RESULT tres' then
                  Result (Abs (Var x' ty') (RESULT tres'))
                else tres')))
Proof
  rw[] >> simp[Once INST_CORE_def] >> rw[] >>
  unabbrev_all_tac >> fs[] >>
  rfs[GSYM INST_def] >>
  imp_res_tac INST_WELLTYPED >>
  fs[variant_inst_thm] >> rw[] >> fs[]
QED

(* provable terms are ok and of type bool *)

Theorem proves_theory_ok:
   ∀thyh c. thyh |- c ⇒ theory_ok (FST thyh)
Proof
  ho_match_mp_tac proves_ind >> rw[]
QED

Theorem theory_ok_sig:
   ∀thy. theory_ok thy ⇒ is_std_sig (sigof thy)
Proof
  Cases >> rw[theory_ok_def]
QED

Theorem proves_term_ok:
   ∀thyh c. thyh |- c ⇒
      hypset_ok (SND thyh) ∧
      EVERY (λp. term_ok (sigof (FST thyh)) p ∧ p has_type Bool) (c::(SND thyh))
Proof
  ho_match_mp_tac proves_strongind >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation,term_ok_def]) >>
  strip_tac >- rw[EQUATION_HAS_TYPE_BOOL] >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac term_ok_welltyped >>
    imp_res_tac theory_ok_sig >>
    rw[term_ok_equation,term_ok_def]) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation] >>
    imp_res_tac WELLTYPED_LEMMA >> fs[] >>
    simp[WELLTYPED] >>
    match_mp_tac EVERY_term_union >>
    rpt conj_tac >>
    match_mp_tac EVERY_term_remove >>
    fs[EVERY_MEM]) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation] >>
    imp_res_tac ACONV_TYPE >> fs[] >-
      metis_tac[WELLTYPED_LEMMA,WELLTYPED,term_ok_welltyped] >>
    match_mp_tac EVERY_term_union >> fs[] ) >>
  strip_tac >- (
    rw[term_ok_VSUBST,hypset_ok_term_image,EVERY_MEM] >>
    imp_res_tac MEM_term_image_imp >> fs[EVERY_MEM] >>
    metis_tac[term_ok_VSUBST,VSUBST_HAS_TYPE] ) >>
  strip_tac >- (
    rw[term_ok_INST,hypset_ok_term_image] >> fs[EVERY_MEM] >>
    rw[] >> imp_res_tac MEM_term_image_imp >>
    metis_tac[SIMP_RULE(srw_ss())[EVERY_MEM]term_ok_INST,INST_HAS_TYPE,TYPE_SUBST_Bool] ) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation,term_ok_def] >>
    metis_tac[EVERY_term_union]) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac term_ok_welltyped >>
    imp_res_tac theory_ok_sig >>
    rw[term_ok_equation,term_ok_def]) >>
  rw[theory_ok_def]
QED

(* some derived rules *)

val assume = proves_rules |> CONJUNCTS |> el 2
Theorem deductAntisym_equation =
  proves_rules |> CONJUNCTS |> el 4
Theorem eqMp_equation =
  proves_rules |> CONJUNCTS |> el 5
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
Theorem refl_equation =
  proves_rules |> CONJUNCTS |> el 9
Theorem appThm_equation =
  proves_rules |> CONJUNCTS |> el 8
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]

Theorem addAssum:
   ∀thy h c a. (thy,h) |- c ∧ term_ok (sigof thy) a ∧ (a has_type Bool) ⇒
      (thy,term_union [a] h) |- c
Proof
  rw[] >>
  ho_match_mp_tac (MP_CANON eqMp_equation) >>
  map_every qexists_tac[`c`,`c`] >> simp[] >>
  qspecl_then[`a`,`thy`]mp_tac assume >>
  imp_res_tac proves_theory_ok >> fs[] >> strip_tac >>
  Cases_on`ACONV (c === c) a` >- (
    qspecl_then[`c === c`,`thy`]mp_tac refl_equation >>
    imp_res_tac theory_ok_sig >>
    imp_res_tac proves_term_ok >>
    fs[term_ok_equation] >> strip_tac >>
    imp_res_tac eqMp_equation >>
    fs[term_union_thm] ) >>
  qspecl_then[`c`,`thy`]mp_tac refl_equation >>
  imp_res_tac proves_term_ok >> fs[] >> strip_tac >>
  qspecl_then[`a`,`c === c`,`[a]`,`[]`,`thy`]mp_tac deductAntisym_equation >>
  simp[term_union_thm] >>
  `term_remove (c === c) [a] = [a]` by (
    simp[Once term_remove_def,GSYM ACONV_eq_orda] ) >>
  rw[] >>
  imp_res_tac eqMp_equation >>
  metis_tac[ACONV_REFL,term_union_idem]
QED

(* inference system respects alpha-equivalence *)

val rws = [
  rich_listTheory.EL_APPEND1,
  rich_listTheory.EL_APPEND2,
  rich_listTheory.EL_LENGTH_APPEND_rwt,
  rich_listTheory.EL_TAKE,
  rich_listTheory.EL_DROP,
  rich_listTheory.EL_CONS]

Theorem proves_concl_ACONV[local]:
  ∀thyh c c'. thyh |- c ∧ ACONV c c' ∧ welltyped c' ⇒ thyh |- c'
Proof
  rw[] >>
  qspecl_then[`c'`,`FST thyh`]mp_tac refl_equation >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_aconv >> pop_assum kall_tac >> simp[] >>
  Cases_on`thyh`>>fs[]>>
  metis_tac[eqMp_equation,term_union_thm,ACONV_SYM]
QED

Theorem proves_ACONV_lemma[local]:
  ∀thy c h' h1 h.
    (thy,h1++h) |- c ∧
    hypset_ok (h1++h') ∧
    EVERY (λx. EXISTS (ACONV x) h') h ∧
    EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) h'
    ⇒ (thy,h1++h') |- c
Proof
  ntac 2 gen_tac >> Induct >> rw[] >> rw[] >>
  imp_res_tac proves_term_ok >> fs[hypset_ok_cons] >>
  Cases_on`EXISTS (ACONV h) h''` >- (
    `∃h0 hr. (h'' = h0::hr) ∧ ACONV h h0` by (
      Cases_on`h''`>>fs[]>-metis_tac[ACONV_SYM]>>
      fs[EXISTS_MEM] >>
      `alpha_lt h''' e'` by (
        fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM] ) >>
      `alpha_lt h e` by (
        fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM] ) >>
      `alpha_lt e e'` by metis_tac[alpha_lt_trans_ACONV,ACONV_SYM] >>
      `alpha_lt h e'` by metis_tac[transitive_alpha_lt,relationTheory.transitive_def] >>
      fs[alpha_lt_def,ACONV_eq_orda] ) >>
    rw[] >>
    qspecl_then[`thy`,`h1++h0::hr`,`c`,`h`]mp_tac addAssum >>
    imp_res_tac WELLTYPED_LEMMA >> simp[] >>
    qspecl_then[`h1`,`h`,`h0`,`hr`]mp_tac term_union_replace >>
    impl_tac >- (
      simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
      rpt(qpat_x_assum`EVERY P (X::Y)`kall_tac) >>
      rw[] >>
      fs[hypset_ok_el_less] >- (
        first_x_assum(qspecl_then[`n`,`LENGTH h1`]mp_tac) >>
        simp rws >>
        metis_tac[alpha_lt_trans_ACONV,ACONV_SYM]) >>
      first_x_assum(qspecl_then[`LENGTH h1`,`LENGTH h1 + SUC n`]mp_tac) >>
      simp rws >>
      metis_tac[alpha_lt_trans_ACONV,ACONV_SYM]) >>
    disch_then SUBST1_TAC >> strip_tac >>
    first_x_assum(qspecl_then[`h1++[h]`,`hr`]mp_tac) >>
    impl_tac >- (
      conj_tac >- metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] >>
      conj_tac >- (
        imp_res_tac proves_term_ok >> fs[] >>
        metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
      qpat_x_assum`EVERY P1 X`kall_tac >>
      qmatch_assum_abbrev_tac`EVERY P (h0::hr)` >>
      qpat_x_assum`EXISTS X (h0::hr)`kall_tac >>
      fs[EVERY_MEM] >> rw[] >>
      `P x` by res_tac >> pop_assum mp_tac >>
      qpat_x_assum`P h0`kall_tac >>
      simp_tac std_ss [Abbr`P`] >>
      strip_tac >>
      fs[hypset_ok_el_less,MEM_EL,PULL_EXISTS] >>
      first_x_assum(qspecl_then[`LENGTH h1`,`LENGTH h1 + SUC n`]mp_tac) >>
      simp rws >> strip_tac >>
      `ACONV h0 x` by metis_tac[ACONV_TRANS,ACONV_SYM] >>
      rfs[ACONV_eq_orda,alpha_lt_def] ) >>
    metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
  qspecl_then[`thy`,`h1++h''`,`c`,`h`]mp_tac addAssum >>
  imp_res_tac WELLTYPED_LEMMA >> simp[] >>
  qspecl_then[`h1`,`h`,`h''`]mp_tac term_union_insert >>
  impl_tac >- (
    fs[EVERY_MEM,EXISTS_MEM] >>
    conj_tac >- (
      rw[] >>
      qpat_x_assum`hypset_ok (h1 ++ h::h')`mp_tac >>
      simp[hypset_ok_el_less,MEM_EL,PULL_EXISTS] >>
      fs[MEM_EL,PULL_EXISTS] >>
      disch_then(qspecl_then[`n`,`LENGTH h1`]mp_tac) >>
      simp rws ) >>
    rw[] >>
    last_x_assum(qspec_then`z`mp_tac) >> simp[] >>
    strip_tac >- metis_tac[ACONV_SYM] >>
    fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM] >> rw[] >> fs[] >>
    metis_tac[ACONV_SYM,alpha_lt_trans_ACONV] ) >>
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

Theorem proves_ACONV:
   ∀thy h' c' h c.
      (thy,h) |- c ∧ welltyped c' ∧ ACONV c c' ∧
      hypset_ok h' ∧
      EVERY (λx. EXISTS (ACONV x) h') h ∧
      EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) h'
      ⇒ (thy,h') |- c'
Proof
  rw[] >>
  qsuff_tac`(thy,h') |- c` >- metis_tac[proves_concl_ACONV] >>
  qpat_x_assum`welltyped c'`kall_tac >>
  qpat_x_assum`ACONV c c'`kall_tac >>
  metis_tac[proves_ACONV_lemma,APPEND]
QED

(* more derived rules *)

Theorem sym_equation:
   ∀thyh p q. thyh |- p === q ⇒ thyh |- q === p
Proof
  rpt strip_tac >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac proves_term_ok >>
  imp_res_tac theory_ok_sig >>
  `(FST thyh,[]) |- p === p` by (
    match_mp_tac refl_equation >> simp[] >>
    fs[term_ok_equation]) >>
  `(FST thyh,[]) |- Equal (typeof p) === Equal (typeof p)` by (
    match_mp_tac refl_equation >> simp[term_ok_clauses] >>
    fs[term_ok_equation] >>
    metis_tac[term_ok_type_ok] ) >>
  qspecl_then[`[]`,`SND thyh`,`Equal (typeof p)`,`p`]mp_tac appThm_equation >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[] >> impl_keep_tac
    >- fs[term_ok_equation,EQUATION_HAS_TYPE_BOOL] >>
  simp[term_union_thm] >>
  strip_tac >> mp_tac appThm_equation >>
  Cases_on`thyh`>>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  full_simp_tac std_ss [] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  fs[term_ok_equation] >>
  simp[GSYM equation_def,term_union_thm] >>
  qpat_x_assum`typeof _ = typeof _`(assume_tac o SYM) >>
  simp[GSYM equation_def] >>
  fs[EQUATION_HAS_TYPE_BOOL] >>
  metis_tac[eqMp_equation,term_union_thm,ACONV_REFL]
QED

Theorem sym:
   ∀thyh p q ty.
      thyh |- Comb (Comb (Equal ty) p) q ⇒
      thyh |- Comb (Comb (Equal ty) q) p
Proof
  rw[] >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_welltyped >> fs[] >>
  metis_tac[equation_def,sym_equation]
QED

Theorem trans_equation:
   ∀thy h1 h2 t1 t2a t2b t3.
      (thy,h2) |- t2b === t3 ⇒
      (thy,h1) |- t1 === t2a ⇒
      ACONV t2a t2b ⇒
      (thy,term_union h1 h2) |- t1 === t3
Proof
  rw[] >>
  imp_res_tac proves_theory_ok >> fs[] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac proves_term_ok >>
  rfs[term_ok_equation] >>
  qspecl_then[`Comb (Equal (typeof t3)) t3`,`thy`]mp_tac refl_equation >>
  simp[term_ok_clauses] >>
  impl_tac >- metis_tac[term_ok_type_ok,term_ok_welltyped] >>
  disch_then(mp_tac o MATCH_MP appThm_equation) >>
  disch_then(qspecl_then[`h1`,`t2a`,`t1`]mp_tac) >>
  impl_tac >- metis_tac[sym_equation] >>
  fs[EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac ACONV_TYPE >> rfs[] >>
  qpat_x_assum`typeof t3 = X`(assume_tac o SYM) >>
  simp[GSYM equation_def] >>
  disch_then(mp_tac o MATCH_MP eqMp_equation) >>
  disch_then(qspecl_then[`h2`,`t3 === t2b`]mp_tac) >>
  simp[term_union_thm] >>
  impl_tac >- metis_tac[sym_equation] >>
  impl_tac >- (
    simp[ACONV_def,RACONV,equation_def] >>
    simp[GSYM ACONV_def] ) >>
  metis_tac[sym_equation]
QED

Theorem trans:
   ∀thy h1 h2 t1 t2a t2b t3 ty.
      (thy,h2) |- Comb (Comb (Equal ty) t2b) t3 ⇒
      (thy,h1) |- Comb (Comb (Equal ty) t1) t2a ⇒
      ACONV t2a t2b ⇒
      (thy,term_union h1 h2) |- Comb (Comb (Equal ty) t1) t3
Proof
  rw[] >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_welltyped >> fs[] >>
  metis_tac[trans_equation,equation_def]
QED

Theorem proveHyp:
   ∀thy h1 c1 h2 c2. (thy,h1) |- c1 ∧ (thy,h2) |- c2 ⇒
      (thy,term_union h2 (term_remove c2 h1)) |- c1
Proof
  rw[] >>
  imp_res_tac proves_term_ok >>
  imp_res_tac proves_theory_ok >> fs[] >>
  qspecl_then[`c2`,`c1`,`h2`,`h1`,`thy`]mp_tac deductAntisym_equation >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`(thy,h3) |- c2 === c1` >>
  qspecl_then[`h3`,`h2`,`c2`,`c2`,`c1`,`thy`]mp_tac eqMp_equation >>
  simp[] >>
  strip_tac >>
  match_mp_tac proves_ACONV >>
  first_assum(match_exists_tac o concl) >>
  simp[] >>
  conj_tac >- metis_tac[welltyped_def] >>
  unabbrev_all_tac >>
  simp[EVERY_MEM,EXISTS_MEM] >>
  conj_tac >> gen_tac >>
  disch_then(mp_tac o MATCH_MP MEM_term_union_imp) >>
  strip_tac >>
  TRY(pop_assum(mp_tac o MATCH_MP MEM_term_union_imp)) >>
  TRY strip_tac >>
  imp_res_tac MEM_term_remove_imp >>
  TRY(fs[EVERY_MEM]>>NO_TAC) >>
  metis_tac[MEM_term_union,hypset_ok_term_union,hypset_ok_term_remove,ACONV_REFL]
QED

(* extension is transitive *)

Theorem extends_trans:
   ∀c1 c2 c3. c1 extends c2 ∧ c2 extends c3 ⇒ c1 extends c3
Proof
  rw[extends_def] >> metis_tac[RTC_TRANSITIVE,transitive_def]
QED

(* extensions have all distinct names *)

Theorem updates_ALL_DISTINCT:
   ∀upd ctxt. upd updates ctxt ⇒
      (ALL_DISTINCT (MAP FST (type_list ctxt)) ⇒
       ALL_DISTINCT (MAP FST (type_list (upd::ctxt)))) ∧
      (ALL_DISTINCT (MAP FST (const_list ctxt)) ⇒
       ALL_DISTINCT (MAP FST (const_list (upd::ctxt))))
Proof
  ho_match_mp_tac updates_ind >> simp[] >>
  rw[ALL_DISTINCT_APPEND,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX]
QED

Theorem extends_ALL_DISTINCT:
   ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒
      (ALL_DISTINCT (MAP FST (type_list ctxt1)) ⇒
       ALL_DISTINCT (MAP FST (type_list ctxt2))) ∧
      (ALL_DISTINCT (MAP FST (const_list ctxt1)) ⇒
       ALL_DISTINCT (MAP FST (const_list ctxt2)))
Proof
  simp[IMP_CONJ_THM,FORALL_AND_THM] >> conj_tac >>
  ho_match_mp_tac extends_ind >>
  METIS_TAC[updates_ALL_DISTINCT]
QED

Theorem init_ALL_DISTINCT:
   ALL_DISTINCT (MAP FST (const_list init_ctxt)) ∧
    ALL_DISTINCT (MAP FST (type_list init_ctxt))
Proof
  EVAL_TAC
QED

Theorem updates_DISJOINT:
   ∀upd ctxt.
    upd updates ctxt ⇒
    DISJOINT (FDOM (alist_to_fmap (consts_of_upd upd))) (FDOM (tmsof ctxt)) ∧
    DISJOINT (FDOM (alist_to_fmap (types_of_upd upd))) (FDOM (tysof ctxt))
Proof
  ho_match_mp_tac updates_ind >>
  simp[IN_DISJOINT] >> rw[] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  PROVE_TAC[]
QED

Theorem updates_upd_ALL_DISTINCT:
   ∀upd ctxt. upd updates ctxt ⇒
      ALL_DISTINCT (MAP FST (consts_of_upd upd)) ∧
      ALL_DISTINCT (MAP FST (types_of_upd upd))
Proof
  ho_match_mp_tac updates_ind >> rw[] >>
  rw[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX]
QED

Theorem updates_upd_DISJOINT:
   ∀upd ctxt. upd updates ctxt ⇒
      DISJOINT (set (MAP FST (types_of_upd upd))) (set (MAP FST (type_list ctxt))) ∧
      DISJOINT (set (MAP FST (consts_of_upd upd))) (set (MAP FST (const_list ctxt)))
Proof
  ho_match_mp_tac updates_ind >> rw[IN_DISJOINT,MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS,LET_THM] >>
  metis_tac[]
QED

(* signature extensions preserve ok *)

Theorem type_ok_extend:
   ∀t tyenv tyenv'.
    tyenv ⊑ tyenv' ∧
    type_ok tyenv t ⇒
    type_ok tyenv' t
Proof
  ho_match_mp_tac type_ind >>
  rw[type_ok_def,EVERY_MEM] >>
  res_tac >>
  imp_res_tac FLOOKUP_SUBMAP
QED

Theorem term_ok_extend:
   ∀t tyenv tmenv tyenv' tmenv'.
    tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧
    term_ok (tyenv,tmenv) t ⇒
    term_ok (tyenv',tmenv') t
Proof
  Induct >> simp[term_ok_def] >> rw[] >>
  imp_res_tac type_ok_extend >>
  imp_res_tac FLOOKUP_SUBMAP >>
  metis_tac[]
QED

Theorem term_ok_updates:
   ∀upd ctxt. upd updates ctxt ⇒
      term_ok (sigof (thyof ctxt)) tm ⇒
      term_ok (sigof (thyof (upd::ctxt))) tm
Proof
  rw[] >> match_mp_tac term_ok_extend >>
  map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
  simp[] >> conj_tac >> match_mp_tac finite_mapTheory.SUBMAP_FUNION >>
  metis_tac[updates_DISJOINT,finite_mapTheory.SUBMAP_REFL,pred_setTheory.DISJOINT_SYM]
QED

Theorem is_std_sig_extend:
   ∀tyenv tmenv tyenv' tmenv'.
    is_std_sig (tyenv,tmenv) ∧ tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ⇒
    is_std_sig (tyenv',tmenv')
Proof
  rw[is_std_sig_def] >> imp_res_tac FLOOKUP_SUBMAP
QED

(* updates preserve ok *)

Theorem updates_theory_ok:
   ∀upd ctxt. upd updates ctxt ⇒ theory_ok (thyof ctxt) ⇒ theory_ok (thyof (upd::ctxt))
Proof
  ho_match_mp_tac updates_ind >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    fs[theory_ok_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    fs[theory_ok_def] >>
    conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
    `tmsof ctxt ⊑ tmsof ctxt |+ (name,ty)` by simp[] >>
    metis_tac[is_std_sig_extend,term_ok_extend,SUBMAP_REFL] ) >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    imp_res_tac proves_term_ok >>
    fs[theory_ok_def,EVERY_MAP] >>
    rfs[term_ok_equation,UNCURRY,EQUATION_HAS_TYPE_BOOL] >>
    Q.PAT_ABBREV_TAC`tms' = X ⊌ tmsof ctxt` >>
    `tmsof ctxt ⊑ tms'` by (
      simp[Abbr`tms'`] >>
      match_mp_tac SUBMAP_FUNION >>
      fs[IN_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
      metis_tac[] ) >>
    conj_tac >- (
      simp[Abbr`tms'`] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY_MEM,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,MEM_MAP,PULL_EXISTS] >>
      fs[term_ok_def] ) >>
    reverse conj_tac >- metis_tac[is_std_sig_extend,SUBMAP_REFL] >>
    gen_tac >> reverse strip_tac >- metis_tac[term_ok_extend,SUBMAP_REFL] >>
    simp[] >>
    conj_tac >- (
      match_mp_tac term_ok_VSUBST >>
      simp[MEM_MAP,PULL_EXISTS,UNCURRY,Once has_type_cases,term_ok_def] >>
      conj_tac >- metis_tac[term_ok_extend,SUBMAP_REFL] >>
      simp[Abbr`tms'`,FLOOKUP_FUNION,ALOOKUP_MAP,FORALL_PROD] >> rw[] >>
      imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> rw[] >>
      fs[EVERY_MEM,term_ok_def,FORALL_PROD] >>
      metis_tac[is_instance_refl] ) >>
    match_mp_tac VSUBST_HAS_TYPE >>
    simp[MEM_MAP,PULL_EXISTS,UNCURRY,Once has_type_cases] ) >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    fs[theory_ok_def] >>
    `tysof ctxt ⊑ tysof ctxt |+ (name,arity)` by simp[] >>
    metis_tac[is_std_sig_extend,term_ok_extend,type_ok_extend,SUBMAP_REFL] ) >>
  srw_tac[][conexts_of_upd_def] >>
  fs[theory_ok_def] >>
  Q.PAT_ABBREV_TAC`tms' = X ⊌ tmsof ctxt` >>
  Q.PAT_ABBREV_TAC`tys' = tysof ctxt |+ X` >>
  `tmsof ctxt ⊑ tms'` by (
    simp[Abbr`tms'`] >>
    match_mp_tac SUBMAP_FUNION >>
    fs[IN_DISJOINT] >>
    metis_tac[] ) >>
  `tysof ctxt ⊑ tys'` by (
    simp[Abbr`tys'`] ) >>
  `is_std_sig (tys',tms')` by metis_tac[is_std_sig_extend] >>
  imp_res_tac proves_term_ok >> fs[term_ok_def] >>
  imp_res_tac term_ok_type_ok >>
  conj_tac >- (
    simp[Abbr`tms'`] >>
    ho_match_mp_tac IN_FRANGE_FUNION_suff >>
    reverse conj_tac >- metis_tac[type_ok_extend] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_suff >>
    simp[type_ok_def] >>
    fs[is_std_sig_def] >>
    imp_res_tac WELLTYPED_LEMMA >>
    unabbrev_all_tac >>
    simp[type_ok_def,FLOOKUP_UPDATE,EVERY_MAP] >>
    metis_tac[type_ok_extend,term_ok_type_ok] ) >>
  simp[] >>
  imp_res_tac WELLTYPED_LEMMA >>
  `name ∉ {«fun»;«bool»}` by (
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  pop_assum mp_tac >> simp[] >> strip_tac >>
  Q.PAT_ABBREV_TAC`eq1 = l1 === r1` >>
  Q.PAT_ABBREV_TAC`eq2 = l2 === r` >>
  Q.PAT_ABBREV_TAC`eq3 = l3 === r3` >>
  qpat_x_assum`X has_type Y`mp_tac >>
  simp[Once has_type_cases] >> strip_tac >> rfs[] >>
  `type_ok tys' rep_type` by (
    match_mp_tac type_ok_extend >>
    HINT_EXISTS_TAC >> fs[Abbr`rep_type`] ) >>
  `term_ok (tys',tms') eq1` by (
    unabbrev_all_tac >>
    simp[term_ok_equation,term_ok_def,type_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE,EVERY_MAP] >>
    rfs[is_std_sig_def] ) >>
  `term_ok (tys',tms') pred` by metis_tac[term_ok_extend] >>
  `eq1 has_type Bool` by (
    unabbrev_all_tac >> simp[EQUATION_HAS_TYPE_BOOL] ) >>
  `eq2 has_type Bool` by (
    unabbrev_all_tac >> simp[EQUATION_HAS_TYPE_BOOL] ) >>
  imp_res_tac WELLTYPED_LEMMA >>
  `eq3 has_type Bool` by (
    unabbrev_all_tac >> simp[EQUATION_HAS_TYPE_BOOL,welltyped_equation] ) >>
  `term_ok (tys',tms') eq3` by (
    unabbrev_all_tac >>
    simp[term_ok_equation,term_ok_def,type_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE,EVERY_MAP] >>
    fs[is_std_sig_def] ) >>
  metis_tac[term_ok_extend]
QED

Theorem extends_theory_ok:
   ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ theory_ok (thyof ctxt1) ⇒ theory_ok (thyof ctxt2)
Proof
  ho_match_mp_tac extends_ind >> metis_tac[updates_theory_ok]
QED

(* init_ctxt ok *)

Theorem init_theory_ok:
   theory_ok (thyof init_ctxt)
Proof
  rw[theory_ok_def,init_ctxt_def,type_ok_def,FLOOKUP_UPDATE,conexts_of_upd_def] >>
  rw[is_std_sig_def,FLOOKUP_UPDATE]
QED

(* is_std_sig is preserved *)

Theorem is_std_sig_extends:
   ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ is_std_sig (sigof ctxt1) ⇒ is_std_sig (sigof ctxt2)
Proof
  ho_match_mp_tac extends_ind >>
  REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac updates_ind >>
  srw_tac[][is_std_sig_def,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
  TRY BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[]
QED

(* recover constant definition as a special case of specification *)

Overload ConstDef = ``λx t. ConstSpec [(x,t)] (Var x (typeof t) === t)``

Theorem ConstDef_updates:
   ∀name tm ctxt.
    theory_ok (thyof ctxt) ∧
    term_ok (sigof ctxt) tm ∧
    name ∉ FDOM (tmsof ctxt) ∧
    CLOSED tm ∧
    set (tvars tm) ⊆ set (tyvars (typeof tm))
    ⇒ ConstDef name tm updates ctxt
Proof
  rw[] >>
  match_mp_tac(List.nth(CONJUNCTS updates_rules,2)) >>
  simp[EVERY_MAP] >> fs[SUBSET_DEF] >>
  simp[vfree_in_equation] >> fs[CLOSED_def] >>
  match_mp_tac(List.nth(CONJUNCTS proves_rules,1)) >>
  imp_res_tac term_ok_welltyped >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_type_ok >>
  simp[EQUATION_HAS_TYPE_BOOL,term_ok_equation,term_ok_def]
QED

(* lookups in extended contexts *)

Theorem FLOOKUP_tmsof_updates:
   ∀upd ctxt. upd updates ctxt ⇒
    FLOOKUP (tmsof (thyof ctxt)) name = SOME ty ⇒
    FLOOKUP (tmsof (thyof (upd::ctxt))) name = SOME ty
Proof
  rw[finite_mapTheory.FLOOKUP_FUNION] >>
  BasicProvers.CASE_TAC >> imp_res_tac updates_DISJOINT >>
  fs[pred_setTheory.IN_DISJOINT,listTheory.MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[alistTheory.ALOOKUP_MEM]
QED

Theorem FLOOKUP_tysof_updates:
   ∀upd ctxt. upd updates ctxt ⇒
    FLOOKUP (tysof (thyof ctxt)) name = SOME a ⇒
    FLOOKUP (tysof (thyof (upd::ctxt))) name = SOME a
Proof
  rw[finite_mapTheory.FLOOKUP_FUNION] >>
  BasicProvers.CASE_TAC >> imp_res_tac updates_DISJOINT >>
  fs[pred_setTheory.IN_DISJOINT,listTheory.MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[alistTheory.ALOOKUP_MEM]
QED

Theorem FLOOKUP_tysof_extends:
   ∀ctxt2 ctxt1. ctxt1 extends ctxt2 ⇒
   (FLOOKUP (tysof (sigof ctxt2)) k = SOME v) ⇒
   (FLOOKUP (tysof (sigof ctxt1)) k = SOME v)
Proof
  ho_match_mp_tac extends_ind
  \\ REWRITE_TAC[GSYM o_DEF]
  \\ rw[ALOOKUP_APPEND]
  \\ CASE_TAC
  \\ fs[updates_cases]
  \\ rw[] \\ fs[]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[MEM_MAP,EXISTS_PROD]
  \\ metis_tac[]
QED

Theorem FLOOKUP_tmsof_extends:
   ∀ctxt2 ctxt1. ctxt1 extends ctxt2 ⇒
   (FLOOKUP (tmsof (sigof ctxt2)) k = SOME v) ⇒
   (FLOOKUP (tmsof (sigof ctxt1)) k = SOME v)
Proof
  ho_match_mp_tac extends_ind
  \\ REWRITE_TAC[GSYM o_DEF]
  \\ rw[ALOOKUP_APPEND]
  \\ CASE_TAC
  \\ fs[updates_cases]
  \\ rw[] \\ fs[]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[MEM_MAP,EXISTS_PROD]
  \\ TRY(qpat_x_assum`_ = SOME _`mp_tac \\ rw[])
  \\ metis_tac[]
QED

Theorem extends_sub:
   ∀ctxt2 ctxt1. ctxt2 extends ctxt1 ⇒
      tmsof ctxt1 ⊑ tmsof ctxt2 ∧
      tysof ctxt1 ⊑ tysof ctxt2 ∧
      axsof ctxt1 ⊆ axsof ctxt2
Proof
  simp[extends_def] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >>
  simp[PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  rpt conj_tac >>
  TRY (
    match_mp_tac finite_mapTheory.SUBMAP_FUNION >>
    disj2_tac >> simp[] >>
    imp_res_tac updates_DISJOINT >> fs[] >>
    fs[finite_mapTheory.SUBMAP_DEF,pred_setTheory.IN_DISJOINT] >>
    metis_tac[] ) >>
  metis_tac[pred_setTheory.SUBSET_UNION,pred_setTheory.SUBSET_TRANS]
QED

(* proofs still work in extended contexts *)

Theorem update_extension[local]:
  !lhs tm.
      lhs |- tm
      ⇒
      !ctxt tms upd.
        lhs = (thyof ctxt,tms) ∧
        upd updates ctxt
        ⇒
        (thyof (upd::ctxt),tms) |- tm
Proof
  ho_match_mp_tac proves_ind >>
  rw []
  >- (rw [Once proves_cases] >>
      disj1_tac >>
      MAP_EVERY qexists_tac [`l`, `r`, `ty`, `x`] >>
      rw [] >>
      match_mp_tac type_ok_extend >>
      qexists_tac `tysof (sigof (thyof ctxt))` >>
      rw [] >>
      match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
      fs [Once updates_cases])
  >- (rw [Once proves_cases] >>
      disj2_tac >>
      disj1_tac >>
      rw []
      >- (imp_res_tac updates_theory_ok >>
          fs [])
      >- (match_mp_tac term_ok_extend >>
          MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
          rw []
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              fs [Once updates_cases])
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              metis_tac [updates_DISJOINT])
          >- (Cases_on `ctxt` >>
              fs [])))
  >- (rw [Once proves_cases] >>
      disj2_tac >>
      disj1_tac >>
      rw [] >>
      MAP_EVERY qexists_tac [`t`, `ty`, `x`] >>
      rw []
      >- (imp_res_tac updates_theory_ok >>
          fs [])
      >- (match_mp_tac type_ok_extend >>
          qexists_tac `tysof ctxt` >>
          rw []
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              fs [Once updates_cases])
          >- (Cases_on `ctxt` >>
              fs []))
      >- (match_mp_tac term_ok_extend >>
          MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
          rw []
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              fs [Once updates_cases])
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              metis_tac [updates_DISJOINT])
          >- (Cases_on `ctxt` >>
              fs [])))
  >- (rw [Once proves_cases] >>
      ntac 3 disj2_tac >>
      disj1_tac >>
      rw [] >>
      metis_tac [])
  >- (rw [Once proves_cases] >>
      ntac 4 disj2_tac >>
      disj1_tac >>
      rw [] >>
      metis_tac [])
  >- (rw [Once proves_cases] >>
      ntac 5 disj2_tac >>
      disj1_tac >>
      rw [] >>
      MAP_EVERY qexists_tac [`tm`, `h`, `ilist`] >>
      rw [] >>
      res_tac  >>
      fs [] >>
      rw [] >>
      match_mp_tac term_ok_extend >>
      MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
      rw []
      >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
          fs [Once updates_cases])
      >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
          metis_tac [updates_DISJOINT]))
  >- (rw [Once proves_cases] >>
      ntac 6 disj2_tac >>
      disj1_tac >>
      rw [] >>
      MAP_EVERY qexists_tac [`tm`, `h`, `tyin`] >>
      rw [] >>
      fs [EVERY_MAP, EVERY_MEM] >>
      rw [] >>
      match_mp_tac type_ok_extend >>
      qexists_tac `tysof ctxt` >>
      rw [] >>
      match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
      fs [Once updates_cases])
  >- (rw [Once proves_cases] >>
      ntac 7 disj2_tac >>
      disj1_tac >>
      rw [] >>
      metis_tac [])
  >- (rw [Once proves_cases] >>
      ntac 7 disj2_tac >>
      disj1_tac >>
      rw [] >>
      qexists_tac `t` >>
      rw []
      >- (imp_res_tac updates_theory_ok >>
          fs [])
      >- (match_mp_tac term_ok_extend >>
          MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
          rw []
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              fs [Once updates_cases])
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              metis_tac [updates_DISJOINT])
          >- (Cases_on `ctxt` >>
              fs [])))
  >- (rw [Once proves_cases] >>
      ntac 8 disj2_tac >>
      rw []
      >- (imp_res_tac updates_theory_ok >>
          fs [])
      >- (Cases_on `ctxt` >>
          fs []))
QED

Theorem updates_proves:
   ∀upd ctxt.  upd updates ctxt ⇒
    ∀h c.
    (thyof ctxt,h) |- c ⇒
    (thyof (upd::ctxt),h) |- c
Proof
  metis_tac[update_extension]
QED

Theorem extends_proves:
   !c2 c1.
     c2 extends c1
     ==>
     !h c.
       (thyof c1,h) |- c ==> (thyof c2,h) |- c
Proof
  Induct \\ rw [extends_def]
  \\ fs [Once RTC_CASES1] \\ rw [] \\ fs [BETA_THM]
  \\ fs [GSYM extends_def]
  \\ first_x_assum drule
  \\ disch_then drule \\ rw []
  \\ drule updates_proves
  \\ disch_then drule \\ rw []
QED

(* types occurring in a term *)

Definition types_in_def[simp]:
  types_in (Var x ty) = {ty} ∧
  types_in (Const c ty) = {ty} ∧
  types_in (Comb t1 t2) = types_in t1 ∪ types_in t2 ∧
  types_in (Abs v t) = types_in v ∪ types_in t
End

Theorem type_ok_types_in:
   ∀sig. is_std_sig sig ⇒ ∀tm ty. term_ok sig tm ∧ ty ∈ types_in tm ⇒ type_ok (tysof sig) ty
Proof
  gen_tac >> strip_tac >> Induct >> simp[] >> rw[] >>
  TRY (imp_res_tac term_ok_def >> NO_TAC) >> fs[term_ok_def]
QED

Theorem VFREE_IN_types_in:
   ∀t2 t1. VFREE_IN t1 t2 ⇒ typeof t1 ∈ types_in t2
Proof
  ho_match_mp_tac term_induction >> rw[] >> rw[]
QED

Theorem Var_subterm_types_in[local]:
  ∀t x ty. Var x ty subterm t ⇒ ty ∈ types_in t
Proof
  ho_match_mp_tac term_induction >> rw[subterm_Comb,subterm_Abs] >>
  metis_tac[]
QED

Theorem Const_subterm_types_in[local]:
  ∀t x ty. Const x ty subterm t ⇒ ty ∈ types_in t
Proof
  ho_match_mp_tac term_induction >> rw[subterm_Comb,subterm_Abs] >>
  metis_tac[]
QED

Theorem subterm_typeof_types_in:
   ∀t1 t2 name args. (Tyapp name args) subtype (typeof t1) ∧ t1 subterm t2 ∧ welltyped t2 ∧ name ≠ «fun» ⇒
      ∃ty2. Tyapp name args subtype ty2 ∧ ty2 ∈ types_in t2
Proof
  ho_match_mp_tac term_induction >>
  conj_tac >- ( rw[] >> metis_tac[Var_subterm_types_in] ) >>
  conj_tac >- ( rw[] >> metis_tac[Const_subterm_types_in] ) >>
  conj_tac >- (
    rw[] >>
    imp_res_tac subterm_welltyped >> fs[] >> fs[] >>
    last_x_assum match_mp_tac >> simp[] >>
    conj_tac >- (
      simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[subtype_Tyapp] >>
      metis_tac[relationTheory.RTC_REFL] ) >>
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[subterm_Comb] ) >>
  rw[] >>
  fs[subtype_Tyapp] >- (
    last_x_assum(match_mp_tac) >> simp[] >>
    conj_tac >- (
      simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] ) >>
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[subterm_Abs] ) >>
  first_x_assum(match_mp_tac) >> simp[] >>
  conj_tac >- (
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[subterm_Abs]
QED

(* a type matching algorithm, based on the implementation in HOL4 *)

Definition tymatch_def:
  (tymatch [] [] sids = SOME sids) ∧
  (tymatch [] _ _ = NONE) ∧
  (tymatch _ [] _ = NONE) ∧
  (tymatch (Tyvar name::ps) (ty::obs) sids =
   let (s,ids) = sids in
   let v = REV_ASSOCD (Tyvar name) s (Tyvar name) in
   case if v = Tyvar name then
          if MEM name ids then SOME v else NONE
        else SOME v
   of NONE => if v=ty then tymatch ps obs (s,name::ids) else tymatch ps obs ((ty,v)::s,ids)
    | SOME ty1 => if ty1=ty then tymatch ps obs sids else NONE) ∧
  (tymatch (Tyapp c1 a1::ps) (Tyapp c2 a2::obs) sids =
   if c1=c2 then tymatch (a1++ps) (a2++obs) sids else NONE) ∧
  (tymatch _ _ _ = NONE)
End

Definition arities_match_def:
  (arities_match [] [] ⇔ T) ∧
  (arities_match [] _ ⇔ F) ∧
  (arities_match _ [] ⇔ F) ∧
  (arities_match (Tyapp c1 a1::xs) (Tyapp c2 a2::ys) ⇔
   ((c1 = c2) ⇒ arities_match a1 a2) ∧ arities_match xs ys) ∧
  (arities_match (_::xs) (_::ys) ⇔ arities_match xs ys)
End

Theorem arities_match_length:
   ∀l1 l2. arities_match l1 l2 ⇒ (LENGTH l1 = LENGTH l2)
Proof
  ho_match_mp_tac arities_match_ind >> simp[arities_match_def]
QED

Theorem arities_match_nil[simp]:
   (arities_match [] ls = (ls = [])) ∧
    (arities_match ls [] = (ls = []))
Proof
  Cases_on`ls`>> simp[arities_match_def]
QED

Theorem arities_match_Tyvar[simp]:
   arities_match (Tyvar v::ps) (ty::obs) = arities_match ps obs
Proof
  Cases_on`ty`>>simp[arities_match_def]
QED

Theorem arities_match_append:
   ∀l1 l2 l3 l4.
    arities_match l1 l2 ∧ arities_match l3 l4 ⇒
    arities_match (l1++l3) (l2++l4)
Proof
  ho_match_mp_tac arities_match_ind >>
  simp[arities_match_def]
QED

Theorem tymatch_SOME:
   ∀ps obs sids s' ids'.
     arities_match ps obs ∧
      DISJOINT (set (MAP SND (FST sids))) (set (MAP Tyvar (SND sids))) ∧
      (∀name. ¬MEM (Tyvar name,Tyvar name) (FST sids)) ∧
      ALL_DISTINCT (MAP SND (FST sids)) ∧
      (tymatch ps obs sids = SOME (s',ids')) ⇒
       ∃s1 ids1.
         (s' = s1++(FST sids)) ∧ (ids' = ids1++(SND sids)) ∧
         DISJOINT (set (MAP SND s')) (set (MAP Tyvar ids')) ∧
         (∀name. ¬MEM (Tyvar name,Tyvar name) s') ∧
         ALL_DISTINCT (MAP SND s') ∧
         (MAP (TYPE_SUBST s') ps = obs)
Proof
  ho_match_mp_tac tymatch_ind >>
  simp[tymatch_def,arities_match_def] >>
  conj_tac >- (
    rpt gen_tac >>
    `∃s ids. sids = (s,ids)` by metis_tac[pairTheory.pair_CASES] >>
    simp[] >> strip_tac >>
    rpt gen_tac >>
    reverse IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[arities_match_def] >> rfs[] >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND,ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[] >> rfs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND,ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[] >> rfs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      `¬MEM (Tyvar name) (MAP SND s)` by (
        fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
        BasicProvers.EVERY_CASE_TAC >- (
          imp_res_tac ALOOKUP_FAILS >> fs[MEM_MAP,EXISTS_PROD] ) >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      reverse BasicProvers.EVERY_CASE_TAC >> fs[] >- (
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[ALL_DISTINCT_APPEND] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    strip_tac >> fs[] >> rfs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    `¬MEM (Tyvar name) (MAP SND s)` by (
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
      BasicProvers.EVERY_CASE_TAC >- (
        imp_res_tac ALOOKUP_FAILS >> fs[MEM_MAP,EXISTS_PROD] ) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    `¬MEM (Tyvar name) (MAP Tyvar ids)` by fs[MEM_MAP] >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
    BasicProvers.CASE_TAC >>
    fs[ALL_DISTINCT_APPEND] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `arities_match (a1++ps) (a2++obs)` by
    (imp_res_tac arities_match_append) >>
  fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac (std_ss++ETA_ss) [] >>
  imp_res_tac arities_match_length >>
  fs[APPEND_EQ_APPEND] >>
  rfs[] >>
  `LENGTH l = 0` by DECIDE_TAC >>
  fs[LENGTH_NIL]
QED

Definition match_type_def:
  match_type ty1 ty2 = OPTION_MAP FST (tymatch [ty1] [ty2] ([],[]))
End

Theorem type_ok_arities_match:
   ∀tys ty1 ty2.
    type_ok tys ty1 ∧ type_ok tys ty2 ⇒ arities_match [ty1] [ty2]
Proof
  gen_tac >> ho_match_mp_tac type_ind >> simp[] >>
  gen_tac >> strip_tac >>
  gen_tac >> Cases >> simp[arities_match_def] >>
  rw[type_ok_def] >> fs[] >>
  fs[EVERY_MEM] >>
  `∀ty1 ty2. MEM ty1 l ∧ MEM ty2 l' ⇒ arities_match [ty1] [ty2]` by metis_tac[] >>
  pop_assum mp_tac >>
  qpat_x_assum`LENGTH X = Y`mp_tac >>
  rpt (pop_assum kall_tac) >>
  map_every qid_spec_tac[`l'`,`l`] >>
  Induct >> simp[LENGTH_NIL] >>
  gen_tac >> Cases >> rw[] >>
  `arities_match l t` by metis_tac[] >>
  `arities_match [h] [h']` by metis_tac[] >>
  metis_tac[arities_match_append,APPEND]
QED

Theorem match_type_SOME:
   ∀ty1 ty2 s. arities_match [ty1] [ty2] ⇒
    (match_type ty1 ty2 = SOME s) ⇒
    (TYPE_SUBST s ty1 = ty2)
Proof
  rw[match_type_def] >>
  qspecl_then[`[ty1]`,`[ty2]`,`[],[]`]mp_tac tymatch_SOME >>
  simp[] >>
  Cases_on`z`>>simp[]
QED
