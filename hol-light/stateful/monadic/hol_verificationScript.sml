open HolKernel Parse boolLib bossLib lcsymtacs alistTheory listTheory arithmeticTheory combinTheory finite_mapTheory pairTheory monadsyntax
open miscLib miscTheory hol_kernelTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory

val _ = new_theory "hol_verification";

val _ = temp_overload_on ("monad_bind", ``ex_bind``);
val _ = temp_overload_on ("return", ``ex_return``);

infix \\ val op \\ = op THEN;

val rev_assocd_thm = prove(
  ``rev_assocd = REV_ASSOCD``,
  SIMP_TAC std_ss [FUN_EQ_THM] \\ Induct_on `x'`
  \\ ONCE_REWRITE_TAC [rev_assocd_def] \\ SRW_TAC [] [REV_ASSOCD]
  \\ Cases_on `h` \\ SRW_TAC [] [REV_ASSOCD]);

(* ------------------------------------------------------------------------- *)
(* Translations from implementation types to model types.                    *)
(* ------------------------------------------------------------------------- *)

val _ = temp_overload_on("impossible_term",``holSyntax$Comb (Var "x" Bool) (Var "x" Bool)``);

val hol_ty_def = tDefine "hol_ty" `
  (hol_ty (hol_kernel$Tyvar v) = holSyntax$Tyvar v) /\
  (hol_ty (Tyapp s tys) = Tyapp s (MAP hol_ty tys))`
 (WF_REL_TAC `measure hol_type_size` \\ REPEAT STRIP_TAC
  \\ SUFF_TAC ``hol_type_size a < hol_type1_size tys`` THEN1 DECIDE_TAC
  \\ Induct_on `tys` \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [hol_type_size_def] \\ DECIDE_TAC);

val hol_tm_def = Define `
  (hol_tm (hol_kernel$Var v ty) = holSyntax$Var v (hol_ty ty)) /\
  (hol_tm (Const s ty) = Const s (hol_ty ty)) /\
  (hol_tm (Comb x y) = Comb (hol_tm x) (hol_tm y)) /\
  (hol_tm (Abs (Var v ty) x) = Abs v (hol_ty ty) (hol_tm x)) /\
  (hol_tm _ = impossible_term)`;

val hol_def_def = Define`
  (hol_def (NewAxiom prop) = NewAxiom (hol_tm prop)) ∧
  (hol_def (NewConst s ty) = NewConst s (hol_ty ty)) ∧
  (hol_def (NewType s n) = NewType s n) ∧
  (hol_def (ConstSpec eqs tm) =
    ConstSpec (MAP (\(s,t). (s, hol_tm t)) eqs) (hol_tm tm)) ∧
  (hol_def (TypeDefn s1 tm s2 s3) =
    TypeDefn s1 (hol_tm tm) s2 s3)`

val _ = Parse.overload_on("hol_defs",``λdefs. MAP hol_def defs``)

(* ------------------------------------------------------------------------- *)
(* type_ok, term_ok, context_ok and |- for implementation types.             *)
(* ------------------------------------------------------------------------- *)

val TYPE_def = Define `
  TYPE defs ty = type_ok (tysof (hol_defs defs)) (hol_ty ty)`;

val TERM_def = Define `
  TERM defs tm = term_ok (sigof (hol_defs defs)) (hol_tm tm)`;

val CONTEXT_def = Define `
  CONTEXT defs = (hol_defs defs) extends init_ctxt`;

val THM_def = Define `
  THM defs (Sequent asl c) = ((thyof (hol_defs defs), MAP hol_tm asl) |- hol_tm c)`;

(* ------------------------------------------------------------------------- *)
(* State invariant - types/terms can be extracted from defs                  *)
(* ------------------------------------------------------------------------- *)

val STATE_def = Define `
  STATE state defs =
    let ctxt = hol_defs defs in
      (defs = state.the_definitions) /\ CONTEXT defs /\
      (state.the_type_constants = type_list ctxt) /\
      (MAP (λ(name,ty). (name, hol_ty ty)) state.the_term_constants = const_list ctxt) /\
      TERM defs state.the_clash_var`;

val STATE_def = STATE_def |> SIMP_RULE std_ss [LET_DEF];

(* ------------------------------------------------------------------------- *)
(* impossible term lemmas                                                    *)
(* ------------------------------------------------------------------------- *)

val term_ok_impossible_term = prove(
  ``~(term_ok defs impossible_term)``,
  simp[term_ok_def])

val impossible_term_thm = prove(
  ``TERM defs tm ==> hol_tm tm <> impossible_term``,
  SIMP_TAC std_ss [TERM_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def,term_ok_impossible_term])

val Abs_Var = prove(
  ``TERM defs (Abs v tm) ==> ?s ty. v = Var s ty``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC impossible_term_thm
  \\ Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def])

(* ------------------------------------------------------------------------- *)
(* invariant lemmas                                                          *)
(* ------------------------------------------------------------------------- *)

(* TODO: move*)
val updates_ALL_DISTINCT = store_thm("updates_ALL_DISTINCT",
  ``∀upd ctxt. upd updates ctxt ⇒
      (ALL_DISTINCT (MAP FST (type_list ctxt)) ⇒
       ALL_DISTINCT (MAP FST (type_list (upd::ctxt)))) ∧
      (ALL_DISTINCT (MAP FST (const_list ctxt)) ⇒
       ALL_DISTINCT (MAP FST (const_list (upd::ctxt))))``,
  ho_match_mp_tac updates_ind >> simp[] >>
  rw[ALL_DISTINCT_APPEND,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX])

val extends_ALL_DISTINCT = store_thm("extends_ALL_DISTINCT",
  ``∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒
      (ALL_DISTINCT (MAP FST (type_list ctxt1)) ⇒
       ALL_DISTINCT (MAP FST (type_list ctxt2))) ∧
      (ALL_DISTINCT (MAP FST (const_list ctxt1)) ⇒
       ALL_DISTINCT (MAP FST (const_list ctxt2)))``,
  simp[IMP_CONJ_THM,FORALL_AND_THM] >> conj_tac >>
  ho_match_mp_tac extends_ind >>
  METIS_TAC[updates_ALL_DISTINCT])

val init_ALL_DISTINCT = store_thm("init_ALL_DISTINCT",
  ``ALL_DISTINCT (MAP FST (const_list init_ctxt)) ∧
    ALL_DISTINCT (MAP FST (type_list init_ctxt))``,
  EVAL_TAC)

val CONTEXT_ALL_DISTINCT = prove(
  ``CONTEXT defs ⇒ ALL_DISTINCT (MAP FST (type_list (hol_defs defs))) ∧
                   ALL_DISTINCT (MAP FST (const_list (hol_defs defs)))``,
  rw[CONTEXT_def] >>
  METIS_TAC[extends_ALL_DISTINCT,init_ALL_DISTINCT])

val STATE_ALL_DISTINCT = prove(
  ``STATE s defs ⇒ ALL_DISTINCT (MAP FST (type_list (hol_defs defs))) ∧
                   ALL_DISTINCT (MAP FST (const_list (hol_defs defs)))``,
  rw[STATE_def] >> METIS_TAC[CONTEXT_ALL_DISTINCT])

val TYPE_Tyapp = prove(
  ``MEM (tyop,LENGTH args) r.the_type_constants /\
    STATE r defs /\ EVERY (TYPE defs) args ==>
    TYPE defs (Tyapp tyop args)``,
  rw[EVERY_MEM,TYPE_def,hol_ty_def] >>
  imp_res_tac STATE_ALL_DISTINCT >>
  fs[STATE_def] >> rw[type_ok_def,EVERY_MAP,EVERY_MEM] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM)

val CONTEXT_std_sig = prove(
  ``CONTEXT defs ⇒ is_std_sig (sigof (hol_defs defs))``,
  rw[CONTEXT_def] >>
  imp_res_tac extends_theory_ok >> fs[init_theory_ok] >>
  imp_res_tac theory_ok_sig >> fs[is_std_sig_def])

val CONTEXT_fun = prove(
  ``CONTEXT defs ⇒
      ∀a. MEM ("fun",a) (type_list (hol_defs defs)) ⇔ (a = 2)``,
  rw[] >> imp_res_tac CONTEXT_ALL_DISTINCT >>
  imp_res_tac CONTEXT_std_sig >>
  fs[is_std_sig_def] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  EQ_TAC >> rw[] >> res_tac >> fs[] >>
  imp_res_tac ALOOKUP_MEM)

val TYPE = prove(
  ``(STATE state defs ==> TYPE defs (Tyvar v)) /\
    (TYPE defs (Tyapp op tys) ==> EVERY (TYPE defs) tys)``,
  conj_tac >- (
    simp[STATE_def,TYPE_def,hol_ty_def,EVERY_MEM] >>
    rw[] >> simp[type_ok_def] ) >>
  rw[EVERY_MEM,TYPE_def,hol_ty_def] >>
  fs[type_ok_def,EVERY_MAP,EVERY_MEM]);

val TERM = prove(
  ``(TERM defs (Var n ty) ==> TYPE defs ty) /\
    (TERM defs (Const n ty) ==> TYPE defs ty) /\
    (TERM defs (Abs (Var v ty) x) ==> TERM defs x /\ TYPE defs ty) /\
    (TERM defs (Comb x y) ==> TERM defs x /\ TERM defs y)``,
  rw[TERM_def,TYPE_def,hol_tm_def] >> fs[term_ok_def])

val TYPE_Fun = prove(
  ``CONTEXT defs ∧ TYPE defs ty1 /\ TYPE defs ty2 ==>
    TYPE defs (Tyapp "fun" [ty1;ty2])``,
  rw[TYPE_def,hol_ty_def,type_ok_def] >>
  imp_res_tac CONTEXT_fun >>
  METIS_TAC[ALOOKUP_ALL_DISTINCT_MEM,CONTEXT_ALL_DISTINCT]);

val TYPE_11 = prove(
  ``!x y. ((hol_ty x = hol_ty y) = (x = y))``,
  (TypeBase.induction_of(``:hol_type``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE(srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> GEN_ALL
  |> HO_MATCH_MP_TAC) >>
  rw[hol_ty_def] >>
  Cases_on`y`>>rw[hol_ty_def] >>
  rw[MAP_EQ_EVERY2,EVERY2_EVERY] >>
  rw[EQ_IMP_THM] >>
  fs[EVERY_MEM] >> rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,MEM_EL] >>
  simp[LIST_EQ_REWRITE]);

val TERM_11 = prove(
  ``!x y. TERM defs x /\ TERM defs y ==>
          ((hol_tm x = hol_tm y) = (x = y))``,
  Induct >> rw[hol_tm_def] >> fs[] >- (
    Cases_on`y`>>rw[hol_tm_def,TYPE_11] >>
    Cases_on`h'`>>rw[hol_tm_def] )
  >- (
    Cases_on`y`>>rw[hol_tm_def,TYPE_11] >>
    Cases_on`h'`>>fs[hol_tm_def,term_ok_impossible_term] )
  >- (
    fs[TERM_def,hol_tm_def,term_ok_def] >>
    Cases_on`y`>>rw[hol_tm_def,TYPE_11]
    >- METIS_TAC[] >>
    Cases_on`h`>>fs[hol_tm_def,term_ok_impossible_term] ) >>
  fs[TERM_def] >>
  Cases_on`x`>>fs[hol_tm_def,term_ok_impossible_term] >>
  Cases_on`y`>>fs[hol_tm_def] >>
  Cases_on`h'`>>fs[hol_tm_def,term_ok_impossible_term,hol_ty_def,TYPE_11] >>
  fs[term_ok_def] >>
  METIS_TAC[]);

val TERM_Var_SIMP = prove(
  ``(TERM defs (Var n ty) = TYPE defs ty)``,
  rw[TERM_def,TYPE_def,hol_tm_def,term_ok_def]);

val TERM_Var = prove(
  ``TYPE defs ty ==> TERM defs (Var n ty)``,
  METIS_TAC [TERM_Var_SIMP]);

val IMP_TERM_Abs = prove(
  ``TERM defs (Var str ty) /\ TERM defs bod ==>
    TERM defs (Abs (Var str ty) bod)``,
  fs[TERM_def,hol_tm_def,term_ok_def]);

val IMP_TERM_Comb = prove(
  ``TERM defs f /\
    TERM defs a /\
    (typeof (hol_tm a) = ty1) /\
    (typeof (hol_tm f) = Fun ty1 ty2) ==>
    TERM defs (Comb f a)``,
  rw[TERM_def,hol_tm_def,term_ok_def] >>
  METIS_TAC[term_ok_welltyped])

val TERM_Abs = prove(
  ``TERM defs (Abs (Var v ty) tm) <=> TYPE defs ty /\ TERM defs tm``,
  rw[TERM_def,hol_tm_def,term_ok_def,TYPE_def]);

val INST_CORE_LEMMA =
  INST_CORE_HAS_TYPE |> Q.SPECL [`holSyntax$sizeof tm`,`tm`,`[]`,`tyin`]
  |> SIMP_RULE std_ss [MEM,REV_ASSOCD] |> Q.GENL [`tm`,`tyin`]

val INST_CORE_EMPTY = prove(
  ``!tm env.
      EVERY (\(x,y). x = y) env ==>
      (holSyntax$INST_CORE env [] tm = Result tm)``,
  completeInduct_on `holSyntax$sizeof tm` \\ Cases \\ REPEAT STRIP_TAC
  THEN1 (ONCE_REWRITE_TAC [INST_CORE_def] \\ SIMP_TAC std_ss [TYPE_SUBST_NIL]
    \\ `REV_ASSOCD (Var s t) env (Var s t) = Var s t` by ALL_TAC THEN1
     (POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Induct_on `env` \\ FULL_SIMP_TAC std_ss [REV_ASSOCD]
      \\ Cases \\ FULL_SIMP_TAC std_ss [REV_ASSOCD,EVERY_DEF])
    \\ FULL_SIMP_TAC std_ss [LET_THM])
  THEN1 (ONCE_REWRITE_TAC [INST_CORE_def] \\ SIMP_TAC std_ss [TYPE_SUBST_NIL])
  THEN1
   (FULL_SIMP_TAC std_ss [sizeof_def,term_ok_def]
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ ONCE_REWRITE_TAC [INST_CORE_def]
    \\ qmatch_assum_rename_tac`v = 1 + holSyntax$sizeof a0 + holSyntax$sizeof a1`[]
    \\ FIRST_X_ASSUM (fn th => MP_TAC (Q.SPECL [`a0`,`env`] th) THEN
                               MP_TAC (Q.SPECL [`a1`,`env`] th))
    \\ simp[] ) >>
  ONCE_REWRITE_TAC [INST_CORE_def]
  \\ FULL_SIMP_TAC std_ss [TYPE_SUBST_NIL,PULL_FORALL,sizeof_def]
  >> simp[])
  |> Q.SPECL [`tm`,`[]`] |> SIMP_RULE std_ss [EVERY_DEF] |> GEN_ALL;

val THM = prove(
  ``THM defs (Sequent asl c) ==> EVERY (TERM defs) asl /\ TERM defs c``,
  SIMP_TAC std_ss [THM_def] \\ SIMP_TAC std_ss [EVERY_MEM] >>
  strip_tac >> imp_res_tac proves_term_ok >>
  fs[EVERY_MEM,TERM_def,MEM_MAP,PULL_EXISTS])

(*
val MEM_types_Typedef = store_thm("MEM_types_Typedef",
  ``∀x defs. MEM x (FLAT (MAP types_aux defs)) ⇒ ∃t a r. MEM (Typedef (FST x) t a r) defs ∧ (LENGTH (tvars t) = SND x)``,
  Cases >> Induct >> simp[] >>
  Cases >> simp[types_aux_def] >> fs[] >>
  METIS_TAC[])

val MEM_Typedef_MEM_consts_type = store_thm("MEM_Typedef_MEM_consts_type",
  ``∀defs n tm a r. MEM (Typedef n tm a r) defs ⇒
    let rty = domain (typeof tm) in
    let aty = holSyntax$Tyapp n (MAP holSyntax$Tyvar (STRING_SORT (tvars tm))) in
    MEM (a,Fun rty aty) (FLAT (MAP consts_aux defs)) ∧
    MEM (r,Fun aty rty) (FLAT (MAP consts_aux defs))``,
  Induct >> simp[] >>
  rw[consts_def,consts_aux_def] >>
  rw[consts_def,consts_aux_def] >>
  fs[consts_def] >>
  res_tac >>
  fs[LET_THM])

val INST_HAS_TYPE = store_thm("INST_HAS_TYPE",
  ``∀tm tyin ty. tm has_type ty ⇒ holSyntax$INST tyin tm has_type TYPE_SUBST tyin ty``,
  rw[holSyntaxTheory.INST_def] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac holSyntaxTheory.INST_CORE_HAS_TYPE >>
  simp[] >>
  `welltyped tm` by METIS_TAC[holSyntaxTheory.welltyped_def] >>
  imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
  simp[] >>
  simp[REV_ASSOCD] >> rw[] >> rw[])

val INST_CORE_NIL_is_Result = store_thm("INST_CORE_NIL_is_Result",
  ``∀tyin tm. welltyped tm ⇒ ∃r. holSyntax$INST_CORE [] tyin tm = Result r``,
  rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[REV_ASSOCD] >> rw[] >> rw[])

val INST_equation = store_thm("INST_equation",
  ``∀tyin l r. welltyped (l === r) ⇒ (holSyntax$INST tyin (l === r) = (INST tyin l) === (INST tyin r))``,
  rw[INST_def,equation_def,INST_CORE_def] >>
  UNABBREV_ALL_TAC >> rw[] >> fs[] >>
  imp_res_tac INST_CORE_NIL_is_Result >> fs[] >>
  rpt (first_x_assum(qspec_then`tyin`STRIP_ASSUME_TAC)) >>
  fs[] >> rw[] >>
  qspecl_then[`sizeof l`,`l`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  qspecl_then[`sizeof r`,`r`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[REV_ASSOCD] >> rw[] >> imp_res_tac WELLTYPED_LEMMA >> rw[] )

val term_ok_Comb_welltyped = prove(
  ``term_ok defs (Comb f x) ==> welltyped (Comb f x)``,
  rw[] >> IMP_RES_TAC term_ok_welltyped >> fs[])

val term_ok_Comb = store_thm("term_ok_Comb",
  ``term_ok defs (Comb t1 t2) ⇔ term_ok defs t1 ∧ term_ok defs t2 ∧ welltyped (Comb t1 t2)``,
  EQ_TAC >- (
    strip_tac >>
    imp_res_tac term_ok_Comb_welltyped >>
    simp[] >>
    conj_tac >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  rw[] >>
  simp[Once proves_cases])

val term_ok_Var = store_thm("term_ok_Var",
  ``term_ok defs (Var x ty) ⇔ type_ok defs ty``,
  EQ_TAC >> rw[] >>
  simp[Once proves_cases] >>
  ntac 2 disj2_tac >> disj1_tac >>
  HINT_EXISTS_TAC >>
  rw[] >>
  rw[Once has_type_cases])

val term_ok_Abs = store_thm("term_ok_Abs",
  ``(term_ok defs (Abs x ty tm) ⇔ term_ok defs (Var x ty) ∧ term_ok defs tm)``,
  EQ_TAC >- (
    strip_tac >>
    conj_tac >- (
      simp[Once proves_cases] >>
      disj1_tac >>
      qsuff_tac`type_ok defs (Fun ty (typeof tm))` >- rw[type_ok_Fun] >>
      simp[Once proves_cases] >>
      disj1_tac >>
      HINT_EXISTS_TAC >>
      rw[] >>
      rw[Once has_type_cases] >>
      imp_res_tac term_ok_welltyped >>
      fs[] >> METIS_TAC[WELLTYPED] ) >>
    simp[Once proves_cases] >>
    METIS_TAC[] ) >>
  rw[] >>
  simp[Once proves_cases] >>
  disj1_tac >>
  fs[term_ok_Var])

val term_ok_inst_type_Const = store_thm("term_ok_inst_type_Const",
  ``∀defs name theta ty. term_ok defs (Const name ty) ∧
    (∀s s'. MEM (s',s) theta ⇒ type_ok defs s')
    ⇒ term_ok defs (Const name (TYPE_SUBST theta ty))``,
  rw[] >>
  qmatch_abbrev_tac`term_ok defs c` >>
  qsuff_tac`term_ok defs (c === c)` >- (
    rw[term_ok_equation] ) >>
  qsuff_tac`(defs,[]) |- (c === c)` >- (
    strip_tac >>
    MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,11)) >>
    qexists_tac`[]`>>simp[] ) >>
  qmatch_assum_abbrev_tac`term_ok defs c0` >>
  `c0 === c0 has_type Bool` by (
    simp[EQUATION_HAS_TYPE_BOOL] >>
    METIS_TAC[term_ok_welltyped] ) >>
  `welltyped (c0 === c0)` by METIS_TAC[welltyped_def] >>
  `c === c = INST theta (c0 === c0)` by (
    simp[INST_equation,Abbr`c`,Abbr`c0`,INST_def,INST_CORE_def] ) >>
  pop_assum SUBST1_TAC >>
  `[] = MAP (INST theta) []` by simp[] >>
  pop_assum SUBST1_TAC >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,22)) >>
  conj_tac >- METIS_TAC[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,14)) >>
  metis_tac[proves_IMP])

val type_IND = prove(
  ``!P. (!v. P (Tyvar v)) /\ (!op tys. EVERY P tys ==> P (Tyapp op tys)) ==>
        (!ty. P (ty:hol_type))``,
  REPEAT STRIP_TAC \\ completeInduct_on `hol_type_size ty`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ Cases_on `ty` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!op tys. bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`e`,`e`) \\ Q.SPEC_TAC (`l`,`l`)
  \\ Induct \\ SIMP_TAC std_ss [MEM,hol_type_size_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [hol_type_size_def] \\ DECIDE_TAC);

val has_type_11 = prove(
  ``!t:holSyntax$term ty1 ty2. t has_type ty1 /\ t has_type ty2 ==> (ty1 = ty2)``,
  Induct \\ REPEAT STRIP_TAC \\ NTAC 2 (POP_ASSUM MP_TAC)
  \\ SIMP_TAC std_ss [Once has_type_cases] \\ STRIP_TAC
  \\ SIMP_TAC std_ss [Once has_type_cases] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [term_11,term_distinct] \\ RES_TAC
  \\ fs[] >> rw[] >> res_tac >> fs[])

val typeof_VSUBST = prove(
  ``welltyped rhs /\
     (!s s'.
        MEM (s',s) ilist ==>
        ?x ty. (s = Var x ty) /\ s' has_type ty) ==>
    (typeof (holSyntax$VSUBST ilist rhs) = typeof rhs)``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC VSUBST_WELLTYPED
  \\ FULL_SIMP_TAC std_ss [WELLTYPED]
  \\ IMP_RES_TAC VSUBST_HAS_TYPE
  \\ IMP_RES_TAC has_type_11);

val term_ok_VSUBST = prove(
  ``!y ilist. term_ok defs y /\ EVERY (\(x,y). term_ok defs x /\ ?z ty. y = Var z ty /\ x has_type ty) ilist ==>
        term_ok defs (VSUBST ilist y)``,
  Induct \\ SIMP_TAC std_ss [VSUBST_def,term_ok_Var,term_ok_Comb,term_ok_Abs]
  \\ SRW_TAC [] [] THEN1
   (Induct_on `ilist`
    \\ FULL_SIMP_TAC std_ss [REV_ASSOCD,term_ok_Var]
    \\ Cases \\ SRW_TAC [] [REV_ASSOCD,term_ok_Var])
  \\ TRY (
    MATCH_MP_TAC VSUBST_WELLTYPED >>
    fs[EVERY_MEM,FORALL_PROD] )
  \\ TRY (
    imp_res_tac typeof_VSUBST >>
    fs[EVERY_MEM,FORALL_PROD] >>
    NO_TAC )
  \\ SRW_TAC [] [term_ok_Abs,term_ok_Var]
  \\ UNABBREV_ALL_TAC
  \\ Q.PAT_ASSUM `!ii.bbb` MATCH_MP_TAC
  >> simp[term_ok_Var]
  >> TRY(conj_tac >- simp[Once has_type_cases])
  >> fs[EVERY_MEM,MEM_FILTER,FORALL_PROD]
  >> METIS_TAC[])

val type_subst_EMPTY = prove(
  ``!ty. type_subst [] ty = ty``,
  HO_MATCH_MP_TAC type_IND
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once type_subst_def]
  \\ SIMP_TAC std_ss [rev_assocd_thm,REV_ASSOCD,LET_DEF]
  \\ `MAP (\a. type_subst [] a) tys = tys` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Induct_on `tys` \\ FULL_SIMP_TAC std_ss [MAP,EVERY_DEF]);

*)

(* ------------------------------------------------------------------------- *)
(* Verification of type functions                                            *)
(* ------------------------------------------------------------------------- *)

val can_thm = prove(
  ``can f x s = case f x s of (HolRes _,s) => (HolRes T,s) |
                              (_,s) => (HolRes F,s)``,
  SIMP_TAC std_ss [can_def,ex_bind_def,otherwise_def]
  \\ Cases_on `f x s` \\ Cases_on `q`
  \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]);

val assoc_thm = prove(
  ``!xs y z s s'.
      (assoc y xs s = (z, s')) ==>
      (s' = s) /\ (!i. (z = HolRes i) ==> MEM (y,i) xs) /\
                  (!e. (z = HolErr e) ==> !i. ~MEM (y,i) xs)``,
  Induct \\ SIMP_TAC (srw_ss()) [Once assoc_def,failwith_def]
  \\ Cases \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ Cases_on `y = q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ METIS_TAC []);

val get_type_arity_thm = prove(
  ``!name s z s'.
      (get_type_arity name s = (z,s')) ==> (s' = s) /\
      (!i. (z = HolRes i) ==> MEM (name,i) s.the_type_constants) /\
      (!e. (z = HolErr e) ==> !i. ~MEM (name,i) s.the_type_constants)``,
  SIMP_TAC (srw_ss()) [get_type_arity_def,ex_bind_def,
    get_the_type_constants_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC assoc_thm);

val mk_vartype_thm = store_thm("mk_vartype_thm",
  ``!name s.
      STATE s s.the_definitions ⇒
      TYPE s.the_definitions (mk_vartype name)``,
  SIMP_TAC (srw_ss()) [mk_vartype_def,TYPE_def,hol_ty_def,type_ok_def,STATE_def]);

val mk_type_thm = store_thm("mk_type_thm",
  ``!tyop args s z s'.
      STATE s defs /\ EVERY (TYPE defs) args /\
      (mk_type (tyop,args) s = (z,s')) ==> (s' = s) /\
      ((tyop = "fun") /\ (LENGTH args = 2) ==> ?i. z = HolRes i) /\
      !i. (z = HolRes i) ==> TYPE defs i /\ (i = Tyapp tyop args)``,
  SIMP_TAC std_ss [mk_type_def,try_def,ex_bind_def,otherwise_def]
  \\ NTAC 3 STRIP_TAC \\ Cases_on `get_type_arity tyop s`
  \\ IMP_RES_TAC get_type_arity_thm
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def,ex_return_def]
  \\ SRW_TAC [] [ex_return_def]
  \\ IMP_RES_TAC TYPE_Tyapp
  \\ fs[STATE_def] >> METIS_TAC[CONTEXT_fun])

val dest_type_thm = store_thm("dest_type_thm",
  ``!ty s z s'.
      STATE s defs /\
      (dest_type ty s = (z,s')) /\ TYPE defs ty ==> (s' = s) /\
      !i. (z = HolRes i) ==> ?n tys. (ty = Tyapp n tys) /\ (i = (n,tys)) /\
                                     EVERY (TYPE defs) tys``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def,failwith_def,ex_return_def]
  \\ FULL_SIMP_TAC std_ss [TYPE_def,hol_ty_def,EVERY_MEM] \\ SRW_TAC [] []
  >> fs[type_ok_def,EVERY_MAP,EVERY_MEM])

val dest_vartype_thm = store_thm("dest_vartype_thm",
  ``!ty s z s'.
      (dest_vartype ty s = (z,s')) ==> (s' = s) /\
      !i. (z = HolRes i) ==> (ty = Tyvar i)``,
  Cases \\ FULL_SIMP_TAC (srw_ss())
    [dest_vartype_def,failwith_def,ex_return_def]);

val is_type_thm = store_thm("is_type_thm",
  ``!ty. is_type ty = ?s tys. ty = Tyapp s tys``,
  Cases \\ SIMP_TAC (srw_ss()) [is_type_def]);

val is_vartype_thm = store_thm("is_vartype_thm",
  ``!ty. is_vartype ty = ?s. ty = Tyvar s``,
  Cases \\ SIMP_TAC (srw_ss()) [is_vartype_def]);

val MEM_union = prove(
  ``!xs ys x. MEM x (union xs ys) <=> MEM x xs \/ MEM x ys``,
  Induct \\ FULL_SIMP_TAC std_ss [union_def]
  \\ ONCE_REWRITE_TAC [itlist_def] \\ SRW_TAC [] [insert_def]
  \\ METIS_TAC []);

val tyvars_thm = prove(
  ``!ty s. MEM s (tyvars ty) = MEM s (tyvars (hol_ty ty))``,
  HO_MATCH_MP_TAC hol_kernelTheory.tyvars_ind \\ REPEAT STRIP_TAC
  \\ Cases_on `ty` \\ FULL_SIMP_TAC (srw_ss()) [type_11,type_distinct]
  \\ SIMP_TAC (srw_ss()) [Once hol_kernelTheory.tyvars_def,
       Once holSyntaxTheory.tyvars_def,hol_ty_def]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.FOLDR_MAP]
  \\ Induct_on `l`
  \\ SIMP_TAC (srw_ss()) [Once itlist_def,FOLDR,MEM_union,MEM_LIST_UNION]
  \\ METIS_TAC []);

val type_subst_thm = store_thm("type_subst",
  ``!i ty.
      (hol_ty (type_subst i ty) =
       holSyntax$TYPE_SUBST (MAP (\(n,t). (hol_ty n,hol_ty t)) i) (hol_ty ty)) /\
      (EVERY (\(x,y). TYPE s x /\ TYPE s y) i /\ TYPE s ty ==>
       TYPE s (type_subst i ty))``,
  HO_MATCH_MP_TAC type_subst_ind \\ STRIP_TAC \\ Cases THEN1
   (SIMP_TAC (srw_ss()) [Once type_subst_def]
    \\ SIMP_TAC (srw_ss()) [Once type_subst_def]
    \\ SIMP_TAC std_ss [hol_ty_def,TYPE_SUBST_def]
    \\ Induct_on `i` \\ TRY Cases \\ ONCE_REWRITE_TAC [rev_assocd_def]
    \\ SIMP_TAC (srw_ss()) [REV_ASSOCD,MAP]
    \\ Cases_on `r = Tyvar s'` \\ FULL_SIMP_TAC std_ss [hol_ty_def]
    \\ SRW_TAC [] []
    \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [hol_ty_def,type_11]
    \\ `F` by ALL_TAC \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
    \\ SRW_TAC [] [type_distinct])
  \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [type_subst_def] \\ SIMP_TAC (srw_ss()) [LET_DEF]
  \\ SIMP_TAC std_ss [LET_DEF,prove(``(if x = y then f y else f x) = f x``,METIS_TAC[])]
  \\ Cases_on `l = []`
  THEN1 (FULL_SIMP_TAC std_ss [MAP,hol_ty_def] \\ SRW_TAC [] [TYPE_SUBST_def])
  \\ FULL_SIMP_TAC std_ss [TYPE_SUBST_def,type_11]
  \\ FULL_SIMP_TAC std_ss [TYPE_def,hol_ty_def,LENGTH_MAP,GSYM LENGTH_NIL]
  \\ FULL_SIMP_TAC std_ss [TYPE_SUBST_def,type_11]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``c /\ (c ==> b) ==> c /\ b``)
  \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [MAP_MAP_o,o_DEF] \\ MATCH_MP_TAC (GEN_ALL (snd (EQ_IMP_RULE (SPEC_ALL MAP_EQ_f))))
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM TYPE_SUBST_def]
  \\ MATCH_MP_TAC type_ok_TYPE_SUBST
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
  \\ REPEAT STRIP_TAC \\ RES_TAC);

val mk_fun_ty_thm = store_thm("mk_fun_ty_thm",
  ``!ty1 ty2 s z s'.
      STATE s defs /\ EVERY (TYPE defs) [ty1;ty2] /\
      (mk_fun_ty ty1 ty2 s = (z,s')) ==> (s' = s) /\
      ?i. (z = HolRes i) /\ (i = Tyapp "fun" [ty1;ty2]) /\ TYPE defs i``,
  SIMP_TAC std_ss [mk_fun_ty_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC mk_type_thm \\ FULL_SIMP_TAC (srw_ss()) []);

(* ------------------------------------------------------------------------- *)
(* Verification of term functions                                            *)
(* ------------------------------------------------------------------------- *)

val _ = temp_overload_on("aty",``(Tyvar "A"):hol_type``);
val _ = temp_overload_on("fun",``\x y. hol_kernel$Tyapp "fun" [x;y]``);
val _ = temp_overload_on("bool_ty",``hol_kernel$Tyapp "bool" []``);

val get_const_type_thm = prove(
  ``!name s z s'.
      (get_const_type name s = (z,s')) ==> (s' = s) /\
      (!i. (z = HolRes i) ==> MEM (name,i) s.the_term_constants) /\
      (!e. (z = HolErr e) ==> !i. ~(MEM (name,i) s.the_term_constants))``,
  SIMP_TAC (srw_ss()) [get_const_type_def,ex_bind_def,
    get_the_term_constants_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC assoc_thm);

val term_type_def = Define `
  term_type tm =
    case tm of
      Var _ ty => ty
    | Const _ ty => ty
    | Comb s _ => (case term_type s of Tyapp "fun" (_::ty1::_) => ty1
                                    | _ => Tyvar "")
    | Abs (Var _ ty) t => Tyapp "fun" [ty; term_type t]
    | _ => Tyvar ""`

val term_type = prove(
  ``!defs tm. CONTEXT defs ∧ TERM defs tm ==>
    (hol_ty (term_type tm) = typeof (hol_tm tm)) /\
                             TYPE defs (term_type tm)``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ STRIP_TAC \\ Induct \\ ONCE_REWRITE_TAC [term_type_def]
  \\ SIMP_TAC (srw_ss()) [hol_tm_def,typeof_def]
  \\ rw[] >> imp_res_tac TERM >> fs[] >>
  fs[TERM_def,term_ok_def,hol_tm_def] >> rfs[] >>
  Cases_on`term_type tm`>>fs[hol_ty_def]>>TRY(
    Cases_on`l`>>fs[]>>Cases_on`t`>>fs[]>>
    imp_res_tac TYPE >> fs[] >> NO_TAC) >>
  Cases_on`tm`>>fs[hol_tm_def,term_ok_impossible_term,hol_ty_def,term_ok_def] >>
  MATCH_MP_TAC TYPE_Fun >> rw[] >>
  Cases_on`h`>>fs[TYPE_def,hol_ty_def])

val type_of_thm = prove(
  ``!tm. TERM defs tm /\ STATE s defs ==>
         (type_of tm s = (HolRes (term_type tm),s))``,
  HO_MATCH_MP_TAC type_of_ind \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `CONTEXT defs` by fs[STATE_def]
  \\ Cases_on `tm` \\ ONCE_REWRITE_TAC [type_of_def]
  \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def,hol_tm_def,typeof_def]
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ TRY (FULL_SIMP_TAC (srw_ss()) [Once term_type_def] \\ NO_TAC)
  THEN1
   (ONCE_REWRITE_TAC [ex_bind_def]
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC (srw_ss()) []
    \\ ONCE_REWRITE_TAC [ex_bind_def]
    \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def]
    \\ REVERSE (`?ty1 ty2. term_type h = Tyapp "fun" [ty1;ty2]` by ALL_TAC) THEN1
     (FULL_SIMP_TAC (srw_ss()) [ex_return_def,hol_ty_def,codomain_def]
      \\ IMP_RES_TAC TYPE \\ ASM_SIMP_TAC (srw_ss()) [EVERY_DEF,Once term_type_def])
    \\ `hol_ty (term_type h) = typeof (hol_tm h)` by ALL_TAC
    THEN1 IMP_RES_TAC term_type
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [TERM_def,hol_tm_def,WELLTYPED_CLAUSES]
    \\ fs[term_ok_def] >>
    Cases_on`term_type h`>>fs[hol_ty_def]>>
    Cases_on`l`>>fs[]>>Cases_on`t`>>fs[])
  \\ IMP_RES_TAC Abs_Var \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC (srw_ss()) [Once term_type_def]
  \\ Cases_on `mk_fun_ty ty (term_type h0) s`
  \\ FULL_SIMP_TAC std_ss []
  \\ `EVERY (TYPE defs) [ty; term_type h0]` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [EVERY_DEF,term_type]
  \\ IMP_RES_TAC mk_fun_ty_thm
  \\ FULL_SIMP_TAC (srw_ss()) [ex_bind_def]);

val alphavars_thm = prove(
  ``!env.
      STATE s defs /\ TERM defs tm1 /\ TERM defs tm2 /\
      EVERY (\(v1,v2). TERM defs v1 /\ TERM defs v2) env ==>
      (alphavars env tm1 tm2 = ALPHAVARS
         (MAP (\(v1,v2). (hol_tm v1, hol_tm v2)) env) (hol_tm tm1, hol_tm tm2))``,
  Induct \\ SIMP_TAC (srw_ss()) [Once alphavars_def,ALPHAVARS_def]
  THEN1 METIS_TAC [TERM_11] \\ Cases \\ FULL_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC [TERM_11]);

val raconv_thm = prove(
  ``!tm1 tm2 env.
      STATE s defs /\ TERM defs tm1 /\ TERM defs tm2 /\
      EVERY (\(v1,v2). TERM defs v1 /\ TERM defs v2) env ==>
      (raconv env tm1 tm2 = RACONV
         (MAP (\(v1,v2). (hol_tm v1, hol_tm v2)) env) (hol_tm tm1, hol_tm tm2))``,
  Induct THEN1
   (REVERSE (Cases_on `tm2`) \\ ONCE_REWRITE_TAC [raconv_def]
    \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]
    THEN1 (Cases_on `h` \\ FULL_SIMP_TAC std_ss [RACONV,hol_tm_def])
    THEN1 (FULL_SIMP_TAC std_ss [RACONV,hol_tm_def])
    THEN1 (SRW_TAC [] [RACONV,hol_tm_def])
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC alphavars_thm
    \\ FULL_SIMP_TAC std_ss [hol_tm_def,RACONV])
  THEN1
   (Cases_on `tm2` \\ SIMP_TAC (srw_ss()) [Once raconv_def,hol_tm_def,RACONV]
    \\ SRW_TAC [] [RACONV,domain_def,hol_ty_def]
    \\ IMP_RES_TAC TERM
    \\ TRY (METIS_TAC [TYPE_11])
    \\ IMP_RES_TAC Abs_Var
    \\ FULL_SIMP_TAC (srw_ss()) [RACONV,domain_def,hol_ty_def,hol_tm_def])
  THEN1
   (Cases_on `tm2` \\ SIMP_TAC (srw_ss()) [Once raconv_def,hol_tm_def,RACONV]
    \\ SRW_TAC [] [RACONV] \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
    \\ imp_res_tac Abs_Var \\ simp[hol_tm_def,RACONV])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [hol_tm_def]
  \\ Cases_on `tm2` \\ SIMP_TAC (srw_ss()) [Once raconv_def,hol_tm_def,RACONV]
  \\ IMP_RES_TAC Abs_Var
  \\ SRW_TAC [] [RACONV,hol_tm_def]
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Abs (Var s4 ty4) t4)` []
  \\ Q.PAT_ASSUM `!tm2.bbb` (MP_TAC o Q.SPECL
        [`t4`,`((Var s' ty,Var s4 ty4)::env)`])
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
  \\ discharge_hyps
  THEN1 (REPEAT STRIP_TAC \\ MATCH_MP_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [MAP,hol_tm_def]
  \\ `(hol_ty ty = hol_ty ty4) = (ty = ty4)` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss [TYPE_11])

val aconv_thm = store_thm("aconv_thm",
  ``!tm1 tm2 env.
      STATE s defs /\ TERM defs tm1 /\ TERM defs tm2 ==>
      (aconv tm1 tm2 = ACONV (hol_tm tm1) (hol_tm tm2))``,
  SIMP_TAC std_ss [aconv_def,ACONV_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (raconv_thm |> Q.SPECL [`t1`,`t2`,`[]`]
       |> SIMP_RULE std_ss [EVERY_DEF,MAP])
  \\ FULL_SIMP_TAC std_ss []);

val is_term_thm = store_thm("is_term_thm",
  ``(is_var tm = ?n ty. tm = Var n ty) /\
    (is_const tm = ?n ty. tm = Const n ty) /\
    (is_abs tm = ?v x. tm = Abs v x) /\
    (is_comb tm = ?x y. tm = Comb x y)``,
  Cases_on `tm` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val mk_var_thm = store_thm("mk_var_thm",
  ``STATE s defs /\ TYPE defs ty ==> TERM defs (mk_var(v,ty))``,
  SIMP_TAC std_ss [mk_var_def] \\ METIS_TAC [TERM_Var]);

val mk_abs_thm = store_thm("mk_abs_thm",
  ``!res.
      TERM defs bvar /\ TERM defs bod /\ (mk_abs(bvar,bod) s = (res,s1)) ==>
      (s1 = s) /\ !t. (res = HolRes t) ==> TERM defs t /\ (t = Abs bvar bod)``,
  FULL_SIMP_TAC std_ss [mk_abs_def] \\ Cases_on `bvar`
  \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def,failwith_def,IMP_TERM_Abs]);

val mk_comb_thm = prove(
  ``TERM defs f /\ TERM defs a /\ STATE s defs /\
    (mk_comb(f,a)s = (res,s1)) ==>
    (s1 = s) /\
    (!t. (res = HolErr t) ==> !ty. term_type f <> fun (term_type a) ty) /\
    !t. (res = HolRes t) ==> TERM defs t /\ (t = Comb f a)``,
  SIMP_TAC std_ss [mk_comb_def,ex_bind_def] \\ STRIP_TAC
  \\ MP_TAC (type_of_thm |> SIMP_RULE std_ss [] |> Q.SPEC `f`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ MP_TAC (type_of_thm |> SIMP_RULE std_ss [] |> Q.SPEC `a`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.PAT_ASSUM `xxx = (res,s1)` (ASSUME_TAC o GSYM)
  \\ Cases_on `term_type f` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ FULL_SIMP_TAC (srw_ss()) [failwith_def,ex_return_def]
  \\ IMP_RES_TAC term_type
  \\ IMP_RES_TAC type_of_thm
  \\ FULL_SIMP_TAC (srw_ss()) [TYPE_def]
  \\ Q.PAT_ASSUM `term_type f = fun h h'` ASSUME_TAC
  \\ Q.PAT_ASSUM `term_type a = h` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [hol_ty_def,MAP]
  \\ METIS_TAC [IMP_TERM_Comb,STATE_def]);

val dest_var_thm = store_thm("dest_var_thm",
  ``TERM defs v /\ STATE s defs ==>
    (dest_var v s = (res,s')) ==>
    (s' = s) /\ !n ty. (res = HolRes (n,ty)) ==> TYPE defs ty``,
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [hol_kernelTheory.dest_var_def,ex_return_def,Once EQ_SYM_EQ,failwith_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM);

val dest_const_thm = store_thm("dest_const_thm",
  ``TERM defs v /\ STATE s defs ==>
    (dest_const v s = (res,s')) ==>
    (s' = s) /\ !n ty. (res = HolRes (n,ty)) ==> TYPE defs ty``,
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [dest_const_def,ex_return_def,Once EQ_SYM_EQ,failwith_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM);

val dest_comb_thm = store_thm("dest_comb_thm",
  ``TERM defs v /\ STATE s defs ==>
    (dest_comb v s = (res,s')) ==>
    (s' = s) /\ !x y. (res = HolRes (x,y)) ==> TERM defs x /\ TERM defs y``,
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [dest_comb_def,ex_return_def,Once EQ_SYM_EQ,failwith_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM);

val dest_abs_thm = store_thm("dest_abs_thm",
  ``TERM defs v /\ STATE s defs ==>
    (dest_abs v s = (res,s')) ==>
    (s' = s) /\ !x y. (res = HolRes (x,y)) ==> TERM defs x /\ TERM defs y``,
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [dest_abs_def,ex_return_def,Once EQ_SYM_EQ,failwith_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC TERM
  \\ IMP_RES_TAC TERM_Var \\ FULL_SIMP_TAC std_ss []);

val rator_thm = store_thm("rator_thm",
  ``TERM defs v /\ STATE s defs ==>
    (rator v s = (res,s')) ==>
    (s' = s) /\ !x. (res = HolRes x) ==> TERM defs x``,
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [rator_def,ex_return_def,Once EQ_SYM_EQ,failwith_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM);

val rand_thm = store_thm("rand_thm",
  ``TERM defs v /\ STATE s defs ==>
    (rand v s = (res,s')) ==>
    (s' = s) /\ !x. (res = HolRes x) ==> TERM defs x``,
  Cases_on `v`
  \\ SIMP_TAC (srw_ss()) [rand_def,ex_return_def,Once EQ_SYM_EQ,failwith_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM);

val type_subst_bool = prove(
  ``type_subst i bool_ty = bool_ty``,
  SIMP_TAC (srw_ss()) [Once type_subst_def,LET_DEF]);

val type_subst_fun = prove(
  ``type_subst i (fun ty1 ty2) = fun (type_subst i ty1) (type_subst i ty2)``,
  SIMP_TAC (srw_ss()) [Once type_subst_def,LET_DEF] \\ SRW_TAC [] []);

val TERM_Const = prove(
  ``STATE r defs /\ MEM (name,a) r.the_term_constants ==>
    TERM defs (Const name a)``,
  rw[STATE_def,TERM_def,hol_tm_def,term_ok_def] >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  qpat_assum`X = Y`(ASSUME_TAC o SYM) >>
  simp[ALOOKUP_MAP] >>
  qpat_assum`ALL_DISTINCT X`mp_tac >>
  simp[Once MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  strip_tac >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  simp[] >>
  fs[CONTEXT_def] >>
  imp_res_tac extends_theory_ok >> fs[init_theory_ok] >>
  fs[theory_ok_def] >> first_x_assum MATCH_MP_TAC >>
  MATCH_MP_TAC ALOOKUP_IN_FRANGE >>
  simp[ALOOKUP_MAP] >> METIS_TAC[])

val TERM_Const_type_subst = prove(
  ``EVERY (\(x,y). TYPE defs x /\ TYPE defs y) theta /\
    TERM defs (Const name a) ==> TERM defs (Const name (type_subst theta a))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
  \\ IMP_RES_TAC type_subst_thm
  \\ FULL_SIMP_TAC std_ss [type_subst_thm,TERM_def,hol_tm_def,TYPE_def] >>
  fs[term_ok_def] >>
  conj_tac >- (
    match_mp_tac type_ok_TYPE_SUBST >>
    rfs[EVERY_MAP,EVERY_MEM,FORALL_PROD] >>
    METIS_TAC[] ) >>
  simp[TYPE_SUBST_compose] >>
  METIS_TAC[])

val mk_const_thm = store_thm("mk_const_thm",
  ``!name theta s z s'.
      STATE s defs /\ EVERY (\(x,y). TYPE defs x /\ TYPE defs y) theta /\
      (mk_const (name,theta) s = (z,s')) ==> (s' = s) /\
      !i. (z = HolRes i) ==> TERM defs i``,
  SIMP_TAC std_ss [mk_const_def,try_def,ex_bind_def,otherwise_def]
  \\ NTAC 3 STRIP_TAC \\ Cases_on `get_const_type name s`
  \\ IMP_RES_TAC get_const_type_thm
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def,ex_return_def]
  \\ SRW_TAC [] [ex_return_def]
  \\ MATCH_MP_TAC TERM_Const_type_subst \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC get_const_type_thm \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC TERM_Const);

val get_const_type_Equal = prove(
  ``STATE s defs ==>
    (get_const_type "=" s = (HolRes (fun aty (fun aty bool_ty)),s))``,
  SIMP_TAC std_ss [STATE_def]
  \\ Cases_on `get_const_type "=" s`
  \\ IMP_RES_TAC get_const_type_thm \\ REPEAT STRIP_TAC >>
  imp_res_tac CONTEXT_std_sig >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  qpat_assum`X = Y`(ASSUME_TAC o SYM) >>
  fs[is_std_sig_def] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >>
  reverse(Cases_on`q`)>>fs[]>-METIS_TAC[]>>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  rfs[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  Cases_on`a`>>fs[hol_ty_def]>>
  Cases_on`l`>>fs[hol_ty_def]>>
  Cases_on`h`>>fs[hol_ty_def]>>
  Cases_on`t`>>fs[hol_ty_def]>>
  Cases_on`h`>>fs[hol_ty_def]>>
  Cases_on`l`>>fs[hol_ty_def]>>
  Cases_on`h`>>fs[hol_ty_def]>>
  Cases_on`t`>>fs[hol_ty_def]>>
  Cases_on`h`>>fs[hol_ty_def])

(*
val get_const_type_Select = prove(
  ``STATE s defs ==>
    (get_const_type "@" s = (HolRes (fun (fun aty bool_ty) aty),s))``,
  SIMP_TAC std_ss [STATE_def]
  \\ Cases_on `get_const_type "@" s`
  \\ IMP_RES_TAC get_const_type_thm \\ REPEAT STRIP_TAC
  \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FULL_SIMP_TAC std_ss [consts_def]
    \\ `?x. MEM ("@",x) (MAP (\(name,ty). (name,hol_ty ty))
        s.the_term_constants)` by ALL_TAC THEN1
     (POP_ASSUM (ASSUME_TAC o GSYM) \\ ASM_SIMP_TAC std_ss []
      \\ SRW_TAC [] [] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [MEM_MAP] \\ Cases_on `y`
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [consts_def] >>
  `!a. ~MEM ("@",a) (FLAT (MAP consts_aux (hol_defs defs)))` by (
    qx_gen_tac`z` >>
    spose_not_then STRIP_ASSUME_TAC >>
    qmatch_assum_abbrev_tac`l1 ++ l2 = MAP f l3` >>
    `MAP FST l3 = MAP FST (MAP f l3)` by (
      simp[Abbr`f`,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_pair] ) >>
    `ALL_DISTINCT (MAP FST (l1 ++ l2))` by METIS_TAC[] >>
    fs[ALL_DISTINCT_APPEND] >>
    pop_assum(qspec_then`"@"`mp_tac) >>
    simp[MEM_MAP,EXISTS_PROD,Abbr`l2`] >>
    METIS_TAC[] ) >>
  qsuff_tac`hol_ty a = typeof (Select α)` >- (
    simp[] >>
    Cases_on`a`>>simp[hol_ty_def] >>
    Cases_on`l`>>simp[]>>
    Cases_on`h`>>simp[hol_ty_def]>>
    Cases_on`t`>>simp[]>>
    Cases_on`h`>>simp[hol_ty_def]>>
    Cases_on`l`>>simp[]>>
    Cases_on`h`>>simp[hol_ty_def]>>
    Cases_on`t`>>simp[]>>
    Cases_on`h`>>simp[hol_ty_def]) >>
  qmatch_assum_abbrev_tac`l1 ++ l2 = MAP f l3` >>
  `MEM ("@",hol_ty a) (l1 ++ l2)` by (
    asm_simp_tac std_ss [] >>
    simp[MEM_MAP,Abbr`f`,EXISTS_PROD] >>
    METIS_TAC[] ) >>
  fs[Abbr`l2`] >>
  METIS_TAC[]);
*)

val mk_const_eq = prove(
  ``STATE s defs ==>
    (mk_const ("=",[]) s =
     (HolRes (Const "=" (fun aty (fun aty bool_ty))),s))``,
  SIMP_TAC std_ss [mk_const_def,ex_bind_def,try_def,otherwise_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC get_const_type_Equal
  \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ EVAL_TAC);

val mk_eq_lemma = prove(
  ``inst [(term_type x,aty)] (Const "=" (fun aty (fun aty bool_ty))) s =
    ex_return
        (Const "="
           (fun (term_type x) (fun (term_type x) bool_ty))) s``,
  SIMP_TAC (srw_ss()) [inst_def,inst_aux_def,LET_DEF]
  \\ NTAC 50 (SIMP_TAC (srw_ss()) [Once type_subst_def,LET_DEF,mk_vartype_def,
       rev_assocd_def]) \\ SRW_TAC [] [] \\ METIS_TAC []);

val mk_eq_thm = store_thm("mk_eq_thm",
  ``TERM defs x /\ TERM defs y /\ STATE s defs ==>
    (mk_eq(x,y)s = (res,s')) ==>
    (s' = s) /\
    (!t. (res = HolErr t) ==> ((term_type x) <> (term_type y))) /\
    !t. (res = HolRes t) ==>
    (t = Comb (Comb (Const "=" (fun (term_type x)
                               (fun (term_type x) bool_ty))) x) y) /\
    TERM defs t``,
  STRIP_TAC \\ SIMP_TAC std_ss [mk_eq_def,try_def,ex_bind_def,
    otherwise_def,mk_vartype_def]
  \\ `CONTEXT defs` by fs[STATE_def]
  \\ MP_TAC (type_of_thm |> SIMP_RULE std_ss [] |> Q.SPEC `x`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC mk_const_eq \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [mk_eq_lemma,ex_return_def]
  \\ Cases_on `mk_comb (Const "=" (fun (term_type x)
                                  (fun (term_type x) bool_ty)),x) s`
  \\ `TERM defs (Const "=" (fun (term_type x)
                           (fun (term_type x) bool_ty)))` by ALL_TAC THEN1
   (IMP_RES_TAC term_type >>
    IMP_RES_TAC CONTEXT_std_sig
    \\ FULL_SIMP_TAC (srw_ss()) [TERM_def,hol_tm_def,hol_ty_def] >>
    simp[term_ok_def] >> fs[is_std_sig_def,type_ok_def,TYPE_def] >>
    rfs[] >>
    qexists_tac`[(typeof (hol_tm x),Tyvar"A")]` >>
    simp[REV_ASSOCD] )
  \\ Q.ABBREV_TAC `eq = (Const "=" (fun (term_type x) (fun (term_type x) bool_ty)))`
  \\ MP_TAC (mk_comb_thm |> Q.INST [`f`|->`eq`,`a`|->`x`,`res`|->`q`,`s1`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) [failwith_def] THEN1
   (Q.UNABBREV_TAC `eq` \\ FULL_SIMP_TAC std_ss [mk_comb_def,ex_bind_def]
    \\ IMP_RES_TAC (Q.SPEC `y` type_of_thm)
    \\ Q.PAT_ASSUM `type_of x s = (HolRes (term_type x),s)` ASSUME_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``term_type (Const "=" ty)``,ex_return_def])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `mk_comb (Comb eq x,y) s`
  \\ MP_TAC (mk_comb_thm |> Q.INST [`f`|->`Comb eq x`,`a`|->`y`,
      `res`|->`q`,`s1`|->`r'`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.UNABBREV_TAC `eq` \\ FULL_SIMP_TAC std_ss [mk_comb_def,ex_bind_def]
  \\ IMP_RES_TAC (Q.SPEC `y` type_of_thm)
  \\ Q.PAT_ASSUM `type_of x s = (HolRes (term_type x),s)` ASSUME_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``term_type (Const "=" ty)``,ex_return_def,
         ``term_type (Comb x y)`` |> SIMP_CONV (srw_ss()) [Once term_type_def],
         ``type_of (Comb x y)`` |> SIMP_CONV (srw_ss()) [Once type_of_def],
         ``type_of (Const x y)`` |> SIMP_CONV (srw_ss()) [Once type_of_def],
         ex_bind_def,dest_type_def]);

val TERM_Eq_x = prove(
  ``STATE s defs /\ TERM defs (Comb (Const "=" ty) x) ==>
    (Fun (typeof (hol_tm x)) (Fun (typeof (hol_tm x)) Bool) = hol_ty ty)``,
  rw[TERM_def,STATE_def,hol_tm_def] >>
  fs[term_ok_def] >>
  imp_res_tac CONTEXT_std_sig >>
  fs[is_std_sig_def] >> rw[] >>
  fs[TYPE_SUBST_def])

val TERM_Comb = prove(
  ``CONTEXT defs ⇒
    (TERM defs (Comb f a) <=>
     TERM defs f /\ TERM defs a /\
     ?ty. hol_ty (term_type f) = Fun (hol_ty (term_type a)) ty)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC term_type
  \\ FULL_SIMP_TAC std_ss [TERM_def,WELLTYPED_CLAUSES,hol_tm_def,type_11,term_ok_def]
  \\ METIS_TAC[term_ok_welltyped])

val MAP_EQ_2 = prove(
  ``(MAP f l = [x;y]) ⇔ ∃x0 y0. (l = [x0;y0]) ∧ (x = f x0) ∧ (y = f y0)``,
  Cases_on`l`>>simp[]>>Cases_on`t`>>simp[]>>METIS_TAC[])

val MAP_EQ_2_SYM = prove(
  ``([x;y] = MAP f l) ⇔ (MAP f l = [x;y])``,METIS_TAC[])

val MAP_TYPE_11 = prove(
  ``(MAP hol_ty l = MAP hol_ty r) ⇔ (l = r)``,
  EQ_TAC >> simp[] >> strip_tac >>
  match_mp_tac (MP_CANON (Q.ISPEC`hol_ty`(Q.GEN`f`(SPEC_ALL MAP_EQ_MAP_IMP)))) >>
  simp[TYPE_11])

val Equal_type = prove(
  ``STATE s defs ∧ TERM defs (Const "=" ty) ==> ?a. ty = fun a (fun a bool_ty)``,
  rw[STATE_def,TERM_def,hol_tm_def] >>
  imp_res_tac CONTEXT_std_sig >>
  fs[is_std_sig_def,term_ok_def] >>
  Cases_on`ty`>>fs[hol_ty_def,MAP_EQ_2]>>
  rpt(
    (qmatch_assum_abbrev_tac`X = hol_ty Y` ORELSE
     qmatch_assum_abbrev_tac`hol_ty Y = X`) >>
    qunabbrev_tac`X`>>
    Cases_on`Y`>>fs[markerTheory.Abbrev_def,hol_ty_def,MAP_EQ_2,MAP_EQ_2_SYM] >>
    rpt BasicProvers.VAR_EQ_TAC) >>
  fs[ETA_AX,MAP_TYPE_11])

val Equal_type_IMP = prove(
  ``STATE s defs ∧ TERM defs (Comb (Const "=" (fun a' (fun a' bool_ty))) ll) ==>
    (typeof (hol_tm ll) = (hol_ty a'))``,
  simp[TERM_Comb] >> strip_tac >>
  imp_res_tac TERM_Eq_x >>
  fs[Once term_type_def] >>
  fs[hol_ty_def] >>
  rw[] >> imp_res_tac term_type >> simp[])

val dest_eq_thm = store_thm("dest_eq_thm",
  ``TERM defs tm /\ STATE s defs /\ (dest_eq tm s = (res, s')) ==>
    (s' = s) /\ !t1 t2. (res = HolRes (t1,t2)) ==> TERM defs t1 /\ TERM defs t2 /\
    (hol_tm tm = Comb (Comb (Equal (typeof (hol_tm t1))) (hol_tm t1)) (hol_tm t2))``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [dest_eq_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [failwith_def,ex_return_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [hol_tm_def]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC TERM_Eq_x);

val MEM_term_union = prove(
  ``!l1 l2 x. MEM x (term_union l1 l2) ==> MEM x l1 \/ MEM x l2``,
  Induct \\ ONCE_REWRITE_TAC [term_union_def] \\ SIMP_TAC (srw_ss()) [LET_DEF]
  \\ SRW_TAC [] [] \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val term_union_thm = prove(
  ``!l l'.
      EVERY (TERM defs) l /\ EVERY (TERM defs) l' /\ STATE s defs ==>
      (MAP hol_tm (term_union l l') = TERM_UNION (MAP hol_tm l) (MAP hol_tm l'))``,
  Induct \\ SIMP_TAC (srw_ss()) [TERM_UNION_def,MAP,Once term_union_def,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `EXISTS (aconv h) (term_union l l') =
      EXISTS (ACONV (hol_tm h)) (TERM_UNION (MAP hol_tm l) (MAP hol_tm l'))` by
        ALL_TAC THEN1
   (RES_TAC \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once (GSYM th)])
    \\ SIMP_TAC std_ss [EXISTS_MEM,MEM_MAP,PULL_EXISTS]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC MEM_term_union
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ RES_TAC
    \\ METIS_TAC [aconv_thm])
  \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] []);

val vfree_in_thm = prove(
  ``!y. TERM defs y /\ TYPE defs ty /\ STATE s defs ==>
        (VFREE_IN (Var name (hol_ty ty)) (hol_tm y) = vfree_in (Var name ty) y)``,
  Induct THEN1
   (FULL_SIMP_TAC std_ss [VFREE_IN_def,hol_tm_def,term_11]
    \\ ONCE_REWRITE_TAC [vfree_in_def] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
    \\ METIS_TAC [TYPE_11])
  THEN1
   (FULL_SIMP_TAC std_ss [VFREE_IN_def,hol_tm_def,term_11] \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC std_ss [VFREE_IN_def,hol_tm_def,term_11,term_distinct]
    \\ ONCE_REWRITE_TAC [vfree_in_def] \\ SIMP_TAC (srw_ss()) [])
  THEN1
   (REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def] \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once vfree_in_def])
  THEN1
   (REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def] \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once vfree_in_def]
    \\ IMP_RES_TAC Abs_Var
    \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def,VFREE_IN_def,term_11]
    \\ IMP_RES_TAC TERM
    \\ FULL_SIMP_TAC std_ss []
    \\ METIS_TAC [TYPE_11]));

val VFREE_IN_IMP = prove(
  ``!y. TERM defs y /\ TYPE defs ty /\ STATE s defs /\
        VFREE_IN (Var name (hol_ty ty)) (hol_tm y) ==>
        vfree_in (Var name ty) y``,
  METIS_TAC [vfree_in_thm]);

val SELECT_LEMMA = prove(
  ``(@f. !s s'. f (s',s) <=> s <> t) = (\(z,y). y <> t)``,
  Q.ABBREV_TAC `p = (@f. !s s'. f (s',s) <=> s <> t)`
  \\ `?f. !s s'. f (s',s) <=> s <> t` by ALL_TAC
  THEN1 (Q.EXISTS_TAC `(\(z,y). y <> t)` \\ FULL_SIMP_TAC std_ss [])
  \\ `!s s'. p (s',s) <=> s <> t` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD]);

val SELECT_LEMMA2 = prove(
  ``(@f.
       !s s''.
         f (s'',s) <=>
         VFREE_IN (Var s' (hol_ty ty)) s'' /\ VFREE_IN s (hol_tm tm')) =
    (\(x,y). VFREE_IN (Var s' (hol_ty ty)) x /\ VFREE_IN y (hol_tm tm'))``,
  Q.ABBREV_TAC `p = (@f. !s s''. f (s'',s) <=>
         VFREE_IN (Var s' (hol_ty ty)) s'' /\ VFREE_IN s (hol_tm tm'))`
  \\ `?f. !s s''. f (s'',s) <=>
         VFREE_IN (Var s' (hol_ty ty)) s'' /\ VFREE_IN s (hol_tm tm')` by ALL_TAC
  THEN1 (Q.EXISTS_TAC `(\(s'',s). VFREE_IN (Var s' (hol_ty ty)) s'' /\
                VFREE_IN s (hol_tm tm'))` \\ FULL_SIMP_TAC std_ss [])
  \\ `!s s''. p (s'',s) <=> VFREE_IN (Var s' (hol_ty ty)) s'' /\
                            VFREE_IN s (hol_tm tm')` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD]);

val is_var_thm = prove(
  ``!x. is_var x = ?v ty. x = Var v ty``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [is_var_def]);

val VSUBST_EMPTY = prove(
  ``(!tm. holSyntax$VSUBST [] tm = tm)``,
  Induct
  \\ FULL_SIMP_TAC (srw_ss()) [VSUBST_def,REV_ASSOCD,EVERY_DEF,FILTER,LET_THM]);

val REPLICATE_GENLIST = store_thm("REPLICATE_GENLIST",
  ``!n. REPLICATE n x = GENLIST (K x) n``,
  Induct THEN SRW_TAC[][rich_listTheory.REPLICATE,GENLIST_CONS])

val variant_thm = prove(
  ``!xs v x name.
      TERM defs x /\ TYPE defs ty /\ STATE s defs /\
      (xs = [x]) /\ (v = (Var name ty)) ==>
      (variant xs (Var name ty) =
       Var (VARIANT (hol_tm x) name (hol_ty ty)) ty)``,
  REWRITE_TAC [VARIANT_def] \\ HO_MATCH_MP_TAC variant_ind
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
  \\ MP_TAC (Q.SPEC `x` vfree_in_thm) \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [EXISTS_DEF]
  \\ REVERSE (Cases_on `vfree_in (Var name ty) x`)
  \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`hol_tm x`,`name`,`hol_ty ty`])
    \\ Cases_on `VARIANT_PRIMES (hol_tm x) name (hol_ty ty)`
    THEN1 FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE])
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`hol_tm x`,`name`,`hol_ty ty`])
  \\ Cases_on `VARIANT_PRIMES (hol_tm x) name (hol_ty ty)`
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE]
  \\ REPEAT STRIP_TAC
  \\ `!m. m < n ==>
         VFREE_IN (Var (STRCAT name (REPLICATE (SUC m) #"'")) (hol_ty ty))
           (hol_tm x)` by ALL_TAC
  THEN1 (REPEAT STRIP_TAC \\ `SUC m < SUC n` by DECIDE_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [REPLICATE_GENLIST])
  \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE_GENLIST,GENLIST_CONS]
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`hol_tm x`,`STRCAT name "'"`,`hol_ty ty`])
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ Cases_on `VARIANT_PRIMES (hol_tm x) (STRCAT name "'") (hol_ty ty) = n`
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `VARIANT_PRIMES (hol_tm x) (STRCAT name "'") (hol_ty ty) < n \/
      n < VARIANT_PRIMES (hol_tm x) (STRCAT name "'") (hol_ty ty)` by DECIDE_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

val REPLICATE_11 = prove(
  ``!m n x. (REPLICATE n x = REPLICATE m x) = (m = n)``,
  Induct \\ Cases \\ SRW_TAC [] [rich_listTheory.REPLICATE]);

val EXISTS_union = prove(
  ``!xs ys. EXISTS P (union xs ys) <=> EXISTS P xs \/ EXISTS P ys``,
  SIMP_TAC std_ss [EXISTS_MEM,MEM_MAP,MEM_union] \\ METIS_TAC []);

val VFREE_IN_TYPE = prove(
  ``!x. VFREE_IN (Var name oty) (hol_tm x) /\ TERM defs x ==>
        ?ty. (oty = hol_ty ty) /\ TYPE defs ty``,
  Induct
  THEN1 (SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def,term_11] \\ METIS_TAC [TERM])
  THEN1 (SRW_TAC [] [hol_tm_def,VFREE_IN_def,term_11,term_distinct])
  THEN1 (SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def,term_11]
         \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def,term_11] \\ STRIP_TAC
  \\ IMP_RES_TAC Abs_Var \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def] \\ METIS_TAC []);

val VFREE_IN_IMP_MEM = prove(
  ``VFREE_IN (Var name oty) (hol_tm h0) /\ TERM defs h0 /\ STATE s defs ==>
    ?ty1. MEM (Var name ty1) (frees h0) /\ (oty = hol_ty ty1) /\ TYPE defs ty1``,
  Induct_on `h0` THEN1 (Q.SPEC_TAC (`oty`,`oty`)
    \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def,VFREE_IN_def,term_11,Once frees_def]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [])
  THEN1 (SRW_TAC [] [hol_tm_def,VFREE_IN_def,term_11,Once frees_def,term_distinct])
  THEN1 (SIMP_TAC (srw_ss()) [Once frees_def,MEM_union,hol_tm_def,VFREE_IN_def]
         \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC) \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def]
  \\ SIMP_TAC (srw_ss()) [Once frees_def,MEM_union,hol_tm_def,VFREE_IN_def]
  \\ SIMP_TAC (srw_ss()) [subtract_def,MEM_FILTER]
  \\ IMP_RES_TAC VFREE_IN_TYPE \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `ty1` \\ FULL_SIMP_TAC std_ss [term_11]
  \\ DISJ2_TAC \\ REPEAT STRIP_TAC
  \\ METIS_TAC [TYPE_11]);

val MEM_frees_EQ = prove(
  ``!a x. MEM x (frees a) = ?n ty. (x = Var n ty) /\ MEM (Var n ty) (frees a)``,
  Induct \\ SIMP_TAC (srw_ss()) [Once frees_def,MEM_union]
  THEN1 (SIMP_TAC (srw_ss()) [Once frees_def,MEM_union])
  THEN1 (SIMP_TAC (srw_ss()) [Once frees_def,MEM_union])
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC (srw_ss()) [Once frees_def,MEM_union] THEN1 (METIS_TAC [])
  \\ SIMP_TAC (srw_ss()) [subtract_def,MEM_FILTER]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val variant_alt = prove(
  ``!xs v x name a.
      TERM defs a /\ TYPE defs (type_subst theta ty) /\ STATE s defs /\
      (xs = frees a) /\
      (v = (Var name (type_subst theta ty))) ==>
      (variant (frees a) (Var name (type_subst theta ty)) =
       Var (VARIANT (hol_tm a) name (hol_ty (type_subst theta ty)))
              (type_subst theta ty))``,
  REWRITE_TAC [VARIANT_def] \\ HO_MATCH_MP_TAC variant_ind
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
  \\ Q.ABBREV_TAC `ty1 = type_subst theta ty` \\ POP_ASSUM (K ALL_TAC)
  \\ `EXISTS (vfree_in (Var name ty1)) (frees a) =
      VFREE_IN (Var name (hol_ty ty1)) (hol_tm a)` by ALL_TAC THEN1
   (Q.PAT_ASSUM `TERM defs a` MP_TAC \\ Q.PAT_ASSUM `TYPE defs ty1` MP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `STATE st defs` []
    \\ Q.PAT_ASSUM `STATE st defs` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `a` \\ SIMP_TAC (srw_ss()) [Once frees_def,Once vfree_in_def]
    THEN1 (FULL_SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def,term_11]
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ METIS_TAC [TYPE_11])
    THEN1 (SRW_TAC [] [hol_tm_def,VFREE_IN_def,term_11,term_distinct])
    THEN1 (REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
      \\ FULL_SIMP_TAC std_ss [EXISTS_union,hol_tm_def,VFREE_IN_def])
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [hol_tm_def,VFREE_IN_def]
    \\ FIRST_X_ASSUM (fn th => FULL_SIMP_TAC std_ss [SYM th])
    \\ FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,subtract_def,MEM_FILTER,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC [MEM_frees_EQ]
    \\ FULL_SIMP_TAC std_ss [term_11,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC [vfree_in_def] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ METIS_TAC [TYPE_11])
  \\ FULL_SIMP_TAC std_ss []
  \\ REVERSE (Cases_on `VFREE_IN (Var name (hol_ty ty1)) (hol_tm a)`) THEN1
   (MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`hol_tm a`,`name`,`hol_ty ty1`])
    \\ Cases_on `VARIANT_PRIMES (hol_tm a) name (hol_ty ty1)`
    THEN1 FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE])
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`hol_tm a`,`name`,`hol_ty ty1`])
  \\ Cases_on `VARIANT_PRIMES (hol_tm a) name (hol_ty ty1)`
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.GEN `m` o SIMP_RULE std_ss [] o Q.SPEC `SUC m`)
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`hol_tm a`,`STRCAT name "'"`,`hol_ty ty1`])
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ Q.ABBREV_TAC `k = VARIANT_PRIMES (hol_tm a) (STRCAT name "'") (hol_ty ty1)`
  \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE_GENLIST,GENLIST_CONS]
  \\ Cases_on `k = n` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `k < n \/ n < k` by DECIDE_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

val term_type_Var = prove(
  ``term_type (Var v ty) = ty``,
  SIMP_TAC (srw_ss()) [Once term_type_def]);

val vsubst_aux_thm = prove(
  ``!t tm theta. EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2 /\
                     (term_type t1 = term_type t2) /\ is_var t2) theta /\
    TERM defs tm /\ STATE s defs /\
    (vsubst_aux theta tm = t) ==>
    TERM defs t /\
    (hol_tm t = VSUBST (MAP (\(t1,t2). (hol_tm t1, hol_tm t2)) theta) (hol_tm tm))``,
  SIMP_TAC std_ss [] \\ Induct THEN1
   (NTAC 4 STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once vsubst_aux_def]
    \\ SIMP_TAC (srw_ss()) [Once vsubst_aux_def,VSUBST_def,hol_tm_def]
    \\ Induct_on `theta` \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [rev_assocd_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVERY_DEF,REV_ASSOCD,hol_tm_def]
    \\ Cases \\ FULL_SIMP_TAC (srw_ss()) [REV_ASSOCD_def]
    \\ Cases_on `r = Var s' h` \\ FULL_SIMP_TAC std_ss []
    THEN1 (FULL_SIMP_TAC std_ss [hol_tm_def])
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [] \\ METIS_TAC [TERM_11,hol_tm_def])
  THEN1
   (NTAC 4 STRIP_TAC \\ SIMP_TAC (srw_ss()) [Once vsubst_aux_def]
    \\ SIMP_TAC (srw_ss()) [Once vsubst_aux_def,VSUBST_def,hol_tm_def]
    \\ SRW_TAC [] [VSUBST_def])
  THEN1
   (STRIP_TAC \\ REPEAT (Q.PAT_ASSUM `!theta. bbb` (ASSUME_TAC o SPEC_ALL))
    \\ ONCE_REWRITE_TAC [vsubst_aux_def] \\ SIMP_TAC (srw_ss()) [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [hol_tm_def,VSUBST_def,term_11]
    \\ REVERSE (REPEAT STRIP_TAC)
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [TERM_def,term_ok_def,hol_tm_def]
    \\ SIMP_TAC std_ss [GSYM VSUBST_def]
    \\ MATCH_MP_TAC VSUBST_WELLTYPED
    \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS,FORALL_PROD,EVERY_MEM]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [is_var_thm]
    \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def,term_11]
    \\ FULL_SIMP_TAC std_ss [EVAL ``term_type (Var v ty)``]
    \\ rw[]
    \\ fs[STATE_def]
    \\ IMP_RES_TAC (REWRITE_RULE [TERM_def] term_type)
    \\ METIS_TAC[WELLTYPED,term_ok_welltyped])
  \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [vsubst_aux_def] \\ SIMP_TAC (srw_ss()) [LET_DEF]
  \\ STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC (srw_ss()) [is_var_def,hol_tm_def]
  \\ Cases_on `FILTER (\(t,x). x <> Var s' ty) theta = []`
  \\ FULL_SIMP_TAC std_ss [hol_tm_def] THEN1
   (SIMP_TAC std_ss [REWRITE_RULE[SELECT_LEMMA]VSUBST_def,LET_THM]
    \\ `(FILTER (\(z,y). y <> Var s' (hol_ty ty))
         (MAP (\(t1,t2). (hol_tm t1,hol_tm t2)) theta)) = []` by ALL_TAC THEN1
     (POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Induct_on `theta` \\ FULL_SIMP_TAC std_ss [MAP,FILTER]
      \\ Cases \\ FULL_SIMP_TAC std_ss [MAP,FILTER]
      \\ Cases_on `r = Var s' ty` \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def])
    \\ FULL_SIMP_TAC (srw_ss()) [VSUBST_EMPTY])
  (*
  \\ SIMP_TAC std_ss [SELECT_LEMMA2]
  \\ `EXISTS
       (@f.
          !s s''.
            f (s'',s) <=>
            VFREE_IN (Var s' (hol_ty ty)) s'' /\ VFREE_IN s (hol_tm tm'))
       (FILTER (\(z,y). y <> Var s' (hol_ty ty))
          (MAP (\(t1,t2). (hol_tm t1,hol_tm t2)) theta)) =
      EXISTS (\(t,x). vfree_in (Var s' ty) t /\ vfree_in x tm')
        (FILTER (\(t,x). x <> Var s' ty) theta)` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [SELECT_LEMMA2,EXISTS_MEM,MEM_FILTER,MEM_MAP,
      PULL_EXISTS,EXISTS_PROD,EVERY_MEM,FORALL_PROD] \\ REPEAT STRIP_TAC
    \\ EQ_TAC \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
     (Cases_on `p_2'` \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]
      \\ Q.MATCH_ASSUM_RENAME_TAC `MEM (pp,Var nn h1) theta` []
      \\ Q.LIST_EXISTS_TAC [`pp`,`Var nn h1`]
      \\ IMP_RES_TAC TERM \\ IMP_RES_TAC TYPE \\ IMP_RES_TAC vfree_in_thm
      \\ FULL_SIMP_TAC (srw_ss()) [term_11] \\ METIS_TAC [TYPE_11])
    \\ Cases_on `p_2` \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]
    \\ Q.MATCH_ASSUM_RENAME_TAC `MEM (pp,Var nn h1) theta` []
    \\ Q.LIST_EXISTS_TAC [`pp`,`Var nn h1`]
    \\ IMP_RES_TAC TERM \\ IMP_RES_TAC TYPE \\ IMP_RES_TAC vfree_in_thm
    \\ FULL_SIMP_TAC (srw_ss()) [term_11,hol_tm_def] \\ METIS_TAC [TYPE_11])
  *)
  \\ REVERSE (Cases_on `EXISTS (\(t,x). vfree_in (Var s' ty) t /\ vfree_in x tm')
       (FILTER (\(t,x). x <> Var s' ty) theta)`) THEN1
   (IMP_RES_TAC TERM \\ IMP_RES_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [] >>
    simp[hol_tm_def,TERM_Abs] >>
    simp[VSUBST_def] >>
    BasicProvers.CASE_TAC >- (
      fs[EXISTS_MEM,EVERY_MEM,MEM_FILTER,FORALL_PROD,EXISTS_PROD,MEM_MAP] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_rename_tac`VFREE_IN (Var x (hol_ty ty)) (hol_tm pm)`[] >>
      qmatch_assum_rename_tac`VFREE_IN (hol_tm qm) (hol_tm pm2)`[] >>
      first_x_assum(qspecl_then[`pm`,`qm`]mp_tac) >>
      discharge_hyps >- (
        simp[] >> spose_not_then STRIP_ASSUME_TAC >> fs[hol_tm_def] ) >>
      strip_tac >- METIS_TAC[vfree_in_thm] >>
      first_x_assum(qspecl_then[`pm`,`qm`]mp_tac) >>
      Cases_on`qm`>>simp[]>>strip_tac>>fs[term_type_Var,hol_tm_def] >>
      METIS_TAC[vfree_in_thm,TERM] ) >>
    Q.PAT_ABBREV_TAC`thet = FILTER P theta` >>
    first_x_assum(qspec_then`thet`mp_tac)>>
    discharge_hyps >- (
      fs[EVERY_MEM,Abbr`thet`,MEM_FILTER,FORALL_PROD]>>
      rw[]>>METIS_TAC[])>>
    rw[Abbr`thet`] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    simp[rich_listTheory.FILTER_MAP] >>
    AP_TERM_TAC >>
    simp[rich_listTheory.FILTER_EQ,FORALL_PROD] >>
    fs[EVERY_MEM,FORALL_PROD] >>
    strip_tac >> Cases >> strip_tac >> res_tac >> fs[hol_tm_def] >>
    METIS_TAC[TYPE_11] ) >>
  simp[] >>
  `TERM defs (vsubst_aux (FILTER (\(t,x). x <> Var s' ty) theta) tm') /\
      TYPE defs ty` by
   (IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `FILTER (\(t,x). x <> Var s' ty) theta`)
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_FILTER])
  \\ IMP_RES_TAC variant_thm \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [hol_tm_def,term_11]
  \\ `(hol_tm (vsubst_aux (FILTER (\ (t,x). x <> Var s' ty) theta) tm')) =
      (VSUBST
       (FILTER ( \ (z,y). y <> Var s' (hol_ty ty))
         (MAP ( \ (t1,t2). (hol_tm t1,hol_tm t2)) theta)) (hol_tm tm'))` by
   (Q.PAT_ASSUM `!theta.bbb` (MP_TAC o
        Q.SPEC `FILTER (\(t,x). x <> Var s' ty) theta`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_FILTER,PULL_EXISTS])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ Q.PAT_ASSUM `EVERY PP xx` MP_TAC
    \\ Q.SPEC_TAC (`theta`,`xs`) \\ Induct
    \\ SIMP_TAC std_ss [MEM,FILTER,MAP] \\ Cases
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF] \\ STRIP_TAC
    \\ SRW_TAC [] []
    \\ METIS_TAC [TERM_11,TERM_def,hol_tm_def])
  \\ FULL_SIMP_TAC std_ss [TERM_Abs]
  \\ Q.PAT_ABBREV_TAC `theta1 = (FOO::FILTER (\(t,x). x <> Var s' ty) theta)`
  \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPEC `theta1`)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `theta1` \\ IMP_RES_TAC TERM_Var_SIMP
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,MEM_FILTER,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC [term_type_def] \\ SIMP_TAC (srw_ss()) [])
  \\ SIMP_TAC std_ss [VSUBST_def,LET_THM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SELECT_LEMMA2]
  \\ reverse BasicProvers.CASE_TAC >- (
      fs[EXISTS_MEM,EVERY_MEM,MEM_FILTER,FORALL_PROD,EXISTS_PROD,MEM_MAP] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_rename_tac`vfree_in (Var x ty) pm`[] >>
      qmatch_assum_rename_tac`vfree_in qm pm2`[] >>
      first_x_assum(qspecl_then[`pm`,`qm`]mp_tac) >> simp[] >>
      strip_tac >>
      first_x_assum(qspecl_then[`hol_tm pm`,`hol_tm qm`]mp_tac) >>
      discharge_hyps >- (
        conj_tac >- (
          spose_not_then STRIP_ASSUME_TAC >>
          Cases_on`qm`>>fs[hol_tm_def] >>
          METIS_TAC[TYPE_11] ) >>
        METIS_TAC[] ) >>
      Cases_on`qm`>>fs[hol_tm_def] >>
      METIS_TAC[vfree_in_thm,TERM] ) >>
  qunabbrev_tac`theta1` >>
  Q.PAT_ABBREV_TAC`vv = holSyntax$VARIANT A B Z` >>
  simp[hol_tm_def] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[rich_listTheory.FILTER_MAP] >>
  AP_TERM_TAC >>
  simp[rich_listTheory.FILTER_EQ,FORALL_PROD] >>
  fs[EVERY_MEM,FORALL_PROD] >>
  strip_tac >> Cases >> strip_tac >> res_tac >> fs[hol_tm_def] >>
  METIS_TAC[TYPE_11] )

val forall_thm = prove(
  ``!f s (xs:(hol_term # hol_term) list). (forall f xs s = (res,s')) ==>
    (!x. ?r. f x s = (r,s)) ==>
    (s' = s) /\ ((res = HolRes T) ==> EVERY (\x. FST (f x s) = HolRes T) xs)``,
  STRIP_TAC \\ STRIP_TAC
  \\ Induct \\ ASM_SIMP_TAC (srw_ss()) [Once forall_def,ex_return_def,ex_bind_def]
  \\ STRIP_TAC \\ Cases_on `f h s` \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC \\ STRIP_TAC
  \\ `r = s` by METIS_TAC [PAIR,PAIR_EQ] \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `a` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [FST,PAIR]);

val assoc_state = prove(
  ``!xs x. ?r. assoc x xs s = (r,s)``,
  Induct \\ ONCE_REWRITE_TAC [assoc_def] \\ TRY Cases
  \\ FULL_SIMP_TAC (srw_ss()) [failwith_def,ex_return_def] \\ SRW_TAC [] []);

val type_of_state = prove(
  ``!tm. ?r. type_of tm s = (r,s)``,
  HO_MATCH_MP_TAC type_of_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [Once type_of_def] \\ Cases_on `tm`
  \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def,failwith_def,ex_bind_def]
  THEN1
   (TRY (Cases_on `r`) \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def]
    \\ TRY (Cases_on `a`)
    \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def,failwith_def,ex_return_def]
    \\ Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `h`) \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def]
  \\ TRY (Cases_on `r`) \\ FULL_SIMP_TAC (srw_ss()) [dest_type_def]
  \\ FULL_SIMP_TAC (srw_ss()) [mk_fun_ty_def,mk_type_def,ex_bind_def,
        try_def,otherwise_def,get_type_arity_def,
        get_the_type_constants_def,failwith_def,ex_return_def]
  \\ STRIP_ASSUME_TAC (assoc_state |> ISPEC ``s.the_type_constants``
        |> ISPEC ``"fun"``) \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] []);

val vsubst_thm = store_thm("vsubst_thm",
  ``EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) theta /\
    TERM defs tm /\ STATE s defs /\
    (vsubst theta tm s = (res, s')) ==>
    (s' = s) /\ !t. (res = HolRes t) ==> TERM defs t /\
    (hol_tm t = VSUBST (MAP (\(t1,t2). (hol_tm t1, hol_tm t2)) theta) (hol_tm tm)) /\
    (EVERY (\(p_1,p_2). ?x ty. (hol_tm p_2 = Var x ty) /\
                               (hol_tm p_1) has_type ty) theta)``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [vsubst_def]
  \\ Cases_on `theta = []`
  \\ FULL_SIMP_TAC (srw_ss()) [MAP,VSUBST_EMPTY,ex_return_def,ex_bind_def]
  \\ Q.PAT_ABBREV_TAC `test = (\(t,x) state.
        case type_of t state of
          (HolRes ty,state) =>
            (case dest_var x state of
               (HolRes vty,state) => (HolRes (ty = SND vty),state)
             | (HolErr e,state) => (HolErr e,state))
        | (HolErr e,state) => (HolErr e,state))`
  \\ Cases_on `forall test theta s`
  \\ MP_TAC (forall_thm |> Q.SPECL [`test`,`s`,`theta`] |> Q.GENL [`res`,`s'`])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `TERM defs tm /\ STATE s defs` \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `test` \\ FULL_SIMP_TAC std_ss [FORALL_PROD]
    \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `p_1` type_of_state)
    \\ Cases_on `r'` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `p_2`
    \\ FULL_SIMP_TAC (srw_ss()) [hol_kernelTheory.dest_var_def,ex_return_def,failwith_def])
  \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `a` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ `EVERY
       (\(t1,t2).
          TERM defs t1 /\ TERM defs t2 /\
          (term_type t1 = term_type t2) /\ is_var t2) theta` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [EVERY_MEM,FORALL_PROD] \\ NTAC 3 STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `test`
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC type_of_thm
    \\ FULL_SIMP_TAC (srw_ss()) [hol_kernelTheory.dest_var_def]
    \\ Cases_on `p_2`
    \\ FULL_SIMP_TAC (srw_ss()) [hol_kernelTheory.dest_var_def,ex_return_def,failwith_def,is_var_def]
    \\ SIMP_TAC (srw_ss()) [Once term_type_def])
  \\ IMP_RES_TAC (vsubst_aux_thm |> SIMP_RULE std_ss [])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,FORALL_PROD] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Cases_on `p_2` \\ FULL_SIMP_TAC (srw_ss()) [is_var_def,hol_tm_def,term_11]
  \\ IMP_RES_TAC term_type
  \\ FULL_SIMP_TAC std_ss [TERM_def,hol_tm_def,typeof_def]
  \\ FULL_SIMP_TAC std_ss [WELLTYPED,term_type_Var] >>
  rfs[STATE_def] >>
  rw[] >> METIS_TAC [WELLTYPED,term_ok_welltyped])

val inst_aux_Var = prove(
  ``inst_aux [] theta (Var v ty) state =
      (HolRes (Var v (type_subst theta ty)),state)``,
  SIMP_TAC (srw_ss()) [Once inst_aux_def,rev_assocd_thm,REV_ASSOCD,
       LET_DEF,ex_return_def] \\ METIS_TAC []);

val MEM_subtract = prove(
  ``!xs ys x. MEM x (subtract xs ys) <=> MEM x xs /\ ~MEM x ys``,
  FULL_SIMP_TAC std_ss [subtract_def,MEM_FILTER,MEM] \\ METIS_TAC []);

val MEM_frees = prove(
  ``!tm y. TERM defs tm /\ MEM y (frees tm) ==>
           ?v ty. (y = Var v ty) /\ TYPE defs ty``,
  Induct \\ SIMP_TAC (srw_ss()) [Once frees_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [MEM_union,MEM_subtract]);

val inst_aux_thm = prove(
  ``!env theta tm s s' res.
      EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
      EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) env /\
      TERM defs tm /\ STATE s defs /\
      (inst_aux env theta tm s = (res, s')) ==>
      STATE s' defs /\
      case res of
      | HolRes t =>
         (INST_CORE (MAP (\(t1,t2). (hol_tm t1, hol_tm t2)) env)
           (MAP (\(t1,t2). (hol_ty t1, hol_ty t2)) theta) (hol_tm tm) =
           Result (hol_tm t))
      | HolErr v =>
         (INST_CORE (MAP (\(t1,t2). (hol_tm t1, hol_tm t2)) env)
           (MAP (\(t1,t2). (hol_ty t1, hol_ty t2)) theta) (hol_tm tm) =
           Clash (hol_tm s'.the_clash_var))``,
  HO_MATCH_MP_TAC inst_aux_ind \\ NTAC 4 STRIP_TAC \\ Cases_on `tm`
  \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1
   (ONCE_REWRITE_TAC [inst_aux_def] \\ SIMP_TAC (srw_ss()) [LET_DEF]
    \\ `(if type_subst theta h = h then Var s h
      else Var s (type_subst theta h)) = Var s (type_subst theta h)` by METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [rev_assocd_thm] \\ POP_ASSUM (K ALL_TAC)
    \\ SIMP_TAC std_ss [INST_CORE_def,hol_tm_def]
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM type_subst_thm,ex_return_def]
    \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ NTAC 7 STRIP_TAC
    \\ `(REV_ASSOCD (Var s (hol_ty (type_subst theta h)))
           (MAP (\(t1,t2). (hol_tm t1,hol_tm t2)) env)
           (Var s (hol_ty h)) =
         Var s (hol_ty h)) =
       (REV_ASSOCD (Var s (type_subst theta h)) env (Var s h) = Var s h)`
          by ALL_TAC THEN1
     (Induct_on `env` \\ FULL_SIMP_TAC std_ss [MAP,REV_ASSOCD]
      \\ Cases \\ FULL_SIMP_TAC std_ss [MAP,REV_ASSOCD,EVERY_DEF] \\ STRIP_TAC
      \\ `(hol_tm r = hol_tm (Var s (type_subst theta h))) =
          (r = Var s (type_subst theta h))` by ALL_TAC THEN1
       (MATCH_MP_TAC (TERM_11 |> GEN_ALL)
        \\ Q.LIST_EXISTS_TAC [`defs`]
        \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC (TERM_Var |> GEN_ALL)
        \\ FULL_SIMP_TAC std_ss [TYPE_def,type_subst_thm]
        \\ MATCH_MP_TAC type_ok_TYPE_SUBST
        \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [TYPE_def,
             EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] \\ METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss [hol_tm_def]
      \\ Cases_on `r = Var s (type_subst theta h)`
      \\ FULL_SIMP_TAC std_ss [hol_tm_def,EVERY_DEF]
      \\ SIMP_TAC std_ss [GSYM hol_tm_def]
      \\ MATCH_MP_TAC (TERM_11 |> GEN_ALL)
      \\ Q.LIST_EXISTS_TAC [`defs`]
      \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.SPEC_TAC (`res`,`res`)
    \\ Cases_on `REV_ASSOCD (Var s (type_subst theta h)) env (Var s h) = Var s h`
    \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def,ex_bind_def,
         set_the_clash_var_def,failwith_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (srw_ss()) [STATE_def,hol_tm_def,LET_DEF]
    \\ Q.PAT_ASSUM `defs = s'.the_definitions` ASSUME_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [MAP_APPEND]
    \\ MATCH_MP_TAC (TERM_Var |> GEN_ALL)
    \\ FULL_SIMP_TAC std_ss [TYPE_def,type_subst_thm]
    \\ MATCH_MP_TAC type_ok_TYPE_SUBST \\ IMP_RES_TAC TERM
    \\ FULL_SIMP_TAC std_ss [TYPE_def]
    \\ FULL_SIMP_TAC std_ss [TYPE_def,
             EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] \\ METIS_TAC [])
  THEN1
   (ONCE_REWRITE_TAC [inst_aux_def] \\ SIMP_TAC (srw_ss()) [LET_DEF,ex_return_def]
    \\ NTAC 4 STRIP_TAC
    \\ `(res = HolRes (Const s (type_subst theta h))) /\ (s' = s'')` by ALL_TAC
    THEN1 (Cases_on `type_subst theta h = h` \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]
    \\ SIMP_TAC std_ss [INST_CORE_def,type_subst_thm])
  THEN1
   (ONCE_REWRITE_TAC [inst_aux_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,ex_return_def,ex_bind_def]
    \\ NTAC 4 STRIP_TAC \\ Cases_on `inst_aux env theta h s`
    \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (Q.PAT_ASSUM `HolErr xx = res` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]
      \\ ONCE_REWRITE_TAC [INST_CORE_def] \\ IMP_RES_TAC TERM
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def,LET_THM])
    \\ Cases_on `inst_aux env theta h0 r`
    \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (Q.PAT_ASSUM `HolErr xx = res` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]
      \\ ONCE_REWRITE_TAC [INST_CORE_def] \\ IMP_RES_TAC TERM
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def,LET_THM])
    THEN1
     (Q.PAT_ASSUM `HolRes xx = res` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC (srw_ss()) [hol_tm_def]
      \\ ONCE_REWRITE_TAC [INST_CORE_def] \\ IMP_RES_TAC TERM
      \\ FULL_SIMP_TAC std_ss []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`)
      \\ FULL_SIMP_TAC (srw_ss()) [IS_CLASH_def,RESULT_def,LET_THM]))
  \\ SIMP_TAC (srw_ss()) [Once inst_aux_def]
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ NTAC 7 STRIP_TAC
  \\ IMP_RES_TAC Abs_Var
  \\ Q.MATCH_ASSUM_RENAME_TAC `h = Var v ty` []
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [Once inst_aux_def]
  \\ `!ty'. (if ty' = ty then Var v ty else Var v ty') = Var v ty'` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [rev_assocd_thm,REV_ASSOCD,LET_DEF,ex_return_def]
  \\ SIMP_TAC (srw_ss()) [ex_bind_def,otherwise_def]
  \\ Cases_on `inst_aux ((Var v ty,Var v (type_subst theta ty))::env) theta h0 s`
  \\ Q.PAT_ASSUM `!x yy.bbb` (K ALL_TAC)
  \\ Q.PAT_ASSUM `!x yy.bbb` (MP_TAC o Q.SPECL
       [`((Var v ty,Var v (type_subst theta ty))::env)`,`s`])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (IMP_RES_TAC TERM \\ IMP_RES_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ MATCH_MP_TAC TERM_Var \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [TYPE_def,type_subst_thm]
    \\ MATCH_MP_TAC type_ok_TYPE_SUBST
    \\ FULL_SIMP_TAC std_ss [MEM_MAP,EXISTS_PROD,PULL_EXISTS,FORALL_PROD,
         EVERY_MEM] \\ METIS_TAC [])
  \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [INST_CORE_def,hol_tm_def,LET_THM]
    \\ FULL_SIMP_TAC std_ss [hol_tm_def,type_subst_thm,IS_RESULT_def,RESULT_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC (srw_ss()) [get_the_clash_var_def,failwith_def]
  \\ Cases_on `r.the_clash_var <> Var v (type_subst theta ty)`
  \\ `(r.the_clash_var = Var v (type_subst theta ty)) =
      (hol_tm r.the_clash_var =
       Var v (TYPE_SUBST (MAP (\(t1,t2). (hol_ty t1,hol_ty t2)) theta)
        (hol_ty ty)))` by ALL_TAC THEN1
   (SIMP_TAC std_ss [GSYM type_subst_thm,GSYM hol_tm_def]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ MATCH_MP_TAC TERM_11 \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (Q.PAT_ASSUM `STATE r defs` MP_TAC
      \\ SIMP_TAC std_ss [STATE_def,LET_DEF]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ MATCH_MP_TAC TERM_Var \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [TYPE_def,type_subst_thm]
    \\ MATCH_MP_TAC type_ok_TYPE_SUBST \\ IMP_RES_TAC TERM
    \\ FULL_SIMP_TAC std_ss [TYPE_def]
    \\ FULL_SIMP_TAC std_ss [TYPE_def,
             EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [INST_CORE_def,hol_tm_def,LET_THM]
    \\ FULL_SIMP_TAC std_ss [hol_tm_def,type_subst_thm,IS_RESULT_def,CLASH_def])
  THEN1 (FULL_SIMP_TAC std_ss [type_subst_thm,hol_tm_def])
  \\ SIMP_TAC (srw_ss()) [inst_aux_Var,``dest_var (Var v ty) state``
        |> SIMP_CONV (srw_ss()) [hol_kernelTheory.dest_var_def,ex_return_def]]
  \\ Q.ABBREV_TAC `fresh_name = (VARIANT
                (RESULT
                   (INST_CORE []
                      (MAP ( \ (t1,t2). (hol_ty t1,hol_ty t2)) theta)
                      (hol_tm h0))) v
                (TYPE_SUBST
                   (MAP ( \ (t1,t2). (hol_ty t1,hol_ty t2)) theta)
                   (hol_ty ty)))`
  \\ Q.PAT_ASSUM `!x y. bbb` (MP_TAC o Q.SPEC `r`)
  \\ IMP_RES_TAC TERM
  \\ Cases_on `inst_aux [] theta h0 r` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ REVERSE (Cases_on `q`) THEN1
   (FULL_SIMP_TAC (srw_ss()) []
    \\ MP_TAC (INST_CORE_LEMMA |> Q.SPECL
        [`(MAP (\(t1,t2). (hol_ty t1,hol_ty t2)) theta)`,`(hol_tm h0)`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [TERM_def] >> METIS_TAC[term_ok_welltyped])
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [result_distinct])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.MATCH_ASSUM_RENAME_TAC `inst_aux [] theta h0 r = (HolRes a,r1)` []
  \\ `(variant (frees a) (Var v (type_subst theta ty))) =
      Var fresh_name (type_subst theta ty)` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [GSYM type_subst_thm,RESULT_def]
    \\ Q.UNABBREV_TAC `fresh_name`
    \\ MATCH_MP_TAC variant_alt \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE STRIP_TAC THEN1
     (IMP_RES_TAC TERM
      \\ FULL_SIMP_TAC std_ss [TYPE_def,type_subst_thm]
      \\ MATCH_MP_TAC type_ok_TYPE_SUBST
      \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [TYPE_def,
             EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [TERM_def]
    \\ qmatch_assum_abbrev_tac`INST_CORE [] tyin tm = Result rr`
    \\ `rr = RESULT (INST_CORE [] tyin tm)` by rw[] >> pop_assum SUBST1_TAC
    \\ MATCH_MP_TAC term_ok_INST_CORE
    \\ simp[Abbr`tyin`,EVERY_MAP,EVERY_MEM,FORALL_PROD] >>
       fs[EVERY_MEM,TYPE_def,FORALL_PROD]
    \\ REPEAT STRIP_TAC \\ RES_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [inst_aux_Var,``dest_var (Var v ty) state``
        |> SIMP_CONV (srw_ss()) [hol_kernelTheory.dest_var_def,ex_return_def]]
  \\ Q.PAT_ASSUM `!x y z.bbb` (MP_TAC o Q.SPECL
       [`fresh_name`,`ty`,`(type_subst theta ty)`,`r1`])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `inst_aux ((Var fresh_name ty,
                  Var fresh_name (type_subst theta ty))::env) theta
       (vsubst_aux [(Var fresh_name ty,Var v ty)] h0) r1`
  \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [EVERY_DEF] \\ REPEAT STRIP_TAC
    \\ TRY (MATCH_MP_TAC TERM_Var) \\ IMP_RES_TAC TERM
    \\ FULL_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [TYPE_def,type_subst_thm]
      \\ MATCH_MP_TAC type_ok_TYPE_SUBST
      \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [TYPE_def,
             EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS] \\ METIS_TAC [])
    \\ (vsubst_aux_thm |> SIMP_RULE std_ss []
     |> Q.SPECL [`tm`,`[Var v ty,Var y ty]`]
     |> SIMP_RULE std_ss [EVERY_DEF,MAP,hol_tm_def]
     |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> MP_CANON |> MATCH_MP_TAC)
    \\ ONCE_REWRITE_TAC [term_type_def]
    \\ FULL_SIMP_TAC (srw_ss()) [is_var_def]
    \\ REPEAT STRIP_TAC
    \\ TRY (MATCH_MP_TAC TERM_Var) \\ IMP_RES_TAC TERM
    \\ FULL_SIMP_TAC std_ss [])
  \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [hol_tm_def,type_subst_thm]
  \\ SIMP_TAC std_ss [INST_CORE_def,LET_THM]
  \\ FULL_SIMP_TAC std_ss [hol_tm_def,type_subst_thm,IS_RESULT_def,CLASH_def]
  \\ FULL_SIMP_TAC std_ss [GSYM type_subst_thm]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [hol_tm_def]
  \\ `(hol_tm (vsubst_aux [(Var fresh_name ty,Var v ty)] h0)) =
      (VSUBST [(Var fresh_name (hol_ty ty),Var v (hol_ty ty))] (hol_tm h0))` by
   ((vsubst_aux_thm |> SIMP_RULE std_ss []
     |> Q.SPECL [`tm`,`[Var v ty,Var y ty]`]
     |> SIMP_RULE std_ss [EVERY_DEF,MAP,hol_tm_def]
     |> UNDISCH_ALL |> CONJUNCT2 |> DISCH_ALL |> MP_CANON |> MATCH_MP_TAC)
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC (srw_ss()) [is_var_def]
    \\ ONCE_REWRITE_TAC [term_type_def] \\ SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [IS_RESULT_def,RESULT_def])

val inst_lemma = prove(
  ``EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
    TERM defs tm /\ STATE s defs /\
    (inst theta tm s = (res, s')) ==>
    STATE s' defs /\ !t. (res = HolRes t) ==>
    (hol_tm t = INST (MAP (\(t1,t2). (hol_ty t1, hol_ty t2)) theta) (hol_tm tm))``,
  SIMP_TAC std_ss [INST_def,inst_def] \\ Cases_on `theta = []`
  \\ ASM_SIMP_TAC std_ss [MAP,EVERY_DEF,ex_return_def] THEN1
   (Q.SPEC_TAC (`res`,`res`) \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [TERM_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ imp_res_tac term_ok_welltyped
    \\ IMP_RES_TAC INST_CORE_HAS_TYPE
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`[]`,`[]`])
    \\ FULL_SIMP_TAC std_ss [MEM,REV_ASSOCD]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [RESULT_def]
    \\ FULL_SIMP_TAC std_ss [INST_CORE_EMPTY,result_11,RESULT_def])
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (inst_aux_thm |> Q.SPECL [`[]`,`theta`]
                  |> SIMP_RULE std_ss [EVERY_DEF,MAP])
  \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [TERM_def] >> imp_res_tac term_ok_welltyped
  \\ IMP_RES_TAC INST_CORE_HAS_TYPE
  \\ POP_ASSUM (MP_TAC o Q.SPECL
       [`(MAP (\(t1,t2). (hol_ty t1,hol_ty t2)) theta)`,`[]`])
  \\ FULL_SIMP_TAC std_ss [MEM,REV_ASSOCD] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MAP,RESULT_def,result_distinct,result_11]
  \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) [])

val inst_thm = store_thm("inst_thm",
  ``EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
    TERM defs tm /\ STATE s defs /\
    (inst theta tm s = (res, s')) ==>
    STATE s' defs /\ !t. (res = HolRes t) ==> TERM defs t /\
    (hol_tm t = INST (MAP (\(t1,t2). (hol_ty t1, hol_ty t2)) theta) (hol_tm tm))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC inst_lemma
  \\ FULL_SIMP_TAC std_ss [TERM_def] >> imp_res_tac term_ok_welltyped
  \\ IMP_RES_TAC INST_CORE_LEMMA
  \\ SIMP_TAC std_ss [INST_def]
  \\ POP_ASSUM (MP_TAC o Q.SPEC `(MAP (\(t1,t2). (hol_ty t1,hol_ty t2)) theta)`)
  \\ STRIP_TAC
  \\ MATCH_MP_TAC term_ok_INST_CORE
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS,FORALL_PROD,EVERY_MEM]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,TYPE_def,FORALL_PROD,MEM,IS_RESULT_def]
  \\ METIS_TAC [])

(* ------------------------------------------------------------------------- *)
(* Verification of thm functions                                             *)
(* ------------------------------------------------------------------------- *)

val dest_thm_thm = store_thm("dest_thm_thm",
  ``THM defs th /\ STATE s defs /\ (dest_thm th = (asl, c)) ==>
    EVERY (TERM defs) asl /\ TERM defs c``,
  REPEAT STRIP_TAC \\ Cases_on `th` \\ IMP_RES_TAC THM
  \\ FULL_SIMP_TAC std_ss [dest_thm_def] \\ METIS_TAC []);

val hyp_thm = store_thm("hyp_thm",
  ``THM defs th /\ STATE s defs /\ (hyp th = asl) ==>
    EVERY (TERM defs) asl``,
  REPEAT STRIP_TAC \\ Cases_on `th` \\ IMP_RES_TAC THM
  \\ FULL_SIMP_TAC std_ss [hyp_def] \\ METIS_TAC []);

val concl_thm = store_thm("concl_thm",
  ``THM defs th /\ STATE s defs /\ (concl th = c) ==>
    TERM defs c``,
  REPEAT STRIP_TAC \\ Cases_on `th` \\ IMP_RES_TAC THM
  \\ FULL_SIMP_TAC std_ss [concl_def] \\ METIS_TAC []);

val REFL_thm = store_thm("REFL_thm",
  ``TERM defs tm /\ STATE s defs /\ (REFL tm s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  SIMP_TAC std_ss [REFL_def,ex_bind_def] \\ Cases_on `mk_eq(tm,tm) s`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC mk_eq_thm
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ Q.PAT_ASSUM `xxx = th` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) [THM_def,hol_tm_def,hol_ty_def,domain_def] >>
  rw[] >>
  fs[STATE_def] >> rw[] >> imp_res_tac term_type
  \\ simp[GSYM equation_def]
  \\ MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,8)) >>
  fs[CONTEXT_def,TERM_def] >>
  METIS_TAC[extends_theory_ok,init_theory_ok])

val TRANS_thm = store_thm("TRANS_thm",
  ``THM defs th1 /\ THM defs th2 /\ STATE s defs /\
    (TRANS th1 th2 s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  Cases_on `th1` \\ Cases_on `th2` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [TRANS_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ SRW_TAC [] [ex_bind_def] \\ IMP_RES_TAC THM
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Comb (Comb (Const "=" h1) ll) m1)` []
  \\ POP_ASSUM MP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Comb (Comb (Const "=" h2) m2) rr)` []
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM \\ Cases_on `mk_eq (ll,rr) s`
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`ll`,`y`|->`rr`,`res`|->`q`,`s'`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def]
  \\ MP_TAC (aconv_thm |> Q.SPECL [`m1`,`m2`] |> SIMP_RULE std_ss [])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC >>
  rpt(qpat_assum`H |- C`mp_tac) >>
  imp_res_tac term_union_thm >> simp[] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[hol_tm_def,hol_ty_def] >>
  imp_res_tac Equal_type >> fs[hol_ty_def] >>
  imp_res_tac Equal_type_IMP >>
  ntac 2 (pop_assum(mp_tac o SYM)) >>
  simp[GSYM equation_def] >> rw[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,9)) >>
  METIS_TAC[])

val MK_COMB_thm = store_thm("MK_COMB_thm",
  ``THM defs th1 /\ THM defs th2 /\ STATE s defs /\
    (MK_COMB (th1,th2) s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  Cases_on `th1` \\ Cases_on `th2` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [MK_COMB_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ SRW_TAC [] [ex_bind_def] \\ IMP_RES_TAC THM
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Comb (Comb (Const "=" h1) f1) f2)` []
  \\ POP_ASSUM MP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Comb (Comb (Const "=" h2) x1) x2)` []
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
  \\ Cases_on `mk_comb (f1,x1) s`
  \\ MP_TAC (mk_comb_thm |> Q.INST [`f`|->`f1`,`a`|->`x1`,`res`|->`q`,`s1`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ Cases_on `mk_comb (f2,x2) s`
  \\ MP_TAC (mk_comb_thm |> Q.INST [`f`|->`f2`,`a`|->`x2`,`res`|->`q`,`s1`|->`r'`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ Cases_on `mk_eq (Comb f1 x1,Comb f2 x2) s`
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`Comb f1 x1`,
         `y`|->`Comb f2 x2`,`res`|->`q`,`s'`|->`r''`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def] >>
  rpt(qpat_assum`H |- C`mp_tac) >>
  imp_res_tac term_union_thm >> simp[] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[hol_tm_def,hol_ty_def] >>
  imp_res_tac Equal_type >> fs[hol_ty_def] >>
  imp_res_tac Equal_type_IMP >>
  ntac 2 (pop_assum(mp_tac o SYM)) >>
  `codomain (typeof (hol_tm f1)) = typeof (Comb (hol_tm f1) (hol_tm x1))` by simp[] >>
  pop_assum SUBST1_TAC >> simp_tac std_ss [GSYM equation_def] >>
  rw[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,7)) >>
  qpat_assum`TERM x (Comb f1 x1)`mp_tac >> simp[TERM_Comb] >> strip_tac >>
  fs[TERM_def] >> imp_res_tac term_ok_welltyped >> simp[])

val ABS_thm = store_thm("ABS_thm",
  ``TERM defs tm /\ THM defs th1 /\ STATE s defs /\
    (ABS tm th1 s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  Cases_on `th1` \\ SIMP_TAC std_ss [ABS_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ Cases_on `h'` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ FULL_SIMP_TAC std_ss [ex_bind_def]
  \\ Cases_on `s'' = "="` \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []
  \\ TRY (
      POP_ASSUM MP_TAC \\
      NTAC 3 BasicProvers.CASE_TAC \\
      STRIP_TAC \\
      FULL_SIMP_TAC std_ss [] \\
      NO_TAC)
  \\ Q.MATCH_ASSUM_RENAME_TAC
       `THM defs (Sequent l (Comb (Comb (Const "=" h) t1) t2))` []
  \\ Cases_on `mk_abs (tm,t1) s` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ MP_TAC (mk_abs_thm |> Q.SPECL [`q`] |> Q.INST [`bvar`|->`tm`,
       `bod`|->`t1`,`s1`|->`r`])
  \\ IMP_RES_TAC THM \\ IMP_RES_TAC TERM \\ IMP_RES_TAC TERM
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `mk_abs (tm,t2) s` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ MP_TAC (mk_abs_thm |> Q.SPECL [`q`] |> Q.INST [`bvar`|->`tm`,
       `bod`|->`t2`,`s1`|->`r'`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
  \\ Cases_on `mk_eq (Abs tm t1,Abs tm t2) s`
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`Abs tm t1`,`y`|->`Abs tm t2`,
                                  `res`|->`q`,`s'`|->`r''`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [THM_def]
  >> rpt(qpat_assum`H |- C`mp_tac) >>
  imp_res_tac term_union_thm >> simp[] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[hol_tm_def,hol_ty_def] >>
  imp_res_tac Equal_type >> fs[hol_ty_def] >>
  imp_res_tac Equal_type_IMP >>
  ntac 1 (pop_assum(mp_tac o SYM)) >>
  simp[GSYM equation_def] >>
  imp_res_tac Abs_Var >>
  rw[hol_tm_def] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,0)) >>
  fs[EVERY_MAP,EVERY_MEM,PULL_EXISTS,TYPE_def,term_type_Var,hol_tm_def] >>
  REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC TERM \\ IMP_RES_TAC VFREE_IN_IMP)

val BETA_thm = store_thm("BETA_thm",
  ``TERM defs tm /\ STATE s defs /\
    (BETA tm s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  SIMP_TAC std_ss [BETA_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Cases_on `tm` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ SRW_TAC [] [ex_bind_def,ex_return_def]
  \\ IMP_RES_TAC TERM \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `t2 = Var name ty` [] \\ POP_ASSUM (K ALL_TAC)
  \\ Q.MATCH_ASSUM_RENAME_TAC `TERM defs (Abs (Var name ty) bod)` []
  \\ Cases_on `mk_eq (Comb (Abs (Var name ty) bod) (Var name ty),bod) s`
  \\ IMP_RES_TAC TERM
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`Comb (Abs (Var name ty) bod) (Var name ty)`,
         `y`|->`bod`,`res`|->`q`,`s'`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[hol_tm_def,hol_ty_def] >>
  `typeof (hol_tm bod) = typeof (Comb (Abs name (hol_ty ty) (hol_tm bod)) (Var name (hol_ty ty)))` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp_tac std_ss [GSYM equation_def] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,2)) >>
  fs[CONTEXT_def,TERM_def,TYPE_def] >>
  METIS_TAC[extends_theory_ok,init_theory_ok])

val ASSUME_thm = store_thm("ASSUME_thm",
  ``TERM defs tm /\ STATE s defs /\
    (ASSUME tm s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  SIMP_TAC std_ss [ASSUME_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ STRIP_TAC \\ MP_TAC (type_of_thm |> Q.SPEC `tm`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [ex_bind_def]
  \\ MP_TAC (mk_type_thm |> Q.SPECL [`"bool"`,`[]`,`s`])
  \\ Cases_on `mk_type ("bool",[]) s`
  \\ FULL_SIMP_TAC (srw_ss()) [EVERY_DEF]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `term_type tm = bool_ty`
  \\ FULL_SIMP_TAC (srw_ss()) [failwith_def,ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def]
  >> simp[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,1)) >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[STATE_def] >> imp_res_tac term_type >> rfs[hol_ty_def] >>
  fs[TERM_def] >>
  imp_res_tac term_ok_welltyped >>
  FULL_SIMP_TAC std_ss [WELLTYPED]
  >> METIS_TAC[CONTEXT_def,extends_theory_ok,init_theory_ok])

val EQ_MP_thm = store_thm("EQ_MP_thm",
  ``THM defs th1 /\ THM defs th2 /\ STATE s defs /\
    (EQ_MP th1 th2 s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  Cases_on `th1` \\ Cases_on `th2` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [EQ_MP_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [failwith_def]
  \\ SRW_TAC [] [ex_bind_def,ex_return_def] \\ IMP_RES_TAC THM
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
  \\ Q.MATCH_ASSUM_RENAME_TAC `THM defs (Sequent l
        (Comb (Comb (Const "=" h1) t1) t2))` []
  \\ FULL_SIMP_TAC std_ss [THM_def]
  >> rpt(qpat_assum`H |- C`mp_tac) >>
  imp_res_tac term_union_thm >> simp[] >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  fs[hol_tm_def,hol_ty_def] >>
  imp_res_tac TERM_Eq_x >> pop_assum (assume_tac o SYM) >>
  simp[GSYM equation_def] >> rw[] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,4)) >>
  fs[TERM_Comb] >>
  METIS_TAC[aconv_thm])

val FILTER_ACONV = prove(
  ``STATE s defs /\ TERM defs tm /\ EVERY (TERM defs) l ==>
    (MAP hol_tm (FILTER (\t1. ~aconv tm t1) l) =
     FILTER ($~ o ACONV (hol_tm tm)) (MAP hol_tm l))``,
  Induct_on `l` \\ FULL_SIMP_TAC std_ss [EVERY_DEF,FILTER,MAP]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC aconv_thm
  \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] []);

val DEDUCT_ANTISYM_RULE_thm = store_thm("DEDUCT_ANTISYM_RULE_thm",
  ``THM defs th1 /\ THM defs th2 /\ STATE s defs /\
    (DEDUCT_ANTISYM_RULE th1 th2 s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  Cases_on `th1` \\ Cases_on `th2` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [DEDUCT_ANTISYM_RULE_def,LET_DEF,ex_bind_def]
  \\ Cases_on `mk_eq (h,h') s` \\ STRIP_TAC
  \\ IMP_RES_TAC THM
  \\ MP_TAC (mk_eq_thm |> Q.INST [`x`|->`h`,
         `y`|->`h'`,`res`|->`q`,`s'`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ FULL_SIMP_TAC std_ss [THM_def]
  >> simp[hol_tm_def,hol_ty_def] >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  `EVERY (TERM defs) (term_remove h' l) ∧
   EVERY (TERM defs) (term_remove h l')` by (
    simp[term_remove_def,EVERY_FILTER] >>
    fs[EVERY_MEM]) >>
  `CONTEXT defs` by fs[STATE_def] >>
  imp_res_tac term_type >>
  simp[GSYM equation_def] >>
  imp_res_tac term_union_thm >>
  simp[] >>
  imp_res_tac FILTER_ACONV >>
  simp[term_remove_def] >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,3)) >>
  simp[])

val map_lemma = prove(
  ``!P l s res s'.
      (map (inst theta) l s = (res,s')) /\ STATE s defs ==>
      EVERY (\x. !s. STATE s defs ==>
                     ?r s'. (inst theta x s = (r,s')) /\ STATE s' defs /\
                        !t. (r = HolRes t) ==> P x t) l ==>
      STATE s' defs /\ !ts. (res = HolRes ts) ==> EVERY2 P l ts``,
  STRIP_TAC \\ Induct \\ SIMP_TAC (srw_ss()) [Once map_def,ex_return_def,ex_bind_def]
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ NTAC 5 STRIP_TAC \\ Cases_on `inst theta h s` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ,GSYM AND_IMP_INTRO]
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `s`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `map (inst theta) l r`
  \\ REVERSE (Cases_on `q`) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) []);

val INST_TYPE_thm = store_thm("INST_TYPE_thm",
  ``EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) theta /\
    THM defs th1 /\ STATE s defs /\
    (INST_TYPE theta th1 s = (res, s')) ==>
    STATE s' defs /\ !th. (res = HolRes th) ==> THM defs th``,
  Cases_on `th1` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [INST_TYPE_def,LET_DEF,ex_bind_def]
  \\ STRIP_TAC \\ IMP_RES_TAC THM
  \\ Cases_on `map (inst theta) l s`
  \\ MP_TAC (map_lemma |> Q.SPECL [`\tm t. (hol_tm t =
      INST (MAP (\(t1,t2). (hol_ty t1,hol_ty t2)) theta) (hol_tm tm))`,`l`,`s`])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC
    \\ Cases_on `inst theta x s'''` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
    \\ IMP_RES_TAC (inst_thm |> SIMP_RULE std_ss [EVERY_MEM])
    \\ METIS_TAC [])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ Cases_on `inst theta h r`
  \\ MP_TAC (inst_thm |> Q.INST [`res`|->`q`,`s'`|->`r'`,`tm`|->`h`,`s`|->`r`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [THM_def] >>
  Q.PAT_ABBREV_TAC`tyin:(type#type)list = MAP X theta` >>
  `MAP hol_tm a = MAP (INST tyin) (MAP hol_tm l)` by (
    fs[LIST_EQ_REWRITE,EVERY2_EVERY,Abbr`tyin`,EVERY_MEM] >>
    rfs[MEM_ZIP,PULL_EXISTS,EL_MAP] ) >>
  pop_assum SUBST1_TAC >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,6)) >>
  simp[EVERY_MAP,Abbr`tyin`] >>
  fs[EVERY_MEM,FORALL_PROD,TYPE_def] >>
  METIS_TAC[])

val map_lemma = prove(
  ``!l P s res s'.
      (map (vsubst theta) l s = (res,s')) ==>
      EVERY (\x. ?r. (vsubst theta x s = (r,s)) /\
                     !t. (r = HolRes t) ==> P x t) l ==>
      (s' = s) /\ !ts. (res = HolRes ts) ==> EVERY2 P l ts``,
  Induct \\ SIMP_TAC (srw_ss()) [Once map_def,ex_return_def,ex_bind_def]
  \\ NTAC 5 STRIP_TAC \\ Cases_on `vsubst theta h s` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `r = s` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `map (vsubst theta) l s`
  \\ NTAC 2 STRIP_TAC \\ RES_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []);

val INST_thm = store_thm("INST_thm",
  ``EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) theta /\
    THM defs th1 /\ STATE s defs /\
    (INST theta th1 s = (res, s')) ==>
    (s' = s) /\ !th. (res = HolRes th) ==> THM defs th``,
  Cases_on `th1` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [hol_kernelTheory.INST_def,LET_DEF,ex_bind_def]
  \\ STRIP_TAC \\ IMP_RES_TAC THM
  \\ Cases_on `map (vsubst theta) l s`
  \\ MP_TAC (map_lemma |> Q.SPECL [`l`,`\tm t. (hol_tm t =
      VSUBST (MAP (\(t1,t2). (hol_tm t1,hol_tm t2)) theta) (hol_tm tm))`,`s`])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC
    \\ Cases_on `vsubst theta x s` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
    \\ IMP_RES_TAC (vsubst_thm |> SIMP_RULE std_ss [EVERY_MEM])
    \\ METIS_TAC [])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [ex_return_def]
  \\ Cases_on `vsubst theta h s`
  \\ MP_TAC (vsubst_thm |> Q.INST [`res`|->`q`,`s'`|->`r'`,`tm`|->`h`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [THM_def] >>
  Q.PAT_ABBREV_TAC`tyin:(term#term)list = MAP X theta` >>
  `MAP hol_tm a = MAP (VSUBST tyin) (MAP hol_tm l)` by (
    fs[LIST_EQ_REWRITE,EVERY2_EVERY,Abbr`tyin`,EVERY_MEM] >>
    rfs[MEM_ZIP,PULL_EXISTS,EL_MAP] ) >>
  pop_assum SUBST1_TAC >>
  MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,5)) >>
  simp[EVERY_MAP,Abbr`tyin`,MEM_MAP,PULL_EXISTS] >>
  fs[EVERY_MEM,FORALL_PROD,TERM_def] >>
  METIS_TAC[])

(* ------------------------------------------------------------------------- *)
(* Verification of definition functions                                      *)
(* ------------------------------------------------------------------------- *)

val TYPE_CONS_EXTEND = store_thm("TYPE_CONS_EXTEND",
  ``STATE s (d::defs) /\ TYPE defs ty ==> TYPE (d::defs) ty``,
  simp[STATE_def,TYPE_def] >> strip_tac >>
  match_mp_tac type_ok_extend >>
  HINT_EXISTS_TAC >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  Cases_on`d`>>fs[hol_def_def,SUBMAP_FUNION] >>
  match_mp_tac SUBMAP_FUNION >>
  fs[pred_setTheory.IN_DISJOINT])

val TERM_CONS_EXTEND = store_thm("TERM_CONS_EXTEND",
  ``STATE s (d::defs) /\ TERM defs tm ==> TERM (d::defs) tm``,
  simp[STATE_def,TERM_def] >> strip_tac >>
  match_mp_tac term_ok_extend >>
  map_every qexists_tac[`tysof(hol_defs defs)`,`tmsof(hol_defs defs)`] >>
  imp_res_tac CONTEXT_ALL_DISTINCT >>
  Cases_on`d`>>fs[hol_def_def,SUBMAP_FUNION,LET_THM] >>
  TRY conj_tac >> match_mp_tac SUBMAP_FUNION >>
  fs[pred_setTheory.IN_DISJOINT] >>
  fs[ALL_DISTINCT_APPEND] >>
  METIS_TAC[])

val freesin_IMP = prove(
  ``!rhs vars.
       freesin vars rhs /\ TERM defs rhs /\ VFREE_IN (Var x ty) (hol_tm rhs) ==>
       ?oty. (hol_ty oty = ty) /\ MEM (Var x oty) vars``,
  Induct \\ SIMP_TAC (srw_ss()) [Once freesin_def,hol_tm_def]
  THEN1 (SIMP_TAC std_ss [VFREE_IN_def,term_11] \\ METIS_TAC [])
  THEN1 (REPEAT STRIP_TAC \\ IMP_RES_TAC TERM
         \\ FULL_SIMP_TAC std_ss [hol_tm_def,CLOSED_def,VFREE_IN_def])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [CLOSED_def,hol_tm_def,VFREE_IN_def]
  \\ IMP_RES_TAC TERM
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(Var s ty'::vars)`)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Q.EXISTS_TAC `oty` \\ FULL_SIMP_TAC std_ss [MEM]
  \\ FULL_SIMP_TAC (srw_ss()) [term_11]);

val IMP_CLOSED = prove(
  ``!rhs. freesin [] rhs /\ TERM defs rhs ==> CLOSED (hol_tm rhs)``,
  SIMP_TAC std_ss [CLOSED_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC freesin_IMP \\ FULL_SIMP_TAC std_ss [MEM]);

val MEM_type_vars_in_term = prove(
  ``!rhs v. TERM defs rhs /\ STATE st defs ==>
            (MEM v (type_vars_in_term rhs) = MEM v (tvars (hol_tm rhs)))``,
  Induct
  \\ SIMP_TAC (srw_ss()) [Once type_vars_in_term_def,hol_tm_def,tvars_def,tyvars_thm]
  THEN1 (FULL_SIMP_TAC std_ss [MEM_union,MEM_LIST_UNION] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC Abs_Var
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC TERM \\ FULL_SIMP_TAC std_ss [hol_tm_def,MEM_union,
       tvars_def,MEM_LIST_UNION]
  \\ IMP_RES_TAC TERM_Var \\ FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]);

val sequent_has_type_bool = prove(
  ``(d,h) |- c ⇒ EVERY (λt. t has_type Bool) (c::h)``,
  strip_tac >> imp_res_tac proves_term_ok >> fs[EVERY_MEM])

val THM_term_ok_bool = prove(
  ``THM defs (Sequent asl p) ⇒
    EVERY (λt. term_ok (sigof (hol_defs defs)) t ∧ (typeof t = Bool)) (MAP hol_tm (p::asl))``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC THM
  \\ FULL_SIMP_TAC std_ss [THM_def]
  \\ IMP_RES_TAC sequent_has_type_bool
  \\ IMP_RES_TAC proves_term_ok
  \\ FULL_SIMP_TAC std_ss [TERM_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM]
  \\ NTAC 2 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [WELLTYPED_LEMMA])

val hol_ty_is_Fun = prove(
  ``(hol_ty x = Fun y z) ⇔ ∃y0 z0. (x = Tyapp "fun" [y0;z0]) ∧ (y = hol_ty y0) ∧ (z = hol_ty z0)``,
  Cases_on`x`>>simp[hol_ty_def,MAP_EQ_2] >>
  METIS_TAC[])

val STRCAT_SHADOW_def = zDefine`
  STRCAT_SHADOW = STRCAT`

val first_dup_thm = prove(
  ``∀ls acc. (first_dup ls acc = NONE) ⇒ ALL_DISTINCT ls ∧ (∀x. MEM x ls ⇒ ¬MEM x acc)``,
  Induct >> simp[Once first_dup_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >>
  strip_tac >> res_tac >>
  fs[MEM] >> METIS_TAC[])

val new_constants_thm = prove(
  ``∀ls s res s'. (new_constants ls s = (res,s')) ⇒
      (∀u. (res = HolRes u) ∧ ALL_DISTINCT (MAP FST s.the_term_constants) ⇒
           ALL_DISTINCT (MAP FST ls ++ MAP FST s.the_term_constants) ∧
           (s' = s with the_term_constants := ls++s.the_term_constants)) ∧
      (∀msg. (res = HolErr msg) ⇒ (s' = s))``,
  simp_tac std_ss [new_constants_def,GSYM STRCAT_SHADOW_def] >>
  simp[ex_bind_def,get_the_term_constants_def] >>
  rpt gen_tac >>
  reverse BasicProvers.CASE_TAC >- (
    simp[failwith_def] >> rw[] ) >>
  imp_res_tac first_dup_thm >>
  strip_tac >>
  Cases_on`res`>>
  fs[set_the_term_constants_def] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  simp[ALL_DISTINCT_APPEND])

val new_specification_thm = store_thm("new_specification_thm",
  ``THM defs th /\ STATE s defs ==>
    case new_specification th s of
    | (HolErr msg, s') => (s' = s)
    | (HolRes th, s') => (?d. THM (d::defs) th /\
                              STATE s' (d::defs))``,
  Cases_on`th` >>
  simp_tac std_ss [new_specification_def,GSYM STRCAT_SHADOW_def] >>
  simp[ex_bind_def,ex_return_def] >>
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`(f:hol_term -> hol_refs -> (((string#hol_type)#hol_term) hol_result#hol_refs)) = X` >>
  `EVERY (λt. term_ok (hol_defs defs) t ∧ typeof t = Bool) (MAP hol_tm (h::l))` by (
    match_mp_tac THM_term_ok_bool >>
    fs[STATE_def] >>
    METIS_TAC[proves_IMP] ) >>
  `∀l defs s s'.
    STATE s defs ∧ EVERY (λt. term_ok (hol_defs defs) t ∧ typeof t = Bool) (MAP hol_tm l)
    ⇒ (∀res. map f l s = (HolRes res,s') ⇒
     (s' = s) ∧
     LIST_REL
       (λe ((s,ty),t).
         let ty = hol_ty ty in let t = hol_tm t in
         hol_tm e = Var s ty === t ∧ t has_type ty ∧
         CLOSED t ∧ (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))) ∧
         term_ok (hol_defs defs) t ∧ type_ok (hol_defs defs) ty)
       l res) ∧
     (∀msg. map f l s = (HolErr msg,s') ⇒ s' = s)` by (
    pop_assum kall_tac >> pop_assum mp_tac >> ntac 2 (pop_assum kall_tac) >> strip_tac >>
    Induct >- simp[map_def,ex_return_def] >>
    simp[Once map_def,ex_bind_def] >>
    qx_genl_tac[`tm`,`defs`] >>
    rpt gen_tac >> strip_tac >>
    Cases_on`f tm s`>>fs[]>>
    `s = r` by (
      pop_assum mp_tac >>
      simp[Abbr`f`] >>
      mp_tac(Q.GENL[`res`,`s'`]dest_eq_thm) >>
      Cases_on`dest_eq tm s`>>simp[]>>
      `TERM defs tm` by simp[TERM_def] >>
      Cases_on`q'`>>simp[]>>
      qmatch_assum_rename_tac`dest_eq tm s = (HolRes q',X)`["X"] >>
      Cases_on`q'`>>simp[] >> strip_tac >>
      BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_rename_tac`dest_eq tm s = (HolRes(v,t),s)`[] >>
      MP_TAC(Q.GENL[`res`,`s'`]dest_var_thm) >>
      Cases_on`dest_var v s`>>simp[]>>
      Cases_on`q'`>>simp[]>>
      qmatch_assum_rename_tac`dest_var v s = (HolRes q',X)`["X"]>>
      Cases_on`q'`>>simp[] >> strip_tac >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      simp[failwith_def] ) >>
    reverse conj_tac >- (
      simp[Once map_def,ex_bind_def] >>
      Cases_on`q`>>fs[]>>
      Cases_on`map f l r`>>fs[]>>
      Cases_on`q`>>simp[ex_return_def] >>
      rw[] >>
      first_x_assum(qspecl_then[`defs`,`r`]mp_tac) >>
      simp[] ) >>
    Cases_on`q`>>simp[]>>
    Cases_on`map f l r`>>simp[]>>
    Cases_on`q`>>simp[ex_return_def]>>
    strip_tac >>
    qpat_assum`f tm s = X`mp_tac >>
    simp[Abbr`f`] >>
    mp_tac(Q.GENL[`res`,`s'`]dest_eq_thm) >>
    `TERM defs tm` by simp[TERM_def] >>
    Cases_on`dest_eq tm s`>>simp[]>>
    Cases_on`q`>>rfs[]>>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`dest_eq tm s = (HolRes q,X)`["X"] >>
    Cases_on`q`>>simp[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`dest_eq tm s = (HolRes(v,t),s)`[] >>
    MP_TAC(Q.GENL[`res`,`s'`]dest_var_thm) >>
    Cases_on`dest_var v s`>>simp[]>>
    Cases_on`q`>>simp[]>>
    qmatch_assum_rename_tac`dest_var v s = (HolRes q,X)`["X"]>>
    Cases_on`q`>>simp[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    BasicProvers.CASE_TAC>>
    BasicProvers.CASE_TAC>>
    ntac 2 (pop_assum mp_tac ) >>
    simp_tac(srw_ss())[failwith_def] >>
    ntac 3 strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[] >>
    simp[Once CONJ_SYM,GSYM CONJ_ASSOC] >>
    Cases_on`v`>>TRY(
      fs[dest_var_def,failwith_def] >> NO_TAC) >>
    qpat_assum`dest_var Z X = Y`mp_tac >>
    simp[dest_var_def,ex_return_def] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    conj_tac >- (
      simp[equation_def,hol_tm_def] ) >>
    qpat_assum`dest_eq tm r = X`mp_tac >>
    Cases_on`tm`>>simp_tac(srw_ss())[dest_eq_def,failwith_def] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    simp_tac(srw_ss())[ex_return_def] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    pop_assum mp_tac >>
    simp[hol_tm_def] >> strip_tac >>
    qmatch_assum_abbrev_tac`TERM defs (Comb X Y)` >>
    `welltyped (hol_tm (Comb X Y))` by (
      fs[TERM_def] >>
      imp_res_tac term_ok_welltyped ) >>
    pop_assum mp_tac >>
    simp[hol_tm_def,Abbr`X`,Abbr`Y`] >> strip_tac >>
    fs[hol_ty_is_Fun] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[TYPE_11] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    conj_tac >- (
      fs[holSyntaxTheory.WELLTYPED] >>
      imp_res_tac holSyntaxTheory.WELLTYPED_LEMMA >>
      METIS_TAC[] ) >>
    conj_tac >- (
      simp[CLOSED_def] >>
      PROVE_TAC[freesin_IMP,MEM] ) >>
    conj_tac >- (
      fs[subset_def,EVERY_MEM] >>
      METIS_TAC[MEM_type_vars_in_term,tyvars_thm] ) >>
    conj_asm1_tac >- (
      fs[hol_tm_def,term_ok_Comb] ) >>
    conj_tac >- (
      simp[Once proves_cases] >>
      fs[WELLTYPED] >> METIS_TAC[] ) >>
    first_x_assum(qspecl_then[`defs`,`r`]mp_tac) >>
    simp[] ) >>
  first_x_assum(qspecl_then[`l`,`defs`,`s`]mp_tac) >>
  Cases_on`map f l s` >> simp[]>>
  reverse(Cases_on`q`)>>simp[] >>
  (discharge_hyps >- fs[]) >> simp[] >>
  strip_tac >>
  BasicProvers.CASE_TAC >- (
    simp[failwith_def] ) >>
  BasicProvers.CASE_TAC >>
  qspecl_then[`MAP FST a`,`s`]mp_tac new_constants_thm >>
  simp[] >>
  `ALL_DISTINCT (MAP FST s.the_term_constants)` by (
    fs[STATE_def] ) >>
  Cases_on`q`>>simp[] >>
  simp[oneTheory.one] >>
  strip_tac >>
  simp[add_def_def,ex_bind_def,get_the_definitions_def,set_the_definitions_def] >>
  qpat_assum`map f l r = X`kall_tac >>
  qunabbrev_tac`f` >>
  Q.PAT_ABBREV_TAC`theta:(hol_term#hol_term)list = MAP X (MAP FST a)` >>
  Q.PAT_ABBREV_TAC`d = Constdef X h` >>
  Q.PAT_ABBREV_TAC`s':hol_refs = X` >>
  qexists_tac`d` >>
  reverse conj_asm2_tac >- (
    fs[STATE_def,Abbr`s'`] >>
    simp[hol_defs_def,Abbr`d`] >>
    fs[consts_def,types_def,types_aux_def,consts_aux_def] >>
    qpat_assum`X = MAP Z s.the_term_constants`(assume_tac o SYM) >>
    simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
    rfs[] >>
    simp[TERM_def,hol_defs_def] >>
    conj_asm1_tac >- (
      simp[Once proves_cases] >>
      map_every qexists_tac[`[]`,`Tt`] >>
      match_mp_tac(List.nth(CONJUNCTS proves_rules,24)) >>
      simp[truth_thm] >>
      fs[THM_def] >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      Q.PAT_ABBREV_TAC`l':holSyntax$term list = MAP X a` >>
      `l' = MAP hol_tm l` by (
        simp[LIST_EQ_REWRITE,Abbr`l'`] >>
        fs[EVERY2_EVERY,EVERY_MEM] >>
        rfs[MEM_ZIP,MEM_EL,PULL_EXISTS,EL_MAP,UNCURRY] >>
        simp[equation_def] >>
        METIS_TAC[WELLTYPED_LEMMA] ) >>
      simp[EVERY_MAP] >>
      fs[EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,MEM_EL,PULL_EXISTS,EL_MAP,UNCURRY] >>
      conj_tac >- (
        rw[] >>
        qmatch_assum_abbrev_tac`(hol_defs defs,asl) |- hol_tm h` >>
        `TERM defs h` by simp[TERM_def] >>
        imp_res_tac freesin_IMP >>
        fs[MEM_MAP,MEM_EL,PULL_EXISTS] >>
        rpt BasicProvers.VAR_EQ_TAC >>
        qexists_tac`n` >>
        simp[EL_MAP] >>
        fs[UNCURRY] >>
        fs[TYPE_11] >>
        METIS_TAC[] ) >>
      qpat_assum`MAP X s.the_term_constants = Y`(ASSUME_TAC o SYM) >>
      simp[consts_def,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
      fs[MAP_MAP_o,combinTheory.o_DEF] ) >>
    conj_asm1_tac >- (
      match_mp_tac term_ok_cons >>
      simp[UNCURRY,MAP_MAP_o,combinTheory.o_DEF] >>
      fs[TERM_def] ) >>
    simp[MAP_EQ_f] >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,UNCURRY,PULL_EXISTS] >>
    simp[MEM_EL,PULL_EXISTS] >>
    METIS_TAC[term_ok_welltyped,WELLTYPED_LEMMA] ) >>
  simp[THM_def] >>
  qspecl_then[`s'`,`d::defs`,`theta`,`h`]mp_tac
    (Q.GENL[`defs`,`s`](CONV_RULE (RESORT_FORALL_CONV List.rev) vsubst_aux_thm)) >>
  simp[] >>
  match_mp_tac IMP_IMP >>
  conj_asm1_tac >- (
    reverse conj_tac >- (
      match_mp_tac (GEN_ALL TERM_CONS_EXTEND) >>
      fs[TERM_def,THM_def] >>
      METIS_TAC[] ) >>
    simp[Abbr`theta`,EVERY_MAP] >>
    simp[EVERY_MEM,UNCURRY,Once term_type_def,is_var_def] >>
    simp[Once term_type_def,TERM_Var_SIMP] >>
    ntac 2 strip_tac >>
    conj_asm1_tac >- (
      match_mp_tac (GEN_ALL TERM_Const) >>
      HINT_EXISTS_TAC >>
      simp[Abbr`s'`,MEM_MAP] >>
      METIS_TAC[] ) >>
    simp[TYPE_def] >>
    simp[Once proves_cases] >>
    fs[TERM_def,hol_tm_def] >>
    METIS_TAC[has_type_rules] ) >>
  strip_tac >> simp[] >>
  match_mp_tac(List.nth(CONJUNCTS proves_rules,25)) >>
  fs[STATE_def] >>
  qmatch_assum_abbrev_tac`Abbrev(d=Constdef eqs h)` >>
  qexists_tac`MAP (λ(s,t). (s,hol_tm t)) eqs` >>
  simp[Abbr`s'`,Abbr`d`,hol_defs_def,PULL_EXISTS] >>
  simp[Abbr`theta`,Abbr`eqs`] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,hol_tm_def] >>
  simp[MAP_EQ_f] >>
  fs[EVERY2_EVERY,EVERY_MEM,MEM_EL,PULL_EXISTS,UNCURRY] >>
  rfs[EL_ZIP,PULL_EXISTS] >>
  METIS_TAC[term_ok_welltyped,WELLTYPED_LEMMA])

val _ = delete_const"STRCAT_SHADOW"

val new_basic_definition_thm = store_thm("new_basic_definition_thm",
  ``TERM defs tm /\ STATE s defs ==>
    case new_basic_definition tm s of
    | (HolErr msg, s') => (s' = s)
    | (HolRes th, s') => (?d. (* def_ok (hol_def d) (hol_defs defs) /\ *)
                              THM (d::defs) th /\
                              STATE s' (d::defs))``,
  rw[] >>
  simp[new_basic_definition_def,ex_bind_def] >>
  Cases_on`ASSUME tm s` >>
  imp_res_tac ASSUME_thm >>
  Cases_on`q`>>fs[] >>
  imp_res_tac new_specification_thm ) |> UNDISCH

val MEM_STRING_SORT = prove(
  ``!xs x. MEM x (STRING_SORT xs) = MEM x xs``,
  Induct \\ FULL_SIMP_TAC std_ss
    [STRING_SORT_def,FOLDR,INORDER_INSERT_def,MEM_APPEND,MEM_FILTER,MEM]
  \\ REPEAT STRIP_TAC \\ Cases_on `MEM x xs` \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [stringTheory.string_lt_cases]);

val ALL_DISTINCT_STRING_SORT = prove(
  ``!xs. ALL_DISTINCT (STRING_SORT xs)``,
  Induct
  \\ FULL_SIMP_TAC std_ss [STRING_SORT_def,FOLDR,ALL_DISTINCT,INORDER_INSERT_def]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_APPEND,MEM_FILTER,MEM,MEM_APPEND,
       ALL_DISTINCT,stringTheory.string_lt_nonrefl]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ TRY (MATCH_MP_TAC FILTER_ALL_DISTINCT)
  \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [stringTheory.string_lt_antisym,stringTheory.string_lt_trans,
        stringTheory.string_lt_cases]);

val SORTED_CONS = prove(
  ``!x. SORTED $<= (x::xs) <=> SORTED $<= xs /\ !y. MEM (y:string) xs ==> x <= y``,
  Induct_on `xs` \\ FULL_SIMP_TAC std_ss [sortingTheory.SORTED_DEF,MEM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ METIS_TAC [stringTheory.string_lt_antisym,stringTheory.string_lt_trans,
        stringTheory.string_lt_cases,stringTheory.string_le_def]);

val SORTED_APPEND = prove(
  ``!xs ys.
      SORTED $<= xs /\ SORTED $<= ys /\
      (!x y. MEM x xs /\ MEM y ys ==> x <= y:string) ==> SORTED $<= (xs ++ ys)``,
  Induct \\ SIMP_TAC std_ss [sortingTheory.SORTED_DEF,MEM,APPEND]
  \\ SIMP_TAC std_ss [SORTED_CONS,MEM_APPEND] \\ METIS_TAC []);

val SORTED_FILTER = prove(
  ``!xs. SORTED $<= (xs:string list) ==> SORTED $<= (FILTER P xs)``,
  Induct \\ SIMP_TAC std_ss [sortingTheory.SORTED_DEF,FILTER]
  \\ SRW_TAC [] [SORTED_CONS,MEM_FILTER]);

val SORTED_STRING_SORT = prove(
  ``!xs. SORTED $<= (STRING_SORT xs)``,
  Induct
  \\ FULL_SIMP_TAC std_ss [STRING_SORT_def,FOLDR,ALL_DISTINCT,INORDER_INSERT_def]
  \\ FULL_SIMP_TAC std_ss [sortingTheory.SORTED_DEF,MEM_FILTER,MEM,MEM_APPEND,
       ALL_DISTINCT,stringTheory.string_lt_nonrefl]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SORTED_APPEND
  \\ REPEAT STRIP_TAC \\ TRY (MATCH_MP_TAC SORTED_APPEND)
  \\ REPEAT STRIP_TAC \\ TRY (MATCH_MP_TAC SORTED_FILTER)
  \\ FULL_SIMP_TAC std_ss [MEM_FILTER,MEM,sortingTheory.SORTED_DEF]
  \\ FULL_SIMP_TAC std_ss [stringTheory.string_le_def,MEM,MEM_APPEND,MEM_FILTER]
  \\ METIS_TAC [stringTheory.string_lt_antisym,stringTheory.string_lt_trans,
        stringTheory.string_lt_cases]);

val SORTED_EQ = prove(
  ``!xs ys. SORTED $<= xs /\ SORTED $<= (ys:string list) /\
            ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
            (!x. MEM x xs = MEM x ys) ==> (xs = ys)``,
  Induct THEN1 (Cases \\ SIMP_TAC std_ss [MEM] \\ METIS_TAC [])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [MEM] THEN1 METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [SORTED_CONS,ALL_DISTINCT,CONS_11]
  \\ NTAC 2 STRIP_TAC \\ REVERSE (`h' = h` by ALL_TAC) THEN1 METIS_TAC []
  \\ Q.PAT_ASSUM `!ys. bbb ==> (xxx = yyy)` (K ALL_TAC)
  \\ CCONTR_TAC \\ `MEM h xs /\ MEM h' t` by METIS_TAC [] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [stringTheory.string_le_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [stringTheory.string_lt_antisym,stringTheory.string_lt_trans,
        stringTheory.string_lt_cases])

val PART_LEMMA = prove(
  ``!xs t1 t2 P. (FST (PART P xs t1 t2) = REVERSE (FILTER P xs) ++ t1) /\
                 (SND (PART P xs t1 t2) = REVERSE (FILTER (\x. ~(P x)) xs) ++ t2)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [sortingTheory.PART_DEF,FILTER]
  \\ SRW_TAC [] []);

val ALL_DISTINCT_QSORT = prove(
  ``!R xs. ALL_DISTINCT xs ==> ALL_DISTINCT (QSORT R xs)``,
  HO_MATCH_MP_TAC sortingTheory.QSORT_IND
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [sortingTheory.QSORT_DEF]
  \\ Cases_on `PARTITION (\y. R y h) t` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_APPEND,ALL_DISTINCT,MEM,MEM_APPEND,
       sortingTheory.QSORT_MEM,sortingTheory.PARTITION_DEF]
  \\ (PART_LEMMA |> Q.SPECL [`t`,`[]`,`[]`,`(\y:'a. R y (h:'a))`] |> MP_TAC)
  \\ FULL_SIMP_TAC std_ss [APPEND_NIL] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_REVERSE,FILTER_ALL_DISTINCT,
       MEM_REVERSE,MEM_FILTER] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val ALL_DISTINCT_union = prove(
  ``!xs. ALL_DISTINCT (hol_kernel$union xs ys) = ALL_DISTINCT ys``,
  Induct \\ SIMP_TAC (srw_ss()) [union_def,Once itlist_def,insert_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [union_def]);

val ALL_DISTINCT_tyvars_ALT = prove(
  ``!h. ALL_DISTINCT (tyvars (h:hol_type))``,
  HO_MATCH_MP_TAC type_IND \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once hol_kernelTheory.tyvars_def]
  \\ Induct_on `tys` \\ SIMP_TAC (srw_ss()) [Once itlist_def,MAP]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_union]);

val ALL_DISTINCT_type_vars_in_term = prove(
  ``!P. ALL_DISTINCT (type_vars_in_term P)``,
  Induct \\ SIMP_TAC (srw_ss()) [Once type_vars_in_term_def]
  \\ FULL_SIMP_TAC std_ss [tyvars_ALL_DISTINCT,ALL_DISTINCT_union]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_tyvars_ALT]);

val QSORT_type_vars_in_term = prove(
  ``TERM defs P /\ STATE st defs ==>
    (QSORT $<= (type_vars_in_term P) = STRING_SORT (tvars (hol_tm P)))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC SORTED_EQ \\ STRIP_TAC THEN1
   (MATCH_MP_TAC sortingTheory.QSORT_SORTED
    \\ FULL_SIMP_TAC std_ss [relationTheory.transitive_def,relationTheory.total_def]
    \\ SRW_TAC [] [stringTheory.string_le_def]
    \\ METIS_TAC [stringTheory.string_lt_antisym,stringTheory.string_lt_trans,
        stringTheory.string_lt_cases])
  \\ FULL_SIMP_TAC std_ss [sortingTheory.QSORT_MEM]
  \\ IMP_RES_TAC MEM_type_vars_in_term
  \\ FULL_SIMP_TAC std_ss [MEM_STRING_SORT,ALL_DISTINCT_STRING_SORT,
        SORTED_STRING_SORT,tvars_ALL_DISTINCT]
  \\ MATCH_MP_TAC ALL_DISTINCT_QSORT
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_type_vars_in_term]);

val STATE_IMP_LEMMA = prove(
  ``STATE s defs ==> context_ok (hol_defs defs)``,
  FULL_SIMP_TAC std_ss [STATE_def,LET_DEF]);

val domain_type_def = Define `
  domain_type ty = term_type (Comb (Var "a" ty) ARB)`

val term_type_SIMP = prove(
  ``(domain_type (fun t1 t2) = t2) /\
    (term_type (Comb x y) = domain_type (term_type x)) /\
    (term_type (Var name ty) = ty) /\
    (term_type (Const name ty) = ty)``,
  SIMP_TAC (srw_ss()) [domain_type_def,Once term_type_def]
  \\ ONCE_REWRITE_TAC [term_type_def]
  \\ SIMP_TAC (srw_ss()) [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC (srw_ss()) [Once term_type_def]);

val get_type_arity_fun = prove(
  ``ALL_DISTINCT (MAP FST s.the_type_constants) ∧
    s.the_type_constants = types (hol_defs defs)
    ⇒ get_type_arity "fun" s = (HolRes 2,s)``,
  qspecl_then[`"fun"`,`s`]mp_tac get_type_arity_thm >>
  Cases_on`get_type_arity "fun" s`>>simp[] >>
  rw[] >>
  fs[types_def] >>
  reverse(Cases_on`q`)>>fs[]>-METIS_TAC[]>>
  rfs[ALL_DISTINCT_APPEND,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  METIS_TAC[])

val new_basic_type_definition_thm = store_thm("new_basic_type_definition_thm",
  ``THM defs th /\ STATE s defs ==>
    case new_basic_type_definition tyname absname repname th s of
    | (HolErr msg, s') => (s' = s)
    | (HolRes (th1,th2), s') => (?d. (* def_ok (hol_def d) (hol_defs defs) /\ *)
                                     THM (d::defs) th1 /\ THM (d::defs) th2 /\
                                     STATE s' (d::defs))``,
  Cases_on `th` \\ SIMP_TAC (srw_ss())
     [new_basic_type_definition_def,Once ex_bind_def,ex_return_def,failwith_def,
      can_def |> SIMP_RULE std_ss [otherwise_def,ex_bind_def,ex_return_def]]
  \\ MP_TAC (get_const_type_thm |> Q.SPECL [`absname`,`s`])
  \\ MP_TAC (get_const_type_thm |> Q.SPECL [`repname`,`s`])
  \\ Cases_on `get_const_type absname s`
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ Cases_on `get_const_type repname s`
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ Cases_on `absname = repname`
  \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def,try_def]
  \\ Cases_on `l = []` \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def,try_def]
  \\ FULL_SIMP_TAC std_ss [otherwise_def,failwith_def]
  \\ SIMP_TAC std_ss [Once dest_comb_def,failwith_def,ex_return_def]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ NTAC 3 STRIP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `THM defs (Sequent [] (Comb P x))` []
  \\ Cases_on `freesin [] P` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ IMP_RES_TAC THM \\ IMP_RES_TAC TERM
  \\ IMP_RES_TAC QSORT_type_vars_in_term \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC type_of_thm
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [new_type_def,set_the_type_constants_def,
       get_the_type_constants_def,failwith_def,can_def]
  \\ NTAC 4 (SIMP_TAC std_ss [Once ex_bind_def,ex_return_def,otherwise_def])
  \\ MP_TAC (get_type_arity_thm |> Q.SPECL [`tyname`,`s`])
  \\ Cases_on `get_type_arity tyname s` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [add_def_def,Once ex_bind_def,
        get_the_definitions_def,set_the_definitions_def]
  \\ SIMP_TAC std_ss [EVAL ``monad_unitbind x y``,Once ex_bind_def]
  \\ SIMP_TAC (srw_ss()) [mk_type_def,try_def,otherwise_def,get_type_arity_def,
       get_the_type_constants_def,Once assoc_def]
  \\ NTAC 3 (SIMP_TAC (srw_ss()) [Once ex_bind_def,ex_return_def])
  \\ SIMP_TAC (srw_ss()) [mk_fun_ty_def]
  \\ SIMP_TAC (srw_ss()) [mk_type_def,try_def,otherwise_def]
  \\ NTAC 1 (SIMP_TAC (srw_ss()) [Once ex_bind_def,ex_return_def])
  \\ Q.ABBREV_TAC `s2 = (s with
           <|the_type_constants :=
               (tyname,LENGTH (STRING_SORT
                   (tvars (hol_tm P))))::s.the_type_constants;
             the_definitions :=
               Typedef tyname P absname repname::s.the_definitions|>)`
  \\ `get_type_arity "fun" s2 = (HolRes 2, s2)` by (
    match_mp_tac (GEN_ALL get_type_arity_fun) >>
    fs[STATE_def,Abbr`s2`] >>
    qexists_tac`Typedef tyname P absname repname::s.the_definitions` >>
    fs[hol_defs_def,types_def,types_aux_def] >> rfs[] >>
    simp[MEM_MAP,FORALL_PROD] >>
    METIS_TAC[] )
  \\ FULL_SIMP_TAC (srw_ss()) [o_DEF,Once ex_bind_def,Once new_constant_def]
  \\ POP_ASSUM (K ALL_TAC)
  \\ NTAC 3 (FULL_SIMP_TAC (srw_ss()) [o_DEF,Once ex_bind_def,can_def,otherwise_def])
  \\ MP_TAC (get_const_type_thm |> Q.SPECL [`repname`,`s2`])
  \\ Cases_on `get_const_type repname s2` \\ FULL_SIMP_TAC std_ss [ex_return_def]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (Q.UNABBREV_TAC `s2` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [get_the_term_constants_def,Once ex_bind_def,
       set_the_term_constants_def]
  \\ FULL_SIMP_TAC (srw_ss()) [get_the_term_constants_def,Once mk_const_def]
  \\ FULL_SIMP_TAC (srw_ss()) [try_def,Once ex_bind_def,ex_return_def,otherwise_def]
  \\ FULL_SIMP_TAC (srw_ss()) [get_const_type_def]
  \\ NTAC 2 (FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def,get_the_term_constants_def])
  \\ FULL_SIMP_TAC (srw_ss()) [Once assoc_def,ex_return_def]
  \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ Q.ABBREV_TAC `s3 = (s2 with
           the_term_constants :=
             (repname,
              fun (Tyapp tyname (MAP Tyvar (STRING_SORT (tvars (hol_tm P)))))
                (term_type x))::s2.the_term_constants)`
  \\ `get_type_arity "fun" s3 = (HolRes 2,s3)` by ALL_TAC THEN1
   (MATCH_MP_TAC (GEN_ALL get_type_arity_fun) >>
    fs[STATE_def,Abbr`s3`,Abbr`s2`] >>
    qexists_tac`Typedef tyname P absname repname::s.the_definitions` >>
    fs[hol_defs_def,types_def,types_aux_def] >> rfs[] >>
    simp[MEM_MAP,FORALL_PROD] >>
    METIS_TAC[] )
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC (srw_ss()) [o_DEF,Once ex_bind_def,Once new_constant_def]
  \\ NTAC 3 (FULL_SIMP_TAC (srw_ss()) [o_DEF,Once ex_bind_def,can_def,otherwise_def])
  \\ MP_TAC (get_const_type_thm |> Q.SPECL [`absname`,`s3`])
  \\ Cases_on `get_const_type absname s3` \\ FULL_SIMP_TAC std_ss [ex_return_def]
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (STRIP_TAC \\ `F` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `s3` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `s2` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC (srw_ss()) [get_the_term_constants_def,Once ex_bind_def,
       set_the_term_constants_def]
  \\ FULL_SIMP_TAC (srw_ss()) [get_the_term_constants_def,Once mk_const_def]
  \\ FULL_SIMP_TAC std_ss [type_subst_EMPTY,mk_var_def]
  \\ FULL_SIMP_TAC (srw_ss()) [try_def,Once ex_bind_def,ex_return_def,otherwise_def]
  \\ FULL_SIMP_TAC (srw_ss()) [try_def,Once ex_bind_def,ex_return_def,otherwise_def]
  \\ FULL_SIMP_TAC (srw_ss()) [get_const_type_def]
  \\ NTAC 2 (FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def,get_the_term_constants_def])
  \\ FULL_SIMP_TAC (srw_ss()) [Once assoc_def,ex_return_def]
  \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ Q.ABBREV_TAC `s4 = (s3 with
       the_term_constants :=
         (absname,
          fun (term_type x)
            (Tyapp tyname (MAP Tyvar (STRING_SORT (tvars (hol_tm P))))))::
             s3.the_term_constants)`
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once mk_comb_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ SIMP_TAC (srw_ss()) [Once type_of_def,ex_return_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ SIMP_TAC (srw_ss()) [Once type_of_def,ex_return_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ SIMP_TAC (srw_ss()) [Once mk_comb_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ SIMP_TAC (srw_ss()) [Once type_of_def,ex_return_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ SIMP_TAC (srw_ss()) [Once type_of_def,ex_return_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ SIMP_TAC (srw_ss()) [Once type_of_def,ex_return_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ SIMP_TAC (srw_ss()) [Once dest_type_def,ex_return_def]
  \\ ASM_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ `tyname <> "bool" /\ tyname <> "ind" /\ tyname <> "fun" /\
      absname <> "=" /\ absname <> "@" /\
      repname <> "=" /\ repname <> "@"` by ALL_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [STATE_def,LET_DEF,hol_defs_def,hol_def_def]
    \\ Q.PAT_ASSUM `defs = xxx` ASSUME_TAC
    \\ Q.PAT_ASSUM `s.the_type_constants = xxx` ASSUME_TAC
    \\ Q.PAT_ASSUM `xxx = MAP yyy s.the_term_constants` ASSUME_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND,MEM_MAP,FORALL_PROD,PULL_EXISTS]
    \\ fs[types_def,consts_def] >>
    rpt (conj_tac >- METIS_TAC[]) >>
    qmatch_assum_abbrev_tac`l1 ++ l2 = MAP f s.the_term_constants` >>
    `∃ty1 ty2. MEM ("@",ty1) (MAP f s.the_term_constants) ∧ MEM ("=",ty2) (MAP f s.the_term_constants)` by (
      qpat_assum`X = MAP f Y`(assume_tac o SYM) >>
      simp[Abbr`l2`] >> PROVE_TAC[] ) >>
    fs[MEM_MAP,Abbr`f`,FORALL_PROD,EXISTS_PROD] >>
    METIS_TAC[] ) >>
  (*
  \\ `def_ok (hol_def (Typedef tyname P absname repname)) (hol_defs defs)` by ALL_TAC
  THEN1
   (FULL_SIMP_TAC std_ss [hol_def_def,hol_defs_def,HD,def_ok,MEM]
    \\ IMP_RES_TAC TERM \\ IMP_RES_TAC term_type \\ IMP_RES_TAC IMP_CLOSED
    \\ FULL_SIMP_TAC std_ss [TERM_def,welltyped_in,WELLTYPED_CLAUSES,
         hol_tm_def,domain,ALL_DISTINCT_APPEND]
    \\ FULL_SIMP_TAC (srw_ss()) [STATE_def,LET_DEF,hol_defs_def,
         context_ok,hol_def_def]
    \\ Q.PAT_ASSUM `defs = xxx` ASSUME_TAC
    \\ Q.PAT_ASSUM `s.the_type_constants = xxx` ASSUME_TAC
    \\ Q.PAT_ASSUM `s.the_term_constants = xxx` ASSUME_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND,MEM_MAP,FORALL_PROD,
         PULL_EXISTS,type_11]
    \\ FULL_SIMP_TAC std_ss [THM_def]
    \\ IMP_RES_TAC THM_LEMMA
    \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ FULL_SIMP_TAC std_ss [hol_tm_def,typeof,codomain])
  *)
  `(hol_defs defs,[]) |- Comb (hol_tm P) (hol_tm x)` by ( fs[THM_def,hol_tm_def] ) >>
  `CLOSED (hol_tm P)` by (
    simp[CLOSED_def] >>
    imp_res_tac freesin_IMP >>
    fs[] ) >>
  `Comb (hol_tm P) (hol_tm x) has_type Bool` by (
    imp_res_tac sequent_has_type_bool >> fs[] ) >>
  pop_assum mp_tac >> simp[Once has_type_cases] >> strip_tac >>
  `(hol_def(Typedef tyname P absname repname) :: hol_defs defs,[]) |- Comb (hol_tm P) (hol_tm x)` by (
      match_mp_tac(List.nth(CONJUNCTS proves_rules,26)) >>
      simp[hol_def_def,hol_defs_def] >>
      HINT_EXISTS_TAC >>
      HINT_EXISTS_TAC >>
      simp[] >>
      fs[STATE_def,MEM_MAP,FORALL_PROD] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rfs[] ) >>
  `tyname ∉ set (MAP FST (types (hol_defs defs)))` by (
      rfs[STATE_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rfs[MEM_MAP,FORALL_PROD] ) >>
  `absname ∉ set (MAP FST (consts (hol_defs defs)))` by (
      rfs[STATE_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rfs[MEM_MAP,FORALL_PROD] ) >>
  `repname ∉ set (MAP FST (consts (hol_defs defs)))` by (
      rfs[STATE_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rfs[MEM_MAP,FORALL_PROD] ) >>
  `STATE s4 (Typedef tyname P absname repname :: defs)` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `s4` \\ Q.UNABBREV_TAC `s3` \\ Q.UNABBREV_TAC `s2`
    \\ FULL_SIMP_TAC (srw_ss()) [STATE_def,LET_DEF,hol_defs_def,hol_def_def] >>
    conj_asm1_tac >- (
      simp[Once proves_cases] >>
      rfs[STATE_def] >>
      PROVE_TAC[] ) >>
    conj_tac >- (
      fs[types_def,types_aux_def] ) >>
    conj_tac >- rfs[STATE_def] >>
    conj_tac >- (
      rfs[STATE_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rfs[MEM_MAP,FORALL_PROD] ) >>
    conj_tac >- (
      simp[TERM_def,hol_defs_def] >>
      match_mp_tac term_ok_cons >>
      rfs[TERM_def,STATE_def] ) >>
    rfs[STATE_def,consts_def,consts_aux_def,LET_THM,hol_ty_def] >>
    simp[MAP_MAP_o,combinTheory.o_DEF,hol_ty_def] >>
    simp_tac(srw_ss()++boolSimps.ETA_ss)[] >>
    imp_res_tac WELLTYPED_LEMMA >>
    simp[] >>
    PROVE_TAC[term_type] )
  \\ Q.ABBREV_TAC `dd = Typedef tyname P absname repname`
  \\ Q.ABBREV_TAC `abs = (Const absname
            (fun (term_type x)
               (Tyapp tyname (MAP Tyvar (STRING_SORT (tvars (hol_tm P)))))))`
  \\ Q.ABBREV_TAC `rep = (Const repname
               (fun (Tyapp tyname (MAP Tyvar (STRING_SORT (tvars (hol_tm P)))))
                  (term_type x)))`
  \\ Q.ABBREV_TAC
       `(aa:hol_term) = Var "a" (Tyapp tyname
          (MAP Tyvar (STRING_SORT (tvars (hol_tm P)))))`
  \\ Q.ABBREV_TAC `(aaty:hol_type) =
        Tyapp tyname (MAP Tyvar (STRING_SORT (tvars (hol_tm P))))`
  \\ `term_type abs = (fun (term_type x) aaty)` by ALL_TAC THEN1
        (Q.UNABBREV_TAC `abs` \\ SIMP_TAC (srw_ss()) [Once term_type_def])
  \\ `term_type rep = (fun aaty (term_type x))` by ALL_TAC THEN1
        (Q.UNABBREV_TAC `rep` \\ SIMP_TAC (srw_ss()) [Once term_type_def])
  \\ `term_type aa = aaty` by ALL_TAC THEN1
        (Q.UNABBREV_TAC `aa` \\ SIMP_TAC (srw_ss()) [Once term_type_def])
  \\ `term_type P = fun (term_type x) bool_ty` by ALL_TAC THEN1
   (IMP_RES_TAC term_type >>
    imp_res_tac WELLTYPED_LEMMA >>
    `hol_ty (fun (term_type x) bool_ty) = Fun dty Bool` by (
      simp[hol_ty_def] ) >>
    PROVE_TAC[TYPE_11] ) >>
  `hol_ty (term_type x) = dty` by (
    imp_res_tac WELLTYPED_LEMMA >>
    imp_res_tac term_type >>
    rw[] ) >>
  `(hol_defs (dd::defs),[]) |- (hol_tm(Comb abs(Comb rep aa)) === hol_tm aa)` by (
    simp[hol_defs_def,Abbr`dd`] >>
    MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,26)) >>
    simp[] >>
    Q.LIST_EXISTS_TAC[`"a"`,`hol_ty (term_type x)`,`hol_tm x`] >>
    simp[hol_tm_def,Abbr`abs`,hol_ty_def,Abbr`aa`,Abbr`aaty`,equation_def,Abbr`rep`] >>
    simp_tac(srw_ss()++boolSimps.ETA_ss)[MAP_MAP_o,combinTheory.o_DEF,hol_ty_def] >>
    PROVE_TAC[] ) >>
  qabbrev_tac`rr = Var "r" (term_type x)` >>
  `(hol_defs (dd::defs),[]) |- (hol_tm(Comb P rr) ===
                                hol_tm(Comb rep (Comb abs rr)) ===
                                hol_tm(rr))` by (
    simp[hol_defs_def,Abbr`dd`] >>
    MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,26)) >>
    simp[] >>
    Q.LIST_EXISTS_TAC[`"r"`,`hol_ty (term_type x)`,`hol_tm x`] >>
    simp[hol_tm_def,Abbr`abs`,hol_ty_def,Abbr`aa`,Abbr`aaty`,equation_def,Abbr`rep`,Abbr`rr`] >>
    simp_tac(srw_ss()++boolSimps.ETA_ss)[MAP_MAP_o,combinTheory.o_DEF,hol_ty_def] ) >>
  `TERM (dd::defs) abs /\ TERM (dd::defs) rep /\ TERM (dd::defs) aa` by
   (simp[TERM_def] >>
    fs[hol_tm_def] >>
    qmatch_assum_abbrev_tac`(d,h) |- lhs === hol_tm aa` >>
    `term_ok d (lhs === hol_tm aa)` by (
      MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,11)) >>
      qexists_tac`h` >>simp[Abbr`h`] ) >>
    fs[term_ok_equation,Abbr`lhs`,term_ok_Comb] )
  \\ STRIP_TAC
  \\ MP_TAC (mk_eq_thm |> Q.GENL [`s'`,`res`] |> Q.INST
      [`s`|->`s4`,`x`|->`Comb abs (Comb rep aa)`,`y`|->`aa`,`defs`|->`dd::defs`])
  \\ Cases_on `mk_eq (Comb abs (Comb rep aa),aa) s4` \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ (b1 /\ b ==> b2) ==> ((b ==> b1) ==> b2)``)
  \\ STRIP_TAC THEN1
    (FULL_SIMP_TAC (srw_ss()) [TERM_Comb,term_type_SIMP,hol_ty_def,type_11])
  \\ STRIP_TAC \\ REVERSE (Cases_on `q`) THEN1
   (FULL_SIMP_TAC (srw_ss()) [term_type_SIMP]
    \\ Q.PAT_ASSUM `xx <> (yy:hol_type)` MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [term_type_SIMP])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  >> `TERM (dd::defs) rr` by (
    simp[TERM_def] >>
    qmatch_assum_abbrev_tac`(d,h) |- A === B === C` >>
    `term_ok d (A === B === C)` by (
      MATCH_MP_TAC(List.nth(CONJUNCTS proves_rules,11)) >>
      qexists_tac`h` >>simp[Abbr`h`] ) >>
    fs[term_ok_equation] )
  \\ MP_TAC (mk_comb_thm |> Q.GENL [`s1`,`res`] |> Q.INST
      [`s`|->`s4`,`f`|->`abs`,`a`|->`rr`,`defs`|->`dd::defs`])
  \\ Cases_on `mk_comb (abs,rr) s4` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ REVERSE (Cases_on `q`) THEN1
   (FULL_SIMP_TAC (srw_ss()) [term_type_SIMP]
    \\ Q.PAT_ASSUM `xx <> (yy:hol_type)` MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [term_type_SIMP,Abbr`rr`])
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ MP_TAC (mk_comb_thm |> Q.GENL [`s1`,`res`] |> Q.INST
      [`s`|->`s4`,`f`|->`rep`,`a`|->`Comb abs rr`,
       `defs`|->`dd::defs`])
  \\ Cases_on `mk_comb (rep,Comb abs rr) s4`
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ REVERSE (Cases_on `q`) THEN1
   (FULL_SIMP_TAC (srw_ss()) [term_type_SIMP]
    \\ Q.PAT_ASSUM `xx <> (yy:hol_type)` MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [term_type_SIMP,Abbr`rr`])
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ MP_TAC (mk_comb_thm |> Q.GENL [`s1`,`res`] |> Q.INST
      [`s`|->`s4`,`f`|->`P`,`a`|->`rr`,`defs`|->`dd::defs`])
  \\ Cases_on `mk_comb (P,rr) s4`
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ (b1 /\ b ==> b2) ==> ((b ==> b1) ==> b2)``)
  \\ STRIP_TAC THEN1 (IMP_RES_TAC TERM_CONS_EXTEND)
  \\ STRIP_TAC \\ REVERSE (Cases_on `q`) THEN1
   (FULL_SIMP_TAC (srw_ss()) [term_type_SIMP,Abbr`rr`])
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ MP_TAC (mk_eq_thm |> Q.GENL [`s'`,`res`] |> Q.INST
      [`s`|->`s4`,`x`|->`Comb rep (Comb abs rr)`,
       `y`|->`rr`,`defs`|->`dd::defs`])
  \\ Cases_on `(mk_eq
       (Comb rep (Comb abs rr), rr) s4)` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ REVERSE (Cases_on `q`) THEN1
   (FULL_SIMP_TAC (srw_ss()) [term_type_SIMP,Abbr`rr`]
    \\ Q.PAT_ASSUM `xx <> (yy:hol_type)` MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [term_type_SIMP])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.PAT_ABBREV_TAC `(rhs:hol_term) = Comb
          (Comb (Const "=" tyy) xx) yy`
  \\ FULL_SIMP_TAC (srw_ss()) [Once ex_bind_def]
  \\ MP_TAC (mk_eq_thm |> Q.GENL [`s'`,`res`] |> Q.INST
      [`s`|->`s4`,`x`|->`Comb P rr`,
       `y`|->`rhs`,`defs`|->`dd::defs`])
  \\ Cases_on `mk_eq (Comb P rr,rhs) s4`
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ (b1 /\ b ==> b2) ==> ((b ==> b1) ==> b2)``)
  \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `rhs`
    \\ FULL_SIMP_TAC (srw_ss()) [term_type_SIMP,TERM_Comb,hol_ty_def,type_11,LET_THM]
    \\ IMP_RES_TAC term_type
    \\ REPEAT BasicProvers.VAR_EQ_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [term_type_SIMP,TERM_Comb,hol_ty_def,type_11,LET_THM,Abbr`rr`]
    >> simp_tac(srw_ss())[TERM_def,hol_tm_def,hol_ty_def]
    >> fs[TYPE_def] )
  \\ STRIP_TAC \\ REVERSE (Cases_on `q`) THEN1
   (Q.UNABBREV_TAC `rhs`
    \\ FULL_SIMP_TAC (srw_ss()) [term_type_SIMP]
    \\ Q.PAT_ASSUM `xx <> (yy:hol_type)` MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [term_type_SIMP])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `Typedef tyname P absname repname`
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [THM_def,MAP] >>
  qpat_assum`(X,Z) |- Y`mp_tac >>
  qpat_assum`(X,Z) |- Y`mp_tac >>
  qmatch_abbrev_tac`holSyntax$|- H c1 ⇒ H |- c2 ⇒ H |- c3 ∧ H |- c4` >>
  qsuff_tac`c1 = c3 ∧ c2 = c4`>-rw[] >>
  conj_tac >- (
    simp[Abbr`c1`,Abbr`c3`,hol_tm_def,hol_ty_def] >>
    imp_res_tac term_type >>
    asm_simp_tac std_ss [hol_tm_def] >>
    simp_tac std_ss [GSYM equation_def] ) >>
  simp[Abbr`c2`,Abbr`c4`,hol_tm_def,hol_ty_def,Abbr`rhs`] >>
  imp_res_tac term_type >>
  asm_simp_tac std_ss [hol_tm_def] >>
  simp_tac std_ss [GSYM equation_def])

val _ = export_theory();
