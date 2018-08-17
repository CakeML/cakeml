open HolKernel Parse boolLib bossLib;
open lcsymtacs preamble boolSimps

open cmlPtreeConversionTheory
open gramPropsTheory

val _ = new_theory "cmlPtreeConversionProps";
val _ = set_grammar_ancestry ["cmlPtreeConversion", "gramProps"]

val _ = export_rewrites ["option.OPTION_IGNORE_BIND_def"]
(* " *)

(* a function for mapping types back to ASTs, used to check that the
   conversion functions are doing something reasonable *)

(* first, capture those types that we expect to be in the range of the
   conversion *)
val user_expressible_tyname_def = Define‘
  (user_expressible_tyname (Short s) ⇔ T) ∧
  (user_expressible_tyname (Long m (Short s)) ⇔ T) ∧
  (user_expressible_tyname _ ⇔ F)
’;
val _ = augment_srw_ss [rewrites [user_expressible_tyname_def]]

val _ = temp_overload_on ("ND", “λn. Nd (mkNT n, ARB)”)
val _ = temp_overload_on ("LF", “λt. Lf (TOK t, ARB)”)
val tyname_to_AST_def = Define‘
  tyname_to_AST (Short n) = ND nTyOp [ND nUQTyOp [LF (AlphaT n)]] ∧
  tyname_to_AST (Long md (Short n)) = ND nTyOp [LF (LongidT md n)] ∧
  tyname_to_AST _ = ARB
’;

val tyname_inverted = Q.store_thm(
  "tyname_inverted",
  ‘∀id. user_expressible_tyname id ⇒
        ptree_Tyop (tyname_to_AST id) = SOME id’,
  Cases >>
  simp[ptree_Tyop_def, tyname_to_AST_def, ptree_UQTyop_def] >>
  rename [‘Long m j’] >> Cases_on ‘j’ >>
  simp[ptree_Tyop_def, tyname_to_AST_def, ptree_UQTyop_def]);

val tyname_validptree = Q.store_thm(
  "tyname_validptree",
  ‘∀id. user_expressible_tyname id ⇒
          valid_ptree cmlG (tyname_to_AST id) ∧
          ptree_head (tyname_to_AST id) = NN nTyOp’,
  Cases >> simp[tyname_to_AST_def, cmlG_FDOM, cmlG_applied] >>
  rename [‘Long m j’] >> Cases_on ‘j’ >>
  simp[tyname_to_AST_def, cmlG_applied, cmlG_FDOM]);


val user_expressible_type_def = tDefine "user_expressible_type" ‘
  (user_expressible_type (Atvar _) ⇔ T) ∧
  (user_expressible_type (Atapp tys tycon) ⇔
     EVERY user_expressible_type tys ∧
     user_expressible_tyname tycon) ∧
  (user_expressible_type (Attup tys) ⇔
     EVERY user_expressible_type tys ∧ 2 ≤ LENGTH tys) ∧
  (user_expressible_type (Atfun dty rty) ⇔
     user_expressible_type dty ∧ user_expressible_type rty)
’ (WF_REL_TAC ‘measure ast$ast_t_size’ >> simp[] >> conj_tac >> rpt gen_tac >>
   Induct_on ‘tys’ >>
   dsimp[astTheory.ast_t_size_def] >> rpt strip_tac >> res_tac  >> simp[]);
val _ = augment_srw_ss [rewrites [
           SIMP_RULE (srw_ss() ++ ETA_ss) [] user_expressible_type_def]]

val type_to_AST_def = tDefine "type_to_AST" ‘
  type_to_AST (Atvar s) (* : (token,MMLnonT,unit) parsetree *) =
    ND nType [ND nPType [ND nDType [ND nTbase [LF (TyvarT s)]]]] ∧
  (type_to_AST (Atfun dty rty) =
   ND nType [
     ND nPType [ND nDType [ND nTbase [LF LparT; type_to_AST dty; LF RparT]]];
     LF ArrowT;
     ND nType [
       ND nPType [ND nDType [ND nTbase [LF LparT; type_to_AST rty; LF RparT]]]
     ]
   ]) ∧
  (type_to_AST (Atapp tys id) =
     let
       tyop = tyname_to_AST id
     in
       case tys of
           [] => ND nType [ND nPType [ND nDType [ND nTbase [tyop]]]]
         | [ty] =>
           ND nType [
             ND nPType [
               ND nDType [
                 ND nDType [ND nTbase [LF LparT; type_to_AST ty; LF RparT]];
                 tyop
               ]
             ]
           ]
         | ty1::tyrest =>
           ND nType [
             ND nPType [
               ND nDType [
                 ND nTbase [
                   LF LparT;
                   ND nTypeList2 [
                     type_to_AST ty1; LF CommaT;
                     typel_to_AST tyrest
                   ];
                   LF RparT;
                   tyop
                 ]
               ]
             ]
           ]) ∧
  (type_to_AST (Attup tys) = ND nType [typel_to_AST_PType tys]) ∧

  typel_to_AST [] = ARB ∧
  typel_to_AST [ty] = ND nTypeList1 [type_to_AST ty] ∧
  typel_to_AST (ty1::tyrest) = ND nTypeList1 [type_to_AST ty1; LF CommaT;
                                              typel_to_AST tyrest] ∧

  typel_to_AST_PType [] = ARB ∧
  typel_to_AST_PType [ty] =
    ND nPType [ND nDType [ND nTbase [LF LparT; type_to_AST ty; LF RparT]]] ∧
  typel_to_AST_PType (ty::tys) =
    ND nPType [ND nDType [ND nTbase [LF LparT; type_to_AST ty; LF RparT]];
               LF StarT;
               typel_to_AST_PType tys]
’ (WF_REL_TAC
     ‘measure (λs. case s of INL ty => ast_t_size ty
                           | INR (INL tyl) => ast_t1_size tyl
                           | INR (INR tyl) => ast_t1_size tyl)’)

val destTyvarPT_tyname_to_AST = Q.store_thm(
  "destTyvarPT_tyname_to_AST",
  ‘∀i. user_expressible_tyname i ⇒ destTyvarPT (tyname_to_AST i) = NONE’,
  Cases >> simp[tyname_to_AST_def] >>
  rename [‘Long _ j’] >> Cases_on ‘j’ >>
  simp[tyname_to_AST_def]);

val _ = temp_type_abbrev ("PT", “:(token,MMLnonT,α) parsetree”);

val types_inverted = Q.store_thm(
  "types_inverted",
  ‘(∀ty.
     user_expressible_type ty ⇒
       ptree_Type nType (type_to_AST ty : α PT) = SOME ty ∧
       valid_ptree cmlG (type_to_AST ty : α PT) ∧
       ptree_head (type_to_AST ty : α PT) = NN nType) ∧
   (∀tys.
     EVERY user_expressible_type tys ∧ tys ≠ [] ⇒
       ptree_TypeList1 (typel_to_AST tys : α PT) = SOME tys ∧
       valid_ptree cmlG (typel_to_AST tys : α PT) ∧
       ptree_head (typel_to_AST tys : α PT) = NN nTypeList1) ∧
   (∀tys.
     EVERY user_expressible_type tys ∧ tys ≠ [] ⇒
       ptree_PType (typel_to_AST_PType tys : α PT) = SOME tys ∧
       valid_ptree cmlG (typel_to_AST_PType tys : α PT) ∧
       ptree_head (typel_to_AST_PType tys : α PT) = NN nPType)’,
  ho_match_mp_tac (theorem "type_to_AST_ind") >>
  rpt conj_tac >> simp[]
  >- simp[ptree_Type_def, type_to_AST_def, tuplify_def, cmlG_FDOM, cmlG_applied]
  >- (rpt gen_tac >> ntac 2 strip_tac >> rename [‘Atfun dty rty’] >>
      simp[type_to_AST_def] >> fs[] >>
      dsimp[ptree_Type_def, tokcheck_def, tuplify_def, cmlG_FDOM, cmlG_applied])
  >- (rpt gen_tac >> ntac 2 strip_tac >>
      rename [‘Atapp args tycon’] >>
      simp[type_to_AST_def] >> Cases_on ‘args’ >> simp[]
      >- simp[Ntimes ptree_Type_def 5, tuplify_def,
              destTyvarPT_tyname_to_AST, tyname_inverted,
              tyname_validptree, cmlG_applied, cmlG_FDOM] >>
      fs[] >>
      rename [‘tl = []’] >> Cases_on ‘tl’
      >- (simp[ptree_Type_def, tuplify_def,
               destTyvarPT_tyname_to_AST, tyname_inverted,
               tokcheck_def, cmlG_FDOM, cmlG_applied, tyname_validptree] >>
          dsimp[tyname_validptree, cmlG_applied, cmlG_FDOM]) >>
      fs[] >>
      simp[Ntimes ptree_Type_def 6, tokcheck_def, cmlG_FDOM,
           cmlG_applied] >>
      dsimp[tyname_inverted, tuplify_def, tyname_validptree,
            cmlG_applied, cmlG_FDOM])
  >- (gen_tac >> rename [‘Attup args’] >> ntac 2 strip_tac >>
      simp[type_to_AST_def, Ntimes ptree_Type_def 1] >>
      ‘args ≠ []’ by (strip_tac >> fs[]) >> fs[] >>
      simp[cmlG_applied, cmlG_FDOM] >>
      ‘∃x y xs. args = x::y::xs’
        by (Cases_on ‘args’ >> fs[] >> rename [‘2 ≤ SUC (LENGTH rest)’] >>
            Cases_on ‘rest’ >> fs[]) >>
      simp[tuplify_def])
  >- (simp[type_to_AST_def, cmlG_FDOM, cmlG_applied, Once ptree_Type_def])
  >- (simp[type_to_AST_def] >> rpt strip_tac >> fs[] >>
      simp[ptree_Type_def, tokcheck_def, cmlG_applied, cmlG_FDOM])
  >- (simp[type_to_AST_def] >>
      dsimp[ptree_Type_def, tokcheck_def, cmlG_applied, cmlG_FDOM])
  >- (simp[type_to_AST_def] >> rpt strip_tac >>
      dsimp[Ntimes ptree_Type_def 6, tokcheck_def,
            cmlG_FDOM, cmlG_applied]));

val type_to_AST_injection = Q.store_thm(
  "type_to_AST_injection",
  ‘INJ type_to_AST
       { t | user_expressible_type t }
       { ast | valid_ptree cmlG ast ∧ ptree_head ast = NN nType }’,
  simp[INJ_DEF] >> metis_tac[types_inverted, SOME_11]);

val ptree_Type_surjection = Q.store_thm(
  "ptree_Type_surjection",
  ‘∀t. user_expressible_type t ⇒
       ∃pt. valid_ptree cmlG pt ∧ ptree_head pt = NN nType ∧
            ptree_Type nType pt = SOME t’,
  metis_tac[types_inverted]);

val ptree_head_TOK = Q.store_thm(
  "ptree_head_TOK",
  `(ptree_head pt = TOK sym ⇔ ?l. pt = Lf (TOK sym,l)) ∧
    (TOK sym = ptree_head pt ⇔ ?l. pt = Lf (TOK sym,l))`,
  Cases_on `pt` >> Cases_on`p` >> simp[] >> metis_tac[]);
val _ = export_rewrites ["ptree_head_TOK"]

val start =
  Cases_on `pt` >> Cases_on `p` >> simp[]
  >- (rw[] >> fs[]) >>
  strip_tac >> rveq >> fs[cmlG_FDOM, cmlG_applied, MAP_EQ_CONS] >>
  rveq >> fs[MAP_EQ_CONS] >> rveq

val UQTyOp_OK = Q.store_thm(
  "UQTyOp_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nUQTyOp) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃utyop. ptree_UQTyop pt = SOME utyop`,
  start >> simp[ptree_UQTyop_def, tokcheck_def]);

val TyOp_OK = Q.store_thm(
  "TyOp_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTyOp) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyop. ptree_Tyop pt = SOME tyop ∧ user_expressible_tyname tyop`,
  start >> simp[ptree_Tyop_def] >>
  asm_match `valid_ptree cmlG pt'` >>
  `destLf pt' = NONE`
    by (Cases_on `pt'` >> fs[MAP_EQ_CONS] >> rename [`Lf tokloc`] >>
        Cases_on `tokloc` >>
        rveq >> fs[] >> rveq >> fs[]) >>
  dsimp[] >> metis_tac [UQTyOp_OK]);

val TyvarN_OK = Q.store_thm(
  "TyvarN_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTyvarN) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyvn. ptree_TyvarN pt = SOME tyvn`,
  start >> simp[ptree_TyvarN_def]);

val TyVarList_OK = Q.store_thm(
  "TyVarList_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTyVarList) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyvnms. ptree_linfix nTyVarList CommaT ptree_TyvarN pt = SOME tyvnms`,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >> conj_tac >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM, Once FORALL_PROD] >>
  rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) []
  >- (simp[ptree_linfix_def] >> metis_tac [TyvarN_OK]) >>
  simp_tac (srw_ss()) [Once ptree_linfix_def] >>
  fs[MAP_EQ_APPEND, MAP_EQ_CONS, tokcheck_def] >> rveq >>
  metis_tac [TyvarN_OK]);

val TypeName_OK = Q.store_thm(
  "TypeName_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTypeName) ∧
    MAP TOK toks = ptree_fringe pt ⇒
    ∃tn. ptree_TypeName pt = SOME tn`,
  start >> simp[ptree_TypeName_def, tokcheck_def] >| [
    metis_tac[UQTyOp_OK],
    full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_CONS, MAP_EQ_APPEND] >>
    metis_tac[UQTyOp_OK, TyVarList_OK],
    metis_tac[UQTyOp_OK]
  ]);

val tuplify_OK = Q.store_thm(
  "tuplify_OK",
  `tl <> [] ⇒
   ∃t. tuplify tl = SOME t ∧
       (EVERY user_expressible_type tl ⇒ user_expressible_type t)`,
  strip_tac >>
  `∃h tl0. tl = h::tl0` by (Cases_on `tl` >> fs[]) >>
  Cases_on `tl0` >> simp[tuplify_def]);

val Type_OK0 = Q.store_thm(
  "Type_OK0",
  `valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
    (N ∈ {nType; nDType; nTbase} ∧
     ptree_head pt = NT (mkNT N)
       ⇒
     ∃t. ptree_Type N pt = SOME t ∧ user_expressible_type t) ∧
    (ptree_head pt = NT (mkNT nPType) ⇒
     ∃tl. ptree_PType pt = SOME tl ∧ tl <> [] ∧
          EVERY user_expressible_type tl) ∧
    (ptree_head pt = NT (mkNT nTypeList1) ⇒
     ∃tl. ptree_TypeList1 pt = SOME tl ∧ EVERY user_expressible_type tl) ∧
    (ptree_head pt = NT (mkNT nTypeList2) ⇒
     ∃tl. ptree_Typelist2 pt = SOME tl ∧ EVERY user_expressible_type tl)`,
  map_every qid_spec_tac [`N`, `toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >>
  dsimp[] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >>
  rveq >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  simp[Once ptree_Type_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, tokcheck_def]
  >- metis_tac[tuplify_OK]
  >- (dsimp[] >> metis_tac[tuplify_OK])
  >- (dsimp[] >> metis_tac[TyOp_OK])
  >- metis_tac[]
  >- (rename1 `ptree_head pt'` >>
      `destTyvarPT pt' = NONE`
        by (Cases_on `pt'` >> fs[] >> rename[`Lf p`] >> Cases_on `p` >>
            fs[] >> fs[]) >>
      dsimp[] >> metis_tac[TyOp_OK])
  >- (dsimp[] >> metis_tac [TyOp_OK])
  >- metis_tac[]
  >- (dsimp[] >> metis_tac[])
  >- (dsimp[] >> metis_tac[])
  >- (dsimp[] >> metis_tac[])
  >- (dsimp[] >> metis_tac[])
  >- (dsimp[] >> metis_tac[]));

fun okify c q th =
    th |> UNDISCH |> c |> Q.INST [`N` |-> q]
       |> SIMP_RULE (srw_ss()) [] |> DISCH_ALL
       |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO, GSYM CONJ_ASSOC]

val Type_OK = save_thm("Type_OK", okify CONJUNCT1 `nType` Type_OK0);

val V_OK = Q.store_thm(
  "V_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nV) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_V pt = SOME i`,
  start >> simp[ptree_V_def]);

val FQV_OK = Q.store_thm(
  "FQV_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nFQV) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_FQV pt = SOME i`,
  start >> simp[ptree_FQV_def]
  >- metis_tac[V_OK, optionTheory.OPTION_MAP_DEF,
               optionTheory.OPTION_CHOICE_def] >>
  simp[ptree_V_def]);

val UQConstructorName_OK = Q.store_thm(
  "UQConstructorName_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nUQConstructorName) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_UQConstructorName pt = SOME i`,
  start >> simp[ptree_UQConstructorName_def]);

val n = SIMP_RULE bool_ss [GSYM AND_IMP_INTRO]
val ConstructorName_OK = Q.store_thm(
  "ConstructorName_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nConstructorName) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_ConstructorName pt = SOME i`,
  start >> simp[ptree_ConstructorName_def]
  >- (erule strip_assume_tac (n UQConstructorName_OK) >>
      simp[]) >>
  simp[ptree_UQConstructorName_def]);

val Ops_OK0 = Q.store_thm(
  "Ops_OK0",
  `N ∈ {nMultOps; nAddOps; nListOps; nRelOps; nCompOps} ∧ valid_ptree cmlG pt ∧
    MAP TK toks = ptree_fringe pt ∧ ptree_head pt = NT (mkNT N) ⇒
    ∃opv. ptree_Op pt = SOME opv`,
  start >> simp[ptree_Op_def, tokcheck_def, tokcheckl_def]);

val MAP_TK11 = Q.prove(
  `∀l1 l2. MAP TK l1 = MAP TK l2 ⇔ l1 = l2`,
  Induct_on `l1` >> simp[] >- metis_tac[] >> rpt gen_tac >>
  Cases_on `l2` >> simp[]);
val _ = augment_srw_ss [rewrites [MAP_TK11]]

val OpID_OK = Q.store_thm(
  "OpID_OK",
  ‘ptree_head pt = NN nOpID ∧ MAP TK toks = ptree_fringe pt ∧
    valid_ptree cmlG pt ⇒
    ∃astv. ptree_OpID pt = SOME astv ∧
           ((∃cnm. astv = Con cnm []) ∨
            (∃v. astv = Var v))’,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  dsimp[] >> conj_tac >> simp[Once FORALL_PROD] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >> rveq >>
  fs[MAP_EQ_CONS, MAP_EQ_APPEND] >>
  simp[ptree_OpID_def, isConstructor_def, isSymbolicConstructor_def, ifM_def] >>
  rw[] >> Cases_on `s` >> fs[oHD_def] >> rw[]);

val std = rpt (first_x_assum (erule strip_assume_tac o n)) >>
          simp[]
val Pattern_OK0 = Q.store_thm(
  "Pattern_OK0",
  `valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
    (N ∈ {nPattern; nPtuple; nPapp; nPbase; nPcons; nPConApp} ∧
    ptree_head pt = NT (mkNT N) ⇒
     ∃p. ptree_Pattern N pt = SOME p) ∧
    (ptree_head pt = NN nPatternList ⇒
     ∃pl. ptree_Plist pt = SOME pl ∧ pl <> [])`,
  map_every qid_spec_tac [`N`, `toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >>
  dsimp[] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >>
  rpt (Q.PAT_X_ASSUM `Y = ptree_head X` (assume_tac o SYM)) >>
  rveq >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  simp[Once ptree_Pattern_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, tokcheckl_def, tokcheck_def] >>
  rpt (Q.UNDISCH_THEN `bool$T` (K ALL_TAC)) >>
  TRY (std >> NO_TAC)
  >- (erule strip_assume_tac (n Type_OK) >> simp[])
  >- (asm_match `pl <> []` >> Cases_on `pl` >> fs[] >>
      asm_match `ptree_Plist pt = SOME (ph::ptl)` >>
      Cases_on `ptl` >> simp[])
  >- (asm_match `ptree_head pt' = NN nV` >>
      `ptree_Pattern nPtuple pt' = NONE ∧ ptree_ConstructorName pt' = NONE`
        by (Cases_on `pt'` >> fs[] >| [
              rename[`Lf p`] >> Cases_on `p` >> fs[],
              rename[`Nd p l`] >> Cases_on `p` >> fs[]
            ] >>
            fs[ptree_Pattern_def, ptree_ConstructorName_def])>>
      erule strip_assume_tac (n V_OK) >> simp[])
  >- (asm_match `ptree_head pt' = NN nConstructorName` >>
      `ptree_Pattern nPtuple pt' = NONE`
        by (Cases_on `pt'`
            >- (rename[`Lf p`] >> Cases_on `p` >> fs[]) >>
            rename[`Nd p _`] >> Cases_on `p` >> fs[ptree_Pattern_def])>>
      erule strip_assume_tac (n ConstructorName_OK) >> rw[])
  >- simp[ptree_Pattern_def, ptree_ConstructorName_def, ptree_V_def]
  >- simp[ptree_Pattern_def, ptree_ConstructorName_def, ptree_V_def]
  >- simp[ptree_Pattern_def, ptree_ConstructorName_def, ptree_V_def]
  >- simp[ptree_Pattern_def, ptree_ConstructorName_def, ptree_V_def]
  >- (erule strip_assume_tac (n OpID_OK) >> simp[EtoPat_def] >>
      rename [`Var v`] >> Cases_on `v` >> simp[EtoPat_def])
  >- (erule strip_assume_tac (n ConstructorName_OK) >> simp[])
  >- simp[ptree_ConstructorName_def]);

val Pattern_OK = save_thm("Pattern_OK", okify CONJUNCT1 `nPattern` Pattern_OK0);

val Eseq_encode_OK = Q.store_thm(
  "Eseq_encode_OK",
  `∀l. l <> [] ⇒ ∃e. Eseq_encode l = SOME e`,
  Induct >> simp[] >>
  Cases_on `l` >> simp[Eseq_encode_def]);

val PbaseList1_OK = Q.store_thm(
  "PbaseList1_OK",
  `valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ∧
    ptree_head pt = NT (mkNT nPbaseList1) ⇒
    ∃pl. ptree_PbaseList1 pt = SOME pl ∧ 0 < LENGTH pl`,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  dsimp[] >> conj_tac >> simp[Once FORALL_PROD] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >> rveq >>
  rpt (Q.PAT_X_ASSUM `Y = ptree_head X` (assume_tac o SYM)) >>
  fs[MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND] >>
  dsimp[Once ptree_PbaseList1_def]
  >- (erule strip_assume_tac (Pattern_OK0 |> Q.INST [`N` |-> `nPbase`] |> n) >>
      fs[])
  >- (rename1 `ptree_head pbt = NN nPbase` >>
      rename1 `ptree_fringe pbt = MAP TK pbtoks` >>
      mp_tac
        (Pattern_OK0 |> Q.INST [`N` |-> `nPbase`, `pt` |-> `pbt`,
                                `toks` |-> `pbtoks`] |> n) >>
      simp[] >> fs[]))

val Eliteral_OK = Q.store_thm(
  "Eliteral_OK",
  `valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ∧
   ptree_head pt = NT (mkNT nEliteral) ⇒
   ∃t. ptree_Eliteral pt = SOME t`,
  start >> simp[ptree_Eliteral_def]);

val _ = print "The E_OK proof takes a while\n"
val E_OK0 = Q.store_thm(
  "E_OK0",
  `valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
    (N ∈ {nE; nE'; nEhandle; nElogicOR; nElogicAND; nEtuple; nEmult;
          nEadd; nElistop; nErel; nEcomp; nEbefore; nEtyped; nEapp;
          nEbase} ∧
     ptree_head pt = NT (mkNT N)
       ⇒
     ∃t. ptree_Expr N pt = SOME t) ∧
    (ptree_head pt = NT (mkNT nEseq) ⇒
     ∃el. ptree_Eseq pt = SOME el ∧ el <> []) ∧
    (ptree_head pt = NT (mkNT nPEs) ⇒ ∃pes. ptree_PEs pt = SOME pes) ∧
    (ptree_head pt = NT (mkNT nElist2) ⇒
     ∃el. ptree_Exprlist nElist2 pt = SOME el) ∧
    (ptree_head pt = NT (mkNT nElist1) ⇒
     ∃el. ptree_Exprlist nElist1 pt = SOME el) ∧
    (ptree_head pt = NT (mkNT nLetDecs) ⇒ ∃lds. ptree_LetDecs pt = SOME lds) ∧
    (ptree_head pt = NT (mkNT nPE) ⇒ ∃pe. ptree_PE pt = SOME pe) ∧
    (ptree_head pt = NT (mkNT nPE') ⇒ ∃pe. ptree_PE' pt = SOME pe) ∧
    (ptree_head pt = NT (mkNT nLetDec) ⇒ ∃ld. ptree_LetDec pt = SOME ld) ∧
    (ptree_head pt = NT (mkNT nAndFDecls) ⇒
     ∃fds. ptree_AndFDecls pt = SOME fds) ∧
    (ptree_head pt = NT (mkNT nFDecl) ⇒ ∃fd. ptree_FDecl pt = SOME fd)`,
  map_every qid_spec_tac [`N`, `toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >> dsimp[] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >>
  rpt (Q.PAT_X_ASSUM `X = ptree_head Y` (assume_tac o SYM)) >>
  rveq >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  simp[Once ptree_Expr_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, tokcheck_def, tokcheckl_def] >>
  rpt (Q.UNDISCH_THEN `bool$T` (K ALL_TAC)) >>
  TRY (std >> NO_TAC)
  >- (erule strip_assume_tac (n Pattern_OK) >> std)
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (erule strip_assume_tac (n Type_OK) >> simp[])
  >- (erule strip_assume_tac Eseq_encode_OK >> simp[])
  >- (asm_match `ptree_head pt' = NN nEtuple` >>
      `ptree_FQV pt' = NONE ∧ ptree_ConstructorName pt' = NONE ∧
       ptree_Eliteral pt' = NONE`
        by (Cases_on `pt'`
            >- (rename[`Lf p`] >> Cases_on `p` >> fs[]) >>
            rename[`Nd p _`] >> Cases_on `p` >> fs[] >>
            simp[ptree_FQV_def, ptree_ConstructorName_def,
                 ptree_Eliteral_def]) >>
      std)
  >- (asm_match `ptree_head pt' = NN nFQV` >>
      `ptree_Eliteral pt' = NONE`
        by (Cases_on `pt'`
            >- (rename [`Lf p`] >> Cases_on `p` >> fs[]) >>
            rename[`Nd p`] >> Cases_on `p` >> fs[] >>
            simp[ptree_Eliteral_def]) >>
      erule strip_assume_tac (n FQV_OK) >> simp[])
  >- (asm_match `ptree_head pt' = NN nConstructorName` >>
      `ptree_FQV pt' = NONE ∧ ptree_Eliteral pt' = NONE`
        by (Cases_on `pt'`
            >- (rename[`Lf p`] >> Cases_on `p` >> fs[]) >>
            rename[`Nd p`] >> Cases_on `p` >> fs[] >>
            simp[ptree_FQV_def, ptree_Eliteral_def]) >>
      erule strip_assume_tac (n ConstructorName_OK) >> rw[])
  >- (erule strip_assume_tac (n Eliteral_OK) >> simp[])
  >- (erule strip_assume_tac (n Eseq_encode_OK) >> simp[])
  >- (erule strip_assume_tac (n OpID_OK) >> simp[])
  >- (simp[ptree_Eliteral_def, ptree_FQV_def, ptree_ConstructorName_def,
           ptree_Expr_def])
  >- (rw[])
  >- (erule strip_assume_tac (n Pattern_OK) >> std)
  >- (erule strip_assume_tac (n Pattern_OK) >> std)
  >- (erule strip_assume_tac (n Pattern_OK) >> std)
  >- (dsimp[] >>
      map_every (erule strip_assume_tac o n) [V_OK, PbaseList1_OK] >>
      asm_match `0 < LENGTH pl` >> Cases_on `pl` >> fs[oHD_def] >> std));

val E_OK = save_thm("E_OK", okify CONJUNCT1 `nE` E_OK0)
val AndFDecls_OK = save_thm(
  "AndFDecls_OK",
  okify (last o #1 o front_last o CONJUNCTS) `v` E_OK0);

val PTbase_OK = Q.store_thm(
  "PTbase_OK",
  ‘valid_ptree cmlG pt ∧ ptree_head pt = NN nPTbase ∧
   MAP TK toks = ptree_fringe pt ⇒
   ∃ty. ptree_PTbase pt = SOME ty’,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >> rveq >>
  simp[ptree_PTbase_def, tokcheck_def]
  >- (erule strip_assume_tac (n TyOp_OK) >> simp[] >>
      rename [‘destTyvarPT pt’] >>
      Cases_on ‘OPTION_MAP Atvar (destTyvarPT pt)’ >>
      simp[]) >>
  metis_tac[Type_OK]);

val TbaseList_OK = Q.store_thm(
  "TbaseList_OK",
  ‘valid_ptree cmlG pt ∧ ptree_head pt = NN nTbaseList ∧
   MAP TK toks = ptree_fringe pt ⇒
   ∃tys. ptree_TbaseList pt = SOME tys’,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >> gen_tac >> strip_tac >>
  simp[cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  fs[MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >> rveq >>
  simp[Once ptree_TbaseList_def] >> dsimp[] >>
  fs[FORALL_AND_THM, DISJ_IMP_THM, MAP_EQ_APPEND] >>
  metis_tac[PTbase_OK]);

val Dconstructor_OK = Q.store_thm(
  "Dconstructor_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nDconstructor ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃dc. ptree_Dconstructor pt = SOME dc`,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_Dconstructor_def, tokcheck_def]
  >- (map_every (erule strip_assume_tac o n)
                [UQConstructorName_OK, Type_OK] >>
      simp[]) >>
  map_every (erule strip_assume_tac o n) [UQConstructorName_OK, TbaseList_OK] >>
  simp[])

val DtypeCons_OK = Q.store_thm(
  "DtypeCons_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nDtypeCons ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃dtc. ptree_linfix nDtypeCons BarT ptree_Dconstructor pt = SOME dtc`,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_APPEND, MAP_EQ_CONS] >>
  simp[Once ptree_linfix_def, tokcheck_def] >>
  erule strip_assume_tac (n Dconstructor_OK) >> simp[]);

val DtypeDecl_OK = Q.store_thm(
  "DtypeDecl_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nDtypeDecl ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃dtd. ptree_DtypeDecl pt = SOME dtd`,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_DtypeDecl_def] >>
  map_every (erule strip_assume_tac o n) [DtypeCons_OK, TypeName_OK] >>
  simp[tokcheck_def]);

val DtypeDecls_OK = Q.store_thm(
  "DtypeDecls_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nDtypeDecls ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃td. ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt = SOME td`,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_APPEND, MAP_EQ_CONS] >>
  simp[Once ptree_linfix_def, tokcheck_def] >>
  erule strip_assume_tac (n DtypeDecl_OK) >> simp[]);

val TypeDec_OK = Q.store_thm(
  "TypeDec_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nTypeDec ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃td. ptree_TypeDec pt = SOME td`,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> fs[MAP_EQ_CONS] >>
  simp[ptree_TypeDec_def, tokcheck_def] >>
  erule strip_assume_tac (n DtypeDecls_OK) >> simp[]);

val TypeAbbrevDec_OK = Q.store_thm(
  "TypeAbbrevDec_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nTypeAbbrevDec ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃td. ptree_TypeAbbrevDec pt = SOME td`,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> fs[MAP_EQ_CONS] >> rveq >>
  simp[ptree_TypeAbbrevDec_def, pairTheory.EXISTS_PROD,
       PULL_EXISTS, tokcheck_def] >>
  metis_tac[SIMP_RULE (srw_ss()) [pairTheory.EXISTS_PROD] TypeName_OK,
            Type_OK]);

val Decl_OK = Q.store_thm(
  "Decl_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nDecl ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃d. ptree_Decl pt = SOME d`,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> fs[MAP_EQ_CONS] >>
  simp[ptree_Decl_def, tokcheckl_def, tokcheck_def]
  >- (map_every (erule strip_assume_tac o n) [Pattern_OK, E_OK] >>
      simp[])
  >- (erule strip_assume_tac (n AndFDecls_OK) >> simp[])
  >- (erule strip_assume_tac (n TypeDec_OK) >> simp[])
  >- (erule strip_assume_tac (n Dconstructor_OK) >> simp[] >>
      asm_match `ptree_Dconstructor pt' = SOME dc` >>
      Cases_on `dc` >> simp[])
  >- (erule strip_assume_tac (n TypeAbbrevDec_OK) >> simp[] >>
      qmatch_abbrev_tac `∃d. OPTION_CHOICE foo (SOME _) = SOME d` >>
      Cases_on `foo` >> simp[]));

val Decls_OK = Q.store_thm(
  "Decls_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nDecls ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃ds. ptree_Decls pt = SOME ds`,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  rpt (Q.PAT_X_ASSUM `X = ptree_head Y` (assume_tac o SYM)) >>
  full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_APPEND, MAP_EQ_CONS] >>
  simp[ptree_Decls_def, tokcheck_def] >>
  asm_match `ptree_head pt' = NN nDecl` >>
  `destLf pt' = NONE`
    by (Cases_on `pt'`
        >- (rename[`Lf p`] >> Cases_on `p` >> fs[]) >>
        rename[`Nd p`] >> Cases_on `p` >> fs[]) >>
  erule strip_assume_tac (n Decl_OK) >> simp[])

val OptTypEqn_OK = Q.store_thm(
  "OptTypEqn_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nOptTypEqn ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃typopt. ptree_OptTypEqn pt = SOME typopt`,
  start >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[ptree_OptTypEqn_def, tokcheck_def] >> metis_tac[Type_OK]);

<<<<<<< HEAD
val StructName_OK = Q.store_thm(
  "StructName_OK",
  ‘valid_ptree cmlG pt ∧ ptree_head pt = NN nStructName ∧
   MAP TK toks = ptree_fringe pt ⇒
   ∃snm. ptree_StructName pt = SOME snm’,
  start >> simp[ptree_StructName_def]);
val SigName_OK = Q.store_thm(
  "SigName_OK",
  ‘valid_ptree cmlG pt ∧ ptree_head pt = NN nSigName ∧
   MAP TK toks = ptree_fringe pt ⇒
   ∃snm. ptree_SigName pt = SOME snm’,
  start >> simp[ptree_SigName_def]);
val SigDefName_OK = Q.store_thm(
  "SigDefName_OK",
  ‘valid_ptree cmlG pt ∧ ptree_head pt = NN nSigDefName ∧
   MAP TK toks = ptree_fringe pt ⇒
   ∃snm. ptree_SigDefName pt = SOME snm’,
  start >> simp[ptree_SigDefName_def]);

val Sig_OK = Q.store_thm(
  "Sig_OK",
  ‘∀pt toks.
     valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
     (ptree_head pt = NN nSignature ⇒
      ∃snm sds. ptree_Signature pt = SOME (snm, sds)) ∧
     (ptree_head pt = NN nSignatureValue ⇒
      ∃sds. ptree_SignatureValue pt = SOME sds) ∧
     (ptree_head pt = NN nSpecLineList ⇒
      ∃sds. ptree_SpeclineList pt = SOME sds) ∧
     (ptree_head pt = NN nSpecLine ⇒ ∃sd. ptree_SpecLine pt = SOME sd)’,
  ho_match_mp_tac grammarTheory.ptree_ind >> strip_tac >>
  simp[Once FORALL_PROD] >- dsimp[] >> rw[] >>
  fs[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM, ptree_SpecLine_def] >> rw[] >>
  fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM, tokcheckl_def,
     tokcheck_def]
  >- (rename [‘ptree_SigDefName’] >> metis_tac[SigDefName_OK])
  >- metis_tac[]
  >- (rename [‘ptree_Type’, ‘ptree_V’] >> metis_tac[V_OK, Type_OK])
  >- (rename [‘ptree_TypeName’, ‘ptree_OptTypEqn’] >>
      dsimp[EXISTS_PROD, EXISTS_OPTION] >>
      metis_tac[option_CASES, TypeName_OK, OptTypEqn_OK, pair_CASES])
  >- (rename [‘ptree_Dconstructor’] >> dsimp[EXISTS_PROD] >>
      metis_tac[pair_CASES, Dconstructor_OK])
  >- (rename [‘ptree_StructName’, ‘ptree_SigName’] >>
      metis_tac[StructName_OK, SigName_OK])
  >- (rename [‘NN nSignature = ptree_head pt’] >>
      fs[FORALL_AND_THM, DECIDE ``(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)``]>>
      first_x_assum (drule_all_then strip_assume_tac) >> simp[] >>
      qmatch_abbrev_tac ‘∃sd. OPTION_CHOICE foo _ = SOME sd’ >>
      Cases_on ‘foo’ >> simp[])
  >- (rename [‘NN nTypeDec = ptree_head pt’] >>
      drule TypeDec_OK >> simp[] >> strip_tac >> simp[]));
=======
val SpecLine_OK = Q.store_thm(
  "SpecLine_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nSpecLine ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃sl. ptree_SpecLine pt = SOME sl`,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_SpecLine_def, pairTheory.EXISTS_PROD, PULL_EXISTS,
              tokcheckl_def, tokcheck_def] >>
  metis_tac[V_OK, Type_OK, TypeName_OK, TypeDec_OK, Dconstructor_OK,
            pairTheory.pair_CASES, OptTypEqn_OK]);

val SpecLineList_OK = Q.store_thm(
  "SpecLineList_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nSpecLineList ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃sl. ptree_SpeclineList pt = SOME sl`,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  rpt (Q.PAT_X_ASSUM `X = ptree_head Y` (assume_tac o SYM)) >>
  full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_APPEND, MAP_EQ_CONS] >>
  simp[ptree_SpeclineList_def, tokcheck_def] >>
  erule strip_assume_tac (n SpecLine_OK) >> simp[] >>
  asm_match `ptree_head pt' = NN nSpecLine` (* >>
  Cases_on `pt'`
  >- (rename[`Lf p`] >> Cases_on `p` >> fs[]) >> simp[] *))

val StructName_OK = Q.store_thm(
  "StructName_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nStructName ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃sl. ptree_StructName pt = SOME sl`,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_StructName_def]);

val SignatureValue_OK = Q.store_thm(
  "SignatureValue_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nSignatureValue ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃sv. ptree_SignatureValue pt = SOME sv`,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_SignatureValue_def, tokcheckl_def, tokcheck_def] >>
  metis_tac[SpecLineList_OK, oneTheory.one]);
>>>>>>> origin/master

val Structure_OK = Q.store_thm(
  "Structure_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nStructure ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃s. ptree_Structure pt = SOME s`,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_Structure_def] >>
  rpt (Q.PAT_X_ASSUM `X = ptree_head Y` (assume_tac o SYM)) >>
  map_every (erule strip_assume_tac o n) [Decls_OK, StructName_OK] >>
  simp[tokcheck_def, tokcheckl_def] >>
  asm_match `ptree_head pt' = NN nOptionalSignatureAscription` >>
  Cases_on `pt'` >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq
  >- (rename[`Lf p`] >> Cases_on `p` >> fs[]) >>
  rename[`Nd p`] >> Cases_on `p` >> fs[] >>
  fs[cmlG_FDOM, cmlG_applied, MAP_EQ_CONS] >> rveq >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS] >>
<<<<<<< HEAD
  metis_tac[SigName_OK]);
=======
  metis_tac[SignatureValue_OK, oneTheory.one]);
>>>>>>> origin/master

val TopLevelDec_OK = Q.store_thm(
  "TopLevelDec_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nTopLevelDec ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃t. ptree_TopLevelDec pt = SOME t`,
  start
  >- (erule strip_assume_tac (n Structure_OK) >> simp[ptree_TopLevelDec_def])
  >- (drule_then drule Sig_OK >> simp[] >> rw[] >>
      simp[ptree_TopLevelDec_def, OPTION_CHOICE_EQUALS_OPTION,
           OPTION_CHOICE_EQ_NONE] >>
      metis_tac[option_CASES]) >>
  erule strip_assume_tac (n Decl_OK) >> simp[ptree_TopLevelDec_def] >>
  simp[ptree_TopLevelDec_def, OPTION_CHOICE_EQUALS_OPTION,
       OPTION_CHOICE_EQ_NONE] >> metis_tac[option_CASES]);

val TopLevelDecs_OK = Q.store_thm(
  "TopLevelDecs_OK",
  `valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
    (ptree_head pt = NN nTopLevelDecs ⇒ ∃ts. ptree_TopLevelDecs pt = SOME ts) ∧
    (ptree_head pt = NN nNonETopLevelDecs ⇒
     ∃ts. ptree_NonETopLevelDecs pt = SOME ts)`,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  conj_tac >> simp[Once FORALL_PROD] >>
  dsimp[] >> rpt strip_tac >> fs[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >>
  rpt (Q.PAT_X_ASSUM `X = ptree_head Y` (assume_tac o SYM)) >>
  rveq >> dsimp[ptree_TopLevelDecs_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND, tokcheck_def] >>
  TRY (Cases_on`toks`>>fs[]>>metis_tac[])
  >- (fs[MAP_EQ_CONS] >> rveq >> metis_tac[E_OK])
  >- (rename[`destLf lf`] >> Cases_on `lf` >> fs[]
      >- (rename[`Lf p`] >> Cases_on `p` >> fs[]) >>
      metis_tac[TopLevelDec_OK, grammarTheory.ptree_fringe_def])
  >- (rename[`destLf lf`] >> Cases_on `lf` >> fs[]
      >- (rename[`Lf p`] >> Cases_on `p` >> fs[]) >>
      metis_tac[TopLevelDec_OK, grammarTheory.ptree_fringe_def]));

(*
val REPLTop_OK = Q.store_thm(
  "REPLTop_OK",
  `valid_ptree cmlG pt ∧ ptree_head pt = NN nREPLTop ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃r. ptree_REPLTop pt = SOME r`,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[ptree_REPLTop_def]
  >- (erule strip_assume_tac (n TopLevelDec_OK) >> simp[]) >>
  rename1 `ptree_TopLevelDec pt0` >>
  Cases_on `ptree_TopLevelDec pt0` >> simp[] >>
  erule strip_assume_tac (n E_OK) >> simp[]);
*)

val _ = export_theory();
