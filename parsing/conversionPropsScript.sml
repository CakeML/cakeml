open HolKernel Parse boolLib bossLib;
open lcsymtacs parsingPreamble boolSimps

open cmlPtreeConversionTheory
open gramPropsTheory

val _ = new_theory "conversionProps";

val ptree_head_TOK = store_thm(
  "ptree_head_TOK",
  ``ptree_head pt = TOK sym ⇔ pt = Lf (TOK sym)``,
  Cases_on `pt` >> simp[]);
val _ = export_rewrites ["ptree_head_TOK"]

val start =
  Cases_on `pt` >> simp[grammarTheory.MAP_EQ_SING]
  >- (rw[] >> fs[]) >>
  strip_tac >> rveq >> fs[cmlG_FDOM, cmlG_applied, MAP_EQ_CONS] >>
  rveq >> fs[MAP_EQ_CONS] >> rveq

val UQTyOp_OK = store_thm(
  "UQTyOp_OK",
  ``valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT nUQTyOp) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃utyop. ptree_UQTyop pt = SOME utyop``,
  start >> simp[ptree_UQTyop_def, OPTION_CHOICE_def]);

val TyOp_OK = store_thm(
  "TyOp_OK",
  ``valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT nTyOp) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyop. ptree_Tyop pt = SOME tyop``,
  start >> simp[ptree_Tyop_def, OPTION_CHOICE_def] >>
  asm_match `valid_ptree mmlG pt'` >>
  `destLf pt' = NONE`
    by (Cases_on `pt'` >> fs[OPTION_CHOICE_def, MAP_EQ_CONS] >>
        rveq >> fs[]) >>
  simp[OPTION_CHOICE_def] >> metis_tac [UQTyOp_OK]);

val TyvarN_OK = store_thm(
  "TyvarN_OK",
  ``valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT nTyvarN) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyvn. ptree_TyvarN pt = SOME tyvn``,
  start >> simp[ptree_TyvarN_def]);

val TyVarList_OK = store_thm(
  "TyVarList_OK",
  ``valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT nTyVarList) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyvnms. ptree_linfix nTyVarList CommaT ptree_TyvarN pt = SOME tyvnms``,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) []
  >- (simp[ptree_linfix_def] >> metis_tac [TyvarN_OK]) >>
  simp_tac (srw_ss()) [Once ptree_linfix_def] >> simp[gramTheory.assert_def] >>
  simp[optionTheory.OPTION_IGNORE_BIND_def] >> dsimp[] >>
  fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rveq >>
  metis_tac [TyvarN_OK]);

val TypeName_OK = store_thm(
  "TypeName_OK",
  ``valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT nTypeName) ∧
    MAP TOK toks = ptree_fringe pt ⇒
    ∃tn. ptree_TypeName pt = SOME tn``,
  start >> simp[ptree_TypeName_def] >| [
    metis_tac[UQTyOp_OK],
    full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_CONS, MAP_EQ_APPEND] >>
    metis_tac[UQTyOp_OK, TyVarList_OK],
    metis_tac[UQTyOp_OK]
  ]);

val tuplify_OK = store_thm(
  "tuplify_OK",
  ``tl <> [] ⇒ ∃t. tuplify tl = SOME t``,
  strip_tac >>
  `∃h tl0. tl = h::tl0` by (Cases_on `tl` >> fs[]) >>
  Cases_on `tl0` >> simp[tuplify_def]);


val Type_OK0 = store_thm(
  "Type_OK0",
  ``valid_ptree mmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
    (N ∈ {nType; nDType; nTbase} ∧
     ptree_head pt = NT (mkNT N)
       ⇒
     ∃t. ptree_Type N pt = SOME t) ∧
    (ptree_head pt = NT (mkNT nPType) ⇒
     ∃tl. ptree_PType pt = SOME tl ∧ tl <> []) ∧
    (ptree_head pt = NT (mkNT nTypeList1) ⇒
     ∃tl. ptree_TypeList1 pt = SOME tl) ∧
    (ptree_head pt = NT (mkNT nTypeList2) ⇒
     ∃tl. ptree_Typelist2 pt = SOME tl)``,
  map_every qid_spec_tac [`N`, `toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  dsimp[] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >>
  rveq >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  simp[Once ptree_Type_def, gramTheory.assert_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, optionTheory.OPTION_IGNORE_BIND_def,
     OPTION_CHOICE_def]
  >- metis_tac[tuplify_OK]
  >- metis_tac[tuplify_OK]
  >- metis_tac[TyOp_OK]
  >- metis_tac[]
  >- (asm_match `ptree_head pt' = NN nTyOp` >>
      `destTyvarPT pt' = NONE` by (Cases_on `pt'` >> fs[]) >>
      simp[OPTION_CHOICE_def] >> metis_tac[TyOp_OK])
  >- metis_tac [TyOp_OK]
  >- metis_tac[]
  >- (dsimp[] >> metis_tac[])
  >- (dsimp[] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[])

val Type_OK = save_thm(
  "Type_OK",
  Type_OK0 |> UNDISCH |> CONJUNCT1 |> Q.INST [`N` |-> `nType`]
           |> SIMP_RULE (srw_ss()) [] |> DISCH_ALL
           |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO, GSYM CONJ_ASSOC]);

val V_OK = store_thm(
  "V_OK",
  ``valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT nV) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_V pt = SOME i``,
  start >> simp[ptree_V_def, OPTION_CHOICE_def]);

val FQV_OK = store_thm(
  "FQV_OK",
  ``valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT nFQV) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_FQV pt = SOME i``,
  start >> simp[ptree_FQV_def, OPTION_CHOICE_def]
  >- metis_tac[V_OK, optionTheory.OPTION_MAP_DEF,
               OPTION_CHOICE_def] >>
  simp[OPTION_CHOICE_def, ptree_V_def]);




val _ = export_theory();
