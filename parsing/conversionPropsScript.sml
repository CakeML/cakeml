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

val _ = export_theory();
