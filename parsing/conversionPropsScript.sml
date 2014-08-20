open HolKernel Parse boolLib bossLib;
open lcsymtacs parsingPreamble boolSimps

open cmlPtreeConversionTheory
open gramPropsTheory

val _ = new_theory "conversionProps";

val _ = export_rewrites ["option.OPTION_IGNORE_BIND_def"]

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
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nUQTyOp) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃utyop. ptree_UQTyop pt = SOME utyop``,
  start >> simp[ptree_UQTyop_def]);

val TyOp_OK = store_thm(
  "TyOp_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTyOp) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyop. ptree_Tyop pt = SOME tyop``,
  start >> simp[ptree_Tyop_def] >>
  asm_match `valid_ptree cmlG pt'` >>
  `destLf pt' = NONE`
    by (Cases_on `pt'` >> fs[MAP_EQ_CONS] >>
        rveq >> fs[]) >>
  simp[] >> metis_tac [UQTyOp_OK]);

val TyvarN_OK = store_thm(
  "TyvarN_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTyvarN) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyvn. ptree_TyvarN pt = SOME tyvn``,
  start >> simp[ptree_TyvarN_def]);

val TyVarList_OK = store_thm(
  "TyVarList_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTyVarList) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃tyvnms. ptree_linfix nTyVarList CommaT ptree_TyvarN pt = SOME tyvnms``,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) []
  >- (simp[ptree_linfix_def] >> metis_tac [TyvarN_OK]) >>
  simp_tac (srw_ss()) [Once ptree_linfix_def] >> simp[] >>
  simp[] >> dsimp[] >>
  fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rveq >>
  metis_tac [TyvarN_OK]);

val TypeName_OK = store_thm(
  "TypeName_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTypeName) ∧
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
  ``valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
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
  simp[Once ptree_Type_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM]
  >- metis_tac[tuplify_OK]
  >- metis_tac[tuplify_OK]
  >- metis_tac[TyOp_OK]
  >- metis_tac[]
  >- (asm_match `ptree_head pt' = NN nTyOp` >>
      `destTyvarPT pt' = NONE` by (Cases_on `pt'` >> fs[]) >>
      simp[] >> metis_tac[TyOp_OK])
  >- metis_tac [TyOp_OK]
  >- metis_tac[]
  >- (dsimp[] >> metis_tac[])
  >- (dsimp[] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[])

fun okify c q th =
    th |> UNDISCH |> c |> Q.INST [`N` |-> q]
       |> SIMP_RULE (srw_ss()) [] |> DISCH_ALL
       |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO, GSYM CONJ_ASSOC]

val Type_OK = save_thm("Type_OK", okify CONJUNCT1 `nType` Type_OK0);

val V_OK = store_thm(
  "V_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nV) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_V pt = SOME i``,
  start >> simp[ptree_V_def]);

val FQV_OK = store_thm(
  "FQV_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nFQV) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_FQV pt = SOME i``,
  start >> simp[ptree_FQV_def]
  >- metis_tac[V_OK, optionTheory.OPTION_MAP_DEF,
               optionTheory.OPTION_CHOICE_def] >>
  simp[ptree_V_def]);

val UQConstructorName_OK = store_thm(
  "UQConstructorName_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nUQConstructorName) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_UQConstructorName pt = SOME i``,
  start >> simp[ptree_UQConstructorName_def]);

val n = SIMP_RULE bool_ss [GSYM AND_IMP_INTRO]
val ConstructorName_OK = store_thm(
  "ConstructorName_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nConstructorName) ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃i. ptree_ConstructorName pt = SOME i``,
  start >> simp[ptree_ConstructorName_def]
  >- (erule strip_assume_tac (n UQConstructorName_OK) >>
      simp[]) >>
  simp[ptree_UQConstructorName_def]);

val Ops_OK0 = store_thm(
  "Ops_OK0",
  ``N ∈ {nMultOps; nAddOps; nListOps; nRelOps; nCompOps} ∧ valid_ptree cmlG pt ∧
    MAP TK toks = ptree_fringe pt ∧ ptree_head pt = NT (mkNT N) ⇒
    ∃opv. ptree_Op pt = SOME opv``,
  start >> simp[ptree_Op_def]);

val MAP_TK11 = prove(
  ``∀l1 l2. MAP TK l1 = MAP TK l2 ⇔ l1 = l2``,
  Induct_on `l1` >> simp[] >- metis_tac[] >> rpt gen_tac >>
  Cases_on `l2` >> simp[]);
val _ = augment_srw_ss [rewrites [MAP_TK11]]

val std = rpt (first_x_assum (erule strip_assume_tac o n)) >>
          simp[]
val Pattern_OK0 = store_thm(
  "Pattern_OK0",
  ``valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
    (N ∈ {nPattern; nPtuple; nPapp; nPbase} ∧ ptree_head pt = NT (mkNT N) ⇒
     ∃p. ptree_Pattern N pt = SOME p) ∧
    (ptree_head pt = NN nPatternList ⇒
     ∃pl. ptree_Plist pt = SOME pl ∧ pl <> [])``,
  map_every qid_spec_tac [`N`, `toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  dsimp[] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >>
  rveq >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  simp[Once ptree_Pattern_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (Q.UNDISCH_THEN `bool$T` (K ALL_TAC)) >>
  TRY (std >> NO_TAC)
  >- (asm_match `pl <> []` >> Cases_on `pl` >> fs[] >>
      asm_match `ptree_Plist pt = SOME (ph::ptl)` >>
      Cases_on `ptl` >> simp[])
  >- (erule strip_assume_tac (n ConstructorName_OK) >> simp[])
  >- (asm_match `ptree_head pt' = NN nV` >>
      `ptree_Pattern nPtuple pt' = NONE ∧ ptree_ConstructorName pt' = NONE`
        by (Cases_on `pt'` >> fs[ptree_Pattern_def, ptree_ConstructorName_def])>>
      erule strip_assume_tac (n V_OK) >> simp[])
  >- (asm_match `ptree_head pt' = NN nConstructorName` >>
      `ptree_Pattern nPtuple pt' = NONE`
        by (Cases_on `pt'` >> fs[ptree_Pattern_def])>>
      erule strip_assume_tac (n ConstructorName_OK) >> rw[])
  >- simp[ptree_Pattern_def, ptree_ConstructorName_def,
          ptree_V_def] >>
  simp[ptree_Pattern_def, ptree_ConstructorName_def,
       ptree_V_def]);

val Pattern_OK = save_thm("Pattern_OK", okify CONJUNCT1 `nPattern` Pattern_OK0);

val Vlist1_OK = store_thm(
  "Vlist1_OK",
  ``ptree_head pt = NN nVlist1 ∧ MAP TK toks = ptree_fringe pt ∧
    valid_ptree cmlG pt ⇒
    ∃vl. ptree_Vlist1 pt = SOME vl ∧ vl <> []``,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  dsimp[] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >>
  rveq >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  simp[Once ptree_Vlist1_def] >> fs[FORALL_AND_THM, DISJ_IMP_THM] >>
  dsimp[] >> erule strip_assume_tac (n V_OK) >> simp[]);

val Eseq_encode_OK = store_thm(
  "Eseq_encode_OK",
  ``∀l. l <> [] ⇒ ∃e. Eseq_encode l = SOME e``,
  Induct >> simp[] >>
  Cases_on `l` >> simp[Eseq_encode_def]);

val _ = print "The E_OK proof takes a while\n"
val E_OK0 = store_thm(
  "E_OK0",
  ``valid_ptree cmlG pt ∧ MAP TK toks = ptree_fringe pt ⇒
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
    (ptree_head pt = NT (mkNT nFDecl) ⇒ ∃fd. ptree_FDecl pt = SOME fd)``,
  map_every qid_spec_tac [`N`, `toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  dsimp[] >> rpt strip_tac >>
  fs[MAP_EQ_CONS, cmlG_FDOM, cmlG_applied, MAP_EQ_APPEND] >>
  rveq >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  simp[Once ptree_Expr_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (Q.UNDISCH_THEN `bool$T` (K ALL_TAC)) >>
  TRY (std >> NO_TAC)
  >- (erule strip_assume_tac (n V_OK) >> std)
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (match_mp_tac (GEN_ALL Ops_OK0) >> simp[])
  >- (erule strip_assume_tac (n Type_OK) >> simp[])
  >- (erule strip_assume_tac Eseq_encode_OK >> simp[])
  >- (asm_match `ptree_head pt' = NN nEtuple` >>
      `destLf pt' = NONE`
        by (Cases_on `pt'` >> fs[] >> rveq >> fs[MAP_EQ_CONS]) >>
      `ptree_FQV pt' = NONE ∧ ptree_ConstructorName pt' = NONE`
        by (Cases_on `pt'` >> fs[] >>
            simp[ptree_FQV_def, ptree_ConstructorName_def]) >>
      std)
  >- (asm_match `ptree_head pt' = NN nFQV` >>
      `destLf pt' = NONE`
        by (Cases_on `pt'` >> fs[] >> rveq >> fs[MAP_EQ_CONS]) >>
      erule strip_assume_tac (n FQV_OK) >> simp[])
  >- (asm_match `ptree_head pt' = NN nConstructorName` >>
      `destLf pt' = NONE`
        by (Cases_on `pt'` >> fs[] >> rveq >> fs[MAP_EQ_CONS]) >>
      `ptree_FQV pt' = NONE`
        by (Cases_on `pt'` >> fs[] >> simp[ptree_FQV_def]) >>
      erule strip_assume_tac (n ConstructorName_OK) >> rw[])
  >- (erule strip_assume_tac (n Eseq_encode_OK) >> simp[])
  >- (asm_match `ptree_head pt' = NN nLetDec` >>
      `∀s. pt' <> Lf s` by (Cases_on `pt'` >> fs[MAP_EQ_CONS] >> rveq >> fs[])>>
      simp[])
  >- (erule strip_assume_tac (n Pattern_OK) >> std)
  >- (erule strip_assume_tac (n Pattern_OK) >> std)
  >- (erule strip_assume_tac (n V_OK) >> std) >>
  dsimp[] >>
  map_every (erule strip_assume_tac o n) [V_OK, Vlist1_OK] >>
  asm_match `vl <> []` >> Cases_on `vl` >> fs[oHD_def] >> std)

val E_OK = save_thm("E_OK", okify CONJUNCT1 `nE` E_OK0)
val AndFDecls_OK = save_thm(
  "AndFDecls_OK",
  okify (last o #1 o front_last o CONJUNCTS) `v` E_OK0)

val Dconstructor_OK = store_thm(
  "Dconstructor_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nDconstructor ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃dc. ptree_Dconstructor pt = SOME dc``,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_Dconstructor_def]
  >- (map_every (erule strip_assume_tac o n)
                [UQConstructorName_OK, Type_OK] >>
      simp[]) >>
  erule strip_assume_tac (n UQConstructorName_OK) >> simp[])

val DtypeCons_OK = store_thm(
  "DtypeCons_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nDtypeCons ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃dtc. ptree_linfix nDtypeCons BarT ptree_Dconstructor pt = SOME dtc``,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_APPEND, MAP_EQ_CONS] >>
  simp[Once ptree_linfix_def] >>
  erule strip_assume_tac (n Dconstructor_OK) >> simp[]);

val DtypeDecl_OK = store_thm(
  "DtypeDecl_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nDtypeDecl ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃dtd. ptree_DtypeDecl pt = SOME dtd``,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_DtypeDecl_def] >>
  map_every (erule strip_assume_tac o n) [DtypeCons_OK, TypeName_OK] >>
  simp[]);

val DtypeDecls_OK = store_thm(
  "DtypeDecls_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nDtypeDecls ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃td. ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt = SOME td``,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_APPEND, MAP_EQ_CONS] >>
  simp[Once ptree_linfix_def] >>
  erule strip_assume_tac (n DtypeDecl_OK) >> simp[]);

val TypeDec_OK = store_thm(
  "TypeDec_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nTypeDec ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃td. ptree_TypeDec pt = SOME td``,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> fs[MAP_EQ_CONS] >>
  simp[ptree_TypeDec_def] >>
  erule strip_assume_tac (n DtypeDecls_OK) >> simp[]);

val TypeAbbrevDec_OK = store_thm(
  "TypeAbbrevDec_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nTypeAbbrevDec ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃td. ptree_TypeAbbrevDec pt = SOME td``,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> fs[MAP_EQ_CONS] >> rveq >>
  simp[ptree_TypeAbbrevDec_def, pairTheory.EXISTS_PROD,
       PULL_EXISTS] >>
  metis_tac[SIMP_RULE (srw_ss()) [pairTheory.EXISTS_PROD] TypeName_OK,
            Type_OK]);

val Decl_OK = store_thm(
  "Decl_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nDecl ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃d. ptree_Decl pt = SOME d``,
  start >> fs[MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> fs[MAP_EQ_CONS] >>
  simp[ptree_Decl_def]
  >- (map_every (erule strip_assume_tac o n) [Pattern_OK, E_OK] >>
      simp[])
  >- (erule strip_assume_tac (n AndFDecls_OK) >> simp[])
  >- (erule strip_assume_tac (n TypeDec_OK) >> simp[])
  >- (erule strip_assume_tac (n Dconstructor_OK) >> simp[] >>
      asm_match `ptree_Dconstructor pt' = SOME dc` >>
      Cases_on `dc` >> simp[])
  >- (erule strip_assume_tac (n TypeAbbrevDec_OK) >> simp[] >>
      qmatch_abbrev_tac `∃d. foo ++ SOME x = SOME d` >>
      Cases_on `foo` >> simp[]));

val Decls_OK = store_thm(
  "Decls_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nDecls ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃ds. ptree_Decls pt = SOME ds``,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_APPEND, MAP_EQ_CONS] >>
  simp[ptree_Decls_def]
  >- (asm_match `ptree_head pt' = NN nDecl` >>
      `∀s. pt' <> Lf s`
        by (Cases_on `pt'` >> fs[MAP_EQ_CONS] >> rveq >> fs[])>>
      erule strip_assume_tac (n Decl_OK) >> simp[]) >>
  metis_tac[]);

val OptTypEqn_OK = store_thm(
  "OptTypEqn_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nOptTypEqn ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃typopt. ptree_OptTypEqn pt = SOME typopt``,
  start >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[ptree_OptTypEqn_def] >> metis_tac[Type_OK]);

val SpecLine_OK = store_thm(
  "SpecLine_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nSpecLine ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃sl. ptree_SpecLine pt = SOME sl``,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_SpecLine_def, pairTheory.EXISTS_PROD, PULL_EXISTS] >>
  metis_tac[V_OK, Type_OK, TypeName_OK, TypeDec_OK, Dconstructor_OK,
            pairTheory.pair_CASES, OptTypEqn_OK]);

val SpecLineList_OK = store_thm(
  "SpecLineList_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nSpecLineList ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃sl. ptree_SpeclineList pt = SOME sl``,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  simp[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rpt strip_tac >> rveq >>
  full_simp_tac (srw_ss() ++ DNF_ss) [MAP_EQ_APPEND, MAP_EQ_CONS] >>
  simp[ptree_SpeclineList_def]
  >- (erule strip_assume_tac (n SpecLine_OK) >> simp[] >>
      asm_match `ptree_head pt' = NN nSpecLine` >>
      Cases_on `pt'` >> fs[MAP_EQ_CONS]) >>
  metis_tac[]);

val StructName_OK = store_thm(
  "StructName_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nStructName ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃sl. ptree_StructName pt = SOME sl``,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_StructName_def]);

val SignatureValue_OK = store_thm(
  "SignatureValue_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nSignatureValue ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃sv. ptree_SignatureValue pt = SOME sv``,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_SignatureValue_def] >>
  metis_tac[SpecLineList_OK]);

val Structure_OK = store_thm(
  "Structure_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nStructure ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃s. ptree_Structure pt = SOME s``,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, FORALL_AND_THM, DISJ_IMP_THM] >>
  rveq >> simp[ptree_Structure_def] >>
  map_every (erule strip_assume_tac o n) [Decls_OK, StructName_OK] >> simp[] >>
  asm_match `ptree_head pt' = NN nOptionalSignatureAscription` >>
  Cases_on `pt'` >> fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
  fs[cmlG_FDOM, cmlG_applied, MAP_EQ_CONS] >> rveq >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS] >>
  metis_tac[SignatureValue_OK]);

val TopLevelDec_OK = store_thm(
  "TopLevelDec_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nTopLevelDec ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃t. ptree_TopLevelDec pt = SOME t``,
  start
  >- (erule strip_assume_tac (n Structure_OK) >> simp[ptree_TopLevelDec_def]) >>
  erule strip_assume_tac (n Decl_OK) >> simp[ptree_TopLevelDec_def] >>
  Cases_on `ptree_Structure e` >> simp[]);

val TopLevelDecs_OK = store_thm(
  "TopLevelDecs_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nTopLevelDecs ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃ts. ptree_TopLevelDecs pt = SOME ts``,
  map_every qid_spec_tac [`toks`, `pt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >>
  dsimp[] >> rpt strip_tac >> fs[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >>
  rveq >> dsimp[ptree_TopLevelDecs_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND] >>
  TRY (Cases_on`toks`>>fs[]>>metis_tac[]) >>
  first_x_assum (erule strip_assume_tac) >>
  erule strip_assume_tac (n TopLevelDec_OK) >> simp[]>> rw[]);

val REPLTop_OK = store_thm(
  "REPLTop_OK",
  ``valid_ptree cmlG pt ∧ ptree_head pt = NN nREPLTop ∧
    MAP TK toks = ptree_fringe pt ⇒
    ∃r. ptree_REPLTop pt = SOME r``,
  start >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[ptree_REPLTop_def]
  >- (erule strip_assume_tac (n TopLevelDec_OK) >> simp[]) >>
  Cases_on `ptree_TopLevelDec e` >> simp[] >>
  erule strip_assume_tac (n E_OK) >> simp[]);

val _ = export_theory();
