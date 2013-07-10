open HolKernel boolLib bossLib

open pred_setTheory
open mmlPEGTheory gramTheory gramPropsTheory
open lcsymtacs boolSimps
open parsingPreamble

open pegSoundTheory

val _ = new_theory "pegComplete"

val _ = augment_srw_ss [rewrites [
  peg_eval_seql_CONS, peg_eval_tok_SOME, tokeq_def, bindNT_def, mktokLf_def,
  peg_eval_choicel_CONS, pegf_def, peg_eval_seq_SOME, pnt_def, peg_eval_try,
  try_def]]

val has_length = assert (can (find_term (same_const listSyntax.length_tm)) o
                         concl)

val peg_eval_choice_NONE =
  ``peg_eval G (i, choice s1 s2 f) NONE``
    |> SIMP_CONV (srw_ss()) [Once pegTheory.peg_eval_cases]

val peg_eval_tok_NONE =
  ``peg_eval G (i, tok P f) NONE``
    |> SIMP_CONV (srw_ss()) [Once pegTheory.peg_eval_cases]

val peg_eval_seq_NONE =
  ``peg_eval G (i, seq s1 s2 f) NONE``
    |> SIMP_CONV (srw_ss()) [Once pegTheory.peg_eval_cases]

val disjImpI = prove(``~p \/ q ⇔ p ⇒ q``, DECIDE_TAC)

val ptree_head_eq_tok0 = prove(
  ``(ptree_head pt = TOK tk) ⇔ (pt = Lf (TOK tk))``,
  Cases_on `pt` >> simp[]);
val ptree_head_eq_tok = save_thm(
  "ptree_head_eq_tok",
  CONJ ptree_head_eq_tok0
       (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ)) ptree_head_eq_tok0))
val _ = export_rewrites ["ptree_head_eq_tok"]

open NTpropertiesTheory
val firstSet_nTyVarList = Store_thm(
  "firstSet_nTyVarList",
  ``firstSet mmlG [NT (mkNT nTyVarList)] = { TyvarT s | T }``,
  simp[firstSetML_eqn] >> simp[firstSetML_def] >>
  simp[cmlG_applied, cmlG_FDOM] >> simp[firstSetML_def] >>
  simp[cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM] >>
  simp[firstSetML_def]);
val _ =
    firstSetML_def |> CONJUNCTS |> (fn l => List.take(l,2)) |> rewrites
                   |> (fn ss => augment_srw_ss [ss])

val firstSet_nLetDec = Store_thm(
  "firstSet_nLetDec",
  ``firstSet mmlG [NT (mkNT nLetDec)] = {ValT; FunT}``,
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM,
       cmlG_applied, INSERT_UNION_EQ]);

val firstSet_nLetDecs = Store_thm(
  "firstSet_nLetDecs",
  ``firstSet mmlG [NT (mkNT nLetDecs)] = {ValT; FunT; SemicolonT}``,
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM,
       cmlG_applied] >>
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied, INSERT_UNION_EQ]);

val firstSet_nMultOps = Store_thm(
  "firstSet_nMultOps",
  ``firstSet mmlG (NT (mkNT nMultOps)::rest) =
      {AlphaT "div"; AlphaT"mod"; StarT; SymbolT "/"}``,
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ]);

val firstSet_nRelOps = Store_thm(
  "firstSet_nRelOps",
  ``firstSet mmlG (NT (mkNT nRelOps)::rest) =
      {SymbolT "<"; SymbolT ">"; SymbolT "<="; SymbolT ">="; SymbolT "<>";
       EqualsT}``,
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]);

val firstSet_nAddOps = Store_thm(
  "firstSet_nAddOps",
  ``firstSet mmlG (NT (mkNT nAddOps)::rest) = {SymbolT "+"; SymbolT "-"}``,
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_applied, cmlG_FDOM,
       INSERT_UNION_EQ]);

val firstSet_nCompOps = Store_thm(
  "firstSet_nCompOps",
  ``firstSet mmlG (NT (mkNT nCompOps)::rest) = {AlphaT "o"; SymbolT ":="}``,
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ])

val firstSet_nUQTyOp = store_thm(
  "firstSet_nUQTyOp",
  ``firstSet mmlG [NT (mkNT nUQTyOp)] = { AlphaT l | T } ∪ { SymbolT l | T }``,
  dsimp[EXTENSION, EQ_IMP_THM, firstSet_def] >> rpt conj_tac >>
  simp[Once relationTheory.RTC_CASES1, cmlG_applied, cmlG_FDOM] >>
  dsimp[]);

val firstSet_nStructure = Store_thm(
  "firstSet_nStructure",
  ``firstSet mmlG [NT (mkNT nStructure)] = {StructureT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]);

val firstSet_nTypeDec = Store_thm(
  "firstSet_nTypeDec",
  ``firstSet mmlG [NT (mkNT nTypeDec)] = {DatatypeT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]);

val firstSet_nDecl = Store_thm(
  "firstSet_nDecl",
  ``firstSet mmlG [NT (mkNT nDecl)] = {ValT; FunT; DatatypeT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ]);

val firstSet_nTopLevelDec = Store_thm(
  "firstSet_nTopLevelDec",
  ``firstSet mmlG [NT (mkNT nTopLevelDec)] =
    {ValT; FunT; DatatypeT; StructureT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied, INSERT_UNION_EQ, INSERT_COMM]);

val firstSet_nTopLevelDecs = Store_thm(
  "firstSet_nTopLevelDecs",
  ``firstSet mmlG [NN nTopLevelDecs] = {ValT; FunT; DatatypeT; StructureT}``,
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM] >>
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM] >>
  simp[INSERT_UNION_EQ, INSERT_COMM]);

val firstSet_nSpecLine = Store_thm(
  "firstSet_nSpecLine",
  ``firstSet mmlG [NT (mkNT nSpecLine)] = {ValT; DatatypeT; TypeT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied, INSERT_UNION_EQ, INSERT_COMM]);

val firstSet_nSpecLineList = Store_thm(
  "firstSet_nSpecLineList",
  ``firstSet mmlG [NT (mkNT nSpecLineList)] =
      {ValT; DatatypeT; TypeT; SemicolonT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ, INSERT_COMM]);

val firstSet_nTypeDec = Store_thm(
  "firstSet_nTypeDec",
  ``firstSet mmlG [NT (mkNT nTypeDec)] = {DatatypeT}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]);

val firstSet_nV = store_thm(
  "firstSet_nV",
  ``firstSet mmlG (NN nV:: rest) =
      { AlphaT s | s ≠ "" ∧ ¬isUpper (HD s) ∧ s ≠ "before" ∧ s ≠ "div" ∧
                   s ≠ "mod" ∧ s ≠ "o" ∧ s ≠ "true" ∧ s ≠ "false" ∧ s ≠ "ref"} ∪
      { SymbolT s | s ≠ "+" ∧ s ≠ "*" ∧ s ≠ "-" ∧ s ≠ "/" ∧ s ≠ "<" ∧ s ≠ ">" ∧
                    s ≠ "<=" ∧ s ≠ ">=" ∧ s ≠ "<>" ∧ s ≠ ":="}``,
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]);

val firstSet_nVlist1 = Store_thm(
  "firstSet_nVlist1",
  ``firstSet mmlG (NN nVlist1 :: rest) = firstSet mmlG [NN nV]``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied, firstSet_nV]);

val firstSet_nFQV = store_thm(
  "firstSet_nFQV",
  ``firstSet mmlG [NT (mkNT nFQV)] =
      firstSet mmlG [NT (mkNT nV)] ∪
      { LongidT m i | (m,i) | i ≠ "" ∧ (isAlpha (HD i) ⇒ ¬isUpper (HD i))}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION]);

val firstSet_nConstructorName = store_thm(
  "firstSet_nConstructorName",
  ``firstSet mmlG (NN nConstructorName :: rest) =
      { LongidT str s | (str,s) | s ≠ "" ∧ isAlpha (HD s) ∧ isUpper (HD s) } ∪
      { AlphaT s | s ≠ "" ∧ isUpper (HD s) } ∪
      { AlphaT "true"; AlphaT "false"; AlphaT "ref"}``,
  ntac 2 (simp [Once firstSet_NT, cmlG_applied, cmlG_FDOM]) >>
  dsimp[Once EXTENSION, EQ_IMP_THM]);

val firstSetML_nConstructorName = Store_thm(
  "firstSetML_nConstructorName",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ⇒
    (firstSetML mmlG sn (NN nConstructorName::rest) =
     firstSet mmlG [NN nConstructorName])``,
  simp[firstSetML_eqn] >>
  ntac 2 (simp[firstSetML_def] >> simp[cmlG_applied, cmlG_FDOM]) >>
  strip_tac >> simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[firstSetML_def]);

val firstSetML_nV = Store_thm(
  "firstSetML_nV",
  ``mkNT nV ∉ sn ⇒
    (firstSetML mmlG sn (NN nV::rest) = firstSet mmlG [NN nV])``,
  simp[firstSetML_eqn] >> simp[firstSetML_def] >>
  simp[cmlG_FDOM, cmlG_applied] >> strip_tac >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSetML_nFQV = Store_thm(
  "firstSetML_nFQV",
  ``mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ⇒
    (firstSetML mmlG sn (NN nFQV::rest) = firstSet mmlG [NN nFQV])``,
  simp[firstSetML_eqn] >>
  ntac 2 (simp[firstSetML_def] >> simp[cmlG_FDOM, cmlG_applied]) >>
  strip_tac >> simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSet_nEbase = Store_thm(
  "firstSet_nEbase",
  ``firstSet mmlG [NT (mkNT nEbase)] =
      {LetT; LparT} ∪ firstSet mmlG [NT (mkNT nFQV)] ∪ {IntT i | T} ∪
      firstSet mmlG [NT (mkNT nConstructorName)]``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION] >> gen_tac >> eq_tac >> rw[] >> simp[]);

val firstSetML_nEbase = Store_thm(
  "firstSetML_nEbase",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEbase)::rest) =
    firstSet mmlG [NT (mkNT nEbase)]``,
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >> strip_tac >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSet_nEapp = Store_thm(
  "firstSet_nEapp",
  ``firstSet mmlG [NT (mkNT nEapp)] = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[Once firstSetML_eqn, SimpLHS] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSetML_nEapp = Store_thm(
  "firstSetML_nEapp",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEapp) :: rest) =
    firstSet mmlG [NT(mkNT nEbase)]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSet_nEmult = Store_thm(
  "firstSet_nEmult",
  ``firstSet mmlG [NT (mkNT nEmult)] = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nEmult = Store_thm(
  "firstSetML_nEmult",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEmult) :: rest) =
    firstSet mmlG [NT (mkNT nEbase)]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nEadd = Store_thm(
  "firstSet_nEadd",
  ``firstSet mmlG [NT (mkNT nEadd)] = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nEadd = Store_thm(
  "firstSetML_nEadd",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEadd) :: rest) =
    firstSet mmlG [NT(mkNT nEbase)]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nErel = Store_thm(
  "firstSet_nErel",
  ``firstSet mmlG (NT(mkNT nErel)::rest) = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nErel = Store_thm(
  "firstSetML_nErel",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nErel) :: rest) = firstSet mmlG [NN nEbase]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nEcomp = Store_thm(
  "firstSet_nEcomp",
  ``firstSet mmlG (NT(mkNT nEcomp)::rest) = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nEcomp = Store_thm(
  "firstSetML_nEcomp",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEcomp) :: rest) = firstSet mmlG [NN nEbase]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nEbefore = Store_thm(
  "firstSet_nEbefore",
  ``firstSet mmlG (NT(mkNT nEbefore)::rest) =
      firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nEbefore = Store_thm(
  "firstSetML_nEbefore",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEbefore)::rest) = firstSet mmlG [NN nEbase]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nEtyped = Store_thm(
  "firstSet_nEtyped",
  ``firstSet mmlG (NT(mkNT nEtyped)::rest) = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nEtyped = Store_thm(
  "firstSetML_nEtyped",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEtyped)::rest) = firstSet mmlG [NN nEbase]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nElogicAND = Store_thm(
  "firstSet_nElogicAND",
  ``firstSet mmlG (NT(mkNT nElogicAND)::rest) = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nElogicAND = Store_thm(
  "firstSetML_nElogicAND",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nElogicAND)::rest) =
      firstSet mmlG [NN nEbase]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nElogicOR = Store_thm(
  "firstSet_nElogicOR",
  ``firstSet mmlG (NT(mkNT nElogicOR)::rest) = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nElogicOR = Store_thm(
  "firstSetML_nElogicOR",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
    mkNT nElogicOR ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nElogicOR)::rest) =
      firstSet mmlG [NN nEbase]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nEhandle = Store_thm(
  "firstSet_nEhandle",
  ``firstSet mmlG (NT(mkNT nEhandle)::rest) = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nEhandle = Store_thm(
  "firstSetML_nEhandle",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
    mkNT nElogicOR ∉ sn ∧ mkNT nEhandle ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEhandle)::rest) =
      firstSet mmlG [NN nEbase]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nEhandle' = Store_thm(
  "firstSet_nEhandle'",
  ``firstSet mmlG (NT(mkNT nEhandle')::rest) = firstSet mmlG [NT (mkNT nEbase)]``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSetML_nEhandle' = Store_thm(
  "firstSetML_nEhandle'",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
    mkNT nElogicOR ∉ sn ∧ mkNT nEhandle' ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nEhandle')::rest) =
      firstSet mmlG [NN nEbase]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]));

val firstSet_nE = store_thm(
  "firstSet_nE",
  ``firstSet mmlG (NT(mkNT nE)::rest) =
      firstSet mmlG [NT (mkNT nEbase)] ∪ {IfT; CaseT; FnT; RaiseT}``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val NOTIN_firstSet_nE = Store_thm(
  "NOTIN_firstSet_nE",
  ``ValT ∉ firstSet mmlG (NT (mkNT nE) :: rest) ∧
    StructureT ∉ firstSet mmlG (NT (mkNT nE) :: rest) ∧
    FunT ∉ firstSet mmlG (NT (mkNT nE) :: rest) ∧
    DatatypeT ∉ firstSet mmlG (NT (mkNT nE) :: rest) ∧
    SemicolonT ∉ firstSet mmlG (NT (mkNT nE) :: rest)``,
  simp[firstSet_nE, firstSet_nFQV] >>
  rpt (dsimp[Once firstSet_NT, cmlG_FDOM, cmlG_applied, disjImpI]))

val firstSetML_nE = Store_thm(
  "firstSetML_nE",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
    mkNT nElogicOR ∉ sn ∧ mkNT nEhandle ∉ sn ∧ mkNT nE ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nE)::rest) = firstSet mmlG [NN nE]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM, firstSet_nE]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSet_nE' = store_thm(
  "firstSet_nE'",
  ``firstSet mmlG (NT(mkNT nE')::rest) =
      firstSet mmlG [NT (mkNT nEbase)] ∪ {IfT; FnT; RaiseT}``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSetML_nE' = Store_thm(
  "firstSetML_nE'",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
    mkNT nElogicOR ∉ sn ∧ mkNT nEhandle' ∉ sn ∧ mkNT nE' ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nE')::rest) = firstSet mmlG [NN nE']``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM, firstSet_nE']) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSet_nPbase = Store_thm(
  "firstSet_nPbase",
  ``firstSet mmlG (NN nPbase :: rest) =
      {LparT; UnderbarT } ∪ {IntT i | T } ∪
      firstSet mmlG [NN nConstructorName] ∪ firstSet mmlG [NN nV]``,
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]);

val firstSetML_nPbase = Store_thm(
  "firstSetML_nPbase",
  ``mkNT nPbase ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nConstructorName ∉ sn ∧
    mkNT nUQConstructorName ∉ sn ⇒
    firstSetML mmlG sn (NN nPbase :: rest) = firstSet mmlG [NN nPbase]``,
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]);

val firstSet_nPattern = Store_thm(
  "firstSet_nPattern",
  ``firstSet mmlG (NN nPattern :: rest) = firstSet mmlG [NN nPbase]``,
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]);

val NOTIN_firstSet_nV = Store_thm(
  "NOTIN_firstSet_nV",
  ``CommaT ∉ firstSet mmlG [NN nV] ∧ LparT ∉ firstSet mmlG [NN nV] ∧
    RparT ∉ firstSet mmlG [NN nV] ∧ UnderbarT ∉ firstSet mmlG [NN nV] ∧
    FnT ∉ firstSet mmlG [NN nV] ∧ IfT ∉ firstSet mmlG [NN nV] ∧
    EqualsT ∉ firstSet mmlG [NN nV] ∧ DarrowT ∉ firstSet mmlG [NN nV] ∧
    ValT ∉ firstSet mmlG [NN nV] ∧ FunT ∉ firstSet mmlG [NN nV] ∧
    SemicolonT ∉ firstSet mmlG [NN nV] ∧ ColonT ∉ firstSet mmlG [NN nV]``,
  simp[firstSet_nV]);

val NOTIN_firstSet_nFQV = Store_thm(
  "NOTIN_firstSet_nFQV",
  ``CommaT ∉ firstSet mmlG [NN nFQV] ∧ LparT ∉ firstSet mmlG [NN nFQV] ∧
    RparT ∉ firstSet mmlG [NN nFQV] ∧ UnderbarT ∉ firstSet mmlG [NN nFQV] ∧
    FnT ∉ firstSet mmlG [NN nFQV] ∧ IfT ∉ firstSet mmlG [NN nFQV] ∧
    EqualsT ∉ firstSet mmlG [NN nFQV] ∧ DarrowT ∉ firstSet mmlG [NN nFQV] ∧
    ValT ∉ firstSet mmlG [NN nFQV] ∧ FunT ∉ firstSet mmlG [NN nFQV] ∧
    SemicolonT ∉ firstSet mmlG [NN nFQV] ∧ ColonT ∉ firstSet mmlG [NN nFQV]``,
  simp[firstSet_nFQV]);

val NOTIN_firstSet_nConstructorName = Store_thm(
  "NOTIN_firstSet_nConstructorName",
  ``CommaT ∉ firstSet mmlG [NN nConstructorName] ∧
    LparT ∉ firstSet mmlG [NN nConstructorName] ∧
    ColonT ∉ firstSet mmlG [NN nConstructorName] ∧
    RparT ∉ firstSet mmlG [NN nConstructorName] ∧
    FnT ∉ firstSet mmlG [NN nConstructorName] ∧
    ValT ∉ firstSet mmlG [NN nConstructorName] ∧
    FunT ∉ firstSet mmlG [NN nConstructorName] ∧
    UnderbarT ∉ firstSet mmlG [NN nConstructorName] ∧
    SemicolonT ∉ firstSet mmlG [NN nConstructorName] ∧
    EqualsT ∉ firstSet mmlG [NN nConstructorName] ∧
    DarrowT ∉ firstSet mmlG [NN nConstructorName] ∧
    IfT ∉ firstSet mmlG [NN nConstructorName]``,
  simp[firstSet_nConstructorName]);

val mmlPEG_total =
    pegTheory.peg_eval_total |> Q.GEN `G` |> Q.ISPEC `mmlPEG`
                             |> C MATCH_MP PEG_wellformed

val nVlist1_expr =
    ``nt (mkNT nVlist1) I ∈ Gexprs mmlPEG``
      |> SIMP_CONV (srw_ss()) [PEG_exprs] |> EQT_ELIM

val peg_respects_firstSets = store_thm(
  "peg_respects_firstSets",
  ``∀N i0 t.
      t ∉ firstSet mmlG [NT N] ∧ ¬peg0 mmlPEG (nt N I) ∧
      nt N I ∈ Gexprs mmlPEG ⇒
      peg_eval mmlPEG (t::i0, nt N I) NONE``,
  rpt gen_tac >> CONV_TAC CONTRAPOS_CONV >> simp[] >>
  Cases_on `nt N I ∈ Gexprs mmlPEG` >> simp[] >>
  IMP_RES_THEN (qspec_then `t::i0` (qxchl [`r`] assume_tac)) mmlPEG_total >>
  pop_assum (assume_tac o MATCH_MP (CONJUNCT1 pegTheory.peg_deterministic)) >>
  simp[] >>
  `r = NONE ∨ ∃i ptl. r = SOME(i,ptl)`
    by metis_tac[optionTheory.option_CASES, pairTheory.pair_CASES] >>
  simp[] >> rveq >>
  `∃pt. ptl = [pt] ∧ ptree_head pt = NT N ∧ valid_ptree mmlG pt ∧
        MAP TK (t::i0) = ptree_fringe pt ++ MAP TK i`
    by metis_tac [peg_sound] >>
  rveq >> Cases_on `peg0 mmlPEG (nt N I)` >> simp[] >>
  `LENGTH i < LENGTH (t::i0)` by metis_tac [not_peg0_LENGTH_decreases] >>
  `ptree_fringe pt = [] ∨ ∃tk rest. ptree_fringe pt = TK tk:: MAP TK rest`
    by (Cases_on `ptree_fringe pt` >> simp[] >> fs[] >> rveq >>
        fs[MAP_EQ_APPEND] >> metis_tac[])
  >- (fs[] >> pop_assum kall_tac >>
      first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  fs[] >> rveq >> metis_tac [firstSet_nonempty_fringe])

val sym2peg_def = Define`
  sym2peg (TOK tk) = tokeq tk ∧
  sym2peg (NT N) = nt N I
`;

val not_peg0_peg_eval_NIL_NONE = store_thm(
  "not_peg0_peg_eval_NIL_NONE",
  ``¬peg0 G sym ∧ sym ∈ Gexprs G ∧ wfG G ⇒
    peg_eval G ([], sym) NONE``,
  strip_tac >>
  `∃r. peg_eval G ([], sym) r`
    by metis_tac [pegTheory.peg_eval_total] >>
  Cases_on `r` >> simp[] >> Cases_on `x` >>
  erule mp_tac not_peg0_LENGTH_decreases >> simp[]);

val list_case_lemma = prove(
  ``([x] = case a of [] => [] | h::t => f h t) ⇔
    (a ≠ [] ∧ [x] = f (HD a) (TL a))``,
  Cases_on `a` >> simp[]);

val left_insert_def = Define`
  (left_insert (Lf x) p sep c = Lf x) ∧
  (left_insert (Nd n subs) p sep c =
     if n <> p then Nd n subs
     else
       case subs of
           [c0] => Nd p [Nd p [c]; sep; c0]
         | [p'; s'; c'] => Nd p [left_insert p' p sep c; s'; c']
         | _ => Nd p subs)
`;

val lassoc_reassociated = store_thm(
  "lassoc_reassociated",
  ``∀G P SEP C ppt spt cpt pf sf cf.
      G.rules ' P = {[NT P; SEP; C]; [C]} ⇒
      valid_ptree G ppt ∧ ptree_head ppt = NT P ∧
      ptree_fringe ppt = MAP TOK pf ∧
      valid_ptree G spt ∧ ptree_head spt = SEP ∧ ptree_fringe spt = MAP TOK sf ∧
      valid_ptree G cpt ∧ ptree_head cpt = C ∧ ptree_fringe cpt = MAP TOK cf ⇒
      ∃cpt' spt' ppt'.
        valid_ptree G ppt' ∧ ptree_head ppt' = NT P ∧
        valid_ptree G spt' ∧ ptree_head spt' = SEP ∧
        valid_ptree G cpt' ∧ ptree_head cpt' = C ∧
        ptree_fringe cpt' ++ ptree_fringe spt' ++ ptree_fringe ppt' =
        MAP TOK (pf ++ sf ++ cf) ∧
        Nd P [ppt; spt; cpt] = left_insert ppt' P spt' cpt'``,
  rpt gen_tac >> strip_tac >>
  map_every qid_spec_tac [`cf`, `sf`, `pf`, `cpt`, `spt`, `ppt`] >>
  ho_match_mp_tac grammarTheory.ptree_ind >> simp[MAP_EQ_SING] >>
  qx_gen_tac `subs` >> strip_tac >> simp[MAP_EQ_CONS] >>
  reverse (rpt strip_tac) >> rveq >> fs[]
  >- (qpat_assum `!x. PP x` kall_tac >>
      asm_match `ptree_fringe c0pt = MAP TOK pf` >>
      map_every qexists_tac [`c0pt`, `spt`, `Nd P [cpt]`] >>
      simp[left_insert_def]) >>
  asm_match `ptree_head ppt = NT P` >>
  asm_match `ptree_head s0pt = ptree_head spt` >>
  asm_match `ptree_head c0pt = ptree_head cpt` >>
  fs [MAP_EQ_APPEND] >> rveq >>
  asm_match `ptree_fringe ppt = MAP TOK pf` >>
  asm_match `ptree_fringe s0pt = MAP TOK sf0` >>
  asm_match `ptree_fringe c0pt = MAP TOK cf0` >>
  first_x_assum (fn th =>
    first_x_assum (qspec_then `ppt` mp_tac) >>
    mp_tac (assert (is_forall o concl) th)) >>
  simp[] >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  disch_then (qspecl_then [`s0pt`, `c0pt`, `pf`, `sf0`, `cf0`] mp_tac) >>
  simp[] >>
  disch_then (qxchl [`cpt'`, `spt'`, `ppt'`] strip_assume_tac) >>
  map_every qexists_tac [`cpt'`, `spt'`, `Nd P [ppt'; spt; cpt]`] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, left_insert_def])

val left_insert_mk_linfix = store_thm(
  "left_insert_mk_linfix",
  ``left_insert (mk_linfix N acc arg) N s c =
    mk_linfix N (left_insert acc N s c) arg``,
  qid_spec_tac `acc` >> completeInduct_on `LENGTH arg` >> rw[] >>
  full_simp_tac (srw_ss() ++ DNF_ss)[] >>
  `arg = [] ∨ ∃h1 t. arg = h1::t` by (Cases_on `arg` >> simp[])
  >- simp[mk_linfix_def] >>
  `t = [] ∨ ∃h2 t2. t = h2::t2` by (Cases_on `t` >> simp[])
  >- simp[mk_linfix_def] >>
  rw[] >> simp[mk_linfix_def, left_insert_def]);

val REVERSE_11 = store_thm(
  "REVERSE_11",
  ``(REVERSE l1 = REVERSE l2) ⇔ (l1 = l2)``,
  METIS_TAC [listTheory.REVERSE_REVERSE])
val _ = export_rewrites ["REVERSE_11"]

val firstSets_nV_nConstructorName = store_thm(
  "firstSets_nV_nConstructorName",
  ``¬(t ∈ firstSet mmlG [NN nConstructorName] ∧ t ∈ firstSet mmlG [NN nV])``,
  Cases_on `t ∈ firstSet mmlG [NN nV]` >> simp[] >>
  fs[firstSet_nV, firstSet_nConstructorName]);

val elim_disjineq = prove( ``p \/ x ≠ y ⇔ (x = y ⇒ p)``, DECIDE_TAC)
val elim_det = prove(``(!x. P x ⇔ (x = y)) ==> P y``, METIS_TAC[])

val peg_det = CONJUNCT1 pegTheory.peg_deterministic

val peg_seql_NONE_det = store_thm(
  "peg_seql_NONE_det",
  ``peg_eval G (i0, seql syms f) NONE ⇒
    ∀f' r. peg_eval G (i0, seql syms f') r ⇔ r = NONE``,
  Induct_on `syms` >> simp[] >> rpt strip_tac >>
  rpt (first_x_assum (assume_tac o MATCH_MP peg_det)) >> simp[]);

val peg_seql_NONE_append = store_thm(
  "peg_seql_NONE_append",
  ``∀i0 f. peg_eval G (i0, seql (l1 ++ l2) f) NONE ⇔
           peg_eval G (i0, seql l1 I) NONE ∨
           ∃i' r. peg_eval G (i0, seql l1 I) (SOME(i',r)) ∧
                  peg_eval G (i', seql l2 I) NONE``,
  Induct_on `l1` >> simp[] >- metis_tac [peg_seql_NONE_det] >>
  map_every qx_gen_tac [`h`, `i0`] >>
  Cases_on `peg_eval G (i0,h) NONE` >> simp[] >>
  dsimp[] >> metis_tac[]);

val peg_seql_SOME_append = store_thm(
  "peg_seql_SOME_append",
  ``∀i0 l2 f i r.
      peg_eval G (i0, seql (l1 ++ l2) f) (SOME(i,r)) ⇔
      ∃i' r1 r2.
          peg_eval G (i0, seql l1 I) (SOME(i',r1)) ∧
          peg_eval G (i', seql l2 I) (SOME(i,r2)) ∧
          (r = f (r1 ++ r2))``,
  Induct_on `l1` >> simp[]
  >- (Induct_on `l2` >- simp[] >>
      ONCE_REWRITE_TAC [peg_eval_seql_CONS] >>
      simp_tac (srw_ss() ++ DNF_ss) []) >>
  dsimp[] >> metis_tac[]);

fun has_const c = assert (Lib.can (find_term (same_const c)) o concl)

val nE'_nE = store_thm(
  "nE'_nE",
  ``∀i0 i r.
      peg_eval mmlPEG (i0, nt (mkNT nE') I) (SOME(i,r)) ∧
      (i ≠ [] ⇒ HD i ≠ HandleT) ⇒
      ∃r'. peg_eval mmlPEG (i0, nt (mkNT nE) I) (SOME(i,r'))``,
  gen_tac >> completeInduct_on `LENGTH i0` >> gen_tac >> strip_tac >>
  full_simp_tac (srw_ss() ++ DNF_ss) [AND_IMP_INTRO] >>
  simp[peg_eval_NT_SOME] >> simp[mmlpeg_rules_applied] >>
  rpt strip_tac >> rveq >> simp[peg_eval_tok_NONE] >> fs[]
  >- metis_tac[]
  >- (dsimp[] >> DISJ2_TAC >> DISJ1_TAC >>
      qpat_assum `peg_eval X Y (SOME Z)` mp_tac >> simp[peg_eval_NT_SOME] >>
      simp_tac list_ss [mmlpeg_rules_applied] >>
      ONCE_REWRITE_TAC [peg_eval_seql_CONS] >>
      simp_tac list_ss [pnt_def, tokeq_def] >> strip_tac >> rveq >>
      pop_assum mp_tac >>
      qabbrev_tac `
        L1 = [tok ($= HandleT) mktokLf; tok ($= (AlphaT "IntError")) mktokLf;
              nt (mkNT nV) I; tok ($= DarrowT) mktokLf]
      ` >>
      `∀e. L1 ++ [e] = L1 ++ [e]` by simp[] >>
      pop_assum mp_tac >>
      pop_assum (fn abbr =>
        let val th = REWRITE_RULE [markerTheory.Abbrev_def] abbr
        in
          CONV_TAC (LAND_CONV
                      (BINDER_CONV (LAND_CONV (REWRITE_CONV [th])))) >>
          assume_tac abbr
        end) >> simp_tac bool_ss [listTheory.APPEND] >>
      disch_then kall_tac >>
      ONCE_REWRITE_TAC [peg_eval_seql_CONS] >>
      simp_tac (list_ss ++ DNF_ss) [try_def, peg_eval_seql_NIL] >>
      rpt strip_tac >> rveq >> pop_assum mp_tac >>
      ONCE_REWRITE_TAC [peg_eval_choicel_CONS] >>
      simp_tac list_ss [peg_eval_choicel_SING, peg_eval_empty] >>
      first_x_assum (assume_tac o MATCH_MP peg_det o
                     assert (free_in ``nElogicOR`` o concl)) >>
      asm_simp_tac list_ss [] >>
      strip_tac >> rveq
      >- (simp_tac (list_ss ++ DNF_ss) [] >> DISJ1_TAC >>
          pop_assum mp_tac >> simp[peg_seql_SOME_append] >>
          strip_tac >> rveq >> simp[] >>
          first_x_assum (assume_tac o MATCH_MP peg_det o
                         has_const ``seql``) >> simp[] >>
          rpt (first_x_assum (assume_tac o MATCH_MP elim_det)) >>
          imp_res_tac length_no_greater >> fs[] >>
          first_x_assum match_mp_tac >>
          imp_res_tac (MATCH_MP not_peg0_LENGTH_decreases
                                peg0_nElogicOR) >>
          asimp[] >> metis_tac[]) >>
      simp_tac (list_ss ++ DNF_ss) [] >>
      pop_assum mp_tac >>
      simp[peg_seql_NONE_append, peg_seql_SOME_append] >> strip_tac >- simp[] >>
      Q.UNDISCH_THEN `peg_eval mmlPEG (i,seql L1 I) (SOME(i',r))`
        (assume_tac o MATCH_MP peg_det) >> simp[] >>
      rpt (first_x_assum (assume_tac o MATCH_MP elim_det)) >>
      first_x_assum (mp_tac o has_const ``seql``) >>
      simp[Abbr`L1`] >> strip_tac >> fs[])
  >- (dsimp[] >> DISJ2_TAC >>
      simp[peg_eval_seq_NONE, peg_respects_firstSets,
           firstSet_nFQV] >>
      rpt (first_x_assum (assume_tac o MATCH_MP peg_det o
                          assert (free_in ``nE`` o concl))) >>
      simp[] >> rpt (first_x_assum (assume_tac o MATCH_MP elim_det)) >>
      imp_res_tac length_no_greater >>
      first_x_assum match_mp_tac >> fs[] >> asimp[] >> metis_tac[])
  >- (dsimp[] >> DISJ2_TAC >>
      simp[peg_eval_seq_NONE, peg_respects_firstSets, firstSet_nFQV] >>
      rpt (first_x_assum (assume_tac o MATCH_MP peg_det o
                          assert (free_in ``nV`` o concl))) >>
      simp[] >> rpt (first_x_assum (assume_tac o MATCH_MP elim_det)) >>
      imp_res_tac length_no_greater >> fs[] >> first_x_assum match_mp_tac >>
      asimp[] >> metis_tac[]) >>
  dsimp[] >> imp_res_tac peg_sound >> rveq >>
  asm_match `ptree_head pt = NN nEhandle'` >>
  `0 < LENGTH (ptree_fringe pt)`
    by metis_tac [nullable_Ehandle', fringe_length_not_nullable] >>
  Cases_on `ptree_fringe pt` >> fs[] >> rveq >>
  IMP_RES_THEN mp_tac firstSet_nonempty_fringe >>
  simp[firstSet_nFQV, firstSet_nV, firstSet_nConstructorName])

val nE'_bar_nE = store_thm(
  "nE'_bar_nE",
  ``∀i0 i i' r r'.
        peg_eval mmlPEG (i0, nt (mkNT nE) I) (SOME(i,r)) ∧
        (i ≠ [] ⇒ HD i ≠ BarT ∧ HD i ≠ HandleT) ∧ i' ≠ [] ∧
        peg_eval mmlPEG (i0, nt (mkNT nE') I) (SOME(i',r')) ⇒
        HD i' ≠ BarT``,
  gen_tac >> completeInduct_on `LENGTH i0` >> rpt strip_tac >>
  full_simp_tac (srw_ss() ++ DNF_ss) [AND_IMP_INTRO] >> rw[] >>
  rpt (qpat_assum `peg_eval X Y Z` mp_tac) >>
  simp[peg_eval_NT_SOME] >>
  simp_tac std_ss [mmlpeg_rules_applied] >>
  simp_tac std_ss [Once peg_eval_choicel_CONS] >> strip_tac
  >- ((* raise case *)
      simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
      simp_tac (list_ss ++ DNF_ss) [peg_eval_seql_CONS] >>
      pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
      rw[] >> simp[peg_eval_tok_NONE] >>
      first_x_assum (assume_tac o MATCH_MP peg_det) >> simp[] >>
      metis_tac[]) >>
  first_x_assum (assume_tac o MATCH_MP peg_seql_NONE_det) >>
  qpat_assum `peg_eval mmlPEG X Y` mp_tac >>
  simp_tac std_ss [Once peg_eval_choicel_CONS] >>
  strip_tac
  >- ((* handle case *)
      asm_simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
      asm_simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
      DISJ2_TAC >> reverse conj_tac
      >- (simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS,
                                        peg_eval_choicel_SING] >>
          DISJ2_TAC >> conj_tac >>
          simp_tac list_ss [Once peg_eval_seql_CONS] >> rpt gen_tac >>
          DISJ1_TAC >> strip_tac >> fs[tokeq_def] >> rw[] >>
          imp_res_tac peg_sound >> fs[] >>
          asm_match `ptree_head pt = NN nEhandle` >>
          `0 < LENGTH (ptree_fringe pt)`
            by metis_tac [fringe_length_not_nullable,
                          nullable_Ehandle] >>
          Cases_on `ptree_fringe pt` >> fs[] >> rw[] >>
          IMP_RES_THEN mp_tac firstSet_nonempty_fringe >>
          simp[firstSet_nFQV]) >>
      pop_assum mp_tac >>
      simp[peg_eval_NT_SOME] >>
      simp_tac list_ss [mmlpeg_rules_applied, pnt_def, try_def, tokeq_def] >>
      ONCE_REWRITE_TAC [peg_eval_seql_CONS] >> simp_tac list_ss [] >>
      strip_tac >> rveq >>
      qpat_assum `peg_eval mmlPEG (i0, nt X Y) Z`
        (assume_tac o MATCH_MP peg_det) >>
      asm_simp_tac list_ss [] >>
      qpat_assum `peg_eval X Y Z` mp_tac >>
      simp_tac list_ss [peg_eval_seql_CONS, peg_eval_seql_NIL] >>
      simp_tac list_ss [peg_eval_choicel_CONS, peg_eval_empty,
                        elim_disjineq] >>
      qabbrev_tac `
        L1 = [tok ($= HandleT) mktokLf; tok ($= (AlphaT "IntError")) mktokLf;
              nt (mkNT nV) I; tok ($= DarrowT) mktokLf]
      ` >>
      `∀e. L1 ++ [e] = L1 ++ [e]` by simp[] >>
      pop_assum mp_tac >>
      pop_assum (fn abbr =>
        let val th = REWRITE_RULE [markerTheory.Abbrev_def] abbr
        in
          CONV_TAC (LAND_CONV
                      (BINDER_CONV (LAND_CONV (REWRITE_CONV [th])))) >>
          assume_tac abbr
        end) >> simp_tac bool_ss [listTheory.APPEND] >>
      disch_then kall_tac >>
      strip_tac
      >- (pop_assum mp_tac >> simp[peg_seql_SOME_append] >>
          strip_tac >> rveq >>
          first_x_assum (assume_tac o MATCH_MP peg_det o has_const ``seql``) >>
          simp[] >> simp[elim_disjineq] >> rpt (gen_tac ORELSE DISCH_TAC) >>
          rveq >> simp[peg_seql_NONE_append] >>
          conj_tac
          >- (rpt strip_tac >>
              asm_match `peg_eval mmlPEG (badi, nt(mkNT nE) I) (SOME(i,rr))` >>
              asm_match `peg_eval mmlPEG (badi,nt(mkNT nE') I) (SOME(i',r3))` >>
              first_x_assum (qspecl_then [`badi`, `i`, `i'`, `rr`, `r3`] mp_tac) >>
              simp[] >>
              rpt (first_x_assum (assume_tac o MATCH_MP elim_det)) >>
              imp_res_tac length_no_greater >> fs[] >>
              IMP_RES_TAC (MATCH_MP not_peg0_LENGTH_decreases peg0_nElogicOR) >>
              asimp[]) >>
          DISJ2_TAC >> rpt strip_tac >>
          rpt (first_x_assum (assume_tac o MATCH_MP elim_det)) >>
          markerLib.UNABBREV_TAC "L1" >> fs[] >> rveq >> fs[]) >>
      rveq >> pop_assum mp_tac >>
      simp[peg_seql_NONE_append, peg_seql_SOME_append] >>
      strip_tac >> simp[]
      >- (pop_assum (assume_tac o MATCH_MP peg_det o has_const ``seql``) >>
          simp[] >> rpt strip_tac >> fs[]) >>
      first_x_assum (assume_tac o MATCH_MP peg_det o has_const ``seql``) >>
      simp[] >> rpt (gen_tac ORELSE DISCH_TAC) >> rveq >>
      `i' ≠ i`  by metis_tac[] >> simp[elim_disjineq] >>
      rpt (gen_tac ORELSE DISCH_TAC) >> rveq >>
      first_assum (mp_tac o PART_MATCH (lhand o lhand) nE'_nE o concl) >>
      simp[] >>
      first_x_assum (assume_tac o MATCH_MP peg_det o has_const ``nE``) >>
      simp[]) >>
  asm_simp_tac list_ss [Once peg_eval_choicel_CONS] >>
  pop_assum mp_tac >>
  asm_simp_tac list_ss [Once peg_eval_choicel_CONS] >>
  strip_tac
  >- ((* if-then-else *)
      full_simp_tac list_ss [peg_eval_seql_CONS, tokeq_def, pnt_def, pegf_def,
                             peg_eval_tok_SOME, peg_eval_seql_NIL,
                             peg_eval_seq_NONE, peg_eval_empty] >> rveq >>
      dsimp[] >>
      rpt (first_x_assum (assume_tac o MATCH_MP peg_det o has_const ``nE``)) >>
      simp[elim_disjineq, peg_eval_seq_NONE] >>
      rpt (first_x_assum (assume_tac o MATCH_MP elim_det)) >>
      asm_match `peg_eval mmlPEG (IfT::i1, nt (mkNT nEhandle) I) NONE` >>
      `peg_eval mmlPEG (IfT::i1, nt (mkNT nEhandle') I) NONE`
         by simp[firstSet_nFQV, peg_respects_firstSets] >>
      pop_assum (assume_tac o MATCH_MP peg_det) >> simp[] >>
      rpt strip_tac >> rveq >>
      asm_match `peg_eval mmlPEG (ii, nt (mkNT nE') I) (SOME(jj, rr))` >>
      asm_match `peg_eval mmlPEG (ii, nt (mkNT nE) I) (SOME(kk, ss))` >>
      first_x_assum (qspecl_then [`ii`, `kk`, `jj`, `ss`, `rr`] mp_tac) >>
      simp[] >> imp_res_tac length_no_greater >> fs[] >> asimp[]) >>
  asm_simp_tac list_ss [Once peg_eval_choicel_CONS] >>
  full_simp_tac list_ss [pnt_def, pegf_def, peg_eval_seq_SOME, peg_eval_seq_NONE,
                         peg_eval_empty] >>
  pop_assum mp_tac >>
  asm_simp_tac list_ss [elim_disjineq, Once peg_eval_choicel_CONS] >> strip_tac
  >- ((* fn v => e *)
      pop_assum mp_tac >>
      asm_simp_tac list_ss [peg_eval_seql_CONS, tokeq_def, peg_eval_tok_SOME] >>
      strip_tac >> rveq >>
      asm_simp_tac list_ss [peg_eval_choicel_CONS, peg_eval_seql_CONS,
                            peg_eval_tok_NONE, peg_eval_tok_SOME] >>
      simp[disjImpI, elim_disjineq] >>
      asm_match `peg_eval mmlPEG (i1, nt (mkNT nV) I) (SOME(DarrowT::i2,r1))` >>
      `peg_eval mmlPEG (FnT::i1, nt (mkNT nEhandle') I) NONE`
        by simp[firstSet_nFQV, peg_respects_firstSets] >>
      rpt (first_x_assum (assume_tac o MATCH_MP peg_det)) >> simp[] >>
      rpt strip_tac >> rveq >>
      rpt (first_x_assum (assume_tac o MATCH_MP elim_det)) >>
      asm_match `peg_eval mmlPEG (i2, nt(mkNT nE) I) (SOME(i3,r3))` >>
      asm_match `peg_eval mmlPEG (i2, nt(mkNT nE') I) (SOME(i4,r4))` >>
      first_x_assum (qspecl_then [`i2`, `i3`, `i4`, `r3`, `r4`] mp_tac) >>
      simp[] >> fs[peg_eval_seql_NIL] >> rveq >>
      imp_res_tac length_no_greater >> fs[] >> asimp[]) >>
  pop_assum mp_tac >>
  asm_simp_tac list_ss [peg_eval_choicel_SING, peg_eval_seql_CONS,
                        peg_eval_seql_NIL, peg_eval_tok_SOME, tokeq_def] >>
  rpt strip_tac >> rveq >> fs[] >>
  asm_match `peg_eval mmlPEG (CaseT::i1, nt(mkNT nEhandle') I) (SOME(i2,r1))` >>
  `peg_eval mmlPEG (CaseT::i1, nt(mkNT nEhandle') I) NONE`
    by simp[firstSet_nFQV, firstSet_nV, firstSet_nConstructorName,
            peg_respects_firstSets] >>
  pop_assum (assume_tac o MATCH_MP peg_det) >> fs[])

val nestoppers_def = Define`
  nestoppers =
     UNIV DIFF ({AndalsoT; ArrowT; BarT; ColonT; HandleT; OrelseT;
                 AlphaT "before"} ∪
                firstSet mmlG [NN nMultOps] ∪
                firstSet mmlG [NN nRelOps] ∪
                firstSet mmlG [NN nAddOps] ∪
                firstSet mmlG [NN nCompOps] ∪
                firstSet mmlG [NN nEbase])
`;
val _ = export_rewrites ["nestoppers_def"]

val stoppers_def = Define`
  (stoppers nAndFDecls =
     UNIV DIFF ({BarT; HandleT} ∪ firstSet mmlG [NN nEbase])) ∧
  (stoppers nDtypeDecls = UNIV DELETE AndT) ∧
  (stoppers nE = nestoppers) ∧
  (stoppers nE' = BarT INSERT nestoppers) ∧
  (stoppers nEadd =
     UNIV DIFF (firstSet mmlG [NN nMultOps] ∪
                firstSet mmlG [NN nAddOps] ∪
                firstSet mmlG [NN nEbase])) ∧
  (stoppers nEapp = UNIV DIFF firstSet mmlG [NN nEbase]) ∧
  (stoppers nEbefore =
     UNIV DIFF ({AlphaT "before"} ∪
                firstSet mmlG [NN nCompOps] ∪
                firstSet mmlG [NN nRelOps] ∪
                firstSet mmlG [NN nMultOps] ∪
                firstSet mmlG [NN nAddOps] ∪
                firstSet mmlG [NN nEbase])) ∧
  (stoppers nEcomp =
     UNIV DIFF (firstSet mmlG [NN nCompOps] ∪
                firstSet mmlG [NN nRelOps] ∪
                firstSet mmlG [NN nMultOps] ∪
                firstSet mmlG [NN nAddOps] ∪
                firstSet mmlG [NN nEbase])) ∧
  (stoppers nEhandle = nestoppers) ∧
  (stoppers nEhandle' = BarT INSERT nestoppers) ∧
  (stoppers nElist1 = nestoppers DELETE CommaT) ∧
  (stoppers nElist2 = nestoppers DELETE CommaT) ∧
  (stoppers nElogicAND =
     UNIV DIFF ({AndalsoT; ColonT; ArrowT; AlphaT "before"} ∪
                firstSet mmlG [NN nCompOps] ∪
                firstSet mmlG [NN nRelOps] ∪
                firstSet mmlG [NN nMultOps] ∪
                firstSet mmlG [NN nAddOps] ∪
                firstSet mmlG [NN nEbase])) ∧
  (stoppers nElogicOR =
     UNIV DIFF ({AndalsoT; ColonT; ArrowT; OrelseT; AlphaT "before"} ∪
                firstSet mmlG [NN nCompOps] ∪
                firstSet mmlG [NN nRelOps] ∪
                firstSet mmlG [NN nMultOps] ∪
                firstSet mmlG [NN nAddOps] ∪
                firstSet mmlG [NN nEbase])) ∧
  (stoppers nEmult =
     UNIV DIFF (firstSet mmlG [NN nEbase] ∪
                firstSet mmlG [NN nMultOps])) ∧
  (stoppers nErel =
     UNIV DIFF (firstSet mmlG [NN nRelOps] ∪
                firstSet mmlG [NN nMultOps] ∪
                firstSet mmlG [NN nAddOps] ∪
                firstSet mmlG [NN nEbase])) ∧
  (stoppers nEseq = nestoppers DELETE SemicolonT) ∧
  (stoppers nEtyped =
     UNIV DIFF ({ColonT; ArrowT; AlphaT "before"} ∪
                firstSet mmlG [NN nCompOps] ∪
                firstSet mmlG [NN nRelOps] ∪
                firstSet mmlG [NN nMultOps] ∪
                firstSet mmlG [NN nAddOps] ∪
                firstSet mmlG [NN nEbase])) ∧
  (stoppers nFDecl = nestoppers) ∧
  (stoppers nLetDec = nestoppers) ∧
  (stoppers nLetDecs = nestoppers DIFF {FunT; ValT; SemicolonT}) ∧
  (stoppers nPattern =
     UNIV DIFF ({LparT; UnderbarT} ∪ { IntT i | T } ∪
                firstSet mmlG [NN nV] ∪ firstSet mmlG [NN nConstructorName])) ∧
  (stoppers nPatternList1 =
     UNIV DIFF ({CommaT; LparT; UnderbarT} ∪ {IntT i | T} ∪
                firstSet mmlG [NN nV] ∪ firstSet mmlG [NN nConstructorName])) ∧
  (stoppers nPE = nestoppers) ∧
  (stoppers nPE' = BarT INSERT nestoppers) ∧
  (stoppers nPEs = nestoppers) ∧
  (stoppers nSpecLine = UNIV DIFF {ArrowT; AndT}) ∧
  (stoppers nSpecLineList = UNIV DIFF {ValT; DatatypeT; TypeT; SemicolonT;
                                       ArrowT; AndT}) ∧
  (stoppers nStarTypes = UNIV DELETE StarT) ∧
  (stoppers nTopLevelDecs = UNIV DIFF {StructureT; ValT; FunT; DatatypeT}) ∧
  (stoppers nType = UNIV DELETE ArrowT) ∧
  (stoppers nTypeDec = UNIV DELETE AndT) ∧
  (stoppers nTypeList1 = UNIV DIFF {CommaT; ArrowT}) ∧
  (stoppers nTypeList2 = UNIV DIFF {CommaT; ArrowT}) ∧
  (stoppers nTyVarList = {RparT}) ∧
  (stoppers nOptionalSignatureAscription = UNIV DELETE SealT) ∧
  (stoppers nVlist1 = UNIV DIFF firstSet mmlG [NN nV]) ∧
  (stoppers _ = UNIV)
`;
val _ = export_rewrites ["stoppers_def"]


(* could generalise this slightly: allowing for nullable seps, but this would
   require a more complicated condition on the sfx, something like
     (sfx ≠ [] ∧ ¬nullable mmlG [SEP] ⇒ HD sfx ∉ firstSet mmlG [SEP]) ∧
     (sfx ≠ [] ∧ nullable mmlG [SEP] ⇒ HD sfx ∉ firstSet mmlG [C])
   and I can't be bothered with that right now. *)

fun attack_asmguard (g as (asl,w)) = let
  val (l,r) = dest_imp w
  val (h,c) = dest_imp l
in
  SUBGOAL_THEN h (fn th => DISCH_THEN (fn imp => MP_TAC (MATCH_MP imp th)))
end g

val peg_linfix_complete = store_thm(
  "peg_linfix_complete",
  ``(∀n. SEP = NT n ⇒
         ∃nn. n = mkNT nn ∧ nt (mkNT nn) I ∈ Gexprs mmlPEG ∧
              stoppers nn = UNIV) ∧
    (∀n. C = NT n ⇒ ∃nn. n = mkNT nn) ∧
    (∀t. t ∈ firstSet mmlG [SEP] ⇒ t ∉ stoppers P) ∧
    (∀n. C = NT (mkNT n) ⇒
         (∀t. t ∈ firstSet mmlG [SEP] ⇒ t ∈ stoppers n) ∧
         (∀t. t ∈ stoppers P ⇒ t ∈ stoppers n)) ∧
    ¬peg0 mmlPEG (sym2peg C) ∧ ¬nullable mmlG [C] ∧
    ¬peg0 mmlPEG (sym2peg SEP) ∧ ¬nullable mmlG [SEP] ∧
    mmlG.rules ' (mkNT P) = { [NT (mkNT P); SEP; C] ; [C] } ∧
    (∀pt pfx0 sfx.
       LENGTH pfx0 < LENGTH master ∧
       (∀n. ptree_head pt = NT (mkNT n) ∧ sfx ≠ [] ⇒ HD sfx ∈ stoppers n) ∧
       valid_ptree mmlG pt ∧ ptree_head pt ∈ {SEP; C} ∧
       ptree_fringe pt = MAP TOK pfx0 ⇒
       peg_eval mmlPEG (pfx0 ++ sfx, sym2peg (ptree_head pt))
                       (SOME(sfx,[pt]))) ∧
    (∀pt sfx.
       valid_ptree mmlG pt ∧ ptree_head pt = C ∧
       (∀n. C = NT (mkNT n) ∧ sfx ≠ [] ⇒ HD sfx ∈ stoppers n) ∧
       ptree_fringe pt = MAP TOK master ⇒
       peg_eval mmlPEG (master ++ sfx, sym2peg C) (SOME(sfx,[pt])))
 ⇒
    ∀pfx pt sfx.
      IS_SUFFIX master pfx ∧
      valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT P) ∧
      (sfx ≠ [] ⇒ HD sfx ∈ stoppers P) ∧
      ptree_fringe pt = MAP TOK pfx
  ⇒
      peg_eval mmlPEG (pfx ++ sfx,
                       peg_linfix (mkNT P) (sym2peg C) (sym2peg SEP))
                      (SOME(sfx,[pt]))``,
  strip_tac >>
  simp[peg_linfix_def, list_case_lemma, peg_eval_rpt] >> dsimp[] >>
  gen_tac >>
  completeInduct_on `LENGTH pfx` >> rpt strip_tac >>
  full_simp_tac (srw_ss() ++ DNF_ss) [] >> rveq >>
  `∃subs. pt = Nd (mkNT P) subs`
    by (Cases_on `pt` >> fs[MAP_EQ_CONS] >> rw[] >> fs[]) >> rw[] >> fs[] >>
  Q.UNDISCH_THEN `MAP ptree_head subs ∈ mmlG.rules ' (mkNT P)` mp_tac >>
  simp[MAP_EQ_CONS] >> reverse (rpt strip_tac) >> rveq >> fs[]
  >- (asm_match `ptree_fringe cpt = MAP TK pfx` >>
      map_every qexists_tac [`sfx`, `[cpt]`, `[]`] >>
      first_x_assum (kall_tac o has_length) >>
      conj_tac
      >- (fs[rich_listTheory.IS_SUFFIX_compute] >>
          IMP_RES_THEN (assume_tac o SIMP_RULE (srw_ss()) [])
            rich_listTheory.IS_PREFIX_LENGTH >>
          Cases_on `cpt`
          >- fs[MAP_EQ_SING, sym2peg_def] >>
          fs[] >> rveq >> fs[sym2peg_def] >>
          fs[DECIDE ``x:num ≤ y ⇔ x < y ∨ x = y``] >>
          `pfx = master` suffices_by rw[] >>
          metis_tac[rich_listTheory.IS_PREFIX_LENGTH_ANTI, REVERSE_11,
                    listTheory.LENGTH_REVERSE]) >>
      simp[Once pegTheory.peg_eval_cases, mk_linfix_def, peg_eval_seq_NONE] >>
      DISJ1_TAC >>
      Cases_on `SEP` >> fs[sym2peg_def, peg_eval_tok_NONE]
      >- (Cases_on `sfx` >> fs[] >> strip_tac >> fs[]) >> rveq >> fs[] >>
      Cases_on `sfx` >- simp[not_peg0_peg_eval_NIL_NONE, PEG_wellformed] >>
      fs[] >> metis_tac [peg_respects_firstSets]) >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  asm_match `
    mmlG.rules ' (mkNT P) = {[NN P; ptree_head spt; ptree_head cpt];
                             [ptree_head cpt]}
  ` >> asm_match `ptree_head ppt = NN P` >>
  fs[MAP_EQ_APPEND] >> rw[] >>
  asm_match `ptree_fringe ppt = MAP TK pf` >>
  asm_match `ptree_fringe spt = MAP TK sf` >>
  asm_match `ptree_fringe cpt = MAP TK cf` >>
  qispl_then [`mmlG`, `mkNT P`, `ptree_head spt`, `ptree_head cpt`,
              `ppt`, `spt`, `cpt`, `pf`, `sf`, `cf`] mp_tac
    lassoc_reassociated >> simp[MAP_EQ_APPEND] >>
  dsimp[] >>
  map_every qx_gen_tac [`cpt'`, `spt'`, `ppt'`]  >> rpt strip_tac >>
  asm_match `ptree_fringe cpt' = MAP TK cf'` >>
  asm_match `ptree_fringe spt' = MAP TK sf'` >>
  asm_match `ptree_fringe ppt' = MAP TK pf'` >>
  map_every qexists_tac [`sf' ++ pf' ++ sfx`, `[cpt']`] >>
  `0 < LENGTH (MAP TK sf') ∧ 0 < LENGTH (MAP TK cf')`
    by metis_tac [fringe_length_not_nullable] >>
  ntac 2 (pop_assum mp_tac) >> simp[] >> ntac 2 strip_tac >>
  CONV_TAC EXISTS_AND_CONV >> conj_tac
  >- (REWRITE_TAC [GSYM APPEND_ASSOC] >>
      first_x_assum match_mp_tac >> simp[] >>
      conj_tac
      >- (fs[rich_listTheory.IS_SUFFIX_compute] >>
          IMP_RES_THEN mp_tac rich_listTheory.IS_PREFIX_LENGTH >>
          asimp[]) >>
      Cases_on `sf'` >> fs[] >>
      rpt (first_x_assum (kall_tac o has_length)) >> rpt strip_tac >>
      fs[] >>
      asm_match `ptree_fringe spt' = TK s1::MAP TK ss` >>
      `s1 ∈ firstSet mmlG [ptree_head spt']`
        by metis_tac [firstSet_nonempty_fringe] >>
      metis_tac[]) >>
  first_x_assum (qspecl_then [`pf'`, `ppt'`, `sfx`] mp_tac) >>
  first_assum (SUBST1_TAC o assert (listSyntax.is_append o lhs o concl)) >>
  asimp[] >>
  `IS_SUFFIX master pf'`
    by (first_x_assum (SUBST_ALL_TAC o
                       assert (listSyntax.is_append o lhs o concl)) >>
        fs[rich_listTheory.IS_SUFFIX_compute,
           listTheory.REVERSE_APPEND] >>
        metis_tac[rich_listTheory.IS_PREFIX_APPEND1]) >>
  simp[] >>
  disch_then (qxchl [`pf1`, `cplist`, `sclist`] strip_assume_tac) >>
  first_x_assum (kall_tac o assert (is_forall o concl)) >>
  first_x_assum (qspecl_then [`spt'`, `sf'`, `pf' ++ sfx`] mp_tac o
                 assert (free_in ``spt:mlptree`` o concl)) >>
  simp[] >>
  Q.UNDISCH_THEN `IS_SUFFIX master (pf ++ sf ++ cf)` mp_tac >>
  simp[rich_listTheory.IS_SUFFIX_compute] >>
  disch_then (mp_tac o MATCH_MP rich_listTheory.IS_PREFIX_LENGTH) >>
  asimp[] >> strip_tac >> attack_asmguard
  >- (gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >> fs[]) >>
  strip_tac >>
  simp[Once pegTheory.peg_eval_cases] >> dsimp[] >> DISJ2_TAC >>
  map_every qexists_tac [`pf1`, `sclist`, `pf' ++ sfx`, `[spt']`,
                         `cplist`] >> simp[] >>
  Cases_on `ptree_head cpt`
  >- (fs[sym2peg_def] >>
      simp[mk_linfix_def, left_insert_mk_linfix, left_insert_def]) >>
  simp[left_insert_mk_linfix] >> fs[sym2peg_def] >>
  first_x_assum (mp_tac o MATCH_MP peg_sound) >> rw[] >>
  simp[mk_linfix_def, left_insert_def]);


val peg_eval_NT_NONE = save_thm(
  "peg_eval_NT_NONE",
  ``peg_eval mmlPEG (i0, nt (mkNT n) I) NONE``
     |> SIMP_CONV (srw_ss()) [Once pegTheory.peg_eval_cases])

fun PULLV v t = let
  val (bv,b) = dest_abs(rand t)
in
  if bv = v then ALL_CONV
  else BINDER_CONV (PULLV v) THENC SWAP_VARS_CONV
end t

fun unify_firstconj th (g as (asl,w)) = let
  val (exvs, body) = strip_exists w
  val c = hd (strip_conj body)
  val (favs, fabody) = strip_forall (concl th)
  val con = #2 (dest_imp fabody)
  val theta = Unify.simp_unify_terms (set_diff (free_vars c) exvs) c con
  fun inst_exvs theta =
      case theta of
          [] => ALL_TAC
        | {redex,residue} :: rest =>
          if mem redex exvs andalso
             null (intersect (free_vars residue) (union favs exvs))
          then
            CONV_TAC (PULLV redex) THEN EXISTS_TAC residue THEN
            inst_exvs rest
          else inst_exvs rest
  fun inst_favs theta th =
      case theta of
          [] => mp_tac th
        | {redex,residue} :: rest =>
          if mem redex favs then
            inst_favs rest (th |> CONV_RULE (PULLV redex) |> SPEC residue)
          else inst_favs rest th
in
  inst_exvs theta THEN inst_favs theta th
end g



val completeness = store_thm(
  "completeness",
  ``∀pt N pfx sfx.
      valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT N) ∧
      mkNT N ∈ FDOM mmlPEG.rules ∧
      (sfx ≠ [] ⇒ HD sfx ∈ stoppers N) ∧ ptree_fringe pt = MAP TOK pfx ⇒
      peg_eval mmlPEG (pfx ++ sfx, nt (mkNT N) I)
                      (SOME(sfx, [pt]))``,
  ho_match_mp_tac parsing_ind >> qx_gen_tac `pt` >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss() ++ CONJ_ss) [AND_IMP_INTRO]) >>
  map_every qx_gen_tac [`N`, `pfx`, `sfx`] >> strip_tac >> fs[] >>
  `∃subs. pt = Nd (mkNT N) subs`
  by (Cases_on `pt` >> simp[] >> fs[] >> rw[] >> fs[MAP_EQ_SING]) >>
  rveq >> fs[] >>
  rpt (first_x_assum (mp_tac o assert (free_in ``mmlG.rules`` o concl))) >>
  Cases_on `N` >> simp[cmlG_applied, cmlG_FDOM]
  >- (print_tac "nVlist1" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> rw[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >> rw[]
      >- ((* nV nVlist1 *)
          asm_match `ptree_head vpt = NN nV` >>
          asm_match `ptree_head vlist1pt = NN nVlist1` >>
          asm_match `ptree_fringe vpt = MAP TK vtks` >>
          asm_match `ptree_fringe vlist1pt = MAP TK vltks` >>
          map_every qexists_tac [`[vpt]`, `vltks ++ sfx`, `[vlist1pt]`] >>
          simp[] >>
          `0 < LENGTH (MAP TK vtks) ∧ 0 < LENGTH (MAP TK vltks)`
          by metis_tac[fringe_length_not_nullable, nullable_Vlist1,
                       nullable_V] >> fs[] >>
          REWRITE_TAC [GSYM APPEND_ASSOC] >> simp[]) >>
      (* nV *)
      asm_match `ptree_head vpt = NN nV` >>
      map_every qexists_tac [`[vpt]`, `sfx`, `[]`] >> simp[] >>
      simp[NT_rank_def] >> Cases_on `sfx` >>
      simp[not_peg0_peg_eval_NIL_NONE] >> fs[peg_respects_firstSets])
  >- (print_tac "nV" >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_V_def,
           peg_eval_choice, gramTheory.assert_def, peg_eval_tok_NONE] >>
      dsimp[MAP_EQ_SING] >> rpt strip_tac >> rveq >>
      fs[MAP_EQ_SING, sumID_def])
  >- (print_tac "nUQTyOp" >>
      simp[MAP_EQ_SING] >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG,
           peg_eval_choice, gramTheory.assert_def, peg_eval_tok_NONE] >>
      strip_tac >> rveq >> fs[MAP_EQ_SING])
  >- (print_tac "nUQConstructorName" >>
      simp[MAP_EQ_SING, peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_UQConstructorName_def,
           gramTheory.assert_def] >>
      strip_tac >> rveq >> fs[MAP_EQ_SING])
  >- (print_tac "nTyvarN" >> dsimp[MAP_EQ_SING] >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >> rpt strip_tac >>
      fs[MAP_EQ_SING])
  >- (print_tac "nTypeName" >>
      simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied, FDOM_cmlPEG] >>
      rpt strip_tac >> rveq >> fs[]
      >- (DISJ1_TAC >> fs[MAP_EQ_SING] >> rveq >>
          asm_match `NN nUQTyOp = ptree_head pt` >>
          first_x_assum (qspecl_then [`pt`, `nUQTyOp`, `pfx`, `sfx`] mp_tac)>>
          simp[NT_rank_def, FDOM_cmlPEG] >> fs[])
      >- (DISJ2_TAC >> fs[MAP_EQ_CONS] >> simp[peg_eval_seq_NONE] >> rveq >>
          fs[] >>
          asm_match `ptree_head tyvl_pt = NN nTyVarList` >>
          asm_match `ptree_head tyop_pt = NN nUQTyOp` >>
          fs [MAP_EQ_APPEND, MAP_EQ_SING, MAP_EQ_CONS] >> rveq >>
          asm_match `ptree_fringe tyop_pt = MAP TK opf` >> conj_tac
          >- simp[Once pegTheory.peg_eval_cases, FDOM_cmlPEG,
                  mmlpeg_rules_applied, peg_eval_tok_NONE] >>
          dsimp[] >>
          map_every qexists_tac [`[tyvl_pt]`, `opf ++ sfx`, `[tyop_pt]`] >>
          simp[] >>
          asm_match `ptree_fringe tyvl_pt = MAP TK vlf` >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
          asimp[FDOM_cmlPEG]) >>
      DISJ2_TAC >> fs[MAP_EQ_CONS] >> rveq >> fs[MAP_EQ_CONS] >> rveq >>
      simp[peg_eval_seq_NONE, peg_eval_tok_NONE] >>
      simp[Once pegTheory.peg_eval_cases, FDOM_cmlPEG, mmlpeg_rules_applied,
           peg_eval_tok_NONE])
  >- (print_tac "nTypeList2" >> dsimp[MAP_EQ_CONS] >>
      map_every qx_gen_tac [`typt`, `tylpt`] >> rw[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >>
      simp[peg_eval_NT_SOME] >> simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      dsimp[] >> asm_match `ptree_fringe typt = MAP TK tyf` >>
      asm_match `MAP TK lf = ptree_fringe tylpt` >>
      first_assum (qspecl_then [`typt`, `nType`, `tyf`, `CommaT::lf ++ sfx`]
                               mp_tac o has_length) >>
      simp_tac (srw_ss() ++ ARITH_ss) [FDOM_cmlPEG] >> simp[] >> strip_tac >>
      map_every qexists_tac [`[typt]`, `lf ++ sfx`, `[tylpt]`] >>
      simp[FDOM_cmlPEG])
  >- (print_tac "nTypeList1" >> dsimp[MAP_EQ_CONS] >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_tok_NONE] >>
      dsimp[] >> conj_tac
      >- (qx_gen_tac `typt` >> rw[] >> fs[] >> DISJ2_TAC >> DISJ1_TAC >>
                     first_x_assum (qspecl_then [`typt`, `nType`, `pfx`, `sfx`] mp_tac) >>
                     simp[NT_rank_def, FDOM_cmlPEG] >> Cases_on `sfx` >> fs[]) >>
      map_every qx_gen_tac [`typt`, `tylpt`] >> rw[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >> DISJ1_TAC >>
      asm_match `ptree_fringe typt = MAP TK tyf` >>
      asm_match `MAP TK tylf = ptree_fringe tylpt` >>
      map_every qexists_tac [`[typt]`, `tylf ++ sfx`, `[tylpt]`] >>
      simp[] >> REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      simp[FDOM_cmlPEG])
  >- (print_tac "nTypeDec" >> dsimp[MAP_EQ_CONS] >> qx_gen_tac `dtspt` >>
      rw[] >> fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS] >> rw[] >>
      simp[peg_eval_NT_SOME] >>
      simp[FDOM_cmlPEG, mmlpeg_rules_applied, peg_TypeDec_def] >>
      asm_match `MAP TK pfx = ptree_fringe dtspt` >>
      match_mp_tac
      (peg_linfix_complete
         |> Q.INST [`SEP` |-> `TK AndT`, `C` |-> `NN nDtypeDecl`,
                    `P` |-> `nDtypeDecls`, `master` |-> `pfx`]
         |> SIMP_RULE (srw_ss() ++ DNF_ss) [sym2peg_def, MAP_EQ_CONS,
                                            cmlG_applied, EXTENSION,
                                            DISJ_COMM, AND_IMP_INTRO]) >>
      simp[FDOM_cmlPEG])
  >- (print_tac "nType" >> dsimp[MAP_EQ_CONS] >> conj_tac
      >- (simp[peg_eval_NT_SOME] >>
              simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_Type_def,
                   peg_eval_choice, sumID_def, peg_eval_seq_NONE,
                   peg_eval_tok_NONE] >> dsimp[list_case_lemma] >>
              qx_gen_tac `dpt` >> strip_tac >> DISJ1_TAC >> rveq >> fs[] >>
              Cases_on `sfx` >> fs[]
              >- (first_x_assum (qspecl_then [`dpt`, `nDType`, `pfx`, `[]`]
                                             mp_tac) >>
                                simp[NT_rank_def, FDOM_cmlPEG]) >>
              first_x_assum match_mp_tac >> simp[NT_rank_def, FDOM_cmlPEG]) >>
      map_every qx_gen_tac [`dpt`, `typt`] >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_Type_def] >>
      asm_match `ptree_fringe dpt = MAP TK df` >>
      asm_match `MAP TK tf = ptree_fringe typt` >> loseC ``NT_rank`` >>
      map_every qexists_tac [`ArrowT::tf ++ sfx`, `[dpt]`,
                             `[Lf (TK ArrowT); typt]`] >>
      simp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[FDOM_cmlPEG] >>
      dsimp[peg_eval_choice, sumID_def] >> asimp[FDOM_cmlPEG])
  >- (print_tac "nTyVarList" >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      disch_then assume_tac >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`C` |-> `NN nTyvarN`, `SEP` |-> `TK CommaT`,
                                 `P` |-> `nTyVarList`,
                                 `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                      [sym2peg_def, cmlG_applied, cmlG_FDOM, EXTENSION,
                       DISJ_COMM, AND_IMP_INTRO]) >>
      simp[MAP_EQ_SING] >> simp[cmlG_FDOM, cmlG_applied] >>
      `NT_rank (mkNT nTyvarN) < NT_rank (mkNT nTyVarList)`
      by simp[NT_rank_def]>> simp[FDOM_cmlPEG] >> fs[])
  >- (print_tac "nTyOp" >>
      simp[peg_eval_NT_SOME, mmlpeg_rules_applied, FDOM_cmlPEG, MAP_EQ_CONS] >>
      rw[] >> fs[MAP_EQ_CONS]
      >- (asm_match `ptree_head pt = NN nUQTyOp` >>
                    first_x_assum (qspecl_then [`pt`, `nUQTyOp`, `pfx`, `sfx`] mp_tac) >>
                    simp[NT_rank_def, peg_eval_NT_SOME, mmlpeg_rules_applied,
                         FDOM_cmlPEG]) >>
      match_mp_tac peg_respects_firstSets >> simp[firstSet_nUQTyOp, PEG_exprs])
  >- (print_tac "nTopLevelDecs" >> fs[FDOM_cmlPEG])
  (* (dsimp[MAP_EQ_CONS] >> conj_tac
      >- (simp[peg_eval_NT_SOME] >>
          simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_rpt] >>
          map_every qx_gen_tac [`tldpt`, `tldspt`] >> rw[] >>
          fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
          asm_match `ptree_fringe tldpt = MAP TK df` >>
          asm_match `ptree_fringe tldspt = MAP TK sf` >>
          Cases_on `sf = []`
          >- (first_x_assum (qspecl_then [`tldpt`, `nTopLevelDec`, `df`, `sfx`]
                                         mp_tac) >>
              simp[NT_rank_def, FDOM_cmlPEG] >> strip_tac >>
              qexists_tac `[[tldpt]]` >>
              simp[] >> reverse conj_tac
              >- (Cases_on `tldspt` >> fs[cmlG_applied, cmlG_FDOM, MAP_EQ_CONS] >>
                  rw[] >> fs[] >>
                  Q.UNDISCH_THEN `ptree_head tldpt = NN nTopLevelDec` kall_tac >>
                  asm_match `ptree_head tldpt' = NN nTopLevelDec` >>
                  `0 < LENGTH (ptree_fringe tldpt')` suffices_by simp[] >>
                  match_mp_tac (SIMP_RULE (srw_ss() ++ DNF_ss) [AND_IMP_INTRO]
                                          fringe_length_not_nullable) >>
                  qexists_tac `mmlG` >> simp[]) >>
              simp[Once pegTheory.peg_eval_cases] >> qexists_tac `sfx` >> simp[] >>
              simp[Once pegTheory.peg_eval_cases] >>
              reverse (Cases_on `sfx`)
              >- (match_mp_tac peg_respects_firstSets >> fs[PEG_exprs]) >>
              simp[not_peg0_peg_eval_NIL_NONE, PEG_exprs, PEG_wellformed]) >>
          loseC ``NT_rank`` >>
          `¬nullable mmlG [NN nTopLevelDec]` by simp[] >>
          `0 < LENGTH (MAP TK df)`
            by metis_tac [fringe_length_not_nullable] >> fs[] >>
          `0 < LENGTH sf` by (Cases_on `sf` >> fs[]) >>
          `peg_eval mmlPEG (df ++ (sf ++ sfx), nt (mkNT nTopLevelDec) I)
                           (SOME (sf ++ sfx, [tldpt]))` by simp[FDOM_cmlPEG] >>
          `peg_eval mmlPEG (sf ++ sfx, nt (mkNT nTopLevelDecs) I)
                           (SOME (sfx, [tldspt]))` by asimp[FDOM_cmlPEG] >>
          pop_assum (qxchl [`tds`] strip_assume_tac o
                     SIMP_RULE (srw_ss()) [mmlpeg_rules_applied, FDOM_cmlPEG,
                                           peg_eval_rpt] o
                     SIMP_RULE (srw_ss()) [peg_eval_NT_SOME]) >>
          simp[Once pegTheory.peg_eval_cases] >> dsimp[] >>
          map_every qexists_tac [`sf ++ sfx`, `[tldpt]`] >> simp[] >>
          fs[] >> qexists_tac `tds` >> simp[]) >>
      rw[] >> fs[] >> rw[] >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_rpt] >>
      qexists_tac `[]` >> simp[] >> simp[Once pegTheory.peg_eval_cases] >>
      Cases_on `sfx` >>
      fs[peg_respects_firstSets, not_peg0_peg_eval_NIL_NONE, PEG_exprs,
         PEG_wellformed]) *)
  >- (print_tac "nTopLevelDec" >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >> strip_tac >>
      fs[MAP_EQ_SING] >> rw[] >> fs[]
      >- (DISJ1_TAC >> first_x_assum match_mp_tac >>
                    simp[NT_rank_def, FDOM_cmlPEG]) >>
      DISJ2_TAC >> reverse conj_tac
      >- (first_x_assum match_mp_tac >> simp[NT_rank_def, FDOM_cmlPEG]) >>
      `0 < LENGTH (MAP TK pfx)`
      by metis_tac [fringe_length_not_nullable, nullable_Decl] >> fs[] >>
      Cases_on `pfx` >> fs[] >>
      match_mp_tac peg_respects_firstSets >>
      simp[PEG_exprs] >> strip_tac >> rw[] >>
      `StructureT ∈ firstSet mmlG [NN nDecl]`
        by metis_tac [firstSet_nonempty_fringe] >> fs[])
  >- (print_tac "nStructure" >> dsimp[MAP_EQ_CONS] >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS, MAP_EQ_APPEND] >>
      rw[] >> fs[] >>
      simp[peg_eval_NT_SOME] >> simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      dsimp[] >> loseC ``NT_rank`` >>
      asm_match `ptree_head vpt = NN nV` >>
      asm_match `ptree_fringe vpt = MAP TK vf` >>
      asm_match `ptree_head sigpt = NN nOptionalSignatureAscription` >>
      asm_match `ptree_fringe sigpt = MAP TK sf` >>
      asm_match `ptree_head dpt = NN nDecls` >>
      asm_match `ptree_fringe dpt = MAP TK df` >>
      map_every qexists_tac
        [`[vpt]`, `sf ++ [EqualsT; StructT] ++ df ++ [EndT] ++ sfx`,
         `[sigpt]`, `df ++ [EndT] ++ sfx`, `[dpt]`] >>
      simp[] >> REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[])
  >- (print_tac "nStarTypes" >> disch_then assume_tac >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      match_mp_tac
        (peg_linfix_complete
           |> Q.INST [`SEP` |-> `TK StarT`, `C` |-> `NT (mkNT nDType)`,
                      `P` |-> `nStarTypes`, `master` |-> `pfx`]
           |> SIMP_RULE (srw_ss() ++ DNF_ss)
               [cmlG_FDOM, cmlG_applied, sym2peg_def, MAP_EQ_SING,
                AND_IMP_INTRO]
           |> Q.SPEC `pfx` |> SIMP_RULE (srw_ss()) [] |> Q.GEN `pfx`) >>
      simp[] >> simp[NT_rank_def, cmlG_applied, cmlG_FDOM] >> fs[])
  >- (print_tac "nSpecLineList" >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >> simp[MAP_EQ_CONS] >>
      strip_tac >> rveq >> fs[MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
      rw[]
      >- (asm_match `ptree_head slpt = NN nSpecLine` >>
          asm_match `ptree_fringe slpt = MAP TK sf` >>
          asm_match `ptree_head sllpt = NN nSpecLineList` >>
          asm_match `ptree_fringe sllpt = MAP TK lf` >>
          DISJ1_TAC >>
          map_every qexists_tac [`[slpt]`, `lf ++ sfx`, `[sllpt]`] >>
          simp[] >>
          `0 < LENGTH (MAP TK sf)`
            by metis_tac [nullable_SpecLine, fringe_length_not_nullable] >>
          fs[] >>
          Cases_on `lf = []` >> fs[] >- simp[NT_rank_def] >>
          `0 < LENGTH lf` by (Cases_on `lf` >> fs[]) >>
          REWRITE_TAC [GSYM APPEND_ASSOC] >>
          first_x_assum (match_mp_tac o has_length) >> asimp[] >>
          Cases_on `lf` >> fs[] >> rpt strip_tac >> rw[] >>
          IMP_RES_THEN mp_tac firstSet_nonempty_fringe >> simp[])
      >- (DISJ2_TAC >> fs[MAP_EQ_CONS] >> rw[] >>
          simp[peg_respects_firstSets, PEG_exprs]) >>
      DISJ2_TAC >> Cases_on `sfx` >> fs[peg_eval_tok_NONE]
      >- simp[not_peg0_peg_eval_NIL_NONE, PEG_exprs, PEG_wellformed] >>
      simp[peg_respects_firstSets, PEG_exprs])
  >- (print_tac "nSpecLine" >> simp[peg_eval_NT_SOME] >>
      simp[MAP_EQ_CONS] >> strip_tac >> rveq >>
      fs[MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS] >>
      rveq >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_tok_NONE]
      >- (DISJ1_TAC >> dsimp[] >>
          asm_match `ptree_head vpt = NN nV` >>
          asm_match `ptree_fringe vpt = MAP TK vf` >>
          asm_match `ptree_head typt = NN nType` >>
          asm_match `MAP TK tyf = ptree_fringe typt` >> rw[] >>
          map_every qexists_tac [`[vpt]`, `tyf ++ sfx`, `[typt]`] >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[]) >>
      Cases_on `pfx` >> fs[]
      >- (asm_match `ptree_fringe pt = []` >>
          `0 < LENGTH (ptree_fringe pt)`
            by metis_tac [fringe_length_not_nullable, nullable_TypeDec] >>
          pop_assum mp_tac >> simp[]) >>
      IMP_RES_THEN mp_tac firstSet_nonempty_fringe >> simp[] >> rw[] >>
      REWRITE_TAC [Once (GSYM listTheory.APPEND)] >>
      first_x_assum match_mp_tac >> simp[NT_rank_def])
  >- (print_tac "nSignatureValue" >> dsimp[MAP_EQ_CONS] >>
      simp[peg_eval_NT_SOME] >> simp[FDOM_cmlPEG, mmlpeg_rules_applied] >>
      rw[] >> fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
      rw[] >> REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[])
  >- (print_tac "nRelOps" >> simp[peg_eval_NT_SOME] >>
      simp[FDOM_cmlPEG, mmlpeg_rules_applied, MAP_EQ_SING] >>
      strip_tac >> fs[MAP_EQ_SING,peg_eval_tok_NONE])
  >- (print_tac "nREPLTop" >> simp[MAP_EQ_CONS] >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[]
      >- (simp[peg_eval_NT_SOME] >> simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
          DISJ2_TAC >> asm_match `ptree_head tdpt = NN nTopLevelDec` >>
          asm_match `ptree_fringe tdpt = MAP TK tf` >>
          conj_tac
          >- (DISJ1_TAC >>
              `0 < LENGTH (MAP TK tf)`
                by metis_tac[fringe_length_not_nullable,nullable_TopLevelDec] >>
              fs[] >>
              `∃tf0 tft. tf = tf0 :: tft` by (Cases_on `tf` >> fs[]) >> rveq >>
              fs[] >>
              `tf0 ∈ firstSet mmlG [NN nTopLevelDec]`
                by metis_tac [firstSet_nonempty_fringe] >>
              match_mp_tac peg_respects_firstSets >>
              simp[PEG_exprs] >> fs[]) >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
          asimp[]) >>
      simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied, FDOM_cmlPEG] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[])
  >- (print_tac "nREPLPhrase" >> fs[FDOM_cmlPEG])
      (*
      (simp[MAP_EQ_CONS] >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[]
      >- (simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied, FDOM_cmlPEG] >>
          DISJ2_TAC >> asm_match `ptree_head tdspt = NN nTopLevelDecs` >>
          asm_match `ptree_fringe tdspt = MAP TK tf` >> conj_tac
          >- (DISJ1_TAC >>
              `tf = [] ∨ ∃tf0 tft. tf = tf0 :: tft`
                by (Cases_on `tf` >> fs[]) >> rveq >> fs[] >|
              [
                ALL_TAC,
                `tf0 ∈ firstSet mmlG [NN nTopLevelDecs]`
                  by metis_tac [firstSet_nonempty_fringe]
              ] >>
              match_mp_tac peg_respects_firstSets >>
              simp[PEG_exprs] >> fs[]) >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
          asimp[]) >>
      simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied, FDOM_cmlPEG] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[]) *)
  >- (print_tac "nPtuple" >> fs[FDOM_cmlPEG])
  >- (print_tac "nPbase" >> fs[FDOM_cmlPEG])
  >- (print_tac "nPatternList2" >> fs[FDOM_cmlPEG])
  >- (print_tac "nPatternList1" >>
      simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied, FDOM_cmlPEG] >>
      disch_then assume_tac >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`SEP` |-> `TK CommaT`, `C` |-> `NN nPattern`,
                                 `P` |-> `nPatternList1`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_FDOM, cmlG_applied, INSERT_COMM,
                            MAP_EQ_SING, AND_IMP_INTRO]
                      |> Q.SPEC `pfx` |> SIMP_RULE (srw_ss()) []
                      |> Q.GEN `pfx`) >>
      simp[cmlG_applied, cmlG_FDOM] >> rpt strip_tac
      >- simp[NT_rank_def] >> fs[])
  >- (print_tac "nPattern" >> dsimp[MAP_EQ_CONS] >> rpt strip_tac
      >- ((* constructorName Tuple *) rveq >> fs[DISJ_IMP_THM, FORALL_AND_THM]>>
          simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
          simp_tac std_ss [peg_Pattern_def, Once peg_eval_choicel_CONS] >>
          DISJ1_TAC >> simp_tac std_ss [peg_eval_seql_CONS] >>
          simp_tac std_ss [peg_eval_seql_NIL] >>
          asm_match `ptree_head cnpt = NN nConstructorName` >>
          full_simp_tac list_ss [MAP_EQ_APPEND] >>
          asm_match `ptree_fringe cnpt = MAP TK cnf` >> rveq >>
          asm_match `ptree_head ptpt = NN nPtuple` >>
          asm_match `ptree_fringe ptpt = MAP TK ptf` >>
          map_every qexists_tac [`[cnpt]`, `ptf ++ sfx`] >>
          CONV_TAC EXISTS_AND_CONV >>
          `0 < LENGTH (MAP TK ptf)`
             by metis_tac [fringe_length_not_nullable,
                            nullable_Ptuple] >> full_simp_tac list_ss[] >>
          conj_tac
          >- (REWRITE_TAC [GSYM APPEND_ASSOC, pnt_def] >> asimp[]) >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
          DISJ1_TAC >>
          simp_tac std_ss [Once peg_eval_choicel_CONS, peg_eval_seql_CONS,
                           tokeq_def, peg_eval_tok_SOME] >>
          simp_tac (std_ss ++ DNF_ss)
            [Once peg_eval_choicel_CONS, peg_eval_choicel_SING,
             peg_eval_seql_CONS, peg_eval_seql_NIL] >>
          DISJ2_TAC>> dsimp[] >> DISJ1_TAC >>
          Cases_on `ptpt` >> fs[MAP_EQ_SING, cmlG_FDOM, cmlG_applied] >> rw[]>>
          fs[MAP_EQ_CONS] >> rw[] >>
          fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_CONS, MAP_EQ_APPEND] >> rw[]>>
          asm_match `ptree_head p2pt = NN nPatternList2` >>
          Cases_on `p2pt` >> fs[MAP_EQ_SING] >> rw[] >> fs[] >>
          fs[cmlG_applied, cmlG_FDOM, MAP_EQ_CONS] >> rw[] >>
          fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND, MAP_EQ_CONS] >>
          rw[] >> asm_match `ptree_head ppt = NN nPattern` >>
          asm_match `ptree_fringe ppt = MAP TK pf` >>
          asm_match `ptree_head p1pt = NN nPatternList1` >>
          asm_match `MAP TK p1f = ptree_fringe p1pt` >>
          map_every qexists_tac [`[ppt]`, `p1f ++ [RparT] ++ sfx`, `[p1pt]`] >>
          `0 < LENGTH (MAP TK pf)`
            by metis_tac[fringe_length_not_nullable, nullable_Pattern] >> fs[]>>
          loseC ``NT_rank`` >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[] >>
          simp[patConsApplied_def] >>
          Cases_on `pf` >> fs[] >>
          simp[peg_eval_tok_NONE] >> strip_tac >> rw[] >>
          IMP_RES_THEN mp_tac firstSet_nonempty_fringe >> simp[])
      >- ((* constructorname pbase *)
          simp_tac std_ss [Once peg_eval_NT_SOME, peg_Pattern_def,
                           FDOM_cmlPEG, mmlpeg_rules_applied] >>
          conj_tac >- rw[] >>
          simp_tac std_ss [Once peg_eval_choicel_CONS, pnt_def] >> DISJ1_TAC>>
          simp_tac (std_ss ++ DNF_ss) [peg_eval_seql_CONS] >>
          full_simp_tac std_ss [] >>
          RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [MAP_EQ_APPEND]) >>
          full_simp_tac std_ss [] >> rveq >>
          asm_match `ptree_head cnpt = NN nConstructorName` >>
          asm_match `ptree_fringe cnpt = MAP TK cf` >>
          asm_match `ptree_head pbpt = NN nPbase` >>
          asm_match `ptree_fringe pbpt = MAP TK pf` >>
          map_every qexists_tac [`[cnpt]`, `pf ++ sfx`] >>
          `0 < LENGTH (MAP TK pf) ∧ 0 < LENGTH (MAP TK cf)`
            by metis_tac [fringe_length_not_nullable, nullable_Pbase,
                          nullable_ConstructorName] >>
          full_simp_tac list_ss [FORALL_AND_THM, DISJ_IMP_THM] >>
          CONV_TAC (REDEPTH_CONV EXISTS_AND_CONV) >>
          conj_tac
          >- (REWRITE_TAC [GSYM APPEND_ASSOC] >> asimp[]) >>
          simp_tac list_ss [peg_eval_seql_NIL] >>
          (* must split on form of pbase *)
          Cases_on `pbpt`
          >- (RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >> rveq >>
              RULE_ASSUM_TAC
                (SIMP_RULE (srw_ss()) [MAP_EQ_CONS, MAP_EQ_APPEND]) >> rveq >>
              fs[]) >>
          RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [MAP_EQ_CONS, MAP_EQ_APPEND]) >>
          full_simp_tac std_ss [DISJ_IMP_THM, FORALL_AND_THM] >> rveq >>
          RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [cmlG_FDOM, cmlG_applied]) >>
          asm_match `FLAT (MAP ptree_fringe subs) = MAP TK pf` >>
          Cases_on `MAP ptree_head subs = [NN nV]`
          >- (full_simp_tac std_ss [] >>
              simp_tac (std_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
              DISJ2_TAC >> full_simp_tac list_ss [MAP_EQ_SING] >> rveq >>
              full_simp_tac list_ss [] >>
              `∃pf0 pft. pf = pf0 :: pft` by (Cases_on `pf` >> fs[]) >> rveq>>
              full_simp_tac list_ss [] >>
              `pf0 ∈ firstSet mmlG [NN nV]`
                 by metis_tac [firstSet_nonempty_fringe] >>
              `pf0 ≠ LparT`
                by (strip_tac >> fs[firstSet_nV]) >>
              asm_simp_tac list_ss [Once peg_eval_seql_CONS, tokeq_def,
                                    peg_eval_tok_NONE] >>
              dsimp[peg_eval_choice] >> DISJ2_TAC >>
              simp[peg_eval_seq_NONE, GSYM CONJ_ASSOC] >>
              CONV_TAC EXISTS_AND_CONV >> conj_tac
              >- (match_mp_tac peg_respects_firstSets >> simp[] >>
                  metis_tac [firstSets_nV_nConstructorName]) >>
              dsimp[peg_pbasewocp_def] >> DISJ2_TAC >> DISJ1_TAC >>
              CONV_TAC EXISTS_AND_CONV >> conj_tac
              >- (simp[peg_eval_tok_NONE] >> Cases_on `pf0` >>
                  fs[firstSet_nV]) >>
              asm_match `NN nV = ptree_head vpt` >> qexists_tac `[vpt]` >>
              simp[patConsApplied_def] >>
              REWRITE_TAC [Once (GSYM listTheory.APPEND)] >> asimp[]) >>
          Cases_on `MAP ptree_head subs = [NN nConstructorName]`
          >- (full_simp_tac std_ss [] >>
              simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
              DISJ2_TAC >> REWRITE_TAC [GSYM CONJ_ASSOC] >>
              full_simp_tac list_ss [MAP_EQ_SING] >> rveq >>
              full_simp_tac list_ss [] >> rveq >>
              CONV_TAC EXISTS_AND_CONV >> conj_tac
              >- (simp_tac std_ss [Once peg_eval_seql_CONS] >> DISJ1_TAC >>
                  Cases_on `pf` >> fs[] >> simp[peg_eval_tok_NONE] >>
                  strip_tac >> rw[] >>
                  `LparT ∈ firstSet mmlG [NN nConstructorName]`
                    by metis_tac [firstSet_nonempty_fringe] >>
                  fs[firstSet_nConstructorName]) >>
              dsimp[peg_eval_choice] >> DISJ1_TAC >> simp[patConsApplied_def])>>
          Cases_on `∃i. MAP ptree_head subs = [TK (IntT i)]`
          >- (full_simp_tac std_ss [] >>
              simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
              DISJ2_TAC >> REWRITE_TAC [GSYM CONJ_ASSOC] >>
              full_simp_tac list_ss [MAP_EQ_SING] >> rveq >>
              full_simp_tac list_ss [] >> rveq >>
              CONV_TAC EXISTS_AND_CONV >> conj_tac
              >- (simp_tac std_ss [Once peg_eval_seql_CONS] >> DISJ1_TAC >>
                  Cases_on `pf` >> fs[] >> simp[peg_eval_tok_NONE] >> rw[]) >>
              dsimp[peg_eval_choice] >> DISJ2_TAC >> DISJ1_TAC >>
              REWRITE_TAC [GSYM CONJ_ASSOC] >> CONV_TAC EXISTS_AND_CONV >>
              conj_tac
              >- (simp[peg_eval_seq_NONE] >> Cases_on `pf` >> fs[] >> rw[] >>
                  simp[peg_respects_firstSets, firstSet_nConstructorName]) >>
              dsimp[peg_pbasewocp_def] >>
              asm_match `TK (IntT i) = ptree_head ipt` >> Cases_on `ipt` >>
              fs[MAP_EQ_SING, patConsApplied_def]) >>
          Cases_on `MAP ptree_head subs = [TK UnderbarT]`
          >- (full_simp_tac list_ss [] >>
              full_simp_tac list_ss [MAP_EQ_SING] >>
              asm_match `TK UnderbarT = ptree_head upt` >>
              reverse (Cases_on `upt`) >>
              RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >- fs[] >>
              rveq >>
              RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [MAP_EQ_SING]) >> rveq >>
              simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
              DISJ2_TAC >>
              simp_tac list_ss [Once peg_eval_seql_CONS, tokeq_def,
                                peg_eval_tok_NONE, peg_eval_tok_SOME] >>
              simp_tac (list_ss ++ DNF_ss) [] >> DISJ1_TAC >> dsimp[] >>
              DISJ2_TAC >> REWRITE_TAC [GSYM CONJ_ASSOC] >>
              CONV_TAC EXISTS_AND_CONV >> conj_tac
              >- simp[peg_eval_seq_NONE, peg_respects_firstSets,
                      firstSet_nConstructorName] >>
              simp[peg_pbasewocp_def, peg_eval_tok_NONE, peg_eval_seq_NONE] >>
              dsimp[] >> DISJ2_TAC >>
              simp[peg_respects_firstSets, firstSet_nV, patConsApplied_def]) >>
          simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
          DISJ1_TAC >> simp_tac (list_ss ++ DNF_ss) [Once peg_eval_seql_CONS]>>
          simp_tac (list_ss ++ DNF_ss) [Once peg_eval_seql_CONS,
                                        peg_eval_seql_NIL] >>
          full_simp_tac list_ss []
          >- (RW_TAC list_ss [] >>
              full_simp_tac list_ss [MAP_EQ_CONS] >> rveq >>
              full_simp_tac list_ss [MAP_EQ_CONS, DISJ_IMP_THM, MAP_EQ_APPEND,
                                     FORALL_AND_THM] >> rveq >>
              asm_match `ptree_head lpt = TK LparT` >>
              reverse (Cases_on `lpt`) >- fs[] >>
              full_simp_tac list_ss [grammarTheory.ptree_fringe_def,
                                     grammarTheory.ptree_head_def,
                                     MAP_EQ_CONS] >> rveq >>
              full_simp_tac list_ss [TypeBase.one_one_of ``:(α,β)symbol``] >>
              rveq >> simp_tac list_ss [peg_eval_tok_SOME, tokeq_def] >>
              simp_tac (std_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
              DISJ2_TAC >> REWRITE_TAC [GSYM CONJ_ASSOC] >>
              CONV_TAC EXISTS_AND_CONV >> conj_tac
              >- (simp[peg_eval_tok_NONE] >>
                  asm_match `ptree_head ppt = NN nPattern` >>
                  asm_match `ptree_fringe ppt = MAP TK pf` >>
                  `0 < LENGTH (MAP TK pf)`
                    by metis_tac [fringe_length_not_nullable,
                                  nullable_Pattern] >> fs[] >>
                  Cases_on `pf` >> fs[] >> strip_tac >> rw[] >>
                  `RparT ∈ firstSet mmlG [NN nPattern]`
                    by metis_tac[firstSet_nonempty_fringe] >>
                  fs[firstSet_nConstructorName, firstSet_nV]) >>
              simp_tac (std_ss ++ DNF_ss)
                [peg_eval_choicel_SING, peg_eval_seql_CONS,
                 peg_eval_seql_NIL] >>
              simp_tac (list_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
              DISJ2_TAC >> simp[peg_eval_tok_NONE] >>
              asm_match `ptree_head ppt = NN nPattern` >> qexists_tac `[ppt]`>>
              simp[patConsApplied_def] >>
              asm_match `ptree_head rppt = TK RparT` >>
              Cases_on `rppt` >> fs[] >> rw[] >> fs[MAP_EQ_CONS] >>
              REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[]) >>
          full_simp_tac list_ss [MAP_EQ_CONS] >> rveq >>
          full_simp_tac list_ss [MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >>
          rveq >>
          full_simp_tac list_ss [MAP_EQ_APPEND] >>
          asm_match `ptree_head lppt = TK LparT` >>
          Cases_on `lppt` >> fs[] >> rveq >> rw[] >> fs[MAP_EQ_CONS] >> rveq>>
          dsimp[] >> simp[patConsApplied_def]) >>
      (* pbase *)
      fs[] >> rw[] >>
      simp_tac std_ss [peg_eval_NT_SOME] >> conj_tac
      >- simp[] >>
      asm_match `ptree_head pbpt = NN nPbase` >>
      Cases_on `pbpt` >> fs[MAP_EQ_CONS, cmlG_applied, cmlG_FDOM] >> rveq >>
      fs[DISJ_IMP_THM, FORALL_AND_THM]
      >- (simp_tac (std_ss ++ DNF_ss)
                   [mmlpeg_rules_applied, peg_Pattern_def,
                    Once peg_eval_choicel_CONS, pnt_def,
                    tokeq_def, peg_eval_choicel_SING] >>
          DISJ2_TAC >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_seql_CONS] >> DISJ1_TAC >>
          asm_match `ptree_head vpt = NN nV` >>
          asm_match `ptree_fringe vpt = MAP TK vf` >>
          `0 < LENGTH (MAP TK vf)`
            by metis_tac [fringe_length_not_nullable, nullable_V] >> fs[] >>
          `∃vh vt. vf = vh :: vt` by (Cases_on `vf` >> fs[]) >> rveq >> fs[] >>
          `vh ∈ firstSet mmlG [NN nV]` by metis_tac [firstSet_nonempty_fringe]>>
          conj_tac
          >- (match_mp_tac peg_respects_firstSets >> simp[] >>
              metis_tac [firstSets_nV_nConstructorName]) >>
          simp[peg_pbasewoc_def, peg_pbasewocp_def] >> DISJ1_TAC >> DISJ2_TAC>>
          simp[peg_eval_tok_NONE] >> rpt strip_tac
          >- (Cases_on `vh` >> fs[firstSet_nV]) >>
          REWRITE_TAC [Once (GSYM listTheory.APPEND)] >> simp[NT_rank_def])
      >- ((* bare constructor *)
          simp_tac (std_ss ++ DNF_ss)
                   [peg_Pattern_def, Once peg_eval_choicel_CONS, pnt_def,
                    tokeq_def, peg_eval_choicel_SING, mmlpeg_rules_applied] >>
          DISJ1_TAC >>
          simp_tac (std_ss ++ DNF_ss)
                   [peg_eval_seql_CONS, Once peg_eval_choicel_CONS] >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
          DISJ2_TAC >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_seql_CONS] >>
          DISJ1_TAC >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
          DISJ2_TAC >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_choicel_CONS] >>
          DISJ2_TAC >> simp[] >> simp[peg_eval_seq_NONE] >>
          simp[peg_pbasewocp_def, peg_eval_seq_NONE] >>
          asm_match `ptree_head cnpt = NN nConstructorName` >>
          qexists_tac `[cnpt]` >> simp[patConsApplied_def] >>
          simp[NT_rank_def] >>
          simp[peg_eval_tok_NONE] >>
          Cases_on `sfx` >> fs[]
          >- simp[not_peg0_peg_eval_NIL_NONE, PEG_wellformed] >>
          simp[peg_respects_firstSets] >> strip_tac >>
          asm_match `isInt h` >> Cases_on`h` >> fs[])
      >- ((* integer *)
          fs[MAP_EQ_SING] >> rveq >>
          simp_tac (std_ss ++ DNF_ss) [mmlpeg_rules_applied, peg_Pattern_def,
                                       Once peg_eval_choicel_CONS] >>
          DISJ2_TAC >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_seql_CONS] >> DISJ1_TAC >>
          conj_tac
          >- simp[peg_respects_firstSets, firstSet_nConstructorName] >>
          simp[peg_pbasewoc_def, peg_pbasewocp_def])
      >- ((* (Pattern) *)
          fs[MAP_EQ_CONS, MAP_EQ_APPEND] >> rveq >>
          simp_tac (std_ss ++ DNF_ss) [mmlpeg_rules_applied, peg_Pattern_def,
                                       Once peg_eval_choicel_CONS] >>
          DISJ2_TAC >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_seql_CONS] >> DISJ1_TAC >>
          conj_tac >- simp[peg_respects_firstSets] >>
          simp[peg_pbasewocp_def, peg_pbasewoc_def,
               peg_eval_tok_NONE, peg_eval_seq_NONE] >> DISJ2_TAC >>
          simp[peg_respects_firstSets, peg_pbaseP_def, peg_eval_tok_NONE] >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[] >>
          asm_match `ptree_head ppt = NN nPattern` >>
          asm_match `ptree_fringe ppt = MAP TK pf` >>
          `0 < LENGTH(MAP TK pf)`
            by metis_tac [fringe_length_not_nullable, nullable_Pattern] >>
          fs[] >> Cases_on `pf` >> fs[] >> strip_tac >> rw[] >>
          IMP_RES_THEN mp_tac firstSet_nonempty_fringe >> simp[])
      >- ((* () *)
          fs[MAP_EQ_CONS] >> rveq >>
          simp_tac (std_ss ++ DNF_ss) [mmlpeg_rules_applied, peg_Pattern_def,
                                       Once peg_eval_choicel_CONS] >>
          DISJ2_TAC >>
          simp_tac (std_ss ++ DNF_ss) [Once peg_eval_seql_CONS] >>
          DISJ1_TAC >>
          simp[peg_pbasewoc_def, peg_pbasewocp_def, peg_eval_tok_NONE,
              peg_eval_seq_NONE, peg_respects_firstSets, peg_pbaseP_def]) >>
      (* _ *) fs[MAP_EQ_CONS] >> rveq >>
      simp_tac (std_ss ++ DNF_ss)  [mmlpeg_rules_applied, peg_Pattern_def,
                                    Once peg_eval_choicel_CONS] >>
      DISJ2_TAC >>
      simp_tac (std_ss ++ DNF_ss) [Once peg_eval_seql_CONS] >>
      DISJ1_TAC >>
      simp[peg_respects_firstSets, peg_pbasewocp_def, peg_pbasewoc_def,
           peg_eval_seq_NONE, peg_eval_tok_NONE] >>
      simp[peg_respects_firstSets, firstSet_nV, firstSet_nConstructorName])
  >- (print_tac "nPEs" >>
      simp[MAP_EQ_CONS] >> strip_tac >> rw[] >> fs[] >> rw[]
      >- ((* single nPE *)
         simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> DISJ2_TAC >>
         reverse CONJ_ASM2_TAC >- simp[NT_rank_def] >>
         pop_assum mp_tac >>
         simp[peg_eval_tok_NONE] >>
         ONCE_REWRITE_TAC [peg_eval_NT_SOME] >> simp[mmlpeg_rules_applied] >>
         strip_tac >> rveq >> fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rveq >> dsimp[] >>
         first_assum
           (assume_tac o MATCH_MP (CONJUNCT1 pegTheory.peg_deterministic) o
            assert (free_in ``DarrowT`` o concl)) >>
         simp[] >>
         simp[Once peg_eval_NT_NONE, mmlpeg_rules_applied, peg_eval_tok_NONE] >>
         asm_match `peg_eval mmlPEG (i2, nt (mkNT nE) I) (SOME(sfx,r2))` >>
         Cases_on `peg_eval mmlPEG (i2, nt (mkNT nE') I) NONE` >> simp[] >>
         DISJ1_TAC >>
         `∃rr. peg_eval mmlPEG (i2, nt (mkNT nE') I) rr`
           by simp[MATCH_MP pegTheory.peg_eval_total PEG_wellformed] >>
         `∃i3 r3. rr = SOME(i3,r3)`
           by metis_tac[optionTheory.option_CASES, pairTheory.pair_CASES] >>
         rveq >> pop_assum (assume_tac o MATCH_MP peg_det) >>
         simp[] >> Cases_on `i3` >> simp[] >>
         metis_tac[nE'_bar_nE, listTheory.HD, listTheory.NOT_CONS_NIL]) >>
      simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> dsimp[] >>
      DISJ1_TAC >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >> rveq >>
      asm_match `ptree_head pept = NN nPE'` >>
      asm_match `ptree_fringe pept = MAP TK pef` >>
      asm_match `ptree_head pspt = NN nPEs` >>
      asm_match `ptree_fringe pspt = MAP TK psf` >>
      map_every qexists_tac [`[pept]`, `psf ++ sfx`, `[pspt]`] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      conj_tac
      >- asimp[firstSet_nConstructorName, firstSet_nV, firstSet_nFQV] >>
      asimp[])
  >- (print_tac "nPE'" >> simp[MAP_EQ_CONS] >> strip_tac >>
      simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> dsimp[] >>
      rveq >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >>
      rveq >>
      asm_match `ptree_head ppt = NN nPattern` >>
      asm_match `ptree_fringe ppt = MAP TK pf` >>
      asm_match `ptree_head e'pt = NN nE'` >>
      asm_match `MAP TK ef = ptree_fringe e'pt` >>
      map_every qexists_tac [`[ppt]`, `ef ++ sfx`, `[e'pt]`] >> simp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[])
  >- (print_tac "nPE" >> simp[MAP_EQ_CONS] >> strip_tac >>
      simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> dsimp[] >>
      rveq >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >>
      rveq >>
      asm_match `ptree_head ppt = NN nPattern` >>
      asm_match `ptree_fringe ppt = MAP TK pf` >>
      asm_match `ptree_head ept = NN nE` >>
      asm_match `MAP TK ef = ptree_fringe ept` >>
      map_every qexists_tac [`[ppt]`, `ef ++ sfx`, `[ept]`] >> simp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[])
  >- (print_tac "nOptionalSignatureAscription" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied]>>
      strip_tac >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
      Cases_on `sfx` >> simp[peg_eval_tok_NONE] >> fs[])
  >- (print_tac "nMultOps" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      rw[] >> fs[MAP_EQ_CONS, peg_eval_tok_NONE])
  >- (print_tac "nLetDecs" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> rw[]>>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >> rw[]
      >- (DISJ1_TAC >>
          asm_match `ptree_head lpt = NN nLetDec` >>
          asm_match `ptree_fringe lpt = MAP TK lf` >>
          asm_match `ptree_head lspt = NN nLetDecs` >>
          asm_match `ptree_fringe lspt = MAP TK lsf` >>
          map_every qexists_tac [`[lpt]`, `lsf ++ sfx`, `[lspt]`] >>
          `0 < LENGTH (MAP TK lf)`
            by metis_tac [fringe_length_not_nullable,
                          nullable_LetDec] >> fs[] >>
          Cases_on`lsf` >> fs[] >- simp[NT_rank_def] >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
          first_x_assum (match_mp_tac o has_length) >> simp[] >>
          IMP_RES_THEN mp_tac firstSet_nonempty_fringe >> rw[] >> rw[])
      >- simp[peg_respects_firstSets] >>
      DISJ2_TAC >> Cases_on `sfx` >>
      simp[not_peg0_peg_eval_NIL_NONE, peg_eval_tok_NONE] >>
      fs[peg_respects_firstSets])
  >- (print_tac "nLetDec" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      rw[] >> fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >>
      rw[] >> dsimp[peg_eval_tok_NONE] >>
      asm_match `ptree_head vpt = NN nV` >>
      asm_match `ptree_fringe vpt = MAP TK vf` >>
      asm_match `ptree_head ept = NN nE` >>
      asm_match `MAP TK ef = ptree_fringe ept` >>
      map_every qexists_tac [`[vpt]`, `ef ++ sfx`, `[ept]`] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[])
  >- (print_tac "nFQV" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied,
           peg_longV_def] >> rw[] >> fs[MAP_EQ_SING] >> rveq >>
      simp[NT_rank_def, peg_eval_seq_NONE, peg_respects_firstSets,
           firstSet_nV, gramTheory.assert_def])
  >- (print_tac "nFDecl" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> rw[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS, DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
      dsimp[] >>
      asm_match `ptree_head vpt = NN nV` >>
      asm_match `ptree_fringe vpt = MAP TK vf` >>
      asm_match `ptree_head vlpt = NN nVlist1` >>
      asm_match `ptree_fringe vlpt = MAP TK vlf` >>
      asm_match `ptree_head ept = NN nE` >>
      asm_match `MAP TK ef = ptree_fringe ept` >>
      map_every qexists_tac [`[vpt]`, `vlf ++ EqualsT::ef ++ sfx`, `[vlpt]`,
                             `ef ++ sfx`, `[ept]`] >> asimp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[])
  >- (print_tac "nExn" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> rw[] >>
      fs[MAP_EQ_CONS, peg_eval_tok_NONE])
  >- (print_tac "nEtyped" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> rw[] >>
      fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> rw[]
      >- (dsimp[] >> DISJ2_TAC >> DISJ1_TAC >> simp[NT_rank_def] >>
          simp[peg_eval_tok_NONE] >> Cases_on `sfx` >> fs[]) >>
      dsimp[] >> DISJ1_TAC >>
      asm_match `ptree_head ept = NN nEbefore` >>
      asm_match `ptree_fringe ept = MAP TK ef` >>
      asm_match `ptree_head tpt = NN nType` >>
      asm_match `MAP TK tf = ptree_fringe tpt` >>
      map_every qexists_tac [`[ept]`, `tf ++ sfx`, `[tpt]`] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[]) >>
  >- (print_tac "nEtuple" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> rw[] >>
      fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[])
  >- (print_tac "nEseq" >>
      disch_then assume_tac >>
      simp[Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`P` |-> `nEseq`, `SEP` |-> `TK SemicolonT`,
                                 `C` |-> `NN nE`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_applied, MAP_EQ_CONS,
                            AND_IMP_INTRO]) >>
      simp[cmlG_applied, cmlG_FDOM, NT_rank_def] >>
      fs[])
  >- (print_tac "nErel" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> rw[] >>
      fs[MAP_EQ_CONS,MAP_EQ_APPEND,DISJ_IMP_THM,FORALL_AND_THM] >>
      rw[peg_nonfix_def] >> dsimp[]
      >- (DISJ1_TAC >>
          Q.REFINE_EXISTS_TAC `[e1pt]` >> simp[] >>
          CONV_TAC (REDEPTH_CONV EXISTS_AND_CONV) >>
          Q.HO_MATCH_ABBREV_TAC
            `∃i0. peg_eval mmlPEG (e1f ++ rf ++ e2f ++ sfx, X) (SOME(i0,Y)) ∧
                  PP i0` >>
          map_every markerLib.UNABBREV_TAC ["X", "Y", "PP"] >>
          markerLib.RM_ALL_ABBREVS_TAC >>
          qexists_tac `rf ++ e2f ++ sfx` >>
          `0 < LENGTH (MAP TK rf) ∧ 0 < LENGTH (MAP TK e1f)`
            by metis_tac[fringe_length_not_nullable, nullable_Eadd,
                         nullable_RelOps] >>
          fs[] >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
          conj_tac
          >- (first_x_assum (match_mp_tac o has_length) >> asimp[] >>
              Cases_on `rf` >> fs[] >>
              IMP_RES_THEN mp_tac firstSet_nonempty_fringe >>
              simp[] >>
              rw[] >> rw[firstSet_nFQV, firstSet_nV,
                         firstSet_nConstructorName]) >>
          qexists_tac `e2f ++ sfx` >>
          Q.REFINE_EXISTS_TAC `[rt]` >> simp[] >>
          REWRITE_TAC [GSYM APPEND_ASSOC] >> asimp[]) >>
      DISJ2_TAC >> asimp[NT_rank_def] >>
      Cases_on `sfx` >>
      simp[not_peg0_peg_eval_NIL_NONE, peg_eval_seq_NONE] >>
      fs[peg_respects_firstSets])
  >- (print_tac "nEmult" >> disch_then assume_tac >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`P` |-> `nEmult`, `SEP` |-> `NN nMultOps`,
                                 `C` |-> `NN nEapp`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_applied, MAP_EQ_CONS,
                            AND_IMP_INTRO]) >>
      simp[cmlG_applied, cmlG_FDOM, NT_rank_def] >>
      fs[] >> simp[firstSet_nFQV, firstSet_nV, firstSet_nConstructorName] >>
      rw[disjImpI, stringTheory.isUpper_def])
  >- (print_tac "nElogicOR" >> disch_then assume_tac >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`P` |-> `nElogicOR`, `SEP` |-> `TK OrelseT`,
                                 `C` |-> `NN nElogicAND`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_applied, MAP_EQ_CONS,
                            AND_IMP_INTRO]) >>
      simp[cmlG_applied, cmlG_FDOM, NT_rank_def] >>
      conj_tac >- simp[firstSet_nFQV, firstSet_nConstructorName,
                       firstSet_nV] >> fs[])
  >- (print_tac "nElogicAND" >> disch_then assume_tac >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`P` |-> `nElogicAND`, `SEP` |-> `TK AndalsoT`,
                                 `C` |-> `NN nEtyped`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_applied, MAP_EQ_CONS,
                            AND_IMP_INTRO]) >>
      simp[cmlG_applied, cmlG_FDOM, NT_rank_def] >>
      conj_tac >- simp[firstSet_nV,firstSet_nConstructorName,firstSet_nFQV] >>
      fs[])
  >- (print_tac "nElist2" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >> rw[] >>
      fs[MAP_EQ_CONS, MAP_EQ_APPEND, FORALL_AND_THM, DISJ_IMP_THM] >> rw[] >>
      asm_match `ptree_head ept = NN nE` >>
      asm_match `ptree_head elpt = NN nElist1` >>
      asm_match `MAP TK lf = ptree_fringe elpt` >> dsimp[] >>
      map_every qexists_tac [`[ept]`, `lf ++ sfx`, `[elpt]`] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> simp[])
  >- (print_tac "nElist1" >>
      disch_then assume_tac >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`P` |-> `nElist1`, `SEP` |-> `TK CommaT`,
                                 `C` |-> `NN nE`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_applied, MAP_EQ_CONS,
                            AND_IMP_INTRO]) >>
      simp[cmlG_applied, cmlG_FDOM, NT_rank_def] >>
      dsimp[EXTENSION, EQ_IMP_THM] >> fs[])
  >- (print_tac "nEhandle'" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      strip_tac >>
      fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> rw[]
      >- (asm_match `ptree_head ept = NN nElogicOR` >>
          map_every qexists_tac [`[ept]`, `sfx`, `[]`] >>
          conj_tac
          >- (first_x_assum match_mp_tac >> simp[NT_rank_def] >>
              strip_tac >>
              fs[firstSet_nConstructorName, firstSet_nFQV, firstSet_nV]) >>
          simp[peg_eval_tok_NONE] >> DISJ1_TAC >>
          Cases_on `sfx` >> simp[] >> rw[] >> fs[]) >>
      asm_match `ptree_head ept = NN nElogicOR` >>
      asm_match `ptree_head vpt = NN nV` >>
      asm_match `ptree_fringe vpt = MAP TK vf` >>
      asm_match `ptree_head e'pt = NN nE'` >>
      asm_match `MAP TK e'f = ptree_fringe e'pt` >>
      qexists_tac `[ept]` >> dsimp[] >>
      map_every qexists_tac [`vf ++ DarrowT::e'f ++ sfx`, `[vpt]`] >>
      simp[] >> qexists_tac `e'f ++ sfx` >> asimp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[firstSet_nConstructorName, firstSet_nFQV, firstSet_nV])
  >- (print_tac "nEhandle" >>
      simp[MAP_EQ_CONS, Once peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      strip_tac >>
      fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> rw[]
      >- (asm_match `ptree_head ept = NN nElogicOR` >>
          map_every qexists_tac [`[ept]`, `sfx`, `[]`] >>
          simp[NT_rank_def, peg_eval_tok_NONE] >> DISJ1_TAC >>
          Cases_on `sfx` >> simp[] >> strip_tac >> fs[]) >>
      asm_match `ptree_head ept = NN nElogicOR` >>
      asm_match `ptree_head vpt = NN nV` >>
      asm_match `ptree_fringe vpt = MAP TK vf` >>
      asm_match `ptree_head e'pt = NN nE` >>
      asm_match `MAP TK e'f = ptree_fringe e'pt` >>
      qexists_tac `[ept]` >> dsimp[] >>
      map_every qexists_tac [`vf ++ DarrowT::e'f ++ sfx`, `[vpt]`] >>
      simp[] >> qexists_tac `e'f ++ sfx` >> asimp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      asimp[firstSet_nConstructorName, firstSet_nFQV, firstSet_nV])
  >- (print_tac "nEcomp" >> disch_then assume_tac >>
      simp[peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`P` |-> `nEcomp`, `SEP` |-> `NN nCompOps`,
                                 `C` |-> `NN nErel`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_applied, MAP_EQ_CONS,
                            AND_IMP_INTRO]) >>
      simp[cmlG_applied, cmlG_FDOM] >> conj_tac
      >- (conj_tac
          >- simp[firstSet_nV, firstSet_nFQV, firstSet_nConstructorName,
                  stringTheory.isUpper_def] >>
          simp[NT_rank_def]) >>
      fs[])
  >- (print_tac "nEbefore" >> disch_then assume_tac >>
      simp[peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`P` |-> `nEbefore`,
                                 `SEP` |-> `TK (AlphaT "before")`,
                                 `C` |-> `NN nEcomp`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_applied, MAP_EQ_CONS,
                            AND_IMP_INTRO]) >>
      simp[cmlG_applied, cmlG_FDOM, NT_rank_def] >>
      conj_tac >- simp[firstSet_nConstructorName, firstSet_nFQV, firstSet_nV,
                       stringTheory.isUpper_def]>>
      fs[])
  >- (print_tac "nEbase" ...)
  >- (print_tac "nEapp" ...)
  >- (print_tac "nEadd" >> disch_then assume_tac >>
      simp[peg_eval_NT_SOME, mmlpeg_rules_applied] >>
      match_mp_tac (peg_linfix_complete
                      |> Q.INST [`P` |-> `nEadd`, `SEP` |-> `NN nAddOps`,
                                 `C` |-> `NN nEmult`, `master` |-> `pfx`]
                      |> SIMP_RULE (srw_ss() ++ DNF_ss)
                           [sym2peg_def, cmlG_applied, MAP_EQ_CONS,
                            AND_IMP_INTRO]) >>
      simp[cmlG_applied, cmlG_FDOM, NT_rank_def] >>
      conj_tac >- simp[firstSet_nConstructorName, firstSet_nFQV, firstSet_nV,
                       stringTheory.isUpper_def]>>
      fs[])
  >- (print_tac "nE'" >>
      simp_tac list_ss [MAP_EQ_CONS, Once peg_eval_NT_SOME,
                        Once peg_eval_choicel_CONS,
                        mmlpeg_rules_applied] >>
      strip_tac >>
      full_simp_tac list_ss [MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM,
                             FORALL_AND_THM] >> rveq >>
      full_simp_tac list_ss [] >>
      RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >> rveq >>
      RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [MAP_EQ_CONS]) >> rveq
      >- (asm_simp_tac list_ss [peg_eval_seql_CONS, peg_eval_tok_SOME,
                                peg_eval_tok_NONE, tokeq_def, pnt_def] >>
          RW_TAC list_ss [] >>
          simp_tac list_ss [Once peg_eval_choicel_CONS] >> DISJ2_TAC >>
          conj_tac >- simp[peg_respects_firstSets, pnt_def,
                           peg_eval_seq_NONE] >>
          simp_tac list_ss [Once peg_eval_choicel_CONS] >> DISJ1_TAC >>
          dsimp[] >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
          Q.REFINE_EXISTS_TAC `[somept]` >> simp[] >>
          first_assum (unify_firstconj o has_length) >>
          CONV_TAC (REDEPTH_CONV EXISTS_AND_CONV) >>
          disch_then (fn th => conj_tac THENL [match_mp_tac th, ALL_TAC])
          >- simp[firstSet_nFQV, firstSet_nV, firstSet_nConstructorName] >>
          Q.REFINE_EXISTS_TAC `[somept]` >> simp[] >>
          first_assum (unify_firstconj o has_length) >>
          disch_then (fn th => conj_tac THENL [match_mp_tac th, ALL_TAC])
          >- simp[firstSet_nFQV, firstSet_nV, firstSet_nConstructorName] >>
          asimp[])
      >- (asm_simp_tac list_ss [peg_eval_seql_CONS, peg_eval_tok_SOME,
                                peg_eval_tok_NONE, tokeq_def, pnt_def] >>
          RW_TAC list_ss [] >>
          simp_tac list_ss [Once peg_eval_choicel_CONS] >> DISJ2_TAC >>
          conj_tac >- simp[peg_respects_firstSets, pegf_def,
                           peg_eval_seq_NONE] >>
          simp_tac list_ss [Once peg_eval_choicel_CONS] >> DISJ2_TAC >>
          dsimp[peg_eval_tok_NONE] >>
          REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
          Q.REFINE_EXISTS_TAC `[somept]` >> simp[] >>
          first_assum (unify_firstconj o has_length) >>
          disch_then (fn th => conj_tac THENL [match_mp_tac th, ALL_TAC])
          >- simp[] >> asimp[])
      >- (DISJ1_TAC >> simp[]) >>
      DISJ2_TAC >>
      `0 < LENGTH (MAP TK pfx)`
        by metis_tac [fringe_length_not_nullable, nullable_Ehandle'] >>
      full_simp_tac list_ss [] >> conj_tac
      >- (Cases_on `pfx` >> fs[peg_eval_tok_NONE, disjImpI] >> rw[] >>
          IMP_RES_THEN mp_tac firstSet_nonempty_fringe >>
          simp[firstSet_nConstructorName, firstSet_nFQV, firstSet_nV]) >>
      simp_tac std_ss [Once peg_eval_choicel_CONS] >> DISJ1_TAC >>
      simp[NT_rank_def])







*)
val _ = export_theory();
