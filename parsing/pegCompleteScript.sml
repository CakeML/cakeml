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
val firstSet_nTyVarList = store_thm(
  "firstSet_nTyVarList",
  ``firstSet mmlG [NT (mkNT nTyVarList)] = { TyvarT s | T }``,
  simp[firstSetML_eqn] >> simp[firstSetML_def] >>
  simp[cmlG_applied, cmlG_FDOM] >> simp[firstSetML_def] >>
  simp[cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM] >>
  simp[firstSetML_def]);

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

val firstSet_nFQV = store_thm(
  "firstSet_nFQV",
  ``firstSet mmlG [NT (mkNT nFQV)] =
      firstSet mmlG [NT (mkNT nV)] ∪
      { LongidT m i | (m,i) | i ≠ "" ∧ (isAlpha (HD i) ⇒ ¬isUpper (HD i))}``,
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION]);

val firstSetML_nConstructorName = Store_thm(
  "firstSetML_nConstructorName",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ⇒
    (firstSetML mmlG sn (NN nConstructorName::rest) =
     firstSet mmlG [NN nConstructorName])``,
  simp[firstSetML_eqn] >>
  ntac 2 (simp[firstSetML_def] >> simp[cmlG_applied, cmlG_FDOM]) >>
  strip_tac >> simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[firstSetML_def]);

val _ =
    firstSetML_def |> CONJUNCTS |> (fn l => List.take(l,2)) |> rewrites
                   |> (fn ss => augment_srw_ss [ss])

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

val firstSet_nE = Store_thm(
  "firstSet_nE",
  ``firstSet mmlG (NT(mkNT nE)::rest) =
      firstSet mmlG [NT (mkNT nEbase)] ∪ {IfT; CaseT; FnT; RaiseT}``,
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSetML_nE = Store_thm(
  "firstSetML_nE",
  ``mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
    mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
    mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
    mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
    mkNT nElogicOR ∉ sn ∧ mkNT nEhandle ∉ sn ∧ mkNT nE ∉ sn ⇒
    firstSetML mmlG sn (NT (mkNT nE)::rest) = firstSet mmlG [NN nE]``,
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

val firstSet_nE' = Store_thm(
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
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]);

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

(* could generalise this slightly: allowing for nullable seps, but this would
   require a more complicated condition on the sfx, something like
     (sfx ≠ [] ∧ ¬nullable mmlG [SEP] ⇒ HD sfx ∉ firstSet mmlG [SEP]) ∧
     (sfx ≠ [] ∧ nullable mmlG [SEP] ⇒ HD sfx ∉ firstSet mmlG [C])
   and I can't be bothered with that right now. *)

val peg_linfix_complete = store_thm(
  "peg_linfix_complete",
  ``(∀n. SEP = NT n ⇒ nt n I ∈ Gexprs mmlPEG) ∧
    ¬peg0 mmlPEG (sym2peg C) ∧ ¬nullable mmlG [C] ∧
    ¬peg0 mmlPEG (sym2peg SEP) ∧ ¬nullable mmlG [SEP] ∧
    mmlG.rules ' (mkNT P) = { [NT (mkNT P); SEP; C] ; [C] } ∧
    (∀pt pfx0 sfx.
       LENGTH pfx0 < LENGTH master ∧
       valid_ptree mmlG pt ∧ ptree_head pt ∈ {SEP; C} ∧
       ptree_fringe pt = MAP TOK pfx0 ⇒
       peg_eval mmlPEG (pfx0 ++ sfx, sym2peg (ptree_head pt))
                       (SOME(sfx,[pt]))) ∧
    (∀pt sfx.
       valid_ptree mmlG pt ∧ ptree_head pt = C ∧
       ptree_fringe pt = MAP TOK master ⇒
       peg_eval mmlPEG (master ++ sfx, sym2peg C) (SOME(sfx,[pt])))
 ⇒
    ∀pfx pt sfx.
      IS_SUFFIX master pfx ∧
      valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT P) ∧
      (sfx ≠ [] ⇒ HD sfx ∉ firstSet mmlG [SEP]) ∧
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
      first_x_assum (kall_tac o assert (is_forall o concl)) >>
      conj_tac
      >- (fs[rich_listTheory.IS_SUFFIX_compute] >>
          IMP_RES_THEN (assume_tac o SIMP_RULE (srw_ss()) [])
            rich_listTheory.IS_PREFIX_LENGTH >>
          fs[DECIDE ``x:num ≤ y ⇔ x < y ∨ x = y``] >>
          `pfx = master` suffices_by rw[] >>
          metis_tac[rich_listTheory.IS_PREFIX_LENGTH_ANTI, REVERSE_11,
                    listTheory.LENGTH_REVERSE]) >>
      simp[Once pegTheory.peg_eval_cases, mk_linfix_def, peg_eval_seq_NONE] >>
      DISJ1_TAC >>
      Cases_on `SEP` >> fs[sym2peg_def, peg_eval_tok_NONE]
      >- (Cases_on `sfx` >> fs[]) >>
      Cases_on `sfx` >- simp[not_peg0_peg_eval_NIL_NONE, PEG_wellformed] >>
      fs[peg_respects_firstSets]) >>
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
      fs[rich_listTheory.IS_SUFFIX_compute] >>
      IMP_RES_THEN mp_tac rich_listTheory.IS_PREFIX_LENGTH >>
      asimp[]) >>
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
  asimp[] >> rpt strip_tac >>
  simp[Once pegTheory.peg_eval_cases] >> dsimp[] >> DISJ2_TAC >>
  map_every qexists_tac [`pf1`, `sclist`, `pf' ++ sfx`, `[spt']`,
                         `cplist`] >> simp[] >>
  Cases_on `ptree_head cpt`
  >- (fs[sym2peg_def] >>
      simp[mk_linfix_def, left_insert_mk_linfix, left_insert_def]) >>
  simp[left_insert_mk_linfix] >> fs[sym2peg_def] >>
  first_x_assum (mp_tac o MATCH_MP peg_sound) >> rw[] >>
  simp[mk_linfix_def, left_insert_def]);

val stoppers_def = Define`
  (stoppers nVlist1 = {}) ∧
  (stoppers nV = UNIV) ∧
  (stoppers nTyVarList = {RparT}) ∧
  (stoppers nTypeList2 = UNIV DIFF {CommaT; ArrowT}) ∧
  (stoppers nTypeList1 = UNIV DIFF {CommaT; ArrowT}) ∧
  (stoppers nTypeDec = UNIV DELETE AndT) ∧
  (stoppers nType = UNIV DELETE ArrowT) ∧
  (stoppers nTopLevelDecs = UNIV DIFF {StructureT; ValT; FunT; DatatypeT}) ∧
  (stoppers nStarTypes = UNIV DELETE StarT) ∧
  (stoppers nSpecLineList = UNIV DIFF {ValT; DatatypeT; TypeT; SemicolonT;
                                       ArrowT; AndT}) ∧
  (stoppers nSpecLine = UNIV DIFF {ArrowT; AndT}) ∧
  (stoppers _ = UNIV)
`;
val _ = export_rewrites ["stoppers_def"]
(*
val completeness = store_thm(
  "completeness",
  ``∀pt N pfx sfx.
      valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT N) ∧
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
      dsimp[MAP_EQ_CONS] >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      conj_tac
      >- ((* nV nVlist1 *)
          map_every qx_gen_tac [`vpt`, `vlist1pt`] >> strip_tac >>
          rveq >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
          fs[MAP_EQ_APPEND] >>
          asm_match `ptree_fringe vpt = MAP TK vtks` >>
          asm_match `ptree_fringe vlist1pt = MAP TK vltks` >>
          map_every qexists_tac [`[vpt]`, `vltks ++ sfx`, `[vlist1pt]`] >>
          simp[] >> conj_tac
          >- (first_x_assum (qspecl_then [`vpt`, `nV`, `vtks`, `vltks ++ sfx`]
                                         mp_tac o has_length) >>
              simp[] >> disch_then match_mp_tac >>
              erule mp_tac
                (MATCH_MP fringe_length_not_nullable nullable_Vlist1) >>
              simp[]) >>
          first_x_assum (qspecl_then [`vlist1pt`, `nVlist1`, `vltks`, `sfx`]
                                     mp_tac o has_length) >>
          simp[] >> disch_then match_mp_tac >>
          erule mp_tac
            (MATCH_MP fringe_length_not_nullable nullable_V) >> simp[]) >>
      (* nV *)
      qx_gen_tac `vpt` >> strip_tac >>rveq >> fs[] >>
      map_every qexists_tac [`[vpt]`, `sfx`, `[]`] >> simp[] >>
      first_x_assum (qspecl_then [`vpt`, `nV`, `pfx`, `sfx`] mp_tac) >>
      simp[NT_rank_def] >>
      qxchl [`r`] strip_assume_tac
        (MATCH_MP mmlPEG_total nVlist1_expr |> Q.SPEC `[]`) >>
      Cases_on `r` >> simp[] >> Cases_on `x` >> simp[] >>
      imp_res_tac (MATCH_MP (GEN_ALL not_peg0_LENGTH_decreases) peg0_nVlist1) >>
      fs[])
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
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >>
      rpt strip_tac >> rveq >> fs[]
      >- (DISJ1_TAC >> fs[MAP_EQ_SING] >> rveq >>
          asm_match `NN nUQTyOp = ptree_head pt` >>
          first_x_assum (qspecl_then [`pt`, `nUQTyOp`, `pfx`, `sfx`] mp_tac)>>
          simp[NT_rank_def] >> fs[])
      >- (DISJ2_TAC >> fs[MAP_EQ_CONS] >> simp[peg_eval_seq_NONE] >> rveq >>
          fs[] >>
          asm_match `ptree_head tyvl_pt = NN nTyVarList` >>
          asm_match `ptree_head tyop_pt = NN nUQTyOp` >>
          fs [MAP_EQ_APPEND, MAP_EQ_SING, MAP_EQ_CONS] >> rveq >>
          asm_match `ptree_fringe tyop_pt = MAP TK opf` >> conj_tac
          >- simp[Once pegTheory.peg_eval_cases, FDOM_cmlPEG, mmlpeg_rules_applied,
                  peg_eval_tok_NONE] >>
          dsimp[] >>
          map_every qexists_tac [`[tyvl_pt]`, `opf ++ sfx`, `[tyop_pt]`] >>
          simp[] >>
          asm_match `ptree_fringe tyvl_pt = MAP TK vlf` >>
          first_x_assum
             (qspecl_then [`tyvl_pt`, `nTyVarList`, `vlf`,
                           `RparT::(opf ++ sfx)`] mp_tac o has_length) >>
              simp[] >> metis_tac[listTheory.APPEND_ASSOC, listTheory.APPEND])>>
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
      simp_tac (srw_ss() ++ ARITH_ss) [] >> simp[] >> strip_tac >>
      map_every qexists_tac [`[typt]`, `lf ++ sfx`, `[tylpt]`] >>
      simp[])
  >- (print_tac "nTypeList1" >> dsimp[MAP_EQ_CONS] >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_tok_NONE] >>
      dsimp[] >> conj_tac
      >- (qx_gen_tac `typt` >> rw[] >> fs[] >> DISJ2_TAC >> DISJ1_TAC >>
          first_x_assum (qspecl_then [`typt`, `nType`, `pfx`, `sfx`] mp_tac) >>
          simp[NT_rank_def] >> Cases_on `sfx` >> fs[]) >>
      map_every qx_gen_tac [`typt`, `tylpt`] >> rw[] >>
      fs[MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >> DISJ1_TAC >>
      asm_match `ptree_fringe typt = MAP TK tyf` >>
      asm_match `MAP TK tylf = ptree_fringe tylpt` >>
      map_every qexists_tac [`[typt]`, `tylf ++ sfx`, `[tylpt]`] >>
      simp[] >> REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >>
      simp[])
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
      simp[])
  >- (print_tac "nType" >> dsimp[MAP_EQ_CONS] >> conj_tac
      >- (simp[peg_eval_NT_SOME] >>
          simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_Type_def,
               peg_eval_choice, sumID_def, peg_eval_seq_NONE,
               peg_eval_tok_NONE] >> dsimp[list_case_lemma] >>
          qx_gen_tac `dpt` >> strip_tac >> DISJ1_TAC >> rveq >> fs[] >>
          Cases_on `sfx` >> fs[]
          >- (first_x_assum (qspecl_then [`dpt`, `nDType`, `pfx`, `[]`]
                                         mp_tac) >> simp[NT_rank_def]) >>
          first_x_assum match_mp_tac >> simp[NT_rank_def]) >>
      map_every qx_gen_tac [`dpt`, `typt`] >> rw[] >>
      fs[DISJ_IMP_THM, FORALL_AND_THM, MAP_EQ_APPEND, MAP_EQ_CONS] >> rw[] >>
      simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_Type_def] >>
      asm_match `ptree_fringe dpt = MAP TK df` >>
      asm_match `MAP TK tf = ptree_fringe typt` >> loseC ``NT_rank`` >>
      map_every qexists_tac [`ArrowT::tf ++ sfx`, `[dpt]`,
                             `[Lf (TK ArrowT); typt]`] >> simp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, listTheory.APPEND] >> asimp[] >>
      dsimp[peg_eval_choice, sumID_def] >> asimp[])
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
        by simp[NT_rank_def]>> simp[] >> fs[])
  >- (print_tac "nTyOp" >>
      simp[peg_eval_NT_SOME, mmlpeg_rules_applied, FDOM_cmlPEG, MAP_EQ_CONS] >>
      rw[] >> fs[MAP_EQ_CONS]
      >- (asm_match `ptree_head pt = NN nUQTyOp` >>
          first_x_assum (qspecl_then [`pt`, `nUQTyOp`, `pfx`, `sfx`] mp_tac) >>
          simp[NT_rank_def, peg_eval_NT_SOME, mmlpeg_rules_applied,
               FDOM_cmlPEG]) >>
      match_mp_tac peg_respects_firstSets >> simp[firstSet_nUQTyOp, PEG_exprs])
  >- (print_tac "nTopLevelDecs" >> dsimp[MAP_EQ_CONS] >> conj_tac
      >- (simp[peg_eval_NT_SOME] >>
          simp[mmlpeg_rules_applied, FDOM_cmlPEG, peg_eval_rpt] >>
          map_every qx_gen_tac [`tldpt`, `tldspt`] >> rw[] >>
          fs[MAP_EQ_CONS, MAP_EQ_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
          asm_match `ptree_fringe tldpt = MAP TK df` >>
          asm_match `ptree_fringe tldspt = MAP TK sf` >>
          Cases_on `sf = []`
          >- (first_x_assum (qspecl_then [`tldpt`, `nTopLevelDec`, `df`, `sfx`]
                                         mp_tac) >>
              simp[NT_rank_def] >> strip_tac >> qexists_tac `[[tldpt]]` >>
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
                           (SOME (sf ++ sfx, [tldpt]))` by simp[] >>
          `peg_eval mmlPEG (sf ++ sfx, nt (mkNT nTopLevelDecs) I)
                           (SOME (sfx, [tldspt]))` by asimp[] >>
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
         PEG_wellformed])
  >- (print_tac "nTopLevelDec" >> simp[peg_eval_NT_SOME] >>
      simp[mmlpeg_rules_applied, FDOM_cmlPEG] >> strip_tac >>
      fs[MAP_EQ_SING] >> rw[] >> fs[]
      >- (DISJ1_TAC >> first_x_assum match_mp_tac >> simp[NT_rank_def]) >>
      DISJ2_TAC >> reverse conj_tac
      >- (first_x_assum match_mp_tac >> simp[NT_rank_def]) >>
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
          DISJ2_TAC





*)
val _ = export_theory();
