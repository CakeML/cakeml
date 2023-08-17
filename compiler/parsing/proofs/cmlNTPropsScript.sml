(*
  Properties (first sets etc) for non-terminals in the CakeML grammar
*)
open HolKernel Parse boolLib bossLib;

open preamble
open NTpropertiesTheory gramTheory gramPropsTheory
val _ = new_theory "cmlNTProps";

val _ = set_grammar_ancestry ["gramProps"]

val disjImpI = Q.prove(`~p \/ q ⇔ p ⇒ q`, DECIDE_TAC)

Theorem firstSet_nUQTyOp[simp]:
  firstSet cmlG (NN nUQTyOp::rest) =
  {AlphaT s | T} ∪ {SymbolT s | T}
Proof
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSet_nTyOp[simp]:
  firstSet cmlG (NN nTyOp :: rest) =
  {AlphaT s | T} ∪ {SymbolT s | T} ∪ {LongidT s1 s2 | T}
Proof
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSet_nPTbase[simp]:
  firstSet cmlG (NN nPTbase :: rest) =
  firstSet cmlG [NN nTyOp] ∪ {LparT} ∪ {TyvarT s | T}
Proof
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM, SimpLHS] >>
  simp[nullable_PTbase] >> dsimp[Once EXTENSION] >> metis_tac[]
QED

Theorem firstSet_nTbaseList[simp]:
  firstSet cmlG (NN nTbaseList :: rest) =
  firstSet cmlG [NN nPTbase] ∪ firstSet cmlG rest
Proof
  simp[Once firstSet_NT, SimpLHS, cmlG_FDOM, cmlG_applied,
       nullable_TbaseList] >> simp[]
QED

Theorem firstSet_nTyVarList[simp]:
  firstSet cmlG [NT (mkNT nTyVarList)] = { TyvarT s | T }
Proof
  simp[firstSetML_eqn] >> simp[firstSetML_def] >>
  simp[cmlG_applied, cmlG_FDOM] >> simp[firstSetML_def] >>
  simp[cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM] >>
  simp[firstSetML_def]
QED
val _ =
firstSetML_def |> CONJUNCTS |> (fn l => List.take(l,2)) |> rewrites
                                                        |> (fn ss => augment_srw_ss [ss])

Theorem firstSet_nLetDec[simp]:
  firstSet cmlG [NT (mkNT nLetDec)] = {ValT; FunT}
Proof
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM,
       cmlG_applied, INSERT_UNION_EQ]
QED

Theorem firstSet_nLetDecs[simp]:
  firstSet cmlG [NT (mkNT nLetDecs)] = {ValT; FunT; SemicolonT}
Proof
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM,
       cmlG_applied] >>
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied, INSERT_UNION_EQ]
QED

Theorem firstSet_nTypeDec[simp]:
  firstSet cmlG [NT (mkNT nTypeDec)] = {DatatypeT}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]
QED

Theorem firstSet_nTypeAbbrevDec[simp]:
  firstSet cmlG [NT (mkNT nTypeAbbrevDec)] = {TypeT}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]
QED

Theorem firstSet_nStructure[simp]:
  firstSet cmlG [NT (mkNT nStructure)] = {StructureT}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]
QED

Theorem firstSet_nDecl[simp]:
  firstSet cmlG [NT (mkNT nDecl)] =
  {ValT; FunT; DatatypeT;ExceptionT;TypeT;LocalT;StructureT}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ]
QED

Theorem firstSet_nDecls[simp]:
  firstSet cmlG [NN nDecls] =
  {ValT; DatatypeT; FunT; SemicolonT; ExceptionT; TypeT; LocalT;StructureT}
Proof
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  ONCE_REWRITE_TAC [firstSetML_def] >>
  simp[cmlG_applied, cmlG_FDOM, INSERT_UNION_EQ, INSERT_COMM]
QED

Theorem IMAGE_GSPEC1[local]:
  IMAGE f (GSPEC (λa. (g a, P a))) = GSPEC (λa. (f (g a), P a))
Proof
  simp[EXTENSION, PULL_EXISTS]
QED

Theorem BIGUNION_singletons[local,simp]:
  BIGUNION (GSPEC (λa. {f a}, P a)) = GSPEC (λa. f a, P a)
Proof
  simp[Once EXTENSION, PULL_EXISTS]
QED

Theorem firstSet_nMultOps[simp]:
  firstSet cmlG (NT (mkNT nMultOps)::rest) =
  {AlphaT "div"; AlphaT"mod"; StarT} ∪ {SymbolT s | validMultSym s}
Proof
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ, IMAGE_GSPEC1]
QED

Theorem firstSet_nRelOps[simp]:
  firstSet cmlG (NT (mkNT nRelOps)::rest) =
  EqualsT INSERT {SymbolT s | validRelSym s}
Proof
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_applied, cmlG_FDOM,
       IMAGE_GSPEC1] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSet_nAddOps[simp]:
  firstSet cmlG (NT (mkNT nAddOps)::rest) = {SymbolT s | validAddSym s}
Proof
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_applied, cmlG_FDOM,
       INSERT_UNION_EQ, IMAGE_GSPEC1]
QED

Theorem firstSet_nCompOps[simp]:
  firstSet cmlG (NT (mkNT nCompOps)::rest) = {AlphaT "o"; SymbolT ":="}
Proof
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ]
QED

Theorem firstSet_nListOps[simp]:
  firstSet cmlG (NT (mkNT nListOps)::rest) = {SymbolT s | validListSym s}
Proof
  simp[firstSetML_eqn, Once firstSetML_def, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ, INSERT_COMM, IMAGE_GSPEC1]
QED

Theorem firstSet_nSpecLine[simp]:
  firstSet cmlG [NT (mkNT nSpecLine)] =
  {ValT; DatatypeT; TypeT; ExceptionT}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied, INSERT_UNION_EQ, INSERT_COMM]
QED

Theorem firstSet_nSpecLineList[simp]:
  firstSet cmlG [NT (mkNT nSpecLineList)] =
  {ValT; DatatypeT; TypeT; SemicolonT; ExceptionT}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied,
       INSERT_UNION_EQ, INSERT_COMM]
QED

Theorem firstSet_nV:
  firstSet cmlG (NN nV:: rest) =
  { AlphaT s | s ≠ "" ∧ ¬isUpper (HD s) ∧ s ≠ "before" ∧ s ≠ "div" ∧
               s ≠ "mod" ∧ s ≠ "o"} ∪
                                    { SymbolT s | validPrefixSym s }
Proof
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM, IMAGE_GSPEC1] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSet_nFQV:
  firstSet cmlG [NT (mkNT nFQV)] =
  firstSet cmlG [NT (mkNT nV)] ∪
           { LongidT m i | (m,i) | i ≠ "" ∧ (isAlpha (HD i) ⇒ ¬isUpper (HD i))}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION]
QED

Theorem firstSet_nUQConstructorName:
  firstSet cmlG (NN nUQConstructorName :: rest) =
  { AlphaT s | s ≠ "" ∧ isUpper (HD s) }
Proof
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSet_nConstructorName:
  firstSet cmlG (NN nConstructorName :: rest) =
  { LongidT str s | (str,s) | s ≠ "" ∧ isAlpha (HD s) ∧ isUpper (HD s)} ∪
                                                                        { AlphaT s | s ≠ "" ∧ isUpper (HD s) }
Proof
  ntac 2 (simp [Once firstSet_NT, cmlG_applied, cmlG_FDOM]) >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSetML_nConstructorName[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ⇒
  (firstSetML cmlG sn (NN nConstructorName::rest) =
   firstSet cmlG [NN nConstructorName])
Proof
  simp[firstSetML_eqn] >>
  ntac 2 (simp[firstSetML_def] >> simp[cmlG_applied, cmlG_FDOM]) >>
  strip_tac >> simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[firstSetML_def]
QED

Theorem firstSetML_nV[simp]:
  mkNT nV ∉ sn ⇒
  (firstSetML cmlG sn (NN nV::rest) = firstSet cmlG [NN nV])
Proof
  simp[firstSetML_eqn] >> simp[firstSetML_def] >>
  simp[cmlG_FDOM, cmlG_applied] >> strip_tac >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSetML_nFQV[simp]:
  mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ⇒
  (firstSetML cmlG sn (NN nFQV::rest) = firstSet cmlG [NN nFQV])
Proof
  simp[firstSetML_eqn] >>
  ntac 2 (simp[firstSetML_def] >> simp[cmlG_FDOM, cmlG_applied]) >>
  strip_tac >> simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSet_nEtuple[simp]:
  firstSet cmlG [NT (mkNT nEtuple)] = {LparT}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied]
QED

Theorem firstSet_nEliteral[simp]:
  firstSet cmlG [NT (mkNT nEliteral)] =
  {IntT i | T} ∪ {StringT s | T} ∪ {CharT c | T} ∪ {WordT w | T} ∪
               {FFIT s | T}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION] >> gen_tac >> eq_tac >> rw[]
QED

Theorem firstSetML_nEliteral[simp]:
  mkNT nEliteral ∉ sn ⇒
  firstSetML cmlG sn (NT (mkNT nEliteral)::rest) =
  firstSet cmlG [NT (mkNT nEliteral)]
Proof
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION] >> metis_tac[]
QED

Theorem firstSet_nEbase[simp]:
  firstSet cmlG [NT (mkNT nEbase)] =
  {LetT; LparT; LbrackT; OpT} ∪ firstSet cmlG [NT (mkNT nFQV)] ∪
                              firstSet cmlG [NT (mkNT nEliteral)] ∪
                              firstSet cmlG [NT (mkNT nConstructorName)]
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION] >> gen_tac >> eq_tac >> rw[] >> simp[]
QED

Theorem firstSetML_nEbase[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEliteral ∉ sn ⇒
  firstSetML cmlG sn (NT (mkNT nEbase)::rest) =
  firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >> strip_tac >>
  Cases_on `mkNT nEtuple ∈ sn` >>
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied] >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSet_nEapp[simp]:
  firstSet cmlG [NT (mkNT nEapp)] = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[Once firstSetML_eqn, SimpLHS] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSetML_nEapp[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nEapp) :: rest) =
  firstSet cmlG [NT(mkNT nEbase)]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSet_nEmult[simp]:
  firstSet cmlG [NT (mkNT nEmult)] = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nEmult[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nEmult) :: rest) =
  firstSet cmlG [NT (mkNT nEbase)]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nEadd[simp]:
  firstSet cmlG [NT (mkNT nEadd)] = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nEadd[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nEliteral ∉ sn⇒
  firstSetML cmlG sn (NT (mkNT nEadd) :: rest) =
  firstSet cmlG [NT(mkNT nEbase)]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nElistop[simp]:
  firstSet cmlG (NT (mkNT nElistop)::rest) =
  firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nElistop[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nElistop ∉ sn ∧
  mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nElistop) :: rest) =
  firstSet cmlG [NT(mkNT nEbase)]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nErel[simp]:
  firstSet cmlG (NT(mkNT nErel)::rest) = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nErel[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nElistop ∉ sn ∧
  mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nErel) :: rest) = firstSet cmlG [NN nEbase]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nEcomp[simp]:
  firstSet cmlG (NT(mkNT nEcomp)::rest) = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nEcomp[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
  mkNT nElistop ∉ sn ∧ mkNT nEliteral ∉ sn ⇒
  firstSetML cmlG sn (NT (mkNT nEcomp) :: rest) = firstSet cmlG [NN nEbase]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nEbefore[simp]:
  firstSet cmlG (NT(mkNT nEbefore)::rest) =
  firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nEbefore[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
  mkNT nEbefore ∉ sn ∧ mkNT nElistop ∉ sn ∧ mkNT nEliteral ∉ sn ⇒
  firstSetML cmlG sn (NT (mkNT nEbefore)::rest) = firstSet cmlG [NN nEbase]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nEtyped[simp]:
  firstSet cmlG (NT(mkNT nEtyped)::rest) = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nEtyped[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
  mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElistop ∉ sn ∧
  mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nEtyped)::rest) = firstSet cmlG [NN nEbase]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nElogicAND[simp]:
  firstSet cmlG (NT(mkNT nElogicAND)::rest) = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nElogicAND[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
  mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
  mkNT nElistop ∉ sn ∧ mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nElogicAND)::rest) =
  firstSet cmlG [NN nEbase]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nElogicOR[simp]:
  firstSet cmlG (NT(mkNT nElogicOR)::rest) = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nElogicOR[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
  mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
  mkNT nElogicOR ∉ sn ∧ mkNT nElistop ∉ sn ∧ mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nElogicOR)::rest) =
  firstSet cmlG [NN nEbase]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nEhandle[simp]:
  firstSet cmlG (NT(mkNT nEhandle)::rest) = firstSet cmlG [NT (mkNT nEbase)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSetML_nEhandle[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
  mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
  mkNT nElogicOR ∉ sn ∧ mkNT nEhandle ∉ sn ∧ mkNT nElistop ∉ sn ∧
  mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nEhandle)::rest) =
  firstSet cmlG [NN nEbase]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM])
QED

Theorem firstSet_nE:
  firstSet cmlG (NT(mkNT nE)::rest) =
  firstSet cmlG [NT (mkNT nEbase)] ∪ {IfT; CaseT; FnT; RaiseT}
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSet_nTopLevelDecs[simp]:
  firstSet cmlG [NN nTopLevelDecs] =
  {ValT; FunT; SemicolonT; DatatypeT; StructureT; ExceptionT; TypeT;
   LocalT} ∪
           firstSet cmlG [NT (mkNT nE)]
Proof
  simp[Once firstSet_NT, cmlG_applied, cmlG_FDOM] >>
  ONCE_REWRITE_TAC [firstSet_NT] >> simp[cmlG_applied, cmlG_FDOM] >>
  simp[INSERT_UNION_EQ, INSERT_COMM] >>
  simp[EXTENSION, EQ_IMP_THM] >> rpt strip_tac >> rveq >> simp[]
QED

Theorem firstSet_nNonETopLevelDecs[simp]:
  firstSet cmlG [NN nNonETopLevelDecs] =
  {ValT; FunT; SemicolonT; DatatypeT; StructureT; ExceptionT; TypeT;
   LocalT}
Proof
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  simp[Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  simp[INSERT_COMM, INSERT_UNION_EQ]
QED

Theorem firstSet_nEseq[simp]:
  firstSet cmlG (NN nEseq :: rest) = firstSet cmlG [NN nE]
Proof
  simp[SimpLHS, Once firstSet_NT, cmlG_FDOM, cmlG_applied] >>
  simp[firstSet_nE]
QED

Theorem NOTIN_firstSet_nE[simp]:
  ValT ∉ firstSet cmlG (NT (mkNT nE) :: rest) ∧
  StructureT ∉ firstSet cmlG (NT (mkNT nE) :: rest) ∧
  FunT ∉ firstSet cmlG (NT (mkNT nE) :: rest) ∧
  DatatypeT ∉ firstSet cmlG (NT (mkNT nE) :: rest) ∧
  ExceptionT ∉ firstSet cmlG (NT (mkNT nE) :: rest) ∧
  SemicolonT ∉ firstSet cmlG (NT (mkNT nE) :: rest) ∧
  RparT ∉ firstSet cmlG (NN nE :: rest) ∧
  RbrackT ∉ firstSet cmlG (NN nE :: rest) ∧
  TypeT ∉ firstSet cmlG (NN nE :: rest)
Proof
  simp[firstSet_nE, firstSet_nFQV] >>
  rpt (dsimp[Once firstSet_NT, cmlG_FDOM, cmlG_applied, disjImpI])
QED

Theorem firstSetML_nE[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
  mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
  mkNT nElogicOR ∉ sn ∧ mkNT nEhandle ∉ sn ∧ mkNT nE ∉ sn ∧
  mkNT nElistop ∉ sn ∧ mkNT nEliteral ∉ sn ⇒
  firstSetML cmlG sn (NT (mkNT nE)::rest) = firstSet cmlG [NN nE]
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM, firstSet_nE]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSet_nE':
  firstSet cmlG (NT(mkNT nE')::rest) =
  firstSet cmlG [NT (mkNT nEbase)] ∪ {IfT; RaiseT}
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSetML_nE'[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nUQConstructorName ∉ sn ∧
  mkNT nEbase ∉ sn ∧ mkNT nFQV ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nEapp ∉ sn ∧
  mkNT nEmult ∉ sn ∧ mkNT nEadd ∉ sn ∧ mkNT nErel ∉ sn ∧ mkNT nEcomp ∉ sn ∧
  mkNT nEbefore ∉ sn ∧ mkNT nEtyped ∉ sn ∧ mkNT nElogicAND ∉ sn ∧
  mkNT nElogicOR ∉ sn ∧ mkNT nE' ∉ sn ∧ mkNT nElistop ∉ sn ∧
  mkNT nEliteral ∉ sn
  ⇒
  firstSetML cmlG sn (NT (mkNT nE')::rest) = firstSet cmlG [NN nE']
Proof
  ntac 2 (simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM, firstSet_nE']) >>
  simp[Once EXTENSION, EQ_IMP_THM] >> dsimp[]
QED

Theorem firstSet_nElist1[simp]:
  firstSet cmlG (NT (mkNT nElist1)::rest) = firstSet cmlG [NT (mkNT nE)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]
QED

Theorem firstSet_nElist2[simp]:
  firstSet cmlG (NT (mkNT nElist2)::rest) = firstSet cmlG [NT (mkNT nE)]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]
QED

Theorem firstSetML_nPtuple[simp]:
  mkNT nPtuple ∉ sn ⇒ (firstSetML cmlG sn (NN nPtuple :: rest) = {LparT})
Proof
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied]
QED

Theorem firstSet_nPtuple[simp]:
  firstSet cmlG (NN nPtuple :: rest) = {LparT}
Proof
  simp[firstSetML_eqn, firstSetML_nPtuple]
QED

Theorem firstSet_nPbase[simp]:
  firstSet cmlG (NN nPbase :: rest) =
  {LparT; UnderbarT; LbrackT; OpT} ∪ {IntT i | T } ∪ {StringT s | T } ∪
                                   {CharT c | T } ∪
                                   firstSet cmlG [NN nConstructorName] ∪ firstSet cmlG [NN nV]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSetML_nPbase[simp]:
  mkNT nPbase ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nConstructorName ∉ sn ∧
  mkNT nUQConstructorName ∉ sn ∧ mkNT nPtuple ∉ sn ⇒
  firstSetML cmlG sn (NN nPbase :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSet_nPConApp[simp]:
  firstSet cmlG (NN nPConApp :: rest) =
  firstSet cmlG [NN nConstructorName]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  simp[Once firstSetML_def]
QED

Theorem firstSetML_nPConApp[simp]:
  mkNT nConstructorName ∉ sn ∧ mkNT nPConApp ∉ sn ∧
  mkNT nUQConstructorName ∉ sn ⇒
  firstSetML cmlG sn (NN nPConApp :: rest) =
  firstSet cmlG [NN nConstructorName]
Proof
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied] >>
  simp[Once firstSetML_def]
QED

Theorem firstSet_nPapp[simp]:
  firstSet cmlG (NN nPapp :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSetML_nPapp[simp]:
  mkNT nPbase ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nConstructorName ∉ sn ∧
  mkNT nUQConstructorName ∉ sn ∧ mkNT nPtuple ∉ sn ∧ mkNT nPapp ∉ sn ∧
  mkNT nPConApp ∉ sn ⇒
  firstSetML cmlG sn (NN nPapp :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSet_nPcons[simp]:
  firstSet cmlG (NN nPcons :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM]
QED

Theorem firstSetML_nPcons[simp]:
  mkNT nPbase ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nConstructorName ∉ sn ∧
  mkNT nUQConstructorName ∉ sn ∧ mkNT nPtuple ∉ sn ∧ mkNT nPapp ∉ sn ∧
  mkNT nPcons ∉ sn ∧ mkNT nPConApp ∉ sn ⇒
  firstSetML cmlG sn (NN nPcons :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied]
QED

Theorem firstSet_nPas[simp]:
  firstSet cmlG (NN nPas :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  rw [EXTENSION, EQ_IMP_THM] >> gs []
QED

Theorem firstSetML_nPas[simp]:
  mkNT nPbase ∉ sn ∧ mkNT nV ∉ sn ∧ mkNT nConstructorName ∉ sn ∧
  mkNT nUQConstructorName ∉ sn ∧ mkNT nPtuple ∉ sn ∧ mkNT nPapp ∉ sn ∧
  mkNT nPcons ∉ sn ∧ mkNT nPConApp ∉ sn ∧ mkNT nPas ∉ sn ⇒
  firstSetML cmlG sn (NN nPas :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[Once firstSetML_def, cmlG_FDOM, cmlG_applied] >>
  rw [EXTENSION, EQ_IMP_THM] >> gs []
QED

Theorem firstSet_nPattern[simp]:
  firstSet cmlG (NN nPattern :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[SimpLHS, firstSetML_eqn] >>
  simp[Once firstSetML_def, cmlG_applied, cmlG_FDOM] >>
  dsimp[Once EXTENSION, EQ_IMP_THM]
QED

Theorem firstSet_nPatternList[simp]:
  firstSet cmlG (NN nPatternList :: rest) = firstSet cmlG [NN nPattern]
Proof
  simp[SimpLHS, Once firstSet_NT, cmlG_FDOM, cmlG_applied] >> simp[]
QED

Theorem firstSet_nPbaseList1[simp]:
  firstSet cmlG (NN nPbaseList1 :: rest) = firstSet cmlG [NN nPbase]
Proof
  simp[SimpLHS, Once firstSet_NT, cmlG_FDOM, cmlG_applied] >> simp[]
QED

Theorem NOTIN_firstSet_nV[simp]:
  CommaT ∉ firstSet cmlG [NN nV] ∧ LparT ∉ firstSet cmlG [NN nV] ∧
  RparT ∉ firstSet cmlG [NN nV] ∧ UnderbarT ∉ firstSet cmlG [NN nV] ∧
  BarT ∉ firstSet cmlG [NN nV] ∧ OpT ∉ firstSet cmlG [NN nV] ∧
  FnT ∉ firstSet cmlG [NN nV] ∧ IfT ∉ firstSet cmlG [NN nV] ∧
  EqualsT ∉ firstSet cmlG [NN nV] ∧ DarrowT ∉ firstSet cmlG [NN nV] ∧
  ValT ∉ firstSet cmlG [NN nV] ∧
  ExceptionT ∉ firstSet cmlG [NN nV] ∧
  EndT ∉ firstSet cmlG [NN nV] ∧
  AndT ∉ firstSet cmlG [NN nV] ∧
  FFIT s ∉ firstSet cmlG [NN nV] ∧
  FunT ∉ firstSet cmlG [NN nV] ∧
  LbrackT ∉ firstSet cmlG [NN nV] ∧
  LocalT ∉ firstSet cmlG [NN nV] ∧
  RbrackT ∉ firstSet cmlG [NN nV] ∧
  InT ∉ firstSet cmlG [NN nV] ∧
  IntT i ∉ firstSet cmlG [NN nV] ∧
  StringT s ∉ firstSet cmlG [NN nV] ∧
  CharT c ∉ firstSet cmlG [NN nV] ∧
  ThenT ∉ firstSet cmlG [NN nV] ∧
  ElseT ∉ firstSet cmlG [NN nV] ∧
  CaseT ∉ firstSet cmlG [NN nV] ∧
  LetT ∉ firstSet cmlG [NN nV] ∧
  OfT ∉ firstSet cmlG [NN nV] ∧
  RaiseT ∉ firstSet cmlG [NN nV] ∧
  DatatypeT ∉ firstSet cmlG [NN nV] ∧
  TypeT ∉ firstSet cmlG [NN nV] ∧
  SemicolonT ∉ firstSet cmlG [NN nV] ∧ ColonT ∉ firstSet cmlG [NN nV] ∧
  StructureT ∉ firstSet cmlG [NN nV] ∧ WordT w ∉ firstSet cmlG [NN nV] ∧
  SymbolT "::" ∉ firstSet cmlG [NN nV]
Proof
  simp[firstSet_nV] >> simp[validPrefixSym_def]
QED

Theorem NOTIN_firstSet_nFQV[simp]:
  AndT ∉ firstSet cmlG [NN nFQV] ∧
  BarT ∉ firstSet cmlG [NN nFQV] ∧
  CaseT ∉ firstSet cmlG [NN nFQV] ∧
  CharT c ∉ firstSet cmlG [NN nFQV] ∧
  ColonT ∉ firstSet cmlG [NN nFQV] ∧
  CommaT ∉ firstSet cmlG [NN nFQV] ∧
  DarrowT ∉ firstSet cmlG [NN nFQV] ∧
  DatatypeT ∉ firstSet cmlG [NN nFQV] ∧
  ElseT ∉ firstSet cmlG [NN nFQV] ∧
  EndT ∉ firstSet cmlG [NN nFQV] ∧
  EqualsT ∉ firstSet cmlG [NN nFQV] ∧
  ExceptionT ∉ firstSet cmlG [NN nFQV] ∧
  FFIT s ∉ firstSet cmlG [NN nFQV] ∧
  FnT ∉ firstSet cmlG [NN nFQV] ∧
  FunT ∉ firstSet cmlG [NN nFQV] ∧
  IfT ∉ firstSet cmlG [NN nFQV] ∧
  InT ∉ firstSet cmlG [NN nFQV] ∧
  IntT i ∉ firstSet cmlG [NN nFQV] ∧
  LbrackT ∉ firstSet cmlG [NN nFQV] ∧
  LetT ∉ firstSet cmlG [NN nFQV] ∧
  LocalT ∉ firstSet cmlG [NN nFQV] ∧
  LparT ∉ firstSet cmlG [NN nFQV] ∧
  OfT ∉ firstSet cmlG [NN nFQV] ∧
  OpT ∉ firstSet cmlG [NN nFQV] ∧
  RaiseT ∉ firstSet cmlG [NN nFQV] ∧
  RbrackT ∉ firstSet cmlG [NN nFQV] ∧
  RparT ∉ firstSet cmlG [NN nFQV] ∧
  SemicolonT ∉ firstSet cmlG [NN nFQV] ∧
  StringT s ∉ firstSet cmlG [NN nFQV] ∧
  StructureT ∉ firstSet cmlG [NN nFQV] ∧
  ThenT ∉ firstSet cmlG [NN nFQV] ∧
  TypeT ∉ firstSet cmlG [NN nFQV] ∧
  UnderbarT ∉ firstSet cmlG [NN nFQV] ∧
  ValT ∉ firstSet cmlG [NN nFQV] ∧
  WordT w ∉ firstSet cmlG [NN nFQV]
Proof
  simp[firstSet_nFQV]
QED

Theorem NOTIN_firstSet_nConstructorName[simp]:
  AndT ∉ firstSet cmlG [NN nConstructorName] ∧
  BarT ∉ firstSet cmlG [NN nConstructorName] ∧
  ColonT ∉ firstSet cmlG [NN nConstructorName] ∧
  CaseT ∉ firstSet cmlG [NN nConstructorName] ∧
  CharT c ∉ firstSet cmlG [NN nConstructorName] ∧
  CommaT ∉ firstSet cmlG [NN nConstructorName] ∧
  DarrowT ∉ firstSet cmlG [NN nConstructorName] ∧
  DatatypeT ∉ firstSet cmlG [NN nConstructorName] ∧
  ElseT ∉ firstSet cmlG [NN nConstructorName] ∧
  EndT ∉ firstSet cmlG [NN nConstructorName] ∧
  EqualsT ∉ firstSet cmlG [NN nConstructorName] ∧
  ExceptionT ∉ firstSet cmlG [NN nConstructorName] ∧
  FFIT s ∉ firstSet cmlG [NN nConstructorName] ∧
  FnT ∉ firstSet cmlG [NN nConstructorName] ∧
  FunT ∉ firstSet cmlG [NN nConstructorName] ∧
  IfT ∉ firstSet cmlG [NN nConstructorName] ∧
  InT ∉ firstSet cmlG [NN nConstructorName] ∧
  IntT i ∉ firstSet cmlG [NN nConstructorName] ∧
  LbrackT ∉ firstSet cmlG [NN nConstructorName] ∧
  LetT ∉ firstSet cmlG [NN nConstructorName] ∧
  LocalT ∉ firstSet cmlG [NN nConstructorName] ∧
  LparT ∉ firstSet cmlG [NN nConstructorName] ∧
  OfT ∉ firstSet cmlG [NN nConstructorName] ∧
  OpT ∉ firstSet cmlG [NN nConstructorName] ∧
  RaiseT ∉ firstSet cmlG [NN nConstructorName] ∧
  RbrackT ∉ firstSet cmlG [NN nConstructorName] ∧
  RparT ∉ firstSet cmlG [NN nConstructorName] ∧
  SemicolonT ∉ firstSet cmlG [NN nConstructorName] ∧
  StringT s ∉ firstSet cmlG [NN nConstructorName] ∧
  StructureT ∉ firstSet cmlG [NN nConstructorName] ∧
  SymbolT "::" ∉ firstSet cmlG [NN nConstructorName] ∧
  SymbolT "ref" ∉ firstSet cmlG [NN nConstructorName] ∧
  ThenT ∉ firstSet cmlG [NN nConstructorName] ∧
  TypeT ∉ firstSet cmlG [NN nConstructorName] ∧
  UnderbarT ∉ firstSet cmlG [NN nConstructorName] ∧
  ValT ∉ firstSet cmlG [NN nConstructorName] ∧
  WordT w ∉ firstSet cmlG [NN nConstructorName]
Proof
  simp[firstSet_nConstructorName]
QED

Theorem firstSets_nV_nConstructorName:
   ¬(t ∈ firstSet cmlG [NN nConstructorName] ∧ t ∈ firstSet cmlG [NN nV])
Proof
  Cases_on `t ∈ firstSet cmlG [NN nV]` >> simp[] >>
  fs[firstSet_nV, firstSet_nConstructorName]
QED

val _ = export_theory();
