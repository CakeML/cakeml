open HolKernel Parse boolLib bossLib

open lcsymtacs boolSimps
open gramTheory

open mmlvalidTheory

val dsimp = asm_simp_tac (srw_ss() ++ DNF_ss)

val MAP_EQ_SING = grammarTheory.MAP_EQ_SING

val _ = new_theory "gramProps"

val mmlvalid_not_INR = store_thm(
  "mmlvalid_not_INR",
  ``mmlvalid pt ∧ ptree_fringe pt = MAP TOK i ⇒ ptree_head pt ≠ NT (INR n)``,
  Cases_on `pt` >>
  dsimp[MAP_EQ_SING, mmlvalid_thm] >> rpt strip_tac >> rw[] >>
  fs[mml_okrule_eval_th])

val NT_rank_def = Define`
  NT_rank N =
    case N of
      | INR _ => 0n
      | INL n =>
        if n = nElist1                 then 15
        else if n = nE                 then 14
        else if n = nEhandle           then 13
        else if n = nElogicOR          then 12
        else if n = nElogicAND         then 11
        else if n = nEtyped            then 10
        else if n = nEbefore           then  9
        else if n = nEcomp             then  8
        else if n = nErel              then  7
        else if n = nEadd              then  6
        else if n = nEmult             then  5
        else if n = nEapp              then  4
        else if n = nEbase             then  3
        else if n = nFQV               then  2
        else if n = nV                 then  1
        else if n = nVlist1            then  2
        else if n = nDtypeCons         then  3
        else if n = nDconstructor      then  2
        else if n = nConstructorName   then  2
        else if n = nUQConstructorName then  1
        else if n = nTypeList          then  5
        else if n = nType              then  4
        else if n = nStarTypesP        then  5
        else if n = nStarTypes         then  4
        else if n = nDType             then  3
        else if n = nTyOp              then  2
        else if n = nTypeName          then  2
        else if n = nUQTyOp            then  1
        else 0
`

(*
val unambiguous = store_thm(
  "unambiguous",
  ``∀i N p1 p2.
      valid_ptree mmlG p1 ∧ ptree_fringe p1 = MAP TOK i ∧
      ptree_head p1 = NT N ∧
      valid_ptree mmlG p2 ∧ ptree_fringe p2 = MAP TOK i ∧
      ptree_head p2 = NT N ⇒
      p1 = p2``,
  ntac 2 gen_tac >> `∃iN. iN = (i,N)` by simp[] >> pop_assum mp_tac >>
  map_every qid_spec_tac [`N`, `i`, `iN`] >>
  Q.ISPEC_THEN
    `measure (LENGTH:token list -> num) LEX measure (NT_rank: NT -> num)`
    (HO_MATCH_MP_TAC o SIMP_RULE (srw_ss()) [pairTheory.WF_LEX])
    relationTheory.WF_INDUCTION_THM >>
  dsimp[pairTheory.LEX_DEF, AND_IMP_INTRO, mmlvalid_SYM] >>
  rpt strip_tac >>
  `(∃x. N = INR x) ∨ ∃n. N = INL n` by (Cases_on `N` >> simp[])
  >- metis_tac[mmlvalid_not_INR] >> rw[] >>
  Cases_on `n`
  >- ((* nVlist1 *) Cases_on `p1` >> fs[MAP_EQ_SING] >> rw[] >>
      Cases_on `p2` >> fs[MAP_EQ_SING, mmlvalid_thm, mml_okrule_eval_th]
)

*)
val _ = export_theory()
