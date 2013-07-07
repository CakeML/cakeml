open HolKernel Parse boolLib bossLib;
open lcsymtacs parsingPreamble

val _ = new_theory "conversionProps";


(*




val TypeName_OK = store_thm(
  "TypeName_OK",
  ``valid_ptree mmlG pt ∧ ptree_head pt = NT (mkNT nTypeName) ∧
    MAP TOK toks = ptree_fringe pt ⇒
    ∃tn. ptree_TypeName pt = SOME tn``,
  Cases_on `pt` >> simp[grammarTheory.MAP_EQ_SING]
  >- (rw[] >> fs[]) >>
  simp[

*)

val _ = export_theory();
