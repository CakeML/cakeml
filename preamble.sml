structure preamble =
struct
local open intLib wordsLib in end
open HolKernel bossLib boolLib boolSimps pairLib lcsymtacs
     Parse Defn Tactic res_quanTheory
     pairTheory optionTheory sumTheory combinTheory
     listTheory rich_listTheory alistTheory llistTheory
     arithmeticTheory finite_mapTheory sptreeTheory
     pred_setTheory set_relationTheory relationTheory
     sortingTheory stringTheory wordsTheory
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;
val var_eq_tac = BasicProvers.VAR_EQ_TAC;
open miscTheory
open miscLib (* TODO: inline *)
end
