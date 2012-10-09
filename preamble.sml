structure preamble =
struct
open HolKernel bossLib boolLib pairLib lcsymtacs
open Parse Defn Tactic res_quanTheory
open finite_mapTheory listTheory pairTheory pred_setTheory
open set_relationTheory sortingTheory stringTheory wordsTheory
open relationTheory
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;
end
