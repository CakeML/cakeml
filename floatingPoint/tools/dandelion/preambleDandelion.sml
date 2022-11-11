(**
   Proof tools (e.g. tactics) used throughout the development.
   Copied from CakeML (https://github.com/CakeML/cakeml)
**)
structure preambleDandelion =
struct
local open intLib in end;
open set_relationTheory; (* comes first so relationTheory takes precedence *)
open ASCIInumbersTheory BasicProvers Defn HolKernel Parse SatisfySimps Tactic
     monadsyntax alistTheory alignmentTheory arithmeticTheory bagTheory boolLib
     boolSimps bossLib containerTheory combinTheory dep_rewrite
     finite_mapTheory indexedListsTheory listTheory llistTheory (* lcsymtacs  *)
     markerLib mp_then optionTheory pairLib
     pairTheory pred_setTheory quantHeuristicsLib relationTheory res_quanTheory
     rich_listTheory sortingTheory sptreeTheory stringTheory sumTheory
     realTheory realLib RealArith transcTheory;

(* TOOD: move? *)
val wf_rel_tac = WF_REL_TAC
val sym_sub_tac = SUBST_ALL_TAC o SYM;
val match_exists_tac = part_match_exists_tac (hd o strip_conj)
val asm_exists_tac = first_assum(match_exists_tac o concl)
val cond_cases_tac = COND_CASES_TAC
val top_case_tac = TOP_CASE_TAC
val real_tac = rpt (qpat_x_assum ‘! x. _’ kall_tac) >> REAL_ASM_ARITH_TAC
val eq_tac = EQ_TAC
val eval_tac = EVAL_TAC
fun impl_subgoal_tac th =
  let
    val hyp_to_prove = lhand (concl th)
  in
    SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end;

fun real_prove_rw_tac (t:Q.tmquote) (rw:thm list -> tactic) =
  t by real_tac >> pop_assum $ rw o single

val real_rw = fn (t:Q.tmquote) => real_prove_rw_tac t rewrite_tac

val real_once_rw = fn (t:Q.tmquote) => real_prove_rw_tac t once_rewrite_tac

fun transitivity_for t =
  (irule REAL_LE_TRANS ORELSE irule REAL_LT_TRANS) >> qexists_tac t

fun mp_with_then tac t1 ith =
  qpat_assum t1 ( fn th => tac (MATCH_MP ith th));

fun mpx_with_then tac t1 ith =
  qpat_x_assum t1 ( fn th => tac (MATCH_MP ith th));

val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0

end;
