structure miscLib = struct
open HolKernel boolLib bossLib lcsymtacs
fun RATOR_X_ASSUM t ttac (g as (asl,w)) = UNDISCH_THEN (first (can (match_term t) o fst o strip_comb) asl) ttac g
fun rator_x_assum q ttac = Q_TAC (C RATOR_X_ASSUM ttac) q
fun RATOR_ASSUM t ttac (g as (asl,w)) = ttac (ASSUME (first (can (match_term t) o fst o strip_comb) asl)) g
fun rator_assum q ttac = Q_TAC (C RATOR_ASSUM ttac) q
val rev_assum_list = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC)
fun last_x_assum x = rev_assum_list >> first_x_assum x >> rev_assum_list
fun qx_choosel_then [] ttac = ttac
  | qx_choosel_then (q::qs) ttac = Q.X_CHOOSE_THEN q (qx_choosel_then qs ttac)
val discharge_hyps =
  qmatch_abbrev_tac`(P⇒Q)⇒R` >>
  Q.SUBGOAL_THEN`P`
    (fn P => disch_then (mp_tac o PROVE_HYP P o UNDISCH) >> map_every qunabbrev_tac[`P`,`Q`,`R`]) >|
  [map_every qunabbrev_tac[`P`,`Q`,`R`],ALL_TAC]
end
