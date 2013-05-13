structure miscLib = struct
open HolKernel boolLib bossLib lcsymtacs
val _ = set_trace"goalstack print goal at top"0
fun RATOR_X_ASSUM t ttac (g as (asl,w)) = UNDISCH_THEN (first (can (match_term t) o fst o strip_comb) asl) ttac g
fun rator_x_assum q ttac = Q_TAC (C RATOR_X_ASSUM ttac) q
fun RATOR_ASSUM t ttac (g as (asl,w)) = ttac (ASSUME (first (can (match_term t) o fst o strip_comb) asl)) g
fun rator_assum q ttac = Q_TAC (C RATOR_ASSUM ttac) q
val rev_assum_list = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC)
fun last_assum x = rev_assum_list >> first_assum x >> rev_assum_list
fun last_x_assum x = rev_assum_list >> first_x_assum x >> rev_assum_list
fun qx_choosel_then [] ttac = ttac
  | qx_choosel_then (q::qs) ttac = Q.X_CHOOSE_THEN q (qx_choosel_then qs ttac)
val discharge_hyps =
  let val P = genvar bool
      val Q = genvar bool
      val R = genvar bool
  in
  Q.MATCH_ABBREV_TAC`(^P⇒^Q)⇒^R` >>
  SUBGOAL_THEN P
    (fn th => disch_then (mp_tac o PROVE_HYP th o UNDISCH) >> map_every qunabbrev_tac[`^P`,`^Q`,`^R`]) >|
  [map_every qunabbrev_tac[`^P`,`^Q`,`^R`],ALL_TAC]
  end
fun prove_hyps_by tac th = PROVE_HYP (prove(list_mk_conj (hyp th),tac)) th
end
