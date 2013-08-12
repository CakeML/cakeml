structure miscLib = struct
open HolKernel boolLib bossLib lcsymtacs
val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0
fun RATOR_X_ASSUM t ttac (g as (asl,w)) = UNDISCH_THEN (first (can (match_term t) o fst o strip_comb) asl) ttac g
fun rator_x_assum q ttac = Q_TAC (C RATOR_X_ASSUM ttac) q
fun RATOR_ASSUM t ttac (g as (asl,w)) = ttac (ASSUME (first (can (match_term t) o fst o strip_comb) asl)) g
fun rator_assum q ttac = Q_TAC (C RATOR_ASSUM ttac) q
val IMP_IMP = METIS_PROVE[]``(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)``
val discharge_hyps = match_mp_tac IMP_IMP >> conj_tac
fun prove_hyps_by tac th = PROVE_HYP (prove(list_mk_conj (hyp th),tac)) th
end
