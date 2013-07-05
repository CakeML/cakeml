structure parsingPreamble :> parsingPreamble =
struct

open HolKernel boolLib lcsymtacs bossLib boolSimps
val MAP_EQ_SING = grammarTheory.MAP_EQ_SING
val MAP_EQ_APPEND = grammarTheory.MAP_EQ_APPEND
val APPEND_ASSOC = listTheory.APPEND_ASSOC

val FDOM_cmlPEG = mmlPEGTheory.FDOM_cmlPEG
val mmlpeg_rules_applied = mmlPEGTheory.mmlpeg_rules_applied

fun loseC c =
    first_x_assum
      (K ALL_TAC o assert (can (find_term (same_const c)) o concl))
fun asm_match q = Q.MATCH_ASSUM_RENAME_TAC q []

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

fun dsimp thl = asm_simp_tac (srw_ss() ++ DNF_ss) thl
fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl
fun csimp thl = asm_simp_tac (srw_ss() ++ CONJ_ss) thl

val kill_asm_guard =
    disch_then (fn th => SUBGOAL_THEN (lhand (concl th))
                                      (MP_TAC o MATCH_MP th)) >- asimp[]

fun qispl_then [] ttac = ttac
  | qispl_then (q::qs) ttac = Q.ISPEC_THEN q (qispl_then qs ttac)
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = Q.X_CHOOSE_THEN q (qxchl qs ttac)
val rveq = rpt BasicProvers.VAR_EQ_TAC

fun erule k th = let
  fun c th = let
    val (vs, body) = strip_forall (concl th)
  in
    if is_imp body then
      first_assum (c o MATCH_MP th) ORELSE
      first_assum (c o MATCH_MP th o SYM)
    else k th
  end
  fun is_resolvable th = let
    val (vs, body) = strip_forall (concl th)
  in
    is_imp body
  end
in
  if is_resolvable th then c th else NO_TAC
end

fun print_tac s (g as (asl,w)) = let
  fun mmlnt_test t = is_const t andalso type_of t = ``:MMLnonT``
in
  case get_first (Lib.total (find_term mmlnt_test)) asl of
      NONE => raise Fail "No MMLnonT in goal"
    | SOME t => if term_to_string t = s then
                  (print ("print_tac: "^s^"\n"); ALL_TAC g)
                else raise Fail ("MMLnonT not "^s)
end



end
