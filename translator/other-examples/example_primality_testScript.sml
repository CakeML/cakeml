(*
  This is a simple example of applying the translator to an
  efficient primality tester formalised by Joe Hurd.
*)
Theory example_primality_test
Ancestors
  miller_rabin arithmetic combin ListProg
Libs
  ml_translatorLib

fun find_def tm = let
  val thy = #Thy (dest_thy_const tm)
  val name = #Name (dest_thy_const tm)
  in fetch thy (name ^ "_def") handle HOL_ERR _ =>
     fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
     fetch thy (name)
  end

(* Miller-Rabin -- has higher-order functions and `MOD n` *)

val _ = translation_extends "ListProg";

val res = translate EVEN_MOD2;

Theorem UNIT_thm[local]:
  UNIT x s = (x,s)
Proof
  FULL_SIMP_TAC std_ss [state_transformerTheory.UNIT_DEF]
QED

val _ = translate UNIT_thm;

val def = find_def ``BIND``;
val _ = translate (SIMP_RULE std_ss [FUN_EQ_THM] def);

Theorem lemma[local]:
  prob_while_cut c b n = \x. prob_while_cut c b n x
Proof
  SIMP_TAC std_ss [FUN_EQ_THM]
QED

val def = find_def ``prob_while_cut``
          |> ONCE_REWRITE_RULE [lemma] |> SIMP_RULE std_ss []
val _ = translate def;

val _ = translate K_DEF;
val _ = translate I_THM;

val def = find_def ``many``;
val _ = translate def;

val log2_def = find_def ``log2``;
val _ = translate log2_def;

val factor_twos_def = find_def ``factor_twos``;
val _ = translate factor_twos_def;

val def = find_def ``exp_mod_step``;
val _ = translate def;

val def = find_def ``exp_mod_binary``;
val _ = translate def;

val witness_tail_def = find_def ``witness_tail``;
val _ = translate witness_tail_def;

val def = find_def ``witness``;
val _ = translate def;

val def = find_def ``shd``;
val _ = translate def;

val def = find_def ``stl``;
val _ = translate def;

val def = find_def ``prob_unif``;
val _ = translate def;

val def = find_def ``prob_uniform_cut``;
val _ = translate def;

val _ = translate miller_rabin_1_def;

val _ = translate miller_rabin_def;

(* discharging the preconditions *)

Theorem exp_mod_step_side[local]:
  ∀b n k acc. k ≠ 0 ⇒ exp_mod_step_side b n k acc
Proof
  ho_match_mp_tac expModTheory.exp_mod_step_ind \\ rpt strip_tac
  \\ once_rewrite_tac [fetch "-" "exp_mod_step_side_def"]
  \\ Cases_on ‘k’ \\ Cases_on ‘n’ \\ gvs []
QED

Theorem witness_tail_side[local]:
  ∀r n a. 0 < n ⇒ witness_tail_side n a r
Proof
  Induct \\ once_rewrite_tac [fetch "-" "witness_tail_side_def"] \\ gvs []
QED

Theorem witness_side[local]:
  ∀n a. 0 < n ⇒ witness_side n a
Proof
  rw [fetch "-" "witness_side_def", fetch "-" "exp_mod_binary_side_def",
      exp_mod_step_side, witness_tail_side]
QED

Theorem prob_uniform_cut_side[local]:
  ∀t n s. 0 < n ⇒ prob_uniform_cut_side t n s
Proof
  Induct \\ once_rewrite_tac [fetch "-" "prob_uniform_cut_side_def"]
  \\ Cases_on ‘n’ \\ gvs [] \\ rpt (pairarg_tac \\ gvs [])
QED

Theorem miller_rabin_1_side[local]:
  ∀n s. miller_rabin_1_side n s ⇔ T
Proof
  rw [fetch "-" "miller_rabin_1_side_def"]
  \\ ‘n ≠ 0’ by (strip_tac \\ gvs [])
  \\ gvs [witness_side, prob_uniform_cut_side]
QED

val _ = update_precondition miller_rabin_1_side;

Theorem miller_rabin_side[local]:
  ∀n s. miller_rabin_side n s ⇔ T
Proof
  rw [fetch "-" "miller_rabin_side_def", miller_rabin_1_side]
QED

val _ = update_precondition miller_rabin_side;

