
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_primality_test";

open miller_rabinTheory;
open arithmeticTheory;
open combinTheory;

open ml_translatorLib;

fun find_def tm = let
  val thy = #Thy (dest_thy_const tm)
  val name = #Name (dest_thy_const tm)
  in fetch thy (name ^ "_def") handle HOL_ERR _ =>
     fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
     fetch thy (name)
  end

(* Miller-Rabin -- has higher-order functions and `MOD n` *)

val res = translate EVEN_MOD2;

val _ = translate (find_def ``UNIT``);
val BIND_def = find_def ``BIND``;
val _ = translate (SIMP_RULE std_ss [FUN_EQ_THM] BIND_def);

val prob_while_cut_def = find_def ``prob_while_cut``;
val _ = translate prob_while_cut_def;

val _ = translate K_DEF;
val _ = translate I_THM;
val many_def = find_def ``many``;
val _ = translate many_def;

val log2_def = find_def ``log2``;
val _ = translate log2_def;

val factor_twos_def = find_def ``factor_twos``;
val _ = translate factor_twos_def;

val def = find_def ``modexp``;
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


val _ = export_theory();

