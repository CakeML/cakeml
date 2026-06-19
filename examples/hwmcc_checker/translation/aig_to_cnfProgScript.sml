(*
  Translates aig_to_cnf (and its dependencies on cnf).
*)
Theory aig_to_cnfProg
Ancestors
  ml_translator  (* MEMBER_INTRO *)
  aig_fmapsProg aig_to_cnf
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_fmapsProg";

val r = translate aig_to_cnfTheory.negate_def;
val r = translate aig_to_cnfTheory.eq_every_to_cnf_def;
val r = translate aig_to_cnfTheory.not_TT_def;
val r = translate aig_to_cnfTheory.var_to_name_def;
val r = translate aig_to_cnfTheory.var_to_lit_def;
val r = translate (aig_to_cnfTheory.and_to_cnf_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate aig_to_cnfTheory.to_cnf_def;
val r = translate aig_to_cnfTheory.direct_circuit_to_cnf_def;

fun translate_rest i = let
  val r = translate (aig_to_cnfTheory.new_live_def |> i)
  val r = translate (aig_to_cnfTheory.prune_rev_def |> i)
  val r = translate (aig_to_cnfTheory.prune_for_def |> i)
  val r = translate (aig_to_cnfTheory.aig_rename_aux_def |> i)
  val r = translate (aig_to_cnfTheory.aig_rename_rev_def |> i)
  val r = translate (aig_to_cnfTheory.aig_to_cnf_def |> i)
  in r end

(*
  ((num + num) iext, num, num) circuit
*)
val i = INST_TYPE
          [alpha |-> “:(num + num) iext”,
           beta  |-> “:num”,
           gamma |-> “:num”]
val r = translate_rest i;

(*
  (((num + num) iext + (num + num) iext) iext, num + num, num + num) circuit
*)
val i = INST_TYPE
          [alpha |-> “:((num + num) iext + (num + num) iext) iext”,
           beta  |-> “:num + num”,
           gamma |-> “:num + num”]
val r = translate_rest i;

(*
  ((num + num) iext, num, num) circuit
*)
val i = INST_TYPE
          [alpha |-> “:(num + num) iext”,
           beta  |-> “:num”,
           gamma |-> “:num”]
val r = translate_rest i;

(*
  (num iext, num, num) circuit
*)
val i = INST_TYPE
          [alpha |-> “:num iext”,
           beta  |-> “:num”,
           gamma |-> “:num”]
val r = translate_rest i;

(*
  ((num iext + num iext) iext, num + num, num + num) circuit
*)
val i = INST_TYPE
          [alpha |-> “:(num iext + num iext) iext”,
           beta  |-> “:num + num”,
           gamma |-> “:num + num”]
val r = translate_rest i;
