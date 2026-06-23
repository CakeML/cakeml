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

(* By instantiating the types, the translator should translate finite maps
   with something more efficient than alists, assuming aig_fmapsProgScript.sml
   contains the appropriate comparison functions.

   The general type for circuits is ('α, 'β, 'γ) circuit.
 *)

(*
  For encode_is_witness_reset
*)
val i = INST_TYPE
          [alpha |-> “:(num + num) iext”,
           beta  |-> “:num”,
           gamma |-> “:num”]
val r = translate_rest i;

(*
  For encode_is_witness_transition
*)
val i = INST_TYPE
          [alpha |-> “:((num + num) iext + (num + num) iext) iext”,
           beta  |-> “:num + num”,
           gamma |-> “:num + num”]
val r = translate_rest i;

(*
  For encode_is_witness_property
*)
val i = INST_TYPE
          [alpha |-> “:(num + num) iext”,
           beta  |-> “:num”,
           gamma |-> “:num”]
val r = translate_rest i;

(*
  For encode_is_witness_base
*)
val i = INST_TYPE
          [alpha |-> “:num iext”,
           beta  |-> “:num”,
           gamma |-> “:num”]
val r = translate_rest i;

(*
  For encode_is_witness_step
*)
val i = INST_TYPE
          [alpha |-> “:(num iext + num iext) iext”,
           beta  |-> “:num + num”,
           gamma |-> “:num + num”]
val r = translate_rest i;

(*
  For encode_is_witness_liveness
*)
val i = INST_TYPE
          [alpha |-> “:(((num + num) iext + (num + num) iext) iext + (num + num) iext) iext”,
           beta  |-> “:num + num”,
           gamma |-> “:num + num”]
val r = translate_rest i;

(*
  For encode_is_witness_decrease
*)
val i = INST_TYPE
          [alpha |-> “:((num iext + num iext) iext + num iext) iext”,
           beta  |-> “:num + num”,
           gamma |-> “:num + num”]
val r = translate_rest i;

(*
  For encode_is_witness_closure
*)
val i = INST_TYPE
          [alpha |-> “:((((num iext + num iext) iext + num iext) iext + num iext) iext + num iext) iext”,
           beta  |-> “:(num + num) + num”,
           gamma |-> “: (num + num) + num”]
val r = translate_rest i;


(*
  For encode_is_witness_consistent
*)
val i = INST_TYPE
          [alpha |-> “:(((num iext + num iext) iext + num iext) iext + (num + num) iext) iext”,
           beta  |-> “:(num + num) + num”,
           gamma |-> “: (num + num) + num”]
val r = translate_rest i;
