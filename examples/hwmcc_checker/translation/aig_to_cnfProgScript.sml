(*
  Translates xaig_to_cnf (and its dependencies on xaig).
*)
Theory aig_to_cnfProg
Ancestors
  ml_translator  (* MEMBER_INTRO *)
  aig_cert_encodeProg xaig_to_cnf aig_to_cnf
Libs
  preamble ml_translatorLib MapProgLib

val _ = translation_extends "aig_cert_encodeProg";

(* The lowering keys finite maps by the gate, input and latch names of the
   circuit it is given, and every circuit reaching it is named by num. *)
val _ = add_fmap_for_cmp miscTheory.TotOrd_num_cmp;

(* The xaig definitions name the gate, input and latch type variables
   'a, 'i and 'l. *)
val to_num =
  INST_TYPE [alpha |-> “:num”, mk_vartype "'i" |-> “:num”,
             mk_vartype "'l" |-> “:num”];

(*----------------------------------------------------------------------*
   the parsed circuit: xor/ite detection
 *----------------------------------------------------------------------*)

val r = translate (xaig_to_cnfTheory.match_xor_def |> to_num);
val r = translate (xaig_to_cnfTheory.match_ite_def |> to_num);
val r = translate (xaig_to_cnfTheory.optimize_gate_def |> to_num);
val r = translate (xaig_to_cnfTheory.add_and_def |> to_num);
val r = translate (xaig_to_cnfTheory.xaig_opt_rev_def |> to_num);

(*----------------------------------------------------------------------*
   the lowering to CNF
 *----------------------------------------------------------------------*)

val r = translate cnfTheory.negate_def;

val r = translate xaig_to_cnfTheory.xvar_to_num_def;
val r = translate xaig_to_cnfTheory.xvar_to_lit_def;
val r = translate xaig_to_cnfTheory.eq_every_pos_def;
val r = translate xaig_to_cnfTheory.eq_every_neg_def;
val r = translate xaig_to_cnfTheory.or_every_pos_def;
val r = translate xaig_to_cnfTheory.or_every_neg_def;
val r = translate xaig_to_cnfTheory.xor_pos_def;
val r = translate xaig_to_cnfTheory.xor_neg_def;
val r = translate xaig_to_cnfTheory.ite_pos_def;
val r = translate xaig_to_cnfTheory.ite_neg_def;
val r = translate xaig_to_cnfTheory.gty_pos_def;
val r = translate xaig_to_cnfTheory.gty_neg_def;
val r = translate xaig_to_cnfTheory.xgty_to_cnf_def;

(* The polarity map is keyed by the renamed gate names; neither definition
   mentions a literal, so nothing in them pins the key type down. *)
val r = translate (xaig_to_cnfTheory.pol_of_def |> to_num);
val r = translate xaig_to_cnfTheory.flip_pol_def;
val r = translate (xaig_to_cnfTheory.add_pol_def |> to_num);
val r = translate xaig_to_cnfTheory.add_lit_pol_def;
val r = translate xaig_to_cnfTheory.gty_pols_def;
val r = translate xaig_to_cnfTheory.add_lits_pol_def;
val r = translate xaig_to_cnfTheory.add_gty_pol_def;
val r = translate xaig_to_cnfTheory.xto_cnf_def;
val r = translate xaig_to_cnfTheory.direct_xaig_to_cnf_def;

(*----------------------------------------------------------------------*
   pruning and renaming a circuit
 *----------------------------------------------------------------------*)

val r = translate (xaig_to_cnfTheory.gty_lits_def |> to_num);
val r = translate (aig_to_cnfTheory.new_live_def |> to_num);
val r = translate (xaig_to_cnfTheory.xprune_rev_def |> to_num);
val r = translate (xaig_to_cnfTheory.xprune_for_def |> to_num);
val r = translate (xaig_to_cnfTheory.xrename_lit_def |> to_num);
val r = translate (xaig_to_cnfTheory.xrename_lits_def |> to_num);
val r = translate (xaig_to_cnfTheory.xrename_gty_def |> to_num);
val r = translate (xaig_to_cnfTheory.xaig_rename_rev_def |> to_num);
val r = translate (xaig_to_cnfTheory.xaig_to_cnf_def |> to_num);
