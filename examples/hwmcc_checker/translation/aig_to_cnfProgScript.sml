(*
  Translates xaig_to_cnf (and its dependencies on xaig).
*)
Theory aig_to_cnfProg
Ancestors
  ml_translator  (* MEMBER_INTRO *)
  aig_fmapsProg xaig_to_cnf aig_to_cnf
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_fmapsProg";

(* The xaig definitions name the gate, input and latch type variables
   'a, 'i and 'l. *)
fun xinst (a, b, c) =
  INST_TYPE [alpha |-> a, mk_vartype "'i" |-> b, mk_vartype "'l" |-> c];

val nnn = xinst (“:num”, “:num”, “:num”);

(*----------------------------------------------------------------------*
   the parsed circuit: xor/ite detection
 *----------------------------------------------------------------------*)

val r = translate (xaig_to_cnfTheory.match_xor_def |> nnn);
val r = translate (xaig_to_cnfTheory.match_ite_def |> nnn);
val r = translate (xaig_to_cnfTheory.optimize_gate_def |> nnn);
val r = translate (xaig_to_cnfTheory.add_and_def |> nnn);
val r = translate (xaig_to_cnfTheory.xaig_opt_rev_def |> nnn);

(*----------------------------------------------------------------------*
   the lowering to CNF

   Renaming hands out num names, so everything from here on is monomorphic
   whatever the encoded condition was named by.
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
val to_num = INST_TYPE [alpha |-> “:num”];

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
   pruning and renaming an encoded condition

   One instance per gate name type of the nine conditions; reset and safety
   share one, as do closure and stable.
 *----------------------------------------------------------------------*)

fun translate_rest i = let
  val r = translate (xaig_to_cnfTheory.gty_lits_def |> i)
  val r = translate (aig_to_cnfTheory.new_live_def |> i)
  val r = translate (xaig_to_cnfTheory.xprune_rev_def |> i)
  val r = translate (xaig_to_cnfTheory.xprune_for_def |> i)
  val r = translate (xaig_to_cnfTheory.xrename_lit_def |> i)
  val r = translate (xaig_to_cnfTheory.xrename_lits_def |> i)
  val r = translate (xaig_to_cnfTheory.xrename_gty_def |> i)
  val r = translate (xaig_to_cnfTheory.xaig_rename_rev_def |> i)
  val r = translate (xaig_to_cnfTheory.xaig_to_cnf_def |> i)
  in r end

(* the parsed circuits *)
val r = translate_rest nnn;

(* reset, safety *)
val r = translate_rest (xinst (“:(num + num) ext”, “:num”, “:num”));

(* transition *)
val r = translate_rest
  (xinst (“:((num + num) + (num + num)) ext”, “:num + num”, “:num + num”));

(* base *)
val r = translate_rest (xinst (“:num ext”, “:num”, “:num”));

(* induction *)
val r = translate_rest
  (xinst (“:(num + num) ext”, “:num + num”, “:num + num”));

(* liveness *)
val r = translate_rest
  (xinst (“:(((num + num) + (num + num)) + (num + num)) ext”,
          “:num + num”, “:num + num”));

(* decrease *)
val r = translate_rest
  (xinst (“:((num + num) + num) ext”, “:num + num”, “:num + num”));

(* closure, stable *)
val r = translate_rest
  (xinst (“:(((num + num) + num) + (num + num)) ext”,
          “:(num + num) + num”, “:(num + num) + num”));
