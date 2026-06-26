(*
  Translates aig_parse.
*)
Theory aig_parseProg
Ancestors
  errorMonad sptree
  aig_parse aigProg
Libs
  preamble ml_translatorLib MapProgLib

val _ = translation_extends "aigProg";

fun demonadify thm = SRULE [oneline bind_def, guard_def, UNCURRY] thm;

val r = register_type “:('a, 'e) error”;
val r = register_type “:'a sptree$num_map”;

val r = register_type “:counts”;
val r = register_type “:aiger”;
val r = register_type “:maps”;

val r = translate aig_parseTheory.is_char_def;
val r = translate aig_parseTheory.consume_space_def;
val r = translate aig_parseTheory.consume_line_def;
val r = translate aig_parseTheory.expect_char_def;

val r = translate stringTheory.isDigit_def;

val r = translate aig_parseTheory.parse_number_aux_def;
val parse_number_aux_side_def = theorem "parse_number_aux_side_def";
Theorem parse_number_aux_side[local]:
  ∀s i acc. parse_number_aux_side s i acc
Proof
  Induct_on ‘strlen s - i’
  >> rw [Once parse_number_aux_side_def, isDigit_def]
QED
val r = update_precondition parse_number_aux_side;

val r = translate aig_parseTheory.parse_number_def;
val parse_number_side_def = definition "parse_number_side_def";
Theorem parse_number_side[local]:
  parse_number_side s i
Proof
  simp [parse_number_side_def, isDigit_def]
QED
val r = update_precondition parse_number_side;

val r = translate (aig_parseTheory.parse_numbers_aux_def |> demonadify);
val r = translate aig_parseTheory.parse_numbers_def;

val r = translate aig_parseTheory.parse_opt_number_def;

val r = translate aig_parseTheory.parse_leb_aux_def;
val r = translate aig_parseTheory.parse_leb_def;

val r = translate (aig_parseTheory.parse_counts_def |> demonadify);

val r = translate aig_parseTheory.convert_lit_def;

val r = translate (aig_parseTheory.parse_lit_def |> demonadify);

val r = translate (aig_parseTheory.parse_literals_aux_def |> demonadify);
val r = translate aig_parseTheory.parse_literals_def;

val r = translate (aig_parseTheory.parse_justices_aux_def |> demonadify);
val r = translate (aig_parseTheory.parse_justices_def |> demonadify);

val r = translate (aig_parseTheory.parse_latches_aux_def |> demonadify);
val r = translate aig_parseTheory.parse_latches_def;

val _ = use_sub_check true;
val r = translate (aig_parseTheory.parse_ands_aux_def |> demonadify);
val _ = use_sub_check false;

val r = translate aig_parseTheory.parse_ands_def;

val r = translate (aig_parseTheory.parse_aiger_def |> demonadify);

val r = translate sptreeTheory.insert_def;
val r = translate aig_parseTheory.insert_if_def;

val r = translate (aig_parseTheory.parse_entry_def |> demonadify);
val r = translate aig_parseTheory.parse_symbol_table_aux_def;
val r = translate (aig_parseTheory.parse_symbol_table_def |> demonadify);

val r = translate (aig_parseTheory.parse_aiger_and_symbols_def |> demonadify);

val r = translate sptreeTheory.lookup_def;
val r = translate sptreeTheory.fromAList_def;

val r = translate aig_parseTheory.default_shared_def;
val r = translate aig_parseTheory.shared_lit_def;
val r = translate aig_parseTheory.shared_latch_key_def;
val r = translate aig_parseTheory.shared_latch_map_def;
val r = translate aig_parseTheory.shared_latches_def;
val r = translate aig_parseTheory.shared_circuit_def;

val r = translate sptreeTheory.lrnext_def;
val r = translate sptreeTheory.foldi_def;

(* make_interv returns a finite_map; we want to make sure it gets translated
   to something efficient. *)

Type num_bvar[local] = “:(num, num) bvar”
Type num_var[local] = “:(num, num, num) var”

Definition num_bvar_cmp_def:
  num_bvar_cmp (x1: num_bvar) (x2: num_bvar) =
    case x1 of
    | Ff =>
      (case x2 of
       | Ff => EQUAL
       | _  => LESS)
    | Input i1 =>
      (case x2 of
       | Ff => GREATER
       | Input i2 => num_cmp i1 i2
       | _  => LESS)
    | Latch l1 =>
      (case x2 of
       | Latch l2 => num_cmp l1 l2
       | _ => GREATER)
End

Definition num_var_cmp_def:
  num_var_cmp (x1: num_var) (x2: num_var) =
    case x1 of
    | Name n1 =>
      (case x2 of
       | Name n2 => num_cmp n1 n2
       | _ => LESS)
    | Base b1 =>
      (case x2 of
       | Name _ => GREATER
       | Base b2 => num_bvar_cmp b1 b2)
End

Theorem num_bvar_cmp_eq[local] =
  num_bvar_cmp_def |> SRULE [num_cmp_def]

Theorem num_var_cmp_eq[local] =
  num_var_cmp_def |> SRULE [num_cmp_def, num_bvar_cmp_def]

Theorem TotOrd_num_var:
  TotOrd (num_var_cmp : num_var -> num_var -> ordering)
Proof
  rw [totoTheory.TotOrd, num_var_cmp_def, num_bvar_cmp_def, num_cmp_def]
  >> every_case_tac >> fs []
QED

val r = translate num_cmp_def;
val r = translate num_bvar_cmp_eq;
val r = translate num_var_cmp_eq;

val r = add_fmap_for_cmp TotOrd_num_var;

val r = translate FOLDL;
val r = translate aig_parseTheory.make_interv_def;
