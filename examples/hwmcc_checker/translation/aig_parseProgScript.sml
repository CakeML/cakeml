(*
  Translates aig_parse.
*)
Theory aig_parseProg
Ancestors
  errorMonad sptree
  aig_parse aigProg
Libs
  preamble ml_translatorLib

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
val r = translate aig_parseTheory.make_interv_def;
