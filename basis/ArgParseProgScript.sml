(*
  Module for parsing flags given as command-line arguments.
*)
open preamble ml_translatorLib ml_progLib TextIOProgTheory
     ArgParseTheory;

val _ = new_theory"ArgParseProg";

val _ = translation_extends "TextIO";

val _ = ml_prog_update (open_module "ArgParse");

val () = generate_sigs := true;

val r = translate OPTION_CHOICE_def;
val r = translate get_long_def;

Theorem get_long_side:
  get_long_side x
Proof
  rw [fetch "-" "get_long_side_def"]
QED

val _ = update_precondition get_long_side;

val r = translate get_short_def;

Theorem get_short_side:
  get_short_side x
Proof
  rw [fetch "-" "get_short_side_def"]
QED

val _ = update_precondition get_short_side;

val r = translate is_ident_def;
val r = translate get_option_def;

val r = translate parse_arg_def;
val r = translate parse_args_aux_def;
val r = translate parse_args_def;
val r = translate expandArgs_def;
val r = translate parse_def;

val r = translate isFlag_def;
val r = translate destOption_def;
val r = translate showFlag_def;
val r = translate getFlagName_def;

val _ = register_type ``:'a flagConf``;
val r = translate matchArg_def;

Theorem mkArgsConf_ind =
  REWRITE_RULE [GSYM mllistTheory.drop_def] mkArgsConf_ind;

Theorem mkArgsConf_def =
  REWRITE_RULE [GSYM mllistTheory.drop_def] mkArgsConf_def;

val _ = add_preferred_thy"-";
val r = translate mkArgsConf_def;

val sigs = module_signatures [
  "mkArgsConf",
  "parse"
];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory()

