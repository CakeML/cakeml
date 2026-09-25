(*
  Translates the CakeML source AST types into an Ast module, with generated
  pretty-printers, so that they are part of the REPL's initial environment.
*)
Theory astProg
Ancestors
  ast ml_translator candle_kernelProg
Libs
  preamble ml_translatorLib ml_progLib addPrettyPrintersLib[qualified]

val _ = translation_extends "candle_kernelProg";

val _ = (use_full_type_names := false);

val _ = ml_prog_update (open_module "Ast");

val _ = register_type ``:lit``;
val _ = register_type ``:('a,'b) id``;
val _ = register_type ``:ast_t``;
val _ = register_type ``:pat``;
val _ = register_type ``:lop``;
val _ = register_type ``:shift``;
val _ = register_type ``:word_size``;
val _ = register_type ``:prim_type``;
val _ = register_type ``:arith``;
val _ = register_type ``:op``;
val _ = register_type ``:ast$locs``;
val _ = register_type ``:exp``;
val _ = register_type ``:dec``;

(* the declarations of the open Ast module block in the ML_code theorem *)
val ast_decs =
  get_ml_prog_state () |> remove_snocs |> get_thm |> concl |> strip_comb |> snd
  |> el 2 |> listSyntax.dest_list |> fst |> hd
  |> pairSyntax.dest_pair |> snd |> pairSyntax.strip_pair |> el 2;

val _ = ml_prog_update (addPrettyPrintersLib.add_pps
          (addPrettyPrintersLib.pps_of_global_tys ast_decs));

val _ = ml_prog_update (close_module NONE);
