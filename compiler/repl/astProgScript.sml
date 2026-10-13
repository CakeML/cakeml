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

(* Preserve the actual incoming program for initialization decomposition. *)
val ast_prefix_state = get_ml_prog_state () |> remove_snocs;
val ast_prefix = get_prog ast_prefix_state;

Definition ast_prefix_prog_def:
  ast_prefix_prog = ^ast_prefix
End

Theorem Decls_ast_prefix = get_Decls_thm ast_prefix_state
  |> REWRITE_RULE [GSYM ast_prefix_prog_def];

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

Definition ast_type_decs_def:
  ast_type_decs = ^ast_decs
End

val _ = ml_prog_update (addPrettyPrintersLib.add_pps
          (addPrettyPrintersLib.pps_of_global_tys ast_decs));

val _ = ml_prog_update (close_module NONE);

(* Partitions of the generated Ast module, used to stage its initialization. *)
val ast_state = get_ml_prog_state () |> remove_snocs;
val ast_prog_tm = get_prog ast_state;
val ast_module_body = ast_prog_tm |> listSyntax.dest_list |> fst |> last
  |> rand |> listSyntax.dest_list |> fst;
val ast_pp_decs = List.drop (ast_module_body,
  ast_decs |> listSyntax.dest_list |> fst |> length);

Definition ast_pp_decs_def:
  ast_pp_decs = ^(listSyntax.mk_list (ast_pp_decs, ``:ast$dec``))
End

Definition ast_prog_def:
  ast_prog = ^ast_prog_tm
End

Theorem ast_prog_partition =
  ``ast_prog = ast_prefix_prog ++
      [Dmod «Ast» (ast_type_decs ++ ast_pp_decs)]``
  |> PURE_REWRITE_CONV [ast_prog_def, ast_prefix_prog_def,
       ast_type_decs_def, ast_pp_decs_def, APPEND, REFL_CLAUSE]
  |> EQT_ELIM;

Theorem Decls_ast_prog = get_Decls_thm ast_state
  |> REWRITE_RULE [GSYM ast_prog_def];
