(*
  Translation of CakeML source AST
*)
Theory decProg
Ancestors
  ast ml_translator ml_pmatch[qualified] semanticPrimitives
  repl_init_envProg ast_extras
Libs
  preamble ml_translatorLib ml_progLib

open preamble astTheory semanticPrimitivesTheory;
open ml_translatorLib ml_translatorTheory ml_progLib;
open repl_init_envProgTheory;

val _ = translation_extends "repl_init_envProg";

(* this is a hack to make the translator avoid these names *)
Datatype:
  dummy = Tyvar | Tyapp | Var | Const | Abs | Comb | Sequent
End
val _ = register_type ``:dummy``;
(* end of hack *)

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
val _ = register_type ``:locn``;
val _ = register_type ``:locs``;
val _ = register_type ``:exp``;
val _ = register_type ``:dec``;

Theorem IsTypeRep_LIST_v = fetch_v_fun “:'a list” |> snd |> hd;

Theorem IsTypeRep_AST_DEC_v:
  IsTypeRep AST_DEC_v AST_DEC_TYPE
Proof
  irule_at Any (fetch_v_fun “:ast$dec” |> snd |> hd)
  \\ irule_at Any (fetch_v_fun “:'a list” |> snd |> hd)
  \\ rpt (irule_at Any (fetch_v_fun “:ast$exp” |> snd |> hd))
  \\ rpt (irule_at Any (fetch_v_fun “:'a # 'b” |> snd |> hd))
  \\ rpt (irule_at Any (fetch_v_fun “:ast$exp” |> snd |> hd))
  \\ rpt (irule_at Any (fetch_v_fun “:ast$pat” |> snd |> hd))
  \\ rpt (irule_at Any (fetch_v_fun “:ast$lit” |> snd |> hd))
  \\ rpt (irule_at Any (fetch_v_fun “:word8” |> snd |> hd))
  \\ rpt (irule_at Any (fetch_v_fun “:word64” |> snd |> hd))
  \\ rpt (irule_at Any (fetch_v_fun “:string” |> snd |> hd))
  \\ rpt (irule_at Any (fetch_v_fun “:mlstring” |> snd |> hd))
  \\ fs []
QED

Theorem EqualityType_AST_DEC_TYPE =
  EqualityType_rule [] “:dec”;

Theorem EqualityType_LIST_TYPE_AST_DEC_TYPE =
  EqualityType_rule [] “:dec list”;

val r = translate ast_extrasTheory.every_exp_def;
val r = translate ast_extrasTheory.every_dec_def;
val r = translate namespaceTheory.id_to_n_def;
val r = translate repl_decs_allowedTheory.safe_exp_pmatch;
val r = translate candle_prover_invTheory.safe_dec_def;
val r = translate repl_decs_allowedTheory.decs_allowed_def;
