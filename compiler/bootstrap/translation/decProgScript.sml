(*
  Translation of CakeML source AST
*)

open preamble astTheory semanticPrimitivesTheory;
open ml_translatorLib ml_translatorTheory ml_progLib;
open repl_init_envProgTheory;

val _ = new_theory "decProg";

val _ = set_grammar_ancestry ["ast","ml_translator","ml_pmatch"];

val _ = translation_extends "repl_init_envProg";

val _ = use_string_type true;

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
val _ = register_type ``:opn``;
val _ = register_type ``:opb``;
val _ = register_type ``:opw``;
val _ = register_type ``:shift``;
val _ = register_type ``:word_size``;
val _ = register_type ``:fp_uop``;
val _ = register_type ``:fp_bop``;
val _ = register_type ``:fp_top``;
val _ = register_type ``:fp_cmp``;
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

val _ = export_theory();
