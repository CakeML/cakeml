(*
  Translation of CakeML source AST
*)

open preamble astTheory semanticPrimitivesTheory;
open ml_translatorLib ml_translatorTheory ml_progLib;
open repl_init_envProgTheory;

val _ = new_theory "decProg";

val _ = translation_extends "repl_init_envProg";

val _ = use_string_type true;

val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
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

val _ = export_theory();
