(*
  Module for the built-in double floating-point type.
  Defines basic arithmetic operations like +,-,*,/, and FMA,
  logical operations <, <=, >, >=, and =
  and to-/fromString functions for parsing and pretty-printing constants
*)
open preamble
     ml_translatorLib ml_progLib basisFunctionsLib
     wordsTheory
     CommandLineProgTheory;

val _ = new_theory"DoubleProg";

val _ = translation_extends "CommandLineProg";

(* Double module -- translated *)

val _ = ml_prog_update (open_module "Double");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "double" (Atapp [] (Short "word64"))`` I);

val _ = ml_prog_update open_local_block;

val concat_all_def = Define `
  concat_all (a:word8) b c d e f g h =
    concat_word_list [a;b;c;d;e;f;g;h]:64 word`

val concat_all_impl = REWRITE_RULE [concat_word_list_def, dimindex_8, ZERO_SHIFT, WORD_OR_CLAUSES] concat_all_def;

val _ = (next_ml_names := ["concat_all"]);
val _ = translate concat_all_impl;

val _ = ml_prog_update open_local_in_block;

val _ = process_topdecs
  `fun fromString s =
    let
      val iobuff = Word8Array.array 8 (Word8.fromInt 0);
      val _ = #(double_fromString) s iobuff;
      val a = Word8Array.sub iobuff 0;
      val b = Word8Array.sub iobuff 1;
      val c = Word8Array.sub iobuff 2;
      val d = Word8Array.sub iobuff 3;
      val e = Word8Array.sub iobuff 4;
      val f = Word8Array.sub iobuff 5;
      val g = Word8Array.sub iobuff 6;
      val h = Word8Array.sub iobuff 7;
    in
      concat_all a b c d e f g h
    end;` |> append_prog;

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update open_local_block;

val byte_0_def = Define `byte_0 (d:word64) = (w2w d):word8`;
val byte_1_def = Define `byte_1 (d:word64) = (w2w (d >>> 8)):word8`;
val byte_2_def = Define `byte_2 (d:word64) = (w2w (d >>> 16)):word8`;
val byte_3_def = Define `byte_3 (d:word64) = (w2w (d >>> 24)):word8`;
val byte_4_def = Define `byte_4 (d:word64) = (w2w (d >>> 32)):word8`;
val byte_5_def = Define `byte_5 (d:word64) = (w2w (d >>> 40)):word8`;
val byte_6_def = Define `byte_6 (d:word64) = (w2w (d >>> 48)):word8`;
val byte_7_def = Define `byte_7 (d:word64) = (w2w (d >>> 56)):word8`;

val _ = translate byte_0_def;
val _ = translate byte_1_def;
val _ = translate byte_2_def;
val _ = translate byte_3_def;
val _ = translate byte_4_def;
val _ = translate byte_5_def;
val _ = translate byte_6_def;
val _ = translate byte_7_def;

val is_0_byte_def = Define `
  is_0_byte (c:word8) = (c = n2w 0)`;

val _ = translate is_0_byte_def;

val _ = ml_prog_update open_local_in_block;

val _ = process_topdecs
  `fun toString d =
    let
      val iobuff = Word8Array.array (256) (Word8.fromInt 0);
      val _ = Word8Array.update iobuff 0 (byte_0 d);
      val _ = Word8Array.update iobuff 1 (byte_1 d);
      val _ = Word8Array.update iobuff 2 (byte_2 d);
      val _ = Word8Array.update iobuff 3 (byte_3 d);
      val _ = Word8Array.update iobuff 4 (byte_4 d);
      val _ = Word8Array.update iobuff 5 (byte_5 d);
      val _ = Word8Array.update iobuff 6 (byte_6 d);
      val _ = Word8Array.update iobuff 7 (byte_7 d);
      val _ = #(double_toString) "" iobuff;
      val n = fst (Option.valOf (Word8Array.findi is_0_byte iobuff));
    in
        Word8Array.substring iobuff 0 n
    end;` |> append_prog;

val _ = ml_prog_update close_local_blocks;

(* Ternary operations *)
val _ = trans "fma" ``fp64_mul_add roundTiesToEven``;

(* Binary operations *)
val _ = trans "+" ``fp64_add roundTiesToEven``;
val _ = trans "-" ``fp64_sub roundTiesToEven``;
val _ = trans "*" ``fp64_mul roundTiesToEven``;
val _ = trans "/" ``fp64_div roundTiesToEven``;
val _ = trans "<" ``fp64_lessThan``;
val _ = trans ">" ``fp64_greaterThan``;
val _ = trans "<=" ``fp64_lessEqual``;
val _ = trans ">=" ``fp64_greaterEqual``;
val _ = trans "=" ``fp64_equal``;

(* Unary operations *)
val _ = trans "abs" ``fp64_abs``;
val _ = trans "sqrt" ``fp64_sqrt roundTiesToEven``;
val _ = trans "~" ``fp64_negate``;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
