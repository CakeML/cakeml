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

val replaceMLneg_def = Define ‘replaceMLneg x = if x = #"~" then #"-" else x’;
val _ = translate replaceMLneg_def;

val prepareString_def = Define ‘prepareString (s:mlstring) = translate replaceMLneg s’
val _ = translate prepareString_def;

val _ = ml_prog_update open_local_in_block;

val _ = append_prog “[Dlet unknown_loc (Pvar "fromWord")
                        (Fun "v1" (App FpFromWord [Var (Short "v1")]))]”

val _ = append_prog “[Dlet unknown_loc (Pvar "toWord")
                        (Fun "v1" (App FpToWord [Var (Short "v1")]))]”

val _ = process_topdecs
  `fun fromString s =
    let
      val sPrepped = preparestring s;
      val iobuff = Word8Array.array 8 (Word8.fromInt 0);
      val _ = #(double_fromString) sPrepped iobuff;
      val a = Word8Array.sub iobuff 0;
      val b = Word8Array.sub iobuff 1;
      val c = Word8Array.sub iobuff 2;
      val d = Word8Array.sub iobuff 3;
      val e = Word8Array.sub iobuff 4;
      val f = Word8Array.sub iobuff 5;
      val g = Word8Array.sub iobuff 6;
      val h = Word8Array.sub iobuff 7;
    in
      fromWord (Word64.concatAll a b c d e f g h)
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
      val w = toWord d
      val iobuff = Word8Array.array (256) (Word8.fromInt 0);
      val _ = Word8Array.update iobuff 0 (byte_0 w);
      val _ = Word8Array.update iobuff 1 (byte_1 w);
      val _ = Word8Array.update iobuff 2 (byte_2 w);
      val _ = Word8Array.update iobuff 3 (byte_3 w);
      val _ = Word8Array.update iobuff 4 (byte_4 w);
      val _ = Word8Array.update iobuff 5 (byte_5 w);
      val _ = Word8Array.update iobuff 6 (byte_6 w);
      val _ = Word8Array.update iobuff 7 (byte_7 w);
      val _ = #(double_toString) "" iobuff;
      val n = fst (Option.valOf (Word8Array.findi is_0_byte iobuff));
    in
        Word8Array.substring iobuff 0 n
    end;` |> append_prog;

val _ = ml_prog_update close_local_blocks;

(* Ternary operations *)

val fma = “[Dlet unknown_loc (Pvar "fma")
  (Fun "v1" (Fun "v2" (Fun "v3" (FpOptimise NoOpt (App (FP_top FP_Fma)
  [Var (Short "v3"); Var (Short "v1"); Var (Short "v2")])))))]”

val _ = append_prog fma;

(* Binary operations *)

fun binop s b = “[Dlet unknown_loc (Pvar ^s)
  (Fun "v1" (Fun "v2" (FpOptimise NoOpt (App (FP_bop ^b) [Var (Short
  "v1"); Var (Short "v2")]))))]”

fun cmp s b = “[Dlet unknown_loc (Pvar ^s)
  (Fun "v1" (Fun "v2" (FpOptimise NoOpt (App (FP_cmp ^b) [Var (Short
  "v1"); Var (Short "v2")]))))]”

val _ = append_prog $ binop “"+"” “FP_Add”;
val _ = append_prog $ binop “"-"” “FP_Sub”;
val _ = append_prog $ binop “"*"” “FP_Mul”;
val _ = append_prog $ binop “"/"” “FP_Div”;

val _ = append_prog $ cmp “"<"” “FP_Less”;
val _ = append_prog $ cmp “"<="” “FP_LessEqual”;
val _ = append_prog $ cmp “">"” “FP_Greater”;
val _ = append_prog $ cmp “">="” “FP_GreaterEqual”;
val _ = append_prog $ cmp “"="” “FP_Equal”;

(* Unary operations *)

fun monop s b = “[Dlet unknown_loc (Pvar ^s)
  (Fun "v1" (FpOptimise NoOpt (App (FP_uop ^b) [Var (Short "v1")])))]”

val _ = append_prog $ monop “"abs"” “FP_Abs”;
val _ = append_prog $ monop “"sqrt"” “FP_Sqrt”;
val _ = append_prog $ monop “"~"” “FP_Neg”;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
