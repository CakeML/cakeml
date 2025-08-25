(*
  Module for the built-in double floating-point type.
  Defines basic arithmetic operations like +,-,*,/, and FMA,
  logical operations <, <=, >, >=, and =
  and to-/fromString functions for parsing and pretty-printing constants
*)
Theory DoubleProg
Ancestors
  words CommandLineProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "CommandLineProg";

val cakeml = append_prog o process_topdecs;

(* Double module -- translated *)

val _ = ml_prog_update (open_module "Double");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "double" (Atapp [] (Short "double"))`` I);

val _ = ml_prog_update open_local_block;

(* --------------------------------------------------------------------------
 * Byte array for the FFI communication
 * ------------------------------------------------------------------------- *)

local
  val bytes_e = ``(App Aw8alloc [Lit (IntLit 256); Lit (Word8 0w)])``
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val st = get_ml_prog_state () |> ml_progLib.get_state
  val new_st = ``^st with refs := ^st.refs ++ [W8array (REPLICATE 256 0w)]``
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, bytes_e, new_st, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal
    |> (EVAL THENC SCONV[semanticPrimitivesTheory.state_component_equality])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
  val v_def = define_abbrev false "bytes_loc" v_tm
  val eval_thm =  v_thm |> REWRITE_RULE [GSYM v_def]
in
  val _ = ml_prog_update (add_Dlet eval_thm "bytes");
end

(* --------------------------------------------------------------------------
 * Helper functions
 * ------------------------------------------------------------------------- *)

Definition byte_0_def:
  byte_0 (d:word64) = (w2w d):word8
End

Definition byte_1_def:
  byte_1 (d:word64) = (w2w (d >>> 8)):word8
End

Definition byte_2_def:
  byte_2 (d:word64) = (w2w (d >>> 16)):word8
End

Definition byte_3_def:
  byte_3 (d:word64) = (w2w (d >>> 24)):word8
End

Definition byte_4_def:
  byte_4 (d:word64) = (w2w (d >>> 32)):word8
End

Definition byte_5_def:
  byte_5 (d:word64) = (w2w (d >>> 40)):word8
End

Definition byte_6_def:
  byte_6 (d:word64) = (w2w (d >>> 48)):word8
End

Definition byte_7_def:
  byte_7 (d:word64) = (w2w (d >>> 56)):word8
End

val _ = translate byte_0_def;
val _ = translate byte_1_def;
val _ = translate byte_2_def;
val _ = translate byte_3_def;
val _ = translate byte_4_def;
val _ = translate byte_5_def;
val _ = translate byte_6_def;
val _ = translate byte_7_def;

Definition is_0_byte_def:
  is_0_byte (c: word8) = (c = n2w 0)
End

val _ = translate is_0_byte_def;

Quote cakeml:
  fun read_bytes offset =
    let
      val a = Word8Array.sub bytes offset;
      val b = Word8Array.sub bytes (offset + 1);
      val c = Word8Array.sub bytes (offset + 2);
      val d = Word8Array.sub bytes (offset + 3);
      val e = Word8Array.sub bytes (offset + 4);
      val f = Word8Array.sub bytes (offset + 5);
      val g = Word8Array.sub bytes (offset + 6);
      val h = Word8Array.sub bytes (offset + 7);
    in
      Word64.concatAll a b c d e f g h
    end
End

Quote cakeml:
  fun write_bytes offset d =
    let
      val _ = Word8Array.update bytes offset (byte_0 d);
      val _ = Word8Array.update bytes (offset + 1) (byte_1 d);
      val _ = Word8Array.update bytes (offset + 2) (byte_2 d);
      val _ = Word8Array.update bytes (offset + 3) (byte_3 d);
      val _ = Word8Array.update bytes (offset + 4) (byte_4 d);
      val _ = Word8Array.update bytes (offset + 5) (byte_5 d);
      val _ = Word8Array.update bytes (offset + 6) (byte_6 d);
      val _ = Word8Array.update bytes (offset + 7) (byte_7 d);
    in
      ()
    end
End

Definition prepareString_def:
  prepareString (s:mlstring) = translate (\c. if c = #"~" then #"-" else c) s
End
val _ = translate prepareString_def;

val _ = ml_prog_update open_local_in_block;

val _ = append_prog
  “[Dlet unknown_loc (Pvar "fromWord")
                     (Fun "x" (App FpFromWord [Var (Short "x")]))]”

val _ = append_prog
  “[Dlet unknown_loc (Pvar "toWord")
                     (Fun "x" (App FpToWord [Var (Short "x")]))]”

(* --------------------------------------------------------------------------
 * Functions that use the FFI
 * ------------------------------------------------------------------------- *)

(* 0: Double.fromString *)
Quote cakeml:
  fun fromString s =
    let
      val _ = #(double_fromString) (preparestring s) bytes;
      val err = Word8Array.sub bytes 0
    in
      if err = Word8.fromInt 0 then
        Some (fromWord (read_bytes 1))
      else
        None
    end
End

(* 1: Double.toString *)
Quote cakeml:
  fun toString d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_toString) "" bytes;
      val n = fst (Option.valOf (Word8Array.findi is_0_byte bytes));
    in
      Word8Array.substring bytes 0 n
    end
End

(* 2: Double.fromInt *)
Quote cakeml:
  fun fromInt n =
    let
      val _ = write_bytes 0 (Word64.fromInt n)
      val _ = #(double_fromInt) "" bytes;
    in
      fromWord (read_bytes 0)
    end
End

(* 3: Double.toInt *)
Quote cakeml:
  fun toInt d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_toInt) "" bytes;
    in
      Word64.toIntSigned (read_bytes 0)
    end
End

(* 4: Double.pow *)
Quote cakeml:
  fun pow x y =
    let
      val _ = write_bytes 0 (toWord x)
      val _ = write_bytes 8 (toWord y)
      val _ = #(double_pow) "" bytes;
    in
      fromWord (read_bytes 0)
    end
End

(* 5: Double.ln *)
Quote cakeml:
  fun ln d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_ln) "" bytes;
    in
      fromWord (read_bytes 0)
    end
End

(* 6: Double.exp *)
Quote cakeml:
  fun exp d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_exp) "" bytes;
    in
      fromWord (read_bytes 0)
    end
End

(* 7: Double.floor *)
Quote cakeml:
  fun floor d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_floor) "" bytes;
    in
      fromWord (read_bytes 0)
    end
End

(* --------------------------------------------------------------------------
 * Ternary operations
 * ------------------------------------------------------------------------- *)

val _ = append_prog
  “[Dlet unknown_loc (Pvar "fma") (Fun "x" (Fun "y" (Fun "z"
    (App (FP_top FP_Fma) [Var (Short "z"); Var (Short "x");
    Var (Short "y")]))))]”

(* --------------------------------------------------------------------------
 * Binary operations
 * ------------------------------------------------------------------------- *)

fun binop s b = “[Dlet unknown_loc (Pvar ^s)
  (Fun "x" (Fun "y" (App (FP_bop ^b) [Var (Short
  "x"); Var (Short "y")])))]”

fun cmp s b = “[Dlet unknown_loc (Pvar ^s)
  (Fun "x" (Fun "y" (App (FP_cmp ^b) [Var (Short
  "x"); Var (Short "y")])))]”

val _ = append_prog $ binop “"+"” “FP_Add”;
val _ = append_prog $ binop “"-"” “FP_Sub”;
val _ = append_prog $ binop “"*"” “FP_Mul”;
val _ = append_prog $ binop “"/"” “FP_Div”;

val _ = append_prog $ cmp “"<"” “FP_Less”;
val _ = append_prog $ cmp “"<="” “FP_LessEqual”;
val _ = append_prog $ cmp “">"” “FP_Greater”;
val _ = append_prog $ cmp “">="” “FP_GreaterEqual”;
val _ = append_prog $ cmp “"="” “FP_Equal”;

(* --------------------------------------------------------------------------
 * Unary operations
 * ------------------------------------------------------------------------- *)

fun monop s b = “[Dlet unknown_loc (Pvar ^s)
  (Fun "x" (App (FP_uop ^b) [Var (Short "x")]))]”

val _ = append_prog $ monop “"abs"” “FP_Abs”;
val _ = append_prog $ monop “"sqrt"” “FP_Sqrt”;
val _ = append_prog $ monop “"~"” “FP_Neg”;

(* --------------------------------------------------------------------------
 * Pretty-printer
 * ------------------------------------------------------------------------- *)

val _ = append_prog “
  [Dlet unknown_loc
     (Pvar "pp_double")
     (Fun "x" (App Opapp [
        Var (Long "PrettyPrinter" (Short "token"));
        App Opapp [Var (Short "toString"); Var (Short "x")]]))]”;

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

