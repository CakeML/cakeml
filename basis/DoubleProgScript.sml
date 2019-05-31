(*
  Module about the built-in integer tyoe. Note that CakeML uses
  arbitrary precision integers (the mathematical intergers).
*)
open preamble
     ml_translatorLib ml_progLib basisFunctionsLib
     wordsTheory
     Word8ArrayProgTheory;

val _ = new_theory"DoubleProg";

val _ = translation_extends "Word8ArrayProg";

(* Double module -- translated *)

val _ = ml_prog_update (open_module "Double");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "double" (Atapp [] (Short "word64"))`` I);

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

(* Define exception for fromString function *)
val _ = process_topdecs `
  exception InvalidFloat;` |> append_prog

val _ = ml_prog_update open_local_block;

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val InvalidFloat = get_exn_conv ``"InvalidFloat"``;

val InvalidFloat_exn_def = Define `
  InvalidFloat_exn v = (v = Conv (SOME ^InvalidFloat) [])`

(* We allocate a "buffer" in which the FFI can store the double word;
  8 times an 8 bit word *)
val iobuff_e = ``(App Aw8alloc [Lit (IntLit 8); Lit (Word8 0w)])``
val eval_thm = let
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val st = get_ml_prog_state () |> ml_progLib.get_state
  val new_st = ``^st with refs := ^st.refs ++ [W8array (REPLICATE 8 0w)]``
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, iobuff_e, new_st, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
  val v_def = define_abbrev false "iobuff_loc" v_tm
in v_thm |> REWRITE_RULE [GSYM v_def] end

val _ = ml_prog_update (add_Dlet eval_thm "iobuff" []);

val concat_all_def = Define `
  concat_all (a:word8) b c d e f g h =
    concat_word_list [a;b;c;d;e;f;g;h]:64 word`

val concat_all_impl = REWRITE_RULE [concat_word_list_def, dimindex_8] concat_all_def;

val _ = (next_ml_names := ["concat_all"]);
val _ = translate concat_all_impl;

val _ = ml_prog_update open_local_in_block;

val _ = process_topdecs
  `fun fromString s =
    let
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

(* We allocate a "buffer" in which the FFI can store the double word
  as a string + some space to store the double word itself *)
val iobuff_e = ``(App Aw8alloc [Lit (IntLit (8 + 255)); Lit (Word8 0w)])``
val eval_thm = let
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val st = get_ml_prog_state () |> ml_progLib.get_state
  val new_st = ``^st with refs := ^st.refs ++ [W8array (REPLICATE (8+255) 0w)]``
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, iobuff_e, new_st, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
  val v_def = define_abbrev false "iobuff_loc" v_tm
in v_thm |> REWRITE_RULE [GSYM v_def] end

val _ = ml_prog_update (add_Dlet eval_thm "iobuff" []);

val split_word8_def = Define `
  split_word8 (w:word64) =
    let
      w1:word8 = w2w w;
      w2:word8 = w2w (w << 8);
      w3:word8 = w2w (w << 16);
      w4:word8 = w2w (w << 24);
      w5:word8 = w2w (w << 32);
      w6:word8 = w2w (w << 40);
      w7:word8 = w2w (w << 48);
      w8:word8 = w2w (w << 56);
    in
      (w1,w2,w3,w4,w5,w6,w7,w8)`

val _ = (next_ml_names := ["split_word8"]);
val _ = translate split_word8_def;

val _ = ml_prog_update open_local_in_block;

val _ = process_topdecs
  `fun toString d =
    let
      val (w1,w2,w3,w4,w5,w6,w7,w8) = split_word8 d;
      val _ = Word8Array.update iobuff 0 w1;
      val _ = Word8Array.update iobuff 1 w2;
      val _ = Word8Array.update iobuff 2 w3;
      val _ = Word8Array.update iobuff 3 w4;
      val _ = Word8Array.update iobuff 4 w5;
      val _ = Word8Array.update iobuff 5 w6;
      val _ = Word8Array.update iobuff 6 w7;
      val _ = Word8Array.update iobuff 7 w8;
      val _ = #(double_toString) s iobuff;
    in
      Word8Array.substring iobuff 8 (255 + 7)
    end;` |> append_prog;

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
