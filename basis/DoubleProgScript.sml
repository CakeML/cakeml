(*
  Module for the built-in double floating-point type.
  Defines basic arithmetic operations like +,-,*,/, and FMA,
  logical operations <, <=, >, >=, and =
  and to-/fromString functions for parsing and pretty-printing constants
*)
Theory DoubleProg
Ancestors
  words CommandLineProg machine_ieee binary_ieee binary_ieeeProps real
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib realSimps[qualified]
  RealArith

val _ = translation_extends "CommandLineProg";

(* Double module -- translated *)

val _ = ml_prog_update (open_module "Double");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] «double» (Atapp [] (Short «double»))`` I);

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

Quote add_cakeml:
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

Quote add_cakeml:
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
  “[Dlet unknown_loc (Pvar «fromWord»)
                     (Fun «x» (App (FromTo (WordT W64) Float64T) [Var (Short «x»)]))]”

val _ = append_prog
  “[Dlet unknown_loc (Pvar «toWord»)
                     (Fun «x» (App (FromTo Float64T (WordT W64)) [Var (Short «x»)]))]”

(* --------------------------------------------------------------------------
 * Functions that use the FFI
 * ------------------------------------------------------------------------- *)

(* 0: Double.fromString *)
Quote add_cakeml:
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
Quote add_cakeml:
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
Quote add_cakeml:
  fun fromInt n =
    let
      val _ = write_bytes 0 (Word64.fromInt n)
      val _ = #(double_fromInt) "" bytes;
    in
      fromWord (read_bytes 0)
    end
End

(* 3: Double.toInt *)
Quote add_cakeml:
  fun toInt d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_toInt) "" bytes;
    in
      Word64.toIntSigned (read_bytes 0)
    end
End

(* 4: Double.pow *)
Quote add_cakeml:
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
Quote add_cakeml:
  fun ln d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_ln) "" bytes;
    in
      fromWord (read_bytes 0)
    end
End

(* 6: Double.exp *)
Quote add_cakeml:
  fun exp d =
    let
      val _ = write_bytes 0 (toWord d)
      val _ = #(double_exp) "" bytes;
    in
      fromWord (read_bytes 0)
    end
End

(* 7: Double.floor *)
Quote add_cakeml:
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
  “[Dlet unknown_loc (Pvar «fma») (Fun «x» (Fun «y» (Fun «z»
    (App (Arith FMA Float64T) [Var (Short «z»); Var (Short «x»);
    Var (Short «y»)]))))]”

(* --------------------------------------------------------------------------
 * Binary operations
 * ------------------------------------------------------------------------- *)

fun c nm = prim_mk_const {Thy = "ml_translator", Name = nm}
fun transc nm cnm = trans nm (c cnm)
val _ = transc "+" "float64_add"
val _ = transc "-" "float64_sub"
val _ = transc "*" "float64_mul"
val _ = transc "/" "float64_div"

val _ = transc "<"  "float64_less"
val _ = transc "<=" "float64_less_equal"
val _ = transc ">"  "float64_greater"
val _ = transc ">=" "float64_greater_equal"
val _ = transc "="  "float64_equal"

(* --------------------------------------------------------------------------
 * Unary operations
 * ------------------------------------------------------------------------- *)

val _ = transc "abs" "float64_abs"
val _ = transc "sqrt" "float64_sqrt"
val _ = transc "~" "float64_neg"

(* ----------------------------------------------------------------------
    Taking floats apart
   ---------------------------------------------------------------------- *)

Type float64 = “:(52,11)float”

Definition significand_def:
  significand f = float_to_fp64 f && 0xFFFFFFFFFFFFFw
End

Theorem significand_correct:
  significand f = w2w (f.Significand)
Proof
  simp[machine_ieeeTheory.float_to_fp64_def, significand_def, word_concat_def,
       word_join_def, word_bits_w2w, GSYM WORD_BITS_OVER_BITWISE,
       WORD_BITS_LSL, WORD_ALL_BITS, w2w_w2w, GSYM WORD_w2w_OVER_BITWISE,
       WORD_LEFT_AND_OVER_OR, w2w_LSL, word_and_lsl_eq_0] >>
  ‘0xFFFFFFFFFFFFFw : word64 = w2w (UINT_MAXw : 52 word)’
    by (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[w2w_eq_n2w]) >>
  pop_assum SUBST1_TAC >>
  simp[WORD_w2w_OVER_BITWISE]
QED

Theorem significand_correct':
  f.Significand = w2w (significand f)
Proof
  simp[machine_ieeeTheory.float_to_fp64_def, significand_def, word_concat_def,
       word_join_def, word_bits_w2w, GSYM WORD_BITS_OVER_BITWISE,
       WORD_BITS_LSL, WORD_ALL_BITS, w2w_w2w, GSYM WORD_w2w_OVER_BITWISE,
       WORD_LEFT_AND_OVER_OR, w2w_LSL, word_and_lsl_eq_0]
QED

Definition exponent_def:
  exponent f = (float_to_fp64 f >>> 52) && 0x7FFw
End

Theorem exponent_correct:
  exponent f = w2w f.Exponent
Proof
  simp[machine_ieeeTheory.float_to_fp64_def, exponent_def, word_concat_def,
       word_join_def, word_bits_w2w, GSYM WORD_BITS_OVER_BITWISE,
       WORD_BITS_LSL, WORD_ALL_BITS, w2w_w2w, GSYM WORD_w2w_OVER_BITWISE,
       WORD_LEFT_AND_OVER_OR, w2w_LSL, word_and_lsl_eq_0, lsl_lsr,
       LSR_LIMIT, word_lsr_n2w, WORD_BITS_ZERO3] >>
  ‘2047w : word64 = w2w (UINT_MAXw : 11 word)’
    by (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[w2w_eq_n2w]) >>
  pop_assum SUBST1_TAC >>
  simp[WORD_w2w_OVER_BITWISE]
QED

Theorem exponent_correct':
  f.Exponent = w2w (exponent f)
Proof
  simp[machine_ieeeTheory.float_to_fp64_def, exponent_def, word_concat_def,
       word_join_def, word_bits_w2w, GSYM WORD_BITS_OVER_BITWISE,
       WORD_BITS_LSL, WORD_ALL_BITS, w2w_w2w, GSYM WORD_w2w_OVER_BITWISE,
       WORD_LEFT_AND_OVER_OR, w2w_LSL, word_and_lsl_eq_0, lsl_lsr,
       LSR_LIMIT, word_lsr_n2w, WORD_BITS_ZERO3]
QED

Definition sign_def:
  sign f = (float_to_fp64 f >>> 63) && 1w
End

Theorem sign_correct:
  sign f = w2w f.Sign
Proof
  simp[machine_ieeeTheory.float_to_fp64_def, sign_def, word_concat_def,
       word_join_def, word_bits_w2w, GSYM WORD_BITS_OVER_BITWISE,
       WORD_BITS_LSL, WORD_ALL_BITS, w2w_w2w, GSYM WORD_w2w_OVER_BITWISE,
       WORD_LEFT_AND_OVER_OR, w2w_LSL, word_and_lsl_eq_0, lsl_lsr,
       LSR_LIMIT, word_lsr_n2w, WORD_BITS_ZERO3] >>
  ‘1w : word64 = w2w (UINT_MAXw : word1)’
    by (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[w2w_eq_n2w]) >>
  pop_assum SUBST1_TAC >>
  simp[WORD_w2w_OVER_BITWISE]
QED

Theorem sign_correct':
  f.Sign = w2w (sign f)
Proof
  simp[machine_ieeeTheory.float_to_fp64_def, sign_def, word_concat_def,
       word_join_def, word_bits_w2w, GSYM WORD_BITS_OVER_BITWISE,
       WORD_BITS_LSL, WORD_ALL_BITS, w2w_w2w, GSYM WORD_w2w_OVER_BITWISE,
       WORD_LEFT_AND_OVER_OR, w2w_LSL, word_and_lsl_eq_0, lsl_lsr,
       LSR_LIMIT, word_lsr_n2w, WORD_BITS_ZERO3] >>
  ‘1w : word1 = UINT_MAXw : word1’
    by (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[w2w_eq_n2w]) >>
  pop_assum SUBST1_TAC >>
  simp[WORD_AND_CLAUSES]
QED

val _ = translate significand_def
val _ = translate exponent_def
val _ = translate sign_def

(* ----------------------------------------------------------------------
    Putting a float together from its constituent parts (layout order)
   ---------------------------------------------------------------------- *)

Definition construct_def:
  construct (sgn:word64) (exp:word64) (sgf:word64) =
    fp64_to_float (
      ((sgn && 1w) << 63) ||
      ((exp && 0x7FFw) << 52) ||
      (sgf && 0xFFFFFFFFFFFFFw)
    )
End

Theorem w2w'_11 = w2w_w2w |> GSYM |> INST_TYPE [beta |-> “:11”] |> SRULE[]
Theorem w2w'_52 = w2w_w2w |> GSYM |> INST_TYPE [beta |-> “:52”] |> SRULE[]
Theorem w2w'_01 = w2w_w2w |> GSYM |> INST_TYPE [beta |-> “:1”] |> SRULE[]

Theorem w2w_range_11 =
        word_bits_w2w |> INST_TYPE [alpha |-> “:64”, beta |-> “:11”]
                      |> SPEC_ALL |> Q.INST [‘h’ |-> ‘10’, ‘l’ |-> ‘0’]
                      |> SRULE[WORD_ALL_BITS] |> SYM
Theorem w2w_range_52 =
        word_bits_w2w |> INST_TYPE [alpha |-> “:64”, beta |-> “:52”]
                      |> SPEC_ALL
                      |> Q.INST [‘h’ |-> ‘51’, ‘l’ |-> ‘0’]
                      |> SRULE[WORD_ALL_BITS] |> SYM
Theorem w2w_range_01 =
        word_bits_w2w |> INST_TYPE [alpha |-> “:64”, beta |-> “:1”]
                      |> SPEC_ALL
                      |> Q.INST [‘h’ |-> ‘0’, ‘l’ |-> ‘0’]
                      |> SRULE[WORD_ALL_BITS] |> SYM


Theorem construct_correct:
  construct sig exp sgf = <|
    Sign := w2w sig;
    Exponent := w2w exp;
    Significand := w2w sgf
  |>
Proof
  simp[construct_def, machine_ieeeTheory.fp64_to_float_def,
       word_extract_def, GSYM WORD_BITS_OVER_BITWISE,
       WORD_BITS_LSL, GSYM WORD_w2w_OVER_BITWISE] >>
  simp[w2w'_11, w2w'_52, w2w'_01] >>
  ‘1w : word1 = UINT_MAXw : word1’
    by (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[w2w_eq_n2w]) >>
  pop_assum SUBST1_TAC >>
  simp[WORD_AND_CLAUSES]
QED

Theorem construct_correct':
  <| Sign := sig; Exponent := exp; Significand := sgf |> =
  construct (w2w sig) (w2w exp) (w2w sgf)
Proof
  simp[construct_def, machine_ieeeTheory.fp64_to_float_def,
       word_extract_def, GSYM WORD_BITS_OVER_BITWISE,
       WORD_BITS_LSL, GSYM WORD_w2w_OVER_BITWISE,
       w2w_range_11, w2w_range_52, w2w_range_01] >>
  simp[w2w_w2w, WORD_ALL_BITS] >>
  ‘1w : word1 = UINT_MAXw : word1’
    by (ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[w2w_eq_n2w]) >>
  pop_assum SUBST1_TAC >>
  simp[WORD_AND_CLAUSES]
QED

val _ = translate construct_def

Definition fnext_hi_def:
  fnext_hi f = fp64_to_float (float_to_fp64 f + 1w)
End

Definition fnext_lo_def:
  fnext_lo f = fp64_to_float (float_to_fp64 f - 1w)
End

val _ = translate fnext_hi_def
val _ = translate fnext_lo_def

Overload f2r[local] = “float_to_real”
Overload nl[local] = “next_lo”

Theorem float_is_finite_characterisation:
  float_is_finite f ⇔ exponent f ≠ 0x7FFw
Proof
  simp[binary_ieeeTheory.float_is_finite,
       binary_ieeeTheory.float_is_subnormal_def,
       binary_ieeeTheory.float_is_normal_def,
       binary_ieeeTheory.float_is_zero, exponent_correct] >>
  Cases_on ‘f.Exponent = 0w’ >> simp[w2w_eq_n2w] >>
  ‘2047w : word11 = UINT_MAXw’ by simp[] >>
  pop_assum SUBST1_TAC >> simp[]
QED

val _ = translate float_is_finite_characterisation

Theorem float_is_zero_characterisation:
  float_is_zero f ⇔ exponent f = 0w ∧ significand f = 0w
Proof
  simp[binary_ieeeTheory.float_is_zero, exponent_correct,
       significand_correct, w2w_eq_n2w]
QED

val _ = translate float_is_zero_characterisation

Definition flt_max_def:
  flt_max : (52,11) float =
  <| Sign := 0w; Exponent := 0x7FEw; Significand := 0xFFFFFFFFFFFFFw |>
End

val _ = translate flt_max_def

Theorem flt_max_correct:
  flt_max = float_top (:52 # 11)
Proof
  simp[float_top_def, flt_max_def, word_T_def, GSYM n2w_sub]
QED

Overload precision[local] = “dimindex”

Definition maxulp_def:
  maxulp : (52,11) float = <|
    Sign := 0w; Significand := 0w;
    Exponent := 1994w
  |>
End

val _ = translate maxulp_def

Definition twicemaxulp_def:
  twicemaxulp : (52,11) float = <|
    Sign := 0w; Significand := 0w; Exponent := 1995w
  |>
End

val _ = translate twicemaxulp_def

Definition ffloat_ulp_def:
  ffloat_ulp (f0:(52,11)float) =
  let f = float64_abs f0
  in
    if float_is_finite f then
      if f = flt_max then maxulp
      else float64_sub (fnext_hi f) f
    else
      twicemaxulp
End
val _ = translate ffloat_ulp_def

Definition posinf64_def:
  posinf64 : (52,11)float = <|
    Sign := 0w; Exponent := 0x7ffw; Significand := 0w
  |>
End
val _ = translate posinf64_def

Definition neginf64_def:
  neginf64 : (52,11) float = <|
    Sign := 1w; Exponent := 0x7ffw; Significand :=  0w
  |>
End
val _ = translate neginf64_def

Definition posmin64_def:
  posmin64 = ^(rhs $ concl $ EVAL “fp64_to_float 1w”)
End
val _ = translate posmin64_def

Definition poszero64_def:
  poszero64 = ^(rhs $ concl $ EVAL “fp64_to_float 0w”)
End
val _ = translate poszero64_def

Theorem word_addR_concat:
  FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) ∧
  w2n w2 + y < 2 ** precision(:β) ⇒
  (w1:α word) @@ (w2:β word) + n2w y = (w1 @@ (w2 + n2w y)) : γ word
Proof
  simp[word_concat_def, word_join_def, w2w_def] >>
  Cases_on ‘w2’ >> simp[] >> strip_tac >>
  simp[word_add_n2w, word_mul_n2w, dimword_def,
       word_T_def, dimword_def, UINT_MAX_def, WORD_MUL_LSL] >>
  ‘n2w (w2n w1 * 2 ** precision(:β)) && n2w (n + y) : (α + β) word = 0w’
    by (simp[word_and_n2w, dimword_def, bitTheory.BITWISE_LT_2EXP] >>
        dep_rewrite.DEP_ONCE_REWRITE_TAC[bitTheory.BITWISE_COMM] >>
        simp[CONJ_COMM] >>
        irule bitTheory.BITWISE_AND_SHIFT_EQ_0 >> simp[]) >>
  drule_then (assume_tac o SYM) WORD_ADD_OR >>
  simp[word_add_n2w, dimword_def] >>
  cong_tac (SOME 1) >>
  ‘n2w (w2n w1 * 2 ** precision(:β)) && n2w n : (α + β) word = 0w’
    by (simp[word_and_n2w, dimword_def, bitTheory.BITWISE_LT_2EXP] >>
        dep_rewrite.DEP_ONCE_REWRITE_TAC[bitTheory.BITWISE_COMM] >>
        simp[CONJ_COMM] >>
        irule bitTheory.BITWISE_AND_SHIFT_EQ_0 >> simp[]) >>
  drule_then (assume_tac o SYM) WORD_ADD_OR >>
  simp[word_add_n2w, dimword_def, Once WORD_OR_COMM] >>
  Cases_on ‘w1’ >> simp[] >>
  rename [‘n1 < dimword(:α)’, ‘n2 + y  < 2 ** precision(:β)’] >>
  ‘n2 + n1 * 2 ** precision(:β) < 2 ** precision(:α + β)’
    by (simp[fcpTheory.index_sum] >> rw[] >>
        simp[EXP_ADD] >> gvs[dimword_def] >>
        irule LESS_EQ_LESS_TRANS >>
        qexists
        ‘(2 ** precision(:β) - 1) +
         (2 ** precision(:α) - 1) * (2 ** precision(:β))’ >>
        irule_at Any (DECIDE “a ≤ m ∧ b ≤ n ⇒ a + b ≤ m + n:num”) >>
        simp[RIGHT_SUB_DISTRIB] >>
        ‘2 ** precision(:β) ≤ 2 ** precision(:α) * 2 ** precision(:β)’
          by simp[] >>
        ‘1 ≤ 2 ** precision(:β)’ by simp[] >>
        simp[DECIDE “1 ≤ x ∧ x ≤ y ⇒ x - 1n + (y - x) = y - 1”]) >>
  simp[] >>
  simp[fcpTheory.index_sum] >> rw[] >>
  simp[EXP_ADD] >> gvs[dimword_def] >>
  irule LESS_EQ_LESS_TRANS >>
  qexists
  ‘(2 ** precision(:β) - 1) +
   (2 ** precision(:α) - 1) * (2 ** precision(:β))’ >>
  irule_at Any (DECIDE “a + b ≤ m ∧ c ≤ n ⇒ a + (b + c) ≤ m + n:num”) >>
  simp[RIGHT_SUB_DISTRIB] >>
  ‘2 ** precision(:β) ≤ 2 ** precision(:α) * 2 ** precision(:β)’
    by simp[] >>
  ‘1 ≤ 2 ** precision(:β)’ by simp[] >>
  simp[DECIDE “1 ≤ x ∧ x ≤ y ⇒ x - 1n + (y - x) = y - 1”]
QED

Theorem fp64_word_concat_assoc:
  (w1 : unit word) @@ ((w2 : 11 word) @@ (w3 : 52 word)):63 word =
  ((w1 @@ w2) : 12 word @@ w3) : word64
Proof
  ‘precision(:unit) + precision(:11) = precision(:12)’
    by (simp[fcpTheory.finite_bit0, fcpTheory.index_bit0,
             fcpTheory.index_bit1, fcpTheory.index_one,
             fcpTheory.finite_bit1, fcpTheory.finite_one]) >>
  dxrule_at_then Any irule (GSYM word_concat_assoc) >>
  simp[fcpTheory.finite_bit0, fcpTheory.index_bit0,
       fcpTheory.index_bit1, fcpTheory.index_one,
       fcpTheory.finite_bit1, fcpTheory.finite_one]
QED

val _ = diminish_srw_ss [
    "word arith", "word ground", "word logic", "word shift",
    "word subtract", "words"
  ]

val _ = augment_srw_ss [
    rewrites [w2n_n2w, WORD_AND_CLAUSES, n2w_11, WORD_ADD_0]
  ]

Theorem next_hi_fnext_hi:
  float_is_finite f ⇒ next_hi f = fnext_hi f
Proof
  rw[next_hi_def, fnext_hi_def]
  >- (irule (iffLR float_to_fp64_11) >>
      simp[float_to_fp64_fp64_to_float, float_to_fp64_def,
           fp64_word_concat_assoc] >>
      irule (GSYM word_addR_concat) >>
      gvs[word_T_def, UINT_MAX_def, dimword_def, fcpTheory.finite_bit0,
          fcpTheory.finite_bit1, fcpTheory.finite_one] >>
      Cases_on ‘f.Significand’ >>
      gvs[dimword_def, WORD_LO_word_T, word_lo_n2w]) >>
  irule (iffLR float_to_fp64_11) >>
  simp[float_to_fp64_fp64_to_float, float_to_fp64_def,
       GSYM fp64_word_concat_assoc] >>
  Cases_on ‘f.Significand’ >> gvs[word_T_def, word_lo_n2w] >>
  rename [‘f.Significand = n2w fS’] >> ‘fS = 4503599627370495’ by simp[] >>
  gvs[WORD_LO_word_T, GSYM fp64_word_concat_assoc] >>
  mp_tac $
    Q.INST [
      ‘w1’ |-> ‘(f:(52,11)float).Sign’, ‘y’ |-> ‘1’,
      ‘w2’ |-> ‘((f:(52,11)float).Exponent : 11 word) @@
                (0xFFFFFFFFFFFFFw : 52 word)’]
       (INST_TYPE [alpha |-> “:one”, beta |-> “:63”, gamma |-> “:64”]
                  word_addR_concat) >>
  impl_tac
  >- (simp[fcpTheory.finite_bit1, fcpTheory.finite_bit0] >>
      simp[word_concat_def, w2w_def, word_join_def] >>
      Cases_on ‘f.Exponent’ >>
      gvs[dimword_def, float_is_finite_Exponent,
          NOT_LESS_EQUAL] >>
      dep_rewrite.DEP_REWRITE_TAC[GSYM WORD_ADD_OR] >>
      ONCE_REWRITE_TAC [WORD_AND_COMM] >>
      irule_at Any (GSYM word_and_lsl_eq_0) >> simp[] >>
      simp[WORD_MUL_LSL, word_mul_n2w, word_add_n2w] >>
      gvs[word_T_def, n2w_11, dimword_def]) >>
  strip_tac >> simp[] >>
  cong_tac (SOME 1) >>
  simp[word_concat_def, w2w_def, word_join_def] >>
  Cases_on ‘f.Exponent’ >>
  gvs[dimword_def, float_is_finite_Exponent,
      NOT_LESS_EQUAL, word_add_n2w, word_T_def] >>
  cong_tac (SOME 1) >>
  dep_rewrite.DEP_REWRITE_TAC[GSYM WORD_ADD_OR] >>
  ONCE_REWRITE_TAC [WORD_AND_COMM] >> simp[] >>
  irule_at Any word_and_lsl_eq_0 >> simp[] >>
  simp[WORD_MUL_LSL, word_mul_n2w, word_add_n2w]
QED

Theorem next_lo_fnext_lo:
  float_is_finite f ∧ ¬float_is_zero f ⇒ next_lo f = fnext_lo f
Proof
  rw[fnext_lo_def] >>
  ‘next_hi (nl f) = f’ by simp[] >>
  ‘float_is_finite (nl f)’ by simp[float_is_finite_next_lo] >>
  dxrule_then assume_tac next_hi_fnext_hi >>
  gvs[WORD_ADD_EQ_SUB, fnext_lo_def, fnext_hi_def] >>
  qpat_x_assum ‘fp64_to_float _ = f’ (mp_tac o Q.AP_TERM ‘float_to_fp64’)>>
  REWRITE_TAC[float_to_fp64_fp64_to_float] >>
  disch_then (mp_tac o Q.AP_TERM ‘λw. w - 1w’) >> simp[WORD_ADD_SUB] >>
  disch_then (mp_tac o Q.AP_TERM ‘fp64_to_float’) >>
  REWRITE_TAC[fp64_to_float_float_to_fp64]
QED

Theorem maxulp_correct:
  f2r maxulp = ulpᶠ (float_top (:52 # 11))
Proof
  simp[float_to_real_def, float_ulp_def, float_top_def, maxulp_def,
       word_T_def, ULP_def, WORD_EQ_SUB_ZERO, realTheory.REAL_DIV_LZERO,
       GSYM n2w_sub, SF realSimps.RMULRELNORM_ss, SF realSimps.RMULCANON_ss]
QED

Overload abs[local] = “realax$abs”

Theorem ABS_REFL' = iffRL ABS_REFL

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss]

Theorem abs_sub_lemma =
        REAL_ARITH “(0 ≤ x ⇔ 0 ≤ y) ∧ abs y < abs x ⇒
                    abs (x - y) = abs x - abs y”

Theorem ffloat_ulp_correct:
  float_is_finite f ⇒
  float_to_real (ffloat_ulp f) = ulpᶠ f
Proof
  rw[ffloat_ulp_def, maxulp_correct, flt_max_correct,
     ml_translatorTheory.float64_abs_thm]
  >- metis_tac[float_ulp_abs] >>
  simp[GSYM next_hi_fnext_hi, ml_translatorTheory.float64_sub_thm] >>
  drule_then assume_tac float_is_finite_float_value >>
  ‘float_is_finite (next_hi (float_abs f))’
    by (irule float_is_finite_next_hi >> simp[float_to_real_float_abs] >>
        ‘abs (f2r f) ≤ largest(:52 # 11)’
          by simp[abs_float_bounds, GSYM float_to_real_float_abs,
                  Excl "float_to_real_float_abs"] >>
        ‘abs (f2r f) ≠ largest(:52 # 11)’ suffices_by simp[] >>
        strip_tac >> gvs[] >>
        qpat_x_assum ‘x ≠ y’ mp_tac >> simp[] >>
        gvs[largest_is_top, GSYM float_to_real_float_abs, float_to_real_eq,
            Excl "float_to_real_float_abs"]) >>
  ‘float_value (next_hi (float_abs f)) = Float (f2r (next_hi (float_abs f)))’
    by simp[float_is_finite_float_value] >>
  ‘float_value (float_abs f) = Float (f2r (float_abs f))’
    by simp[float_is_finite_float_value] >>
  simp[float_sub_def] >> simp[float_round_with_flags_def] >>
  simp[float_round_def] >>
  ‘f2r (next_hi (float_abs f)) - abs (f2r f) = ulpᶠ f’
    by (simp[REAL_EQ_SUB_RADD] >>
        ONCE_REWRITE_TAC[REAL_ADD_COMM] >>
        simp[GSYM next_hi_difference, next_hi_float_abs] >>
        Cases_on ‘f2r f = 0’ >- simp[] >>
        ‘abs (f2r f) < abs (f2r (next_hi f))’ by simp[next_hi_larger] >>
        ‘0 ≤ f2r (next_hi f) ⇔ 0 ≤ f2r f’
          by (simp[] >> ‘f ≠ NEG0’ by (strip_tac >> gvs[])>> simp[]) >>
        simp[abs_sub_lemma]) >>
  simp[] >>
  rev_drule ulp_multiples_representable >> simp[] >>
  disch_then (qspecl_then [‘ulpᶠ f’, ‘1’] mp_tac) >> simp[] >>
  disch_then (qx_choose_then ‘uf’ assume_tac)>>
  drule float_value_float_to_real >> disch_then (assume_tac o SYM) >> gvs[] >>
  ‘f2r uf ≠ 0’ by metis_tac[float_ulp_EQ0] >>
  ‘float_is_finite uf’ by simp[float_is_finite_thm] >>
  simp[round_representable_nonzero, float_is_zero_to_real]
QED

(* --------------------------------------------------------------------------
 * Pretty-printer
 * ------------------------------------------------------------------------- *)

val _ = append_prog “
  [Dlet unknown_loc
     (Pvar «pp_double»)
     (Fun «x» (App Opapp [
        Var (Long «PrettyPrinter» (Short «token»));
        App Opapp [Var (Short «toString»); Var (Short «x»)]]))]”;

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);
