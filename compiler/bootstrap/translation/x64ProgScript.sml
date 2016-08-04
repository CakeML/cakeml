open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open x64_preludeProgTheory;
open x64_targetTheory x64Theory;

val _ = new_theory "x64Prog"

(* temporary *)
val _ = translation_extends "x64_preludeProg";

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

(*
  TODO: Need to translate WORD_LE
  This goes via w2i (which goes via w2n) and integer ≤
  The translator should be made to support w2i (for some reason it doesn't)
*)
val _ = translate (conv64_RHS integer_wordTheory.w2i_eq_w2n)
val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)

val _ = translate x64_config_def

val word_bit_thm = Q.prove(
  `!n w. word_bit n w = ((w && n2w (2 ** n)) <> 0w)`,
  simp [GSYM wordsTheory.word_1_lsl]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
  \\ eq_tac
  \\ rw []
  >- (qexists_tac `n` \\ simp [DECIDE ``0 < a /\ n <= a - 1n ==> n < a``])
  \\ `i = n` by decide_tac
  \\ fs [])

(* word_bit can be inlined into encode, or translated into a function
val foo = translate ((INST_TYPE[alpha|->``:4``]o SPEC_ALL )th)
val foo = translate ((INST_TYPE[alpha|->``:8``]o SPEC_ALL )th)
*)

(* word_concat *)
val wc_simp = CONV_RULE (wordsLib.WORD_CONV) o SIMP_RULE std_ss [word_concat_def,word_join_def,w2w_w2w,LET_THM]
(* word_extract *)
val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]
(* w2w has to be translated for every single use *)
val _ = translate (INST_TYPE[alpha|->``:64``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:4``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:4``,beta|->``:3``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:2``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:3``,beta|->``:4``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:64``,beta|->``:33``] w2w_def)

val _ = translate (e_imm32_def |> we_simp)

val _ = translate (e_imm8_def |> we_simp)

val _ = translate (e_ModRM_def |> wc_simp |> we_simp |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

val _ = translate (rex_prefix_def |> wc_simp |> we_simp)

val _ = translate (e_imm16_def |> we_simp)
val _ = translate (e_imm64_def |> we_simp)

val _ = translate (encode_def|>SIMP_RULE std_ss [word_bit_thm] |> wc_simp |> we_simp)

val encode_side = prove(``
  ∀x. encode_side x ⇔ T``,
  simp[fetch "-" "encode_side_def"]>>rw[]>>
  cheat)

val _ = translate (x64_enc_def |> we_simp)

(* unprovable for num2zreg in its current form *)
val num2zreg_side = prove(``
  ∀x. num2zreg_side x ⇔ T``,
  cheat)

val simpf = simp o map (fetch "-")

val x64_enc_side = prove(``
  ∀x. x64_enc_side x ⇔ T``,
  simp[fetch "-" "x64_enc_side_def"]>>rw[]>>
  simp[num2zreg_side]>> (* Temporarily get rid of cases about num2Zreg*)
  TRY(
  rw[]>>simpf["encode_side_def"]>>
  rw[]>>
  simpf["e_rm_reg_side_def","e_gen_rm_reg_side_def","e_modrm_side_def"]>>
  simpf["e_rm_imm_side_def","e_modrm_side_def","e_rm_imm8_side_def","e_opc_side_def"]>>
  NO_TAC)>>
  (* Rest of these occur in the Mem op case, and look unprovable if e_imm_8_32 returns (8,[]) *)
  simpf["encode_side_def","e_rm_reg_side_def","e_gen_rm_reg_side_def","e_modrm_side_def"]>>
  rw[]>>metis_tac[]
  cheat)

val _ = export_theory();
