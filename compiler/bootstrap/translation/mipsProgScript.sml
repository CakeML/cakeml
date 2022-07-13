(*
  Translate the MIPS instruction encoder and MIPS-specific config.
*)
open preamble;
open evaluateTheory
open ml_translatorLib ml_translatorTheory;
open riscvProgTheory
open mips_targetTheory mipsTheory;
open inliningLib;

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "mipsProg"

val _ = translation_extends "riscvProg";
val _ = ml_translatorLib.use_string_type true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "mipsProg");

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> REWRITE_RULE (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val spec_word_bit = word_bit |> ISPEC``foo:word16`` |> SPEC``15n``|> SIMP_RULE std_ss [word_bit_test] |> CONV_RULE (wordsLib.WORD_CONV)

val defaults =
  [mips_ast_def,mips_encode_def,Encode_def,
   mips_bop_r_def, mips_bop_i_def, mips_memop_def,
   mips_encode_fail_def,
   form1_def,form2_def,form3_def,form4_def,form5_def,form6_def,
   mips_fp_cmp_def,COP1Encode_def]

val mips_enc_thms =
  mips_enc_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:64 asm``])[]
  |> CONJUNCTS
val mips_enc1 = el 1 mips_enc_thms
val mips_enc2 = el 2 mips_enc_thms
val mips_enc3 = el 3 mips_enc_thms
val mips_enc4 = el 4 mips_enc_thms
val mips_enc5 = el 5 mips_enc_thms
val mips_enc6 = el 6 mips_enc_thms

val mips_enc1s =
  mips_enc1
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:64 inst``]) defaults
  |> CONJUNCTS

val mips_enc1_1 = el 1 mips_enc1s
val mips_enc1_2 = el 2 mips_enc1s
  |> SIMP_RULE (srw_ss()++LET_ss) ([Ntimes COND_RAND 5,COND_RATOR,spec_word_bit]@defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]
  |> csethm 5

val (binop::shift::rest) = el 3 mips_enc1s |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 arith``]) [] |> CONJUNCTS

val (binopreg_aux::binopimm_aux::_) = binop |> SIMP_RULE (srw_ss() ++
  DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``])
  [FORALL_AND_THM] |> CONJUNCTS |> map (SIMP_RULE (srw_ss() ++ LET_ss
  ++ DatatypeSimps.expand_type_quants_ss [``:binop``]) [])

val binopreg = binopreg_aux |> CONJUNCTS |> map(fn th => th |>
  SIMP_RULE (srw_ss()++LET_ss) (defaults) |> wc_simp |> we_simp |>
  gconv |>SIMP_RULE std_ss [SHIFT_ZERO])

val binopregth = reconstruct_case ``mips_enc (Inst (Arith (Binop b n
  n0 (Reg n'))))`` (rand o rator o rator o rator o rand o rand o rand)
  (map (csethm 2) binopreg)

val binopimm = binopimm_aux |> CONJUNCTS |> map(fn th => th
  |> SIMP_RULE (srw_ss()++LET_ss)
               (Q.ISPEC`LIST_BIND`COND_RAND :: COND_RATOR :: word_mul_def :: defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])

val binopimmth = reconstruct_case ``mips_enc (Inst (Arith (Binop b n n0 (Imm c))))`` (rand o rator o rator o rator o rand o rand o rand) binopimm

val binopth = reconstruct_case ``mips_enc(Inst (Arith (Binop b n n0 r)))`` (rand o rand o rand o rand) [binopregth,binopimmth]

val shiftths =
  shift
  |> SIMP_RULE(srw_ss()++LET_ss++DatatypeSimps.expand_type_quants_ss[``:shift``])
      (Q.ISPEC`(λ(f,n). P f n)` COND_RAND::
       Q.ISPEC`LIST_BIND`COND_RAND ::
       COND_RATOR ::
       mips_sh32_def :: mips_sh_def ::
      defaults)
  |> CONJUNCTS
  |> map (fn th => th |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])

val shiftth = reconstruct_case ``mips_enc(Inst (Arith (Shift s n n0 n1)))``
  (rand o funpow 3 rator o funpow 3 rand) shiftths

val mips_enc1_3_aux = binopth :: shiftth :: map (fn th => th |>
SIMP_RULE (srw_ss()) defaults |> wc_simp |> we_simp |> gconv |>
SIMP_RULE std_ss [SHIFT_ZERO]) rest

val mips_enc1_3 = reconstruct_case ``mips_enc (Inst (Arith a))`` (rand
o rand o rand) mips_enc1_3_aux

val mips_enc1_4_aux = el 4 mips_enc1s |> SIMP_RULE (srw_ss() ++
DatatypeSimps.expand_type_quants_ss [``:64 addr``,``:memop``])
defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss
[SHIFT_ZERO] |> CONJUNCTS

val mips_enc1_4 = reconstruct_case ``mips_enc (Inst (Mem m n a))``
(rand o rand o rand) [reconstruct_case ``mips_enc (Inst (Mem m n (Addr
n' c)))`` (rand o rator o rator o rand o rand) mips_enc1_4_aux]

val mips_enc1_5_aux = el 5 mips_enc1s |> SIMP_RULE (srw_ss() ++
DatatypeSimps.expand_type_quants_ss [``:fp``]) defaults |> wc_simp |>
we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> CONJUNCTS

val mips_enc1_5 = reconstruct_case ``mips_enc (Inst (FP f))`` (rand o
rand o rand) mips_enc1_5_aux

val mips_simp1 = reconstruct_case ``mips_enc (Inst i)`` (rand o rand)
[mips_enc1_1,mips_enc1_2,mips_enc1_3,mips_enc1_4,mips_enc1_5]

val mips_simp2 = mips_enc2 |> SIMP_RULE (srw_ss() ++ LET_ss) (Once
COND_RAND::COND_RATOR::defaults) |> wc_simp |> we_simp |> gconv |>
SIMP_RULE std_ss [SHIFT_ZERO]

val mips_enc3_aux = mips_enc3
  |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss[``:64 reg_imm``])[FORALL_AND_THM]
  |> CONJUNCTS
  |> map (fn th => th
     |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:cmp``])
                  (mips_cmp_def::defaults)
     |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO])

val mips_enc3_1 = el 1 mips_enc3_aux
val mips_enc3_2 = el 2 mips_enc3_aux

val mips_enc3_1_th =
  mips_enc3_1 |> CONJUNCTS
  |> reconstruct_case ``mips_enc (JumpCmp c n (Reg n') c0)``
     (rand o funpow 3 rator o rand)

val mips_enc3_2_th =
  mips_enc3_2 |> CONJUNCTS
  |> reconstruct_case ``mips_enc (JumpCmp c n (Imm c') c0)``
     (rand o funpow 3 rator o rand)

val mips_simp3 =
  reconstruct_case ``mips_enc (JumpCmp c n r c0)`` (rand o rator o rand)
    [mips_enc3_1_th,mips_enc3_2_th]

val mips_simp4 = mips_enc4 |> SIMP_RULE (srw_ss() ++ LET_ss) (Once
COND_RAND::COND_RATOR::defaults) |> wc_simp |> we_simp |> gconv |>
SIMP_RULE std_ss [SHIFT_ZERO]

val mips_simp5 = mips_enc5 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults
|> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val mips_simp6 = mips_enc6
  |> SIMP_RULE (srw_ss() ++ LET_ss) (Q.ISPEC`LIST_BIND`COND_RAND :: COND_RATOR :: defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val mips_enc_thm = reconstruct_case ``mips_enc i`` rand
[mips_simp1,mips_simp2,mips_simp3,mips_simp4,mips_simp5,mips_simp6]

val cases_defs = LIST_CONJ
  [TypeBase.case_def_of “:'a asm$inst”,
   TypeBase.case_def_of “:asm$cmp”,
   TypeBase.case_def_of “:asm$memop”,
   TypeBase.case_def_of “:asm$binop”,
   TypeBase.case_def_of “:ast$shift”,
   TypeBase.case_def_of “:asm$fp”,
   TypeBase.case_def_of “:'a asm$arith”,
   TypeBase.case_def_of “:'a asm$addr”,
   TypeBase.case_def_of “:'a asm$reg_imm”,
   TypeBase.case_def_of “:'a asm$asm”];

val d1 = Define ‘mips_enc_Const n c = mips_enc (Inst (Const n c))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Skip = mips_enc (Inst Skip)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Loc n c = mips_enc (Loc n c)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Call c = mips_enc (Call c)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_NotTest_Imm n c c0 =
                           mips_enc (JumpCmp NotTest n (Imm c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_NotLess_Imm n c c0 =
                           mips_enc (JumpCmp NotLess n (Imm c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_NotLower_Imm n c c0 =
                           mips_enc (JumpCmp NotLower n (Imm c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_NotEqual_Imm n c c0 =
                           mips_enc (JumpCmp NotEqual n (Imm c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_Test_Imm n c c0 =
                           mips_enc (JumpCmp Test n (Imm c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_Less_Imm n c c0 =
                           mips_enc (JumpCmp Less n (Imm c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_Lower_Imm n c c0 =
                           mips_enc (JumpCmp Lower n (Imm c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_Equal_Imm n c c0 =
                           mips_enc (JumpCmp Equal n (Imm c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_NotTest_Reg n c c0 =
                           mips_enc (JumpCmp NotTest n (Reg c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_NotLess_Reg n c c0 =
                           mips_enc (JumpCmp NotLess n (Reg c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_NotLower_Reg n c c0 =
                           mips_enc (JumpCmp NotLower n (Reg c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_NotEqual_Reg n c c0 =
                           mips_enc (JumpCmp NotEqual n (Reg c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_Test_Reg n c c0 =
                           mips_enc (JumpCmp Test n (Reg c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_Less_Reg n c c0 =
                           mips_enc (JumpCmp Less n (Reg c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_Lower_Reg n c c0 =
                           mips_enc (JumpCmp Lower n (Reg c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpCmp_Equal_Reg n c c0 =
                           mips_enc (JumpCmp Equal n (Reg c) c0)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Jump c =
                           mips_enc (Jump c)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_JumpReg c =
                           mips_enc (JumpReg c)’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Mem_Store a b c =
                    mips_enc (Inst (Mem Store a (Addr b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Mem_Store8 a b c =
                    mips_enc (Inst (Mem Store8 a (Addr b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Mem_Load a b c =
                    mips_enc (Inst (Mem Load a (Addr b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Mem_Load8 a b c =
                    mips_enc (Inst (Mem Load8 a (Addr b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_SubOverflow a b c d =
                    mips_enc (Inst (Arith (SubOverflow a b c d)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_AddOverflow a b c d =
                    mips_enc (Inst (Arith (AddOverflow a b c d)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_AddCarry a b c d =
                    mips_enc (Inst (Arith (AddCarry a b c d)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_LongMul a b c d =
                    mips_enc (Inst (Arith (LongMul a b c d)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_LongDiv a b c d e =
                    mips_enc (Inst (Arith (LongDiv a b c d e)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Div a b c =
                    mips_enc (Inst (Arith (Div a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Shift_Ror a b c =
                    mips_enc (Inst (Arith (Shift Ror a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Shift_Asr a b c =
                    mips_enc (Inst (Arith (Shift Asr a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Shift_Lsr a b c =
                    mips_enc (Inst (Arith (Shift Lsr a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Shift_Lsl a b c =
                    mips_enc (Inst (Arith (Shift Lsl a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Add_Imm a b c =
                    mips_enc (Inst (Arith (Binop Add a b (Imm c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Sub_Imm a b c =
                    mips_enc (Inst (Arith (Binop Sub a b (Imm c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_And_Imm a b c =
                    mips_enc (Inst (Arith (Binop And a b (Imm c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Or_Imm a b c =
                    mips_enc (Inst (Arith (Binop Or a b (Imm c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Xor_Imm a b c =
                    mips_enc (Inst (Arith (Binop Xor a b (Imm c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Add_Reg a b c =
                    mips_enc (Inst (Arith (Binop Add a b (Reg c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Sub_Reg a b c =
                    mips_enc (Inst (Arith (Binop Sub a b (Reg c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_And_Reg a b c =
                    mips_enc (Inst (Arith (Binop And a b (Reg c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Or_Reg a b c =
                    mips_enc (Inst (Arith (Binop Or a b (Reg c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_Arith_Xor_Reg a b c =
                    mips_enc (Inst (Arith (Binop Xor a b (Reg c))))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]

val d1 = CONJ d1 $ Define ‘mips_enc_FPLess a b c =
                    mips_enc (Inst (FP (FPLess a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPLessEqual a b c =
                    mips_enc (Inst (FP (FPLessEqual a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPEqual a b c =
                    mips_enc (Inst (FP (FPEqual a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPAbs a b =
                    mips_enc (Inst (FP (FPAbs a b)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPNeg a b =
                    mips_enc (Inst (FP (FPNeg a b)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPSqrt a b =
                    mips_enc (Inst (FP (FPSqrt a b)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPAdd a b c =
                    mips_enc (Inst (FP (FPAdd a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPSub a b c =
                    mips_enc (Inst (FP (FPSub a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPMul a b c =
                    mips_enc (Inst (FP (FPMul a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPDiv a b c =
                    mips_enc (Inst (FP (FPDiv a b c)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPMov a b =
                    mips_enc (Inst (FP (FPMov a b)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPToInt a b =
                    mips_enc (Inst (FP (FPToInt a b)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘mips_enc_FPFromInt a b =
                    mips_enc (Inst (FP (FPFromInt a b)))’
  |> SIMP_RULE std_ss [mips_enc_thm,cases_defs,APPEND]

val def = mips_enc_thm |> SIMP_RULE std_ss [APPEND] |> SIMP_RULE std_ss [GSYM d1];

val res = CONJUNCTS d1 |> map SPEC_ALL |> map translate;

val res = translate def;

Theorem mips_config_v_thm = translate (mips_config_def |> SIMP_RULE bool_ss
[IN_INSERT,NOT_IN_EMPTY]|> econv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
