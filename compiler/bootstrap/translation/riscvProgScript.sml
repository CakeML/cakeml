(*
  Translate the RISC-V instruction encoder and RISC-V-specific config.
*)
open preamble;
open evaluateTheory
open ml_translatorLib ml_translatorTheory;
open arm8ProgTheory
open riscv_targetTheory riscvTheory;
open inliningLib;

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "riscvProg"

val _ = translation_extends "arm8Prog";
val _ = ml_translatorLib.use_string_type true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "riscvProg");

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

val _ = translate (conv64_RHS integer_wordTheory.WORD_LTi)

val spec_word_bit1 = word_bit |> ISPEC``foo:word32`` |> SPEC``11n``|> SIMP_RULE std_ss [word_bit_test] |> CONV_RULE (wordsLib.WORD_CONV)
val spec_word_bit2 = word_bit |> ISPEC``foo:word64`` |> SPEC``31n``|> SIMP_RULE std_ss [word_bit_test] |> CONV_RULE (wordsLib.WORD_CONV)

val v2w_rw = Q.prove(`
  v2w [P] = if P then 1w else 0w`,
  rw[]>>EVAL_TAC);

val defaults = [riscv_ast_def, riscv_encode_def, Encode_def,
  Itype_def, opc_def, riscv_const32_def, Utype_def, Rtype_def,
  riscv_bop_r_def, riscv_bop_i_def, riscv_encode_fail_def,
  riscv_memop_def, Stype_def, UJtype_def, SBtype_def];

val riscv_enc_thms =
  riscv_enc_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:64 asm``])[]
  |> CONJUNCTS
val riscv_enc1 = el 1 riscv_enc_thms
val riscv_enc2 = el 2 riscv_enc_thms
val riscv_enc3 = el 3 riscv_enc_thms
val riscv_enc4 = el 4 riscv_enc_thms
val riscv_enc5 = el 5 riscv_enc_thms
val riscv_enc6 = el 6 riscv_enc_thms;

val riscv_enc1s =
  riscv_enc1
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:64 inst``]) defaults
  |> CONJUNCTS;

val riscv_enc1_1 = el 1 riscv_enc1s |> wc_simp |> we_simp |> econv

val riscv_enc1_2 = el 2 riscv_enc1s
  |> SIMP_RULE (srw_ss()++LET_ss) ([Q.ISPEC `LIST_BIND` COND_RAND,COND_RATOR,
        LIST_BIND_APPEND,spec_word_bit1,spec_word_bit2]@defaults)
  |> wc_simp |> we_simp |> gconv  |> SIMP_RULE std_ss [SHIFT_ZERO]
  |> csethm 10;

val (binop::shift::rest) = el 3 riscv_enc1s |> SIMP_RULE (srw_ss() ++
  DatatypeSimps.expand_type_quants_ss [``:64 arith``]) [] |> CONJUNCTS;

val (binopreg_aux::binopimm_aux::_) = binop |> SIMP_RULE (srw_ss() ++
  DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``])
  [FORALL_AND_THM] |> CONJUNCTS |> map (SIMP_RULE (srw_ss() ++ LET_ss
  ++ DatatypeSimps.expand_type_quants_ss [``:asm$binop``]) []);

val binopreg = binopreg_aux |> CONJUNCTS |> map(fn th => th |>
  SIMP_RULE (srw_ss()++LET_ss) (defaults) |> wc_simp |> we_simp |>
  gconv |>SIMP_RULE std_ss [SHIFT_ZERO]);

val binopregth = reconstruct_case
  ``riscv_enc (Inst (Arith (Binop b n n0 (Reg n'))))``
  (rand o rator o rator o rator o rand o rand o rand) (map (csethm 2) binopreg)

val binopimm = binopimm_aux |> CONJUNCTS |> map(fn th => th
  |> SIMP_RULE (srw_ss()++LET_ss)
               (Q.ISPEC`LIST_BIND`COND_RAND :: COND_RATOR :: word_mul_def :: defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]);

val binopimmth = reconstruct_case
  ``riscv_enc (Inst (Arith (Binop b n n0 (Imm c))))``
  (rand o rator o rator o rator o rand o rand o rand) binopimm

val binopth = reconstruct_case ``riscv_enc(Inst (Arith (Binop b n n0 r)))``
  (rand o rand o rand o rand) [binopregth,binopimmth];

val shiftths =
  shift
  |> SIMP_RULE(srw_ss()++LET_ss++DatatypeSimps.expand_type_quants_ss[``:shift``])
      (Q.ISPEC`(λ(f,n). P f n)` COND_RAND::
       Q.ISPEC`LIST_BIND`COND_RAND ::
       COND_RATOR ::
       riscv_sh_def ::
      defaults)
  |> CONJUNCTS
  |> map (fn th => th |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]);

val shiftth = reconstruct_case ``riscv_enc(Inst (Arith (Shift s n n0 n1)))``
  (rand o funpow 3 rator o funpow 3 rand) shiftths;

val riscv_enc1_3_aux = binopth :: shiftth :: map (fn th => th |>
  SIMP_RULE (srw_ss()) defaults |> wc_simp |> we_simp |> gconv |>
  SIMP_RULE std_ss [SHIFT_ZERO]) rest;

val riscv_enc1_3 = reconstruct_case ``riscv_enc (Inst (Arith a))``
  (rand o rand o rand) riscv_enc1_3_aux;

val riscv_enc1_4_aux = el 4 riscv_enc1s |> SIMP_RULE (srw_ss() ++
  DatatypeSimps.expand_type_quants_ss [``:64 addr``,``:memop``])
  defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss
  [SHIFT_ZERO] |> CONJUNCTS;

val riscv_enc1_4 = reconstruct_case ``riscv_enc (Inst (Mem m n a))``
  (rand o rand o rand) [reconstruct_case ``riscv_enc (Inst (Mem m n
  (Addr n' c)))`` (rand o rator o rator o rand o rand)
  riscv_enc1_4_aux];

val notw2w = Q.prove(`
  !a. ~w2w a = (-1w ?? (w2w a))`,
  srw_tac[wordsLib.WORD_BIT_EQ_ss][]);

val riscv_enc1_5 = el 5 riscv_enc1s;

val riscv_simp1 = reconstruct_case ``riscv_enc (Inst i)`` (rand o
  rand) [riscv_enc1_1, riscv_enc1_2, riscv_enc1_3, riscv_enc1_4,
  riscv_enc1_5] |> SIMP_RULE std_ss[notw2w, word_2comp_def,
  dimword_32, dimword_20] |> gconv;

val if_eq1w = Q.prove(`
  ((if w2w (c ⋙ m && 1w:word64) = 1w:word20 then 1w:word1 else 0w) && 1w)
  =
  w2w (c ⋙ m && 1w)`,
  rw[]>>fs[]>>
  blastLib.FULL_BBLAST_TAC);

val riscv_simp2 = riscv_enc2 |> SIMP_RULE (srw_ss() ++ LET_ss) (Once
  COND_RAND::COND_RATOR::defaults) |> wc_simp |> we_simp |> gconv |>
  SIMP_RULE std_ss [SHIFT_ZERO, v2w_rw, if_eq1w, word_mul_def] |>
  gconv;

val riscv_enc3_aux = riscv_enc3
  |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss[``:64 reg_imm``])[FORALL_AND_THM]
  |> CONJUNCTS
  |> map (fn th => th
     |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:cmp``])
                  (Q.ISPEC `LIST_BIND` COND_RAND:: COND_RATOR::word_bit_test::defaults)
     |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]);

val riscv_enc3_1 = el 1 riscv_enc3_aux |> SIMP_RULE std_ss [v2w_rw]
val riscv_enc3_2 = el 2 riscv_enc3_aux |> SIMP_RULE std_ss [v2w_rw]

val riscv_enc3_1_th =
  riscv_enc3_1 |> CONJUNCTS
  |> reconstruct_case ``riscv_enc (JumpCmp c n (Reg n') c0)``
     (rand o funpow 3 rator o rand);

val riscv_enc3_2_th =
  riscv_enc3_2 |> CONJUNCTS
  |> reconstruct_case ``riscv_enc (JumpCmp c n (Imm c') c0)``
     (rand o funpow 3 rator o rand);

val riscv_simp3 =
  reconstruct_case ``riscv_enc (JumpCmp c n r c0)`` (rand o rator o rand)
    [riscv_enc3_1_th,riscv_enc3_2_th];

val riscv_simp4 = riscv_enc4 |> SIMP_RULE (srw_ss() ++ LET_ss) (Once
  COND_RAND::COND_RATOR::defaults)|> wc_simp |> we_simp |> gconv |>
  SIMP_RULE std_ss [SHIFT_ZERO, v2w_rw, if_eq1w, word_mul_def] |>
  gconv;

val riscv_simp5 = riscv_enc5 |> SIMP_RULE (srw_ss() ++ LET_ss)
defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss
[SHIFT_ZERO]

val riscv_simp6 = riscv_enc6
  |> SIMP_RULE (srw_ss() ++ LET_ss) (Q.ISPEC`LIST_BIND`COND_RAND :: COND_RATOR ::word_mul_def :: defaults)
  |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val riscv_enc_thm = reconstruct_case ``riscv_enc i`` rand
  [riscv_simp1, riscv_simp2, riscv_simp3, riscv_simp4, riscv_simp5,
  riscv_simp6];

val cases_defs = LIST_CONJ
  [TypeBase.case_def_of “:'a asm$inst”,
   TypeBase.case_def_of “:asm$cmp”,
   TypeBase.case_def_of “:asm$memop”,
   TypeBase.case_def_of “:asm$binop”,
   TypeBase.case_def_of “:ast$shift”,
   TypeBase.case_def_of “:'a asm$arith”,
   TypeBase.case_def_of “:'a asm$addr”,
   TypeBase.case_def_of “:'a asm$reg_imm”,
   TypeBase.case_def_of “:'a asm$asm”];

val d1 = Define ‘riscv_enc_Const n c = riscv_enc (Inst (Const n c))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Skip = riscv_enc (Inst Skip)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Loc n c = riscv_enc (Loc n c)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Call c = riscv_enc (Call c)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_NotTest_Imm n c c0 =
                           riscv_enc (JumpCmp NotTest n (Imm c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_NotLess_Imm n c c0 =
                           riscv_enc (JumpCmp NotLess n (Imm c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_NotLower_Imm n c c0 =
                           riscv_enc (JumpCmp NotLower n (Imm c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_NotEqual_Imm n c c0 =
                           riscv_enc (JumpCmp NotEqual n (Imm c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_Test_Imm n c c0 =
                           riscv_enc (JumpCmp Test n (Imm c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_Less_Imm n c c0 =
                           riscv_enc (JumpCmp Less n (Imm c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_Lower_Imm n c c0 =
                           riscv_enc (JumpCmp Lower n (Imm c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_Equal_Imm n c c0 =
                           riscv_enc (JumpCmp Equal n (Imm c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_NotTest_Reg n c c0 =
                           riscv_enc (JumpCmp NotTest n (Reg c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_NotLess_Reg n c c0 =
                           riscv_enc (JumpCmp NotLess n (Reg c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_NotLower_Reg n c c0 =
                           riscv_enc (JumpCmp NotLower n (Reg c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_NotEqual_Reg n c c0 =
                           riscv_enc (JumpCmp NotEqual n (Reg c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_Test_Reg n c c0 =
                           riscv_enc (JumpCmp Test n (Reg c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_Less_Reg n c c0 =
                           riscv_enc (JumpCmp Less n (Reg c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_Lower_Reg n c c0 =
                           riscv_enc (JumpCmp Lower n (Reg c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpCmp_Equal_Reg n c c0 =
                           riscv_enc (JumpCmp Equal n (Reg c) c0)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Jump c =
                           riscv_enc (Jump c)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_JumpReg c =
                           riscv_enc (JumpReg c)’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Mem_Store a b c =
                    riscv_enc (Inst (Mem Store a (Addr b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Mem_Store8 a b c =
                    riscv_enc (Inst (Mem Store8 a (Addr b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Mem_Load a b c =
                    riscv_enc (Inst (Mem Load a (Addr b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Mem_Load8 a b c =
                    riscv_enc (Inst (Mem Load8 a (Addr b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_SubOverflow a b c d =
                    riscv_enc (Inst (Arith (SubOverflow a b c d)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_AddOverflow a b c d =
                    riscv_enc (Inst (Arith (AddOverflow a b c d)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_AddCarry a b c d =
                    riscv_enc (Inst (Arith (AddCarry a b c d)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_LongMul a b c d =
                    riscv_enc (Inst (Arith (LongMul a b c d)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_LongDiv a b c d e =
                    riscv_enc (Inst (Arith (LongDiv a b c d e)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Div a b c =
                    riscv_enc (Inst (Arith (Div a b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Shift_Ror a b c =
                    riscv_enc (Inst (Arith (Shift Ror a b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Shift_Asr a b c =
                    riscv_enc (Inst (Arith (Shift Asr a b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Shift_Lsr a b c =
                    riscv_enc (Inst (Arith (Shift Lsr a b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Shift_Lsl a b c =
                    riscv_enc (Inst (Arith (Shift Lsl a b c)))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Add_Imm a b c =
                    riscv_enc (Inst (Arith (Binop Add a b (Imm c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Sub_Imm a b c =
                    riscv_enc (Inst (Arith (Binop Sub a b (Imm c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_And_Imm a b c =
                    riscv_enc (Inst (Arith (Binop And a b (Imm c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Or_Imm a b c =
                    riscv_enc (Inst (Arith (Binop Or a b (Imm c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Xor_Imm a b c =
                    riscv_enc (Inst (Arith (Binop Xor a b (Imm c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Add_Reg a b c =
                    riscv_enc (Inst (Arith (Binop Add a b (Reg c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Sub_Reg a b c =
                    riscv_enc (Inst (Arith (Binop Sub a b (Reg c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_And_Reg a b c =
                    riscv_enc (Inst (Arith (Binop And a b (Reg c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Or_Reg a b c =
                    riscv_enc (Inst (Arith (Binop Or a b (Reg c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘riscv_enc_Arith_Xor_Reg a b c =
                    riscv_enc (Inst (Arith (Binop Xor a b (Reg c))))’
  |> SIMP_RULE std_ss [riscv_enc_thm,cases_defs,APPEND]

val def = riscv_enc_thm |> SIMP_RULE std_ss [APPEND] |> SIMP_RULE std_ss [GSYM d1];

val res = CONJUNCTS d1 |> map SPEC_ALL |> map translate;

val res = translate def;

Theorem riscv_config_v_thm = translate (riscv_config_def |> SIMP_RULE bool_ss [IN_INSERT, NOT_IN_EMPTY]|> econv);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
