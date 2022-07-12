(*
  Translate the ARMv7 instruction encoder and ARMv7-specific config.
*)
open preamble;
open evaluateTheory
open ml_translatorLib ml_translatorTheory;
open to_target32ProgTheory
open arm7_targetTheory armTheory;
open inliningLib;
local open to_target32ProgTheory in end;

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "arm7Prog"

val _ = translation_extends "to_target32Prog";
val _ = ml_translatorLib.use_string_type true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "arm7Prog");

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

val v2w_rw = Q.prove(`
  v2w [P] = if P then 1w else 0w`,
  rw[]>>EVAL_TAC);

val notw = Q.prove(`
  !a. ~a = (-1w ?? a)`,
  srw_tac[wordsLib.WORD_BIT_EQ_ss][]);

val if_ARM_BadCode = Q.prove(`
  (case
  (if P then
     ARM c
  else BadCode d)
  of
    ARM w => f w
  | BadCode w => g w
  | Thumb w => h w
  | Thumb2 w => i w
  | ThumbEE w => j w
  ) =
  if P then f c else g d`,
    rw[]);

(*val IS_SOME_rw = Q.prove(`
  (if IS_SOME A then B else C) =
    case A of
    SOME v => B
  | NONE => C`,
  Cases_on`A`>>rw[IS_SOME_DEF]);

(* TODO? more Manual rewrites to get rid of MachineCode type, which probably isn't that expensive *)

val exh_machine_code = Q.prove(`
∀v f.
(case
  case v of
    (N,imms,immr) =>
      ARM8 (f N imms immr)
of
  ARM8 w => g w
| BadCode v3 => h) =
  case v of (N,imms,immr) =>
  g( f N imms immr)`,
  rw[]>>PairCases_on`v`>>rw[])

val LIST_BIND_option = Q.prove(`
  LIST_BIND (case P of NONE => A | SOME v => B v) f =
  case P of NONE => LIST_BIND A f | SOME v => LIST_BIND (B v) f`,
  Cases_on`P`>>rw[]);

val LIST_BIND_pair = Q.prove(`
  LIST_BIND (case P of (l,r) => A l r) f =
  case P of (l,r) => LIST_BIND (A l r) f`,
  Cases_on`P`>>rw[]);

val notw = Q.prove(`
  !a. ~a = (-1w ?? a)`,
  srw_tac[wordsLib.WORD_BIT_EQ_ss][]);
*)
val defaults = [arm7_encode_def,arm7_encode1_def,encode_def,e_data_def,EncodeImmShift_def,v2w_rw,e_load_def,arm7_encode_fail_def,e_multiply_def,e_branch_def,Aligned_def,Align_def,e_store_def];

val finish = fn th => th |> wc_simp |> we_simp |> SIMP_RULE (std_ss) [SHIFT_ZERO,notw]

val arm7_enc_thms =
  arm7_enc_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> SIMP_RULE (srw_ss()) defaults
  |> CONJUNCTS
  |> Array.fromList

fun lookup_at i =
  Array.sub(arm7_enc_thms,i-1)

fun replace_at i f =
  let val th = Array.sub(arm7_enc_thms,i-1)
      val fth = f th in
    Array.update(arm7_enc_thms,i-1,fth) ;
    fth
  end

val arm7_enc1 = replace_at 1 (fn th => th |>finish|> SIMP_RULE (srw_ss()) [] )

val arm7_enc2 = replace_at 2 (fn th => th |> finish |> gconv)

val arm7_enc3 = replace_at 3 (fn th => th |> Q.GEN `bop` |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:binop``]) (LET_THM::arm7_bop_def::defaults) |> finish |> CONJUNCTS
|> reconstruct_case ``arm7_enc (Inst (Arith (Binop bop r1 r2 (Reg r3))))`` (rand o rator o rator o rator o rand o rand o rand))

(* TODO: Uses THE (EncodeARMImmediate)*)
val arm7_enc4 = replace_at 4 (fn th => th |> Q.GEN `bop` |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:binop``]) (arm7_bop_def::defaults) |> finish
|> SIMP_RULE (srw_ss())[word_2comp_def]
|> CONJUNCTS
|> reconstruct_case ``arm7_enc (Inst (Arith (Binop bop r1 r2 (Imm i))))`` (rand o rator o rator o rator o rand o rand o rand))

val arm7_enc5 = replace_at 5 (fn th => th |> Q.GEN `sh` |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:shift``]) (LET_THM::arm7_sh_def::defaults) |> finish
|> SIMP_RULE (srw_ss())[word_2comp_def]
|> CONJUNCTS
|> reconstruct_case ``arm7_enc (Inst (Arith (Shift s r1 r2 n)))`` (rand o rator o rator o rator o rand o rand o rand))

val arm7_enc7 = replace_at 7 (fn th => th |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])

val arm7_enc9 = replace_at 9 (fn th => th |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])

val arm7_enc10 = replace_at 10 (fn th => th |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])
val arm7_enc11 = replace_at 11 (fn th => th |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])

val arm7_enc12 = replace_at 12 (fn th => th |> SIMP_RULE (srw_ss())
  [WORD_LS,word_mul_def, Q.ISPEC`MachineCode_CASE`COND_RAND,
   MachineCode_case_def,COND_RATOR] |> SIMP_RULE std_ss[Once COND_RAND]
  |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])

val arm7_enc13 = replace_at 13 (fn th => th |> SIMP_RULE (srw_ss())
  [WORD_LS,word_mul_def,Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def,COND_RATOR,LET_THM] |> SIMP_RULE std_ss[Once
  COND_RAND] |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])

val arm7_enc14 = replace_at 14 (fn th => th |> SIMP_RULE (srw_ss())
  [WORD_LS,word_mul_def,Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def,COND_RATOR,LET_THM] |> SIMP_RULE std_ss[Once
  COND_RAND] |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])

val arm7_enc15 = replace_at 15 (fn th => th |> SIMP_RULE (srw_ss())
  [WORD_LS,word_mul_def,Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def,COND_RATOR,LET_THM] |> SIMP_RULE std_ss[Once
  COND_RAND] |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])

(* FP *)
val fp_defaults = [arm7_vfp_cmp_def,e_vfp_def,EncodeVFPReg_def]@defaults

val arm7_enc16_to_30 = map (fn i => replace_at i (fn th => th |>
  (SIMP_RULE (srw_ss()) fp_defaults) |> finish |> SIMP_RULE
  (srw_ss())[word_2comp_def]))
  [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

val arm7_enc31 = replace_at 32 (fn th => th |> SIMP_RULE (srw_ss())
  [WORD_LS,word_mul_def,Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def,COND_RATOR,LET_THM] |> finish |> SIMP_RULE
  (srw_ss())[word_2comp_def])

val arm7_enc32 = replace_at 33 (fn th => th |> Q.GEN`cmp` |> SIMP_RULE
  (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:cmp``])
  [arm7_cmp_def,Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def,COND_RATOR,LET_THM] |> finish |> CONJUNCTS |>
  map (SIMP_RULE (srw_ss())[word_2comp_def] ) |> reconstruct_case
  ``arm7_enc (JumpCmp cmp r1 (Reg r2) a)`` (rand o funpow 3 rator o
  rand) )

val arm7_enc33 = replace_at 34 (fn th => th |> Q.GEN`cmp` |> SIMP_RULE
  (srw_ss() ++ LET_ss ++
  DatatypeSimps.expand_type_quants_ss[``:cmp``])
  [arm7_cmp_def,Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def,COND_RATOR,LET_THM] |> finish |> CONJUNCTS |>
  map (SIMP_RULE (srw_ss())[word_2comp_def]) |> reconstruct_case
  ``arm7_enc (JumpCmp cmp r (Imm i) a)`` (rand o funpow 3 rator o
  rand) )

val arm7_enc34 = replace_at 35 (fn th => th |> SIMP_RULE (srw_ss())
  [WORD_LS, word_mul_def, Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def, COND_RATOR] |> finish |> SIMP_RULE
  (srw_ss())[word_2comp_def])

val arm7_enc35 = replace_at 36 (fn th => th |> SIMP_RULE (srw_ss())
  [WORD_LS, word_mul_def, Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def, COND_RATOR] |> finish |> SIMP_RULE
  (srw_ss())[word_2comp_def])

val arm7_enc36 = replace_at 37 (fn th => th |> SIMP_RULE (srw_ss())
  [WORD_LO, word_mul_def, Q.ISPEC`MachineCode_CASE`COND_RAND,
  MachineCode_case_def, COND_RATOR] |> SIMP_RULE std_ss[Once
  COND_RAND] |> finish |> SIMP_RULE (srw_ss())[word_2comp_def])

val arm7_enc_thm =
  List.tabulate (37, fn i => Array.sub(arm7_enc_thms,i)) |> LIST_CONJ

val _ = translate (EncodeARMImmediate_def |> SIMP_RULE (srw_ss())
  [Ntimes EncodeARMImmediate_aux_def 16] |> finish |> SIMP_RULE
  (srw_ss()) [word_2comp_def])

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

val d1 = Define ‘arm7_enc_Const n c = arm7_enc (Inst (Const n c))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Skip = arm7_enc (Inst Skip)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Loc n c = arm7_enc (Loc n c)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Call c = arm7_enc (Call c)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_NotTest_Imm n c c0 =
                           arm7_enc (JumpCmp NotTest n (Imm c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_NotLess_Imm n c c0 =
                           arm7_enc (JumpCmp NotLess n (Imm c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_NotLower_Imm n c c0 =
                           arm7_enc (JumpCmp NotLower n (Imm c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_NotEqual_Imm n c c0 =
                           arm7_enc (JumpCmp NotEqual n (Imm c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_Test_Imm n c c0 =
                           arm7_enc (JumpCmp Test n (Imm c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_Less_Imm n c c0 =
                           arm7_enc (JumpCmp Less n (Imm c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_Lower_Imm n c c0 =
                           arm7_enc (JumpCmp Lower n (Imm c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_Equal_Imm n c c0 =
                           arm7_enc (JumpCmp Equal n (Imm c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_NotTest_Reg n c c0 =
                           arm7_enc (JumpCmp NotTest n (Reg c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_NotLess_Reg n c c0 =
                           arm7_enc (JumpCmp NotLess n (Reg c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_NotLower_Reg n c c0 =
                           arm7_enc (JumpCmp NotLower n (Reg c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_NotEqual_Reg n c c0 =
                           arm7_enc (JumpCmp NotEqual n (Reg c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_Test_Reg n c c0 =
                           arm7_enc (JumpCmp Test n (Reg c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_Less_Reg n c c0 =
                           arm7_enc (JumpCmp Less n (Reg c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_Lower_Reg n c c0 =
                           arm7_enc (JumpCmp Lower n (Reg c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpCmp_Equal_Reg n c c0 =
                           arm7_enc (JumpCmp Equal n (Reg c) c0)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Jump c =
                           arm7_enc (Jump c)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_JumpReg c =
                           arm7_enc (JumpReg c)’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Mem_Store a b c =
                    arm7_enc (Inst (Mem Store a (Addr b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Mem_Store8 a b c =
                    arm7_enc (Inst (Mem Store8 a (Addr b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Mem_Load a b c =
                    arm7_enc (Inst (Mem Load a (Addr b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Mem_Load8 a b c =
                    arm7_enc (Inst (Mem Load8 a (Addr b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_SubOverflow a b c d =
                    arm7_enc (Inst (Arith (SubOverflow a b c d)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_AddOverflow a b c d =
                    arm7_enc (Inst (Arith (AddOverflow a b c d)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_AddCarry a b c d =
                    arm7_enc (Inst (Arith (AddCarry a b c d)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_LongMul a b c d =
                    arm7_enc (Inst (Arith (LongMul a b c d)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_LongDiv a b c d e =
                    arm7_enc (Inst (Arith (LongDiv a b c d e)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Div a b c =
                    arm7_enc (Inst (Arith (Div a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Shift_Ror a b c =
                    arm7_enc (Inst (Arith (Shift Ror a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Shift_Asr a b c =
                    arm7_enc (Inst (Arith (Shift Asr a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Shift_Lsr a b c =
                    arm7_enc (Inst (Arith (Shift Lsr a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Shift_Lsl a b c =
                    arm7_enc (Inst (Arith (Shift Lsl a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Add_Imm a b c =
                    arm7_enc (Inst (Arith (Binop Add a b (Imm c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Sub_Imm a b c =
                    arm7_enc (Inst (Arith (Binop Sub a b (Imm c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_And_Imm a b c =
                    arm7_enc (Inst (Arith (Binop And a b (Imm c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Or_Imm a b c =
                    arm7_enc (Inst (Arith (Binop Or a b (Imm c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Xor_Imm a b c =
                    arm7_enc (Inst (Arith (Binop Xor a b (Imm c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Add_Reg a b c =
                    arm7_enc (Inst (Arith (Binop Add a b (Reg c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Sub_Reg a b c =
                    arm7_enc (Inst (Arith (Binop Sub a b (Reg c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_And_Reg a b c =
                    arm7_enc (Inst (Arith (Binop And a b (Reg c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Or_Reg a b c =
                    arm7_enc (Inst (Arith (Binop Or a b (Reg c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_Arith_Xor_Reg a b c =
                    arm7_enc (Inst (Arith (Binop Xor a b (Reg c))))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]

val d1 = CONJ d1 $ Define ‘arm7_enc_FPLess a b c =
                    arm7_enc (Inst (FP (FPLess a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPLessEqual a b c =
                    arm7_enc (Inst (FP (FPLessEqual a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPEqual a b c =
                    arm7_enc (Inst (FP (FPEqual a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPAbs a b =
                    arm7_enc (Inst (FP (FPAbs a b)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPNeg a b =
                    arm7_enc (Inst (FP (FPNeg a b)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPSqrt a b =
                    arm7_enc (Inst (FP (FPSqrt a b)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPAdd a b c =
                    arm7_enc (Inst (FP (FPAdd a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPSub a b c =
                    arm7_enc (Inst (FP (FPSub a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPMul a b c =
                    arm7_enc (Inst (FP (FPMul a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPDiv a b c =
                    arm7_enc (Inst (FP (FPDiv a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPMov a b =
                    arm7_enc (Inst (FP (FPMov a b)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPToInt a b =
                    arm7_enc (Inst (FP (FPToInt a b)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPFromInt a b =
                    arm7_enc (Inst (FP (FPFromInt a b)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPMovToReg a b c =
                    arm7_enc (Inst (FP (FPMovToReg a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPMovFromReg a b c =
                    arm7_enc (Inst (FP (FPMovFromReg a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘arm7_enc_FPFma a b c =
                    arm7_enc (Inst (FP (FPFma a b c)))’
  |> SIMP_RULE std_ss [arm7_enc_thm,cases_defs,APPEND]

val def = arm7_enc_thm |> SIMP_RULE std_ss [APPEND] |> SIMP_RULE std_ss [GSYM d1];

val res = CONJUNCTS d1 |> map SPEC_ALL |> map translate;

val res = translate def;

val res = translate (arm7_config_def |> SIMP_RULE std_ss[valid_immediate_def] |> gconv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
