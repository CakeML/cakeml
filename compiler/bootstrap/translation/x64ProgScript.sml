(*
  Translate the x64 instruction encoder and x64-specific config.
*)
open preamble;
open evaluateTheory
open ml_translatorLib ml_translatorTheory;
open to_target64ProgTheory
open x64_targetTheory x64Theory;
open inliningLib;

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "x64Prog"

val _ = translation_extends "to_target64Prog";
val _ = ml_translatorLib.use_string_type true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "x64Prog");

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
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val v2w_rw = Q.prove(`
  v2w [P] = if P then 1w else 0w`,
  rw[]>>EVAL_TAC);

val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)

val zreg2num_totalnum2zerg = Q.prove(`
  Zreg2num (total_num2Zreg n) = if n < 16 then n else 0`,
  EVAL_TAC>>IF_CASES_TAC>>fs[Zreg2num_num2Zreg]);

val zreg2num_num2zerg_MOD8 = Q.prove(`
  Zreg2num (num2Zreg (n MOD 8)) = n MOD 8`,
  `n MOD 8 < 8` by fs[] >>
  `n MOD 8 < 16` by DECIDE_TAC>>
  fs[Zreg2num_num2Zreg]);

val n2w_MOD8_simps = Q.prove(`
  n2w (n MOD 8) :word4 >>> 3 = 0w /\
  (n2w (n MOD 8) :word4 && 7w) = n2w (n MOD 8) ∧
  BITS 3 0 (n MOD 8) =n MOD 8`,
  FULL_BBLAST_TAC>>
  `n MOD 8 < 8` by fs[]>>
  `n MOD 8 = 0 \/
  n MOD 8 = 1 \/
  n MOD 8 = 2 \/
  n MOD 8 = 3 \/
  n MOD 8 = 4 \/
  n MOD 8 = 5 \/
  n MOD 8 = 6 \/
  n MOD 8 = 7` by DECIDE_TAC>>
  fs[]);

val Zbinop_name2num_x64_sh = Q.prove(`
  ∀s.Zbinop_name2num (x64_sh s) =
  case s of
    Lsl => 12
  | Lsr => 13
  | Asr => 15
  | Ror => 9`,  Cases>>EVAL_TAC);

val x64_sh_notZtest = Q.prove(`
  ∀s.(x64_sh s) ≠ Ztest `,Cases>>EVAL_TAC);

val exh_if_collapse = Q.prove(`
  ((if P then Ztest else Zcmp) = Ztest) ⇔ P `,rw[]);

val is_rax_zr_thm = Q.prove(`
  is_rax (Zr (total_num2Zreg n)) ⇔
  n = 0 ∨ n ≥ 16`,
  rw[is_rax_def]>>
  EVAL_TAC>>rw[]>>
  rpt(Cases_on`n`>>EVAL_TAC>>fs[]>>
  Cases_on`n'`>>EVAL_TAC>>fs[]))

(* commute list case, option case and if *)
val case_ifs = Q.prove(`
  ((case
    if P then
      l1
    else l2
  of
    [] => A
  | ls => B ls) = if P then case l1 of [] => A | ls => B ls else case l2 of [] => A | ls => B ls)`,rw[])

val case_ifs2 = Q.prove(`
  ((case
    if P then
      SOME (a,b,c)
    else NONE
  of
    NONE => A
  | SOME (a,b,c) => B a b c) = if P then B a b c else A)
  `,
  rw[])

val if_neq = Q.prove(`
  (if P then [x] else []) ≠ [] ⇔ P`,
  rw[])

val fconv = SIMP_RULE (srw_ss()) [SHIFT_ZERO,case_ifs,case_ifs2,if_neq]

val defaults = [x64_ast_def, x64_encode_def, encode_def,
  e_gen_rm_reg_def, e_ModRM_def, e_opsize_def, e_imm32_def,
  rex_prefix_def, x64_dec_fail_def, e_opc_def, e_rax_imm_def,
  e_rm_imm_def, asmSemTheory.is_test_def, x64_cmp_def,
  e_opsize_imm_def, e_imm8_def, e_rm_imm8_def, not_byte_def,
  e_imm16_def, e_imm64_def, Zsize_width_def, x64_bop_def,
  zreg2num_totalnum2zerg, e_imm_8_32_def, Zbinop_name2num_x64_sh,
  x64_sh_notZtest, exh_if_collapse, is_rax_zr_thm]

val x64_enc_thms =
  x64_enc_def
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:64 asm``])[]
  |> CONJUNCTS
val x64_enc1 = el 1 x64_enc_thms
val x64_enc2 = el 2 x64_enc_thms
val x64_enc3 = el 3 x64_enc_thms
val x64_enc4 = el 4 x64_enc_thms
val x64_enc5 = el 5 x64_enc_thms
val x64_enc6 = el 6 x64_enc_thms

val x64_enc1s = x64_enc1 |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:64 inst``]) defaults |> CONJUNCTS

val x64_enc1_1 = el 1 x64_enc1s

val simp_rw = Q.prove(`
  (if ((1w:word4 && n2w (if n < 16 then n else 0) ⋙ 3) = 1w) then 1w else 0w:word4) =
  (1w && n2w (if n < 16 then n else 0) ⋙ 3)`,
  rw[]>>fs[]>>
  blastLib.FULL_BBLAST_TAC);

val x64_enc1_2 = el 2 x64_enc1s |> wc_simp |> we_simp |> gconv |>
 bconv |> SIMP_RULE std_ss [SHIFT_ZERO,Q.ISPEC`Zsize_CASE`
 COND_RAND,COND_RATOR,Zsize_case_def] |> fconv |> SIMP_RULE
 std_ss[Once COND_RAND,simp_rw] |> csethm 2

val (binop::shift::rest) = el 3 x64_enc1s |> SIMP_RULE (srw_ss() ++
DatatypeSimps.expand_type_quants_ss [``:64 arith``]) [] |> CONJUNCTS

val (binopreg_aux::binopimm_aux::_) = binop |> SIMP_RULE (srw_ss() ++
DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``])
[FORALL_AND_THM] |> CONJUNCTS |> map (SIMP_RULE (srw_ss() ++ LET_ss ++
DatatypeSimps.expand_type_quants_ss [``:binop``]) [])

(* TODO: simplify further? *) val binopreg = binopreg_aux |> CONJUNCTS
|> map(fn th => th |> SIMP_RULE (srw_ss()++LET_ss) ((Q.ISPEC
`x64_encode` COND_RAND) ::defaults) |> wc_simp |> we_simp |> gconv |>
bconv |> fconv)

val binopregth = reconstruct_case ``x64_enc (Inst (Arith (Binop b n n0
(Reg n'))))`` (rand o rator o rator o rator o rand o rand o rand) (map
(csethm 2) binopreg)

val binopimm = binopimm_aux |> CONJUNCTS |> map(fn th => th |>
SIMP_RULE (srw_ss()++LET_ss) ((Q.ISPEC `x64_encode` COND_RAND)
::defaults) |> wc_simp |> we_simp |> gconv |> bconv |> fconv)

val binopimmth = reconstruct_case ``x64_enc (Inst (Arith (Binop b n n0
(Imm c))))`` (rand o rator o rator o rator o rand o rand o rand) (map
(csethm 3) binopimm)

val binopth = reconstruct_case ``x64_enc(Inst (Arith (Binop b n n0
r)))`` (rand o rand o rand o rand) [binopregth,binopimmth]

val shiftths =
  shift
  |> SIMP_RULE(srw_ss()++LET_ss++DatatypeSimps.expand_type_quants_ss[``:shift``])
      (x64_sh_def ::
      defaults)
  |> CONJUNCTS
  |> map (fn th => th |> wc_simp |> we_simp |> gconv
  |> bconv |> fconv |> csethm 3)

val shiftth = reconstruct_case ``x64_enc(Inst (Arith (Shift s n n0 n1)))``
  (rand o funpow 3 rator o funpow 3 rand) shiftths

val x64_enc1_3_aux = binopth :: shiftth:: map (fn th => th |>
SIMP_RULE (srw_ss()) defaults |> wc_simp |> we_simp |> gconv |> bconv
|> fconv |> csethm 3) rest

val x64_enc1_3 = reconstruct_case ``x64_enc (Inst (Arith a))`` (rand o
rand o rand) x64_enc1_3_aux

val x64_enc1_4_aux = el 4 x64_enc1s |> SIMP_RULE (srw_ss() ++
DatatypeSimps.expand_type_quants_ss [``:64 addr``,``:memop``])
defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss
[SHIFT_ZERO] |> CONJUNCTS

(*TODO: can commute the NONE and if *)
val x64_enc1_4 = reconstruct_case ``x64_enc (Inst (Mem m n a))`` (rand
o rand o rand) [reconstruct_case ``x64_enc (Inst (Mem m n (Addr n'
c)))`` (rand o rator o rator o rand o rand) (map (csethm 2 o fconv o
bconv) x64_enc1_4_aux)]

(* FP *)
val fp_defaults = [encode_sse_def,xmm_mem_to_rm_def,encode_sse_binop_def]

val x64_enc1_5_aux = el 5 x64_enc1s |> SIMP_RULE (srw_ss() ++
  DatatypeSimps.expand_type_quants_ss [``:fp``]) (defaults @
  fp_defaults) |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss
  [SHIFT_ZERO,zreg2num_num2zerg_MOD8,n2w_MOD8_simps,w2w_n2w,
  dimindex_8,dimindex_4,pair_case_def,v2w_rw] |> gconv |> SIMP_RULE
  (srw_ss()) [] |> CONJUNCTS

val x64_enc1_5 = reconstruct_case ``x64_enc (Inst (FP f))`` (rand o
  rand o rand) x64_enc1_5_aux

val x64_simp1 = reconstruct_case ``x64_enc (Inst i)`` (rand o rand)
  [x64_enc1_1,x64_enc1_2,x64_enc1_3,x64_enc1_4,x64_enc1_5] |>
  SIMP_RULE std_ss [Q.ISPEC `Zbinop_name2num`
  COND_RAND,Zbinop_name2num_thm]

val x64_simp2 = x64_enc2 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |>
  wc_simp |> we_simp |> gconv |> bconv |> fconv

val x64_enc3_aux = x64_enc3
  |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss[``:64 reg_imm``])[FORALL_AND_THM]
  |> CONJUNCTS
  |> map (fn th => th
     |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:cmp``])
                  (Q.ISPEC `LIST_BIND` COND_RAND:: COND_RATOR::word_bit_test::defaults)
     |> wc_simp |> we_simp |> gconv)

val x64_enc3_1 = el 1 x64_enc3_aux
val x64_enc3_2 = el 2 x64_enc3_aux |> SIMP_RULE (srw_ss()) [word_mul_def, Q.ISPEC `w2n` COND_RAND] |> gconv

val x64_enc3_1_th =
  x64_enc3_1 |> CONJUNCTS |> map (fconv o bconv)
  |> reconstruct_case ``x64_enc (JumpCmp c n (Reg n') c0)``
     (rand o funpow 3 rator o rand)

(*bconv takes too long on this one*)
fun avoidp t =
if wordsSyntax.is_word_le t then
  let val (l,r) = wordsSyntax.dest_word_compare t in
    l ~~ ``0xFFFFFFFF80000000w:word64``
  end
else if is_conj t then
  let val(l,r) = dest_conj t in
    avoidp l andalso avoidp r
  end
else
  false

val case_append = Q.prove(`
  (case a ++ [b;c] ++ d of [] => x | ls => ls) = a++[b;c]++d`,
  EVERY_CASE_TAC>>fs[]);

val x64_enc3_2_th =
  x64_enc3_2 |> CONJUNCTS
  |> map (csethm 2 o SIMP_RULE (srw_ss()) [case_append] o fconv o bconv_gen false avoidp)
  |> reconstruct_case ``x64_enc (JumpCmp c n (Imm c') c0)``
     (rand o funpow 3 rator o rand)

val x64_simp3 =
  reconstruct_case ``x64_enc (JumpCmp c n r c0)`` (rand o rator o rand)
    [x64_enc3_1_th,x64_enc3_2_th]

val x64_simp4 = x64_enc4 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val case_append2 = Q.prove(`
  (case a ++ [b;c] of [] => e | ls => ls) = a++[b;c]`,
  EVERY_CASE_TAC>>fs[]);

val x64_simp5 = x64_enc5 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |>
wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> bconv
|> fconv |> SIMP_RULE (srw_ss())[case_append2]

val x64_simp6 = x64_enc6 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |>
wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |>bconv
|> csethm 2

val x64_enc_thm = reconstruct_case ``x64_enc i`` rand
[x64_simp1,x64_simp2,x64_simp3,x64_simp4,x64_simp5,x64_simp6]

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

val d1 = Define ‘x64_enc_Const n c = x64_enc (Inst (Const n c))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Skip = x64_enc (Inst Skip)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Loc n c = x64_enc (Loc n c)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Call c = x64_enc (Call c)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_NotTest_Imm n c c0 =
                           x64_enc (JumpCmp NotTest n (Imm c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_NotLess_Imm n c c0 =
                           x64_enc (JumpCmp NotLess n (Imm c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_NotLower_Imm n c c0 =
                           x64_enc (JumpCmp NotLower n (Imm c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_NotEqual_Imm n c c0 =
                           x64_enc (JumpCmp NotEqual n (Imm c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_Test_Imm n c c0 =
                           x64_enc (JumpCmp Test n (Imm c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_Less_Imm n c c0 =
                           x64_enc (JumpCmp Less n (Imm c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_Lower_Imm n c c0 =
                           x64_enc (JumpCmp Lower n (Imm c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_Equal_Imm n c c0 =
                           x64_enc (JumpCmp Equal n (Imm c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_NotTest_Reg n c c0 =
                           x64_enc (JumpCmp NotTest n (Reg c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_NotLess_Reg n c c0 =
                           x64_enc (JumpCmp NotLess n (Reg c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_NotLower_Reg n c c0 =
                           x64_enc (JumpCmp NotLower n (Reg c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_NotEqual_Reg n c c0 =
                           x64_enc (JumpCmp NotEqual n (Reg c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_Test_Reg n c c0 =
                           x64_enc (JumpCmp Test n (Reg c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_Less_Reg n c c0 =
                           x64_enc (JumpCmp Less n (Reg c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_Lower_Reg n c c0 =
                           x64_enc (JumpCmp Lower n (Reg c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpCmp_Equal_Reg n c c0 =
                           x64_enc (JumpCmp Equal n (Reg c) c0)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Jump c =
                           x64_enc (Jump c)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_JumpReg c =
                           x64_enc (JumpReg c)’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Mem_Store a b c =
                    x64_enc (Inst (Mem Store a (Addr b c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Mem_Store8 a b c =
                    x64_enc (Inst (Mem Store8 a (Addr b c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Mem_Load a b c =
                    x64_enc (Inst (Mem Load a (Addr b c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Mem_Load8 a b c =
                    x64_enc (Inst (Mem Load8 a (Addr b c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_SubOverflow a c d =
                    x64_enc (Inst (Arith (SubOverflow a a c d)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_AddOverflow a c d =
                    x64_enc (Inst (Arith (AddOverflow a a c d)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_AddCarry a c d =
                    x64_enc (Inst (Arith (AddCarry a a c d)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_LongMul a =
                    x64_enc (Inst (Arith (LongMul a a a a)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_LongDiv a =
                    x64_enc (Inst (Arith (LongDiv a a a a a)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Div a b c =
                    x64_enc (Inst (Arith (Div a b c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Shift_Ror a c =
                    x64_enc (Inst (Arith (Shift Ror a a c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Shift_Asr a c =
                    x64_enc (Inst (Arith (Shift Asr a a c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Shift_Lsr a c =
                    x64_enc (Inst (Arith (Shift Lsr a a c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Shift_Lsl a c =
                    x64_enc (Inst (Arith (Shift Lsl a a c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Add_Imm a c =
                    x64_enc (Inst (Arith (Binop Add a a (Imm c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Sub_Imm a c =
                    x64_enc (Inst (Arith (Binop Sub a a (Imm c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_And_Imm a c =
                    x64_enc (Inst (Arith (Binop And a a (Imm c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Or_Imm a c =
                    x64_enc (Inst (Arith (Binop Or a a (Imm c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Xor_Imm a c =
                    x64_enc (Inst (Arith (Binop Xor a a (Imm c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Add_Reg a c =
                    x64_enc (Inst (Arith (Binop Add a a (Reg c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Sub_Reg a c =
                    x64_enc (Inst (Arith (Binop Sub a a (Reg c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_And_Reg a c =
                    x64_enc (Inst (Arith (Binop And a a (Reg c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Or_Reg a b c =
                    x64_enc (Inst (Arith (Binop Or a b (Reg c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_Arith_Xor_Reg a c =
                    x64_enc (Inst (Arith (Binop Xor a a (Reg c))))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]

val d1 = CONJ d1 $ Define ‘x64_enc_FPLess a b c =
                    x64_enc (Inst (FP (FPLess a b c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPLessEqual a b c =
                    x64_enc (Inst (FP (FPLessEqual a b c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPEqual a b c =
                    x64_enc (Inst (FP (FPEqual a b c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPAbs a b =
                    x64_enc (Inst (FP (FPAbs a b)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPNeg a b =
                    x64_enc (Inst (FP (FPNeg a b)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPSqrt a b =
                    x64_enc (Inst (FP (FPSqrt a b)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPAdd a c =
                    x64_enc (Inst (FP (FPAdd a a c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPSub a c =
                    x64_enc (Inst (FP (FPSub a a c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPMul a c =
                    x64_enc (Inst (FP (FPMul a a c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPDiv a c =
                    x64_enc (Inst (FP (FPDiv a a c)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPMov a b =
                    x64_enc (Inst (FP (FPMov a b)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPMovToReg a b =
                    x64_enc (Inst (FP (FPMovToReg a a b)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPMovFromReg a b =
                    x64_enc (Inst (FP (FPMovFromReg a b b)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPToInt a b =
                    x64_enc (Inst (FP (FPToInt a b)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]
val d1 = CONJ d1 $ Define ‘x64_enc_FPFromInt a b =
                    x64_enc (Inst (FP (FPFromInt a b)))’
  |> SIMP_RULE std_ss [x64_enc_thm,cases_defs,APPEND]

val def = x64_enc_thm |> SIMP_RULE std_ss [APPEND] |> SIMP_RULE std_ss [GSYM d1];

val res = CONJUNCTS d1 |> map SPEC_ALL |> map translate;

val res = translate def;

Theorem x64_config_v_thm = translate (x64_config_def |> gconv);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
