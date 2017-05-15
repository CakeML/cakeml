open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open compiler64ProgTheory
open x64_targetTheory x64Theory;

val _ = new_theory "x64Prog"

val _ = translation_extends "compiler64Prog";

val RW = REWRITE_RULE

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

val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)

val _ = register_type``:64 asm_config``

val word_bit_thm = Q.prove(
  `!n w. word_bit n w = ((w && n2w (2 ** n)) <> 0w)`,
  simp [GSYM wordsTheory.word_1_lsl]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
  \\ eq_tac
  \\ rw []
  >- (qexists_tac `n` \\ simp [DECIDE ``0 < a /\ n <= a - 1n ==> n < a``])
  \\ `i = n` by decide_tac
  \\ fs [])

(* word_bit can be inlined into encode (current choice), or translated into a function
val foo = translate ((INST_TYPE[alpha|->``:4``]o SPEC_ALL )th)
*)

(* word_concat *)
val wc_simp = CONV_RULE (wordsLib.WORD_CONV) o SIMP_RULE std_ss [word_concat_def,word_join_def,w2w_w2w,LET_THM]
(* word_extract *)
val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)
val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

(* w2w has to be translated for every single use *)
val _ = translate (INST_TYPE[alpha|->``:64``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:4``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:4``,beta|->``:3``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:2``,beta|->``:8``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:3``,beta|->``:4``] w2w_def)
val _ = translate (INST_TYPE[alpha|->``:64``,beta|->``:33``] w2w_def)

(*simple CSE *)
fun lrthm strip th = th |> SPEC_ALL |> concl |> dest_eq |> (fn (x,y) => (strip x,y))

fun count_terms tlist =
  foldl (fn (t,d) => case Redblackmap.peek(d,t) of
      SOME n => Redblackmap.insert (d,t,n+1)
    |  _ => Redblackmap.insert (d,t,1)) (Redblackmap.mkDict Term.compare) tlist

fun is_subterm x y =
  patternMatchesSyntax.has_subterm (fn t => t = x) y

fun mostgen x [] acc = (x,acc)
|   mostgen x (y::ys) acc =
  if is_subterm x y then mostgen y ys acc
  else if is_subterm y x then mostgen x ys acc
  else mostgen x ys (y::acc)

fun filsubs [] = []
|   filsubs (x::xs) =
  let val (k,vs) = mostgen x xs [] in
    k :: filsubs vs
  end

fun is_fun_type t =
  (can dom_rng (type_of t))

fun let_abs v t tt =
  mk_let (mk_abs(v,subst [(t |-> v)] tt),t)

fun cse lim t =
  let val fvt = free_vars t
      val foo = count_terms (find_terms (fn tt =>
        let val fvs = free_vars tt in
          all (fn v => mem v fvt) fvs andalso
          fvs <> [] andalso
          not(is_fun_type tt) andalso
          not(is_var tt)
        end) t)
      val tlist = map fst (filter (fn (k,v) => v > lim) (Redblackmap.listItems foo))
      val toabs = filsubs tlist
      val name = "cse" in
      #2(foldl (fn (t,(i,tt)) => (i+1,let_abs (mk_var (name^Int.toString i,type_of t)) t tt))
        (0,t) toabs)
  end

fun csethm lim th =
  let val (l,r) = lrthm I th
      val goal = mk_eq(l,cse lim r) in
      prove(goal, simp[th])
  end

(*x64_enc i = case i of ... each of ths is one branch*)
(* reconstructs a case goal *)
fun reconstruct_case t strip ths =
  let val rhs = TypeBase.mk_case (strip t,map (lrthm strip) ths)
  in
    prove(mk_forall (strip t,mk_eq (t,rhs)),Cases >> simp ths) |> SPEC_ALL
  end

val (x64_enc1::x64_enc2::x64_enc3::x64_enc4::x64_enc5::x64_enc6::_) =
x64_enc_def
  |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss[``:64 asm``])[]
  |> CONJUNCTS

val zreg2num_totalnum2zerg = Q.prove(`
  Zreg2num (total_num2Zreg n) = if n < 16 then n else 0`,
  EVAL_TAC>>IF_CASES_TAC>>fs[Zreg2num_num2Zreg]);

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

val defaults = [x64_ast_def,x64_encode_def,encode_def,e_rm_reg_def,e_gen_rm_reg_def,e_ModRM_def,e_opsize_def,e_imm32_def,rex_prefix_def,x64_dec_fail_def,e_opc_def,e_rax_imm_def,e_rm_imm_def,asmSemTheory.is_test_def,x64_cmp_def,e_opsize_imm_def,e_imm8_def,e_rm_imm8_def,not_byte_def,e_imm16_def,e_imm64_def,Zsize_width_def,x64_bop_def,zreg2num_totalnum2zerg,e_imm_8_32_def,Zbinop_name2num_x64_sh,x64_sh_notZtest,exh_if_collapse]

(*val x64_simp1 = x64_enc1 |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 inst``,``:64 arith``,``:64 addr``,``:memop``,``:binop``,``:64 reg_imm``])[] |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]*)

val x64_enc1s = x64_enc1 |> SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:64 inst``]) defaults |> CONJUNCTS

val x64_enc1_1 = el 1 x64_enc1s
val x64_enc1_2 = el 2 x64_enc1s |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> csethm 5

val (binop::rest) = el 3 x64_enc1s |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 arith``]) [] |> CONJUNCTS

val (binopreg_aux::binopimm_aux::_) = binop |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``]) [FORALL_AND_THM] |> CONJUNCTS |> map (SIMP_RULE (srw_ss() ++ LET_ss ++ DatatypeSimps.expand_type_quants_ss [``:binop``]) [])

val binopreg = binopreg_aux |> CONJUNCTS |> map(fn th => th |> SIMP_RULE (srw_ss()++LET_ss) ((Q.ISPEC `x64_encode` COND_RAND) ::defaults) |> wc_simp |> we_simp |> gconv |>SIMP_RULE std_ss [SHIFT_ZERO])

val binopregth = reconstruct_case ``x64_enc (Inst (Arith (Binop b n n0 (Reg n'))))`` (rand o rator o rator o rator o rand o rand o rand) (map (csethm 2) binopreg)

val binopimm = binopimm_aux |> CONJUNCTS |> map(fn th => th |> SIMP_RULE (srw_ss()++LET_ss) ((Q.ISPEC `x64_encode` COND_RAND) ::defaults) |> wc_simp |> we_simp |> gconv |>SIMP_RULE std_ss [SHIFT_ZERO])

val binopimmth = reconstruct_case ``x64_enc (Inst (Arith (Binop b n n0 (Imm c))))`` (rand o rator o rator o rator o rand o rand o rand) (map (csethm 3) binopimm)

val binopth = reconstruct_case ``x64_enc(Inst (Arith (Binop b n n0 r)))`` (rand o rand o rand o rand) [binopregth,binopimmth]

val x64_enc1_3_aux = binopth :: map (fn th => th |> SIMP_RULE (srw_ss()) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> csethm 4) rest

val x64_enc1_3 = reconstruct_case ``x64_enc (Inst (Arith a))`` (rand o rand o rand) x64_enc1_3_aux

val x64_enc1_4_aux = el 4 x64_enc1s |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 addr``,``:memop``]) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> CONJUNCTS

val x64_enc1_4 = reconstruct_case ``x64_enc (Inst (Mem m n a))`` (rand o rand o rand) [reconstruct_case ``x64_enc (Inst (Mem m n (Addr n' c)))`` (rand o rator o rator o rand o rand) (map (csethm 2) x64_enc1_4_aux)]

val x64_simp1 = reconstruct_case ``x64_enc (Inst i)`` (rand o rand) [x64_enc1_1,x64_enc1_2,x64_enc1_3,x64_enc1_4]
 |> SIMP_RULE std_ss [Q.ISPEC `Zbinop_name2num` COND_RAND,Zbinop_name2num_thm]

val x64_simp2 = x64_enc2 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val x64_simp3 = x64_enc3 |> SIMP_RULE (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:64 reg_imm``])[FORALL_AND_THM] |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> CONJUNCTS |> map (csethm 5) |> reconstruct_case ``x64_enc (JumpCmp c n r c0)`` (rand o rator o rand )
 |> SIMP_RULE std_ss [Q.ISPEC `Zbinop_name2num` COND_RAND,Zbinop_name2num_thm,Q.ISPEC `$* 0xFFFFFFFFFFFFFFFFw` COND_RAND] |> gconv

val x64_simp4 = x64_enc4 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO]

val x64_simp5 = x64_enc5 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> csethm 2

val x64_simp6 = x64_enc6 |> SIMP_RULE (srw_ss() ++ LET_ss) defaults |> wc_simp |> we_simp |> gconv |> SIMP_RULE std_ss [SHIFT_ZERO] |> csethm 2

val x64_enc_thm = reconstruct_case ``x64_enc i`` rand [x64_simp1,x64_simp2,x64_simp3,x64_simp4,x64_simp5,x64_simp6]

val _ = translate total_num2Zreg_def
val total_num2zreg_side = Q.prove(`
  ∀x. total_num2zreg_side x ⇔ T`,
  simp[fetch "-" "total_num2zreg_side_def"]>>
  FULL_SIMP_TAC std_ss [fetch "-" "num2zreg_side_def"]>>
  ntac 2 strip_tac>>
  (* Faster than DECIDE_TAC *)
  Cases_on`x`>>FULL_SIMP_TAC std_ss [ADD1]>>
  ntac 7 (Cases_on`n`>>FULL_SIMP_TAC std_ss [ADD1]>>
  Cases_on`n'`>>FULL_SIMP_TAC std_ss [ADD1])>>
  Cases_on`n`>>fs[]) |> update_precondition

val res = translate (GEN_ALL x64_enc_thm)

val _ = translate (x64_config_def |> gconv)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
