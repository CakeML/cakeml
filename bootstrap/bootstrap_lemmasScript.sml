open HolKernel boolLib bossLib pairTheory listTheory lcsymtacs miscLib
open ml_translatorTheory repl_funProofTheory compilerProofTheory ml_repl_moduleTheory
open compile_repl_decsTheory
open bigStepTheory terminationTheory

val _ = temp_tight_equality()
val _ = new_theory "bootstrap_lemmas"

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE

val _ = Globals.max_print_depth := 20

(* TODO: move *)

val LUPDATE_SAME = store_thm("LUPDATE_SAME",
  ``∀n ls. n < LENGTH ls ⇒ (LUPDATE (EL n ls) n ls = ls)``,
  rw[LIST_EQ_REWRITE,EL_LUPDATE]>>rw[])

(* REPL module is closed (should be proved elsewhere?) *)

val all_env_dom_init =
  ``all_env_dom ((THE prim_sem_env).sem_envM,(THE prim_sem_env).sem_envC,(THE prim_sem_env).sem_envE)``
  |> (REWRITE_CONV [initSemEnvTheory.prim_sem_env_eq] THENC
      SIMP_CONV std_ss [free_varsTheory.all_env_dom_def,libTheory.lookup_def] THENC
      SIMP_CONV (srw_ss()) [pred_setTheory.EXTENSION] THENC
      EVAL)

val closed_top_REPL = prove(
  ``closed_top ((THE prim_sem_env).sem_envM,(THE prim_sem_env).sem_envC,(THE prim_sem_env).sem_envE) (Tmod "REPL" NONE ml_repl_module_decls)``,
  simp[free_varsTheory.closed_top_def,all_env_dom_init,FV_decs_ml_repl_module_decls])

(* Equality Type assumptions *)

local
  val ths = CONJUNCTS equality_types
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_thm = prove(
  ``EqualityType abs ⇔
      (!x1 v1. abs x1 v1 ==> no_closures v1) /\
      (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> types_match v1 v2 /\
                                                ((v1 = v2) ⇔ (x1 = x2)))``,
  SIMP_TAC std_ss [EqualityType_def] \\ METIS_TAC []);

(*
val EqualityType_CHAR = find_equality_type_thm``CHAR``
val EqualityType_INT = find_equality_type_thm``INT``
val EqualityType_NUM = find_equality_type_thm``NUM``
val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]
val EqualityType_TOKENS_TOKEN_TYPE = find_equality_type_thm``TOKENS_TOKEN_TYPE``
  |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_CHAR,EqualityType_INT,EqualityType_NUM]
val EqualityType_GRAM_MMLNONT_TYPE = find_equality_type_thm``GRAM_MMLNONT_TYPE``
  |> SIMP_RULE std_ss []

val EqualityType1 = prove(
  ``EqualityType (GRAMMAR_PARSETREE_TYPE TOKENS_TOKEN_TYPE GRAM_MMLNONT_TYPE)``
  assume_tac EqualityType_TOKENS_TOKEN_TYPE >>
  assume_tac EqualityType_GRAM_MMLNONT_TYPE >>
  qmatch_abbrev_tac`EqualityType (GRAMMAR_PARSETREE_TYPE a b)` >>
  ntac 2 (pop_assum kall_tac) >>
  simp[EqualityType_thm] >>
  simp[GSYM FORALL_AND_THM] >>
  ntac 2 (pop_assum mp_tac)
  simp[GSYM RIGHT_FORALL_IMP_THM] >>
  map_every qid_spec_tac[`b`,`a`] >>
  ho_match_mp_tac ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_ind >>
  rw[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def] >>
  TRY (
    Cases_on`x2`>>fs[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def,types_match_def]
*)

fun prove_equality_type tm = prove(``EqualityType ^tm``,cheat)
val EqualityType1 = prove_equality_type ``GRAMMAR_PARSETREE_TYPE TOKENS_TOKEN_TYPE GRAM_MMLNONT_TYPE``
val EqualityType2 = prove_equality_type ``AST_T_TYPE``
val EqualityType3 = prove_equality_type ``AST_PAT_TYPE``
val EqualityType4 = prove_equality_type ``PATLANG_EXP_PAT_TYPE``
val EqualityType5 = prove_equality_type ``AST_EXP_TYPE``
val EqualityType6 = prove_equality_type ``INFER_T_INFER_T_TYPE``
val EqualityTypes = [EqualityType1, EqualityType2, EqualityType3, EqualityType4, EqualityType5, EqualityType6]
(* see also cheated EqualityType_INPUT_TYPE later on *)

val v_to_i1_conv =
  ``v_to_i1 x (Conv y z) a`` |> SIMP_CONV (srw_ss())[Once modLangProofTheory.v_to_i1_cases]
val v_to_i1_lit =
  ``v_to_i1 x (Litv y) a`` |> SIMP_CONV (srw_ss())[Once modLangProofTheory.v_to_i1_cases]
val v_to_i2_conv =
  ``v_to_i2 x (Conv_i1 y z) a`` |> SIMP_CONV (srw_ss())[Once conLangProofTheory.v_to_i2_cases]
val v_to_i2_lit =
  ``v_to_i2 x (Litv_i1 y) a`` |> SIMP_CONV (srw_ss())[Once conLangProofTheory.v_to_i2_cases]
val v_to_exh_conv =
  ``v_to_exh x (Conv_i2 y z) a`` |> SIMP_CONV (srw_ss())[Once exhLangProofTheory.v_to_exh_cases]
val v_pat_conv =
  ``v_pat (Conv_pat x y) a`` |> SIMP_CONV (srw_ss()) [Once patLangProofTheory.v_pat_cases]
val syneq_conv =
  ``syneq (CConv x y) z`` |> SIMP_CONV (srw_ss()) [Once intLangTheory.syneq_cases]
val Cv_bv_conv =
  ``Cv_bv a (CConv x y) z`` |> SIMP_CONV (srw_ss()) [Once bytecodeProofTheory.Cv_bv_cases]
val Cv_bv_lit =
  ``Cv_bv a (CLitv y) z`` |> SIMP_CONV (srw_ss()) [Once bytecodeProofTheory.Cv_bv_cases]

val conv_rws = [printingTheory.v_bv_def,
  v_to_i1_conv,vs_to_i1_MAP,v_to_i1_lit,
  v_to_i2_conv,vs_to_i2_MAP,v_to_i2_lit,
  v_to_exh_conv,free_varsTheory.vs_to_exh_MAP,
  printingTheory.exh_Cv_def,
  v_pat_conv,syneq_conv,Cv_bv_conv,Cv_bv_lit]

val no_closures_vlabs = prove(
  ``∀b c d e f g.
    no_closures b ⇒
    v_to_i1 grd0 b c ∧
    v_to_i2 grd1 c d ∧
    v_to_exh grd2 d e ∧
    v_pat (v_to_pat e) f ∧
    syneq (v_to_Cv f) g
    ⇒
    vlabs g = {} ∧ all_vlabs g``,
  ho_match_mp_tac no_closures_ind >>
  simp[no_closures_def] >>
  simp[Q.SPECL[`X`,`Litv Y`](CONJUNCT1 modLangProofTheory.v_to_i1_cases)] >>
  simp[Q.SPECL[`X`,`Litv_i1 Y`](CONJUNCT1 conLangProofTheory.v_to_i2_cases)] >>
  simp (PULL_EXISTS::conv_rws) >>
  ntac 3 (rpt gen_tac >> strip_tac) >>
  BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs[LIST_REL_EL_EQN,MEM_EL,PULL_EXISTS,EL_MAP,EVERY_MEM] >>
  fs[intLangExtraTheory.vlabs_list_MAP,Once pred_setTheory.EXTENSION,PULL_EXISTS,MEM_EL] >>
  METIS_TAC[])

val LIST_TYPE_CHAR_vlabs = prove(
  ``∀a b c d e f g.
  LIST_TYPE CHAR a b ∧
          v_to_i1 grd0 b c ∧
          v_to_i2 grd1 c d ∧
          v_to_exh grd2 d e ∧
          v_pat (v_to_pat e) f ∧
          syneq (v_to_Cv f) g
          ⇒
          vlabs g = {} ∧ all_vlabs g``,
  Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >>
  simp(PULL_EXISTS::conv_rws) >>
  simp[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[Q.SPECL[`X`,`Litv Y`](CONJUNCT1 modLangProofTheory.v_to_i1_cases),
       Q.SPECL[`X`,`Litv_i1 Y`](CONJUNCT1 conLangProofTheory.v_to_i2_cases)] >>
  METIS_TAC[])

val LEXER_FUN_SYMBOL_TYPE_vlabs = prove(
  ``∀a b c d e f g.
  LEXER_FUN_SYMBOL_TYPE a b ∧
          v_to_i1 grd0 b c ∧
          v_to_i2 grd1 c d ∧
          v_to_exh grd2 d e ∧
          v_pat (v_to_pat e) f ∧
          syneq (v_to_Cv f) g
          ⇒
          vlabs g = {} ∧ all_vlabs g``,
  Induct >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def,PULL_EXISTS] >>
  simp(PULL_EXISTS::conv_rws) >>
  simp[ml_translatorTheory.INT_def,
       Q.SPECL[`X`,`Litv Y`](CONJUNCT1 modLangProofTheory.v_to_i1_cases),
       Q.SPECL[`X`,`Litv_i1 Y`](CONJUNCT1 conLangProofTheory.v_to_i2_cases)] >>
  METIS_TAC[LIST_TYPE_CHAR_vlabs])

val LIST_TYPE_LEXER_FUN_SYMBOL_TYPE_vlabs = prove(
  ``∀ts w w1 w2 w3 w4 w5.
    LIST_TYPE LEXER_FUN_SYMBOL_TYPE ts w ∧
    v_to_i1 grd0 w w1 ∧
    v_to_i2 grd1 w1 w2 ∧
    v_to_exh grd2 w2 w3 ∧
    v_pat (v_to_pat w3) w4 ∧
    syneq (v_to_Cv w4) w5
    ⇒
    vlabs w5 = {} ∧ all_vlabs w5``,
  Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
     rpt gen_tac >> strip_tac >>
     rfs conv_rws  >> rpt BasicProvers.VAR_EQ_TAC >>
     fs conv_rws >> BasicProvers.VAR_EQ_TAC >>
     fs conv_rws >> BasicProvers.VAR_EQ_TAC >>
     fs conv_rws >> BasicProvers.VAR_EQ_TAC ) >>
  simp[PULL_EXISTS] >>
  simp conv_rws >>
  simp[PULL_EXISTS] >>
  qx_gen_tac`z`>>rpt gen_tac >> strip_tac >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs conv_rws >> rpt BasicProvers.VAR_EQ_TAC >>
  fs[GSYM AND_IMP_INTRO] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  strip_tac >>
  simp[GSYM CONJ_ASSOC] >>
  res_tac >> simp[] >>
  ntac 3 (pop_assum kall_tac) >>
  METIS_TAC[LEXER_FUN_SYMBOL_TYPE_vlabs])

(* lemmas about the semantics of a module where we know the last few declarations *)

val evaluate_decs_new_decs_vs = store_thm("evaluate_decs_new_decs_vs",
  ``∀ck mn env s decs res. evaluate_decs ck mn env s decs res ⇒
      ∀env. SND(SND res) = Rval env ⇒ MAP FST env = new_decs_vs decs``,
  ho_match_mp_tac evaluate_decs_ind >> simp[] >> rw[libTheory.emp_def] >>
  imp_res_tac free_varsTheory.evaluate_dec_new_dec_vs >> fs[] >>
  Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def]>>
  rw[libTheory.merge_def])

val ctors_of_tdef_def = Define`
  ctors_of_tdef (_,_,condefs) = MAP FST condefs`
val _ = export_rewrites["ctors_of_tdef_def"]

val ctors_of_dec_def = Define`
  ctors_of_dec (Dtype tds) = FLAT (MAP ctors_of_tdef tds) ∧
  ctors_of_dec (Dexn s _) = [s] ∧
  ctors_of_dec _ = []`
val _ = export_rewrites["ctors_of_dec_def"]

val evaluate_decs_ctors_in = store_thm("evaluate_decs_ctors_in",
  ``∀ck mn env s decs res. evaluate_decs ck mn env s decs res ⇒
      ∀cn.
        IS_SOME (lookup cn (FST(SND res))) ⇒
        MEM cn (FLAT (MAP ctors_of_dec decs))``,
  HO_MATCH_MP_TAC evaluate_decs_ind >>
  simp[libTheory.emp_def] >>
  rw[Once evaluate_dec_cases] >> simp[] >>
  fs[libTheory.merge_def,libTheory.emp_def] >>
  fs[libPropsTheory.lookup_append] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[libTheory.bind_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[miscTheory.IS_SOME_EXISTS] >>
  imp_res_tac libPropsTheory.lookup_in2 >>
  fs[MEM_MAP,semanticPrimitivesTheory.build_tdefs_def,MEM_FLAT,PULL_EXISTS,EXISTS_PROD] >>
  METIS_TAC[])

val merge_envC_emp = prove(
  ``merge_envC (emp,emp) x = x``,
  PairCases_on`x`>>simp[semanticPrimitivesTheory.merge_envC_def,libTheory.emp_def,libTheory.merge_def])

val evaluate_decs_last3 = prove(
  ``∀ck mn env s decs a b c k i j s1 x y decs0 decs1 v p q r.
      evaluate_decs ck mn env s decs (((k,s1),a),b,Rval c) ∧
      decs = decs0 ++ [Dlet (Pvar x) (App Opref [Con i []]);Dlet(Pvar y)(App Opref [Con j []]);Dlet (Pvar p) (Fun q r)]
      ⇒
      ∃n ls1 ls2 ls.
      c = ((p,(Closure(FST env,merge_envC([],b)(FST(SND env)),merge ls1(SND(SND env))) q r))::ls1) ∧
      ls1 = ((y,Loc (n+1))::ls2) ∧ n+1 < LENGTH s1 ∧
      ls2 = ((x,Loc n)::ls) ∧
      is_Refv (EL n s1) ∧
      is_Refv (EL (n+1) s1)``,
  Induct_on`decs0` >>
  rw[Once bigStepTheory.evaluate_decs_cases] >- (
    fs[Once bigStepTheory.evaluate_decs_cases]>>
    fs[semanticPrimitivesTheory.combine_dec_result_def] >>
    fs[Once bigStepTheory.evaluate_dec_cases] >>
    fs[Once bigStepTheory.evaluate_cases] >>
    fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] >>
    fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    fs[semanticPrimitivesTheory.do_app_def] >>
    fs[semanticPrimitivesTheory.store_alloc_def,LET_THM] >>
    fs[terminationTheory.pmatch_def] >> rw[] >>
    fs[Once bigStepTheory.evaluate_decs_cases]>>
    fs[semanticPrimitivesTheory.combine_dec_result_def] >>
    fs[Once bigStepTheory.evaluate_dec_cases] >>
    rator_x_assum`evaluate`mp_tac >>
    simp[Once bigStepTheory.evaluate_cases] >> rw[] >>
    fs[Once bigStepTheory.evaluate_decs_cases]>>
    rw[libTheory.merge_def,libTheory.emp_def,libTheory.bind_def] >>
    fs[pmatch_def,libTheory.bind_def] >> rw[] >>
    fs[Once evaluate_cases] >>
    fs[Once evaluate_cases] >> rw[] >>
    PairCases_on`cenv` >>
    rw[libTheory.emp_def,semanticPrimitivesTheory.merge_envC_def,libTheory.merge_def] >>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2]) >>
  Cases_on`r'`>>fs[semanticPrimitivesTheory.combine_dec_result_def]>>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  rfs[semanticPrimitivesTheory.all_env_to_cenv_def] >>
  rw[libTheory.merge_def] >>
  PairCases_on`cenv` >>
  rw[libTheory.emp_def,semanticPrimitivesTheory.merge_envC_def,libTheory.merge_def])

val evaluate_Tmod_last3 = prove(
  ``evaluate_top ck env0 st (Tmod mn NONE decs) ((cs,u),envC,Rval ([(mn,env)],v)) ⇒
    decs = decs0 ++[Dlet (Pvar x) (App Opref [Con i []]);Dlet (Pvar y) (App Opref [Con j []]);Dlet (Pvar p) (Fun q z)]
  ⇒
    ∃n ls1 ls.
    env = (p,(Closure (FST env0,merge_envC ([],SND(HD(FST envC))) (FST(SND env0)),merge ls (SND(SND env0))) q z))::ls ∧
    (ls = (y,Loc (n+1))::(x,Loc n)::ls1) ∧
    n+1 < LENGTH (SND cs) ∧
    is_Refv (EL n (SND cs)) ∧
    is_Refv (EL (n+1) (SND cs))``,
  Cases_on`cs`>>rw[bigStepTheory.evaluate_top_cases]>>
  imp_res_tac evaluate_decs_last3 >> fs[]) |> GEN_ALL

val check_dup_ctors_flat = Q.prove (
`!defs.
  check_dup_ctors (defs:type_def) =
  ALL_DISTINCT (MAP FST (build_tdefs mn defs))`,
 rw [check_dup_ctors_thm, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
     semanticPrimitivesTheory.build_tdefs_def,
     rich_listTheory.MAP_REVERSE, ALL_DISTINCT_REVERSE]);

val evaluate_decs_tys = prove(
  ``∀decs0 decs1 decs ck mn env s s' tys c tds tvs tn cts cn as.
    evaluate_decs ck (SOME mn) env s decs (s',tys,Rval c) ∧
    decs = decs0 ++ [Dtype tds] ++ decs1 ∧
    MEM (tvs,tn,cts) tds ∧ MEM (cn,as) cts ∧
    ¬MEM cn (FLAT (MAP ctors_of_dec decs1))
    ⇒
    (lookup cn tys = SOME (LENGTH as, TypeId (Long mn tn)))``,
  Induct >> rw[Once evaluate_decs_cases] >- (
    fs[Once evaluate_dec_cases] >> rw[] >>
    simp[libTheory.merge_def,libPropsTheory.lookup_append] >>
    imp_res_tac evaluate_decs_ctors_in >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    Cases_on`lookup cn (build_tdefs (SOME mn) tds)` >- (
      imp_res_tac libPropsTheory.lookup_notin >>
      fs[semanticPrimitivesTheory.build_tdefs_def,MEM_MAP,MEM_FLAT,PULL_EXISTS,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    imp_res_tac (fst(EQ_IMP_RULE(SPEC_ALL check_dup_ctors_flat))) >>
    imp_res_tac libPropsTheory.lookup_in3 >>
    `MEM (cn,LENGTH as,TypeId(Long mn tn)) (build_tdefs (SOME mn) tds)` by (
      simp[semanticPrimitivesTheory.build_tdefs_def,MEM_MAP,MEM_FLAT,PULL_EXISTS,EXISTS_PROD] >>
      simp[astTheory.mk_id_def] >> METIS_TAC[] ) >>
    first_x_assum(qspec_then`SOME mn`mp_tac) >>
    strip_tac >>
    fs[MEM_EL] >>
    qmatch_assum_rename_tac`(cn,X) = EL n1 ls`["X","ls"] >>
    qmatch_assum_rename_tac`(cn,x) = EL n2 ls`["ls"] >>
    `EL n1 (MAP FST (build_tdefs (SOME mn) tds)) =
     EL n2 (MAP FST (build_tdefs (SOME mn) tds))` by (
       simp[EL_MAP] >> METIS_TAC[FST] ) >>
    fs[EL_ALL_DISTINCT_EL_EQ] >>
    `n1 = n2` by METIS_TAC[] >>
    fs[] >>
    METIS_TAC[PAIR_EQ] ) >>
  simp[libPropsTheory.lookup_append,libTheory.merge_def] >>
  Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  simp[])

val evaluate_Tmod_tys = prove(
  ``evaluate_top F env s (Tmod mn NONE decs) (s',([m,tys],e),Rval r) ⇒
    decs = decs0 ++ [Dtype tds] ++ decs1 ⇒
    MEM (tvs,tn,cts) tds ∧ MEM (cn,as) cts ∧
    ¬MEM cn (FLAT (MAP ctors_of_dec decs1))
    ⇒
    (lookup cn tys = SOME (LENGTH as, TypeId (Long mn tn)))``,
  rw[evaluate_top_cases] >>
  METIS_TAC[evaluate_decs_tys]) |> GEN_ALL

(* Environment produced by repl_decs *)

val evaluate_repl_decs = DISCH_ALL module_thm
  |> RW EqualityTypes

val (repl_store,repl_res) =
  CONJUNCT1 evaluate_repl_decs
  |> concl |> strip_comb
  |> snd |> last
  |> dest_pair
val (x,y) = dest_pair repl_res
val y = rand y
val (y,z) = dest_pair y
val repl_all_env = ``^y,merge_envC ^x (THE prim_sem_env).sem_envC,(THE prim_sem_env).sem_envE``

val repl_decs_cs =
  let
    val cs = listSimps.list_compset()
    val _ = computeLib.add_thms[ml_repl_moduleTheory.ml_repl_module_decls] cs
    val _ = computeLib.add_thms[rich_listTheory.LASTN_compute,ctors_of_dec_def,ctors_of_tdef_def] cs
    val _ = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:dec``))
  in
    cs
  end

val last_3_decs = computeLib.CBV_CONV repl_decs_cs ``LASTN 3 ml_repl_module_decls``

val append_3 =
  rich_listTheory.APPEND_BUTLASTN_LASTN |> Q.ISPECL[`3:num`,`ml_repl_module_decls`]
  |> UNDISCH |> SYM |> RW[last_3_decs]
  |> prove_hyps_by(CONV_TAC(computeLib.CBV_CONV repl_decs_cs))

val iloc_repl_env_exist =
  MATCH_MP evaluate_Tmod_last3 (CONJUNCT1 evaluate_repl_decs)
  |> SIMP_RULE (srw_ss())[]
  |> C MATCH_MP append_3
  |> REWRITE_RULE[GSYM append_3]

val repl_env_def = new_specification("repl_env_def",["iloc","repl_env"],iloc_repl_env_exist)

val sum_idx = ``21:num``
val sym_idx = ``77:num``
val el_sum = computeLib.CBV_CONV repl_decs_cs ``EL ^sum_idx ml_repl_module_decls``
val take_sum = computeLib.CBV_CONV repl_decs_cs ``TAKE ^sum_idx ml_repl_module_decls``
val drop_sum = computeLib.CBV_CONV repl_decs_cs ``DROP (^sum_idx + 1) ml_repl_module_decls``
val el_sym = computeLib.CBV_CONV repl_decs_cs ``EL ^sym_idx ml_repl_module_decls``
val take_sym = computeLib.CBV_CONV repl_decs_cs ``TAKE ^sym_idx ml_repl_module_decls``
val drop_sym = computeLib.CBV_CONV repl_decs_cs ``DROP (^sym_idx + 1) ml_repl_module_decls``
val length = computeLib.CBV_CONV repl_decs_cs ``LENGTH ml_repl_module_decls``
val tdefs_sum = prove(
  ``ml_repl_module_decls = ^(lhs(concl take_sum)) ++ [^(lhs(concl el_sum))] ++ ^(lhs(concl drop_sum))``,
  assume_tac length >>
  rw[LIST_EQ_REWRITE] >>
  Cases_on`x < ^sum_idx` >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_TAKE] >>
  Cases_on`x = ^sum_idx` >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
  simp[rich_listTheory.EL_DROP])
val tdefs_sym = prove(
  ``ml_repl_module_decls = ^(lhs(concl take_sym)) ++ [^(lhs(concl el_sym))] ++ ^(lhs(concl drop_sym))``,
  assume_tac length >>
  rw[LIST_EQ_REWRITE] >>
  Cases_on`x < ^sym_idx` >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_TAKE] >>
  Cases_on`x = ^sym_idx` >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
  simp[rich_listTheory.EL_DROP])

val sum_tags_exist =
  MATCH_MP evaluate_Tmod_tys (CONJUNCT1 evaluate_repl_decs)
  |> C MATCH_MP (RW[el_sum]tdefs_sum)
  |> SIMP_RULE(srw_ss()++boolSimps.DNF_ss)[]
  |> CONJUNCTS
  |> List.map (CONV_RULE(LAND_CONV(PURE_REWRITE_CONV[drop_sum]THENC(computeLib.CBV_CONV repl_decs_cs))))
  |> List.map (SIMP_RULE(srw_ss())[])
  |> LIST_CONJ

val sym_tags_exist =
  MATCH_MP evaluate_Tmod_tys (CONJUNCT1 evaluate_repl_decs)
  |> C MATCH_MP (RW[el_sym]tdefs_sym)
  |> SIMP_RULE(srw_ss()++boolSimps.DNF_ss)[]
  |> CONJUNCTS
  |> List.map (CONV_RULE(LAND_CONV(PURE_REWRITE_CONV[drop_sym]THENC(computeLib.CBV_CONV repl_decs_cs))))
  |> List.map (SIMP_RULE(srw_ss())[])
  |> LIST_CONJ

val INPUT_TYPE_def = Define `
  INPUT_TYPE =
  ^(find_term (can (match_term ``OPTION_TYPE xx``)) (concl evaluate_repl_decs))`;

val OUTPUT_TYPE_def = Define `
  OUTPUT_TYPE =
  ^(find_term (can (match_term ``SUM_TYPE xx yy``)) (concl evaluate_repl_decs))`;

val EqualityType_INPUT_TYPE = prove(
  ``EqualityType INPUT_TYPE``,
  cheat)

(* bytecode state produce by repl_decs *)

val prim_invariant' = prove(
  ``invariant' (THE prim_sem_env) (FST(THE prim_env)) (THE prim_bs)``,
  METIS_TAC[initCompEnvTheory.prim_env_inv,optionTheory.THE_DEF,optionTheory.option_CASES,pairTheory.FST])

val prim_env_rs = prove(
  prim_invariant' |> RW[initCompEnvTheory.invariant'_def]
  |> concl |> strip_exists |> snd |> strip_conj |> el 5
  |> (fn tm => list_mk_exists(free_vars tm,tm)),
  METIS_TAC[prim_invariant',initCompEnvTheory.invariant'_def])

val bootstrap_bc_state_exists = prove(
  ``∃bs grd.
      bc_eval (install_code ((SND(SND(compile_repl_decs)))++SND(THE prim_env)) initial_bc_state) = SOME bs ∧
      bc_fetch bs = SOME (Stop T) ∧
      EVERY IS_SOME bs.globals ∧
      env_rs ^repl_all_env ^repl_store grd (FST compile_repl_decs) bs``,
  mp_tac(MATCH_MP bigClockTheory.top_add_clock (CONJUNCT1 evaluate_repl_decs)) >>
  simp[] >>
  `∃c r. Tmod_state "REPL" ml_repl_module_decls = (c,r)` by METIS_TAC[pair_CASES] >> simp[] >>
  assume_tac(``(THE prim_sem_env).sem_store`` |> SIMP_CONV (srw_ss()) [initSemEnvTheory.prim_sem_env_eq]) >> simp[] >>
  disch_then(qx_choose_then`ck`(mp_tac o MATCH_MP compile_top_thm)) >>
  simp[] >>
  STRIP_ASSUME_TAC prim_env_rs >>
  pop_assum(mp_tac o MATCH_MP (RW[GSYM AND_IMP_INTRO]env_rs_change_clock)) >>
  simp[] >> disch_then(qspecl_then[`ck`,`SOME ck`]mp_tac) >> simp[] >>
  strip_tac >>
  CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["bs","rs","types"]))) >>
  `∃rss rsf bc. compile_repl_decs = (rss,rsf,bc)` by METIS_TAC[pair_CASES] >>
  disch_then(qspecl_then[`install_code bc (THE prim_bs with clock := SOME ck)`
                        ,`(FST (THE prim_env)).comp_rs`,`NONE`]mp_tac) >>
  simp[] >>
  fs[compile_repl_decs_def,closed_top_REPL] >>
  disch_then(qspecl_then[`genv,gtagenv,rd`]mp_tac) >>
  CONV_TAC(LAND_CONV(QUANT_CONV(LAND_CONV(SIMP_CONV(srw_ss())[initCompEnvTheory.install_code_def]))))>>
  simp[] >>
  discharge_hyps >- (
    match_mp_tac env_rs_with_bs_irr >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  strip_tac >>
  qexists_tac`bs' with clock := NONE` >>
  simp[GSYM PULL_EXISTS,bytecodeClockTheory.bc_fetch_with_clock] >>
  conj_tac >- (
    match_mp_tac(MP_CANON bytecodeEvalTheory.RTC_bc_next_bc_eval) >>
    reverse conj_tac >- (
      simp[bytecodeEvalTheory.bc_eval1_thm
          ,bytecodeEvalTheory.bc_eval1_def
          ,bytecodeClockTheory.bc_fetch_with_clock] ) >>
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    imp_res_tac bytecodeClockTheory.RTC_bc_next_can_be_unclocked >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl)>>simp[]>>
    match_mp_tac bytecodeExtraTheory.RTC_bc_next_append_code >>
    assume_tac initCompEnvTheory.prim_bs_eq >>
    fs[initCompEnvTheory.prim_bs_def] >>
    imp_res_tac bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next >>
    first_assum(match_exists_tac o concl) >>
    simp[bytecodeTheory.bc_state_component_equality]>>
    REWRITE_TAC[initCompEnvTheory.install_code_def] >>
    EVAL_TAC >> simp[GSYM REVERSE_REV]) >>
  conj_tac >- (
    fs[initCompEnvTheory.install_code_def]>>
    first_x_assum match_mp_tac >>
    simp[initCompEnvTheory.prim_bs_eq] ) >>
  `(THE prim_sem_env).sem_envM = []` by fs[initSemEnvTheory.prim_sem_env_eq] >>
  fs[libTheory.emp_def] >>
  METIS_TAC[env_rs_change_clock,SND,FST])

val bootstrap_bc_state_def = new_specification("bootstrap_bc_state_def",["bootstrap_bc_state","bootstrap_grd"],bootstrap_bc_state_exists)

val repl_bc_state_def = Define`
  repl_bc_state = install_code compile_call_repl_step bootstrap_bc_state`

val repl_bc_state_clock = prove(
  ``bootstrap_bc_state.clock = NONE ∧ repl_bc_state.clock = NONE``,
  rw[repl_bc_state_def,initCompEnvTheory.install_code_def] >>
  strip_assume_tac bootstrap_bc_state_def >>
  imp_res_tac bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_clock_less >>
  fs[optionTheory.OPTREL_def,initCompEnvTheory.install_code_def] >>
  fs[initCompEnvTheory.initial_bc_state_def,initCompEnvTheory.empty_bc_state_def])

(* Effect of evaluating the call *)
val update_io_def  = Define`
  update_io inp out ((c,s),x,y) =
    ((c,LUPDATE (Refv out) (iloc+1) (LUPDATE (Refv inp) iloc s)),x,y)`

val call_dec = rand(rhs(concl(compile_call_repl_step_def)))

val evaluate_call_repl_step = store_thm("evaluate_call_repl_step",
  ``∀x inp out. INPUT_TYPE x inp ⇒
      ∃out'. OUTPUT_TYPE (basis_repl_step x) out' ∧
      evaluate_top F ^repl_all_env (update_io inp out ^repl_store) ^call_dec
        (update_io inp out' ^repl_store, ([],[]), Rval ([],[]))``,
  rw[evaluate_top_cases,evaluate_dec_cases,Once evaluate_cases,libTheory.emp_def] >>
  rw[Once evaluate_cases,semanticPrimitivesTheory.lookup_var_id_def] >>
  rw[Once evaluate_cases,astTheory.pat_bindings_def] >>
  mp_tac(CONJUNCT2 evaluate_repl_decs) >>
  REWRITE_TAC[GSYM INPUT_TYPE_def,GSYM OUTPUT_TYPE_def] >>
  simp[can_lookup_def] >> strip_tac >>
  strip_assume_tac repl_env_def >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[semanticPrimitivesTheory.all_env_to_cenv_def,libTheory.merge_def] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[libPropsTheory.lookup_append] >> fs[] >>
  rw[semanticPrimitivesTheory.do_opapp_def] >>
  simp[PULL_EXISTS] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  simp[PULL_EXISTS] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[libPropsTheory.lookup_append] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  simp[PULL_EXISTS] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.do_app_def] >>
  rw[Once (CONJUNCT2 evaluate_cases)] >>
  fs[Arrow_def,AppReturns_def] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qx_choose_then`out'`strip_assume_tac) >>
  qexists_tac`out'` >> simp[] >>
  simp[semanticPrimitivesTheory.store_lookup_def] >>
  simp[semanticPrimitivesTheory.store_assign_def] >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls`>>
  simp[update_io_def,PULL_EXISTS] >>
  qexists_tac`Litv Unit` >>
  simp[pmatch_def] >>
  fs[evaluate_closure_def] >>
  simp[EL_LUPDATE] >>
  imp_res_tac evaluate_empty_store_IMP >>
  Q.PAT_ABBREV_TAC`ss:v count_store = (xx,LUPDATE  a b c)` >>
  first_x_assum(qspec_then`ss`strip_assume_tac) >>
  fs[Abbr`ss`] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[EL_LUPDATE] >>
  simp[semanticPrimitivesTheory.store_v_same_type_def] >>
  rw[LIST_EQ_REWRITE,EL_LUPDATE] )

(* Compiler's invariant, holds after compiling REPL *)

val COMPILER_RUN_INV_def = Define `
  COMPILER_RUN_INV bs grd inp out ⇔
     env_rs ^repl_all_env (update_io inp out ^repl_store) grd
       (FST compile_repl_decs) bs ∧
    (∃rf pc hdl. bs = repl_bc_state with <| pc := pc; refs := rf; handler := hdl |>) `

val COMPILER_RUN_INV_empty_stack = store_thm("COMPILER_RUN_INV_empty_stack",
  ``COMPILER_RUN_INV bs grd inp out ⇒ (bs.stack = [])``,
  rw[COMPILER_RUN_INV_def]>> PairCases_on`grd` >>
  Cases_on`Tmod_state "REPL" ml_repl_module_decls`>>
  fs[update_io_def,compilerProofTheory.env_rs_def])

val COMPILER_RUN_INV_init = store_thm("COMPILER_RUN_INV_init",
  ``COMPILER_RUN_INV repl_bc_state bootstrap_grd
       (dest_Refv (EL iloc (SND (Tmod_state "REPL" ml_repl_module_decls))))
       (dest_Refv (EL (iloc+1) (SND (Tmod_state "REPL" ml_repl_module_decls))))``,
  rw[COMPILER_RUN_INV_def,repl_bc_state_def] >- (
    Cases_on`Tmod_state "REPL" ml_repl_module_decls` >>
    simp[update_io_def] >>
    strip_assume_tac repl_env_def >> rfs[] >>
    Cases_on`EL iloc r`>>fs[]>>Cases_on`EL (iloc+1) r`>>fs[]>>
    ntac 2 (pop_assum (mp_tac o SYM)) >>
    simp[LUPDATE_SAME] >> rw[] >>
    strip_assume_tac bootstrap_bc_state_def >>
    MATCH_MP_TAC env_rs_with_bs_irr >>
    qexists_tac`bootstrap_bc_state with code := bootstrap_bc_state.code ++ REVERSE compile_call_repl_step` >>
    simp[initCompEnvTheory.install_code_def] >>
    rfs[]  >>
    MATCH_MP_TAC env_rs_append_code >>
    rfs[] >> first_assum(match_exists_tac o concl) >> simp[] >>
    simp[bytecodeTheory.bc_state_component_equality] >>
    simp[compilerTheory.compiler_state_component_equality] >>
    `∃x y z. bootstrap_grd = (x,y,z)` by metis_tac[pair_CASES] >>
    fs[env_rs_def] >>
    rator_x_assum`good_labels`mp_tac >>
    simp[bytecodeExtraTheory.good_labels_def,bytecodeExtraTheory.between_labels_def] >>
    simp[rich_listTheory.FILTER_APPEND,rich_listTheory.FILTER_REVERSE,
         rich_listTheory.EVERY_REVERSE,EVERY_MAP,miscTheory.between_def,
         EVERY_FILTER,compile_call_repl_step_labels] >>
    assume_tac compile_call_repl_step_labels >>
    fs[FILTER_EQ_NIL,EVERY_MEM] ) >>
  simp[bytecodeTheory.bc_state_component_equality])

(* Running the code preserves the invariant *)

val code_start_def = Define `
  code_start bs = next_addr bs.inst_length bootstrap_bc_state.code`;

val COMPILER_RUN_INV_repl_step = store_thm("COMPILER_RUN_INV_repl_step",
  ``COMPILER_RUN_INV bs1 grd1 inp1 out1 /\
    INPUT_TYPE x inp1 ==>
    ?bs2 out2 grd2.
      (bc_eval (bs1 with pc := code_start bs1) = SOME bs2) /\
      bc_fetch bs2 = SOME (Stop T) /\
      COMPILER_RUN_INV bs2 grd2 inp1 out2 /\
      OUTPUT_TYPE (basis_repl_step x) out2``,
  rw[Once COMPILER_RUN_INV_def,code_start_def] >>
  first_assum(mp_tac o MATCH_MP evaluate_call_repl_step) >>
  disch_then(qspec_then`out1`strip_assume_tac) >>
  pop_assum (mp_tac o MATCH_MP bigClockTheory.top_add_clock) >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls`>>
  fs[update_io_def] >>
  disch_then(qx_choose_then`ck`STRIP_ASSUME_TAC) >>
  pop_assum(mp_tac o MATCH_MP compile_special_thm) >> simp[] >>
  disch_then(qspecl_then[`FST compile_repl_decs`]mp_tac) >>
  simp[GSYM compile_call_repl_step_def] >>
  simp[free_varsTheory.closed_top_def,free_varsTheory.all_env_dom_def] >>
  disch_then(qspecl_then[`grd1`,`bootstrap_bc_state.code`
    ,`repl_bc_state with <| clock := SOME ck; refs := rf; handler := hdl|>`]mp_tac) >>
  discharge_hyps >- (
    conj_tac >- (
      qmatch_assum_abbrev_tac`env_rs a b c d e` >>
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`e with clock := SOME ck` >>
      simp[Abbr`e`] >>
      match_mp_tac env_rs_change_clock >>
      first_assum(match_exists_tac o concl) >>
      simp[bytecodeTheory.bc_state_component_equality,Abbr`b`] ) >>
    simp[repl_bc_state_def,initCompEnvTheory.install_code_def] >>
    simp[repl_env_def,compile_call_repl_step_labels] >>
    simp[compilerTerminationTheory.exp_to_i1_def,
         modLangTheory.dec_to_i1_def,
         modLangTheory.decs_to_i1_def,
         conLangTheory.decs_to_i2_def,
         compilerTerminationTheory.pat_to_i2_def,
         compilerTerminationTheory.exp_to_i2_def,
         exhLangTheory.exhaustive_match_def,
         exhLangTheory.add_default_def,
         compilerTerminationTheory.row_to_pat_def,
         compilerTerminationTheory.pat_to_exh_def,
         compilerTerminationTheory.sLet_pat_thm,
         decLangTheory.init_globals_def,
         patLangTheory.pure_pat_def,
         decLangTheory.decs_to_i3_def,
         compilerTerminationTheory.exp_to_exh_def,
         astTheory.pat_bindings_def,
         compilerTerminationTheory.is_unconditional_def,
         UNCURRY] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >>
    EVAL_TAC >>
    rw[finite_mapTheory.FLOOKUP_DEF] >>
    EVAL_TAC) >>
  strip_tac >>
  imp_res_tac bytecodeClockTheory.RTC_bc_next_can_be_unclocked >> fs[] >>
  imp_res_tac bytecodeEvalTheory.RTC_bc_next_bc_eval >>
  pop_assum kall_tac >> pop_assum mp_tac >>
  discharge_hyps >-
    simp[bytecodeEvalTheory.bc_eval1_thm,
         bytecodeEvalTheory.bc_eval1_def,
         bytecodeClockTheory.bc_fetch_with_clock] >>
  strip_tac >>
  Q.PAT_ABBREV_TAC`bs:bc_state = X Y` >>
  qmatch_assum_abbrev_tac`bc_eval bs2 = SOME Y` >>
  `bs = bs2` by (
    unabbrev_all_tac >>
    simp[bytecodeTheory.bc_state_component_equality,repl_bc_state_def] >>
    simp[initCompEnvTheory.install_code_def,repl_bc_state_clock] ) >>
  simp[Abbr`Y`,Abbr`bs2`,bytecodeClockTheory.bc_fetch_with_clock] >>
  qexists_tac`out'` >>
  simp[COMPILER_RUN_INV_def] >>
  qexists_tac`grd'` >>
  conj_asm1_tac >- (
    simp[update_io_def] >>
    MATCH_MP_TAC env_rs_change_clock >>
    simp[EXISTS_PROD] >> qexists_tac`0` >>
    first_assum(match_exists_tac o concl) >>
    simp[bytecodeTheory.bc_state_component_equality] ) >>
  simp[bytecodeTheory.bc_state_component_equality,repl_bc_state_clock] >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_preserves >> fs[] >>
  PairCases_on`grd1`>>PairCases_on`grd'`>>
  fs[env_rs_def,update_io_def] >> rw[] >> fs[] >>
  MATCH_MP_TAC EQ_SYM >>
  MATCH_MP_TAC same_length_gvrel_same >>
  imp_res_tac RTC_bc_next_gvrel >>
  fs[bytecodeProofTheory.Cenv_bs_def,bytecodeProofTheory.s_refs_def] >>
  conj_tac >- (
    metis_tac
    [conLangProofTheory.to_i2_invariant_def,
     modLangProofTheory.to_i1_invariant_def,
     LIST_REL_LENGTH] ) >>
  simp[repl_bc_state_def,initCompEnvTheory.install_code_def] >>
  simp[bootstrap_bc_state_def])

(* Data representation *)

val map0 = ``FST(SND(FST compile_repl_decs).contags_env)``
val short_contags_env_def = Define`
  short_contags_env = SND ^map0`
val short_contags_env_eq =
  ``short_contags_env``
  |> (REWR_CONV short_contags_env_def THENC
      PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq]
      THENC EVAL)

val repl_contags_env_def = Define`
  repl_contags_env = THE (FLOOKUP (FST ^map0) "REPL")`
val repl_contags_env_eq =
  ``repl_contags_env``
  |> (REWR_CONV repl_contags_env_def THENC
      PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq]
      THENC EVAL)

fun mktm s = ``FST(lookup_tag_flat ^(stringSyntax.fromMLstring s) repl_contags_env)``
val inr_tag_def     = Define`inr_tag     = ^(mktm "Inr")`
val inl_tag_def     = Define`inl_tag     = ^(mktm "Inl")`
val errors_tag_def  = Define`errors_tag  = ^(mktm "Errors")`
val others_tag_def  = Define`others_tag  = ^(mktm "Others")`
val longs_tag_def   = Define`longs_tag   = ^(mktm "Longs")`
val numbers_tag_def = Define`numbers_tag = ^(mktm "Numbers")`
val strings_tag_def = Define`strings_tag = ^(mktm "Strings")`

val BlockNil_def  = Define `BlockNil = Block (block_tag+conLang$nil_tag) []`;
val BlockCons_def = Define `BlockCons (x,y) = Block (block_tag+conLang$cons_tag) [x;y]`;
val BlockPair_def = Define `BlockPair (x,y) = Block (block_tag+conLang$tuple_tag) [x;y]`;

val BlockList_def = Define `
  (BlockList [] = BlockNil) /\
  (BlockList (x::xs) = BlockCons(x,BlockList xs))`;

val BlockBool_def = Define `BlockBool b = Block (bool_to_tag b) []`;
val BlockSome_def = Define `BlockSome x = Block (block_tag+conLang$some_tag) [x]`;

val BlockInl_def = Define `BlockInl x = Block (block_tag+inl_tag) [x]`;
val BlockInr_def = Define `BlockInr x = Block (block_tag+inr_tag) [x]`;

val BlockOtherS_def  = Define `BlockOtherS x  = Block (block_tag+others_tag) [x]`;
val BlockLongS_def   = Define `BlockLongS x   = Block (block_tag+longs_tag) [x]`;
val BlockNumberS_def = Define `BlockNumberS x = Block (block_tag+numbers_tag) [x]`;
val BlockStringS_def = Define `BlockStringS x = Block (block_tag+strings_tag) [x]`;
val BlockErrorS_def  = Define `BlockErrorS    = Block (block_tag+errors_tag) []`;

val Chr_def = Define `Chr c = Number (& (ORD c))`;

val BlockSym_def = Define `
  (BlockSym (StringS s) = BlockStringS (BlockList (MAP Chr s))) /\
  (BlockSym (OtherS s) = BlockOtherS (BlockList (MAP Chr s))) /\
  (BlockSym (LongS s) = BlockLongS (BlockList (MAP Chr s))) /\
  (BlockSym (ErrorS) = BlockErrorS) /\
  (BlockSym (NumberS n) = BlockNumberS (Number n))`;

val BlockNum3_def = Define `
  BlockNum3 (x,y,z) =
    BlockPair (Number (&x), BlockPair (Number (&y),Number (&z)))`;

val has_primitive_types_def = Define`
  has_primitive_types gtagenv ⇔
    FLOOKUP gtagenv ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0:num) ∧
    FLOOKUP gtagenv ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2) ∧
    FLOOKUP gtagenv ("SOME",TypeId(Short"option")) = SOME (conLang$some_tag,1)`

val LIST_TYPE_CHAR_BlockList = prove(
  ``(FLOOKUP cm ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0)) ∧
    (FLOOKUP cm ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2))
  ⇒
    ∀s l x y z b.
      LIST_TYPE CHAR s l ∧ v_bv (x,cm,y,z) l b
    ⇒ (b = BlockList (MAP Chr s))``,
  strip_tac >>
  simp[GSYM AND_IMP_INTRO] >>
  Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
    simp conv_rws >>
    simp[BlockList_def,BlockNil_def]) >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[BlockList_def,BlockCons_def] >>
  simp[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp conv_rws >>
  simp[Chr_def] >> rw[] >>
  fs[printingTheory.v_bv_def,printingTheory.exh_Cv_def] >>
  metis_tac[])

val LIST_TYPE_code_BlockList = prove(
  ``(FLOOKUP cm ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0)) ∧
    (FLOOKUP cm ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2))
  ⇒
    ∀s l x y z b.
      LIST_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM NUM)) s l ∧ v_bv (x,cm,y,z) l b
    ⇒ (b = BlockList (MAP BlockNum3 s))``,
  strip_tac >>
  simp[GSYM AND_IMP_INTRO] >>
  Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
    simp conv_rws >>
    simp[BlockList_def,BlockNil_def]) >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[PULL_EXISTS] >> simp conv_rws >>
  simp[BlockList_def,BlockCons_def] >>
  simp[FORALL_PROD,ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp conv_rws >>
  simp[BlockNum3_def,BlockPair_def] >>
  fs[printingTheory.v_bv_def,printingTheory.exh_Cv_def] >>
  metis_tac[])

val LIST_TYPE_v_bv = prove(
  ``(FLOOKUP (FST(SND d)) ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0)) ∧
    (FLOOKUP (FST(SND d)) ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2))
  ⇒
    ∀ls v. LIST_TYPE A ls v ∧ (∀x y. MEM x ls ∧ A x y ⇒ v_bv d y (f x)) ⇒
      v_bv d v (BlockList (MAP f ls))``,
   strip_tac >>
   Induct >> simp[ml_repl_stepTheory.LIST_TYPE_def] >- (
     PairCases_on`d` >>
     simp[printingTheory.v_bv_def] >> fs[] >>
     simp (PULL_EXISTS::conv_rws) >>
     simp[BlockList_def,BlockNil_def] ) >>
   PairCases_on`d`>>fs[PULL_EXISTS]>>
   simp (PULL_EXISTS::conv_rws) >> rw[] >>
   simp[BlockList_def,BlockCons_def] >>
   fs[printingTheory.v_bv_def,PULL_EXISTS,printingTheory.exh_Cv_def] >>
   last_x_assum(qspec_then`v2_2`mp_tac) >> simp[] >> strip_tac >>
   first_x_assum(qspec_then`h`mp_tac) >> simp[] >>
   disch_then(qspec_then`v2_1`mp_tac) >> simp[] >> strip_tac >>
   rpt(first_assum(match_exists_tac o concl)>>simp[])) |> GEN_ALL

val LEXER_FUN_SYMBOL_TYPE_v_bv = prove(
  ``(FLOOKUP (FST(SND d)) ("Errors",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (errors_tag,0)) ∧
    (FLOOKUP (FST(SND d)) ("Others",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (others_tag,1)) ∧
    (FLOOKUP (FST(SND d)) ("Longs",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (longs_tag,1)) ∧
    (FLOOKUP (FST(SND d)) ("Numbers",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (numbers_tag,1)) ∧
    (FLOOKUP (FST(SND d)) ("Strings",TypeId(Long"REPL""lexer_fun_symbol")) = SOME (strings_tag,1)) ∧
    (FLOOKUP (FST(SND d)) ("nil",TypeId(Short"list")) = SOME (conLang$nil_tag,0)) ∧
    (FLOOKUP (FST(SND d)) ("::",TypeId(Short"list")) = SOME (conLang$cons_tag,2))
    ⇒
    ∀x y. LEXER_FUN_SYMBOL_TYPE x y ⇒ v_bv d y (BlockSym x)``,
  strip_tac >> PairCases_on`d`>>fs[]>>
  Cases >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def,PULL_EXISTS] >>
  simp(ml_translatorTheory.INT_def::PULL_EXISTS::conv_rws) >>
  simp[BlockSym_def] >>
  simp[BlockStringS_def,
       BlockNumberS_def,
       BlockLongS_def,
       BlockOtherS_def,
       BlockErrorS_def] >>
  rw[] >>
  (LIST_TYPE_v_bv
   |> Q.ISPEC`Chr`
   |> SIMP_RULE std_ss [FORALL_PROD,GSYM AND_IMP_INTRO]
   |> (fn th => first_x_assum(mp_tac o MATCH_MP th))) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def,Chr_def] >>
  simp[printingTheory.v_bv_def,printingTheory.exh_Cv_def,PULL_EXISTS,GSYM CONJ_ASSOC] >>
  disch_then(qspecl_then[`d0`,`d2`,`d3`,`d4`]mp_tac) >>
  (discharge_hyps >- (
     simp[Once modLangProofTheory.v_to_i1_cases] >>
     simp[Once conLangProofTheory.v_to_i2_cases] >>
     simp[Once bytecodeProofTheory.Cv_bv_cases] )) >>
  METIS_TAC[])

val LIST_TYPE_exists = prove(
  ``∀x. (∀a. MEM a x ⇒ ∃v. A a v) ⇒ ∃l. LIST_TYPE A x l``,
  Induct >>
  simp[ml_repl_stepTheory.LIST_TYPE_def] >>
  METIS_TAC[])

val SPTREE_SPT_TYPE_exists = prove(
  ``∀p. ∃v. SPTREE_SPT_TYPE UNIT_TYPE p v``,
  Induct >>
  simp[ml_repl_stepTheory.SPTREE_SPT_TYPE_def,
       ml_translatorTheory.UNIT_TYPE_def] >>
  METIS_TAC[])

val STATE_TYPE_def = Define`
  STATE_TYPE = ^(INPUT_TYPE_def |> concl |> rhs |> rand |> rand)`

val tac =
    qx_gen_tac`p`>>PairCases_on`p` >>
    simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def]

val ltchartac =
  MATCH_MP_TAC LIST_TYPE_exists >>
  simp[ml_repl_stepTheory.CHAR_def] >>
  simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def]

val infer_t_ind =
  (TypeBase.induction_of``:infer_t``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val INFER_T_INFER_T_TYPE_exists = prove(
  ``∀a. ∃v. INFER_T_INFER_T_TYPE a v``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[ml_repl_stepTheory.INFER_T_INFER_T_TYPE_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[GSYM PULL_EXISTS,EVERY_MEM] >> rw[] >>
  TRY(Cases_on`t`)>>
  simp[ml_repl_stepTheory.AST_TCTOR_TYPE_def,PULL_EXISTS] >>
  TRY(Cases_on`i`)>>simp[ml_repl_stepTheory.AST_ID_TYPE_def]>>
  simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac )

val t_ind =
  (TypeBase.induction_of``:t``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val AST_T_TYPE_exists = prove(
  ``∀a. ∃v. AST_T_TYPE a v``,
  HO_MATCH_MP_TAC t_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def] >>
  simp[NUM_def,ml_translatorTheory.INT_def] >>
  rw[] >- ltchartac >>
  Cases_on`a`>>
  simp[ml_repl_stepTheory.AST_TCTOR_TYPE_def,PULL_EXISTS] >>
  TRY(Cases_on`i`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def]>>
      simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
  TRY (MATCH_MP_TAC LIST_TYPE_exists) >>
  fs[EVERY_MEM])

val COMPILER_COMPILER_STATE_TYPE_exists = prove(
  ``∀s. ∃v. COMPILER_COMPILER_STATE_TYPE s v``,
  Cases >> PairCases_on`p` >>
  simp[ml_repl_stepTheory.COMPILER_COMPILER_STATE_TYPE_def] >>
  simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_repl_stepTheory.FMAP_TYPE_def,PULL_EXISTS,ml_repl_stepTheory.FMAP_EQ_ALIST_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  qexists_tac`fmap_to_alist f` >>
  qexists_tac`fmap_to_alist p1` >> simp[] >>
  qexists_tac`fmap_to_alist p0'` >> simp[] >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- (
    MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    simp[ml_repl_stepTheory.FMAP_TYPE_def,PULL_EXISTS,ml_repl_stepTheory.FMAP_EQ_ALIST_def] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexists_tac`fmap_to_alist p1` >> simp[] >>
    MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    ltchartac ) >>
  conj_tac >- (
    MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    ltchartac ) >>
  conj_tac >- (
    PairCases_on`p0` >>
    simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    simp[ml_repl_stepTheory.FMAP_TYPE_def,PULL_EXISTS,ml_repl_stepTheory.FMAP_EQ_ALIST_def] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexists_tac`fmap_to_alist p03` >>
    qexists_tac`fmap_to_alist p02` >> simp[] >>
    qexists_tac`fmap_to_alist p01` >> simp[] >>
    simp[GSYM PULL_EXISTS] >>
    rw[] >> MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    TRY(Cases_on`p2`)>>
    simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
    simp[ml_repl_stepTheory.OPTION_TYPE_def,ml_repl_stepTheory.FMAP_TYPE_def,ml_repl_stepTheory.FMAP_EQ_ALIST_def] >>
    TRY (
      Cases_on`x`>>simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] ) >>
    TRY (
      Cases_on`i`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def] >>
      simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexists_tac`fmap_to_alist p1` >> simp[] >>
    MATCH_MP_TAC LIST_TYPE_exists >> tac >> rw[] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
    Cases_on`p2`>>
    simp[ml_repl_stepTheory.OPTION_TYPE_def] >>
    Cases_on`x`>>simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
    Cases_on`i`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def] >>
    simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
  MATCH_MP_TAC LIST_TYPE_exists >> tac >>
  rw[] >>
  Cases_on`p0`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def] >>
  simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
  simp[SPTREE_SPT_TYPE_exists])

val REPL_FUN_REPL_FUN_STATE_TYPE_exists = prove(
 ``∀s. ∃v. REPL_FUN_REPL_FUN_STATE_TYPE s v``,
 Cases >>
 PairCases_on`p` >>
 Cases_on`c`>>
 PairCases_on`p` >>
 simp[ml_repl_stepTheory.REPL_FUN_REPL_FUN_STATE_TYPE_def] >>
 simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
 simp[GSYM PULL_EXISTS] >>
 rpt conj_tac >>
 TRY ( ltchartac >> rw[] >> ltchartac >> NO_TAC) >>
 TRY (
   MATCH_MP_TAC LIST_TYPE_exists >>
   strip_tac >> simp[GSYM PULL_EXISTS] >> rw[] >>
   Cases_on`a`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def]>>
   simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac >> NO_TAC) >>
 TRY (
   MATCH_MP_TAC LIST_TYPE_exists >>
   tac >>
   strip_tac >>
   simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   tac >> simp[ml_repl_stepTheory.PAIR_TYPE_def] >>
   simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   rw[] >> TRY ltchartac >> simp[AST_T_TYPE_exists] >>
   Cases_on`p3`>>simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def]>>
   TRY(Cases_on`i`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def,PULL_EXISTS])>>
   simp[GSYM PULL_EXISTS] >> rw[] >>
   TRY ltchartac >> rw[] >> TRY ltchartac >> NO_TAC) >>
 TRY (
   MATCH_MP_TAC LIST_TYPE_exists >>
   tac >>
   strip_tac >>
   simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   rw[] >> TRY ltchartac >> simp[AST_T_TYPE_exists] >>
   Cases_on`p3`>>simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def]>>
   TRY(Cases_on`i`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def,PULL_EXISTS])>>
   simp[GSYM PULL_EXISTS] >> rw[] >>
   TRY ltchartac >> rw[] >> TRY ltchartac >> NO_TAC) >>
 TRY (
   MATCH_MP_TAC LIST_TYPE_exists >>
   tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   simp[INFER_T_INFER_T_TYPE_exists] ) >>
 TRY (
   MATCH_MP_TAC LIST_TYPE_exists >>
   tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   simp[INFER_T_INFER_T_TYPE_exists] ) >>
 simp[COMPILER_COMPILER_STATE_TYPE_exists])

val INPUT_TYPE_exists = prove(
  ``STATE_TYPE s v ⇒ ∃w. INPUT_TYPE (SOME (ts,s)) (Conv(SOME("SOME",TypeId(Short"option")))[Conv(NONE)[w;v]])``,
  simp[STATE_TYPE_def,INPUT_TYPE_def,ml_repl_stepTheory.OPTION_TYPE_def,PULL_EXISTS] >>
  PairCases_on`s` >>
  simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[ml_repl_stepTheory.FMAP_TYPE_def,PULL_EXISTS,ml_repl_stepTheory.FMAP_EQ_ALIST_def] >>
  simp[GSYM PULL_EXISTS] >> rw[REPL_FUN_REPL_FUN_STATE_TYPE_exists] >>
  MATCH_MP_TAC LIST_TYPE_exists >>
  Cases >>
  simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def] >> rw[] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  ltchartac )

val LIST_TYPE_closed = prove(
  ``∀x. (∀a v. MEM a x ∧ A a v ⇒ closed v) ⇒ ∀l. LIST_TYPE A x l ⇒ closed l``,
  Induct >>
  simp[ml_repl_stepTheory.LIST_TYPE_def] >>
  simp[PULL_EXISTS] >> METIS_TAC[])

val PAIR_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed y) ∧
    (∀x y. B x y ⇒ closed y) ∧
    PAIR_TYPE A B a b ⇒
    closed b``,
  gen_tac >>
  PairCases_on`a` >>
  simp[ml_repl_stepTheory.PAIR_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >> METIS_TAC[])

val OPTION_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed y) ∧ OPTION_TYPE A a b ⇒ closed b``,
  Cases >> simp[ml_repl_stepTheory.OPTION_TYPE_def] >> rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >> METIS_TAC[])

val AST_ID_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed y) ∧ AST_ID_TYPE A a b ⇒ closed b``,
  Cases >> simp[ml_repl_stepTheory.AST_ID_TYPE_def] >> rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >> TRY(METIS_TAC[]) >>
  qmatch_abbrev_tac`closed z` >>
  qmatch_assum_rename_tac`B c d`[] >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`,ml_repl_stepTheory.CHAR_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val AST_TCTOR_TYPE_closed = prove(
  ``∀a. AST_TCTOR_TYPE a b ⇒ closed b``,
  Cases >>
  simp[ml_repl_stepTheory.AST_TCTOR_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )

val INFER_T_INFER_T_TYPE_closed = prove(
  ``∀a b. INFER_T_INFER_T_TYPE a b ⇒ closed b``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[ml_repl_stepTheory.INFER_T_INFER_T_TYPE_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >>
  TRY (MATCH_MP_TAC (GEN_ALL AST_TCTOR_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val AST_T_TYPE_closed = prove(
  ``∀a b. AST_T_TYPE a b ⇒ closed b``,
  HO_MATCH_MP_TAC t_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >>
  TRY (MATCH_MP_TAC (GEN_ALL AST_TCTOR_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_closed = prove(
  ``∀a b. SEMANTICPRIMITIVES_TID_OR_EXN_TYPE a b ⇒ closed b``,
  Cases >> simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL free_varsTheory.closed_rules))) >>
  rw[] >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[] >> unabbrev_all_tac >>
  qmatch_abbrev_tac`closed x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val SPTREE_SPT_TYPE_UNIT_TYPE_closed = prove(
  ``∀a b. SPTREE_SPT_TYPE UNIT_TYPE a b ⇒ closed b``,
  Induct >>
  simp[ml_repl_stepTheory.SPTREE_SPT_TYPE_def,PULL_EXISTS,
       ml_translatorTheory.UNIT_TYPE_def])

val COMPILER_COMPILER_STATE_TYPE_closed = prove(
  ``COMPILER_COMPILER_STATE_TYPE x y ⇒ closed y``,
  Cases_on`x` >>
  PairCases_on`p` >>
  simp[ml_repl_stepTheory.COMPILER_COMPILER_STATE_TYPE_def] >>
  simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_repl_stepTheory.FMAP_TYPE_def,PULL_EXISTS,ml_repl_stepTheory.FMAP_EQ_ALIST_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  rw[] >>
  rpt (
    qmatch_abbrev_tac`closed x` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) PAIR_TYPE_closed >>
      simp[Abbr`A`,Abbr`B`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) OPTION_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`SEMANTICPRIMITIVES_TID_OR_EXN_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_closed >>
      simp[]
    ) ORELSE (
      qmatch_assum_abbrev_tac`SPTREE_SPT_TYPE UNIT_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) SPTREE_SPT_TYPE_UNIT_TYPE_closed >>
      simp[]
    ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
      simp[Abbr`A`]
    )) >>
    fs[ml_repl_stepTheory.FMAP_TYPE_def,ml_repl_stepTheory.FMAP_EQ_ALIST_def] >>
    rw[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val REPL_FUN_REPL_FUN_STATE_TYPE_closed = prove(
  ``REPL_FUN_REPL_FUN_STATE_TYPE a v ⇒ closed v``,
  Cases_on`a`>>simp[ml_repl_stepTheory.REPL_FUN_REPL_FUN_STATE_TYPE_def,PULL_EXISTS] >>
  PairCases_on`p` >>
  simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  rw[] >>
  TRY(MATCH_MP_TAC (GEN_ALL COMPILER_COMPILER_STATE_TYPE_closed) >>
      HINT_EXISTS_TAC >> rw[] ) >>
  rpt (
    TRY (MATCH_MP_TAC (GEN_ALL AST_TCTOR_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL INFER_T_INFER_T_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL AST_T_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    qmatch_abbrev_tac`closed x` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) PAIR_TYPE_closed >>
      simp[Abbr`A`,Abbr`B`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) OPTION_TYPE_closed >>
      simp[Abbr`A`]
    ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
      simp[Abbr`A`]
    )) >>
    rw[ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val INPUT_TYPE_closed = prove(
  ``INPUT_TYPE x y ⇒ closed y``,
  simp[INPUT_TYPE_def] >>
  Cases_on`x` >>
  simp[ml_repl_stepTheory.OPTION_TYPE_def] >>
  rw[] >> simp[] >>
  qmatch_assum_rename_tac `PAIR_TYPE X Y s p`["X","Y"] >>
  PairCases_on`s` >>
  fs[ml_repl_stepTheory.PAIR_TYPE_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[ml_repl_stepTheory.FMAP_TYPE_def] >>
  rw[] >- (
    qmatch_rename_tac`closed ls`[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE A vv ls` >>
    Q.ISPECL_THEN[`A`,`vv`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`A`] >>
    Cases >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    rw[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE B s bb` >>
    Q.ISPECL_THEN[`B`,`s`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`B`,ml_repl_stepTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )
  >- (
    qmatch_rename_tac`closed ls`[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE A vv ls` >>
    Q.ISPECL_THEN[`A`,`vv`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`A`] >>
    Cases >> simp[ml_repl_stepTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )
  >> METIS_TAC[REPL_FUN_REPL_FUN_STATE_TYPE_closed])

(* Relationship between the invariant and the references *)

val repl_globals_env_def = Define`
  repl_globals_env = THE (FLOOKUP (FST(FST compile_repl_decs).globals_env) "REPL")`
val repl_globals_env_eq =
  ``repl_globals_env``
  |> (REWR_CONV repl_globals_env_def THENC
      PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq]
      THENC EVAL)
val repl_globals_env_flookup = prove(
  ``FLOOKUP (FST (FST compile_repl_decs).globals_env) "REPL" = SOME map ⇒
    map = repl_globals_env``,
  rw[repl_globals_env_def])

val iind_def = Define`
  iind = THE(FLOOKUP repl_globals_env "input")`
val iind_eq =
  ``iind``
  |> (REWR_CONV iind_def
      THENC PURE_ONCE_REWRITE_CONV[repl_globals_env_eq]
      THENC EVAL)

val oind_def = Define`
  oind = THE(FLOOKUP repl_globals_env "output")`
val oind_eq =
  ``oind``
  |> (REWR_CONV oind_def
      THENC PURE_ONCE_REWRITE_CONV[repl_globals_env_eq]
      THENC EVAL)

val inds_flookup = prove(
  ``FLOOKUP repl_globals_env "input" = SOME x ∧
    FLOOKUP repl_globals_env "output" = SOME y ⇒
    x = iind ∧ y = oind``,
  rw[iind_def,oind_def])

val ptrs_exist = prove(
  ``∃iptr optr.
    iind < LENGTH repl_bc_state.globals ∧
    oind < LENGTH repl_bc_state.globals ∧
    EL iind repl_bc_state.globals = SOME (RefPtr iptr) ∧
    EL oind repl_bc_state.globals = SOME (RefPtr optr)``,
  assume_tac COMPILER_RUN_INV_init >>
  fs[COMPILER_RUN_INV_def] >>
  pop_assum kall_tac >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls`>>fs[update_io_def] >>
  `∃x y z. bootstrap_grd = (x,y,z)` by METIS_TAC[pair_CASES] >>
  fs[env_rs_def]>>
  rator_x_assum`to_i1_invariant`mp_tac >>
  simp[modLangProofTheory.to_i1_invariant_def] >>
  simp[Once modLangProofTheory.v_to_i1_cases] >>
  rw[] >> simp[] >>
  rator_x_assum`global_env_inv_flat`mp_tac >>
  simp[repl_env_def,Once modLangProofTheory.v_to_i1_cases] >>
  strip_tac >>
  first_assum(qspec_then`"input"`mp_tac) >>
  first_x_assum(qspec_then`"output"`mp_tac) >>
  simp[] >> rw[] >> simp[] >>
  `map = repl_globals_env`  by (
    simp[repl_globals_env_def] ) >>
  rw[] >>
  imp_res_tac inds_flookup >> rw[] >>
  fs[conLangProofTheory.to_i2_invariant_def] >>
  fs[LIST_REL_EL_EQN,bytecodeProofTheory.Cenv_bs_def] >>
  rator_x_assum`s_refs`mp_tac >>
  simp[bytecodeProofTheory.s_refs_def,LIST_REL_EL_EQN] >>
  simp[optionTheory.OPTREL_def] >> strip_tac >>
  fs[Once modLangProofTheory.v_to_i1_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[optionTheory.OPTREL_def] >>
  qmatch_assum_rename_tac`EL iind grd0 = SOME (Loc_i1 iloc)`[] >>
  qmatch_assum_rename_tac`EL oind grd0 = SOME (Loc_i1 (iloc+1))`[] >>
  first_assum(qspec_then`iind`mp_tac) >>
  first_x_assum(qspec_then`oind`mp_tac) >>
  qpat_assum`∀n. n < LENGTH genv2 ⇒ P`(fn th =>
    (qspec_then`iind`mp_tac) th >>
    (qspec_then`oind`mp_tac) th) >>
  qpat_assum`∀n. n < LENGTH grd0 ⇒ P`(fn th =>
    (qspec_then`iind`mp_tac) th >>
    (qspec_then`oind`mp_tac) th) >>
  simp[] >> ntac 2 strip_tac >>
  simp[] >> ntac 2 strip_tac >>
  simp[] >> ntac 2 strip_tac >>
  fs[Once conLangProofTheory.v_to_i2_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[relationTheory.O_DEF,printingTheory.exh_Cv_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[Q.SPEC`CLoc X`(CONJUNCT1 (SPEC_ALL bytecodeProofTheory.Cv_bv_cases))])

val ptrs_def = new_specification("ptrs_def",["iptr","optr"],ptrs_exist)

val COMPILER_RUN_INV_references = store_thm("COMPILER_RUN_INV_references",
  ``∀bs grd input output.
    COMPILER_RUN_INV bs grd input output ⇒
    bs.globals = repl_bc_state.globals ∧
    iloc+1 < LENGTH (SND(SND grd)).sm ∧
    EL iloc (SND(SND grd)).sm = iptr ∧
    EL (iloc+1) (SND(SND grd)).sm = optr ∧
    ∃ibc obc.
      FLOOKUP bs.refs iptr = SOME (ValueArray [ibc]) ∧
      FLOOKUP bs.refs optr = SOME (ValueArray [obc]) ∧
      let gtagenv = FST(SND grd) in
      let d = (FST grd,gtagenv,(FST compile_repl_decs).exh,mk_pp (SND (SND grd)) bs) in
      v_bv d input ibc ∧ v_bv d output obc ∧
      has_primitive_types gtagenv ∧
      (∀n a t.
        (lookup n (Tmod_tys "REPL" ml_repl_module_decls) = SOME (a,t)) ⇒
        let tag = FST(lookup_tag_flat n repl_contags_env) in
          (FLOOKUP gtagenv (n,t) = SOME(tag,a)))``,
  rpt gen_tac >>
  simp[COMPILER_RUN_INV_def] >> strip_tac >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls`>>fs[update_io_def] >>
  PairCases_on`grd`>> fs[env_rs_def]>>
  rator_x_assum`to_i1_invariant`mp_tac >>
  simp[modLangProofTheory.to_i1_invariant_def] >>
  simp[Once modLangProofTheory.v_to_i1_cases] >>
  strip_tac >> simp[] >>
  rator_x_assum`global_env_inv_flat`mp_tac >>
  simp[repl_env_def,Once modLangProofTheory.v_to_i1_cases] >>
  strip_tac >>
  first_assum(qspec_then`"input"`mp_tac) >>
  first_x_assum(qspec_then`"output"`mp_tac) >>
  simp[] >> strip_tac >> strip_tac >> simp[] >>
  `map = repl_globals_env`  by (
    simp[repl_globals_env_def] ) >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac inds_flookup >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[CONJ_ASSOC] >>
  qmatch_abbrev_tac`A ∧ B` >>
  qunabbrev_tac`B` >>
  fs[conLangProofTheory.to_i2_invariant_def] >>
  fs[LIST_REL_EL_EQN,bytecodeProofTheory.Cenv_bs_def] >>
  rator_x_assum`s_refs`mp_tac >>
  simp[bytecodeProofTheory.s_refs_def,LIST_REL_EL_EQN] >>
  simp[optionTheory.OPTREL_def] >> strip_tac >>
  fs[Once modLangProofTheory.v_to_i1_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[optionTheory.OPTREL_def] >>
  qmatch_assum_rename_tac`EL iind grd0 = SOME (Loc_i1 iloc)`[] >>
  qmatch_assum_rename_tac`EL oind grd0 = SOME (Loc_i1 (iloc+1))`[] >>
  first_assum(qspec_then`iind`mp_tac) >>
  first_x_assum(qspec_then`oind`mp_tac) >>
  qpat_assum`∀n. n < LENGTH genv2 ⇒ P`(fn th =>
    (qspec_then`iind`mp_tac) th >>
    (qspec_then`oind`mp_tac) th) >>
  qpat_assum`∀n. n < LENGTH grd0 ⇒ P`(fn th =>
    (qspec_then`iind`mp_tac) th >>
    (qspec_then`oind`mp_tac) th) >>
  simp[] >> ntac 2 strip_tac >>
  simp[] >> ntac 2 strip_tac >>
  simp[] >> ntac 2 strip_tac >>
  fs[Once conLangProofTheory.v_to_i2_cases] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[relationTheory.O_DEF,printingTheory.exh_Cv_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[Q.SPEC`CLoc X`(CONJUNCT1 (SPEC_ALL bytecodeProofTheory.Cv_bv_cases))] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[libTheory.el_check_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_assum(qspec_then`iloc`mp_tac) >>
  first_x_assum(qspec_then`iloc+1`mp_tac) >>
  simp[EL_MAP] >>
  simp[finite_mapTheory.FLOOKUP_DEF] >>
  ntac 2 strip_tac >>
  fs[bytecodeProofTheory.good_rd_def] >>
  strip_assume_tac ptrs_def >> fs[] >>
  conj_tac >- fs[markerTheory.Abbrev_def] >>
  rator_x_assum`EVERY`mp_tac >>
  simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  strip_tac >>
  simp[printingTheory.v_bv_def,PULL_EXISTS] >>
  fs[modLangProofTheory.s_to_i1_cases,conLangProofTheory.s_to_i2_cases] >>
  fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
  qpat_assum`∀n. n < LENGTH X ⇒ sv_to_i1 B Y Z`mp_tac >>
  disch_then(fn th => (qspec_then`iloc`mp_tac th) >>
                      (qspec_then`iloc+1`mp_tac th)) >>
  simp[modLangProofTheory.sv_to_i1_cases] >> ntac 2 strip_tac >>
  qpat_assum`∀n. n < LENGTH X ⇒ sv_to_i2 B Y Z`mp_tac >>
  disch_then(fn th => (qspec_then`iloc`mp_tac th) >>
                      (qspec_then`iloc+1`mp_tac th)) >>
  simp[conLangProofTheory.sv_to_i2_cases] >> ntac 2 strip_tac >>
  qpat_assum`∀n. n < LENGTH X ⇒ sv_rel B Y Z`mp_tac >>
  disch_then(fn th => (qspec_then`iloc`mp_tac th) >>
                      (qspec_then`iloc+1`mp_tac th)) >>
  simp[evalPropsTheory.sv_rel_cases] >>
  ntac 2 strip_tac >>
  fs[bytecodeProofTheory.sv_refv_rel_cases] >> rfs[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``Cv_bv`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``Cv_bv`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[printingTheory.exh_Cv_def,PULL_EXISTS] >>
  fs[relationTheory.O_DEF,printingTheory.exh_Cv_def] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``syneq`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``syneq`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[GSYM CONJ_ASSOC] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``v_to_i1`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  reverse conj_tac >- (
    simp[has_primitive_types_def] >>
    rator_x_assum`cenv_inv`mp_tac >>
    simp[conLangProofTheory.cenv_inv_def] >>
    simp[conLangProofTheory.envC_tagged_def] >>
    strip_tac >>
    `∃x. FST(SND(FST compile_repl_decs).contags_env) = (x, short_contags_env)` by (
      simp[short_contags_env_def] >>
      METIS_TAC[pair_CASES,SND,PAIR_EQ] ) >>
    first_assum(qspec_then`Short"nil"`mp_tac) >>
    first_assum(qspec_then`Short"::"`mp_tac) >>
    first_x_assum(qspec_then`Short"SOME"`mp_tac) >>
    ASM_REWRITE_TAC[] >>
    REWRITE_TAC[initSemEnvTheory.prim_sem_env_eq,optionTheory.THE_DEF] >>
    REWRITE_TAC[
      semanticPrimitivesTheory.lookup_con_id_def,
      semanticPrimitivesTheory.merge_envC_def] >>
    EVAL_TAC >> simp[] >>
    REWRITE_TAC[short_contags_env_eq] >>
    EVAL_TAC >> rw[]) >>
  rpt gen_tac >> strip_tac >>
  rator_x_assum`cenv_inv`mp_tac >>
  simp[conLangProofTheory.cenv_inv_def] >>
  simp[conLangProofTheory.envC_tagged_def] >>
  strip_tac >>
  first_x_assum(qspec_then`Long"REPL"n`mp_tac) >>
  Q.PAT_ABBREV_TAC`p:envC = merge_envC X init_envC` >>
  `∃x y. p = (x,y)` by METIS_TAC[pair_CASES] >>
  qunabbrev_tac`p` >>
  simp[semanticPrimitivesTheory.lookup_con_id_def] >>
  qmatch_assum_abbrev_tac`merge_envC([("REPL",e)],emp) init_envC = X` >>
  `lookup "REPL" x = SOME e` by (
    qmatch_assum_rename_tac`merge_envC Y p = X`["Y"] >>
    Cases_on`p`>>fs[semanticPrimitivesTheory.merge_envC_def] >>
    fs[libTheory.merge_def,Abbr`X`] >> rw[] ) >>
  Cases_on`FST(SND(FST compile_repl_decs).contags_env)` >>
  simp[conLangTheory.lookup_tag_env_def,astTheory.id_to_n_def] >>
  strip_tac >>
  fs[conLangProofTheory.gtagenv_wf_def] >>
  fs[finite_mapTheory.FLOOKUP_DEF] >>
  simp[repl_contags_env_def,finite_mapTheory.FLOOKUP_DEF] >>
  IF_CASES_TAC >> fs[] >> METIS_TAC[])

(* Changing the references preserves the invariant *)

fun just_exists_suff_tac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = GEN_ALL(PART_MATCH (snd o dest_imp) th (hd bs))
    val (vs,c) = strip_forall (concl th)
    val (b',_) = dest_imp c
  in
    suff_tac(list_mk_exists(ws,list_mk_conj(b'::tl bs))) >|[assume_tac th,ALL_TAC]
  end g

val COMPILER_RUN_INV_INR = store_thm("COMPILER_RUN_INV_INR",
  ``COMPILER_RUN_INV bs grd inp outp /\ OUTPUT_TYPE (INR (msg,s)) outp ==>
    ?s_bc_val.
      iptr IN FDOM bs.refs /\
      (FLOOKUP bs.refs optr =
         SOME (ValueArray [BlockInr (BlockPair (BlockList (MAP Chr msg),s_bc_val))])) /\
      !ts.
        let inp_bc_val = BlockSome (BlockPair (BlockList (MAP BlockSym ts),s_bc_val))
        in
          ?grd new_inp.
            INPUT_TYPE (SOME (ts,s)) new_inp /\
            COMPILER_RUN_INV (bs with refs := bs.refs |+ (iptr,ValueArray [inp_bc_val]))
              grd new_inp outp``,
  rw[] >>
  imp_res_tac COMPILER_RUN_INV_references >> simp[] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- fs[finite_mapTheory.FLOOKUP_DEF] >>
  fs[OUTPUT_TYPE_def] >>
  fs[ml_repl_stepTheory.SUM_TYPE_def] >>
  fs[ml_repl_stepTheory.PAIR_TYPE_def] >>
  rw[] >>
  fs[LET_THM] >>
  rator_x_assum`v_bv`mp_tac >>
  simp[printingTheory.v_bv_def] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  rw[] >>
  first_assum(qspecl_then[`"Inr"`,`1`,`TypeId(Long"REPL""sum")`]mp_tac) >>
  discharge_hyps >- simp[sum_tags_exist] >>
  simp[Once UNCURRY] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  simp[BlockInr_def,inr_tag_def] >>
  simp[BlockPair_def] >>
  fs[has_primitive_types_def] >>
  imp_res_tac LIST_TYPE_CHAR_BlockList >>
  pop_assum kall_tac >>
  conj_asm1_tac >- (
    pop_assum mp_tac >>
    simp[printingTheory.v_bv_def,printingTheory.exh_Cv_def,PULL_EXISTS] >>
    disch_then match_mp_tac >>
    METIS_TAC[] ) >>
  rpt gen_tac >> strip_tac >>
  fs[GSYM STATE_TYPE_def] >>
  imp_res_tac INPUT_TYPE_exists >>
  first_x_assum(qspec_then`ts`strip_assume_tac) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rator_x_assum`COMPILER_RUN_INV`mp_tac >>
  simp[COMPILER_RUN_INV_def] >> strip_tac >>
  simp[LEFT_EXISTS_AND_THM] >>
  reverse conj_tac >- (
    pop_assum SUBST1_TAC >>
    simp[bytecodeTheory.bc_state_component_equality] ) >>
  simp[EXISTS_PROD] >>
  PairCases_on`grd` >>
  qexists_tac`grd0` >> qexists_tac`grd1` >>
  rator_x_assum`env_rs`mp_tac >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls` >>
  simp[update_io_def] >>
  simp[env_rs_def] >> strip_tac >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    qpat_assum`EVERY (sv_every closed) (LUPDATE X Y Z)`mp_tac >>
    simp[EVERY_MEM,MEM_LUPDATE,PULL_EXISTS] >>
    strip_tac >> gen_tac >> strip_tac >- METIS_TAC[] >>
    BasicProvers.VAR_EQ_TAC >>
    simp[EL_LUPDATE] >>
    reverse IF_CASES_TAC >- (
      first_x_assum(qspec_then`EL j r`match_mp_tac) >>
      simp[EL_LUPDATE] >> METIS_TAC[] ) >>
    simp[] >>
    conj_tac >- ( imp_res_tac INPUT_TYPE_closed >> fs[] ) >>
    assume_tac (CONJUNCT2 repl_env_def) >> rfs[] >>
    fsrw_tac[boolSimps.DNF_ss][] ) >>
  exists_suff_gen_then (mp_tac o RW[GSYM AND_IMP_INTRO]) (INST_TYPE[alpha|->``:num``]to_i1_invariant_change_store) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  disch_then just_exists_suff_tac >- (
    strip_tac >>
    first_x_assum(fn th=> first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rpt(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[modLangProofTheory.to_i1_invariant_def] >>
  rator_x_assum`s_to_i1`mp_tac >>
  simp[modLangProofTheory.s_to_i1_cases] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`v_bv data inp ibc` >>
  `v_bv data w (BlockList (MAP BlockSym ts))` by (
    fs[INPUT_TYPE_def,ml_repl_stepTheory.OPTION_TYPE_def,ml_repl_stepTheory.PAIR_TYPE_def,Abbr`data`] >>
    MATCH_MP_TAC (MP_CANON LIST_TYPE_v_bv) >>
    HINT_EXISTS_TAC >> simp[] >> rw[] >>
    match_mp_tac(MP_CANON (GEN_ALL LEXER_FUN_SYMBOL_TYPE_v_bv)) >>
    simp[] >>
    rpt conj_tac >>
    qmatch_abbrev_tac`FLOOKUP gtagenv (n,a) = SOME b` >>
    first_x_assum(qspec_then`n`mp_tac) >>
    disch_then(qspec_then`a`mp_tac o CONV_RULE(SWAP_FORALL_CONV)) >>
    simp[Abbr`n`,sym_tags_exist] >>
    rw[Abbr`b`] >>
    rw[errors_tag_def,others_tag_def,longs_tag_def,numbers_tag_def,strings_tag_def]) >>
  qunabbrev_tac`data` >>
  pop_assum(strip_assume_tac o SIMP_RULE (srw_ss()) [printingTheory.v_bv_def]) >>
  CONV_TAC SWAP_EXISTS_CONV >>
  Q.PAT_ABBREV_TAC`inp2 = Conv X [Conv Y [w; Z]]` >>
  qmatch_assum_abbrev_tac`v_bv data inp ibc` >>
  `v_bv data inp2 inp_bc_val` by (
    simp(Abbr`inp2`::Abbr`data`::PULL_EXISTS::conv_rws) >>
    simp[Abbr`inp_bc_val`,BlockSome_def] >>
    HINT_EXISTS_TAC >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[printingTheory.exh_Cv_def] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[]) >>
  qunabbrev_tac`data` >>
  pop_assum(strip_assume_tac o SIMP_RULE (srw_ss()) [printingTheory.v_bv_def]) >>
  qmatch_assum_rename_tac`v_to_i1 grd0 inp2 v12`[] >>
  qexists_tac`LUPDATE (Refv v12) iloc s1` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[Abbr`inp2`] >>
    assume_tac(CONJUNCT2 repl_env_def) >> rfs[] >>
    rw[] >>
    simp[modLangProofTheory.sv_to_i1_cases]) >>
  exists_suff_gen_then(mp_tac o RW[GSYM AND_IMP_INTRO]) (INST_TYPE[beta|->``:num``]to_i2_invariant_change_store) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >> (CONV_TAC (RESORT_EXISTS_CONV List.rev)) >>
  qexists_tac`genv2` >>
  pop_assum just_exists_suff_tac >- (
    strip_tac >>
    first_x_assum(fn th=> first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rpt(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[conLangProofTheory.to_i2_invariant_def] >>
  rator_x_assum`s_to_i2`mp_tac >>
  simp[conLangProofTheory.s_to_i2_cases] >>
  strip_tac >>
  qmatch_assum_rename_tac`v_to_i2 grd1 v12 v22`[] >>
  qexists_tac`LUPDATE (Refv v22) iloc s2` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >>
    rw[] >> rw[conLangProofTheory.sv_to_i2_cases]) >>
  simp[miscTheory.LIST_REL_O,PULL_EXISTS,evalPropsTheory.sv_rel_O] >>
  qmatch_assum_rename_tac`v_to_exh Z v22 v23`["Z"] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  fs[miscTheory.LIST_REL_O,evalPropsTheory.sv_rel_O] >>
  qexists_tac`LUPDATE (Refv v23) iloc l3` >>
  simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >> rw[]) >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  qmatch_assum_rename_tac`exh_Cv v23 v24`[] >>
  qexists_tac`LUPDATE (Refv v24) iloc Cs` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >> rw[]) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  conj_tac >- (
    rator_x_assum`closed_vlabs`mp_tac >>
    simp[intLangExtraTheory.closed_vlabs_def,
         intLangExtraTheory.all_vlabs_csg_def] >>
    simp[EVERY_MEM,intLangExtraTheory.vlabs_csg_def] >>
    strip_tac >>
    `vlabs v24 = {} ∧ all_vlabs v24` by (
      MATCH_MP_TAC (MP_CANON (GEN_ALL no_closures_vlabs)) >>
      fs[printingTheory.exh_Cv_def] >>
      rw[Once CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      METIS_TAC[EqualityType_thm,EqualityType_INPUT_TYPE]) >>
    conj_tac >- (
      fs[intLangExtraTheory.store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER] >>
      METIS_TAC[MEM_LUPDATE_E,evalPropsTheory.dest_Refv_def] ) >>
    fs[intLangExtraTheory.vlabs_list_MAP,PULL_EXISTS] >>
    fs[intLangExtraTheory.store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER] >>
    METIS_TAC[MEM_LUPDATE_E,pred_setTheory.NOT_IN_EMPTY,evalPropsTheory.dest_Refv_def] ) >>
  qexists_tac`grd2` >>
  MATCH_MP_TAC bytecodeProofTheory.Cenv_bs_change_store >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[bytecodeTheory.bc_state_component_equality] >>
  `iloc < LENGTH grd2.sm ∧ EL iloc grd2.sm = iptr` by simp[] >>
  `MEM iptr grd2.sm` by METIS_TAC[MEM_EL] >>
  reverse conj_tac >- rw[] >>
  fs[bytecodeProofTheory.Cenv_bs_def,bytecodeProofTheory.s_refs_def,bytecodeProofTheory.good_rd_def] >>
  conj_tac >- (
    fs[miscTheory.FEVERY_ALL_FLOOKUP] >> rw[] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[UNCURRY] >> strip_tac >>
    simp[finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[] >> fs[] ) >>
  conj_tac >- fs[EVERY_MEM] >>
  fs[LIST_REL_EL_EQN,EL_MAP,EL_LUPDATE] >>
  simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
  rw[] >> fs[] >- METIS_TAC[EL_ALL_DISTINCT_EL_EQ] >>
  METIS_TAC[EL_MAP])

val COMPILER_RUN_INV_INL = store_thm("COMPILER_RUN_INV_INL",
  ``COMPILER_RUN_INV bs grd inp outp /\ OUTPUT_TYPE (INL (code,s)) outp ==>
    ?s_bc_val.
      iptr IN FDOM bs.refs /\
      (FLOOKUP bs.refs optr =
         SOME (ValueArray [BlockInl (BlockPair (BlockList (MAP BlockNum3 code),s_bc_val))])) /\
      !ts b.
        let inp_bc_val = BlockSome (BlockPair (BlockList (MAP BlockSym ts),
                                      BlockPair (BlockBool b,s_bc_val)))
        in
          ?grd new_inp.
            INPUT_TYPE (SOME (ts,b,s)) new_inp /\
            COMPILER_RUN_INV (bs with refs := bs.refs |+ (iptr,ValueArray[inp_bc_val]))
              grd new_inp outp``,
  rw[] >>
  imp_res_tac COMPILER_RUN_INV_references >> simp[] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- fs[finite_mapTheory.FLOOKUP_DEF] >>
  fs[OUTPUT_TYPE_def] >>
  fs[ml_repl_stepTheory.SUM_TYPE_def] >>
  fs[ml_repl_stepTheory.PAIR_TYPE_def] >>
  rw[] >>
  fs[LET_THM] >>
  rator_x_assum`v_bv`mp_tac >>
  simp[printingTheory.v_bv_def] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  simp conv_rws >> simp[PULL_EXISTS] >>
  rw[] >>
  first_assum(qspecl_then[`"Inl"`,`1`,`TypeId(Long"REPL""sum")`]mp_tac) >>
  discharge_hyps >- simp[sum_tags_exist] >>
  simp[Once UNCURRY] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  simp[BlockInl_def,inl_tag_def] >>
  simp[BlockPair_def] >>
  fs[has_primitive_types_def] >>
  imp_res_tac LIST_TYPE_code_BlockList >>
  pop_assum kall_tac >>
  conj_asm1_tac >- (
    pop_assum mp_tac >>
    simp[printingTheory.v_bv_def,printingTheory.exh_Cv_def,PULL_EXISTS] >>
    disch_then match_mp_tac >>
    METIS_TAC[] ) >>
  rpt gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac`A s v1_2` >>
  `STATE_TYPE (b,s) (Conv NONE [Litv (Bool b); v1_2])` by (
    simp[STATE_TYPE_def,ml_repl_stepTheory.PAIR_TYPE_def] >>
    simp[ml_translatorTheory.BOOL_def] ) >>
  imp_res_tac INPUT_TYPE_exists >>
  first_x_assum(qspec_then`ts`strip_assume_tac) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rator_x_assum`COMPILER_RUN_INV`mp_tac >>
  simp[COMPILER_RUN_INV_def] >> strip_tac >>
  simp[LEFT_EXISTS_AND_THM] >>
  reverse conj_tac >- (
    pop_assum SUBST1_TAC >>
    simp[bytecodeTheory.bc_state_component_equality] ) >>
  simp[EXISTS_PROD] >>
  PairCases_on`grd` >>
  qexists_tac`grd0` >> qexists_tac`grd1` >>
  rator_x_assum`env_rs`mp_tac >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls` >>
  simp[update_io_def] >>
  simp[env_rs_def] >> strip_tac >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    qpat_assum`EVERY (sv_every closed) (LUPDATE X Y Z)`mp_tac >>
    simp[EVERY_MEM,MEM_LUPDATE,PULL_EXISTS] >>
    strip_tac >> gen_tac >> strip_tac >- METIS_TAC[] >>
    BasicProvers.VAR_EQ_TAC >>
    simp[EL_LUPDATE] >>
    reverse IF_CASES_TAC >- (
      first_x_assum(qspec_then`EL j r`match_mp_tac) >>
      simp[EL_LUPDATE] >> METIS_TAC[] ) >>
    simp[] >>
    conj_tac >- ( imp_res_tac INPUT_TYPE_closed >> fs[] ) >>
    assume_tac (CONJUNCT2 repl_env_def) >> rfs[] >>
    fsrw_tac[boolSimps.DNF_ss][] ) >>
  exists_suff_gen_then (mp_tac o RW[GSYM AND_IMP_INTRO]) (INST_TYPE[alpha|->``:num``]to_i1_invariant_change_store) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  disch_then just_exists_suff_tac >- (
    strip_tac >>
    first_x_assum(fn th=> first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rpt(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[modLangProofTheory.to_i1_invariant_def] >>
  rator_x_assum`s_to_i1`mp_tac >>
  simp[modLangProofTheory.s_to_i1_cases] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`v_bv data inp ibc` >>
  `v_bv data w (BlockList (MAP BlockSym ts))` by (
    fs[INPUT_TYPE_def,ml_repl_stepTheory.OPTION_TYPE_def,ml_repl_stepTheory.PAIR_TYPE_def,Abbr`data`] >>
    MATCH_MP_TAC (MP_CANON LIST_TYPE_v_bv) >>
    HINT_EXISTS_TAC >> simp[] >> rw[] >>
    match_mp_tac(MP_CANON (GEN_ALL LEXER_FUN_SYMBOL_TYPE_v_bv)) >>
    simp[] >>
    rpt conj_tac >>
    qmatch_abbrev_tac`FLOOKUP gtagenv (n,a) = SOME z` >>
    first_x_assum(qspec_then`n`mp_tac) >>
    disch_then(qspec_then`a`mp_tac o CONV_RULE(SWAP_FORALL_CONV)) >>
    simp[Abbr`n`,sym_tags_exist] >>
    rw[Abbr`z`] >>
    rw[errors_tag_def,others_tag_def,longs_tag_def,numbers_tag_def,strings_tag_def]) >>
  qunabbrev_tac`data` >>
  pop_assum(strip_assume_tac o SIMP_RULE (srw_ss()) [printingTheory.v_bv_def]) >>
  CONV_TAC SWAP_EXISTS_CONV >>
  Q.PAT_ABBREV_TAC`inp2 = Conv X [Conv Y [w; Z]]` >>
  qmatch_assum_abbrev_tac`v_bv data inp ibc` >>
  `v_bv data inp2 inp_bc_val` by (
    simp(Abbr`inp2`::Abbr`data`::conv_rws) >>
    simp[Abbr`inp_bc_val`,BlockSome_def] >>
    simp[PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    fs[printingTheory.exh_Cv_def] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp conv_rws >> simp[PULL_EXISTS] >>
    simp[BlockBool_def]) >>
  qunabbrev_tac`data` >>
  pop_assum(strip_assume_tac o SIMP_RULE (srw_ss()) [printingTheory.v_bv_def]) >>
  qmatch_assum_rename_tac`v_to_i1 grd0 inp2 v12`[] >>
  qexists_tac`LUPDATE (Refv v12) iloc s1` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[Abbr`inp2`] >>
    assume_tac(CONJUNCT2 repl_env_def) >> rfs[] >>
    rw[] >>
    simp[modLangProofTheory.sv_to_i1_cases]) >>
  exists_suff_gen_then(mp_tac o RW[GSYM AND_IMP_INTRO]) (INST_TYPE[beta|->``:num``]to_i2_invariant_change_store) >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >> (CONV_TAC (RESORT_EXISTS_CONV List.rev)) >>
  qexists_tac`genv2` >>
  pop_assum just_exists_suff_tac >- (
    strip_tac >>
    first_x_assum(fn th=> first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rpt(first_assum(match_exists_tac o concl) >> simp[])) >>
  fs[conLangProofTheory.to_i2_invariant_def] >>
  rator_x_assum`s_to_i2`mp_tac >>
  simp[conLangProofTheory.s_to_i2_cases] >>
  strip_tac >>
  qmatch_assum_rename_tac`v_to_i2 grd1 v12 v22`[] >>
  qexists_tac`LUPDATE (Refv v22) iloc s2` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >>
    rw[] >> rw[conLangProofTheory.sv_to_i2_cases]) >>
  simp[miscTheory.LIST_REL_O,PULL_EXISTS,evalPropsTheory.sv_rel_O] >>
  qmatch_assum_rename_tac`v_to_exh Z v22 v23`["Z"] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  fs[miscTheory.LIST_REL_O,evalPropsTheory.sv_rel_O] >>
  qexists_tac`LUPDATE (Refv v23) iloc l3` >>
  simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >> rw[]) >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  qmatch_assum_rename_tac`exh_Cv v23 v24`[] >>
  qexists_tac`LUPDATE (Refv v24) iloc Cs` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fs[LIST_REL_EL_EQN,EL_LUPDATE] >>
    gen_tac >> strip_tac >> rw[]) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  conj_tac >- (
    rator_x_assum`closed_vlabs`mp_tac >>
    simp[intLangExtraTheory.closed_vlabs_def,
         intLangExtraTheory.all_vlabs_csg_def] >>
    simp[EVERY_MEM,intLangExtraTheory.vlabs_csg_def] >>
    strip_tac >>
    `vlabs v24 = {} ∧ all_vlabs v24` by (
      MATCH_MP_TAC (MP_CANON (GEN_ALL no_closures_vlabs)) >>
      fs[printingTheory.exh_Cv_def] >>
      rw[Once CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      METIS_TAC[EqualityType_thm,EqualityType_INPUT_TYPE]) >>
    conj_tac >- (
      fs[intLangExtraTheory.store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER] >>
      METIS_TAC[MEM_LUPDATE_E,evalPropsTheory.dest_Refv_def] ) >>
    fs[intLangExtraTheory.vlabs_list_MAP,PULL_EXISTS] >>
    fs[intLangExtraTheory.store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER] >>
    METIS_TAC[MEM_LUPDATE_E,pred_setTheory.NOT_IN_EMPTY,evalPropsTheory.dest_Refv_def] ) >>
  qexists_tac`grd2` >>
  MATCH_MP_TAC bytecodeProofTheory.Cenv_bs_change_store >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[bytecodeTheory.bc_state_component_equality] >>
  `iloc < LENGTH grd2.sm ∧ EL iloc grd2.sm = iptr` by simp[] >>
  `MEM iptr grd2.sm` by METIS_TAC[MEM_EL] >>
  reverse conj_tac >- rw[] >>
  fs[bytecodeProofTheory.Cenv_bs_def,bytecodeProofTheory.s_refs_def,bytecodeProofTheory.good_rd_def] >>
  conj_tac >- (
    fs[miscTheory.FEVERY_ALL_FLOOKUP] >> rw[] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[UNCURRY] >> strip_tac >>
    simp[finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[] >> fs[] ) >>
  conj_tac >- fs[EVERY_MEM] >>
  fs[LIST_REL_EL_EQN,EL_MAP,EL_LUPDATE] >>
  simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
  rw[] >> fs[] >- METIS_TAC[EL_ALL_DISTINCT_EL_EQ] >>
  METIS_TAC[EL_MAP])

val _ = export_theory()
