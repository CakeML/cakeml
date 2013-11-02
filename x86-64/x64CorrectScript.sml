open HolKernel boolLib bossLib helperLib pairTheory lcsymtacs
open ml_translatorTheory sideTheory replDecsTheory replDecsProofsTheory compileCallReplStepDecTheory

val _ = new_theory "x64Correct"

infix \\ val op \\ = op THEN;

val _ = Globals.max_print_depth := 20

(* --- repl_step --- *)

val DeclAssumExists_ml_repl_step_decls = prove(
  ``DeclAssumExists ml_repl_step_decls``,
  MP_TAC ml_repl_stepTheory.ml_repl_step_translator_state_thm
  \\ REWRITE_TAC [markerTheory.Abbrev_def,TAG_def,AND_IMP_INTRO]
  \\ STRIP_TAC
  \\ Q.PAT_ASSUM `pp ==> DeclAssumExists xxx` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [PRECONDITION_def]
  \\ STRIP_TAC THEN1
   (MP_TAC sideTheory.repl_step_side_thm
    \\ FULL_SIMP_TAC std_ss [ml_repl_stepTheory.repl_step_side_def])
  \\ cheat (* EqualityType (GRAMMAR_PARSETREE_TYPE ...) *) )

val SNOC3 = prove(
   ``xs ++ [x3;x2;x1] = SNOC x1 (SNOC x2 (SNOC x3 xs))``,
  SRW_TAC [] []);

val DeclAssumExists_repl_decs = prove(
  ``DeclAssumExists repl_decs``,
  SIMP_TAC std_ss [replDecsTheory.repl_decs_def,SNOC3]
  \\ MATCH_MP_TAC DeclAssumExists_SNOC_Dlet_Fun
  \\ MATCH_MP_TAC (MP_CANON DeclAssumExists_SNOC_Dlet_ALT)
  \\ SIMP_TAC std_ss [Eval_def]
  \\ SIMP_TAC (srw_ss()) [Once AltBigStepTheory.evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [Once AltBigStepTheory.evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [SemanticPrimitivesTheory.do_uapp_def,LET_DEF,
                          SemanticPrimitivesTheory.store_alloc_def]
  \\ MATCH_MP_TAC (MP_CANON DeclAssumExists_SNOC_Dlet_ALT)
  \\ SIMP_TAC std_ss [Eval_def]
  \\ SIMP_TAC (srw_ss()) [Once AltBigStepTheory.evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [Once AltBigStepTheory.evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [SemanticPrimitivesTheory.do_uapp_def,LET_DEF,
                          SemanticPrimitivesTheory.store_alloc_def]
  \\ SIMP_TAC (srw_ss()) [Once AltBigStepTheory.evaluate'_cases]
  \\ SIMP_TAC std_ss [DeclAssumExists_ml_repl_step_decls]);

val check_ctors_decs_ml_repl_step_decls = prove(
  ``check_ctors_decs NONE init_envC ml_repl_step_decls``,
  MP_TAC ml_repl_stepTheory.ml_repl_step_translator_state_thm
  \\ REWRITE_TAC [markerTheory.Abbrev_def,TAG_def,AND_IMP_INTRO]
  \\ STRIP_TAC);

val decs_to_cenv_ml_repl_step_decls = let
  val pat = ``decs_to_cenv NONE ml_repl_step_decls = xxx``
  in ml_repl_stepTheory.ml_repl_step_translator_state_thm
     |> RW [markerTheory.Abbrev_def,TAG_def]
     |> CONJUNCTS
     |> filter (fn th => can (match_term pat) (concl th)) |> hd end

val check_ctors_decs_repl_decs = prove(
  ``check_ctors_decs NONE init_envC repl_decs``,
  SIMP_TAC std_ss [replDecsTheory.repl_decs_def,SNOC3]
  \\ MATCH_MP_TAC (MP_CANON IMP_check_ctors_decs_SNOC)
  \\ REVERSE STRIP_TAC THEN1 EVAL_TAC
  \\ MATCH_MP_TAC (MP_CANON IMP_check_ctors_decs_SNOC)
  \\ REVERSE STRIP_TAC THEN1 EVAL_TAC
  \\ MATCH_MP_TAC (MP_CANON IMP_check_ctors_decs_SNOC)
  \\ SIMP_TAC std_ss [check_ctors_decs_ml_repl_step_decls]
  \\ EVAL_TAC
  \\ REWRITE_TAC [decs_to_cenv_ml_repl_step_decls]
  \\ EVAL_TAC);

val repl_decs_lemma = prove(
  ``(FV_decs repl_decs = ∅) ∧
    (decs_cns NONE repl_decs = ∅) ∧
    (∀i tds.
        i < LENGTH repl_decs ∧
        (EL i repl_decs = Dtype tds) ⇒
        check_dup_ctors NONE
          (decs_to_cenv NONE (TAKE i repl_decs) ++ init_envC)
          tds) ∧
    (∀i cn ts.
        i < LENGTH repl_decs ∧
        (EL i repl_decs = Dexn cn ts) ⇒
        mk_id NONE cn ∉
        set
          (MAP FST
             (decs_to_cenv NONE (TAKE i repl_decs) ++
              init_envC)))``,
  cheat (* translator should do this? *));

val evaluate_decs_repl_decs = let
  val th = DeclAssumC_thm
           |> RW [GSYM AND_IMP_INTRO]
  val th = MATCH_MP th check_ctors_decs_repl_decs
  val th = prove(``?cenv env. DeclAssumC repl_decs cenv env``,
                 METIS_TAC [DeclAssumExists_repl_decs,th,DeclAssumExists_def])
           |> RW [DeclAssumC_def,DeclsC_def]
  in th end

val repl_decs_cenv_env_s_def = new_specification("repl_decs_cenv_env_s_def",
  ["repl_decs_cenv","repl_decs_env","repl_decs_s"],
  evaluate_decs_repl_decs)

val compile_term_def = Define `
  compile_term = (compile_decs NONE FEMPTY init_compiler_state.contab
          <|bvars := []; mvars := FEMPTY;
            cnmap := cmap init_compiler_state.contab|> [] 0
          <|out := []; next_label := init_compiler_state.rnext_label|>
          repl_decs)`;

val new_compiler_state_def = Define `
  new_compiler_state =
    (init_compiler_state with
            <|contab := FST compile_term;
              renv :=
                ZIP
                  ((FST (SND compile_term)).bvars,
                   REVERSE (GENLIST I (FST (SND (SND compile_term)))));
              rsz := FST (SND (SND compile_term));
              rnext_label :=
                (SND (SND (SND compile_term))).next_label|>)`;

val compile_decs_bc_eval = let
  val th = replDecsProofsTheory.compile_repl_decs_thm |> GEN_ALL
           |> Q.SPEC `repl_decs`
           |> RW [repl_decs_lemma]
  val th = MATCH_MP th (repl_decs_cenv_env_s_def |> RW [EVAL ``empty_store``])
  in th |> SIMP_RULE std_ss [LET_DEF,GSYM compile_term_def]
        |> CONV_RULE (DEPTH_CONV (PairRules.PBETA_CONV))
        |> SIMP_RULE (srw_ss()) [GSYM new_compiler_state_def] end

val compile_term_out_EQ_bootstrap_lcode = prove(
  ``REVERSE (SND (SND (SND compile_term))).out = REVERSE bootstrap_lcode``,
  SIMP_TAC std_ss [compile_term_def]
  \\ REWRITE_TAC [compileReplDecsTheory.repl_decs_compiled,
       repl_computeTheory.compile_decs_FOLDL,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ REWRITE_TAC [SND,FST,``<|out := code; next_label := n |>.out``
                          |> SIMP_CONV (srw_ss()) []]
  \\ REWRITE_TAC [compileCallReplStepDecTheory.bootstrap_lcode_def]);

val code_labels_ok_rev_bootstrap_lcode = let
  val lemma1 =
    ``<|out := code; next_label := n |>.out``
    |> SIMP_CONV (srw_ss()) []
  val lemma2 =
    ``<|bvars := names; mvars := FEMPTY; cnmap := internal37|>.bvars``
    |> SIMP_CONV (srw_ss()) []
  val lemma3 = prove(
    ``(?x. (y = x) /\ P x) ==> P y``,
    SIMP_TAC std_ss []);
  val (i,[]) = match_term ``compile_decs mn menv ct m env rsz cs decs`` (rhs(concl compile_term_def))
  val th =
    compilerProofsTheory.compile_decs_append_out
    |> SPEC_ALL |> INST i |> SIMP_RULE (srw_ss()) [LET_DEF,repl_decs_lemma]
    |> RW [compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL,LET_DEF]
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
    |> RW [lemma1,lemma2,GSYM miscTheory.SWAP_REVERSE_SYM]
    |> HO_MATCH_MP lemma3 |> CONJUNCTS |> el 2
    |> CONV_RULE ((RAND_CONV o RAND_CONV o REWR_CONV) (GSYM compileCallReplStepDecTheory.bootstrap_lcode_def))
  in th end

val code_labels_bootstrap_lcode =
  PROVE_HYP code_labels_ok_rev_bootstrap_lcode
  compileCallReplStepDecTheory.code_labels_rev_bootstrap_lcode

val next_addr_code_labels = prove(
  ``length_ok l ==>
    (next_addr l (code_labels l code) = next_addr l code)``,
  FULL_SIMP_TAC std_ss [bytecodeLabelsTheory.code_labels_def]
  \\ Q.SPEC_TAC (`all_labels l code`,`labs`)
  \\ Induct_on `code` THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC \\ Cases_on `h` \\ TRY (Cases_on `l'`)
  \\ FULL_SIMP_TAC (srw_ss()) [bytecodeLabelsTheory.inst_labels_def,
       bytecodeLabelsTheory.length_ok_def]);

val new_compiler_state_renv =
  SIMP_CONV (srw_ss()) [new_compiler_state_def] ``new_compiler_state.renv``
  |> RW [compile_term_def,compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL,LET_THM]
  |> CONV_RULE (DEPTH_CONV (PairRules.PBETA_CONV))
  |> RW [SND]
  |> RW [SIMP_CONV (srw_ss()) [] ``<|bvars := X; mvars := Y; cnmap := Z|>.bvars``]

val length_new_compiler_state_renv =
  EVAL (listSyntax.mk_length(
          new_compiler_state_renv |> concl |> rhs |> rand |> rator |> rand))

val new_compiler_state_rsz =
  SIMP_CONV (srw_ss()) [new_compiler_state_def] ``new_compiler_state.rsz``
  |> RW [compile_term_def,compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL,LET_THM]
  |> CONV_RULE (DEPTH_CONV (PairRules.PBETA_CONV))
  |> RW [SND]

val repl_decs_env_vs =
  MATCH_MP semanticsExtraTheory.evaluate_decs_new_decs_vs repl_decs_cenv_env_s_def
  |> SIMP_RULE (srw_ss())[]
  |> SIMP_RULE (srw_ss())[repl_decs_def,AstTheory.pat_bindings_def]

val MEM_call_repl_step = prove(
  ``MEM "call_repl_step" (MAP FST repl_decs_env)``,
  simp[repl_decs_env_vs])

(* TODO: move *)
val evaluate_decs_append = store_thm("evaluate_decs_append",
  ``∀decs mn menv cenv s env res. evaluate_decs mn menv cenv s env decs res ⇒
      ∀d1 d2 s0 e0 r0. (decs = d1 ++ d2) ∧ evaluate_decs mn menv cenv s env d1 (s0,e0,Rval r0) ⇒
                       ∃s1 e1 r1. evaluate_decs mn menv (merge e0 cenv) s0 (merge r0 env) d2 (s1,e1,r1) ∧
                            (res = (s1, merge e1 e0, combine_dec_result r0 r1))``,
  Induct >- (
    simp[Once BigStepTheory.evaluate_decs_cases] >>
    simp[Once BigStepTheory.evaluate_decs_cases] >>
    simp[Once BigStepTheory.evaluate_decs_cases] >>
    simp[LibTheory.emp_def,LibTheory.merge_def,SemanticPrimitivesTheory.combine_dec_result_def]) >>
  simp[Once BigStepTheory.evaluate_decs_cases] >>
  rw[] >- (
    Cases_on`d1`>>fs[] >- (
      pop_assum mp_tac >>
      simp[Once BigStepTheory.evaluate_decs_cases] >>
      rw[] >>
      simp_tac(srw_ss())[Once BigStepTheory.evaluate_decs_cases] >>
      simp[LibTheory.emp_def,LibTheory.merge_def] >>
      simp[SemanticPrimitivesTheory.combine_dec_result_def] >>
      qexists_tac`Rerr e`>>simp[] ) >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[Once BigStepTheory.evaluate_decs_cases] >>
    rw[] >>
    imp_res_tac determTheory.dec_determ >>
    fs[] ) >>
  Cases_on`d1`>>fs[] >- (
    pop_assum mp_tac >>
    simp[Once BigStepTheory.evaluate_decs_cases] >>
    rw[] >>
    simp_tac(srw_ss())[Once BigStepTheory.evaluate_decs_cases] >>
    simp[LibTheory.emp_def,LibTheory.merge_def] >>
    fs[LibTheory.merge_def] >>
    qexists_tac`combine_dec_result new_env r` >>
    conj_tac >- METIS_TAC[] >>
    simp[SemanticPrimitivesTheory.combine_dec_result_def] >>
    Cases_on`r`>>simp[LibTheory.merge_def]) >>
  pop_assum mp_tac >>
  simp_tac(srw_ss())[Once BigStepTheory.evaluate_decs_cases] >>
  rw[] >>
  fs[LibTheory.merge_def] >>
  imp_res_tac determTheory.dec_determ >>
  fs[] >> rw[] >>
  first_x_assum(qspecl_then[`mn`,`menv`,`new_tds ++ cenv`,`s2`,`new_env ++ env`,`s3,new_tds',r`]mp_tac) >>
  rw[] >>
  Cases_on`r'`>>fs[SemanticPrimitivesTheory.combine_dec_result_def] >>
  first_x_assum(qspecl_then[`t`,`d2`,`s0`,`new_tds''`,`a`]mp_tac) >>
  rw[] >>
  fs[LibTheory.merge_def] >>
  qexists_tac`r1` >> simp[] >>
  Cases_on`r1`>>fs[])

val evaluate_decs_decs_to_cenv = store_thm("evaluate_decs_decs_to_cenv",
  ``∀mn menv cenv s env decs res.
     evaluate_decs mn menv cenv s env decs res ⇒
     ∀v. (SND(SND res ) = Rval v) ⇒
     (decs_to_cenv mn decs = (FST(SND res)))``,
   HO_MATCH_MP_TAC BigStepTheory.evaluate_decs_ind >>
   simp[LibTheory.emp_def] >> rw[] >- simp[SemanticPrimitivesTheory.decs_to_cenv_def] >>
   imp_res_tac compilerProofsTheory.evaluate_dec_dec_to_cenv >>
   fs[] >> simp[SemanticPrimitivesTheory.decs_to_cenv_def,LibTheory.merge_def] >>
   Cases_on`r`>>fs[SemanticPrimitivesTheory.combine_dec_result_def])

val evaluate_decs_ml_repl_decs = let
  val th = DeclAssumC_thm
           |> RW [GSYM AND_IMP_INTRO]
  val th = MATCH_MP th check_ctors_decs_ml_repl_step_decls
  val th = prove(``?cenv env. DeclAssumC ml_repl_step_decls cenv env``,
                 METIS_TAC [DeclAssumExists_ml_repl_step_decls,th,DeclAssumExists_def])
           |> RW [DeclAssumC_def,DeclsC_def]
  in th end

val ml_repl_decs_cenv_env_s_def = new_specification("ml_repl_decs_cenv_env_s_def",
  ["ml_repl_decs_cenv","ml_repl_decs_env","ml_repl_decs_s"],
  evaluate_decs_ml_repl_decs)

val merge_emp = prove(
  ``merge x emp = x``,
    simp[LibTheory.emp_def,LibTheory.merge_def])

val ml_repl_decs_cenv =
  MATCH_MP evaluate_decs_decs_to_cenv ml_repl_decs_cenv_env_s_def
  |> SIMP_RULE (srw_ss())[]
  |> SYM

val do_con_check_ml_repl_decs_None =
  EVAL ``do_con_check (merge ml_repl_decs_cenv xx) (SOME(Short"None")) 0``
  |> RIGHT_CONV_RULE(REWRITE_CONV[ml_repl_decs_cenv])
  |> RIGHT_CONV_RULE(REWRITE_CONV[ml_repl_stepTheory.ml_repl_step_decls,SemanticPrimitivesTheory.decs_to_cenv_def])
  |> RIGHT_CONV_RULE EVAL
  |> EQT_ELIM

val bind_emp = EVAL``bind x y emp``

val repl_decs_env_front = let
  val ss = SIMP_RULE (srw_ss())
  val th =
    repl_decs_cenv_env_s_def
    |> RW[repl_decs_def]
    |> MATCH_MP evaluate_decs_append
    |> Q.SPEC`ml_repl_step_decls`
    |> SIMP_RULE (srw_ss())[]
    |> C MATCH_MP ml_repl_decs_cenv_env_s_def
  val th =
    th |> ss [Once BigStepTheory.evaluate_decs_cases]
    |> ss [Once BigStepTheory.evaluate_dec_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [terminationTheory.pmatch_def,AstTheory.pat_bindings_def]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once SemanticPrimitivesTheory.do_uapp_def,LET_THM,SemanticPrimitivesTheory.store_alloc_def]
  val th =
    th |> ss [do_con_check_ml_repl_decs_None]
    |> ss [Once BigStepTheory.evaluate_decs_cases]
    |> ss [Once BigStepTheory.evaluate_dec_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [terminationTheory.pmatch_def,AstTheory.pat_bindings_def]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once SemanticPrimitivesTheory.do_uapp_def,LET_THM,SemanticPrimitivesTheory.store_alloc_def]
  val th =
    th |> ss [merge_emp,do_con_check_ml_repl_decs_None,bind_emp]
    |> ss [Once BigStepTheory.evaluate_dec_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [terminationTheory.pmatch_def,AstTheory.pat_bindings_def]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [Once SemanticPrimitivesTheory.do_uapp_def,LET_THM,SemanticPrimitivesTheory.store_alloc_def]
  val th =
    th |> ss [Once BigStepTheory.evaluate_dec_cases]
    |> ss [Once BigStepTheory.evaluate_cases]
    |> ss [terminationTheory.pmatch_def,AstTheory.pat_bindings_def]
    |> ss [Once SemanticPrimitivesTheory.do_uapp_def,LET_THM,SemanticPrimitivesTheory.store_alloc_def]
    |> ss [Once BigStepTheory.evaluate_decs_cases]
    |> ss [Once BigStepTheory.evaluate_dec_cases]
    |> ss [terminationTheory.pmatch_def,AstTheory.pat_bindings_def]
  val th =
    th |> ss [Once BigStepTheory.evaluate_dec_cases]
    |> ss [terminationTheory.pmatch_def,AstTheory.pat_bindings_def]
    |> ss [Once BigStepTheory.evaluate_decs_cases]
    |> ss [SemanticPrimitivesTheory.combine_dec_result_def,LibTheory.merge_def,LibTheory.emp_def,LibTheory.bind_def]
  in th end

val env_rs_repl_decs_inp_out = prove(
  ``env_rs [] (cenv ++ init_envC) (0,s)
      repl_decs_env new_compiler_state 0 rd bs' ==>
    ∃cl pout pinp wout winp out inp st.
      (bs'.stack = cl::RefPtr pout::RefPtr pinp::st) ∧
      (FLOOKUP bs'.refs pout = SOME out) ∧
      (FLOOKUP bs'.refs pinp = SOME inp) ∧
      let mv = MAP FST o_f new_compiler_state.rmenv in
      let m = cmap new_compiler_state.contab in
      let pp = mk_pp rd bs' in
      let vout = v_to_Cv mv m (EL (LENGTH ml_repl_decs_s +1) s) in
      let vinp = v_to_Cv mv m (EL (LENGTH ml_repl_decs_s +0) s) in
      syneq vout wout ∧ syneq vinp winp ∧
      Cv_bv pp wout out ∧ Cv_bv pp winp inp``,
  simp[compilerProofsTheory.env_rs_def,LET_THM] >> strip_tac >>
  fs[toBytecodeProofsTheory.Cenv_bs_def] >>
  fs[toBytecodeProofsTheory.env_renv_def] >>
  qpat_assum`EVERY2 P X Y`mp_tac >>
  qpat_assum`EVERY2 P X Cs`mp_tac >>
  simp_tac bool_ss [miscTheory.EVERY2_MAP] >>
  simp[CompilerLibTheory.el_check_def] >>
  `∃x y z w. new_compiler_state.renv = x::y::z::w` by (
    REWRITE_TAC[new_compiler_state_renv] >>
    EVAL_TAC >> SRW_TAC[][] ) >>
  ntac 2 strip_tac >>
  `∃Cx Cy Cz Cw. Cenv = Cx::Cy::Cz::Cw` by (
    fs[listTheory.EVERY2_EVERY] >> rfs[] >>
    Cases_on`Cenv`>>fs[]>>
    Cases_on`t`>>fs[]>>
    Cases_on`t'`>>fs[]) >>
  BasicProvers.VAR_EQ_TAC >>
  pop_assum mp_tac >>
  simp[] >>
  Cases_on`SND x < LENGTH bs'.stack` >> simp[] >>
  Cases_on`SND y < LENGTH bs'.stack` >> simp[] >>
  Cases_on`SND z < LENGTH bs'.stack` >> simp[] >>
  simp[listTheory.EL_REVERSE] >>
  qpat_assum`X = LENGTH bs'.stack`(ASSUME_TAC o SYM) >>
  simp[arithmeticTheory.PRE_SUB1,new_compiler_state_rsz] >>
  qpat_assum`new_compiler_state.renv = X`mp_tac >>
  REWRITE_TAC[new_compiler_state_renv] >>
  CONV_TAC (RATOR_CONV EVAL) >>
  strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rpt strip_tac >>
  rpt (qpat_assum `Cv_bv X Y Z`mp_tac) >>
  simp[] >> rpt strip_tac >>
  rpt (qpat_assum`X < LENGTH Y`mp_tac) >>
  qpat_assum`LENGTH bs'.stack = X`(ASSUME_TAC o SYM) >>
  Cases_on`bs'.stack`>>simp[] >>
  Cases_on`t`>>simp[] >>
  Cases_on`t'`>>simp[] >>
  strip_tac >>
  rpt (qpat_assum `Cv_bv X Y Z`mp_tac) >>
  simp[] >>
  qpat_assum`EVERY2 syneq X Y`mp_tac >>
  simp[pmatchTheory.env_to_Cenv_MAP] >>
  simp[repl_decs_env_front] >>
  simp[GSYM AND_IMP_INTRO] >> strip_tac >>
  simp[compilerTerminationTheory.v_to_Cv_def] >>
  ntac 2 strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ntac 2 strip_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  disch_then(qx_choose_then`pout`STRIP_ASSUME_TAC) >>
  disch_then(qx_choose_then`pinp`STRIP_ASSUME_TAC) >>
  Q.LIST_EXISTS_TAC[`pout`,`pinp`] >> simp[] >>
  qpat_assum`s_refs X Y Z`mp_tac >>
  simp[toBytecodeProofsTheory.s_refs_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ntac 2 (pop_assum mp_tac) >>
  simp[CompilerLibTheory.el_check_def] >>
  qpat_assum`LIST_REL P Cw X`kall_tac >>
  qpat_assum`syneq X Cx`kall_tac >>
  qpat_assum`LIST_REL P X Cw`kall_tac >>
  qpat_assum`Cv_bv X Cx Y`kall_tac >>
  rpt strip_tac >>
  simp[finite_mapTheory.FLOOKUP_DEF] >>
  fs[listTheory.EVERY_MEM] >>
  simp[Once CONJ_ASSOC] >>
  `LENGTH ml_repl_decs_s < LENGTH Cs` by simp[] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    conj_tac >>
    first_x_assum MATCH_MP_TAC >>
    simp[listTheory.MEM_EL] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    PROVE_TAC[] ) >>
  fs[listTheory.EVERY2_EVERY,listTheory.EVERY_MEM,pairTheory.FORALL_PROD] >>
  qexists_tac`EL(LENGTH ml_repl_decs_s+1)Cs` >>
  conj_tac >- (
    first_x_assum MATCH_MP_TAC >>
    simp[listTheory.MEM_ZIP] >>
    PROVE_TAC[] ) >>
  qexists_tac`EL(LENGTH ml_repl_decs_s+0)Cs` >>
  conj_tac >- (
    first_x_assum MATCH_MP_TAC >>
    simp[listTheory.MEM_ZIP] >>
    PROVE_TAC[] ) >>
  conj_tac >> FIRST_X_ASSUM MATCH_MP_TAC >>
  simp[listTheory.MEM_ZIP] >|[
    qexists_tac`LENGTH ml_repl_decs_s+1`,
    qexists_tac`LENGTH ml_repl_decs_s+0`] >>
  simp[listTheory.EL_MAP])

val bc_eval_bootstrap_lcode = prove(
  ``∀bs.
       (bs.code = REVERSE bootstrap_lcode) ∧ length_ok bs.inst_length /\
       (bs.pc = 0) ∧ (bs.stack = []) ∧ (bs.clock = NONE) ⇒
       ∃bs' rd.
         (bc_eval (strip_labels bs) = SOME (strip_labels bs')) ∧
         (bs'.pc = next_addr bs.inst_length (strip_labels bs).code) ∧
         env_rs [] (repl_decs_cenv ++ init_envC) (0,repl_decs_s)
           repl_decs_env new_compiler_state 0 rd bs' /\
         MEM "call_repl_step" (MAP FST repl_decs_env)``,
  STRIP_ASSUME_TAC compile_decs_bc_eval
  \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `bs`)
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC set_sepTheory.IMP_IMP
  \\ SIMP_TAC std_ss [compile_term_out_EQ_bootstrap_lcode]
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `bs'`
  \\ Q.EXISTS_TAC `rd` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (MATCH_MP_TAC (MP_CANON bytecodeEvalTheory.RTC_bc_next_bc_eval)
    \\ IMP_RES_TAC bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next
    \\ IMP_RES_TAC bytecodeLabelsTheory.bc_next_strip_labels_RTC
    \\ FULL_SIMP_TAC std_ss []
    \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC bytecodeLabelsTheory.bc_next_strip_IMP
    \\ REVERSE (`length_ok bs'.inst_length` by ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [] THEN1 METIS_TAC []
    \\ IMP_RES_TAC bytecodeExtraTheory.RTC_bc_next_preserves
    \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC (srw_ss()) [bytecodeLabelsTheory.strip_labels_def]
  \\ FULL_SIMP_TAC std_ss [next_addr_code_labels]
  \\ simp[MEM_call_repl_step]);

val compile_call_term_def = Define `
  compile_call_term = compile_dec FEMPTY (FST (SND compile_repl_decs))
     (FST (SND (SND compile_repl_decs)))
     (FST (SND (SND (SND compile_repl_decs))))
     <|out := [];
       next_label :=
         (SND (SND (SND (SND compile_repl_decs)))).next_label|>
     call_repl_step_dec`;

val compile_call_term_thm =
  call_repl_step_dec_compiled
  |> SIMP_RULE std_ss [GSYM compileCallReplStepDecTheory.call_lcode_def,
       LET_DEF,GSYM compile_call_term_def]

(*

  val th =
    compile_call_repl_step_thm |> GEN_ALL
      |> Q.SPEC `call_repl_step_dec` |> Q.SPEC `NONE`
      |> RW [EVAL ``dec_cns call_repl_step_dec``, (SIMP_RULE(srw_ss())[](EVAL ``FV_dec call_repl_step_dec``))]
      |> Q.SPECL [`repl_decs_cenv`,`[out;inp]`,`repl_decs_env`,`[out';inp']`]
      |> SIMP_RULE std_ss[MEM_call_repl_step]
      (* get rid of all the hypotheses, and expand out the evaluate_dec as far as possible *)

compile_call_term_def

  print_find "repl_decs_compiled"

we need:

|- FV_dec call_repl_step_dec = {}



*)




(*

val entire_x64_implementation_def = Define `
  entire_x64_implementation p =
    {(p:word64,[0x88w:word8])} UNION bignum_code (p + 999w)`;

val out_def = Define `
  (out (Diverge) = ("",F)) /\
  (out (Terminate) = ("",T)) /\
  (out (Result r rest) =
     let (str,res) = out rest in
       (r ++ str,res))`;



val x64_correct = store_thm("x64_correct",
  ``TEMPORAL X64_MODEL (entire_x64_implementation p)
      (T_IMPLIES (INIT_STATE init)
                 (T_DISJ (EVENTUALLY (SEP_EXISTS output result bools. zHEAP_OUTPUT (first_cs init,output) *
                                         cond (repl bools init.init_input result /\ (out result = (output,T)))))
                 (T_DISJ (ALWAYS (EVENTUALLY (SEP_EXISTS output result bools. zHEAP_OK output *
                                         cond (repl bools init.init_input result /\ (out result = (output,F))))))
                         (EVENTUALLY (SEP_EXISTS output rest result bools success. zHEAP_ERROR output *
                                         cond (repl bools init.init_input result /\ (out result = (output ++ rest,success))))))))``,
  cheat);

*)

val _ = export_theory()
