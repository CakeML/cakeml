open HolKernel boolLib bossLib pairTheory listTheory lcsymtacs miscLib
open ml_translatorTheory replCorrectTheory compilerProofTheory sideTheory

val _ = new_theory "bootstrap_lemmas"

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE

val _ = Globals.max_print_depth := 20

(* REPL module is closed (should be proved elsewhere?) *)
val all_env_dom_init =
  ``all_env_dom ([],init_envC,init_env)``
  |> (SIMP_CONV std_ss [free_varsTheory.all_env_dom_def,libTheory.lookup_def] THENC
      SIMP_CONV (srw_ss()) [pred_setTheory.EXTENSION] THENC
      EVAL)

(*
val FV_decs_side_decls =
  ``FV_decs side_decls``
  |> (RAND_CONV(REWR_CONV sideTheory.side_decls) THENC
      computeLib.CBV_CONV(cakeml_computeLib.cakeml_compset()))
*)
val FV_decs_side_decls = prove(``FV_decs side_decls = {}``,cheat)

val closed_top_REPL = prove(
  ``closed_top ([],init_envC,init_env) (Tmod "REPL" NONE side_decls)``,
  simp[free_varsTheory.closed_top_def,all_env_dom_init,FV_decs_side_decls])

(* lemmas about the semantics of a module where we know the last few declarations *)
open bigStepTheory terminationTheory

val evaluate_store_acc = store_thm("evaluate_store_acc",
  ``(∀ck env s e res. evaluate ck env s e res ⇒ SND s ≼ SND(FST res)) ∧
    (∀ck env s e res. evaluate_list ck env s e res ⇒ SND s ≼ SND (FST res)) ∧
    (∀ck env s e f g res. evaluate_match ck env s e f g res ⇒ SND s ≼ SND (FST res))``,
  ho_match_mp_tac evaluate_ind >> rw[] >>
  cheat)
  (*TRY(metis_tac[rich_listTheory.IS_PREFIX_TRANS])*)

val evaluate_dec_store_acc = store_thm("evaluate_dec_store_acc",
  ``∀ck mn env s d res. evaluate_dec ck mn env s d res ⇒
      SND(FST s) ≼ SND(FST(FST res))``,
  ho_match_mp_tac evaluate_dec_ind >> rw[]>>
  imp_res_tac evaluate_store_acc >> fs[])

val evaluate_decs_store_acc = store_thm("evaluate_decs_store_acc",
  ``∀ck mn env s decs res. evaluate_decs ck mn env s decs res ⇒
    SND(FST s) ≼ SND(FST(FST res))``,
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  imp_res_tac evaluate_dec_store_acc >> fs[] >>
  METIS_TAC[rich_listTheory.IS_PREFIX_TRANS])

val evaluate_decs_new_decs_vs = store_thm("evaluate_decs_new_decs_vs",
  ``∀ck mn env s decs res. evaluate_decs ck mn env s decs res ⇒
      ∀env. SND(SND res) = Rval env ⇒ MAP FST env = new_decs_vs decs``,
  ho_match_mp_tac evaluate_decs_ind >> simp[] >> rw[libTheory.emp_def] >>
  imp_res_tac free_varsTheory.evaluate_dec_new_dec_vs >> fs[] >>
  Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def]>>
  rw[libTheory.merge_def])

val build_conv_merge = store_thm("build_conv_merge",
  ``build_conv cenv i ls = SOME v ⇒
    build_conv (merge_envC j cenv) i ls = SOME v``,
  rw[semanticPrimitivesTheory.build_conv_def] >>
  BasicProvers.CASE_TAC>>fs[]>>
  PairCases_on`j`>>PairCases_on`cenv`>>fs[semanticPrimitivesTheory.merge_envC_def]

val evaluate_decs_ref = store_thm("evaluate_decs_ref",
  ``∀ck mn env s decs a b c k i s1 x decs0 decs1 v.
      evaluate_decs ck mn env s decs (((k,s1),a),b,Rval c) ∧
      decs = decs0 ++ [Dlet (Pvar x) (Uapp Opref (Con i []))] ++ decs1 ∧
      x ∉ set(new_decs_vs decs1) ∧
      build_conv (all_env_to_cenv env) i [] = SOME v
      ⇒
      ∃n. lookup x c = SOME (Loc n) ∧ n < LENGTH s1 ∧ EL n s1 = v``,
  Induct_on`decs0` >>
  rw[Once bigStepTheory.evaluate_decs_cases] >- (
    fs[Once bigStepTheory.evaluate_dec_cases] >>
    fs[Once bigStepTheory.evaluate_cases] >>
    fs[semanticPrimitivesTheory.do_uapp_def] >>
    fs[semanticPrimitivesTheory.store_alloc_def,LET_THM] >>
    fs[terminationTheory.pmatch_def] >>
    Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def]>>
    imp_res_tac evaluate_decs_new_decs_vs >> fs[] >>
    rw[libTheory.merge_def,libPropsTheory.lookup_append,libTheory.bind_def] >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac evaluate_decs_store_acc >> fs[] >>
      imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >> fs[] >>
      conj_tac >- DECIDE_TAC >>
      fs[Once bigStepTheory.evaluate_cases] >>
      fs[Once bigStepTheory.evaluate_cases] >>
      fs[rich_listTheory.IS_PREFIX_APPEND] >>
      simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1]) >>
    imp_res_tac libPropsTheory.lookup_in2 >> rfs[]) >>
  Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def]>>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  rfs[semanticPrimitivesTheory.all_env_to_cenv_def]
  rw[libTheory.merge_def,libPropsTheory.lookup_append])

val evaluate_Tmod_ref = prove(
  ``evaluate_top ck env0 st (Tmod mn NONE decs) ((cs,u),envC,Rval ([(mn,env)],v)) ⇒
    decs = decs0 ++[Dlet (Pvar x) (Uapp Opref init)] ++decs1 ∧
    x ∉ set(new_decs_vs decs1)
  ⇒
    ∃n. lookup x env = SOME (Loc n) ∧ n < LENGTH (SND cs)``,
  Cases_on`cs`>>rw[bigStepTheory.evaluate_top_cases]>>
  metis_tac[evaluate_decs_ref]) |> GEN_ALL

(* Equality Type assumptions (should be proved elsewhere?) *)
val EqualityType1 = prove(
  ``EqualityType (GRAMMAR_PARSETREE_TYPE TOKENS_TOKEN_TYPE GRAM_MMLNONT_TYPE)``,
  cheat)
val EqualityType2 = prove(
  ``EqualityType AST_T_TYPE``,
  cheat)
val EqualityType3 = prove(
  ``EqualityType AST_PAT_TYPE``,
  cheat)
val EqualityType4 = prove(
  ``EqualityType PATLANG_EXP_PAT_TYPE``,
  cheat)
val EqualityType5 = prove(
  ``EqualityType AST_EXP_TYPE``,
  cheat)
val EqualityTypes = [EqualityType1, EqualityType2, EqualityType3, EqualityType4, EqualityType5]

(* Define things to bootstrap *)

val compile_top_repl_decs_def = zDefine`
  compile_top_repl_decs = compile_top NONE (FST compile_primitives) (Tmod "REPL" NONE side_decls)`

val compile_repl_decs_def = zDefine
  `compile_repl_decs = code_labels real_inst_length (SND(SND(compile_top_repl_decs)))`

val compile_repl_decs_eq = ASSUME``compile_repl_decs = bootstrap_code``

(* Environment produced by repl_decs *)

val evaluate_side_decls = DISCH_ALL module_thm |> SIMP_RULE std_ss []
  |> RW EqualityTypes

val (repl_store,repl_res) =
  CONJUNCT1 evaluate_side_decls
  |> concl |> strip_comb
  |> snd |> last
  |> dest_pair
val (x,y) = dest_pair repl_res
val y = rand y
val (y,z) = dest_pair y
val repl_all_env = ``^y,merge_envC ^x init_envC,init_env``

val side_decls_cs =
  let
    val cs = listSimps.list_compset()
    val _ = computeLib.add_thms[sideTheory.side_decls] cs
    val _ = computeLib.add_thms[rich_listTheory.LASTN_compute] cs
  in
    cs
  end

val last_3_side_decls = computeLib.CBV_CONV side_decls_cs ``LASTN 3 side_decls``

val side_decls_append_3 =
  rich_listTheory.APPEND_BUTLASTN_LASTN |> Q.ISPECL[`3:num`,`side_decls`]
  |> UNDISCH |> SYM |> RW[last_3_side_decls]
  |> prove_hyps_by(CONV_TAC(computeLib.CBV_CONV side_decls_cs))

val side_decls_state_locs = prove(
  ``∃n1 n2.
    lookup "input" (Tmod_env "REPL" side_decls) = SOME (Loc n1) ∧
    lookup "output" (Tmod_env "REPL" side_decls) = SOME (Loc n2) ∧
    n1 < LENGTH (SND (Tmod_state "REPL" side_decls)) ∧
    n2 < LENGTH (SND (Tmod_state "REPL" side_decls))``,
  mp_tac(MATCH_MP evaluate_Tmod_ref (CONJUNCT1 evaluate_side_decls)) >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(REWRITE_CONV[Once side_decls_append_3])))) >>
  Q.PAT_ABBREV_TAC`d3 = Dlet (Pvar "call_repl_step") X` >>
  disch_then((fn th => mp_tac th >> mp_tac th) o CONV_RULE(RESORT_FORALL_CONV(sort_vars["decs1"]))) >>
  disch_then(qspec_then`[d3]`STRIP_ASSUME_TAC) >>
  Q.PAT_ABBREV_TAC`d2 = Dlet (Pvar "output") X` >>
  disch_then(qspec_then`[d2;d3]`STRIP_ASSUME_TAC) >>
  fs[Abbr`d2`,Abbr`d3`,astTheory.pat_bindings_def])

val io_locs_def = new_specification("io_locs_def",["iloc","oloc"],side_decls_state_locs)

(* Compiler's invariant, holds after compiling REPL *)

val update_io_def  = Define`
  update_io inp out ((c,s),x,y) =
    ((c,LUPDATE inp iloc (LUPDATE out oloc s)),x,y)`

val COMPILER_RUN_INV_def = Define `
  COMPILER_RUN_INV bs inp out =
    ?grd.
      env_rs ^repl_all_env (update_io inp out ^repl_store) grd
        (FST compile_top_repl_decs) bs`
(*
      closed_context [] (repl_decs_cenv ++ init_envC)
        (ml_repl_step_decls_s ++ [out; inp]) repl_decs_env /\
      (bs.clock = NONE) /\ (bs.output = "") /\
      (bs.code = REVERSE bootstrap_lcode ++ REVERSE call_lcode ++ [Stack Pop])`;
*)

val COMPILER_RUN_INV_empty_stack = store_thm("COMPILER_RUN_INV_empty_stack",
  ``COMPILER_RUN_INV bs inpu out ⇒ bs.stack = []``,
  rw[COMPILER_RUN_INV_def]>> PairCases_on`grd` >>
  Cases_on`Tmod_state "REPL" side_decls`>>
  fs[update_io_def,compilerProofTheory.env_rs_def])

val COMPILER_RUN_INV_init = store_thm("COMPILER_RUN_INV_init",
  ``∀bootstrap_lcode. (SND(SND(compile_top_repl_decs))) = bootstrap_lcode ⇒
      ∃bs. bc_eval (install_code bootstrap_lcode initial_bc_state) = SOME bs ∧
           COMPILER_RUN_INV bs``,
  rw[] >>
  mp_tac(MATCH_MP bigClockTheory.top_add_clock (CONJUNCT1 evaluate_side_decls)) >>
  simp[] >>
  `∃c r. Tmod_state "REPL" side_decls = (c,r)` by METIS_TAC[pair_CASES] >> simp[] >>
  disch_then(qx_choose_then`ck`(mp_tac o MATCH_MP compile_top_thm)) >>
  simp[] >>
  (initial_invariant |> RW[invariant_def] |> CONJUNCTS |> el 5
   |> SIMP_RULE(srw_ss())[replTheory.init_repl_state_def]
   |> STRIP_ASSUME_TAC) >>
  pop_assum(mp_tac o MATCH_MP (RW[GSYM AND_IMP_INTRO]env_rs_change_clock)) >>
  simp[] >> disch_then(qspecl_then[`ck`,`SOME ck`]mp_tac) >> simp[] >>
  simp[repl_funTheory.initial_repl_fun_state_def] >>
  strip_tac >>
  Q.PAT_ABBREV_TAC`bs = install_code X Y` >>
  CONV_TAC(LAND_CONV(RESORT_FORALL_CONV(sort_vars["bs","rs","types"]))) >>
  disch_then(qspecl_then[`bs with clock := SOME ck`,`FST compile_primitives`,`NONE`]mp_tac) >>
  simp[] >>
  `∃rss rsf bc. compile_top_repl_decs = (rss,rsf,bc)` by METIS_TAC[pair_CASES] >>
  fs[compile_top_repl_decs_def,closed_top_REPL] >>
  disch_then(qspecl_then[`grd`,`initial_bc_state.code`]mp_tac) >>
  discharge_hyps >- (
    conj_tac >- (
      match_mp_tac env_rs_with_bs_irr >>
      simp[Abbr`bs`,repl_funTheory.install_code_def] >>
      first_assum(match_exists_tac o concl) >> simp[] ) >>
    simp[Abbr`bs`,repl_funTheory.install_code_def] ) >>
  strip_tac >>
  imp_res_tac bytecodeClockTheory.RTC_bc_next_can_be_unclocked >>
  imp_res_tac bytecodeEvalTheory.RTC_bc_next_bc_eval >>
  pop_assum kall_tac >>
  pop_assum mp_tac >>
  discharge_hyps >- (
    simp[bytecodeEvalTheory.bc_eval1_thm
        ,bytecodeEvalTheory.bc_eval1_def
        ,bytecodeClockTheory.bc_fetch_with_clock] ) >>
  strip_tac >> fs[] >>
  `bs with clock := NONE = bs` by (
    simp[Abbr`bs`,repl_funTheory.install_code_def,
         bytecodeTheory.bc_state_component_equality] >>
    mp_tac replCorrectTheory.initial_invariant >>
    simp[invariant_def] ) >>
  pop_assum(SUBST1_TAC o SYM) >> simp[] >>
  simp[COMPILER_RUN_INV_def,compile_top_repl_decs_def] >>
  `emp ++ init_env = init_env` by simp[libTheory.emp_def] >>
  METIS_TAC[env_rs_change_clock,SND,FST])

(* Running the code preserves the invariant *)

val COMPILER_RUN_INV_repl_step = store_thm("COMPILER_RUN_INV_repl_step",
  ``COMPILER_RUN_INV bs1 inp1 out1 /\
    INPUT_TYPE x inp1 ==>
    ?bs2 inp2 out2.
      (bc_eval (bs1 with pc := code_start bs1) = SOME bs2) /\
      COMPILER_RUN_INV bs2 inp2 out2 /\ (bs2.pc = code_end bs1) /\
      OUTPUT_TYPE (repl_step x) out2``,
  REPEAT STRIP_TAC
  \\ REVERSE (`?out2.
     evaluate_dec NONE [] (repl_decs_cenv ++ init_envC)
       (ml_repl_step_decls_s ++ [inp1; out1]) repl_decs_env
       call_repl_step_dec
       (ml_repl_step_decls_s ++ [inp1; out2],Rval ([],[])) /\
     OUTPUT_TYPE (repl_step x) out2` by ALL_TAC)
  THEN1 METIS_TAC [COMPILER_RUN_INV_STEP]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_dec_cases,
       call_repl_step_dec_def,libTheory.emp_def,terminationTheory.pmatch_def,
                          astTheory.pat_bindings_def]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once repl_decs_env_def,lookup_var_id_def,do_app_def]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_cases,libTheory.bind_def]
  \\ SIMP_TAC (srw_ss()) [Once repl_decs_env_def,lookup_var_id_def,do_app_def]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_cases,PULL_EXISTS]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_cases,PULL_EXISTS]
  \\ SIMP_TAC (srw_ss()) [Once repl_decs_env_def,lookup_var_id_def]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_cases,PULL_EXISTS]
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_cases,PULL_EXISTS]
  \\ SIMP_TAC (srw_ss()) [Once repl_decs_env_def,lookup_var_id_def,do_uapp_def,
       store_lookup_def,rich_listTheory.EL_LENGTH_APPEND]
  \\ STRIP_ASSUME_TAC repl_step_do_app
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ `!s env'. do_app s env' Opapp res inp1 = SOME (s,env,exp)` by ALL_TAC THEN1
   (Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
    \\ Cases_on `ALOOKUP l0 s` \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
    \\ Cases_on `x'` \\ FULL_SIMP_TAC (srw_ss()) [do_app_def])
  \\ FULL_SIMP_TAC std_ss []
  \\ `!tt. evaluate F [] (repl_decs_cenv ++ init_envC)
       (0,ml_repl_step_decls_s ++ [inp1; out1]) env exp
       tt <=> (tt = ((0,ml_repl_step_decls_s ++ [inp1; out1]),Rval u))` by
       cheat (* requires difficult proof: evaluate' ==> evaluate *)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `store_assign (LENGTH ml_repl_step_decls_s + 1) u
        (ml_repl_step_decls_s ++ [inp1; out1]) =
      SOME (ml_repl_step_decls_s ++ [inp1; u])` by ALL_TAC THEN1
   (SIMP_TAC std_ss [store_assign_def,LENGTH_APPEND,LENGTH]
    \\ `ml_repl_step_decls_s ++ [inp1; out1] =
        (ml_repl_step_decls_s ++ [inp1]) ++ [out1]` by ALL_TAC THEN1
          FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,APPEND,GSYM APPEND_ASSOC]
    \\ `LENGTH ml_repl_step_decls_s + 1 =
        LENGTH (ml_repl_step_decls_s ++ [inp1])` by SRW_TAC [] []
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH]
    \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [Once bigStepTheory.evaluate_dec_cases,
       call_repl_step_dec_def,libTheory.emp_def,terminationTheory.pmatch_def,
                          astTheory.pat_bindings_def]);

(* Changing the references preserves the invariant *)

val COMPILER_RUN_INV_INR = store_thm("COMPILER_RUN_INV_INR",
  ``COMPILER_RUN_INV bs inp outp /\ OUTPUT_TYPE (INR (msg,s)) outp ==>
    ?x outp_ptr inp_ptr rest s_bc_val.
      (bs.stack = x::(RefPtr outp_ptr)::(RefPtr inp_ptr)::rest) /\
      inp_ptr IN FDOM bs.refs /\
      (FLOOKUP bs.refs outp_ptr =
         SOME (BlockInr (BlockPair (BlockList (MAP Chr msg),s_bc_val)))) /\
      !ts.
        let inp_bc_val = BlockSome (BlockPair (BlockList (MAP BlockSym ts),s_bc_val))
        in
          ?new_inp.
            INPUT_TYPE (SOME (ts,s)) new_inp /\
            COMPILER_RUN_INV (bs with refs := bs.refs |+ (inp_ptr,inp_bc_val))
              new_inp outp``,
  simp[COMPILER_RUN_INV_def] >> strip_tac >> simp[] >>
  imp_res_tac env_rs_repl_decs_inp_out >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- fs[finite_mapTheory.FLOOKUP_DEF] >>
  fs[rich_listTheory.EL_APPEND2] >>
  fs[OUTPUT_TYPE_def] >>
  fs[std_preludeTheory.SUM_TYPE_def] >>
  BasicProvers.VAR_EQ_TAC >>
  fs[compilerTerminationTheory.v_to_Cv_def] >>
  ntac 3 (pop_assum mp_tac) >>
  simp[] >>
  simp[Once intLangTheory.syneq_cases] >> rw[] >>
  qpat_assum`Cv_bv X Y out`mp_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  rw[] >>
  `FLOOKUP (cmap new_compiler_state.contab) (SOME (Short "Inr")) = SOME (14-block_tag)` by (
    REWRITE_TAC[new_compiler_state_contab] >>
    EVAL_TAC ) >>
  fs[BlockInr_def] >>
  qpat_assum`PAIR_TYPE X Y Z A`mp_tac >>
  simp[Once mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >>
  fs[compilerTerminationTheory.v_to_Cv_def] >>
  `FLOOKUP (cmap new_compiler_state.contab) (SOME (Short "Pair")) = SOME (pair_tag-block_tag)` by (
    REWRITE_TAC[new_compiler_state_contab] >>
    EVAL_TAC) >>
  fs[] >>
  qpat_assum`syneq (CConv X Y) Z`mp_tac >>
  simp[Once intLangTheory.syneq_cases] >> rw[] >>
  qpat_assum`Cv_bv X Y out`mp_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  rw[] >>
  simp[BlockPair_def,pair_tag_def] >>
  conj_tac >- (
    MATCH_MP_TAC (MP_CANON (GEN_ALL LIST_TYPE_CHAR_BlockList)) >>
    qmatch_assum_abbrev_tac `Cv_bv pp v y` >>
    qmatch_assum_abbrev_tac `syneq (v_to_Cv m cm l) v` >>
    map_every qexists_tac[`pp`,`m`,`cm`,`l`,`v`] >>
    simp[] >>
    qunabbrev_tac`cm` >>
    REWRITE_TAC[new_compiler_state_contab] >>
    EVAL_TAC ) >>
  gen_tac >>
  fs[GSYM STATE_TYPE_def] >>
  imp_res_tac INPUT_TYPE_exists >>
  pop_assum(qspec_then`ts`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`INPUT_TYPE (SOME (ts,s)) new_inp` >>
  qexists_tac`new_inp` >> simp[] >>
  reverse conj_tac >- (
    fs[semanticsExtraTheory.closed_context_def] >>
    conj_asm1_tac >- METIS_TAC[INPUT_TYPE_closed] >>
    conj_tac >- (
      fs[semanticsExtraTheory.closed_under_cenv_def] >>
      rw[] >> TRY (METIS_TAC[]) >>
      MATCH_MP_TAC (GEN_ALL INPUT_TYPE_all_cns_repl_decs_cenv) >>
      metis_tac[] ) >>
    conj_tac >- (
      fs[semanticsExtraTheory.closed_under_menv_def] ) >>
    rw[] >> TRY (METIS_TAC[]) >>
    imp_res_tac INPUT_TYPE_all_locs >>
    simp[] ) >>
  qexists_tac`rd` >>
  MATCH_MP_TAC compilerProofsTheory.env_rs_change_store >>
  qexists_tac`rd` >>
  qmatch_assum_abbrev_tac`env_rs [] ee cs repl_decs_env new_compiler_state 0 rd bs` >>
  qexists_tac`cs` >> qexists_tac`bs` >>
  simp[bytecodeTheory.bc_state_component_equality] >>
  simp[Abbr`cs`] >>
  fs[compilerProofsTheory.env_rs_def,LET_THM,new_compiler_state_rmenv,pmatchTheory.vs_to_Cvs_MAP] >>
  qmatch_assum_abbrev_tac`LIST_REL syneq (l1 ++ [ii;oo]) Cs` >>
  `LENGTH l1 + 1 < LENGTH Cs` by (
    simp[Abbr`l1`] >> fs[EVERY2_EVERY] >> simp[] ) >>
  qabbrev_tac`Cs1 = TAKE (LENGTH l1) Cs` >>
  qabbrev_tac`Cs2 = DROP (LENGTH l1 + 1) Cs` >>
  (*
  qpat_assum`INPUT_TYPE X Y`mp_tac >>
  simp[INPUT_TYPE_def] >>
  simp[std_preludeTheory.OPTION_TYPE_def] >>
  simp[mini_preludeTheory.PAIR_TYPE_def] >>
  strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qmatch_assum_rename_tac`new_inp = Conv (SOME(Short"Some"))[Conv(SOME(Short"Pair"))[vts;vs]]`[] >>
  pop_assum mp_tac >>
  qmatch_assum_rename_tac`PAIR_TYPE BOOL X s vs0`["X"] >>
  strip_tac >>
  qabbrev_tac`new_inp0 = Conv (SOME(Short"Some"))[Conv(SOME(Short"Pair"))[vts;vs0]]` >>
  *)
  qexists_tac`Cs1 ++ [v_to_Cv FEMPTY (cmap new_compiler_state.contab) new_inp] ++ Cs2` >>
  `FLOOKUP (cmap new_compiler_state.contab) (SOME(Short"Some")) = SOME 7` by (
    REWRITE_TAC[new_compiler_state_contab] >>
    EVAL_TAC ) >>
  conj_tac >- (
    fs[toBytecodeProofsTheory.Cenv_bs_def] >>
    fs[toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def] >>
    fs[miscTheory.FEVERY_ALL_FLOOKUP,UNCURRY] >>
    simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
    conj_tac >- ( rw[] >> fs[finite_mapTheory.FLOOKUP_DEF] ) >>
    conj_asm1_tac >- simp[Abbr`Cs1`,Abbr`Cs2`] >>
    conj_tac >- fs[EVERY_MEM] >>
    qpat_assum`EVERY2 R Cs Z`mp_tac >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,EL_MAP,finite_mapTheory.FAPPLY_FUPDATE_THM] >>
    rw[] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[] >>
    `(EL n rd.sm = pinp) ⇔ (n = LENGTH ml_repl_step_decls_s)` by (
      fs[compilerLibTheory.el_check_def] >> rw[] >>
      simp[EQ_IMP_THM] >>
      fs[EL_ALL_DISTINCT_EL_EQ] >>
      `n < LENGTH rd.sm` by simp[] >>
      METIS_TAC[] ) >>
    simp[] >>
    fs[Abbr`Cs1`,Abbr`Cs2`] >>
    `LENGTH l1 = LENGTH ml_repl_step_decls_s` by (
      simp[Abbr`l1`] ) >>
    Cases_on`n < LENGTH (TAKE (LENGTH l1) Cs)`>- (
      simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
      simp[rich_listTheory.EL_TAKE] ) >>
    fs[] >> rfs[] >>
    Cases_on`n = LENGTH (TAKE (LENGTH ml_repl_step_decls_s) Cs)`>- (
      simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
      strip_tac >>
      simp[Abbr`new_inp`] >>
      simp[compilerTerminationTheory.v_to_Cv_def] >>
      simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
      simp[BlockSome_def] >>
      simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
      simp[pair_tag_def] >>
      conj_tac >- (
        match_mp_tac (MP_CANON (GEN_ALL LIST_TYPE_Cv_bv)) >>
        qexists_tac`LEXER_FUN_SYMBOL_TYPE` >>
        conj_asm1_tac >- (
          REWRITE_TAC[new_compiler_state_contab] >>
          EVAL_TAC ) >>
        fs[INPUT_TYPE_def,mini_preludeTheory.PAIR_TYPE_def,std_preludeTheory.OPTION_TYPE_def] >>
        rw[] >>
        match_mp_tac (MP_CANON LEXER_FUN_SYMBOL_TYPE_Cv_bv) >>
        simp[] >>
        REWRITE_TAC[new_compiler_state_contab] >>
        EVAL_TAC ) >>
      qmatch_abbrev_tac`Cv_bv pp X Y` >>
      qmatch_assum_abbrev_tac`Cv_bv pp X' Y` >>
      match_mp_tac (MP_CANON (CONJUNCT1 toBytecodeProofsTheory.Cv_bv_syneq)) >>
      qexists_tac`X'` >>
      simp[] >>
      match_mp_tac (MP_CANON intLangExtraTheory.syneq_sym_all_vlabs) >>
      simp[Abbr`X`] >>
      match_mp_tac toIntLangProofsTheory.no_closures_all_vlabs >>
      match_mp_tac ml_translatorTheory.no_closures_IMP_NOT_contains_closure >>
      match_mp_tac (GEN_ALL STATE_TYPE_no_closures) >>
      metis_tac[]) >>
    simp[rich_listTheory.EL_APPEND2] >>
    simp[rich_listTheory.EL_DROP] ) >>
  conj_tac >- (
    REWRITE_TAC[Once (GSYM APPEND_ASSOC)] >>
    match_mp_tac miscTheory.EVERY2_APPEND_suff >>
    simp[Abbr`Cs1`,Abbr`Cs2`] >>
    qpat_assum`EVERY2 syneq X Cs`mp_tac >>
    Q.ISPECL_THEN[`LENGTH l1`,`Cs`](assume_tac o SYM) TAKE_DROP >>
    pop_assum SUBST1_TAC >>
    qmatch_abbrev_tac`LIST_REL syneq (l1 ++ l2) (Cl1 ++ Cl2) ==> X` >>
    strip_tac >>
    Q.ISPECL_THEN[`Cl2`,`l2`,`Cl1`,`l1`,`syneq`]mp_tac
      (GEN_ALL(snd(EQ_IMP_RULE miscTheory.EVERY2_APPEND))) >>
    discharge_hyps >- (
      simp[] >>
      conj_asm1_tac >- (
        simp[Abbr`Cl1`,Abbr`l1`,Abbr`Cl2`] >>
        fs[] >> simp[] ) >>
      fs[EVERY2_EVERY] ) >>
    strip_tac >>
    imp_res_tac EVERY2_LENGTH >>
    simp[TAKE_APPEND1,rich_listTheory.DROP_APPEND2] >>
    simp[Abbr`Cl2`,Abbr`Cl1`,Abbr`l2`] >>
    fs[]) >>
  conj_tac >- (
    rw[] >>
    fs[compilerLibTheory.el_check_def] >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    qunabbrev_tac`Cs1`>>
    qunabbrev_tac`Cs2`>>
    MATCH_MP_TAC EVERY_APPEND_lemma >>
    simp[] >>
    fs[intLangExtraTheory.closed_vlabs_def] >>
    MATCH_MP_TAC toIntLangProofsTheory.no_closures_all_vlabs >>
    MATCH_MP_TAC ml_translatorTheory.no_closures_IMP_NOT_contains_closure >>
    MATCH_MP_TAC (GEN_ALL INPUT_TYPE_no_closures) >>
    METIS_TAC[] ) >>
  conj_tac >- (
    REWRITE_TAC[IN_vlabs_list_EVERY] >>
    REWRITE_TAC[EVERY_MAP] >>
    qunabbrev_tac`Cs1`>>
    qunabbrev_tac`Cs2`>>
    MATCH_MP_TAC EVERY_APPEND_lemma >>
    qpat_assum`closed_vlabs A B X Y Z`mp_tac >>
    simp[intLangExtraTheory.closed_vlabs_def,IN_vlabs_list_EVERY,EVERY_MAP] >>
    strip_tac >>
    imp_res_tac INPUT_TYPE_no_closures >>
    imp_res_tac ml_translatorTheory.no_closures_IMP_NOT_contains_closure >>
    imp_res_tac toIntLangProofsTheory.no_closures_vlabs >>
    simp[] ) >>
  simp[] >>
  fs[intLangExtraTheory.closed_Clocs_def] >>
  `∃xx. Cs = Cs1 ++ [xx] ++ Cs2` by (
    simp[Abbr`Cs1`,Abbr`Cs2`] >>
    simp[LIST_EQ_REWRITE] >>
    qexists_tac`EL (LENGTH l1) Cs` >>
    rw[] >>
    Cases_on`x < LENGTH l1`>>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,rich_listTheory.EL_TAKE] >>
    Cases_on`x = LENGTH l1`>>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,rich_listTheory.EL_TAKE] >>
    simp[rich_listTheory.EL_DROP] ) >>
  fs[pred_setTheory.SUBSET_DEF,PULL_EXISTS] >>
  rw[] >> simp[] >>
  TRY (res_tac >> DECIDE_TAC) >>
  imp_res_tac INPUT_TYPE_all_locs >>
  fs[toIntLangProofsTheory.all_Clocs_v_to_Cv]);

val COMPILER_RUN_INV_INL = store_thm("COMPILER_RUN_INV_INL",
  ``COMPILER_RUN_INV bs inp outp /\ OUTPUT_TYPE (INL (m,code,s)) outp ==>
    ?x outp_ptr inp_ptr rest m_bc_val s_bc_val.
      (bs.stack = x::(RefPtr outp_ptr)::(RefPtr inp_ptr)::rest) /\
      inp_ptr IN FDOM bs.refs /\
      (FLOOKUP bs.refs outp_ptr =
         SOME (BlockInl (BlockPair (m_bc_val,
                 BlockPair (BlockList (MAP BlockNum3 code),s_bc_val))))) /\
      !ts b.
        let inp_bc_val = BlockSome (BlockPair (BlockList (MAP BlockSym ts),
                                      BlockPair (BlockBool b,s_bc_val)))
        in
          ?new_inp.
            INPUT_TYPE (SOME (ts,b,s)) new_inp /\
            COMPILER_RUN_INV (bs with refs := bs.refs |+ (inp_ptr,inp_bc_val))
              new_inp outp``,
  simp[COMPILER_RUN_INV_def] >> strip_tac >> simp[] >>
  imp_res_tac env_rs_repl_decs_inp_out >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- fs[finite_mapTheory.FLOOKUP_DEF] >>
  fs[rich_listTheory.EL_APPEND2] >>
  fs[OUTPUT_TYPE_def] >>
  fs[std_preludeTheory.SUM_TYPE_def] >>
  BasicProvers.VAR_EQ_TAC >>
  fs[compilerTerminationTheory.v_to_Cv_def] >>
  ntac 3 (pop_assum mp_tac) >>
  simp[] >>
  simp[Once intLangTheory.syneq_cases] >> rw[] >>
  qpat_assum`Cv_bv X Y out`mp_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  rw[] >>
  `FLOOKUP (cmap new_compiler_state.contab) (SOME (Short "Inl")) = SOME (15-block_tag)` by (
    REWRITE_TAC[new_compiler_state_contab] >>
    EVAL_TAC ) >>
  fs[BlockInl_def] >>
  qpat_assum`PAIR_TYPE X Y Z A`mp_tac >>
  simp[Once mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >>
  fs[compilerTerminationTheory.v_to_Cv_def] >>
  `FLOOKUP (cmap new_compiler_state.contab) (SOME (Short "Pair")) = SOME (pair_tag-block_tag)` by (
    REWRITE_TAC[new_compiler_state_contab] >>
    EVAL_TAC) >>
  fs[] >>
  qpat_assum`syneq (CConv X Y) Z`mp_tac >>
  simp[Once intLangTheory.syneq_cases] >> rw[] >>
  qpat_assum`Cv_bv X Y out`mp_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  rw[] >>
  simp[BlockPair_def,pair_tag_def] >>
  fs[mini_preludeTheory.PAIR_TYPE_def] >>
  BasicProvers.VAR_EQ_TAC >>
  fs[compilerTerminationTheory.v_to_Cv_def] >>
  rfs[] >>
  qpat_assum`syneq (CConv X Y) Z`mp_tac >>
  simp[Once intLangTheory.syneq_cases] >> rw[] >>
  qpat_assum`Cv_bv X Y out`mp_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  rw[] >>
  simp[pair_tag_def] >>
  conj_tac >- (
    MATCH_MP_TAC (MP_CANON (GEN_ALL LIST_TYPE_Num3_Blocklist)) >>
    qmatch_assum_abbrev_tac`LIST_TYPE A code a` >>
    qmatch_assum_abbrev_tac`syneq (v_to_Cv mm cm a) b` >>
    qmatch_assum_abbrev_tac`Cv_bv pp b c` >>
    map_every qexists_tac[`pp`,`mm`,`cm`,`a`,`b`] >>
    simp[] >>
    qunabbrev_tac`cm` >>
    REWRITE_TAC[new_compiler_state_contab] >>
    EVAL_TAC ) >>
  rpt gen_tac >>
  qmatch_assum_abbrev_tac`A s v` >>
  `STATE_TYPE (b,s) (Conv(SOME(Short"Pair"))[@v. BOOL b v;v])` by (
    simp[STATE_TYPE_def,mini_preludeTheory.PAIR_TYPE_def] >>
    simp[ml_translatorTheory.BOOL_def] ) >>
  imp_res_tac INPUT_TYPE_exists >>
  pop_assum(qspec_then`ts`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`INPUT_TYPE (SOME (ts,b,s)) new_inp` >>
  qexists_tac`new_inp` >> simp[] >>
  reverse conj_tac >- (
    fs[semanticsExtraTheory.closed_context_def] >>
    conj_asm1_tac >- METIS_TAC[INPUT_TYPE_closed] >>
    conj_tac >- (
      fs[semanticsExtraTheory.closed_under_cenv_def] >>
      rw[] >> TRY (METIS_TAC[]) >>
      MATCH_MP_TAC (GEN_ALL INPUT_TYPE_all_cns_repl_decs_cenv) >>
      metis_tac[] ) >>
    conj_tac >- (
      fs[semanticsExtraTheory.closed_under_menv_def] ) >>
    rw[] >> TRY (METIS_TAC[]) >>
    imp_res_tac INPUT_TYPE_all_locs >>
    simp[] ) >>
  qexists_tac`rd` >>
  MATCH_MP_TAC compilerProofsTheory.env_rs_change_store >>
  qexists_tac`rd` >>
  qmatch_assum_abbrev_tac`env_rs [] ee cs repl_decs_env new_compiler_state 0 rd bs` >>
  qexists_tac`cs` >> qexists_tac`bs` >>
  simp[bytecodeTheory.bc_state_component_equality] >>
  simp[Abbr`cs`] >>
  fs[compilerProofsTheory.env_rs_def,LET_THM,new_compiler_state_rmenv,pmatchTheory.vs_to_Cvs_MAP] >>
  qmatch_assum_abbrev_tac`LIST_REL syneq (l1 ++ [ii;oo]) Cs` >>
  `LENGTH l1 + 1 < LENGTH Cs` by (
    simp[Abbr`l1`] >> fs[EVERY2_EVERY] >> simp[] ) >>
  qabbrev_tac`Cs1 = TAKE (LENGTH l1) Cs` >>
  qabbrev_tac`Cs2 = DROP (LENGTH l1 + 1) Cs` >>
  qexists_tac`Cs1 ++ [v_to_Cv FEMPTY (cmap new_compiler_state.contab) new_inp] ++ Cs2` >>
  `FLOOKUP (cmap new_compiler_state.contab) (SOME(Short"Some")) = SOME 7` by (
    REWRITE_TAC[new_compiler_state_contab] >>
    EVAL_TAC ) >>
  conj_tac >- (
    fs[toBytecodeProofsTheory.Cenv_bs_def] >>
    fs[toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def] >>
    fs[miscTheory.FEVERY_ALL_FLOOKUP,UNCURRY] >>
    simp[finite_mapTheory.FAPPLY_FUPDATE_THM] >>
    conj_tac >- ( rw[] >> fs[finite_mapTheory.FLOOKUP_DEF] ) >>
    conj_asm1_tac >- simp[Abbr`Cs1`,Abbr`Cs2`] >>
    conj_tac >- fs[EVERY_MEM] >>
    qpat_assum`EVERY2 R Cs Z`mp_tac >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,EL_MAP,finite_mapTheory.FAPPLY_FUPDATE_THM] >>
    rw[] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[] >>
    `(EL n rd.sm = pinp) ⇔ (n = LENGTH ml_repl_step_decls_s)` by (
      fs[compilerLibTheory.el_check_def] >> rw[] >>
      simp[EQ_IMP_THM] >>
      fs[EL_ALL_DISTINCT_EL_EQ] >>
      `n < LENGTH rd.sm` by simp[] >>
      METIS_TAC[] ) >>
    simp[] >>
    fs[Abbr`Cs1`,Abbr`Cs2`] >>
    `LENGTH l1 = LENGTH ml_repl_step_decls_s` by (
      simp[Abbr`l1`] ) >>
    Cases_on`n < LENGTH (TAKE (LENGTH l1) Cs)`>- (
      simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
      simp[rich_listTheory.EL_TAKE] ) >>
    fs[] >> rfs[] >>
    Cases_on`n = LENGTH (TAKE (LENGTH ml_repl_step_decls_s) Cs)`>- (
      simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
      strip_tac >>
      simp[Abbr`new_inp`] >>
      simp[compilerTerminationTheory.v_to_Cv_def] >>
      simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
      simp[BlockSome_def] >>
      simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
      simp[pair_tag_def] >>
      conj_tac >- (
        match_mp_tac (MP_CANON (GEN_ALL LIST_TYPE_Cv_bv)) >>
        qexists_tac`LEXER_FUN_SYMBOL_TYPE` >>
        conj_asm1_tac >- (
          REWRITE_TAC[new_compiler_state_contab] >>
          EVAL_TAC ) >>
        fs[INPUT_TYPE_def,mini_preludeTheory.PAIR_TYPE_def,std_preludeTheory.OPTION_TYPE_def] >>
        rw[] >>
        match_mp_tac (MP_CANON LEXER_FUN_SYMBOL_TYPE_Cv_bv) >>
        simp[] >>
        REWRITE_TAC[new_compiler_state_contab] >>
        EVAL_TAC ) >>
      simp[Once toBytecodeProofsTheory.Cv_bv_cases,ml_translatorTheory.BOOL_def] >>
      simp[compilerTerminationTheory.v_to_Cv_def] >>
      simp[Once toBytecodeProofsTheory.Cv_bv_cases,BlockBool_def] >>
      fs[Abbr`A`,GSYM SUBSTATE_TYPE_def] >>
      qmatch_abbrev_tac`Cv_bv pp X Y` >>
      qmatch_assum_abbrev_tac`Cv_bv pp X' Y` >>
      match_mp_tac (MP_CANON (CONJUNCT1 toBytecodeProofsTheory.Cv_bv_syneq)) >>
      qexists_tac`X'` >>
      simp[] >>
      match_mp_tac (MP_CANON intLangExtraTheory.syneq_sym_all_vlabs) >>
      simp[Abbr`X`] >>
      match_mp_tac toIntLangProofsTheory.no_closures_all_vlabs >>
      metis_tac[SUBSTATE_TYPE_no_closures,ml_translatorTheory.no_closures_IMP_NOT_contains_closure]) >>
    simp[rich_listTheory.EL_APPEND2] >>
    simp[rich_listTheory.EL_DROP] ) >>
  conj_tac >- (
    REWRITE_TAC[Once (GSYM APPEND_ASSOC)] >>
    match_mp_tac miscTheory.EVERY2_APPEND_suff >>
    simp[Abbr`Cs1`,Abbr`Cs2`] >>
    qpat_assum`EVERY2 syneq X Cs`mp_tac >>
    Q.ISPECL_THEN[`LENGTH l1`,`Cs`](assume_tac o SYM) TAKE_DROP >>
    pop_assum SUBST1_TAC >>
    qmatch_abbrev_tac`LIST_REL syneq (l1 ++ l2) (Cl1 ++ Cl2) ==> X` >>
    strip_tac >>
    Q.ISPECL_THEN[`Cl2`,`l2`,`Cl1`,`l1`,`syneq`]mp_tac
      (GEN_ALL(snd(EQ_IMP_RULE miscTheory.EVERY2_APPEND))) >>
    discharge_hyps >- (
      simp[] >>
      conj_asm1_tac >- (
        simp[Abbr`Cl1`,Abbr`l1`,Abbr`Cl2`] >>
        fs[] >> simp[] ) >>
      fs[EVERY2_EVERY] ) >>
    strip_tac >>
    imp_res_tac EVERY2_LENGTH >>
    simp[TAKE_APPEND1,rich_listTheory.DROP_APPEND2] >>
    simp[Abbr`Cl2`,Abbr`Cl1`,Abbr`l2`] >>
    fs[]) >>
  conj_tac >- (
    rw[] >>
    fs[compilerLibTheory.el_check_def] >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    qunabbrev_tac`Cs1`>>
    qunabbrev_tac`Cs2`>>
    MATCH_MP_TAC EVERY_APPEND_lemma >>
    simp[] >>
    fs[intLangExtraTheory.closed_vlabs_def] >>
    MATCH_MP_TAC toIntLangProofsTheory.no_closures_all_vlabs >>
    MATCH_MP_TAC ml_translatorTheory.no_closures_IMP_NOT_contains_closure >>
    MATCH_MP_TAC (GEN_ALL INPUT_TYPE_no_closures) >>
    METIS_TAC[] ) >>
  conj_tac >- (
    REWRITE_TAC[IN_vlabs_list_EVERY] >>
    REWRITE_TAC[EVERY_MAP] >>
    qunabbrev_tac`Cs1`>>
    qunabbrev_tac`Cs2`>>
    MATCH_MP_TAC EVERY_APPEND_lemma >>
    qpat_assum`closed_vlabs Q B X Y Z`mp_tac >>
    simp[intLangExtraTheory.closed_vlabs_def,IN_vlabs_list_EVERY,EVERY_MAP] >>
    strip_tac >>
    imp_res_tac INPUT_TYPE_no_closures >>
    imp_res_tac ml_translatorTheory.no_closures_IMP_NOT_contains_closure >>
    imp_res_tac toIntLangProofsTheory.no_closures_vlabs >>
    simp[] ) >>
  simp[] >>
  fs[intLangExtraTheory.closed_Clocs_def] >>
  `∃xx. Cs = Cs1 ++ [xx] ++ Cs2` by (
    simp[Abbr`Cs1`,Abbr`Cs2`] >>
    simp[LIST_EQ_REWRITE] >>
    qexists_tac`EL (LENGTH l1) Cs` >>
    rw[] >>
    Cases_on`x < LENGTH l1`>>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,rich_listTheory.EL_TAKE] >>
    Cases_on`x = LENGTH l1`>>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2,rich_listTheory.EL_TAKE] >>
    simp[rich_listTheory.EL_DROP] ) >>
  fs[pred_setTheory.SUBSET_DEF,PULL_EXISTS] >>
  rw[] >> simp[] >>
  TRY (res_tac >> DECIDE_TAC) >>
  imp_res_tac INPUT_TYPE_all_locs >>
  fs[toIntLangProofsTheory.all_Clocs_v_to_Cv]);

(* --- misc --- *)

val SNOC3 = prove(
   ``xs ++ [x3;x2;x1] = SNOC x1 (SNOC x2 (SNOC x3 xs))``,
  SRW_TAC [] []);

(* prove various types have no closures *)

val _ = augment_srw_ss[rewrites[terminationTheory.contains_closure_def,ml_translatorTheory.no_closures_def]]

val LIST_TYPE_no_closures = prove(
  ``∀x. (∀a v. MEM a x ∧ A a v ⇒ no_closures v) ⇒
    ∀l. LIST_TYPE A x l ⇒ no_closures l``,
  Induct >>
  simp[mini_preludeTheory.LIST_TYPE_def] >>
  simp[PULL_EXISTS] >> fs[] >>
  METIS_TAC[])

val PAIR_TYPE_no_closures = prove(
  ``∀p q. (∀x y. (x = FST p) ∧ A x y ⇒ no_closures y) ∧
          (∀x y. (x = SND p) ∧ B x y ⇒ no_closures y) ∧
          PAIR_TYPE A B p q ⇒ no_closures q``,
  Cases >> simp[mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >> rw[] >> METIS_TAC[])

val LEXER_FUN_SYMBOL_TYPE_no_closures = prove(
  ``∀x y. LEXER_FUN_SYMBOL_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def] >> rw[] >>
  fs[ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC (MP_CANON (Q.ISPEC`CHAR`(Q.GEN`A` LIST_TYPE_no_closures))) >>
  rw[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  HINT_EXISTS_TAC >>rw[])

val OPTION_TYPE_no_closures = prove(
  ``∀x y. (∀x y. A x y ⇒ no_closures y) ∧
          OPTION_TYPE A x y ⇒ no_closures y``,
  Cases >> simp[std_preludeTheory.OPTION_TYPE_def] >>
  rw[] >> rw[] >> METIS_TAC[])

val AST_ID_TYPE_no_closures = prove(
  ``∀x y. (∀x y. A x y ⇒ no_closures y) ∧
          AST_ID_TYPE A x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.AST_ID_TYPE_def] >>
  rw[] >> rw[] >>
  res_tac >>
  qmatch_assum_abbrev_tac`LIST_TYPE B ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`B`] >> simp[] >>
  rw[Abbr`B`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val COMPILER_COMPILER_STATE_TYPE_no_closures = prove(
  ``∀x y. COMPILER_COMPILER_STATE_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.COMPILER_COMPILER_STATE_TYPE_def,PULL_EXISTS] >>
  PairCases_on`p` >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS,std_preludeTheory.FMAP_TYPE_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  rpt gen_tac >> strip_tac >> rpt conj_tac >>
  rpt (
    qmatch_abbrev_tac`no_closures x` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) OPTION_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val AST_TC0_TYPE_no_closures = prove(
  ``∀x y. AST_TC0_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.AST_TC0_TYPE_def] >>
  rw[] >> rw[] >>
  qmatch_abbrev_tac`no_closures x` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`no_closures x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val infer_t_ind =
  (TypeBase.induction_of``:infer_t``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val t_ind =
  (TypeBase.induction_of``:t``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val pat_ind =
  (TypeBase.induction_of``:pat``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val exp_ind =
  (TypeBase.induction_of``:exp``)
  |> Q.SPECL[`P`,`EVERY (P o SND o SND)`,`P o SND o SND`,`EVERY (P o SND)`,`P o SND`,`P o SND`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val UNIFY_INFER_T_TYPE_no_closures = prove(
  ``∀x y. UNIFY_INFER_T_TYPE x y ⇒ no_closures y``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[ml_repl_stepTheory.UNIFY_INFER_T_TYPE_def] >>
  rw[] >> rw[] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  qmatch_abbrev_tac`no_closures x` >>
  TRY (
    qmatch_assum_abbrev_tac`AST_TC0_TYPE ll x` >>
    Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_no_closures >>
    qexists_tac`ll` >> rw[] ) >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val AST_T_TYPE_no_closures = prove(
  ``∀x y. AST_T_TYPE x y ⇒ no_closures y``,
  HO_MATCH_MP_TAC t_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def] >>
  rw[] >> rw[] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  qmatch_abbrev_tac`no_closures z` >>
  TRY (
    qmatch_assum_abbrev_tac`AST_TC0_TYPE ll z` >>
    Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_no_closures >>
    qexists_tac`ll` >> rw[] ) >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll z` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val AST_LIT_TYPE_no_closures = prove(
  ``∀x y. AST_LIT_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.AST_LIT_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def] >>
  match_mp_tac LIST_TYPE_no_closures >>
  simp[std_preludeTheory.CHAR_def,NUM_def,INT_def])

val AST_PAT_TYPE_no_closures = prove(
  ``∀x y. AST_PAT_TYPE x y ⇒ no_closures y``,
  HO_MATCH_MP_TAC pat_ind >>
  simp[ml_repl_stepTheory.AST_PAT_TYPE_def] >>
  rw[] >> rw[] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  qmatch_abbrev_tac`no_closures z` >>
  TRY (
    qmatch_assum_abbrev_tac`AST_LIT_TYPE ll z` >>
    Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_LIT_TYPE_no_closures >>
    qexists_tac`ll` >> rw[] ) >>
  TRY (
    qpat_assum`OPTION_TYPE A oo z`mp_tac >>
    match_mp_tac (REWRITE_RULE[GSYM AND_IMP_INTRO]OPTION_TYPE_no_closures) >>
    match_mp_tac (REWRITE_RULE[GSYM AND_IMP_INTRO]AST_ID_TYPE_no_closures) >>
    rw[] >>
    match_mp_tac (MP_CANON(Q.ISPEC`CHAR`(Q.GEN`A`LIST_TYPE_no_closures))) >>
    rw[std_preludeTheory.CHAR_def,INT_def,NUM_def] >>
    HINT_EXISTS_TAC >> rw[] ) >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll z` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val AST_OPN_TYPE_no_closures = prove(
  ``∀x y. AST_OPN_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.AST_OPN_TYPE_def,PULL_EXISTS])

val AST_OPB_TYPE_no_closures = prove(
  ``∀x y. AST_OPB_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.AST_OPB_TYPE_def,PULL_EXISTS])

val AST_OP_TYPE_no_closures = prove(
  ``∀x y. AST_OP_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.AST_OP_TYPE_def,PULL_EXISTS] >>
  METIS_TAC[AST_OPN_TYPE_no_closures,AST_OPB_TYPE_no_closures])

val AST_UOP_TYPE_no_closures = prove(
  ``∀x y. AST_UOP_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.AST_UOP_TYPE_def])

val AST_LOP_TYPE_no_closures = prove(
  ``∀x y. AST_LOP_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.AST_LOP_TYPE_def])

val AST_EXP_TYPE_no_closures = prove(
  ``∀z y. AST_EXP_TYPE z y ⇒ no_closures y``,
  HO_MATCH_MP_TAC exp_ind >>
  simp[ml_repl_stepTheory.AST_EXP_TYPE_def] >>
  rw[] >> rw[] >>
  rpt (
    qmatch_abbrev_tac`no_closures x` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) OPTION_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_PAT_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_PAT_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_OP_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_OP_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_UOP_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_UOP_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_LOP_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_LOP_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_LIT_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_LIT_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac >>
    TRY (fs[EVERY_MEM] >> res_tac >> NO_TAC)))

val SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_no_closures = prove(
  ``∀x y. SEMANTICPRIMITIVES_TID_OR_EXN_TYPE x y ⇒ no_closures y``,
  Cases >>
  simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
  rw[] >> rw[] >>
  qmatch_abbrev_tac`no_closures z` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`no_closures z` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll z` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )

val REPL_FUN_REPL_FUN_STATE_TYPE_no_closures = prove(
  ``∀x y. REPL_FUN_REPL_FUN_STATE_TYPE x y ⇒ no_closures y``,
  Cases >>
  PairCases_on`p0`>>
  PairCases_on`p`>>
  simp[ml_repl_stepTheory.REPL_FUN_REPL_FUN_STATE_TYPE_def] >>
  simp[PULL_EXISTS,mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >>
  TRY (
    MATCH_MP_TAC (MP_CANON COMPILER_COMPILER_STATE_TYPE_no_closures) >>
    qexists_tac`c` >> rw[] >> NO_TAC) >>
  rpt (
    qmatch_abbrev_tac`no_closures x` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) OPTION_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_TC0_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`UNIFY_INFER_T_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) UNIFY_INFER_T_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_T_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_T_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`SEMANTICPRIMITIVES_TID_OR_EXN_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val GRAMMAR_PARSETREE_TYPE_no_closures = prove(
  (*
  ``∀A B a b.
      (∀x y. (a = Lf (TOK x)) ∧ A x y ⇒ no_closures y) ∧
      (∀x y z. ((a = Lf (NT (INL x))) ∨ (a = Nd (INL x) z)) ∧ B x y ⇒ no_closures y) ∧
      GRAMMAR_PARSETREE_TYPE A B a b ⇒
      no_closures b``,
      *)
  ``∀A B a b.
      (∀x y. A x y ⇒ no_closures y) ∧
      (∀x y. B x y ⇒ no_closures y) ∧
      GRAMMAR_PARSETREE_TYPE A B a b ⇒
      no_closures b``,
  HO_MATCH_MP_TAC ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_ind >>
  simp[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS] >>
  conj_tac >> ntac 2 gen_tac >> Cases >> rw[std_preludeTheory.SUM_TYPE_def] >>
  fs[NUM_def,INT_def,ml_repl_stepTheory.GRAMMAR_SYMBOL_TYPE_def] >>
  TRY (Cases_on`s`>>fs[std_preludeTheory.SUM_TYPE_def,NUM_def,INT_def]) >>
  res_tac >> METIS_TAC[LIST_TYPE_no_closures])

val TOKENS_TOKEN_TYPE_no_closures = prove(
  ``∀x y. TOKENS_TOKEN_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.TOKENS_TOKEN_TYPE_def,PULL_EXISTS,NUM_def,INT_def] >>
  rw[] >>
  MATCH_MP_TAC (MP_CANON (Q.ISPEC`CHAR`(Q.GEN`A`LIST_TYPE_no_closures))) >>
  simp[std_preludeTheory.CHAR_def,NUM_def,INT_def] >>
  METIS_TAC[])

val GRAM_MMLNONT_TYPE_no_closures = prove(
  ``∀x y. GRAM_MMLNONT_TYPE x y ⇒ no_closures y``,
  Cases >> simp[ml_repl_stepTheory.GRAM_MMLNONT_TYPE_def])

(* one_one theorems for types - should be more automatic *)

val EqualityType_thm = prove(
  ``EqualityType abs ⇔
      (!x1 v1. abs x1 v1 ==> no_closures v1) /\
      (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> types_match v1 v2 /\
                                                ((v1 = v2) ⇔ (x1 = x2)))``,
  SIMP_TAC std_ss [EqualityType_def] \\ METIS_TAC []);

val EqualityType_CHAR = store_thm("EqualityType_CHAR",
  ``EqualityType CHAR``,
  EVAL_TAC >> SRW_TAC[][] >> EVAL_TAC)

val CHAR_11 = prove(
  ``∀x1 v1 x2 v2. CHAR x1 v1 ∧ CHAR x2 v2 ⇒ types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  METIS_TAC[EqualityType_CHAR,EqualityType_thm])

val LIST_TYPE_11 = prove(
  ``!P ts v1 us v2.
      (!x1.
       MEM x1 ts ==>
        !v1 x2 v2.
          P x1 v1 /\ P x2 v2 ==>
          types_match v1 v2 /\ ((v1 = v2) <=> (x1 = x2))) /\
    LIST_TYPE P ts v1 /\ LIST_TYPE P us v2 ==>
    types_match v1 v2 /\ ((v1 = v2) = (ts = us))``,
  STRIP_TAC \\ Induct \\ Cases_on `us` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [mini_preludeTheory.LIST_TYPE_def,types_match_def]
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS,types_match_def]
  \\ METIS_TAC []);

val LIST_TYPE_CHAR_11 =
  LIST_TYPE_11 |> Q.ISPEC`CHAR`
  |> SPEC_ALL |> REWRITE_RULE[Once(GSYM AND_IMP_INTRO)]
  |> UNDISCH |> prove_hyps_by (METIS_TAC[CHAR_11]) |> GEN_ALL

val types_match_Conv = prove(
  ``types_match (Conv x y) z ⇔ ∃x' y'. (z = Conv x' y') ∧ (x ≠ x' ∨ types_match_list y y')``,
  Cases_on`z` >> simp[types_match_def])

val types_match_list_0 = store_thm("types_match_list_0",
  ``types_match_list [] y ⇔ (y = [])``,
  Cases_on`y`>>simp[types_match_def])
val _ = export_rewrites["types_match_list_0"]

val types_match_list_1 = prove(
  ``types_match_list [x] y ⇔ ∃z. (y = [z]) ∧ types_match x z``,
  Cases_on`y`>>simp[types_match_def] >>
  Cases_on`t`>>simp[types_match_def])

val types_match_list_2 = prove(
  ``types_match_list [x;y] z ⇔ ∃w v. (z = [w;v]) ∧ types_match x w ∧ types_match y v``,
  Cases_on`z`>>simp[types_match_def,types_match_list_1,PULL_EXISTS] >> metis_tac[])

val types_match_list_3 = prove(
  ``types_match_list [x;y;z] w ⇔ ∃a b c. (w = [a;b;c]) ∧ types_match x a ∧ types_match y b ∧ types_match z c``,
  Cases_on`w`>>simp[types_match_def,types_match_list_2,PULL_EXISTS] >> metis_tac[])

val OPTION_TYPE_11 = prove(
  ``∀P o1 v1 o2 v2.
    (∀x1. (o1 = SOME x1) ⇒
          ∀v1 x2 v2.
            P x1 v1 ∧ P x2 v2 ⇒
              types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))) ∧
    OPTION_TYPE P o1 v1 ∧ OPTION_TYPE P o2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (o1 = o2))``,
  gen_tac >> Cases >> gen_tac >> Cases >>
  simp[std_preludeTheory.OPTION_TYPE_def,types_match_Conv,PULL_EXISTS] >>
  simp[types_match_list_1] >> metis_tac[])

val PAIR_TYPE_11 = prove(
  ``∀P1 P2 o1 v1 o2 v2.
    (∀a d. (o1 = (a,d)) ⇒
       ∀v1a v2a v1d v2d a2 d2.
        P1 a v1a ∧ P1 a2 v2a  ∧
        P2 d v1d ∧ P2 d2 v2d
        ⇒
        types_match v1a v2a ∧ ((v1a = v2a) ⇔ (a = a2)) ∧
        types_match v1d v2d ∧ ((v1d = v2d) ⇔ (d = d2))) ∧
    PAIR_TYPE P1 P2 o1 v1 ∧ PAIR_TYPE P1 P2 o2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (o1 = o2))``,
  ntac 2 gen_tac >> Cases >> gen_tac >> Cases >>
  simp[mini_preludeTheory.PAIR_TYPE_def,types_match_Conv,PULL_EXISTS] >>
  simp[types_match_list_2] >> metis_tac[])

val AST_ID_TYPE_11 = prove(
 ``∀P x1 v1 x2 v2.
    (∀s a1. (x1 = (Long s a1)) ∨ (x1 = Short a1) ⇒
      ∀v1 a2 v2. P a1 v1 ∧ P a2 v2 ⇒
        types_match v1 v2 ∧ ((v1 = v2) ⇔ (a1 = a2))) ∧
    AST_ID_TYPE P x1 v1 ∧ AST_ID_TYPE P x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  gen_tac >>
  Cases >> simp[ml_repl_stepTheory.AST_ID_TYPE_def,PULL_EXISTS] >>
  Cases >> simp[ml_repl_stepTheory.AST_ID_TYPE_def,PULL_EXISTS
               ,types_match_Conv,types_match_list_1,types_match_list_2] >>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_TC0_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_TC0_TYPE x1 v1 ∧ AST_TC0_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  Cases >> simp[ml_repl_stepTheory.AST_TC0_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_1] >>
  Cases >> simp[ml_repl_stepTheory.AST_TC0_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_1] >>
  METIS_TAC[AST_ID_TYPE_11,LIST_TYPE_CHAR_11])

val AST_T_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_T_TYPE x1 v1 ∧ AST_T_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  HO_MATCH_MP_TAC ml_repl_stepTheory.AST_T_TYPE_ind >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[ml_repl_stepTheory.AST_T_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_2] >>
    rw[] >>
    Cases_on`x2`>>fs[ml_repl_stepTheory.AST_T_TYPE_def]>>BasicProvers.VAR_EQ_TAC>>
    qmatch_assum_abbrev_tac`LIST_TYPE P ts v1` >>
    qpat_assum`LIST_TYPE P ts v1`mp_tac >>
    qmatch_assum_abbrev_tac`LIST_TYPE P us v2` >>
    strip_tac >>
    Q.ISPECL_THEN[`P`,`us`,`v2`,`ts`,`v1`]mp_tac LIST_TYPE_11 >>
    discharge_hyps >- METIS_TAC[] >> strip_tac >>
    METIS_TAC[AST_TC0_TYPE_11] ) >>
  conj_tac >- (
    simp[ml_repl_stepTheory.AST_T_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_1] >>
    rw[] >>
    Cases_on`x2`>>fs[ml_repl_stepTheory.AST_T_TYPE_def]>>BasicProvers.VAR_EQ_TAC>>
    fs[NUM_def,INT_def,types_match_def]) >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_1] >>
  rw[] >>
  Cases_on`x2`>>fs[ml_repl_stepTheory.AST_T_TYPE_def]>>BasicProvers.VAR_EQ_TAC>>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_LIT_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_LIT_TYPE x1 v1 ∧ AST_LIT_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  Cases >>
  simp[ml_repl_stepTheory.AST_LIT_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  Cases >>
  simp[ml_repl_stepTheory.AST_LIT_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  simp[types_match_def] >>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_PAT_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_PAT_TYPE x1 v1 ∧ AST_PAT_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  HO_MATCH_MP_TAC ml_repl_stepTheory.AST_PAT_TYPE_ind >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[ml_repl_stepTheory.AST_PAT_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_1] >>
    rw[] >>
    Cases_on`x2`>>fs[ml_repl_stepTheory.AST_PAT_TYPE_def]>>BasicProvers.VAR_EQ_TAC>>
    METIS_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[ml_repl_stepTheory.AST_PAT_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_2] >>
    rw[] >>
    Cases_on`x2`>>fs[ml_repl_stepTheory.AST_PAT_TYPE_def]>>BasicProvers.VAR_EQ_TAC>>
    qmatch_assum_abbrev_tac`LIST_TYPE P ts v1` >>
    qpat_assum`LIST_TYPE P ts v1`mp_tac >>
    qmatch_assum_abbrev_tac`LIST_TYPE P us v2` >>
    strip_tac >>
    Q.ISPECL_THEN[`P`,`us`,`v2`,`ts`,`v1`]mp_tac LIST_TYPE_11 >>
    discharge_hyps >- METIS_TAC[] >> strip_tac >>
    simp[] >>
    qmatch_assum_abbrev_tac`OPTION_TYPE Q o3 v3` >>
    qpat_assum`OPTION_TYPE Q o3 v3`mp_tac >>
    qmatch_assum_abbrev_tac`OPTION_TYPE Q o4 v4` >>
    strip_tac >>
    Q.ISPECL_THEN[`Q`,`o4`,`v4`,`o3`,`v3`]mp_tac OPTION_TYPE_11 >>
    discharge_hyps >- METIS_TAC[AST_ID_TYPE_11,LIST_TYPE_CHAR_11] >>
    simp[]) >>
  conj_tac >- (
    simp[ml_repl_stepTheory.AST_PAT_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_1] >>
    rw[] >>
    Cases_on`x2`>>fs[ml_repl_stepTheory.AST_PAT_TYPE_def]>>BasicProvers.VAR_EQ_TAC>>
    METIS_TAC[AST_LIT_TYPE_11]) >>
  simp[ml_repl_stepTheory.AST_PAT_TYPE_def,PULL_EXISTS,types_match_Conv,types_match_list_1] >>
  rw[] >>
  Cases_on`x2`>>fs[ml_repl_stepTheory.AST_PAT_TYPE_def]>>BasicProvers.VAR_EQ_TAC>>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_LOP_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_LOP_TYPE x1 v1 ∧ AST_LOP_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  Cases >>
  simp[ml_repl_stepTheory.AST_LOP_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  Cases >>
  simp[ml_repl_stepTheory.AST_LOP_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  simp[types_match_def] >>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_UOP_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_UOP_TYPE x1 v1 ∧ AST_UOP_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  Cases >>
  simp[ml_repl_stepTheory.AST_UOP_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  Cases >>
  simp[ml_repl_stepTheory.AST_UOP_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  simp[types_match_def] >>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_OPN_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_OPN_TYPE x1 v1 ∧ AST_OPN_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  Cases >>
  simp[ml_repl_stepTheory.AST_OPN_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  Cases >>
  simp[ml_repl_stepTheory.AST_OPN_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  simp[types_match_def] >>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_OPB_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_OPB_TYPE x1 v1 ∧ AST_OPB_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  Cases >>
  simp[ml_repl_stepTheory.AST_OPB_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  Cases >>
  simp[ml_repl_stepTheory.AST_OPB_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  simp[types_match_def] >>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_OP_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_OP_TYPE x1 v1 ∧ AST_OP_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  Cases >>
  simp[ml_repl_stepTheory.AST_OP_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  Cases >>
  simp[ml_repl_stepTheory.AST_OP_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  simp[types_match_def] >>
  METIS_TAC[LIST_TYPE_CHAR_11,AST_OPN_TYPE_11,AST_OPB_TYPE_11])

val AST_LIT_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_LIT_TYPE x1 v1 ∧ AST_LIT_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  Cases >>
  simp[ml_repl_stepTheory.AST_LIT_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  Cases >>
  simp[ml_repl_stepTheory.AST_LIT_TYPE_def,PULL_EXISTS] >>
  simp[INT_def,BOOL_def,types_match_Conv,PULL_EXISTS,types_match_list_1] >>
  simp[types_match_def] >>
  METIS_TAC[LIST_TYPE_CHAR_11])

val AST_EXP_TYPE_11 = prove(
  ``∀x1 v1 x2 v2.
    AST_EXP_TYPE x1 v1 ∧ AST_EXP_TYPE x2 v2 ⇒
    types_match v1 v2 ∧ ((v1 = v2) ⇔ (x1 = x2))``,
  HO_MATCH_MP_TAC ml_repl_stepTheory.AST_EXP_TYPE_ind >>
  simp[ml_repl_stepTheory.AST_EXP_TYPE_def,PULL_EXISTS,
       types_match_Conv,types_match_list_1,types_match_list_2,types_match_list_3] >>
  rpt conj_tac >>
  rpt gen_tac >> STRIP_TAC >> Cases_on`x2` >>
  fs[ml_repl_stepTheory.AST_EXP_TYPE_def] >>
  simp[ml_repl_stepTheory.AST_EXP_TYPE_def,PULL_EXISTS,
       types_match_Conv,types_match_list_1,types_match_list_2,types_match_list_3] >>
  rpt gen_tac >> TRY (disch_then assume_tac) >> fs[] >>
  TRY (
    qmatch_abbrev_tac`(types_match vv11 vv12 ∧ types_match vv21 vv22) ∧
                      ((vv11 = vv12) ∧ (vv21 = vv22) ⇔ (xx11 = xx12) ∧ (xx21 = xx22))` >>
    qsuff_tac`(types_match vv11 vv12 ∧ ((vv11 = vv12) ⇔ (xx11 = xx12))) ∧
              (types_match vv21 vv22 ∧ ((vv21 = vv22) ⇔ (xx21 = xx22)))` >- PROVE_TAC[] >>
    conj_tac >> unabbrev_all_tac ) >>
  TRY (
    qmatch_abbrev_tac`(types_match vv11 vv12 ∧ types_match vv21 vv22 ∧ types_match vv31 vv32) ∧
                      ((vv11 = vv12) ∧ (vv21 = vv22) ∧ (vv31 = vv32) ⇔ (xx11 = xx12) ∧ (xx21 = xx22) ∧ (xx31 = xx32))` >>
    qsuff_tac`(types_match vv11 vv12 ∧ ((vv11 = vv12) ⇔ (xx11 = xx12))) ∧
              (types_match vv21 vv22 ∧ ((vv21 = vv22) ⇔ (xx21 = xx22))) ∧
              (types_match vv31 vv32 ∧ ((vv31 = vv32) ⇔ (xx31 = xx32)))` >- PROVE_TAC[] >>
    conj_tac >|[ALL_TAC,conj_tac] >> unabbrev_all_tac ) >>
  rpt (
    TRY(
      qmatch_abbrev_tac`A ∧ B ∧ types_match X Y`>>
      REWRITE_TAC[Once CONJ_ASSOC]>>conj_tac>-metis_tac[]>>unabbrev_all_tac) >>
    qmatch_abbrev_tac`types_match vv1 vv2 ∧ ((vv1 = vv2) ⇔ (xx1 = xx2))` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A xx1 vv1` >>
      qmatch_assum_abbrev_tac`LIST_TYPE A xx2 vv2` >>
      TRY (METIS_TAC[LIST_TYPE_CHAR_11]) >>
      Q.ISPECL_THEN[`A`,`xx1`,`vv1`,`xx2`,`vv2`]mp_tac LIST_TYPE_11 >>
      discharge_hyps >> simp[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B xx1 vv1` >> rfs[] >> fs[] >>
      qmatch_assum_abbrev_tac`PAIR_TYPE A B xx2 vv2` >>
      Q.ISPECL_THEN[`A`,`B`,`xx1`,`vv1`,`xx2`,`vv2`]mp_tac PAIR_TYPE_11 >>
      discharge_hyps (* >|[
        simp[]>>gen_tac>>strip_tac>>strip_tac>>rpt gen_tac>>strip_tac>>
        REWRITE_TAC[Once CONJ_ASSOC] >>
        TRY (qmatch_abbrev_tac`(C1 ∧ C2) ∧ (C3 ∧ C4)`>>conj_tac)
        ,simp[]] *) >> simp[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A xx1 vv1` >>
      qmatch_assum_abbrev_tac`OPTION_TYPE A xx2 vv2` >>
      Q.ISPECL_THEN[`A`,`xx1`,`vv1`,`xx2`,`vv2`]mp_tac OPTION_TYPE_11 >>
      discharge_hyps >> simp[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A xx1 vv1` >>
      qmatch_assum_abbrev_tac`AST_ID_TYPE A xx2 vv2` >>
      Q.ISPECL_THEN[`A`,`xx1`,`vv1`,`xx2`,`vv2`]mp_tac AST_ID_TYPE_11 >>
      discharge_hyps >> simp[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_EXP_TYPE xx1 vv1` >>
      qmatch_assum_abbrev_tac`AST_EXP_TYPE xx2 vv2` >>
      METIS_TAC[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_LOP_TYPE xx1 vv1` >>
      qmatch_assum_abbrev_tac`AST_LOP_TYPE xx2 vv2` >>
      METIS_TAC[AST_LOP_TYPE_11]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_OP_TYPE xx1 vv1` >>
      qmatch_assum_abbrev_tac`AST_OP_TYPE xx2 vv2` >>
      METIS_TAC[AST_OP_TYPE_11]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_PAT_TYPE xx1 vv1` >>
      qmatch_assum_abbrev_tac`AST_PAT_TYPE xx2 vv2` >>
      METIS_TAC[AST_PAT_TYPE_11]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_UOP_TYPE xx1 vv1` >>
      qmatch_assum_abbrev_tac`AST_UOP_TYPE xx2 vv2` >>
      METIS_TAC[AST_UOP_TYPE_11]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_LIT_TYPE xx1 vv1` >>
      qmatch_assum_abbrev_tac`AST_LIT_TYPE xx2 vv2` >>
      METIS_TAC[AST_LIT_TYPE_11]
     )) >>
    unabbrev_all_tac >>
    rpt (gen_tac ORELSE (disch_then strip_assume_tac)) >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[mini_preludeTheory.PAIR_TYPE_def] >>
    TRY(
      qmatch_abbrev_tac`types_match X Y ∧ Z ∧ types_match XX YY ∧ ZZ`>>
      REWRITE_TAC[Once CONJ_ASSOC]>>conj_tac>>unabbrev_all_tac) >>
    TRY(
      qmatch_abbrev_tac`A ∧ types_match X Y ∧ B`>>
      conj_tac >> unabbrev_all_tac) >>
    TRY(metis_tac[LIST_TYPE_CHAR_11,AST_PAT_TYPE_11,SND])) >>
  TRY(METIS_TAC[]))

val GRAMMAR_SYMBOL_TYPE_11 = prove(
  ``∀a1 b1 a2 b2.
    (∀x1 x2 y1 y2. A x1 y1 ∧ A x2 y2 ⇒ types_match y1 y2 ∧ ((y1 = y2) ⇔ (x1 = x2))) ∧
    (∀x1 x2 y1 y2. B x1 y1 ∧ B x2 y2 ⇒ types_match y1 y2 ∧ ((y1 = y2) ⇔ (x1 = x2))) ∧
    GRAMMAR_SYMBOL_TYPE A B a1 b1 ∧
    GRAMMAR_SYMBOL_TYPE A B a2 b2
    ⇒
    types_match b1 b2 ∧ ((b1 = b2) ⇔ (a1 = a2))``,
  Cases >> simp[ml_repl_stepTheory.GRAMMAR_SYMBOL_TYPE_def,PULL_EXISTS
               ,types_match_Conv,types_match_list_1] >>
  Cases >> simp[ml_repl_stepTheory.GRAMMAR_SYMBOL_TYPE_def,PULL_EXISTS
               ,types_match_Conv,types_match_list_1] >>
  rw[] >> TRY(METIS_TAC[])>>
  qmatch_assum_rename_tac`SUM_TYPE B NUM aa bb`[]>>
  qpat_assum`SUM_TYPE B NUM aa bb`mp_tac >>
  qmatch_assum_rename_tac`SUM_TYPE B NUM cc dd`[]>>
  strip_tac >>
  Cases_on`aa`>>Cases_on`cc`>>fs[std_preludeTheory.SUM_TYPE_def,NUM_def,INT_def] >>
  simp[types_match_Conv,types_match_list_1] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[types_match_def] >> METIS_TAC[])

val GRAMMAR_PARSETREE_TYPE_11 = prove(
  ``∀A B a1 b1 a2 b2.
      (∀x1 x2 y1 y2. A x1 y1 ∧ A x2 y2 ⇒ types_match y1 y2 ∧ ((y1 = y2) ⇔ (x1 = x2))) ∧
      (∀x1 x2 y1 y2. B x1 y1 ∧ B x2 y2 ⇒ types_match y1 y2 ∧ ((y1 = y2) ⇔ (x1 = x2))) ∧
      GRAMMAR_PARSETREE_TYPE A B a1 b1 ∧
      GRAMMAR_PARSETREE_TYPE A B a2 b2
      ⇒
      types_match b1 b2 ∧ ((b1 = b2) ⇔ (a1 = a2))``,
  HO_MATCH_MP_TAC ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_ind >>
  simp[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def,PULL_EXISTS,types_match_Conv
      ,types_match_list_1,types_match_list_2] >>
  rpt conj_tac >>
  rpt gen_tac >> STRIP_TAC >> Cases_on`a2` >>
  fs[ml_repl_stepTheory.GRAMMAR_PARSETREE_TYPE_def
    ,std_preludeTheory.SUM_TYPE_def,NUM_def,INT_def
    ,ml_repl_stepTheory.GRAMMAR_SYMBOL_TYPE_def] >>
  rpt gen_tac >> rpt (disch_then STRIP_ASSUME_TAC) >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  TRY (
    qmatch_assum_rename_tac`SUM_TYPE B NUM aa bb`[]>>
    qpat_assum`SUM_TYPE B NUM aa bb`mp_tac >>
    qmatch_assum_rename_tac`SUM_TYPE B NUM cc dd`[]>>
    strip_tac >>
    Cases_on`aa`>>Cases_on`cc`>>fs[std_preludeTheory.SUM_TYPE_def,NUM_def,INT_def] >>
    simp[types_match_Conv,types_match_list_1] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`LIST_TYPE D aa bb`["D"]>>
    qpat_assum`LIST_TYPE D aa bb`mp_tac>>
    qmatch_assum_rename_tac`LIST_TYPE D cc dd`["D"]>>
    strip_tac >>
    Q.ISPECL_THEN[`GRAMMAR_PARSETREE_TYPE A B`,`cc`,`dd`,`aa`,`bb`]mp_tac LIST_TYPE_11 >>
    discharge_hyps >- ( res_tac >> METIS_TAC[] ) >>
    simp[types_match_def] >> METIS_TAC[]) >>
  MATCH_MP_TAC GRAMMAR_SYMBOL_TYPE_11 >>
  METIS_TAC[])

val TOKENS_TOKEN_TYPE_11 = prove(
  ``∀x1 y1 x2 y2. TOKENS_TOKEN_TYPE x1 y1 ∧ TOKENS_TOKEN_TYPE x2 y2 ⇒
                  types_match y1 y2 ∧ ((y1 = y2) ⇔ (x1 = x2)) ``,
  Cases >> simp[ml_repl_stepTheory.TOKENS_TOKEN_TYPE_def,types_match_Conv,types_match_list_1,PULL_EXISTS,NUM_def,INT_def] >>
  Cases >> simp[ml_repl_stepTheory.TOKENS_TOKEN_TYPE_def,types_match_Conv,types_match_list_1,PULL_EXISTS,NUM_def,INT_def] >>
  simp[types_match_list_2,types_match_def] >>
  METIS_TAC[LIST_TYPE_CHAR_11])

val GRAM_MMLNONT_TYPE_11 = prove(
  ``∀x1 y1 x2 y2. GRAM_MMLNONT_TYPE x1 y1 ∧ GRAM_MMLNONT_TYPE x2 y2 ⇒
                  types_match y1 y2 ∧ ((y1 = y2) ⇔ (x1 = x2)) ``,
  HO_MATCH_MP_TAC(TypeBase.induction_of``:MMLnonT``)>>
  simp[ml_repl_stepTheory.GRAM_MMLNONT_TYPE_def,types_match_Conv,PULL_EXISTS] >>
  rpt conj_tac >>
  HO_MATCH_MP_TAC(TypeBase.induction_of``:MMLnonT``)>>
  simp[ml_repl_stepTheory.GRAM_MMLNONT_TYPE_def,types_match_Conv,PULL_EXISTS])

(* Equality Types -- should be in improved automation... *)

val v_ind =
  (TypeBase.induction_of``:v``)
  |> Q.SPECL[`P`,`EVERY (P o SND)`,`P o SND`,`EVERY P`]
  |> SIMP_RULE (srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

val equality_types = prove(
  ``EqualityType AST_T_TYPE ∧
    EqualityType AST_PAT_TYPE ∧
    EqualityType (GRAMMAR_PARSETREE_TYPE TOKENS_TOKEN_TYPE GRAM_MMLNONT_TYPE) ∧
    EqualityType AST_EXP_TYPE``,
  conj_tac >- METIS_TAC[EqualityType_thm,AST_T_TYPE_no_closures,AST_T_TYPE_11] >>
  conj_tac >- METIS_TAC[EqualityType_thm,AST_PAT_TYPE_no_closures,AST_PAT_TYPE_11] >>
  conj_tac >- (
    simp[EqualityType_thm] >>
    conj_tac >- (
      METIS_TAC[GRAMMAR_PARSETREE_TYPE_no_closures,TOKENS_TOKEN_TYPE_no_closures,GRAM_MMLNONT_TYPE_no_closures] ) >>
    rpt gen_tac >> strip_tac >>
    MATCH_MP_TAC (MP_CANON (Q.ISPECL[`TOKENS_TOKEN_TYPE`,`GRAM_MMLNONT_TYPE`]GRAMMAR_PARSETREE_TYPE_11)) >>
    METIS_TAC[TOKENS_TOKEN_TYPE_11,GRAM_MMLNONT_TYPE_11] ) >>
  METIS_TAC[EqualityType_thm,AST_EXP_TYPE_no_closures,AST_EXP_TYPE_11])

(* --- Decl for repl_decs --- *)

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
  \\ SIMP_TAC std_ss [equality_types])

val Decls_ml_repl_step_decls =
  new_specification("Decls_ml_repl_step_decls",
    ["ml_repl_step_decls_env","ml_repl_step_decls_s","ml_repl_step_decls_cenv"],
    DeclAssumExists_ml_repl_step_decls
    |> SIMP_RULE std_ss [DeclAssumExists_def,DeclAssum_def])

val Decls_11 = prove(
  ``Decls mn menv cenv1 s1 env1 ds1 cenv2 s2 env2 ==>
    (Decls mn menv cenv1 s1 env1 ds1 cenv2' s2' env2' <=>
     ((cenv2',s2',env2') = (cenv2,s2,env2)))``,
  cheat);

val Decls_repl_decs_lemma = let
  val i = fst (match_term ``Decls mn menv cenv1 s1 env1 ds1 cenv2 s2 env2``
                 (concl Decls_ml_repl_step_decls))
  val ds2 = repl_decs_def |> concl |> rand |> rand
  val th = Decls_APPEND |> SPEC_ALL |> INST i |> Q.INST [`ds2`|->`^ds2`]
  val th = th |> SIMP_RULE std_ss [MATCH_MP Decls_11 Decls_ml_repl_step_decls]
  val sem_rw =
    SIMP_RULE (srw_ss()) [Once altBigStepTheory.evaluate_decs'_cases,PULL_EXISTS,
                          Once altBigStepTheory.evaluate_dec'_cases,PULL_EXISTS,
                          Once altBigStepTheory.evaluate'_cases,PULL_EXISTS,
                          do_uapp_def,store_alloc_def,LET_DEF,terminationTheory.pmatch'_def,
                          astTheory.pat_bindings_def,combine_dec_result_def,
                          libTheory.merge_def,libTheory.emp_def,libTheory.bind_def]
  fun n_times 0 f x = x
    | n_times n f x = n_times (n-1) f (f x)
  val th = th |> GSYM |> SIMP_RULE std_ss [Once Decls_def,GSYM repl_decs_def]
              |> n_times 10 sem_rw
              |> MATCH_MP (METIS_PROVE [] ``(b <=> c) ==> (b ==> c)``)
              |> GEN_ALL |> SIMP_RULE std_ss []
  in th end;

val repl_decs_env_def = Define `
  repl_decs_env = ^(Decls_repl_decs_lemma |> concl |> rand)`;

val repl_decs_s_def = Define `
  repl_decs_s = ^(Decls_repl_decs_lemma |> concl |> rator |> rand)`;

val repl_decs_cenv_def = Define `
  repl_decs_cenv = ^(Decls_repl_decs_lemma |> concl |> rator |> rator |> rand)`;

val Decls_repl_decs = prove(
  ``Decls NONE [] init_envC empty_store [] repl_decs repl_decs_cenv
     repl_decs_s repl_decs_env``,
  FULL_SIMP_TAC std_ss [Decls_repl_decs_lemma,repl_decs_cenv_def,
    repl_decs_s_def, repl_decs_env_def]);

val DeclAssum_repl_decs = prove(
  ``DeclAssum repl_decs repl_decs_env``,
  METIS_TAC [Decls_repl_decs,DeclAssum_def]);

val DeclAssumExists_repl_decs = prove(
  ``DeclAssumExists repl_decs``,
  METIS_TAC [DeclAssumExists_def,DeclAssum_repl_decs]);


(* --- DeclC for repl_decs --- *)

val check_ctors_decs_ml_repl_step_decls = prove(
  ``check_ctors_decs NONE init_envC ml_repl_step_decls``,
  MP_TAC ml_repl_stepTheory.ml_repl_step_translator_state_thm
  \\ REWRITE_TAC [markerTheory.Abbrev_def,TAG_def,AND_IMP_INTRO]
  \\ STRIP_TAC);

val decs_to_cenv_ml_repl_step_decls = let
  val pat = ``decs_to_cenv NONE ml_repl_step_decls = xxx``
  in ml_repl_stepTheory.ml_repl_step_translator_state_thm
     |> REWRITE_RULE [markerTheory.Abbrev_def,TAG_def]
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

val DeclsC_ml_repl_step_decls = prove(
  ``DeclsC NONE [] init_envC empty_store [] ml_repl_step_decls
     ml_repl_step_decls_cenv ml_repl_step_decls_s ml_repl_step_decls_env``,
  METIS_TAC [DeclC_thm, check_ctors_decs_ml_repl_step_decls, Decls_ml_repl_step_decls]);

val DeclsC_repl_decs = prove(
  ``DeclsC NONE [] init_envC empty_store [] repl_decs repl_decs_cenv
     repl_decs_s repl_decs_env``,
  METIS_TAC [DeclC_thm, check_ctors_decs_repl_decs, Decls_repl_decs]);

val DeclAssumC_repl_decs = prove(
  ``DeclAssumC repl_decs repl_decs_cenv repl_decs_env``,
  METIS_TAC [DeclsC_repl_decs,DeclAssumC_def]);


(* --- expanding Eval repl_step --- *)

val Eval_repl_step1 =
  ml_repl_stepTheory.ml_repl_step_translator_state_thm
  |> CONV_RULE (REWR_CONV TAG_def)
  |> CONV_RULE (REWR_CONV markerTheory.Abbrev_def) |> CONJUNCT2 |> CONJUNCT1
  |> CONV_RULE (REWR_CONV markerTheory.Abbrev_def) |> CONJUNCT2 |> CONJUNCT1
  |> CONV_RULE (REWR_CONV markerTheory.Abbrev_def) |> CONJUNCT2 |> CONJUNCT1
  |> CONV_RULE (REWR_CONV markerTheory.Abbrev_def) |> CONJUNCT2 |> CONJUNCT2
  |> CONJUNCT2 |> CONJUNCT1
  |> RW[sideTheory.repl_step_side_thm,PRECONDITION_def,equality_types]
  |> CONV_RULE (REWR_CONV markerTheory.Abbrev_def)

val INPUT_TYPE_def = Define `
  INPUT_TYPE =
  ^(find_term (can (match_term ``OPTION_TYPE xx``)) (concl Eval_repl_step1))`;

val OUTPUT_TYPE_def = Define `
  OUTPUT_TYPE =
  ^(find_term (can (match_term ``SUM_TYPE xx yy``)) (concl Eval_repl_step1))`;

val Eval_repl_step =
  Eval_repl_step1
  |> RW [GSYM INPUT_TYPE_def,GSYM OUTPUT_TYPE_def]
  |> SPEC_ALL |> UNDISCH
  |> GENL (free_vars (concl Eval_repl_step1))
  |> HO_MATCH_MP Eval_FUN_FORALL
  |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
  |> DISCH_ALL |> GEN_ALL
  |> SIMP_RULE std_ss [DeclAssum_def,PULL_EXISTS]
  |> SPEC_ALL
  |> (fn th => MATCH_MP th (Decls_ml_repl_step_decls))

val repl_step_do_app =
  Eval_repl_step
  |> SIMP_RULE std_ss [Eval_def,Arrow_def,AppReturns_def,
       evaluate_closure_def,PULL_EXISTS,GSYM CONJ_ASSOC]
  |> SIMP_RULE (srw_ss()) [Once altBigStepTheory.evaluate'_cases,PULL_EXISTS]


(* --- instantiation of compiler correctness --- *)

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

val evaluate_decs_repl_decs = DeclsC_repl_decs |> RW [DeclsC_def]

val repl_decs_cenv_env_s_def = evaluate_decs_repl_decs

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
  |> SIMP_RULE (srw_ss())[repl_decs_def,astTheory.pat_bindings_def]

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
    simp[Once bigStepTheory.evaluate_decs_cases] >>
    simp[Once bigStepTheory.evaluate_decs_cases] >>
    simp[Once bigStepTheory.evaluate_decs_cases] >>
    simp[libTheory.emp_def,libTheory.merge_def,semanticPrimitivesTheory.combine_dec_result_def]) >>
  simp[Once bigStepTheory.evaluate_decs_cases] >>
  rw[] >- (
    Cases_on`d1`>>fs[] >- (
      pop_assum mp_tac >>
      simp[Once bigStepTheory.evaluate_decs_cases] >>
      rw[] >>
      simp_tac(srw_ss())[Once bigStepTheory.evaluate_decs_cases] >>
      simp[libTheory.emp_def,libTheory.merge_def] >>
      simp[semanticPrimitivesTheory.combine_dec_result_def] >>
      qexists_tac`Rerr e`>>simp[] ) >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[Once bigStepTheory.evaluate_decs_cases] >>
    rw[] >>
    imp_res_tac determTheory.dec_determ >>
    fs[] ) >>
  Cases_on`d1`>>fs[] >- (
    pop_assum mp_tac >>
    simp[Once bigStepTheory.evaluate_decs_cases] >>
    rw[] >>
    simp_tac(srw_ss())[Once bigStepTheory.evaluate_decs_cases] >>
    simp[libTheory.emp_def,libTheory.merge_def] >>
    fs[libTheory.merge_def] >>
    qexists_tac`combine_dec_result new_env r` >>
    conj_tac >- METIS_TAC[] >>
    simp[semanticPrimitivesTheory.combine_dec_result_def] >>
    Cases_on`r`>>simp[libTheory.merge_def]) >>
  pop_assum mp_tac >>
  simp_tac(srw_ss())[Once bigStepTheory.evaluate_decs_cases] >>
  rw[] >>
  fs[libTheory.merge_def] >>
  imp_res_tac determTheory.dec_determ >>
  fs[] >> rw[] >>
  first_x_assum(qspecl_then[`mn`,`menv`,`new_tds ++ cenv`,`s2`,`new_env ++ env`,`s3,new_tds',r`]mp_tac) >>
  rw[] >>
  Cases_on`r'`>>fs[semanticPrimitivesTheory.combine_dec_result_def] >>
  first_x_assum(qspecl_then[`t`,`d2`,`s0`,`new_tds''`,`a`]mp_tac) >>
  rw[] >>
  fs[libTheory.merge_def] >>
  qexists_tac`r1` >> simp[] >>
  Cases_on`r1`>>fs[])

val evaluate_decs_decs_to_cenv = store_thm("evaluate_decs_decs_to_cenv",
  ``∀mn menv cenv s env decs res.
     evaluate_decs mn menv cenv s env decs res ⇒
     ∀v. (SND(SND res ) = Rval v) ⇒
     (decs_to_cenv mn decs = (FST(SND res)))``,
   HO_MATCH_MP_TAC bigStepTheory.evaluate_decs_ind >>
   simp[libTheory.emp_def] >> rw[] >- simp[semanticPrimitivesTheory.decs_to_cenv_def] >>
   imp_res_tac compilerProofsTheory.evaluate_dec_dec_to_cenv >>
   fs[] >> simp[semanticPrimitivesTheory.decs_to_cenv_def,libTheory.merge_def] >>
   Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def])

val cenv_bind_div_eq_init_envC = store_thm("cenv_bind_div_eq_init_envC",
  ``cenv_bind_div_eq init_envC``, EVAL_TAC)

val closed_context_empty = store_thm("closed_context_empty",
  ``closed_context [] init_envC empty_store []``,
  EVAL_TAC >> rw[])

val evaluate_decs_ml_repl_step_decls = DeclsC_ml_repl_step_decls |> RW [DeclsC_def]

val merge_emp = prove(
  ``merge x emp = x``,
    simp[libTheory.emp_def,libTheory.merge_def])

val ml_repl_step_decls_cenv =
  MATCH_MP evaluate_decs_decs_to_cenv evaluate_decs_ml_repl_step_decls
  |> SIMP_RULE (srw_ss())[]
  |> SYM

val do_con_check_ml_repl_step_decls_None =
  EVAL ``do_con_check (merge ml_repl_step_decls_cenv xx) (SOME(Short"None")) 0``
  |> RIGHT_CONV_RULE(REWRITE_CONV[ml_repl_step_decls_cenv])
  |> RIGHT_CONV_RULE(REWRITE_CONV[ml_repl_stepTheory.ml_repl_step_decls,decs_to_cenv_def])
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
    |> C MATCH_MP evaluate_decs_ml_repl_step_decls
  val th =
    th |> ss [Once bigStepTheory.evaluate_decs_cases]
    |> ss [Once bigStepTheory.evaluate_dec_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [terminationTheory.pmatch_def,astTheory.pat_bindings_def]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once semanticPrimitivesTheory.do_uapp_def,LET_THM,semanticPrimitivesTheory.store_alloc_def]
  val th =
    th |> ss [do_con_check_ml_repl_step_decls_None]
    |> ss [Once bigStepTheory.evaluate_decs_cases]
    |> ss [Once bigStepTheory.evaluate_dec_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [terminationTheory.pmatch_def,astTheory.pat_bindings_def]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once semanticPrimitivesTheory.do_uapp_def,LET_THM,semanticPrimitivesTheory.store_alloc_def]
  val th =
    th |> ss [merge_emp,do_con_check_ml_repl_step_decls_None,bind_emp]
    |> ss [Once bigStepTheory.evaluate_dec_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [terminationTheory.pmatch_def,astTheory.pat_bindings_def]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [Once semanticPrimitivesTheory.do_uapp_def,LET_THM,semanticPrimitivesTheory.store_alloc_def]
  val th =
    th |> ss [Once bigStepTheory.evaluate_dec_cases]
    |> ss [Once bigStepTheory.evaluate_cases]
    |> ss [terminationTheory.pmatch_def,astTheory.pat_bindings_def]
    |> ss [Once semanticPrimitivesTheory.do_uapp_def,LET_THM,semanticPrimitivesTheory.store_alloc_def]
    |> ss [Once bigStepTheory.evaluate_decs_cases]
    |> ss [Once bigStepTheory.evaluate_dec_cases]
    |> ss [terminationTheory.pmatch_def,astTheory.pat_bindings_def]
  val th =
    th |> ss [Once bigStepTheory.evaluate_dec_cases]
    |> ss [terminationTheory.pmatch_def,astTheory.pat_bindings_def]
    |> ss [Once bigStepTheory.evaluate_decs_cases]
    |> ss [semanticPrimitivesTheory.combine_dec_result_def,libTheory.merge_def,libTheory.emp_def,libTheory.bind_def]
  in th end

val env_rs_repl_decs_inp_out = store_thm("env_rs_repl_decs_inp_out",
  ``env_rs [] (cenv ++ init_envC) (0,s)
      repl_decs_env new_compiler_state 0 rd bs' ==>
    ∃cl pout pinp wout winp out inp st.
      (bs'.stack = cl::RefPtr pout::RefPtr pinp::st) ∧
      (FLOOKUP bs'.refs pout = SOME out) ∧
      (FLOOKUP bs'.refs pinp = SOME inp) ∧
      pinp ∉ FDOM rd.cls ∧ pout ∉ FDOM rd.cls ∧
      (el_check (LENGTH ml_repl_step_decls_s+1) rd.sm = SOME pout) ∧
      (el_check (LENGTH ml_repl_step_decls_s+0) rd.sm = SOME pinp) ∧
      let mv = MAP FST o_f new_compiler_state.rmenv in
      let m = cmap new_compiler_state.contab in
      let pp = mk_pp rd bs' in
      let vout = v_to_Cv mv m (EL (LENGTH ml_repl_step_decls_s +1) s) in
      let vinp = v_to_Cv mv m (EL (LENGTH ml_repl_step_decls_s +0) s) in
      syneq vout wout ∧ syneq vinp winp ∧
      Cv_bv pp wout out ∧ Cv_bv pp winp inp``,
  simp[compilerProofsTheory.env_rs_def,LET_THM] >> strip_tac >>
  fs[toBytecodeProofsTheory.Cenv_bs_def] >>
  fs[toBytecodeProofsTheory.env_renv_def] >>
  qpat_assum`EVERY2 P X Y`mp_tac >>
  qpat_assum`EVERY2 P X Cs`mp_tac >>
  simp_tac bool_ss [miscTheory.EVERY2_MAP] >>
  simp[compilerLibTheory.el_check_def] >>
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
  qpat_assum`s_refs X Y Z`mp_tac >>
  simp[toBytecodeProofsTheory.s_refs_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  ntac 2 (pop_assum mp_tac) >>
  simp[compilerLibTheory.el_check_def] >>
  qpat_assum`LIST_REL P Cw X`kall_tac >>
  qpat_assum`syneq X Cx`kall_tac >>
  qpat_assum`LIST_REL P X Cw`kall_tac >>
  qpat_assum`Cv_bv X Cx Y`kall_tac >>
  rpt strip_tac >>
  simp[finite_mapTheory.FLOOKUP_DEF] >>
  fs[listTheory.EVERY_MEM] >>
  simp[Once CONJ_ASSOC] >>
  `LENGTH ml_repl_step_decls_s < LENGTH Cs` by simp[] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    conj_tac >>
    first_x_assum MATCH_MP_TAC >>
    simp[listTheory.MEM_EL] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    PROVE_TAC[] ) >>
  simp[Once CONJ_ASSOC] >>
  conj_tac >- (
    fs[toBytecodeProofsTheory.good_rd_def,miscTheory.FEVERY_ALL_FLOOKUP] >>
    fs[finite_mapTheory.FLOOKUP_DEF,UNCURRY] >>
    METIS_TAC[listTheory.MEM_EL] ) >>
  fs[listTheory.EVERY2_EVERY,listTheory.EVERY_MEM,pairTheory.FORALL_PROD] >>
  qexists_tac`EL(LENGTH ml_repl_step_decls_s+1)Cs` >>
  conj_tac >- (
    first_x_assum MATCH_MP_TAC >>
    simp[listTheory.MEM_ZIP] >>
    PROVE_TAC[] ) >>
  qexists_tac`EL(LENGTH ml_repl_step_decls_s+0)Cs` >>
  conj_tac >- (
    first_x_assum MATCH_MP_TAC >>
    simp[listTheory.MEM_ZIP] >>
    PROVE_TAC[] ) >>
  conj_tac >> FIRST_X_ASSUM MATCH_MP_TAC >>
  simp[listTheory.MEM_ZIP] >|[
    qexists_tac`LENGTH ml_repl_step_decls_s+1`,
    qexists_tac`LENGTH ml_repl_step_decls_s+0`] >>
  simp[listTheory.EL_MAP])

val IMP_IMP = prove(
  ``!b c d.b /\ (c ==> d) ==> ((b ==> c) ==> d)``,
  METIS_TAC []);

val bc_eval_bootstrap_lcode = store_thm("bc_eval_bootstrap_lcode",
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
  \\ MATCH_MP_TAC IMP_IMP
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

val compile_call_term_def = Define [QUOTE "compile_call_term = ",
  ANTIQUOTE(
  call_repl_step_dec_compiled
  |> SIMP_RULE (std_ss) [LET_THM]
  |> concl |> lhs)]

val compile_call_term_thm =
  call_repl_step_dec_compiled
  |> SIMP_RULE std_ss [GSYM compileCallReplStepDecTheory.call_lcode_def,
       LET_DEF,GSYM compile_call_term_def]

val new_decs_vs_ml_repl_step_decls =
  ``new_decs_vs ml_repl_step_decls``
  |> REWRITE_CONV [ml_repl_stepTheory.ml_repl_step_decls]
  |> RIGHT_CONV_RULE EVAL
  |> RIGHT_CONV_RULE (SIMP_CONV std_ss [astTheory.pat_bindings_def])
  |> RIGHT_CONV_RULE EVAL

val FST_SND_SND_compile_repl_decs =
  ``FST (SND (SND compile_repl_decs))``
  |> REWRITE_CONV[compileReplDecsTheory.compile_repl_decs_def]
  |> RW[compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL]

val FST_SND_SND_SND_compile_repl_decs =
  ``FST (SND (SND (SND compile_repl_decs)))``
  |> REWRITE_CONV[compileReplDecsTheory.compile_repl_decs_def]
  |> RW[compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL]

val SND_SND_SND_SND_compile_repl_decs =
  ``SND (SND (SND (SND compile_repl_decs)))``
  |> REWRITE_CONV[compileReplDecsTheory.compile_repl_decs_def]
  |> RW[compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL]

val new_compiler_state_contab =
  SIMP_CONV (srw_ss()) [new_compiler_state_def] ``new_compiler_state.contab``
  |> RW [compile_term_def,compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL,LET_THM]
  |> CONV_RULE (DEPTH_CONV (PairRules.PBETA_CONV))
  |> RW [SND]

val new_compiler_state_rnext_label =
  SIMP_CONV (srw_ss()) [new_compiler_state_def] ``new_compiler_state.rnext_label``
  |> RW [compile_term_def,compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL,LET_THM]
  |> CONV_RULE (DEPTH_CONV (PairRules.PBETA_CONV))
  |> RW [SND]
  |> RW [SIMP_CONV (srw_ss()) [] ``<|out := X; next_label := Y|>.next_label``]

val new_compiler_state_rmenv =
  SIMP_CONV (srw_ss()) [new_compiler_state_def] ``new_compiler_state.rmenv``
  |> RW [compile_term_def,compileReplDecsTheory.repl_decs_compiled,repl_computeTheory.compile_decs_FOLDL,LET_THM]
  |> RW [compilerTheory.init_compiler_state_def]
  |> SIMP_RULE (srw_ss())[]

val compile_term_next_label = prove(
  ``(SND (SND (SND compile_term))).next_label = new_compiler_state.rnext_label``,
  SIMP_TAC std_ss [compile_term_def]
  \\ REWRITE_TAC [compileReplDecsTheory.repl_decs_compiled,
       repl_computeTheory.compile_decs_FOLDL,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ REWRITE_TAC [SND,FST,``<|out := code; next_label := n |>.next_label``
                          |> SIMP_CONV (srw_ss()) []]
  \\ REWRITE_TAC [new_compiler_state_rnext_label]);

val FST_SND_SND_compile_repl_decs_new_compiler_state_renv = prove(
  ``FST(SND(SND compile_repl_decs)) = MAP (CTDec o SND) new_compiler_state.renv``,
  REWRITE_TAC[FST_SND_SND_compile_repl_decs,new_compiler_state_renv] >>
  EVAL_TAC)

val compile_call_new_compiler_state = prove(
  ``compile FEMPTY
        (MAP (CTDec o SND) new_compiler_state.renv)
        TCNonTail
        new_compiler_state.rsz
        <|out := []; next_label := new_compiler_state.rnext_label|>
        (CCall T (CVar (Short 0)) [CLit Unit])
    = compile_call_term``,
  simp[compile_call_term_def] >>
  AP_THM_TAC >>
  simp[FST_SND_SND_compile_repl_decs_new_compiler_state_renv] >>
  simp[new_compiler_state_rsz] >>
  simp[FST_SND_SND_SND_compile_repl_decs] >>
  AP_TERM_TAC >>
  simp[new_compiler_state_rnext_label] >>
  CONV_TAC(RAND_CONV(RAND_CONV(REWR_CONV SND_SND_SND_SND_compile_repl_decs))) >>
  CONV_TAC(RAND_CONV(REWR_CONV(SIMP_CONV (srw_ss()) [] ``<|out := X; next_label := Y|>.next_label``))) >>
  rw[])

val closed_context_repl_decs = save_thm("closed_context_repl_decs",
  repl_decs_cenv_env_s_def
  |> MATCH_MP semanticsExtraTheory.evaluate_decs_closed_context
  |> SIMP_RULE (srw_ss())[LET_THM,repl_decs_lemma,cenv_bind_div_eq_init_envC,closed_context_empty])

val cenv_bind_div_eq_ml_repl_step_decls_cenv_init_envC = prove(
  ``cenv_bind_div_eq (repl_decs_cenv ++ init_envC)``,
  match_mp_tac (semanticsExtraTheory.cenv_bind_div_eq_append) >>
  simp[cenv_bind_div_eq_init_envC] >>
  simp[ml_repl_step_decls_cenv,repl_decs_cenv_def] >>
  simp[initialEnvTheory.init_envC_def] >>
  REWRITE_TAC[decs_to_cenv_ml_repl_step_decls] >>
  EVAL_TAC)

val good_labels_new_compiler_state_bootstrap_lcode = prove(
  ``good_labels new_compiler_state.rnext_label (REVERSE bootstrap_lcode)``,
  qspec_then`<|code:=REVERSE bootstrap_lcode;pc:=0;stack:=[];clock:=NONE|>`mp_tac compile_decs_bc_eval >>
  simp[compile_term_out_EQ_bootstrap_lcode] >>
  strip_tac >>
  fs[compile_term_next_label])

val code_start_def = Define `
  code_start bs = next_addr bs.inst_length (REVERSE bootstrap_lcode)`;

val code_end_def = Define `
  code_end bs = next_addr bs.inst_length
        (REVERSE bootstrap_lcode ++ REVERSE call_lcode ++
         [Stack Pop])`;

val find_index_call_repl_step =
  ``find_index "call_repl_step" (MAP FST repl_decs_env) 0``
  |> (SIMP_CONV std_ss [repl_decs_env_front] THENC EVAL)

val good_labels_all_code = prove(
  ``good_labels new_compiler_state.rnext_label (REVERSE bootstrap_lcode ++ REVERSE call_lcode ++ [Stack Pop])``,
  ASSUME_TAC good_labels_new_compiler_state_bootstrap_lcode >>
  fs[compilerProofsTheory.good_labels_def,rich_listTheory.FILTER_APPEND,ALL_DISTINCT_APPEND] >>
  simp[call_lcode_def])

val compile_call_bc_eval = let
  val th =
    compile_call_repl_step_thm
      |> Q.SPECL [`NONE`,`repl_decs_cenv++init_envC`,`ck`,`ml_repl_step_decls_s++[out;inp]`,`repl_decs_env`
                 ,`ml_repl_step_decls_s++[out';inp']`,`"call_repl_step"`,`0`,`compile_call_term`,`new_compiler_state`]
      |> RW[compile_call_new_compiler_state,compile_call_term_thm,find_index_call_repl_step]
   val evaluate_dec_th =
     th |> SPEC_ALL |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO] |> UNDISCH |> hyp |> hd |> ASSUME
   val ccth =
     semanticsExtraTheory.evaluate_dec_closed_context
     |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
     |> C MATCH_MP evaluate_dec_th
     |> SIMP_RULE (srw_ss()) [GSYM listTheory.MAP_MAP_o
                             ,Once listTheory.MEM_MAP,MEM_call_repl_step
                             ,LET_THM]
     |> UNDISCH
     |> RW[cenv_bind_div_eq_ml_repl_step_decls_cenv_init_envC]
   val th1 =
     th |> SPEC_ALL |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
     |> UNDISCH_ALL
     |> CONJ ccth
     |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_AND_THM]
     |> (fn th => DISCH (first (equal "good_labels" o fst o dest_const o fst o strip_comb) (hyp th)) th)
     |> Q.INST[`bc0`|->`REVERSE bootstrap_lcode`]
     |> (fn th => DISCH (first (can (match_term ``bs.code = X``)) (hyp th)) th)
     |> SIMP_RULE std_ss [good_labels_all_code,(SIMP_CONV (srw_ss()) [] ``<|out := X; next_label := Y|>.out``)]
     |> DISCH_ALL
     |> SIMP_RULE std_ss [AND_IMP_INTRO]
     |> Q.INST [`ck`|->`0`,`csz`|->`0`]
     |> RW [GSYM code_start_def, GSYM code_end_def]
  in th1 end

val call_repl_step_dec_def = Define`
  call_repl_step_dec = Dlet (Plit Unit) (App Opapp (Var (Short "call_repl_step")) (Lit Unit))`

val COMPILER_RUN_INV_STEP = prove(
  ``COMPILER_RUN_INV bs1 out1 inp1 /\
    evaluate_dec NONE [] (repl_decs_cenv ++ init_envC)
      (ml_repl_step_decls_s ++ [out1; inp1]) repl_decs_env
      call_repl_step_dec
      (ml_repl_step_decls_s ++ [out2; inp2],Rval ([],[])) ==>
    ?bs2.
      (bc_eval (bs1 with pc := code_start bs1) = SOME bs2) /\
      COMPILER_RUN_INV bs2 out2 inp2 /\ (bs2.pc = code_end bs1)``,
  SIMP_TAC std_ss [COMPILER_RUN_INV_def] \\ STRIP_TAC
  \\ MP_TAC (compile_call_bc_eval
       |> Q.INST [`bs`|->`bs1 with pc := code_start bs1`,
                  `inp`|->`inp1`,`inp'`|->`inp2`,
                  `out`|->`out1`,`out'`|->`out2`])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [code_start_def,code_end_def,PULL_EXISTS,GSYM call_repl_step_dec_def]
  \\ POP_ASSUM MP_TAC
  \\ miscLib.discharge_hyps THEN1 (
       ASM_SIMP_TAC std_ss [] THEN
       MATCH_MP_TAC compilerProofsTheory.env_rs_with_bs_irr THEN
       HINT_EXISTS_TAC THEN
       ASM_SIMP_TAC (srw_ss())[])
  \\ STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`bs'`,`rd'`]
  \\ IMP_RES_TAC bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next
  \\ IMP_RES_TAC bytecodeExtraTheory.RTC_bc_next_preserves
  \\ IMP_RES_TAC bytecodeExtraTheory.RTC_bc_next_clock_less
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [optionTheory.OPTREL_def]
  \\ FULL_SIMP_TAC (srw_ss()) []);


(* --- connecting the Eval theorem with compiler correctness --- *)


(* instances of Block *)

fun tag_for str = let
  val cnmap =
    compileReplDecsTheory.repl_decs_compiled
    |> concl |> rand |> rand |> rator |> rand |> rand
  val tm = stringSyntax.fromMLstring str
  val pat = ``(SOME (Short ^tm),n:num)``
  val raw = find_term (can (match_term pat)) cnmap |> rand
  in ``^raw + block_tag`` |> EVAL |> concl |> rand end

val nil_tag_def  = Define `nil_tag  = ^(tag_for "nil")`;
val cons_tag_def = Define `cons_tag = ^(tag_for "::")`;
val pair_tag_def = Define `pair_tag = ^(tag_for "Pair")`;

val BlockNil_def  = Define `BlockNil = Block nil_tag []`;
val BlockCons_def = Define `BlockCons (x,y) = Block cons_tag [x;y]`;
val BlockPair_def = Define `BlockPair (x,y) = Block pair_tag [x;y]`;

val BlockList_def = Define `
  (BlockList [] = BlockNil) /\
  (BlockList (x::xs) = BlockCons(x,BlockList xs))`;

val BlockBool_def = Define `BlockBool b = Block (bool_to_tag b) []`;
val BlockSome_def = Define `BlockSome x = Block ^(tag_for "Some") [x]`;

val BlockInl_def = Define `BlockInl x = Block ^(tag_for "Inl") [x]`;
val BlockInr_def = Define `BlockInr x = Block ^(tag_for "Inr") [x]`;

val errors_tag_def  = Define `errors_tag = ^(tag_for "Errors")`;
val others_tag_def  = Define `others_tag = ^(tag_for "Others")`;
val longs_tag_def   = Define `longs_tag = ^(tag_for "Longs")`;
val numbers_tag_def = Define `numbers_tag = ^(tag_for "Numbers")`;
val strings_tag_def = Define `strings_tag = ^(tag_for "Strings")`;

val BlockOtherS_def  = Define `BlockOtherS x  = Block others_tag [x]`;
val BlockLongS_def   = Define `BlockLongS x   = Block longs_tag [x]`;
val BlockNumberS_def = Define `BlockNumberS x = Block numbers_tag [x]`;
val BlockStringS_def = Define `BlockStringS x = Block strings_tag [x]`;
val BlockErrorS_def  = Define `BlockErrorS    = Block errors_tag []`;

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


(* theorems used by x86-64 proofs *)

val LIST_TYPE_CHAR_BlockList = prove(
  ``(FLOOKUP cm (SOME (Short "nil")) = SOME (nil_tag - block_tag)) ∧
    (FLOOKUP cm (SOME (Short "::")) = SOME (cons_tag - block_tag))
  ⇒
    ∀s l v b.
      LIST_TYPE CHAR s l ∧ syneq (v_to_Cv m cm l) v ∧ Cv_bv pp v b
    ⇒ (b = BlockList (MAP Chr s))``,
  strip_tac >>
  simp[GSYM AND_IMP_INTRO] >>
  Induct >> simp[mini_preludeTheory.LIST_TYPE_def] >- (
    simp[Once compilerTerminationTheory.v_to_Cv_def] >>
    simp[Once intLangTheory.syneq_cases,PULL_EXISTS] >>
    simp[Once toBytecodeProofsTheory.Cv_bv_cases,PULL_EXISTS,nil_tag_def] >>
    simp[compilerTerminationTheory.v_to_Cv_def,BlockList_def,BlockNil_def,nil_tag_def] ) >>
  simp[PULL_EXISTS] >>
  simp[compilerTerminationTheory.v_to_Cv_def] >>
  simp[Once intLangTheory.syneq_cases,PULL_EXISTS] >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases,PULL_EXISTS,cons_tag_def] >>
  simp[BlockList_def,BlockCons_def,cons_tag_def] >>
  simp[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[compilerTerminationTheory.v_to_Cv_def,PULL_FORALL] >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  simp[Chr_def] >> metis_tac[])

val LIST_TYPE_Num3_Blocklist = prove(
  ``(FLOOKUP cm (SOME (Short "nil")) = SOME (nil_tag - block_tag)) ∧
    (FLOOKUP cm (SOME (Short "::")) = SOME (cons_tag - block_tag)) ∧
    (FLOOKUP cm (SOME (Short "Pair")) = SOME (pair_tag - block_tag))
  ⇒
    ∀s l v b.
      LIST_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM NUM)) s l ∧ syneq (v_to_Cv m cm l) v ∧ Cv_bv pp v b
    ⇒ (b = BlockList (MAP BlockNum3 s))``,
  strip_tac >>
  simp[GSYM AND_IMP_INTRO] >>
  Induct >> simp[mini_preludeTheory.LIST_TYPE_def] >- (
    simp[Once compilerTerminationTheory.v_to_Cv_def] >>
    simp[Once intLangTheory.syneq_cases,PULL_EXISTS] >>
    simp[Once toBytecodeProofsTheory.Cv_bv_cases,PULL_EXISTS,nil_tag_def] >>
    simp[compilerTerminationTheory.v_to_Cv_def,BlockList_def,BlockNil_def,nil_tag_def] ) >>
  simp[PULL_EXISTS] >>
  simp[compilerTerminationTheory.v_to_Cv_def] >>
  simp[Once intLangTheory.syneq_cases,PULL_EXISTS] >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases,PULL_EXISTS,cons_tag_def] >>
  simp[BlockList_def,BlockCons_def,cons_tag_def] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[compilerTerminationTheory.v_to_Cv_def,PULL_FORALL] >>
  simp[Once intLangTheory.syneq_cases,PULL_EXISTS] >>
  simp[Once intLangTheory.syneq_cases,PULL_EXISTS] >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  rpt gen_tac >> simp[GSYM AND_IMP_INTRO] >> strip_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >>
  strip_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases,PULL_EXISTS] >>
  rpt gen_tac >> simp[GSYM AND_IMP_INTRO] >> strip_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >> strip_tac >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[BlockNum3_def,BlockPair_def,pair_tag_def] >>
  metis_tac[])

val LIST_TYPE_exists = prove(
  ``∀x. (∀a. MEM a x ⇒ ∃v. A a v) ⇒ ∃l. LIST_TYPE A x l``,
  Induct >>
  simp[mini_preludeTheory.LIST_TYPE_def] >>
  METIS_TAC[])

val OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR = prove(
  ``∃v. OPTION_TYPE (AST_ID_TYPE (LIST_TYPE CHAR)) p v``,
  Cases_on`p` >> simp[std_preludeTheory.OPTION_TYPE_def] >>
  Cases_on`x`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def] >>
  rw[GSYM PULL_EXISTS] >>
  MATCH_MP_TAC LIST_TYPE_exists >>
  simp[std_preludeTheory.CHAR_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )

val STATE_TYPE_def = Define`
  STATE_TYPE = ^(INPUT_TYPE_def |> concl |> rhs |> rand |> rand)`

val SUBSTATE_TYPE_def = Define`
  SUBSTATE_TYPE = ^(STATE_TYPE_def |> concl |> rhs |> rand)`

val SUBSTATE_TYPE_no_closures = prove(
  ``SUBSTATE_TYPE x y ⇒ no_closures y``,
  simp[SUBSTATE_TYPE_def] >>
  PairCases_on`x` >>
  simp[mini_preludeTheory.PAIR_TYPE_def] >>
  simp[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[terminationTheory.contains_closure_def] >>
  fs[std_preludeTheory.FMAP_TYPE_def] >>
  rpt conj_tac >>
  rpt (
    qmatch_abbrev_tac`no_closures x` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_no_closures >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`LEXER_FUN_SYMBOL_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LEXER_FUN_SYMBOL_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`REPL_FUN_REPL_FUN_STATE_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) REPL_FUN_REPL_FUN_STATE_TYPE_no_closures >>
      qexists_tac`ll` >> rw[]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val STATE_TYPE_no_closures = prove(
  ``STATE_TYPE x y ⇒ no_closures y``,
  simp[STATE_TYPE_def,GSYM SUBSTATE_TYPE_def] >>
  Cases_on`x` >>
  simp[mini_preludeTheory.PAIR_TYPE_def] >>
  simp[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  strip_tac >>
  imp_res_tac SUBSTATE_TYPE_no_closures >>
  rw[])

val INPUT_TYPE_no_closures = prove(
  ``INPUT_TYPE x y ⇒ no_closures y``,
  simp[INPUT_TYPE_def,GSYM STATE_TYPE_def] >>
  Cases_on`x` >>
  simp[std_preludeTheory.OPTION_TYPE_def] >>
  rw[] >>
  simp[terminationTheory.contains_closure_def] >>
  qmatch_assum_rename_tac `PAIR_TYPE X Y s p`["X","Y"] >>
  Cases_on`s` >>
  fs[mini_preludeTheory.PAIR_TYPE_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  imp_res_tac STATE_TYPE_no_closures >> simp[] >>
  qmatch_abbrev_tac`no_closures x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_no_closures >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  Q.ISPEC_THEN`a`(match_mp_tac o MP_CANON o GEN_ALL) LEXER_FUN_SYMBOL_TYPE_no_closures >>
  METIS_TAC[])


val COMPILER_COMPILER_STATE_TYPE_exists = prove(
  ``∀s. ∃v. COMPILER_COMPILER_STATE_TYPE s v``,
  Cases >> PairCases_on`p` >>
  simp[ml_repl_stepTheory.COMPILER_COMPILER_STATE_TYPE_def] >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[std_preludeTheory.FMAP_TYPE_def,PULL_EXISTS,std_preludeTheory.FMAP_EQ_ALIST_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  qexists_tac`fmap_to_alist f` >>
  qexists_tac`fmap_to_alist p0` >> simp[] >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- (
    MATCH_MP_TAC LIST_TYPE_exists >>
    qx_gen_tac`p`>>PairCases_on`p` >>
    simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    simp[OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR] ) >>
  conj_tac >- (
    MATCH_MP_TAC LIST_TYPE_exists >>
    qx_gen_tac`p`>>PairCases_on`p` >>
    simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    simp[OPTION_TYPE_AST_ID_TYPE_LIST_TYPE_CHAR] ) >>
  conj_tac >- (
    MATCH_MP_TAC LIST_TYPE_exists >>
    qx_gen_tac`p`>>PairCases_on`p` >>
    simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    strip_tac >> MATCH_MP_TAC LIST_TYPE_exists >>
    simp[std_preludeTheory.CHAR_def] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] ) >>
  MATCH_MP_TAC LIST_TYPE_exists >>
  qx_gen_tac`p`>>PairCases_on`p` >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  strip_tac >>
  simp[GSYM PULL_EXISTS] >> conj_tac >>
  MATCH_MP_TAC LIST_TYPE_exists >>
  simp[std_preludeTheory.CHAR_def] >>
  TRY(qx_gen_tac`p`>>PairCases_on`p`) >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def]>>
  strip_tac >> MATCH_MP_TAC LIST_TYPE_exists >>
  simp[std_preludeTheory.CHAR_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val tac =
    qx_gen_tac`p`>>PairCases_on`p` >>
    simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def]

val ltchartac =
  MATCH_MP_TAC LIST_TYPE_exists >>
  simp[std_preludeTheory.CHAR_def] >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def]

val UNIFY_INFER_T_TYPE_exists = prove(
  ``∀a. ∃v. UNIFY_INFER_T_TYPE a v``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[ml_repl_stepTheory.UNIFY_INFER_T_TYPE_def] >>
  simp[NUM_def,ml_translatorTheory.INT_def] >>
  simp[GSYM PULL_EXISTS,EVERY_MEM] >> rw[] >>
  TRY(Cases_on`t`)>>
  simp[ml_repl_stepTheory.AST_TC0_TYPE_def,PULL_EXISTS] >>
  TRY(Cases_on`i`)>>simp[ml_repl_stepTheory.AST_ID_TYPE_def]>>
  simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac )

val AST_T_TYPE_exists = prove(
  ``∀a. ∃v. AST_T_TYPE a v``,
  HO_MATCH_MP_TAC t_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def] >>
  simp[NUM_def,ml_translatorTheory.INT_def] >>
  rw[] >- ltchartac >>
  Cases_on`a`>>
  simp[ml_repl_stepTheory.AST_TC0_TYPE_def,PULL_EXISTS] >>
  TRY(Cases_on`i`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def]>>
      simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
  TRY (MATCH_MP_TAC LIST_TYPE_exists) >>
  fs[EVERY_MEM])

val REPL_FUN_REPL_FUN_STATE_TYPE_exists = prove(
 ``∀s. ∃v. REPL_FUN_REPL_FUN_STATE_TYPE s v``,
 Cases >>
 PairCases_on`p` >>
 PairCases_on`p0` >>
 Cases_on`c`>>
 PairCases_on`p` >>
 simp[ml_repl_stepTheory.REPL_FUN_REPL_FUN_STATE_TYPE_def] >>
 simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
 simp[GSYM PULL_EXISTS] >>
 conj_tac >- (
   MATCH_MP_TAC LIST_TYPE_exists >> tac >>
   Cases_on`p1`>>
   simp[ml_repl_stepTheory.AST_TC0_TYPE_def,PULL_EXISTS] >>
   TRY ltchartac >>
   simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   Cases_on`i`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def]>>
   simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
 conj_tac >- (
   MATCH_MP_TAC LIST_TYPE_exists >>
   tac >>
   strip_tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   Cases_on`p1'`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def]>>
   simp[GSYM PULL_EXISTS] >> rw[] >> ltchartac ) >>
 conj_tac >- (
   MATCH_MP_TAC LIST_TYPE_exists >>
   tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   simp[UNIFY_INFER_T_TYPE_exists] ) >>
 conj_tac >- (
   MATCH_MP_TAC LIST_TYPE_exists >>
   tac >>
   strip_tac >>
   Cases_on`p0`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def,PULL_EXISTS]>>
   Cases_on`p3`>>simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def]>>
   TRY(Cases_on`i`>>simp[ml_repl_stepTheory.AST_ID_TYPE_def,PULL_EXISTS])>>
   simp[GSYM PULL_EXISTS] >> rw[] >>
   TRY ltchartac >> rw[] >> TRY ltchartac >>
   simp[AST_T_TYPE_exists] ) >>
 conj_tac >- (
   MATCH_MP_TAC LIST_TYPE_exists >>
   tac >> simp[GSYM PULL_EXISTS] >> rw[] >> TRY ltchartac >>
   simp[UNIFY_INFER_T_TYPE_exists] ) >>
 simp[COMPILER_COMPILER_STATE_TYPE_exists])

val INPUT_TYPE_exists = prove(
  ``STATE_TYPE s v ⇒ ∃w. INPUT_TYPE (SOME (ts,s)) (Conv(SOME(Short"Some"))[Conv(SOME(Short"Pair"))[w;v]])``,
  simp[STATE_TYPE_def,INPUT_TYPE_def,std_preludeTheory.OPTION_TYPE_def,PULL_EXISTS] >>
  PairCases_on`s` >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[std_preludeTheory.FMAP_TYPE_def,PULL_EXISTS,std_preludeTheory.FMAP_EQ_ALIST_def] >>
  simp[GSYM PULL_EXISTS] >> rw[REPL_FUN_REPL_FUN_STATE_TYPE_exists] >>
  MATCH_MP_TAC LIST_TYPE_exists >>
  Cases >>
  simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def] >> rw[] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  ltchartac )

val LIST_TYPE_closed = prove(
  ``∀x. (∀a v. MEM a x ∧ A a v ⇒ closed env v) ⇒ ∀l. LIST_TYPE A x l ⇒ closed env l``,
  Induct >>
  simp[mini_preludeTheory.LIST_TYPE_def] >>
  simp[PULL_EXISTS] >> METIS_TAC[])

val PAIR_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed env y) ∧
    (∀x y. B x y ⇒ closed env y) ∧
    PAIR_TYPE A B a b ⇒
    closed env b``,
  gen_tac >>
  PairCases_on`a` >>
  simp[mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL semanticsExtraTheory.closed_rules))) >>
  rw[] >> METIS_TAC[])

val OPTION_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed env y) ∧ OPTION_TYPE A a b ⇒ closed env b``,
  Cases >> simp[std_preludeTheory.OPTION_TYPE_def] >> rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL semanticsExtraTheory.closed_rules))) >>
  rw[] >> METIS_TAC[])

val AST_ID_TYPE_closed = prove(
  ``∀a. (∀x y. A x y ⇒ closed env y) ∧ AST_ID_TYPE A a b ⇒ closed env b``,
  Cases >> simp[ml_repl_stepTheory.AST_ID_TYPE_def] >> rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL semanticsExtraTheory.closed_rules))) >>
  rw[] >> TRY(METIS_TAC[]) >>
  qmatch_abbrev_tac`closed env z` >>
  qmatch_assum_rename_tac`B c d`[] >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`,std_preludeTheory.CHAR_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val AST_TC0_TYPE_closed = prove(
  ``∀a. AST_TC0_TYPE a b ⇒ closed env b``,
  Cases >>
  simp[ml_repl_stepTheory.AST_TC0_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL semanticsExtraTheory.closed_rules))) >>
  rw[] >>
  qmatch_abbrev_tac`closed env x` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`closed env x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )

val UNIFY_INFER_T_TYPE_closed = prove(
  ``∀a b. UNIFY_INFER_T_TYPE a b ⇒ closed env b``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[ml_repl_stepTheory.UNIFY_INFER_T_TYPE_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL semanticsExtraTheory.closed_rules))) >>
  rw[] >>
  TRY (MATCH_MP_TAC (GEN_ALL AST_TC0_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
  qmatch_abbrev_tac`closed env x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val AST_T_TYPE_closed = prove(
  ``∀a b. AST_T_TYPE a b ⇒ closed env b``,
  HO_MATCH_MP_TAC t_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def] >>
  rw[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL semanticsExtraTheory.closed_rules))) >>
  rw[] >>
  TRY (MATCH_MP_TAC (GEN_ALL AST_TC0_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
  qmatch_abbrev_tac`closed env x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_closed = prove(
  ``∀a b. SEMANTICPRIMITIVES_TID_OR_EXN_TYPE a b ⇒ closed env b``,
  Cases >> simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
  rw[] >>
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (SPEC_ALL semanticsExtraTheory.closed_rules))) >>
  rw[] >>
  qmatch_abbrev_tac`closed env x` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) AST_ID_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[] >> unabbrev_all_tac >>
  qmatch_abbrev_tac`closed env x` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(MATCH_MP_TAC o MP_CANON) LIST_TYPE_closed >>
  simp[Abbr`A`] >>
  rw[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val COMPILER_COMPILER_STATE_TYPE_closed = prove(
  ``COMPILER_COMPILER_STATE_TYPE x y ⇒ closed [] y``,
  Cases_on`x` >>
  PairCases_on`p` >>
  simp[ml_repl_stepTheory.COMPILER_COMPILER_STATE_TYPE_def] >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  simp[std_preludeTheory.FMAP_TYPE_def,PULL_EXISTS,std_preludeTheory.FMAP_EQ_ALIST_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  rw[] >>
  rpt (
    qmatch_abbrev_tac`closed [] x` >>
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
    rw[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val REPL_FUN_REPL_FUN_STATE_TYPE_closed = prove(
  ``REPL_FUN_REPL_FUN_STATE_TYPE a v ⇒ closed [] v``,
  Cases_on`a`>>simp[ml_repl_stepTheory.REPL_FUN_REPL_FUN_STATE_TYPE_def,PULL_EXISTS] >>
  PairCases_on`p0` >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  PairCases_on`p` >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
  rw[] >>
  TRY(MATCH_MP_TAC (GEN_ALL COMPILER_COMPILER_STATE_TYPE_closed) >>
      HINT_EXISTS_TAC >> rw[] ) >>
  rpt (
    TRY (MATCH_MP_TAC (GEN_ALL AST_TC0_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL UNIFY_INFER_T_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL AST_T_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    TRY (MATCH_MP_TAC (GEN_ALL SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_closed) >> HINT_EXISTS_TAC >> rw[]) >>
    qmatch_abbrev_tac`closed [] x` >>
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
    rw[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val INPUT_TYPE_closed = prove(
  ``INPUT_TYPE x y ⇒ closed [] y``,
  simp[INPUT_TYPE_def] >>
  Cases_on`x` >>
  simp[std_preludeTheory.OPTION_TYPE_def] >>
  rw[] >> simp[] >>
  qmatch_assum_rename_tac `PAIR_TYPE X Y s p`["X","Y"] >>
  PairCases_on`s` >>
  fs[mini_preludeTheory.PAIR_TYPE_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[std_preludeTheory.FMAP_TYPE_def] >>
  rw[] >- (
    qmatch_rename_tac`closed [] ls`[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE A vv ls` >>
    Q.ISPECL_THEN[`[]:envM`,`A`,`vv`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`A`] >>
    Cases >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    rw[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE B s bb` >>
    Q.ISPECL_THEN[`[]:envM`,`B`,`s`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`B`,std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )
  >- (
    qmatch_rename_tac`closed [] ls`[] >>
    qmatch_assum_abbrev_tac`LIST_TYPE A vv ls` >>
    Q.ISPECL_THEN[`[]:envM`,`A`,`vv`](match_mp_tac o MP_CANON) (GEN_ALL LIST_TYPE_closed) >>
    simp[Abbr`A`] >>
    Cases >> simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS] >>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )
  >> METIS_TAC[REPL_FUN_REPL_FUN_STATE_TYPE_closed])

val LIST_TYPE_all_cns = prove(
  ``∀x. (∀a v. MEM a x ∧ A a v ⇒ all_cns v ⊆ s) ⇒
    ∀l. LIST_TYPE A x l ∧ {SOME(Short"nil");SOME(Short"::")} ⊆ s
    ⇒ all_cns l ⊆ s``,
  Induct >>
  simp[mini_preludeTheory.LIST_TYPE_def] >>
  simp[PULL_EXISTS] >>
  fs[pred_setTheory.SUBSET_DEF] >>
  METIS_TAC[])

val PAIR_TYPE_all_cns = prove(
  ``∀x y. (∀x y. A x y ⇒ all_cns y ⊆ s) ∧
          (∀x y. B x y ⇒ all_cns y ⊆ s) ∧
          (SOME(Short"Pair"))∈s ∧
          PAIR_TYPE A B x y ⇒ all_cns y ⊆ s``,
  Cases >> simp[mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
  METIS_TAC[])

val LEXER_FUN_SYMBOL_TYPE_all_cns = prove(
  ``∀x y. LEXER_FUN_SYMBOL_TYPE x y ∧ {
     SOME(Short"nil");
     SOME(Short"::");
     SOME(Short"Errors");
     SOME(Short"Others");
     SOME(Short"Longs");
     SOME(Short"Numbers");
     SOME(Short"Strings")} ⊆ s
  ⇒ all_cns y ⊆ s
  ``,
  Cases >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def] >> rw[] >>
  simp[semanticsExtraTheory.all_cns_def] >>
  fs[ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC pred_setTheory.SUBSET_TRANS >>
  qexists_tac`{SOME(Short "nil"); SOME (Short "::")}` >>
  (conj_tac >- (
    MATCH_MP_TAC (MP_CANON (Q.ISPEC`CHAR`(Q.GEN`A` LIST_TYPE_all_cns))) >>
    rw[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    HINT_EXISTS_TAC >>rw[] )) >>
  simp[] )

val OPTION_TYPE_all_cns = prove(
  ``∀x y. (∀x y. A x y ⇒ all_cns y ⊆ s) ∧
          {SOME(Short"Some");SOME(Short"None")} ⊆ s ∧
          OPTION_TYPE A x y ⇒ all_cns y ⊆ s``,
  Cases >> simp[std_preludeTheory.OPTION_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
  METIS_TAC[])

val AST_ID_TYPE_all_cns = prove(
  ``∀x y. (∀x y. A x y ⇒ all_cns y ⊆ s) ∧
          {SOME(Short"Short");SOME(Short"Long");SOME(Short"nil");SOME(Short"::")} ⊆ s ∧
          AST_ID_TYPE A x y ⇒ all_cns y ⊆ s``,
  Cases >> simp[ml_repl_stepTheory.AST_ID_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
  qmatch_abbrev_tac`all_cns x ⊆ s` >>
  TRY (
    qmatch_assum_abbrev_tac`LIST_TYPE B ll x` >>
    Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_cns >>
    map_every qexists_tac [`ll`,`B`] >> simp[] >>
    rw[Abbr`B`] >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def]) >>
  METIS_TAC[])

val COMPILER_COMPILER_STATE_TYPE_all_cns = prove(
  ``∀x y. COMPILER_COMPILER_STATE_TYPE x y ∧
    {SOME(Short"None");
     SOME(Short"Some");
     SOME(Short"Pair");
     SOME(Short"nil");
     SOME(Short"::");
     SOME(Short"Short");
     SOME(Short"Long");
     SOME(Short"Compiler_state")
    } ⊆ s
  ⇒ all_cns y ⊆ s
   ``,
  Cases >> simp[ml_repl_stepTheory.COMPILER_COMPILER_STATE_TYPE_def,PULL_EXISTS] >>
  PairCases_on`p` >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS,std_preludeTheory.FMAP_TYPE_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  rpt strip_tac >>
  rpt (
    qmatch_abbrev_tac`all_cns x ⊆ s` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) OPTION_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val AST_TC0_TYPE_all_cns = prove(
  ``∀x y. AST_TC0_TYPE x y ∧
    {SOME(Short"Tc_exn");
     SOME(Short"Tc_tup");
     SOME(Short"Tc_fn");
     SOME(Short"Tc_ref");
     SOME(Short"Tc_unit");
     SOME(Short"Tc_bool");
     SOME(Short"Tc_int");
     SOME(Short"Tc_string");
     SOME(Short"Tc_name");
     SOME(Short"nil");
     SOME(Short"::");
     SOME(Short"Short");
     SOME(Short"Long")
    } ⊆ s
  ⇒ all_cns y ⊆ s``,
  Cases >> simp[ml_repl_stepTheory.AST_TC0_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
  qmatch_abbrev_tac`all_cns x ⊆ s` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_all_cns >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`all_cns x ⊆ s` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_cns >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val UNIFY_INFER_T_TYPE_all_cns = prove(
  ``∀x y. UNIFY_INFER_T_TYPE x y ∧
    {SOME(Short"Infer_tuvar");
     SOME(Short"Infer_tapp");
     SOME(Short"Infer_tvar_db");
     SOME(Short"Tc_exn");
     SOME(Short"Tc_tup");
     SOME(Short"Tc_fn");
     SOME(Short"Tc_ref");
     SOME(Short"Tc_unit");
     SOME(Short"Tc_bool");
     SOME(Short"Tc_int");
     SOME(Short"Tc_string");
     SOME(Short"Tc_name");
     SOME(Short"nil");
     SOME(Short"::");
     SOME(Short"Short");
     SOME(Short"Long")
    } ⊆ s
  ⇒ all_cns y ⊆ s``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[ml_repl_stepTheory.UNIFY_INFER_T_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  qmatch_abbrev_tac`all_cns x ⊆ s` >>
  TRY (
    qmatch_assum_abbrev_tac`AST_TC0_TYPE ll x` >>
    Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_all_cns >>
    qexists_tac`ll` >> rw[] ) >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_cns >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val AST_T_TYPE_all_cns = prove(
  ``∀x y. AST_T_TYPE x y ∧
    {SOME(Short"Tvar");
     SOME(Short"Tvar_db");
     SOME(Short"Tapp");
     SOME(Short"Tc_exn");
     SOME(Short"Tc_tup");
     SOME(Short"Tc_fn");
     SOME(Short"Tc_ref");
     SOME(Short"Tc_unit");
     SOME(Short"Tc_bool");
     SOME(Short"Tc_int");
     SOME(Short"Tc_string");
     SOME(Short"Tc_name");
     SOME(Short"nil");
     SOME(Short"::");
     SOME(Short"Short");
     SOME(Short"Long")
    } ⊆ s
  ⇒ all_cns y ⊆ s``,
  HO_MATCH_MP_TAC t_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  qmatch_abbrev_tac`all_cns z ⊆ s` >>
  TRY (
    qmatch_assum_abbrev_tac`AST_TC0_TYPE ll z` >>
    Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_all_cns >>
    qexists_tac`ll` >> rw[] ) >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll z` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_cns >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_all_cns = prove(
  ``∀x y. SEMANTICPRIMITIVES_TID_OR_EXN_TYPE x y ∧
    {SOME(Short"Typeid");
     SOME(Short"Typeexn");
     SOME(Short"nil");
     SOME(Short"::");
     SOME(Short"Short");
     SOME(Short"Long")
     } ⊆ s
  ⇒ all_cns y ⊆ s``,
  Cases >>
  simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
  qmatch_abbrev_tac`all_cns z ⊆ s` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_all_cns >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`all_cns z ⊆ s` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll z` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_cns >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )

val REPL_FUN_REPL_FUN_STATE_TYPE_all_cns = prove(
  ``∀x y. REPL_FUN_REPL_FUN_STATE_TYPE x y ∧
    {SOME(Short"None");
     SOME(Short"Some");
     SOME(Short"Pair");
     SOME(Short"nil");
     SOME(Short"::");
     SOME(Short"Typeid");
     SOME(Short"Typeexn");
     SOME(Short"Tvar");
     SOME(Short"Tvar_db");
     SOME(Short"Tapp");
     SOME(Short"Infer_tuvar");
     SOME(Short"Infer_tapp");
     SOME(Short"Infer_tvar_db");
     SOME(Short"Short");
     SOME(Short"Long");
     SOME(Short"Tc_exn");
     SOME(Short"Tc_tup");
     SOME(Short"Tc_fn");
     SOME(Short"Tc_ref");
     SOME(Short"Tc_unit");
     SOME(Short"Tc_bool");
     SOME(Short"Tc_int");
     SOME(Short"Tc_string");
     SOME(Short"Tc_name");
     SOME(Short"Compiler_state");
     SOME(Short"Repl_fun_state")
    } ⊆ s
  ⇒ all_cns y ⊆ s``,
  Cases >>
  PairCases_on`p0`>>
  PairCases_on`p`>>
  simp[ml_repl_stepTheory.REPL_FUN_REPL_FUN_STATE_TYPE_def] >>
  simp[semanticsExtraTheory.all_cns_def,PULL_EXISTS,mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >>
  TRY (
    MATCH_MP_TAC (MP_CANON COMPILER_COMPILER_STATE_TYPE_all_cns) >>
    qexists_tac`c` >> rw[] >> NO_TAC) >>
  rpt (
    qmatch_abbrev_tac`all_cns x ⊆ s` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) OPTION_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_TC0_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_all_cns >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`UNIFY_INFER_T_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) UNIFY_INFER_T_TYPE_all_cns >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_T_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_T_TYPE_all_cns >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`SEMANTICPRIMITIVES_TID_OR_EXN_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_all_cns >>
      qexists_tac`ll` >> rw[]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val INPUT_TYPE_all_cns = prove(
  ``INPUT_TYPE x y ∧
    {SOME(Short"None");
     SOME(Short"Some");
     SOME(Short"Pair");
     SOME(Short"nil");
     SOME(Short"::");
     SOME(Short"Typeid");
     SOME(Short"Typeexn");
     SOME(Short"Tvar");
     SOME(Short"Tvar_db");
     SOME(Short"Tapp");
     SOME(Short"Infer_tuvar");
     SOME(Short"Infer_tapp");
     SOME(Short"Infer_tvar_db");
     SOME(Short"Short");
     SOME(Short"Long");
     SOME(Short"Tc_exn");
     SOME(Short"Tc_tup");
     SOME(Short"Tc_fn");
     SOME(Short"Tc_ref");
     SOME(Short"Tc_unit");
     SOME(Short"Tc_bool");
     SOME(Short"Tc_int");
     SOME(Short"Tc_string");
     SOME(Short"Tc_name");
     SOME(Short"Compiler_state");
     SOME(Short"Repl_fun_state");
     SOME(Short"Errors");
     SOME(Short"Others");
     SOME(Short"Longs");
     SOME(Short"Numbers");
     SOME(Short"Strings")} ⊆ s
  ⇒ all_cns y ⊆ s``,
  simp[INPUT_TYPE_def] >>
  Cases_on`x` >>
  simp[std_preludeTheory.OPTION_TYPE_def] >>
  rw[] >>
  simp[semanticsExtraTheory.all_cns_def] >>
  qmatch_assum_rename_tac `PAIR_TYPE X Y q p`["X","Y"] >>
  PairCases_on`q` >>
  fs[mini_preludeTheory.PAIR_TYPE_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[std_preludeTheory.FMAP_TYPE_def] >>
  rw[] >>
  rpt (
    qmatch_abbrev_tac`all_cns x ⊆ s` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_all_cns >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`LEXER_FUN_SYMBOL_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LEXER_FUN_SYMBOL_TYPE_all_cns >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`REPL_FUN_REPL_FUN_STATE_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) REPL_FUN_REPL_FUN_STATE_TYPE_all_cns >>
      qexists_tac`ll` >> rw[]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val INPUT_TYPE_all_cns_repl_decs_cenv = prove(
  ``INPUT_TYPE x y ⇒ all_cns y ⊆ cenv_dom (repl_decs_cenv ++ init_envC)``,
  rw[] >>
  imp_res_tac INPUT_TYPE_all_cns >>
  first_x_assum MATCH_MP_TAC >>
  simp[semanticsExtraTheory.cenv_dom_def,pred_setTheory.SUBSET_DEF,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
  simp[repl_decs_cenv_def] >>
  simp[ml_repl_step_decls_cenv] >>
  rw[] >>
  REWRITE_TAC[decs_to_cenv_ml_repl_step_decls] >>
  REWRITE_TAC[MEM,astTheory.id_11,pairTheory.PAIR_EQ] >>
  EVAL_TAC >> simp[])

val LIST_TYPE_all_locs = prove(
  ``∀x. (∀a v. MEM a x ∧ A a v ⇒ (all_locs v = {})) ⇒
    ∀l. LIST_TYPE A x l ⇒ (all_locs l = {})``,
  Induct >>
  simp[mini_preludeTheory.LIST_TYPE_def] >>
  simp[PULL_EXISTS] >>
  fs[pred_setTheory.SUBSET_DEF] >>
  METIS_TAC[])

val PAIR_TYPE_all_locs = prove(
  ``∀x y. (∀x y. A x y ⇒ (all_locs y = {})) ∧
          (∀x y. B x y ⇒ (all_locs y = {})) ∧
          PAIR_TYPE A B x y ⇒ (all_locs y = {})``,
  Cases >> simp[mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
  METIS_TAC[])

val LEXER_FUN_SYMBOL_TYPE_all_locs = prove(
  ``∀x y. LEXER_FUN_SYMBOL_TYPE x y ⇒ (all_locs y = {})``,
  Cases >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def] >> rw[] >>
  simp[semanticsExtraTheory.all_locs_def] >>
  fs[ml_translatorTheory.INT_def] >>
  MATCH_MP_TAC (MP_CANON (Q.ISPEC`CHAR`(Q.GEN`A` LIST_TYPE_all_locs))) >>
  rw[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  HINT_EXISTS_TAC >>rw[])

val OPTION_TYPE_all_locs = prove(
  ``∀x y. (∀x y. A x y ⇒ (all_locs y = {})) ∧
          OPTION_TYPE A x y ⇒ (all_locs y = {})``,
  Cases >> simp[std_preludeTheory.OPTION_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
  METIS_TAC[])

val AST_ID_TYPE_all_locs = prove(
  ``∀x y. (∀x y. A x y ⇒ (all_locs y = {})) ∧
          AST_ID_TYPE A x y ⇒ (all_locs y = {})``,
  Cases >> simp[ml_repl_stepTheory.AST_ID_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
  res_tac >>
  qmatch_assum_abbrev_tac`LIST_TYPE B ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_locs >>
  map_every qexists_tac [`ll`,`B`] >> simp[] >>
  rw[Abbr`B`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val COMPILER_COMPILER_STATE_TYPE_all_locs = prove(
  ``∀x y. COMPILER_COMPILER_STATE_TYPE x y ⇒ (all_locs y = {})``,
  Cases >> simp[ml_repl_stepTheory.COMPILER_COMPILER_STATE_TYPE_def,PULL_EXISTS] >>
  PairCases_on`p` >>
  simp[mini_preludeTheory.PAIR_TYPE_def,PULL_EXISTS,std_preludeTheory.FMAP_TYPE_def] >>
  simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  rpt strip_tac >>
  rpt (
    qmatch_abbrev_tac`all_locs x = {}` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) OPTION_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val AST_TC0_TYPE_all_locs = prove(
  ``∀x y. AST_TC0_TYPE x y ⇒ (all_locs y = {})``,
  Cases >> simp[ml_repl_stepTheory.AST_TC0_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
  qmatch_abbrev_tac`all_locs x = {}` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_all_locs >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`all_locs x = {}` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_locs >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])

val UNIFY_INFER_T_TYPE_all_locs = prove(
  ``∀x y. UNIFY_INFER_T_TYPE x y ⇒ (all_locs y = {})``,
  HO_MATCH_MP_TAC infer_t_ind >>
  simp[ml_repl_stepTheory.UNIFY_INFER_T_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  qmatch_abbrev_tac`(all_locs x = {})` >>
  TRY (
    qmatch_assum_abbrev_tac`AST_TC0_TYPE ll x` >>
    Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_all_locs >>
    qexists_tac`ll` >> rw[] ) >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_locs >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val AST_T_TYPE_all_locs = prove(
  ``∀x y. AST_T_TYPE x y ⇒ (all_locs y = {})``,
  HO_MATCH_MP_TAC t_ind >>
  simp[ml_repl_stepTheory.AST_T_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  qmatch_abbrev_tac`(all_locs z = {})` >>
  TRY (
    qmatch_assum_abbrev_tac`AST_TC0_TYPE ll z` >>
    Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_all_locs >>
    qexists_tac`ll` >> rw[] ) >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll z` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_locs >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[EVERY_MEM] >> METIS_TAC[])

val SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_all_locs = prove(
  ``∀x y. SEMANTICPRIMITIVES_TID_OR_EXN_TYPE x y ⇒ (all_locs y = {})``,
  Cases >>
  simp[ml_repl_stepTheory.SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_def] >>
  rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
  qmatch_abbrev_tac`(all_locs z = {})` >>
  qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_all_locs >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac`(all_locs z = {})` >>
  qmatch_assum_abbrev_tac`LIST_TYPE A ll z` >>
  Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_locs >>
  map_every qexists_tac [`ll`,`A`] >> simp[] >>
  rw[Abbr`A`] >>
  fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] )

val REPL_FUN_REPL_FUN_STATE_TYPE_all_locs = prove(
  ``∀x y. REPL_FUN_REPL_FUN_STATE_TYPE x y ⇒ (all_locs y = {})``,
  Cases >>
  PairCases_on`p0`>>
  PairCases_on`p`>>
  simp[ml_repl_stepTheory.REPL_FUN_REPL_FUN_STATE_TYPE_def] >>
  simp[semanticsExtraTheory.all_locs_def,PULL_EXISTS,mini_preludeTheory.PAIR_TYPE_def] >>
  rw[] >>
  TRY (
    MATCH_MP_TAC (MP_CANON COMPILER_COMPILER_STATE_TYPE_all_locs) >>
    qexists_tac`c` >> rw[] >> NO_TAC) >>
  rpt (
    qmatch_abbrev_tac`(all_locs x = {})` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`OPTION_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) OPTION_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_ID_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_ID_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_TC0_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_TC0_TYPE_all_locs >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`UNIFY_INFER_T_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) UNIFY_INFER_T_TYPE_all_locs >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`AST_T_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) AST_T_TYPE_all_locs >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`SEMANTICPRIMITIVES_TID_OR_EXN_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) SEMANTICPRIMITIVES_TID_OR_EXN_TYPE_all_locs >>
      qexists_tac`ll` >> rw[]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val INPUT_TYPE_all_locs = prove(
  ``INPUT_TYPE x y ⇒ (all_locs y = {})``,
  simp[INPUT_TYPE_def] >>
  Cases_on`x` >>
  simp[std_preludeTheory.OPTION_TYPE_def] >>
  rw[] >>
  simp[terminationTheory.contains_closure_def] >>
  qmatch_assum_rename_tac `PAIR_TYPE X Y s p`["X","Y"] >>
  PairCases_on`s` >>
  fs[mini_preludeTheory.PAIR_TYPE_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[ml_translatorTheory.BOOL_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  fs[std_preludeTheory.FMAP_TYPE_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rw[] >>
  rpt (
    qmatch_abbrev_tac`all_locs x = {}` >>
    ((
      qmatch_assum_abbrev_tac`LIST_TYPE A ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LIST_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`A`] >> simp[] >>
      rw[Abbr`A`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`PAIR_TYPE A B ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) PAIR_TYPE_all_locs >>
      map_every qexists_tac [`ll`,`B`,`A`] >> simp[] >>
      rw[Abbr`A`,Abbr`B`]
     ) ORELSE (
      qmatch_assum_abbrev_tac`LEXER_FUN_SYMBOL_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) LEXER_FUN_SYMBOL_TYPE_all_locs >>
      qexists_tac`ll` >> rw[]
     ) ORELSE (
      qmatch_assum_abbrev_tac`REPL_FUN_REPL_FUN_STATE_TYPE ll x` >>
      Q.ISPEC_THEN`ll`(match_mp_tac o MP_CANON o GEN_ALL) REPL_FUN_REPL_FUN_STATE_TYPE_all_locs >>
      qexists_tac`ll` >> rw[]
     )) >>
    fs[std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
    unabbrev_all_tac ))

val EVERY_APPEND_lemma = prove(
  ``EVERY P ls ∧ P x ∧ n < LENGTH ls ⇒ EVERY P (TAKE n ls ++ [x] ++ DROP (n + 1) ls)``,
  simp[EVERY_MEM] >> strip_tac >>
  `n ≤ LENGTH ls` by DECIDE_TAC >>
  `n + 1 <= LENGTH ls` by DECIDE_TAC >>
  METIS_TAC[rich_listTheory.MEM_TAKE,rich_listTheory.MEM_DROP])

val IN_vlabs_list_EVERY = prove(
  ``(∀cd. cd ∈ vlabs_list vs ⇒ Z cd) ⇔ (EVERY (λs. ∀cd. cd ∈ s ⇒ Z cd) (MAP vlabs vs))``,
  simp[intLangExtraTheory.vlabs_list_MAP,EVERY_MAP,EVERY_MEM,PULL_EXISTS] >>
  METIS_TAC[])

val LIST_TYPE_Cv_bv = prove(
  ``(FLOOKUP m (SOME(Short"nil")) = SOME (nil_tag - block_tag)) ∧
    (FLOOKUP m (SOME(Short"::")) = SOME (cons_tag - block_tag))
  ⇒
    ∀ls v. LIST_TYPE A ls v ∧ (∀x y. MEM x ls ∧ A x y ⇒ Cv_bv pp (v_to_Cv mv m y) (f x)) ⇒
      Cv_bv pp (v_to_Cv mv m v) (BlockList (MAP f ls))``,
   strip_tac >>
   Induct >> simp[mini_preludeTheory.LIST_TYPE_def,compilerTerminationTheory.v_to_Cv_def] >- (
     simp[Once toBytecodeProofsTheory.Cv_bv_cases,BlockList_def,BlockNil_def,nil_tag_def] ) >>
   simp[PULL_EXISTS,compilerTerminationTheory.v_to_Cv_def] >>
   rw[] >>
   simp[Once toBytecodeProofsTheory.Cv_bv_cases,BlockList_def] >>
   simp[BlockCons_def,cons_tag_def]) |> SIMP_RULE (srw_ss())[]

val LEXER_FUN_SYMBOL_TYPE_Cv_bv = prove(
  ``(FLOOKUP m (SOME (Short"Errors")) = SOME (errors_tag - block_tag)) ∧
    (FLOOKUP m (SOME (Short"Others")) = SOME (others_tag - block_tag)) ∧
    (FLOOKUP m (SOME (Short"Longs")) = SOME (longs_tag - block_tag)) ∧
    (FLOOKUP m (SOME (Short"Numbers")) = SOME (numbers_tag - block_tag)) ∧
    (FLOOKUP m (SOME (Short"Strings")) = SOME (strings_tag - block_tag)) ∧
    (FLOOKUP m (SOME(Short"nil")) = SOME (nil_tag - block_tag)) ∧
    (FLOOKUP m (SOME(Short"::")) = SOME (cons_tag - block_tag))
    ⇒
    ∀x y. LEXER_FUN_SYMBOL_TYPE x y ⇒ Cv_bv pp (v_to_Cv mv m y) (BlockSym x)``,
  strip_tac >>
  Cases >> simp[ml_repl_stepTheory.LEXER_FUN_SYMBOL_TYPE_def,PULL_EXISTS] >>
  simp[ml_translatorTheory.INT_def,compilerTerminationTheory.v_to_Cv_def] >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases,BlockSym_def] >>
  simp[BlockStringS_def,strings_tag_def,
       BlockNumberS_def,numbers_tag_def,
       BlockLongS_def,longs_tag_def,
       BlockOtherS_def,others_tag_def,
       BlockErrorS_def,errors_tag_def] >>
  TRY (simp[Once toBytecodeProofsTheory.Cv_bv_cases] >> NO_TAC) >>
  rw[] >>
  MATCH_MP_TAC (Q.ISPEC`CHAR`(Q.GEN`A` (MP_CANON LIST_TYPE_Cv_bv))) >>
  simp[Chr_def,std_preludeTheory.CHAR_def,ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def] >>
  simp[compilerTerminationTheory.v_to_Cv_def] >>
  simp[Once toBytecodeProofsTheory.Cv_bv_cases])

val stack_length =
  compileReplDecsTheory.repl_decs_compiled |> concl |> rand
         |> dest_pair |> snd |> dest_pair |> snd
         |> dest_pair |> snd |> dest_pair |> fst;

val repl_decs_stack_length_def = Define `
  repl_decs_stack_length = ^stack_length`;

val COMPILER_RUN_INV_STACK_LENGTH = store_thm("COMPILER_RUN_INV_STACK_LENGTH",
  ``COMPILER_RUN_INV bs inp outp ==>
    (LENGTH bs.stack = repl_decs_stack_length)``,
  rw[COMPILER_RUN_INV_def,compilerProofsTheory.env_rs_def,LET_THM,toBytecodeProofsTheory.Cenv_bs_def] >>
  fs[new_compiler_state_rsz,repl_decs_stack_length_def]);

val _ = export_theory()
