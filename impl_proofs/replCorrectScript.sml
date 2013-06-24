open preamble boolSimps miscLib;
open lexer_funTheory repl_funTheory replTheory
open lexer_implTheory mmlParseTheory inferSoundTheory BigStepTheory ElabTheory compileLabelsTheory compilerProofsTheory;
open TypeSystemTheory typeSoundTheory weakeningTheory typeSysPropsTheory;

val _ = new_theory "replCorrect";

val lex_impl_all_def = tDefine "lex_impl_all" `
lex_impl_all input = 
  case lex_until_toplevel_semicolon input of
    | NONE => []
    | SOME (t,input') => t::lex_impl_all input'`
(wf_rel_tac `measure LENGTH` >>
 rw [] >>
 metis_tac [lex_until_toplevel_semicolon_LESS]);

val lexer_correct = Q.prove (
  `!input. split_top_level_semi (lexer_fun input) = lex_impl_all input`,
  gen_tac
  >> completeInduct_on`LENGTH input` >> rw[]
  >> rw[Once split_top_level_semi_def]
  >> rw[Once lex_impl_all_def]
  >> rw[lex_until_toplevel_semicolon_def]
  >> rw[Once lexer_fun_def]
  >> rw[Once lex_aux_def]
  >> Cases_on`next_token input` >> rw[]
  >- (
    rw[toplevel_semi_dex_def]
    >> cheat (* false! *)
    )
  >> cheat)

val parser_correct = Q.prove (
`!toks. parse_top toks = repl$parse toks`,
  rw[parse_top_def,replTheory.parse_def] >>
  rw[mmlParseREPLTop_thm] >>
  qspec_then`toks`strip_assume_tac mmlPEGTheory.parse_REPLTop_total >>
  simp[destResult_def] >>
cheat);

val get_type_error_mask_def = Define `
(get_type_error_mask Terminate = []) ∧
(get_type_error_mask Diverge = [F]) ∧
(get_type_error_mask Diverge = [F]) ∧
(get_type_error_mask (Result r rs) =
  (r = "<type error>")::get_type_error_mask rs)`;

val type_infer_invariants_def = Define `
type_infer_invariants rs rinf_st ⇔
      check_menv (FST rinf_st)
    ∧ check_cenv (FST (SND rinf_st))
    ∧ check_env {} (SND (SND rinf_st))
    ∧ (rs.tenvM = convert_menv (FST rinf_st))
    ∧ (rs.tenvC = FST (SND rinf_st))
    ∧ (rs.tenv = (bind_var_list2 (convert_env2 (SND (SND rinf_st))) Empty))`;

val invariant_def = Define`
  invariant rs rfs bs ⇔
    rfs.relaborator_state = (rs.type_bindings, rs.ctors)

    ∧ type_infer_invariants rs rfs.rinferencer_state
    ∧ type_sound_invariants (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,rs.store)

    ∧ EVERY (closed rs.envM) rs.store
    ∧ EVERY (closed rs.envM) (MAP SND rs.envE)
    ∧ EVERY (EVERY (closed rs.envM) o MAP SND) (MAP SND rs.envM)
    ∧ (∀mn n. MEM (Long mn n) (MAP FST rs.envC) ⇒ MEM mn (MAP FST rs.envM))
    ∧ closed_under_cenv rs.envC rs.envM rs.envE rs.store
    ∧ closed_under_menv rs.envM rs.envE rs.store
    ∧ (∀v. MEM v (MAP SND rs.envE) ∨ MEM v rs.store ⇒ all_locs v ⊆ count (LENGTH rs.store))
    ∧ ∃code. let bs' = bs with code := code in
        bs.code = compile_labels bs.inst_length code
      ∧ (∃rd c. env_rs rs.envM rs.envC rs.envE rfs.rcompiler_state rd (c,rs.store) bs')
      ∧ ALL_DISTINCT (FILTER is_Label bs'.code)
      ∧ EVERY (combin$C $< rfs.rcompiler_state.rnext_label o dest_Label) (FILTER is_Label bs'.code)
    `;

(*
val check_menv_to_tenvM_ok = Q.prove (
`!menv. check_menv menv ⇒ tenvM_ok (convert_menv menv)`,
Induct >>
rw [EVERY_MAP,
    check_menv_def, typeSysPropsTheory.tenvM_ok_def, convert_menv_def] >|
[PairCases_on `h` >>
     fs [] >>
     REPEAT (pop_assum mp_tac) >>
     induct_on `h1` >>
     rw [tenv_ok_def, terminationTheory.bind_var_list2_def] >>
     PairCases_on `h` >>
     fs [terminationTheory.bind_var_list2_def, bind_tenv_def,
         tenv_ok_def, num_tvs_bvl2, num_tvs_def] >>
     metis_tac [check_t_to_check_freevars],
 fs [check_menv_def, tenvM_ok_def] >>
     REPEAT (pop_assum mp_tac) >>
     induct_on `menv` >>
     rw [] >>
     PairCases_on `h` >>
     rw [] >>
     fs [convert_menv_def, EVERY_MAP]]);
     *)

val infer_to_type = Q.prove (
`!rs st bs menv cenv env top new_menv new_cenv new_env st2.
  invariant rs st bs ∧
  (infer_top menv cenv env top init_infer_state =
      (Success (new_menv,new_cenv,new_env),st2)) ∧
  (st.rinferencer_state = (menv,cenv,env))
  ⇒
  type_top rs.tenvM rs.tenvC rs.tenv top
           (convert_menv new_menv) new_cenv (convert_env2 new_env)`,
rw [invariant_def, type_infer_invariants_def, type_sound_invariants_def] >>
fs [] >>
rw [] >>
metis_tac [infer_top_sound]);

val type_invariants_pres = Q.prove (
`!rs rfs.
  type_infer_invariants rs (infer_menv,infer_cenv,infer_env) ∧
  infer_top infer_menv infer_cenv infer_env top init_infer_state = 
          (Success (new_infer_menv,new_infer_cenv,new_infer_env), infer_st2)
  ⇒
  type_infer_invariants (update_repl_state rs el0 el1 (convert_menv new_infer_menv) new_infer_cenv (convert_env2 new_infer_env) st' 
                                     envC (Rval (envM,envE)))
                  (new_infer_menv ++ infer_menv, new_infer_cenv ++ infer_cenv,new_infer_env ++ infer_env)`,
rw [update_repl_state_def, type_infer_invariants_def] >>
`check_menv new_infer_menv ∧
 check_cenv new_infer_cenv ∧
 check_env {} new_infer_env` 
           by metis_tac [infer_top_invariant] >|
[fs [check_menv_def],
 fs [check_cenv_def],
 fs [check_env_def],
 rw [convert_menv_def],
 rw [bvl2_append, convert_env2_def]]);

val print_envC_not_type_error = prove(``ls ≠ "<type error>" ⇒ print_envC envc ++ ls ≠ "<type error>"``,
Induct_on`envc`>>
simp[print_envC_def]>>
Cases>>simp[]>>
Induct_on`q`>>simp[SemanticPrimitivesTheory.id_to_string_def]>>
lrw[LIST_EQ_REWRITE])

val print_envE_not_type_error = prove(``print_envE en ≠ "<type error>"``,
Induct_on`en`>>simp[print_envE_def]>>
Cases>>simp[])

val print_result_not_type_error = prove(``r ≠ Rerr Rtype_error ⇒ print_result top envc r ≠ "<type error>"``,
  Cases_on`r`>>
  TRY(Cases_on`e`)>>
  TRY(PairCases_on`a`)>>
  simp[print_result_def]>>
  Cases_on`top`>>simp[print_result_def]>>
  match_mp_tac print_envC_not_type_error >>
  simp[print_envE_not_type_error])

val replCorrect_lem = Q.prove (
`!repl_state error_mask bc_state repl_fun_state.
  invariant repl_state repl_fun_state bc_state ⇒
  ast_repl repl_state
    (get_type_error_mask (main_loop (bc_state,repl_fun_state) input))
    (MAP parse (split_top_level_semi (lexer_fun input)))
    (main_loop (bc_state,repl_fun_state) input)`,

completeInduct_on `LENGTH input` >>
rw [lexer_correct, Once lex_impl_all_def] >>
ONCE_REWRITE_TAC [main_loop_def] >>
cases_on `lex_until_toplevel_semicolon input` >>
rw [get_type_error_mask_def] >-
metis_tac [ast_repl_rules] >>
`?tok input_rest. x = (tok, input_rest)`
        by (cases_on `x` >>
            metis_tac []) >>
rw [] >>
`(parse tok' = NONE) ∨ ∃ast. parse tok' = SOME ast`
        by (cases_on `parse tok'` >>
            metis_tac []) >-
((* A parse error *)
  rw [] >>
  rw [Once ast_repl_cases, parse_elaborate_infertype_compile_def, parser_correct,
      get_type_error_mask_def] >>
 `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
 metis_tac [lexer_correct]) >>
rw[parse_elaborate_infertype_compile_def,parser_correct] >>
qmatch_assum_rename_tac`elaborate_top st.relaborator_state top0 = (new_elab_state, top)`[] >>
qmatch_assum_rename_tac`invariant rs st bs`[] >>
rw [] >>
`?error_msg next_repl_run_infer_state.
  infertype_top st.rinferencer_state top = Failure error_msg ∨ 
  infertype_top st.rinferencer_state top = Success next_repl_run_infer_state`
         by (cases_on `infertype_top st.rinferencer_state top` >>
             metis_tac []) >>
rw [get_type_error_mask_def] >-
((* A type error *)
 `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
 rw[Once ast_repl_cases] >>
     metis_tac [lexer_correct]) >>
simp[] >>
`?infer_menv infer_cenv infer_env.
  st.rinferencer_state = (infer_menv,infer_cenv,infer_env)`
            by metis_tac [pair_CASES] >>
fs [infertype_top_def] >>

`?res infer_st2. infer_top infer_menv infer_cenv infer_env top init_infer_state = (res,infer_st2)`
        by metis_tac [pair_CASES] >>
fs [] >>
cases_on `res` >>
fs [] >>
`∃new_infer_menv new_infer_cenv new_infer_env.  a = (new_infer_menv,new_infer_cenv,new_infer_env)`
        by metis_tac [pair_CASES] >>
fs [] >>
BasicProvers.VAR_EQ_TAC >>
imp_res_tac infer_to_type >>
`type_sound_invariants (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,rs.store)`
        by fs [invariant_def] >>
`¬top_diverges rs.envM rs.envC rs.store rs.envE top ⇒
       ∃r envC2 store2.
         r ≠ Rerr Rtype_error ∧
         evaluate_top rs.envM rs.envC rs.store rs.envE top (store2,envC2,r) ∧
         type_sound_invariants
           (update_type_sound_inv
              (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,
               rs.store) (convert_menv new_infer_menv) new_infer_cenv
              (convert_env2 new_infer_env) store2 envC2 r)`
          by metis_tac [top_type_soundness] >>

simp[update_state_def] >>

qabbrev_tac`est = st.relaborator_state` >> PairCases_on`est` >>
pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])>>fs[]>>
qabbrev_tac`elab_res = elab_top est0 est1 top0` >> PairCases_on`elab_res` >>
pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])>>fs[]>>
`est0 = rs.type_bindings ∧ est1 = rs.ctors` by fs[invariant_def] >>
rpt BasicProvers.VAR_EQ_TAC >>
fs[elaborate_top_def,LET_THM] >>
qmatch_assum_rename_tac`xxxxxxxx = top`[] >> rpt BasicProvers.VAR_EQ_TAC >>

cases_on `bc_eval (install_code (cpam css) code bs)` >> fs[] >- (
  (* Divergence *)
  rw[Once ast_repl_cases,get_type_error_mask_def] >>
  MAP_EVERY qexists_tac [`convert_menv new_infer_menv`,`new_infer_cenv`,`convert_env2 new_infer_env`] >>
  rw [] >>
  qpat_assum`X ⇒ Y`kall_tac >>
  qpat_assum`∀m. X ⇒ Y`kall_tac >>
  rw[top_diverges_cases] >>
  Cases_on`top`>>fs[] >- (
    (* Module *)
    cheat ) >>
  cheat ) >>

(* SO cheat: I think the semantics can't diverge because (bc_eval install_code
 * code bs) = SOME x).  I think this should come from the compiler proof. *)
`¬top_diverges rs.envM rs.envC rs.store rs.envE top` by cheat >>
fs [] >>
`STRLEN input_rest < STRLEN input` by metis_tac[lex_until_toplevel_semicolon_LESS] >>
simp[Once ast_repl_cases,get_type_error_mask_def] >>
disj1_tac >>
MAP_EVERY qexists_tac [`convert_menv new_infer_menv`,
                       `new_infer_cenv`, 
                       `convert_env2 new_infer_env`,
                       `store2`, 
                       `envC2`,
                       `r`] >>
conj_asm2_tac >- metis_tac[print_result_not_type_error] >>
simp[] >>

  qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`,`(store2,envC2,r)`]mp_tac compile_top_thm >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`ck`mp_tac) >>
  disch_then(qspec_then`st.rcompiler_state`mp_tac) >>
  simp[] >>
  `∃code' rd c.
    bs.code = compile_labels bs.inst_length code' ∧
    env_rs rs.envM rs.envC rs.envE st.rcompiler_state rd (c,rs.store) (bs with code := code') ∧
    ALL_DISTINCT (FILTER is_Label code') ∧
    EVERY (combin$C $< st.rcompiler_state.rnext_label o dest_Label) (FILTER is_Label code')` by (
    fs[invariant_def,LET_THM] >> metis_tac[] ) >>
  disch_then(qspecl_then[`rd`,`bs with <| code := code' ++ code; pc := next_addr bs.inst_length code'; clock := SOME ck|>`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    fs[invariant_def,LET_THM] >>
    conj_tac >- cheat >> (* RK cheat: type checker guarantees this? *)
    conj_tac >- cheat >> (* RK cheat: type checker guarantees this? *)
    conj_tac >- metis_tac[] >>
    conj_tac >- cheat >> (* RK cheat: type checker guarantees this? *)
    conj_tac >- metis_tac[] >>
    fs[env_rs_def,LET_THM] >>
    HINT_EXISTS_TAC >>
    HINT_EXISTS_TAC >>
    HINT_EXISTS_TAC >>
    simp[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    rfs[] >>
    match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
    map_every qexists_tac[`rd`,`(c,Cs')`,`bs with <|code := code'; pc := next_addr bs.inst_length code'|>`,`bs.refs`,`SOME ck`] >>
    simp[BytecodeTheory.bc_state_component_equality] >>
    conj_tac >- (
      match_mp_tac toBytecodeProofsTheory.Cenv_bs_with_irr >>
      HINT_EXISTS_TAC >> simp[] ) >>
    fs[toBytecodeProofsTheory.Cenv_bs_def,toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def] ) >>

  disch_then kall_tac (* abandon, since cheating *) >>

conj_tac >- (
  (* printed output is correct *)
  cheat ) >>

 Q.PAT_ABBREV_TAC`new_repl_state = update_repl_state X Y Z a b cd de e f` >>
 Q.PAT_ABBREV_TAC`new_repl_fun_state = if X then Y else Z:repl_fun_state` >>
 qmatch_assum_rename_tac`bc_eval X = SOME new_bc_state`["X"] >>
 first_x_assum(qspec_then`STRLEN input_rest`mp_tac) >>
 simp[] >>
 disch_then (Q.SPEC_THEN `input_rest` strip_assume_tac) >> fs [] >>
 pop_assum (ASSUME_TAC o Q.SPECL [`new_repl_state`, `new_bc_state`,`new_repl_fun_state`]) >>
 Cases_on`bc_fetch bs = SOME Stop`>-(
   (* Exception *)
   cheat) >>
 fs[] >>
 (* SO cheat: Because new_bc_state.pc ≠ 1, I think the compiler proof
  * should guarantee that the semantics evaluate to a value *)
 `?envM envE. r = Rval (envM,envE)` by cheat >>
 rw [] >>
 `type_infer_invariants new_repl_state (new_infer_menv ++ infer_menv,
                                  new_infer_cenv ++ infer_cenv,
                                  new_infer_env ++ infer_env)`
                      by metis_tac [type_invariants_pres, invariant_def] >>
 (* SO cheat: The invariant must be preserved.  I'm working on lemmas for
  * the type system and semantics parts of it, but there will be compiler
  * parts too *)

 `invariant new_repl_state new_repl_fun_state new_bc_state` 
             by (simp [invariant_def] >>
                 UNABBREV_ALL_TAC >>
                 fs [update_repl_state_def] >>

                 (* RK cheat: This is the type system part of the invariant *)
                 conj_tac >- cheat (* metis_tac[] *) >>

                 (* SO cheat: This is the env_rs part of the invariant *)
                 cheat) >>
 fs [] >>
 metis_tac [lexer_correct]);

val FST_compile_fake_exp_contab = store_thm("FST_compile_fake_exp_contab",
  ``FST (compile_fake_exp pr rs vs e) = rs.contab``,
  qabbrev_tac`p = compile_fake_exp pr rs vs e` >>
  PairCases_on`p` >> fs[markerTheory.Abbrev_def] >>
  metis_tac[compile_fake_exp_contab])

val good_compile_primitives = prove(
  ``good_contab (FST compile_primitives).contab ∧
    good_cmap [] (cmap (FST compile_primitives).contab) ∧
    {Short ""} = FDOM (cmap (FST compile_primitives).contab) ∧
    (∀id. FLOOKUP (cmap (FST compile_primitives).contab) id = SOME (cmap (FST compile_primitives).contab ' (Short "")) ⇒ id = Short "")
    ``,
  rw[compile_primitives_def] >>
  rw[CompilerTheory.compile_top_def,CompilerTheory.compile_dec_def] >>
  imp_res_tac compile_fake_exp_contab >>
  rw[good_contab_def,intLangExtraTheory.good_cmap_def] >>
  rw[CompilerTheory.init_compiler_state_def,good_contab_def] >>
  rw[IntLangTheory.tuple_cn_def,IntLangTheory.bind_exc_cn_def,IntLangTheory.div_exc_cn_def] >>
  rw[toIntLangProofsTheory.cmap_linv_def,FAPPLY_FUPDATE_THM] >>
  fs[CompilerTheory.compile_top_def,CompilerTheory.compile_dec_def,LET_THM,UNCURRY,FST_compile_fake_exp_contab] >>
  fs[CompilerTheory.init_compiler_state_def,FLOOKUP_UPDATE])

val compile_primitives_menv = store_thm("compile_primitives_menv",
  ``(FST compile_primitives).rmenv = FEMPTY``,
  rw[compile_primitives_def,CompilerTheory.compile_top_def] >>
  rw[CompilerTheory.init_compiler_state_def])

val compile_primitives_renv = store_thm("compile_primitives_renv",
  ``((FST compile_primitives).renv = GENLIST (λi. (FST(EL i init_env), i)) (LENGTH init_env)) ∧
    ((FST compile_primitives).rsz = LENGTH init_env)``,
  rw[compile_primitives_def,CompilerTheory.compile_top_def] >>
  rw[CompilerTheory.init_compiler_state_def] >>
  fs[CompilerTheory.compile_dec_def,LET_THM] >>
  fs[CompilerTheory.compile_fake_exp_def,LET_THM] >>
  rw[CompilerTheory.init_compiler_state_def] >>
  rw[LIST_EQ_REWRITE,SemanticPrimitivesTheory.init_env_def] >>
  `x ∈ count 13` by rw[] >>
  pop_assum mp_tac >> EVAL_TAC >>
  rw[] >> simp[])

(* Use InferSoundTheory.infer_init_thm and TypeSoundTheory.initial_type_sound_invariants *)
val initial_invariant = prove(
  ``invariant init_repl_state initial_repl_fun_state initial_bc_state``,
  rw[invariant_def,initial_repl_fun_state_def,initial_elaborator_state_def,init_repl_state_def,LET_THM] >>
  rw[check_menv_def,initial_inferencer_state_def,check_cenv_def,check_env_def]
  >- EVAL_TAC
  >- (* type_sound_invariants proof *) (
    rw[type_sound_invariants_def] >>
    map_every qexists_tac[`[]`,`[]`] >>
    rw[tenvM_ok_def,tenvC_ok_def,weakC_mods_def,consistent_con_env_def,weakM_def,weakC_def
      ,TypeSoundInvariantsTheory.type_s_def,SemanticPrimitivesTheory.store_lookup_def] >>
    cheat (*
    rw[Once TypeSoundInvariantsTheory.type_v_cases] >>
    rw[SemanticPrimitivesTheory.init_env_def,TypeSystemTheory.init_tenv_def
      ,TypeSystemTheory.bind_tenv_def,LibTheory.bind_def] >>
    rw[Once TypeSoundInvariantsTheory.type_v_cases] >- (
      rw[Once TypeSoundInvariantsTheory.type_v_cases]
      map_every qexists_tac [`Empty`,`Tint`,`Tfn Tint Tint`] >>
      rw[TypeSystemTheory.bind_tenv_def,LibTheory.bind_def,LibTheory.emp_def
        ,terminationTheory.check_freevars_def] >- cheat >>
      rw[Once TypeSystemTheory.type_e_cases] >>
      map_every qexists_tac[`Tint`,`Tint`] >>
      rw[terminationTheory.check_freevars_def] >- cheat >>
      rw[Once TypeSystemTheory.type_e_cases] >>
    *) ) >>
  >- (
    simp[SemanticPrimitivesTheory.init_env_def,semanticsExtraTheory.closed_cases] >>
    simp[SUBSET_DEF] >> metis_tac[] )
  >- (
    simp[SemanticPrimitivesTheory.init_env_def,toIntLangProofsTheory.closed_under_cenv_def] >>
    rw[] >> rw[semanticsExtraTheory.all_cns_def] )
  >- (
    simp[SemanticPrimitivesTheory.init_env_def,compilerProofsTheory.closed_under_menv_def] >>
    simp[semanticsExtraTheory.closed_cases] >>
    simp[SUBSET_DEF] >> metis_tac[] )
  >- (
    fs[SemanticPrimitivesTheory.init_env_def] ) >>

  simp[env_rs_def,good_compile_primitives,compile_primitives_menv,compile_primitives_renv] >>

  simp[MAP_GENLIST,combinTheory.o_DEF] >>
  Q.PAT_ABBREV_TAC`Cenv = env_to_Cenv FEMPTY X Y` >>

  cheat)

val replCorrect = Q.store_thm ("replCorrect",
`!input output.
  (repl_fun input = output) ⇒
  (repl (get_type_error_mask output) input output)`,
rw [repl_fun_def, repl_def] >>
match_mp_tac replCorrect_lem >>
rw[initial_invariant])

val _ = export_theory ();
