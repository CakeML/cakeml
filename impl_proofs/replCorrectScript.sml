open preamble boolSimps;
open lexer_funTheory repl_funTheory replTheory
open lexer_implTheory mmlParseTheory inferSoundTheory BigStepTheory ElabTheory compilerProofsTheory;
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

(* For using the type soundess theorem, we have to know there are good
 * constructor and module type environments that don't have bits hidden by a
 * signature. *)
val type_sound_invariants_def = Define `
type_sound_invariants rs ⇔
  ?tenvS tenvM tenvC. 
    tenvM_ok tenvM ∧ 
    tenvC_ok tenvC ∧
    tenvC_ok rs.tenvC ∧
    weakC_mods tenvC rs.tenvC ⊆ set (MAP SOME (MAP FST tenvM)) ∧
    (MAP FST tenvM = MAP FST rs.tenvM) ∧
    consistent_mod_env tenvS tenvC rs.envM tenvM ∧
    consistent_con_env rs.envC tenvC ∧
    type_env tenvM tenvC tenvS rs.envE rs.tenv ∧
    type_s tenvM tenvC tenvS rs.store ∧
    weakM tenvM rs.tenvM ∧
    weakC tenvC rs.tenvC`;

val invariant_def = Define`
  invariant rs rfs bs ⇔
    rfs.relaborator_state = (rs.type_bindings, rs.ctors)

    ∧ type_infer_invariants rs rfs.rinferencer_state 
    ∧ type_sound_invariants rs

    ∧ ∃rd c. env_rs rs.envM rs.envC rs.envE rfs.rcompiler_state rd (c,rs.store) bs
    (* ∧ rfs.top = ??? *)`;

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

val infer_to_type = Q.prove (
`!rs st bs menv cenv env top new_menv new_cenv new_env st2.
  invariant rs st bs ∧
  (infer_top menv cenv env top init_infer_state =
      (Success (new_menv,new_cenv,new_env),st2)) ∧
  (st.rinferencer_state = (menv,cenv,env))
  ⇒
  tenvM_ok (convert_menv menv) ∧
  type_top rs.tenvM rs.tenvC rs.tenv top
           (convert_menv new_menv) new_cenv (convert_env2 new_env)`,
rw [invariant_def, type_infer_invariants_def, type_sound_invariants_def] >>
fs [] >>
rw [] >>
metis_tac [infer_top_sound, check_menv_to_tenvM_ok]);

val type_to_eval = Q.prove (
`!rs st bs top tenvM tenvC tenv el0 el1.
  invariant rs st bs ∧
  tenvM_ok rs.tenvM ∧
  type_top rs.tenvM rs.tenvC rs.tenv top tenvM tenvC tenv ∧
  ¬top_diverges rs.envM rs.envC rs.store rs.envE top ⇒
  ?r st'. (r ≠ Rerr Rtype_error) ∧
      evaluate_top rs.envM rs.envC rs.store rs.envE top (st',r) ∧
      type_sound_invariants (update_repl_state rs el0 el1 tenvM tenvC tenv st' r)`,
rw [invariant_def, type_sound_invariants_def] >>
`num_tvs rs.tenv = 0` by metis_tac [type_v_freevars] >>
`?tenvM'' tenvC'' tenv''.
   type_top_ignore_sig rs.tenvM rs.tenvC rs.tenv top tenvM'' tenvC'' tenv'' ∧
   tenvC_ok tenvC'' ∧
   tenvM_ok tenvM'' ∧
   (MAP FST tenvM'' = MAP FST tenvM) ∧
   weakM tenvM'' tenvM ∧
   weakC tenvC'' tenvC`
         by metis_tac [type_top_type_top_ignore_sig] >>
`type_top_ignore_sig tenvM' tenvC' rs.tenv top tenvM'' tenvC'' tenv''`
         by metis_tac [type_top_ignore_sig_weakening] >>
rw [update_repl_state_def] >>
`∃r st' tenvS'.
 r ≠ Rerr Rtype_error ∧
 evaluate_top rs.envM rs.envC rs.store rs.envE top (st',r) ∧
 store_type_extension tenvS tenvS' ∧
 ∀menv' cenv' env'.
   r = Rval (menv',cenv',env') ⇒
   consistent_mod_env tenvS' (tenvC'' ++ tenvC')
     (menv' ++ rs.envM) (tenvM'' ++ tenvM') ∧
   consistent_con_env (cenv' ++ rs.envC) (tenvC'' ++ tenvC') ∧
   disjoint_env tenvC' tenvC'' ∧
   type_s (tenvM'' ++ tenvM') (tenvC'' ++ tenvC') tenvS' st' ∧
   type_env (tenvM'' ++ tenvM') (tenvC'' ++ tenvC') tenvS'
     (env' ++ rs.envE) (bind_var_list2 tenv'' rs.tenv)`
            by metis_tac [top_type_soundness_no_sig] >>
qexists_tac `r` >>
`(?err. r = Rerr err) ∨ (?menv' cenv' env'. r = Rval (menv',cenv',env'))` 
              by (cases_on `r` >>
                  metis_tac [pair_CASES]) >>
rw [] >>
qexists_tac `st'` >>
rw [] >|
[MAP_EVERY qexists_tac [`tenvS'`, `tenvM'`, `tenvC'`] >>
     rw [] >|
     [metis_tac [weakC_refl, consistent_mod_env_weakening, store_type_extension_weakS],
      metis_tac [weakC_refl, weakM_refl, type_v_weakening, store_type_extension_weakS],
      (* SO cheat: We need to strengthen type soundness to know that the store
       * is well typed after an exception since we can continue on to the next
       * input expression *)
      cheat],
 MAP_EVERY qexists_tac [`tenvS'`, `tenvM'' ++ tenvM'`, `merge tenvC'' tenvC'`] >>
     rw [] >|
     [fs [tenvM_ok_def],
      rw [tenvC_ok_merge] >>
          metis_tac [disjoint_env_def, DISJOINT_SYM],
      rw [tenvC_ok_merge, GSYM LibTheory.merge_def] >>
          (* SO cheat: TODO *)
          cheat,
      (* SO cheat: TODO *)
      cheat,
      metis_tac [LibTheory.merge_def],
      metis_tac [LibTheory.merge_def],
      (* SO cheat: TODO *)
      cheat,
      metis_tac [LibTheory.merge_def],
      (* SO cheat: TODO *)
      cheat,
      (* SO cheat: TODO *)
      cheat]]);

val type_invariants_pres = Q.prove (
`!rs rfs.
  type_infer_invariants rs (infer_menv,infer_cenv,infer_env) ∧
  infer_top infer_menv infer_cenv infer_env top init_infer_state = 
          (Success (new_infer_menv,new_infer_cenv,new_infer_env), infer_st2)
  ⇒
  type_infer_invariants (update_repl_state rs el0 el1 (convert_menv new_infer_menv) new_infer_cenv (convert_env2 new_infer_env) st' 
                                     (Rval (envM,envC,envE)))
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

val printer_not_confused = Q.prove (
`!ds cs stack. simple_printer ds cs stack ≠ "<type error>"`,
induct_on `ds` >>
rw [PrinterTheory.simple_printer_def] >>
cases_on `h` >>
rw []);

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
rw [Once ast_repl_cases, parse_elaborate_infertype_compile_def, parser_correct,
    get_type_error_mask_def] >>
`?error_msg next_repl_run_infer_state.
  infertype_top st.rinferencer_state top = Failure error_msg ∨ 
  infertype_top st.rinferencer_state top = Success next_repl_run_infer_state`
         by (cases_on `infertype_top st.rinferencer_state top` >>
             metis_tac []) >>
rw [get_type_error_mask_def] >-
((* A type error *)
 `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
     metis_tac [lexer_correct]) >>
`?new_bc_success new_bc_failure code. compile_top st.rcompiler_state top = (new_bc_success, new_bc_failure, code)`
         by (cases_on `compile_top st.rcompiler_state top` >>
             Cases_on`r` >>
             metis_tac []) >>
rw [] >>
`?infer_menv infer_cenv infer_env. 
  st.rinferencer_state = (infer_menv,infer_cenv,infer_env)`
            by metis_tac [pair_CASES] >>
fs [infertype_top_def] >>
rw [] >>
`?res infer_st2. infer_top infer_menv infer_cenv infer_env top init_infer_state = (res,infer_st2)`
        by metis_tac [pair_CASES] >>
fs [] >>
cases_on `res` >>
rw [] >>
fs [] >>
`∃new_infer_menv new_infer_cenv new_infer_env.  a = (new_infer_menv,new_infer_cenv,new_infer_env)`
        by metis_tac [pair_CASES] >>
fs [] >>
rw [] >>
imp_res_tac infer_to_type >>

cases_on `bc_eval (install_code code bs)` >>
rw [get_type_error_mask_def] >>
qabbrev_tac`est = st.relaborator_state` >> PairCases_on`est` >>
qabbrev_tac`elab_res = elab_top est0 est1 top0` >> PairCases_on`elab_res` >>
`est0 = rs.type_bindings ∧ est1 = rs.ctors` by fs[invariant_def] >>
rpt BasicProvers.VAR_EQ_TAC >>
fs[elaborate_top_def,LET_THM] >>
qabbrev_tac`el = elab_top rs.type_bindings rs.ctors top0` >> PairCases_on`el` >>
fs[] >> 

`rs.tenvM = convert_menv infer_menv` by fs [invariant_def, type_infer_invariants_def] >>
`¬top_diverges rs.envM rs.envC rs.store rs.envE top ⇒
 ∃r st'.
   r ≠ Rerr Rtype_error ∧
   evaluate_top rs.envM rs.envC rs.store rs.envE top (st',r) ∧
   type_sound_invariants (update_repl_state rs el0 el1 (convert_menv new_infer_menv) 
                         new_infer_cenv (convert_env2 new_infer_env) st' r)`
              by metis_tac [type_to_eval] >>


qmatch_assum_rename_tac`xxxxxxxx = top`[] >> BasicProvers.VAR_EQ_TAC >- (

  (* Divergence *)
    MAP_EVERY qexists_tac [`convert_menv new_infer_menv`,`new_infer_cenv`,`convert_env2 new_infer_env`] >>
    rw [] >>


  cheat ) >>

disj1_tac >>
(* SO cheat: I think the semantics can't diverge because (bc_eval install_code
 * code bs) = SOME x).  I think this should come from the compiler proof. *)
`¬top_diverges rs.envM rs.envC rs.store rs.envE top` by cheat >>
fs [] >>
(* SO cheat: We need to prove that lex_until_top_level_semicolon must consume
 * some input *)
`STRLEN input_rest < STRLEN input` by cheat >>
rw [update_state_def, print_fun_def] >>
MAP_EVERY qexists_tac [`convert_menv new_infer_menv`, 
                       `new_infer_cenv`, 
                       `convert_env2 new_infer_env`,
                       `st'`, 
                       `r`] >>
rw [] >|
[(* Non-type errors don't print "<type error>" *)
 cases_on `top` >>
     rw [printer_not_confused],
 (* SO cheat: This is the case for the delaration evaluating to a value.  We
  * must prove that the right thing is printed.  I think this should come from
  * the compiler correctness proof *)
 cheat,
 qabbrev_tac `new_repl_state = update_repl_state rs el0 el1 (convert_menv new_infer_menv) 
                                                    new_infer_cenv (convert_env2 new_infer_env) 
                                                    st' r` >>
     qabbrev_tac `new_repl_fun_state = 
          <|relaborator_state :=
             (elab_res0 ++ rs.type_bindings,elab_res1 ++ rs.ctors);
           rinferencer_state :=
             (new_infer_menv ++ infer_menv,new_infer_cenv ++ infer_cenv,
              new_infer_env ++ infer_env);
           rcompiler_state := new_bc_success; top := top|>` >>
     qabbrev_tac `new_bc_state = (x with stack := TL x.stack)` >>
     res_tac >>
     pop_assum (ASSUME_TAC o Q.SPEC `input_rest`) >>
     fs [] >>
     pop_assum (ASSUME_TAC o Q.SPECL [`new_repl_state`, `new_repl_fun_state`, `new_bc_state`]) >>
     (* SO cheat: Because HD x.stack = Number 0, I think the compiler proof
      * should guarantee that the semantics evaluate to a value *)
     `?v. r = Rval (envM,envC,envE)` by cheat >>
     rw [] >>
     `type_infer_invariants new_repl_state (new_infer_menv ++ infer_menv,
                                      new_infer_cenv ++ infer_cenv,
                                      new_infer_env ++ infer_env)`
                          by metis_tac [type_invariants_pres, invariant_def] >>
     
     (* SO cheat: The invariant must be preserved.  I'm working on lemmas for
      * the type system and semantics parts of it, but there will be compiler
      * parts too *)
     `invariant new_repl_state new_repl_fun_state new_bc_state` 
                 by (rw [invariant_def] >>
                     UNABBREV_ALL_TAC >>
                     fs [update_repl_state_def] >-
                     metis_tac [] >>
                     (* SO cheat: This is the env_rs part of the invariant *)
                     cheat) >>
     fs [] >>
     metis_tac [lexer_correct],
 (* SO cheat: The case where an exception makes it to the top level.
  * The goal is "Exception" = print_result r, but print result tells you what
  * exception you got as print_result (Rerr (Rraise e)) = STRCAT (STRCAT "raise
  * " (print_error e)).  I think the implementation needs to be updated to match
  * the semantics, but it would be possible to change the semantics to not tell
  * you which exception. *)
 cheat,
 (* SO cheat: The exception case, but for the induction.  Because HD x.stack ≠
 * Number 0, I think the compiler proof should let us conclude that the
 * semantics raises an exception *)
 `?err. r = Rerr err` by cheat >>
     rw [update_repl_state_def] >>
     (* SO cheat: This looks false.  The implementation appears to update the
      * inferencer and elaborator state even though an error was raised.  The
      * semantics doesn't update the state of the bindings, it only updates the
      * store. *)
     cheat]);

     (*
Cases_on`top0` >- (
   (* Module *)
  cheat ) >>

fs[elab_top_def,LET_THM] >>
qabbrev_tac`p = elab_dec NONE rs.type_bindings rs.ctors a` >>
PairCases_on`p` >> fs[] >>
fs[markerTheory.Abbrev_def] >>
rpt BasicProvers.VAR_EQ_TAC >>
fs[compile_top_def] >>

simp[Once evaluate_prog_cases] >>
fs[elaborate_top_def,LET_THM] >>
cheat

)
*)

val FST_compile_fake_exp_contab = store_thm("FST_compile_fake_exp_contab",
  ``FST (compile_fake_exp rs vs e) = rs.contab``,
  qabbrev_tac`p = compile_fake_exp rs vs e` >>
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

val initial_invariant = prove(
  ``invariant init_repl_state initial_repl_fun_state initial_bc_state``,
  rw[invariant_def,initial_repl_fun_state_def,initial_elaborator_state_def,init_repl_state_def] >>
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

  (* env_rs proof: *)
  simp[env_rs_def,good_compile_primitives,compile_primitives_menv,compile_primitives_renv] >>

  simp[MAP_GENLIST,combinTheory.o_DEF] >>
  Q.PAT_ABBREV_TAC`Cenv = env_to_Cenv FEMPTY X Y` >>
  CONV_TAC(RESORT_EXISTS_CONV(List.rev))>>

  cheat)

val replCorrect = Q.store_thm ("replCorrect",
`!input output.
  (repl_fun input = output) ⇒
  (repl (get_type_error_mask output) input output)`,
rw [repl_fun_def, repl_def] >>
match_mp_tac replCorrect_lem >>
rw[initial_invariant])

val _ = export_theory ();
