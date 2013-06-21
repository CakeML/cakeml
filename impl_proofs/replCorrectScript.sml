open preamble boolSimps;
open lexer_funTheory repl_funTheory replTheory
open lexer_implTheory mmlParseTheory inferSoundTheory BigStepTheory ElabTheory compilerProofsTheory;
open typeSoundTheory weakeningTheory;

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


val invariant_def = Define`
  invariant rs rfs bs ⇔
    rfs.relaborator_state = (rs.type_bindings, rs.ctors)

    (* The type inferencer *)
    ∧ check_menv (FST rfs.rinferencer_state)
    ∧ check_cenv (FST (SND rfs.rinferencer_state))
    ∧ check_env {} (SND (SND rfs.rinferencer_state))
    ∧ (rs.tenvM = convert_menv (FST rfs.rinferencer_state))
    ∧ (rs.tenvC = FST (SND rfs.rinferencer_state))
    ∧ (rs.tenv = (bind_var_list2 (convert_env2 (SND (SND rfs.rinferencer_state))) Empty))

    (* For using the type soundess theorem *)
    ∧ (?tenvS tenvM tenvC. 
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
         weakC tenvC rs.tenvC)

    ∧ ∃rd c. env_rs rs.envM rs.envC rs.envE rfs.rcompiler_state rd (c,rs.store) bs
    (* ∧ rfs.top = ??? *)`

val infer_to_type = Q.prove (
`!rs st bs menv cenv env top new_menv new_cenv new_env st2.
  invariant rs st bs ∧
  (infer_top menv cenv env top init_infer_state =
      (Success (new_menv,new_cenv,new_env),st2)) ∧
  (st.rinferencer_state = (menv,cenv,env))
  ⇒
  type_top rs.tenvM rs.tenvC rs.tenv top
           (convert_menv new_menv) new_cenv (convert_env2 new_env)`,
rw [invariant_def] >>
fs [] >>
rw [] >>
metis_tac [infer_top_sound]);

val type_to_eval = Q.prove (
`!rs st bs top tenvM tenvC tenv.
  invariant rs st bs ∧
  type_top rs.tenvM rs.tenvC rs.tenv top tenvM tenvC tenv ∧
  ¬top_diverges rs.envM rs.envC rs.store rs.envE top ⇒
  ?r st'. (r ≠ Rerr Rtype_error) ∧
      evaluate_top rs.envM rs.envC rs.store rs.envE top (st',r)`,
rw [invariant_def] >>
`num_tvs rs.tenv = 0` by metis_tac [type_v_freevars] >>
`tenvM_ok rs.tenvM` by cheat >>
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
 metis_tac [top_type_soundness_no_sig]);

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
`¬top_diverges rs.envM rs.envC rs.store rs.envE top ⇒
 ∃r st'.
   r ≠ Rerr Rtype_error ∧
   evaluate_top rs.envM rs.envC rs.store rs.envE top (st',r)`
              by metis_tac [type_to_eval] >>

cases_on `bc_eval (install_code code bs)` >>
rw [get_type_error_mask_def] >>
qabbrev_tac`est = st.relaborator_state` >> PairCases_on`est` >>
qabbrev_tac`elab_res = elab_top est0 est1 top0` >> PairCases_on`elab_res` >>
`est0 = rs.type_bindings ∧ est1 = rs.ctors` by fs[invariant_def] >>
rpt BasicProvers.VAR_EQ_TAC >>
fs[elaborate_top_def,LET_THM] >>
qabbrev_tac`el = elab_top rs.type_bindings rs.ctors top0` >> PairCases_on`el` >>
fs[] >> qmatch_assum_rename_tac`xxxxxxxx = top`[] >> BasicProvers.VAR_EQ_TAC >- (

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
     (* SO cheat: The invariant must be preserved.  I'm working on lemmas for
      * the type system and semantics parts of it, but there will be compiler
      * parts too *)
     `invariant new_repl_state new_repl_fun_state new_bc_state` by cheat >>
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

val good_compile_primitives = prove(
  ``good_contab (FST compile_primitives).contab ∧
    good_cmap [] (cmap (FST compile_primitives).contab) (* ∧ not true
    {Short ""} = FDOM (cmap (FST compile_primitives).contab) *)
    ``,
  rw[compile_primitives_def] >>
  rw[CompilerTheory.compile_dec_def] >>
  rw[CompilerTheory.compile_fake_exp_def] >>
  rw[good_contab_def,intLangExtraTheory.good_cmap_def] >>
  rw[CompilerTheory.init_compiler_state_def,good_contab_def] >>
  rw[IntLangTheory.tuple_cn_def,IntLangTheory.bind_exc_cn_def,IntLangTheory.div_exc_cn_def] >>
  rw[toIntLangProofsTheory.cmap_linv_def,FAPPLY_FUPDATE_THM])

val initial_invariant = prove(
  ``invariant init_repl_state initial_repl_fun_state initial_bc_state``,
  rw[invariant_def,initial_repl_fun_state_def,initial_elaborator_state_def,init_repl_state_def] >>
  rw[check_menv_def,initial_inferencer_state_def,check_cenv_def,check_env_def]
  >- EVAL_TAC >>

  (* env_rs proof: *)
  simp[env_rs_def,good_compile_primitives] >>

  cheat)

val replCorrect = Q.store_thm ("replCorrect",
`!input output.
  (repl_fun input = output) ⇒
  (repl (get_type_error_mask output) input output)`,
rw [repl_fun_def, repl_def] >>
match_mp_tac replCorrect_lem >>
rw[initial_invariant])

val _ = export_theory ();
