(*
  Verification of the function (called repl) that implements the REPL
*)
Theory replProof
Ancestors
  semanticsProps backendProof x64_configProof compiler64Prog
  evaluate semanticPrimitives ml_translator repl_types
  repl_check_and_tweak repl_init
Libs
  preamble

val _ = (max_print_depth := 12);

Definition compiler_inst_def:
  compiler_inst c = (λ(x,y,z).
                do
                  cfg <- v_fun_abs 𝕌(:inc_config) BACKEND_INC_CONFIG_v y;
                  (cfg2,bs,ws) <- compile_inc_progs_for_eval c (x,cfg,z);
                  SOME (BACKEND_INC_CONFIG_v cfg2,bs,ws)
                od)
End

Theorem no_closures_IMP_concrete_v:
  (∀v. no_closures v ⇒ concrete_v v) ∧
  (∀v. EVERY no_closures v ⇒ concrete_v_list v)
Proof
  ho_match_mp_tac concrete_v_ind \\ rw []
  \\ Cases_on ‘v’
  \\ fs [ml_translatorTheory.no_closures_def, SF ETA_ss, concrete_v_def]
QED

Theorem EqualityType_concrete_v[local]:
  a x v ∧ EqualityType a ⇒ concrete_v v
Proof
  fs [ml_translatorTheory.EqualityType_def]
  \\ rw [] \\ res_tac \\ imp_res_tac no_closures_IMP_concrete_v
QED

val EqualityType_LIST_TYPE_AST_DEC_TYPE =
  decProgTheory.EqualityType_LIST_TYPE_AST_DEC_TYPE;

val EqualityType_BACKEND_INC_CONFIG_TYPE =
  decodeProgTheory.EqualityType_BACKEND_INC_CONFIG_TYPE;

Theorem concrete_v_decs:
  LIST_TYPE AST_DEC_TYPE decs v ⇒ concrete_v v
Proof
  rw [] \\ drule EqualityType_concrete_v
  \\ fs [EqualityType_LIST_TYPE_AST_DEC_TYPE]
QED

Theorem concrete_v_inc_config:
  BACKEND_INC_CONFIG_TYPE c v ⇒ concrete_v v
Proof
  rw [] \\ drule EqualityType_concrete_v
  \\ fs [EqualityType_BACKEND_INC_CONFIG_TYPE]
QED

Theorem LIST_TYPE_AST_DEC_IMP:
  LIST_TYPE AST_DEC_TYPE decs decs_v ⇒
  ∀x. LIST_v AST_DEC_v x = decs_v ⇔ x = decs
Proof
  assume_tac EqualityType_LIST_TYPE_AST_DEC_TYPE
  \\ rw []
  \\ ‘IsTypeRep (LIST_v AST_DEC_v) (LIST_TYPE AST_DEC_TYPE)’ by
      (irule decProgTheory.IsTypeRep_LIST_v
       \\ fs [decProgTheory.IsTypeRep_AST_DEC_v])
  \\ fs [ml_translatorTheory.IsTypeRep_def]
  \\ fs [ml_translatorTheory.EqualityType_def]
QED

Theorem BACKEND_INC_CONFIG_IMP:
  BACKEND_INC_CONFIG_TYPE c v ⇒
  ∀x. BACKEND_INC_CONFIG_v x = v ⇔ x = c
Proof
  assume_tac EqualityType_BACKEND_INC_CONFIG_TYPE
  \\ rw [] \\ assume_tac decodeProgTheory.IsTypeRep_BACKEND_INC_CONFIG_v
  \\ fs [ml_translatorTheory.IsTypeRep_def]
  \\ fs [ml_translatorTheory.EqualityType_def]
QED

Theorem v_fun_abs_BACKEND_INC_CONFIG_v:
  BACKEND_INC_CONFIG_TYPE s1 s1_v ⇒
  v_fun_abs 𝕌(:inc_config) BACKEND_INC_CONFIG_v s1_v = SOME s1
Proof
  fs [source_evalProofTheory.v_rel_abs,BACKEND_INC_CONFIG_IMP]
  \\ strip_tac \\ imp_res_tac BACKEND_INC_CONFIG_IMP \\ fs []
QED

Theorem v_to_word64_list_thm:
  ∀ws ws_v. LIST_TYPE WORD ws ws_v ⇒ v_to_word64_list ws_v = SOME ws
Proof
  Induct \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word64_list_def,
                v_to_list_def,list_type_num_def]
  THEN1 EVAL_TAC \\ rw []
  \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word64_list_def,
         v_to_list_def,list_type_num_def]
  \\ res_tac \\ fs []
  \\ gvs [AllCaseEqs(),PULL_EXISTS]
  \\ res_tac \\ fs []
  \\ simp [Once maybe_all_list_def,AllCaseEqs()]
  \\ gvs [ml_translatorTheory.WORD_def]
  \\ EVAL_TAC
QED

Theorem v_to_word8_list_thm:
  ∀bs bs_v. LIST_TYPE WORD bs bs_v ⇒ v_to_word8_list bs_v = SOME bs
Proof
  Induct \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word8_list_def,
                v_to_list_def,list_type_num_def]
  THEN1 EVAL_TAC \\ rw []
  \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word8_list_def,
         v_to_list_def,list_type_num_def]
  \\ res_tac \\ fs []
  \\ gvs [AllCaseEqs(),PULL_EXISTS]
  \\ res_tac \\ fs []
  \\ simp [Once maybe_all_list_def,AllCaseEqs()]
  \\ gvs [ml_translatorTheory.WORD_def]
  \\ EVAL_TAC
QED

Theorem evaluate_Eval:
  (st:'ffi semanticPrimitives$state).eval_state = SOME (EvalDecs s) ∧
  compile_inc_progs_for_eval x64_config (id1,s1,decs) = SOME (s2,bs,ws) ∧
  s.compiler = compiler_inst x64_config ∧
  s.compiler_state = s1_v ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v AST_DEC_v) ⇒
  LIST_TYPE AST_DEC_TYPE decs decs_v ∧
  BACKEND_INC_CONFIG_TYPE s1 s1_v ∧
  BACKEND_INC_CONFIG_TYPE s2 s2_v ∧
  LIST_TYPE WORD ws ws_v ∧
  LIST_TYPE WORD bs bs_v ∧
  nsLookup env.v (Short «env») = SOME (Env env1 id1) ⇒
  nsLookup env.v (Short «decs») = SOME decs_v ⇒
  nsLookup env.v (Short «s1») = SOME s1_v ⇒
  nsLookup env.v (Short «s2») = SOME s2_v ⇒
  nsLookup env.v (Short «bs») = SOME bs_v ⇒
  nsLookup env.v (Short «ws») = SOME ws_v ⇒
  decs_allowed decs ⇒
  evaluate st env [App Eval [Var (Short «env»);  Var (Short «s1»);
                             Var (Short «decs»); Var (Short «s2»);
                             Var (Short «bs»);   Var (Short «ws»)]] =
    let st = (st with eval_state := SOME (EvalDecs
                   (add_decs_generation (s with compiler_state := s2_v)))) in
      if st.clock = 0 then (st, Rerr (Rabort Rtimeout_error)) else
        case evaluate_decs (dec_clock st) env1 decs of
        | (st2,Rval env2) =>
            (case declare_env st2.eval_state (extend_dec_env env2 env1) of
               NONE => (st2,Rerr (Rabort Rtype_error))
             | SOME (x,es2) =>
               (st2 with
                eval_state :=
                  reset_env_generation (SOME (EvalDecs s)) es2,Rval [x]))
        | (st2,Rerr (Rraise v7)) =>
            (st2 with
             eval_state :=
               reset_env_generation (SOME (EvalDecs s)) st2.eval_state,
             Rerr (Rraise v7))
        | (st2,Rerr (Rabort a)) => (st2,Rerr (Rabort a))
Proof
  fs [evaluate_def,do_eval_res_def]
  \\ fs [do_eval_def]
  \\ rpt strip_tac
  \\ ‘v_fun_abs decs_allowed (LIST_v AST_DEC_v) decs_v = SOME decs’ by
   (fs [source_evalProofTheory.v_rel_abs]
    \\ drule LIST_TYPE_AST_DEC_IMP \\ fs []
    \\ DEEP_INTRO_TAC some_intro \\ fs [IN_DEF])
  \\ ‘compiler_agrees (compiler_inst x64_config) (id1,s1_v,decs) (s2_v,bs_v,ws_v)’ by
   (fs [compiler_agrees_def,compiler_inst_def]
    \\ imp_res_tac v_fun_abs_BACKEND_INC_CONFIG_v \\ fs []
    \\ imp_res_tac v_to_word64_list_thm
    \\ imp_res_tac v_to_word8_list_thm
    \\ imp_res_tac BACKEND_INC_CONFIG_IMP
    \\ imp_res_tac concrete_v_inc_config \\ fs [])
  \\ fs [concrete_v_decs,SF SFY_ss]
QED

val evaluate_Con = SIMP_CONV std_ss [evaluate_def,do_con_check_def,build_conv_def]
  “evaluate st env [Con NONE xs]”

val evaluate_Var = SIMP_CONV std_ss [evaluate_def,do_con_check_def]
  “evaluate st env [Var n]”

val evaluate_Lit = SIMP_CONV std_ss [evaluate_def]
  “evaluate st env [Lit n]”

val evaluate_list = List.take (evaluate_def |> CONJUNCTS,2) |> LIST_CONJ

val evaluate_App_Opapp = SIMP_CONV std_ss [evaluate_def,REVERSE_DEF,APPEND]
  “evaluate st env [App Opapp [f;x]]”

Theorem Arrow_IMP:
  ∀x v (s:'ffi semanticPrimitives$state).
    (a --> b) (f:'a -> 'b) vv ∧ a x v ⇒
    ∃env exp junk u ck s1 res.
      do_opapp [vv; v] = SOME (env,exp) ∧ b (f x) u ∧
      evaluate s env [exp] = (s1,res) ∧
      (res ≠ Rerr (Rabort Rtimeout_error) ⇒
        s1 = s with <| clock := s.clock - ck; refs := s.refs ++ junk |> ∧
        res = Rval [u])
Proof
  rw [Arrow_def,
      ml_translatorTheory.AppReturns_def]
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘s.refs’ strip_assume_tac)
  \\ fs [] \\ pop_assum $ irule_at Any
  \\ drule ml_translatorTheory.evaluate_empty_state_IMP
  \\ simp [ml_progTheory.eval_rel_def] \\ strip_tac
  \\ drule evaluatePropsTheory.evaluate_set_init_clock
  \\ fs [] \\ disch_then (qspec_then ‘s.clock’ strip_assume_tac)
  \\ rw [] \\ ‘(s with clock := s.clock) = (s:'ffi semanticPrimitives$state)’ by
               fs [semanticPrimitivesTheory.state_component_equality]
  \\ gvs []
  \\ gvs [semanticPrimitivesTheory.state_component_equality]
  \\ qspecl_then [‘s’,‘env’,‘[exp]’] mp_tac
       (evaluatePropsTheory.is_clock_io_mono_evaluate |> CONJUNCT1)
  \\ fs [evaluatePropsTheory.is_clock_io_mono_def,LESS_EQ_EXISTS]
  \\ strip_tac \\ fs []
  \\ qexists_tac ‘p’ \\ fs []
QED

Overload eval_res_stamp[local] =
  (COMPILER64PROG_EVAL_RES_TYPE_def
   |> concl |> find_term (can (match_term “TypeStamp _ _”)) |> rand);

Theorem evaluate_eval:
  ∀(st:'ffi semanticPrimitives$state).
    st.eval_state = SOME (EvalDecs s) ∧
    s.compiler = compiler_inst x64_config ∧
    s.compiler_state = s1_v ∧
    s.decode_decs = v_fun_abs decs_allowed (LIST_v AST_DEC_v) ∧
    s.env_id_counter = (cur_gen1,next_id1,next_gen1) ∧
    env_v = Env env1 (env_id,0) ∧ decs_allowed decs ∧
    nsLookup env.v (Short eval_str) = SOME eval_v ⇒
    nsLookup env.v (Short arg_str) =
    SOME (Conv NONE [Conv NONE [s1_v; Litv (IntLit (&next_gen))];
                     Conv NONE [env_v; Litv (IntLit (&env_id))];
                     decs_v]) ∧
    BACKEND_INC_CONFIG_TYPE s1 s1_v ∧
    LIST_TYPE AST_DEC_TYPE decs decs_v ∧
    (∀ck junk st1 res. evaluate_decs (st with
                                         <|clock := st.clock − ck; refs := st.refs ++ junk;
                                           eval_state := NONE |>) env1
                                     decs = (st1,res) ⇒ res ≠ Rerr (Rabort Rtype_error)) ⇒
    ∃res s1 ck msg junk.
      evaluate st env [App Opapp [Var (Short eval_str); Var (Short arg_str)]] = (s1,res) ∧
      (res ≠ Rerr (Rabort Rtimeout_error) ⇒
       res = Rval
             [Conv (SOME (TypeStamp «Compile_error» eval_res_stamp))
                   [Litv (StrLit msg)]] ∧
       s1 = st with <|clock := st.clock − ck; refs := st.refs ++ junk|> ∨
       (∃f. res = Rerr (Rabort (Rffi_error f))) ∨
       (∃exn st7 ck1 ck2 s2_v s2.
          evaluate_decs (st with
                            <|clock := st.clock − ck1; refs := st.refs ++ junk;
                              eval_state := NONE|>) env1 decs = (st7,Rerr (Rraise exn)) ∧
          BACKEND_INC_CONFIG_TYPE s2 s2_v ∧
          res = Rval [Conv (SOME (TypeStamp «Eval_exn» eval_res_stamp))
                           [exn; Conv NONE [s2_v; Litv (IntLit (&next_gen + 1))]]] ∧
          s1 = st7 with <| clock := st7.clock - ck2 ;
                           eval_state := SOME (EvalDecs
                                               (s with <|compiler_state := s2_v;
                                                         env_id_counter := (cur_gen1,next_id1,next_gen1 + 1)|>)) |>) ∨
       (∃env2 st7 ck1 ck2 s2_v s2.
          evaluate_decs (st with
                            <|clock := st.clock − ck1; refs := st.refs ++ junk;
                              eval_state := NONE|>) env1 decs = (st7,Rval env2) ∧
          BACKEND_INC_CONFIG_TYPE s2 s2_v ∧
          res = Rval [Conv (SOME (TypeStamp «Eval_result» eval_res_stamp))
                           [Conv NONE
                                 [Env (extend_dec_env env2 env1) (next_gen1,0);
                                  Litv (IntLit (&next_gen))];
                            Conv NONE [s2_v; Litv (IntLit (&next_gen + 1))]]] ∧
          s1 = st7 with <| clock := st7.clock - ck2 ;
                           eval_state := SOME (EvalDecs
                                               (s with <|compiler_state := s2_v;
                                                         env_id_counter := (cur_gen1,next_id1,next_gen1 + 1)|>)) |>))
Proof
  rpt strip_tac \\ gvs []
  \\ simp [evaluate_def,eval_v_def]
  \\ simp [do_opapp_def,find_recfun_def]
  \\ IF_CASES_TAC \\ simp []
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def]
  \\ simp [Once evaluate_def,astTheory.pat_bindings_def,pmatch_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* let compiler_for_eval *)
  \\ simp [Once evaluate_def,namespaceTheory.nsOptBind_def]
  \\ simp [evaluate_App_Opapp,evaluate_Var,build_rec_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rename [‘do_opapp [compiler64prog_compiler_for_eval_v;_]’]
  \\ qmatch_goalsub_abbrev_tac ‘do_opapp [_; arg_v]’
  \\ ‘PAIR_TYPE (PAIR_TYPE NUM NUM)
      (PAIR_TYPE BACKEND_INC_CONFIG_TYPE (LIST_TYPE AST_DEC_TYPE))
      ((env_id,0),(s1,decs)) arg_v’ by
    fs [Abbr‘arg_v’,ml_translatorTheory.PAIR_TYPE_def]
  \\ assume_tac compiler64prog_compiler_for_eval_v_thm
  \\ drule_all Arrow_IMP
  \\ fs [dec_clock_def]
  \\ disch_then (qspec_then ‘(st with clock := st.clock − 2)’ strip_assume_tac)
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs []
  (* case ... of None => ... *)
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def,evaluate_Var]
  \\ Cases_on ‘compiler_for_eval ((env_id,0),s1,decs)’
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [semanticPrimitivesTheory.same_ctor_def]
  THEN1
   (simp [Once evaluate_def,astTheory.pat_bindings_def,pmatch_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ fs [semanticPrimitivesTheory.same_ctor_def]
    \\ fs [evaluate_def,do_con_check_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ fs [build_conv_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ metis_tac [])
  (* Some case *)
  \\ simp [Once evaluate_def,astTheory.pat_bindings_def,pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [semanticPrimitivesTheory.same_ctor_def]
  \\ Cases_on ‘x’ \\ fs [ml_translatorTheory.PAIR_TYPE_def]
  \\ simp [Once evaluate_def,astTheory.pat_bindings_def,pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [] \\ gvs []
  \\ rename [‘PAIR_TYPE _ _ rrr _’] \\ PairCases_on ‘rrr’ \\ fs [PAIR_TYPE_def]
  \\ gvs [pmatch_def]
  (* entering Handle *)
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* Opapp eval_prim *)
  \\ simp [evaluate_App_Opapp,evaluate_Var,build_rec_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rename [‘do_opapp [eval_prim_v;
                        Conv NONE [_; _; decs_v; s2_v; bs_v; ws_v]]’]
  \\ simp [do_opapp_def,eval_prim_v_def]
  \\ IF_CASES_TAC THEN1 fs []
  \\ fs [dec_clock_def]
  (* Mat inside eval_prim *)
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit,pmatch_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit,pmatch_def]
  \\ fs [astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st4 env4’
  \\ ‘st4.eval_state = SOME (EvalDecs s)’ by fs [Abbr‘st4’]
  \\ fs [compiler_for_eval_def]
  \\ drule_then drule evaluate_Eval
  \\ disch_then drule \\ gvs []
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [‘env1’,‘env4’] mp_tac)
  \\ impl_tac
  THEN1 (unabbrev_all_tac \\ fs [])
  \\ strip_tac \\ fs []
  \\ pop_assum kall_tac
  \\ IF_CASES_TAC THEN1 fs []
  \\ fs [dec_clock_def]
  \\ fs [Abbr‘st4’]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate_decs st5’
  \\ ‘∃st6 res6. evaluate_decs (st5 with eval_state := NONE) env1 decs =
                 (st6,res6)’ by metis_tac [PAIR]
  \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> last)
  \\ disch_then (qspec_then ‘SOME (EvalDecs
                                   (add_decs_generation (s with compiler_state := s2_v)))’ mp_tac)
  \\ impl_keep_tac THEN1 (fs [] \\ unabbrev_all_tac \\ fs [] \\ metis_tac [])
  \\ fs [Abbr‘st5’] \\ strip_tac \\ pop_assum kall_tac
  (* cases on res of evaluated decs *)
  \\ reverse (Cases_on ‘res6’) \\ fs []
  THEN1 (* Rerr case *)
   (Cases_on ‘∃a. e = Rabort a’
    THEN1 (gvs [] \\ Cases_on ‘a’ \\ fs [])
    \\ ‘∃exn. e = Rraise exn’ by (Cases_on ‘e’ \\ fs []) \\ gvs []
    \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def,astTheory.pat_bindings_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ simp [evaluate_App_Opapp,evaluate_Var,build_rec_env_def,evaluate_Lit]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ simp [do_opapp_def,mlbasicsProgTheory.plus_v_def]
    \\ IF_CASES_TAC THEN1 fs []
    \\ fs [dec_clock_def]
    \\ simp [Once evaluate_def]
    \\ IF_CASES_TAC THEN1 fs []
    \\ fs [dec_clock_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,do_app_def,do_arith_def,check_type_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,do_con_check_def,build_conv_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
    \\ fs [add_decs_generation_def,reset_env_generation_def]
    \\ qexists_tac ‘junk’ \\ fs []
    \\ first_x_assum $ irule_at $ Pos hd
    \\ first_x_assum $ irule_at $ Pos hd
    \\ qexists_tac ‘2’ \\ fs []
    \\ simp [semanticPrimitivesTheory.state_component_equality])
  \\ fs [declare_env_def,add_decs_generation_def,reset_env_generation_def]
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def,astTheory.pat_bindings_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [evaluate_App_Opapp,evaluate_Var,build_rec_env_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [do_opapp_def,mlbasicsProgTheory.plus_v_def]
  \\ IF_CASES_TAC THEN1 fs []
  \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def]
  \\ IF_CASES_TAC THEN1 fs []
  \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_app_def,do_arith_def,check_type_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_con_check_def,build_conv_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_con_check_def,build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ qexists_tac ‘junk’ \\ fs []
  \\ first_x_assum $ irule_at $ Pos hd
  \\ first_x_assum $ irule_at $ Pos hd
  \\ qexists_tac ‘2’ \\ fs []
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED

val _ = map Parse.hide ["types","types_v","parse","parse_v"];

Theorem repl_types_alt:
  repl_types T (ffi,rs) (types,s,env) ∧
  infertype_prog_inc types decs = Success new_t ⇒
  evaluate_decs s env decs ≠ (new_s,Rerr (Rabort Rtype_error))
Proof
  rw [] \\ imp_res_tac repl_types_thm \\ fs []
QED

Theorem repl_types_clock_refs:
  repl_types T (ffi,rs) (types,st with eval_state := NONE,env1) ⇒
  repl_types T (ffi,rs)
    (types, st with <| clock := st.clock − ck;
                       refs := st.refs ++ junk;
                       eval_state := NONE |>,env1)
Proof
  strip_tac \\ drule repl_types_skip
  \\ disch_then (qspecl_then [‘junk’,‘ck’,‘0’,‘0’] mp_tac)
  \\ match_mp_tac (DECIDE “x = y ⇒ x ⇒ y”) \\ fs []
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [state_component_equality]
QED

Theorem repl_types_clock_refs_ffi:
  repl_types T (ffi,rs) (types,st with eval_state := NONE,env1) ⇒
  repl_types T (ffi,rs)
    (types, st with <| clock := st.clock − ck;
                       refs := st.refs ++ junk; ffi := st.ffi ;
                       eval_state := NONE |>,env1)
Proof
  strip_tac \\ drule repl_types_skip
  \\ disch_then (qspecl_then [‘junk’,‘ck’,‘0’,‘0’] mp_tac)
  \\ match_mp_tac (DECIDE “x = y ⇒ x ⇒ y”) \\ fs []
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [state_component_equality]
QED

Theorem evaluate_clock_decs:
  evaluate_decs s env xs = (s1,res) ⇒ s1.clock ≤ s.clock
Proof
  rw []
  \\ qspecl_then [‘s’,‘env’,‘xs’] mp_tac
       (evaluatePropsTheory.is_clock_io_mono_evaluate |> CONJUNCTS |> last)
  \\ fs [evaluatePropsTheory.is_clock_io_mono_def]
QED

Theorem evaluate_decs_with_NONE:
  evaluate_decs s env1 safe_decs = (s1,res) ∧ s.eval_state = NONE ∧
  res ≠ Rerr (Rabort Rtype_error) ⇒
  evaluate_decs s env1 safe_decs = (s1 with eval_state := NONE,res)
Proof
  strip_tac
  \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> last)
  \\ fs [] \\ rw [GSYM PULL_FORALL]
  \\ fs [state_component_equality]
QED

Overload TYPES_TYPE =
  “PAIR_TYPE ADDPRINTVALS_TYPE_NAMES_TYPE (PAIR_TYPE INFER_INF_ENV_TYPE NUM)”

Theorem evaluate_repl:
  ∀(st:'ffi semanticPrimitives$state) s repl_str arg_str
   env s1_v types cur_gen next_id next_gen env1
   parse_v types_v conf_v env_v decs_v input_str_v
   types decs input_str env_id s1 parse.
     st.eval_state = SOME (EvalDecs s) ∧
     s.compiler = compiler_inst x64_config ∧
     s.compiler_state = s1_v ∧
     s.decode_decs = v_fun_abs decs_allowed (LIST_v AST_DEC_v) ∧
     s.env_id_counter = (cur_gen,next_id,next_gen) ∧
     BACKEND_INC_CONFIG_TYPE s1 s.compiler_state ∧
     LIST_TYPE AST_DEC_TYPE decs decs_v ∧
     TYPES_TYPE types types_v ∧
     STRING_TYPE input_str input_str_v ∧
     (STRING_TYPE --> SUM_TYPE STRING_TYPE (LIST_TYPE AST_DEC_TYPE)) parse parse_v ∧
     env_v = Conv NONE [Env env1 (env_id,0); Litv (IntLit (&env_id))] ∧
     conf_v = Conv NONE [s1_v; Litv (IntLit (&next_gen))] ∧
     repl_types T (ffi,repl_rs) (SND types,st with eval_state := NONE,env1) ∧
     nsLookup env.v repl_str = SOME repl_v ⇒
     nsLookup env.v arg_str =
       SOME (Conv NONE [parse_v; types_v; conf_v; env_v; decs_v; input_str_v]) ⇒
     ∃res s1.
       evaluate st env [App Opapp [Var repl_str; Var arg_str]] = (s1,res) ∧
       res ≠ Rerr (Rabort Rtype_error) ∧
       (∀vs. res = Rval vs ⇒ vs = [Conv NONE []])
Proof
  strip_tac \\ completeInduct_on ‘st.clock’
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ gvs [GSYM PULL_FORALL]
  (* expand App repl *)
  \\ simp [evaluate_def,repl_v_def]
  \\ simp [do_opapp_def,find_recfun_def]
  \\ IF_CASES_TAC \\ simp []
  \\ rename [‘evaluate _ _ [Mat _ _]’]
  \\ simp [Once evaluate_def]
  \\ simp [can_pmatch_all_def,pmatch_def,evaluate_Var]
  \\ simp [Once evaluate_def,astTheory.pat_bindings_def,pmatch_def]
  (* calling check_and_tweak *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ rename [‘evaluate _ _ [App Opapp _]’]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,build_rec_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rename [‘do_opapp [repl_check_and_tweak_check_and_tweak_v;_]’]
  \\ qmatch_goalsub_abbrev_tac ‘do_opapp [_; arg_v]’
  \\ assume_tac repl_check_and_tweak_check_and_tweak_v_thm
  \\ ‘PAIR_TYPE (LIST_TYPE AST_DEC_TYPE) (PAIR_TYPE TYPES_TYPE STRING_TYPE)
           (decs,types,input_str) arg_v’ by
    fs [Abbr‘arg_v’,PAIR_TYPE_def]
  \\ drule_all Arrow_IMP
  \\ fs [dec_clock_def]
  \\ disch_then (qspec_then ‘(st with clock := st.clock − 2)’ strip_assume_tac)
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs []
  (* case split on result of check_and_tweak *)
  \\ rename [‘evaluate _ _ [Mat _ _]’]
  \\ Cases_on ‘check_and_tweak (decs,types,input_str)’
  \\ gvs [inferProgTheory.INFER_EXC_TYPE_def]
  THEN1
   (rename [‘_ = INL msg’]
    \\ simp [Once evaluate_def]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    (* call report_error *)
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,report_error_v_def,do_opapp_def,EVAL “find_recfun s [(s,y,x)]”]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                     namespaceTheory.nsOptBind_def,build_rec_env_def])
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,do_app_def]
    \\ simp [repl_moduleProgTheory.errorMessage_def]
    \\ ‘repl_types T (ffi,repl_rs)
          (SND types,st with <| eval_state := NONE ; refs := st.refs ++ junk |>,env1)’
         by (drule_then irule repl_types_skip_alt \\ fs [])
    \\ ‘MEM (Long «Repl» (Short «errorMessage»),Str,
             the_Loc errorMessage_loc) repl_rs’ by simp [repl_rs_def]
    \\ drule_then drule repl_types_str_assign
    \\ simp [store_assign_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
    \\ Cases_on ‘msg’ \\ gvs [STRING_TYPE_def]
    \\ rename [‘(Refv (Litv (StrLit sss)))’]
    \\ disch_then (qspec_then ‘sss’ mp_tac)
    \\ impl_keep_tac
    >-
     (drule repl_types_thm \\ simp [EVERY_MEM]
      \\ strip_tac \\ first_x_assum drule
      \\ simp [ref_lookup_ok_def]
      \\ simp [store_lookup_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
      \\ strip_tac \\ fs [store_v_same_type_def])
    \\ simp [] \\ strip_tac
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,evaluate_Lit]
    (* recursive call *)
    \\ last_x_assum irule \\ gvs []
    \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
    \\ assume_tac compiler64prog_report_error_dec_v_thm
    \\ rpt (first_assum $ irule_at Any)
    \\ drule_then irule repl_types_skip_alt \\ fs [])
  \\ rename [‘_ = INR xx’] \\ PairCases_on ‘xx’
  \\ rename [‘_ = INR (safe_decs,new_types)’]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def,
          PAIR_TYPE_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [astTheory.pat_bindings_def,pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st6 env6’
  \\ ‘st6.eval_state = SOME (EvalDecs s)’ by fs [Abbr‘st6’]
  \\ drule (evaluate_eval |> Q.INST [‘arg_str’|->‘« v5»’]) \\ simp []
  \\ ‘nsLookup env6.v (Short «eval») = SOME eval_v’ by
   (fs [Abbr‘env6’]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [])
  \\ drule check_and_tweak \\ strip_tac
  \\ disch_then $ drule_then drule
  \\ gvs [Abbr‘env6’]
  \\ disch_then drule
  \\ impl_tac
  THEN1
   (gvs [Abbr‘st6’] \\ rw []
    \\ irule_at Any repl_types_alt
    \\ first_assum $ irule_at Any
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule_at Any repl_types_clock_refs
    \\ first_assum $ irule_at Any)
  \\ strip_tac \\ fs []
  \\ Cases_on ‘∃f. res = Rerr (Rabort (Rffi_error f))’ \\ fs []
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ fs []
  \\ gvs []
  (* Compile_error case *)
  THEN1
   (simp [Once evaluate_def,evaluate_Var]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    (* call report_error *)
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,report_error_v_def,do_opapp_def,EVAL “find_recfun s [(s,y,x)]”]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                     namespaceTheory.nsOptBind_def,build_rec_env_def])
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,do_app_def]
    \\ simp [repl_moduleProgTheory.errorMessage_def]
    \\ ‘repl_types T (ffi,repl_rs)
          (SND types,st6 with <| eval_state := NONE ; refs := st6.refs ++ junk' |>,env1)’
         by (drule_then irule repl_types_skip_alt \\ fs [Abbr‘st6’]
             \\ simp_tac std_ss [GSYM APPEND_ASSOC,rich_listTheory.IS_PREFIX_APPEND3])
    \\ ‘MEM (Long «Repl» (Short «errorMessage»),Str,
             the_Loc errorMessage_loc) repl_rs’ by simp [repl_rs_def]
    \\ drule_then drule repl_types_str_assign
    \\ simp [store_assign_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
    \\ disch_then (qspec_then ‘msg’ mp_tac)
    \\ impl_keep_tac
    >-
     (drule repl_types_thm \\ simp [EVERY_MEM]
      \\ strip_tac \\ pop_assum kall_tac \\ pop_assum drule
      \\ simp [ref_lookup_ok_def] \\ unabbrev_all_tac \\ fs []
      \\ simp [store_lookup_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
      \\ strip_tac \\ fs [store_v_same_type_def])
    \\ simp [] \\ strip_tac
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,evaluate_Lit]
    (* recursive call *)
    \\ last_x_assum irule \\ unabbrev_all_tac \\ gvs []
    \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
    \\ assume_tac compiler64prog_report_error_dec_v_thm
    \\ rpt (first_assum $ irule_at Any)
    \\ drule_then irule repl_types_skip_alt \\ fs [])
  (* Eval exn case *)
  THEN1
   (simp [Once evaluate_def,evaluate_Var]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    (* call report_exn *)
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,report_exn_v_def,do_opapp_def,EVAL “find_recfun s [(s,y,x)]”]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                     namespaceTheory.nsOptBind_def,build_rec_env_def])
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,do_app_def]
    \\ simp [repl_moduleProgTheory.exn_def]
    \\ ‘repl_types T (ffi,repl_rs)
          (SND types,st6 with <| clock := st6.clock - ck1 ;
                                 refs := st6.refs ++ junk' ;
                                 eval_state := NONE |>,env1)’
         by (drule_then irule repl_types_skip_alt \\ fs [Abbr‘st6’]
             \\ simp_tac std_ss [GSYM APPEND_ASSOC,rich_listTheory.IS_PREFIX_APPEND3])
    \\ ‘MEM (Long «Repl» (Short «exn»),Exn,the_Loc exn) repl_rs’ by simp [repl_rs_def]
    \\ drule_then drule repl_types_exn_assign
    \\ disch_then drule
    \\ disch_then drule
    \\ Cases_on ‘store_assign (the_Loc exn) (Refv exn') st7.refs’
    >-
     (qsuff_tac ‘F’ \\ fs [] \\ pop_assum mp_tac \\ simp []
      \\ fs [store_assign_def]
      \\ drule_all repl_types_exn \\ strip_tac
      \\ drule repl_types_thm \\ simp [EVERY_MEM]
      \\ strip_tac \\ pop_assum kall_tac \\ pop_assum drule
      \\ simp [ref_lookup_ok_def] \\ unabbrev_all_tac \\ fs []
      \\ simp [store_lookup_def,repl_moduleProgTheory.exn_def,the_Loc_def]
      \\ strip_tac \\ fs [store_v_same_type_def])
    \\ fs [] \\ strip_tac \\ fs []
    \\ fs [repl_moduleProgTheory.exn_def,the_Loc_def]
    \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                     namespaceTheory.nsOptBind_def,do_app_def])
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,do_app_def]
    \\ simp [repl_moduleProgTheory.errorMessage_def]
    \\ qmatch_goalsub_abbrev_tac ‘StrLit msg_e’
    \\ ‘MEM (Long «Repl» (Short «errorMessage»),Str,
             the_Loc errorMessage_loc) repl_rs’ by simp [repl_rs_def]
    \\ drule_then drule repl_types_str_assign
    \\ simp [store_assign_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
    \\ disch_then (qspec_then ‘msg_e’ mp_tac)
    \\ impl_keep_tac
    >-
     (drule repl_types_thm \\ simp [EVERY_MEM]
      \\ strip_tac \\ first_x_assum drule
      \\ simp [ref_lookup_ok_def]
      \\ simp [store_lookup_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
      \\ strip_tac \\ fs [store_v_same_type_def])
    \\ simp [] \\ strip_tac
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,evaluate_Lit]
    (* call roll_back *)
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ rename [‘evaluate _ _ [App Opapp _]’]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ qmatch_goalsub_abbrev_tac ‘do_opapp [_; arg_v]’
    \\ assume_tac repl_check_and_tweak_roll_back_v_thm
    \\ ‘PAIR_TYPE TYPES_TYPE TYPES_TYPE (types,new_types) arg_v’ by
      fs [Abbr‘arg_v’,PAIR_TYPE_def]
    \\ drule_all Arrow_IMP
    \\ fs [dec_clock_def]
    \\ qmatch_goalsub_abbrev_tac ‘(st3, Rerr (Rabort Rtimeout_error))’
    \\ disch_then (qspec_then ‘dec_clock st3’ strip_assume_tac) \\ fs []
    \\ fs [] \\ IF_CASES_TAC \\ fs []
    \\ unabbrev_all_tac \\ gvs [dec_clock_def]
    \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,evaluate_Lit]
    (* recursive call *)
    \\ last_x_assum irule \\ unabbrev_all_tac \\ gvs []
    \\ conj_tac THEN1 (imp_res_tac evaluate_clock \\ fs [])
    \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
    \\ assume_tac compiler64prog_report_exn_dec_v_thm
    \\ rpt (first_assum $ irule_at Any)
    \\ rewrite_tac [GSYM APPEND_ASSOC,integerTheory.INT_ADD_CALCULATE]
    \\ ‘SND (roll_back (types,new_types)) = roll_back (SND types) (SND new_types)’
       by (PairCases_on ‘types’ \\ PairCases_on ‘new_types’ \\ fs [] \\ EVAL_TAC)
    \\ fs []
    \\ drule_then irule repl_types_skip_alt \\ fs []
    \\ drule evaluate_decs_with_NONE \\ fs []
    \\ simp [semanticPrimitivesTheory.state_component_equality])
  (* Eval_result case *)
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ ‘repl_types T (ffi,repl_rs)
                 (SND new_types,
                  st7 with eval_state := NONE, extend_dec_env env2 env1)’ by
   (irule repl_types_eval
    \\ drule check_and_tweak \\ strip_tac
    \\ first_assum $ irule_at (Pos hd)
    \\ irule_at Any evaluate_decs_with_NONE
    \\ first_assum $ irule_at Any \\ simp [Abbr‘st6’]
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule repl_types_clock_refs \\ simp [])
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  (* evaluating !REPL.isEOF *)
  \\ simp [mlbasicsProgTheory.deref_v_def,do_opapp_def]
  \\ IF_CASES_TAC \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,do_app_def]
  \\ ‘∃eof_n oef_b bv. isEOF_loc = Loc oef_b eof_n ∧
       store_lookup eof_n st7.refs = SOME (Refv (Boolv bv))’ by
   (drule repl_types_thm \\ strip_tac \\ fs [repl_rs_def]
    \\ fs [repl_moduleProgTheory.isEOF_def,the_Loc_def,ref_lookup_ok_def])
  \\ fs []
  (* evaluate if *)
  \\ rename [‘evaluate _ _ [If _ _ _]’]
  \\ simp [Once evaluate_def,evaluate_Var,namespaceTheory.nsOptBind_def,do_if_def]
  \\ IF_CASES_TAC THEN1 simp [evaluate_Con]
  \\ simp []
  (* let new_input = ... *)
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  (* evaluating !REPL.nextString *)
  \\ simp [mlbasicsProgTheory.deref_v_def,do_opapp_def]
  \\ IF_CASES_TAC \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,do_app_def]
  \\ ‘∃next_n next_b inp. nextString_loc = Loc next_b next_n ∧
       store_lookup next_n st7.refs = SOME (Refv (Litv (StrLit inp)))’ by
   (drule repl_types_thm \\ strip_tac \\ fs [repl_rs_def]
    \\ fs [repl_moduleProgTheory.nextString_def,the_Loc_def,ref_lookup_ok_def])
  \\ fs []
  \\ ‘STRING_TYPE inp (Litv (StrLit inp))’ by fs [STRING_TYPE_def]
  (* calling parse *)
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list]
  \\ simp [evaluate_Var,namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ qpat_x_assum ‘(STRING_TYPE --> _) _ parse_v’ mp_tac
  \\ strip_tac
  \\ drule_all Arrow_IMP
  \\ fs [dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac ‘(st2, Rerr (Rabort Rtimeout_error))’
  \\ disch_then (qspec_then ‘(st2 with clock := st2.clock − 1)’ strip_assume_tac)
  \\ fs [] \\ IF_CASES_TAC \\ fs [Abbr‘st2’,dec_clock_def]
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs []
  (* case on result of parse *)
  \\ Cases_on ‘parse inp’ \\ gvs [std_preludeTheory.SUM_TYPE_def]
  THEN1
   (rename [‘_ = INL msg’]
    \\ simp [Once evaluate_def,evaluate_Var]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def]
    \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    (* call report_error *)
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,report_error_v_def,do_opapp_def,EVAL “find_recfun s [(s,y,x)]”]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                     namespaceTheory.nsOptBind_def,build_rec_env_def])
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ fs [] \\ IF_CASES_TAC >- fs []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,do_app_def]
    \\ simp [repl_moduleProgTheory.errorMessage_def]
    \\ ‘repl_types T (ffi,repl_rs)
          (SND new_types,st7 with <| eval_state := NONE ; refs := st7.refs ++ junk'' |>,
           extend_dec_env env2 env1)’
         by (drule_then irule repl_types_skip_alt \\ fs [])
    \\ ‘MEM (Long «Repl» (Short «errorMessage»),Str,
             the_Loc errorMessage_loc) repl_rs’ by simp [repl_rs_def]
    \\ drule_then drule repl_types_str_assign
    \\ simp [store_assign_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
    \\ Cases_on ‘msg’ \\ gvs [STRING_TYPE_def]
    \\ rename [‘(Refv (Litv (StrLit sss)))’]
    \\ disch_then (qspec_then ‘sss’ mp_tac)
    \\ impl_keep_tac
    >-
     (drule repl_types_thm \\ simp [EVERY_MEM]
      \\ strip_tac \\ first_x_assum drule
      \\ simp [ref_lookup_ok_def]
      \\ simp [store_lookup_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
      \\ strip_tac \\ fs [store_v_same_type_def])
    \\ simp [] \\ strip_tac
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,evaluate_Lit]
    (* recursive call *)
    \\ last_x_assum irule \\ gvs []
    \\ conj_tac THEN1 (imp_res_tac evaluate_clock \\ fs [])
    \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
    \\ assume_tac compiler64prog_report_error_dec_v_thm
    \\ rpt (first_assum $ irule_at Any)
    \\ rewrite_tac [GSYM APPEND_ASSOC,integerTheory.INT_ADD_CALCULATE]
    \\ drule_then irule repl_types_skip_alt \\ fs [])
  (* parse is successful *)
  \\ rename [‘_ = INR new_decs’]
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* recursive call *)
  \\ last_x_assum irule
  \\ drule evaluate_clock_decs \\ strip_tac \\ fs []
  \\ unabbrev_all_tac \\ fs []
  \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
  \\ rpt (first_assum $ irule_at Any)
  \\ rewrite_tac [GSYM APPEND_ASSOC,integerTheory.INT_ADD_CALCULATE]
  \\ irule repl_types_clock_refs_ffi \\ fs []
QED

Theorem evaluate_repl_thm =
  evaluate_repl |> SIMP_RULE std_ss [] |> SPEC_ALL
  |> Q.INST [‘cur_gen’|->‘0’,‘next_id’|->‘1’,‘next_gen’|->‘1’,‘env_id’|->‘0’,
             ‘input_str’|->‘«»’,‘decs’|->‘[]’] |> GEN_ALL
  |> SIMP_RULE std_ss [STRING_TYPE_def,LIST_TYPE_def] |> SPEC_ALL;

Theorem evaluate_start_repl:
  (st:'ffi semanticPrimitives$state).eval_state = SOME (EvalDecs s) ∧
  s.compiler = compiler_inst x64_config ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v AST_DEC_v) ∧
  s.env_id_counter = (0,1,1) ∧
  BACKEND_INC_CONFIG_TYPE s1 s.compiler_state ∧
  LIST_TYPE STRING_TYPE cl cl_v ∧
  repl_types T (ffi,repl_rs)
               (repl_prog_types, st with eval_state := NONE, repl_init_env) ∧
  nsLookup env.v start_repl_str = SOME start_repl_v ⇒
  nsLookup env.v arg_str = SOME (Conv NONE [cl_v; s.compiler_state]) ⇒
  ∃res s1.
    evaluate st env [App Opapp [Var start_repl_str; Var arg_str]] = (s1,res) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    (∀vs. res = Rval vs ⇒ vs = [Conv NONE []])
Proof
  rpt strip_tac
  (* expand App start_repl *)
  \\ simp [evaluate_def,start_repl_v_def]
  \\ simp [do_opapp_def,find_recfun_def]
  \\ IF_CASES_TAC \\ simp []
  \\ rename [‘evaluate _ _ [Mat _ _]’]
  \\ simp [Once evaluate_def]
  \\ simp [can_pmatch_all_def,pmatch_def,evaluate_Var]
  \\ simp [Once evaluate_def,astTheory.pat_bindings_def,pmatch_def]
  (* calling select_parse *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ rename [‘evaluate _ _ [App Opapp _]’]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,build_rec_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rename [‘do_opapp [compiler64prog_select_parse_v;_]’]
  \\ assume_tac compiler64prog_select_parse_v_thm
  \\ drule_all Arrow_IMP
  \\ fs [dec_clock_def]
  \\ disch_then (qspec_then ‘(st with clock := st.clock − 2)’ strip_assume_tac)
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs []
  (* let types = init_types *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  (* let conf = ... *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* let env = ... *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  (* let decs = [] *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit,do_con_check_def,build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  (* let input_str = «» *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* call init_next_string *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ rename [‘evaluate _ _ [App Opapp _]’]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,build_rec_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rename [‘do_opapp [compiler64prog_init_next_string_v;_]’]
  \\ assume_tac compiler64prog_init_next_string_v_thm
  \\ drule_all Arrow_IMP
  \\ fs [dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac ‘(st2, Rerr (Rabort Rtimeout_error))’
  \\ disch_then (qspec_then ‘(st2 with clock := st2.clock − 1)’ strip_assume_tac)
  \\ fs [] \\ IF_CASES_TAC \\ fs [Abbr‘st2’]
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs []
  (* update REPL.nextString *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [mlbasicsProgTheory.assign_v_def,do_opapp_def,dec_clock_def]
  \\ IF_CASES_TAC \\ fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ IF_CASES_TAC >- fs []
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st7 env7 [App Opassign _]’
  \\ ‘repl_types T (ffi,repl_rs)
        (repl_prog_types, st7 with eval_state := NONE, repl_init_env)’ by
   (unabbrev_all_tac \\ fs [] \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule repl_types_clock_refs \\ fs [])
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit,Abbr‘env7’]
  \\ fs [do_app_def]
  \\ ‘∃next_n next_b inp. nextString_loc = Loc next_b next_n ∧
       store_lookup next_n st7.refs = SOME (Refv (Litv (StrLit inp)))’ by
   (drule repl_types_thm \\ strip_tac \\ fs [repl_rs_def]
    \\ fs [repl_moduleProgTheory.nextString_def,the_Loc_def,ref_lookup_ok_def])
  \\ fs [] \\ fs [store_assign_def,store_lookup_def,store_v_same_type_def]
  \\ unabbrev_all_tac \\ fs []
  (* call repl *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ irule (GEN_ALL evaluate_repl_thm)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ conj_tac >- EVAL_TAC
  \\ assume_tac repl_init_types_repl_init_types_v_thm
  \\ rpt (first_assum $ irule_at Any)
  \\ simp [repl_init_typesTheory.repl_init_types_def]
  \\ qexists_tac ‘ffi’
  \\ ‘MEM (Long «Repl» (Short «nextString»),Str,the_Loc nextString_loc) repl_rs’ by
        fs [repl_rs_def]
  \\ drule_then drule repl_types_str_assign
  \\ fs [the_Loc_def,store_assign_def,store_v_same_type_def]
  \\ fs [HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def]
  \\ disch_then (qspec_then ‘init_next_string cl’ mp_tac)
  \\ match_mp_tac (DECIDE “x = y ⇒ (x ⇒ y)”)
  \\ rpt AP_TERM_TAC
  \\ fs [semanticPrimitivesTheory.state_component_equality]
QED

Theorem BUTLAST_LAST:
  ∀xs. ~NULL xs ⇒ xs = BUTLAST xs ++ [LAST xs]
Proof
  Induct \\ fs []
  \\ Cases_on ‘xs’ \\ fs []
QED

Theorem BACKEND_INC_CONFIG_TYPE_v[local]:
  BACKEND_INC_CONFIG_TYPE conf u ⇒
  u = BACKEND_INC_CONFIG_v conf
Proof
  rw [] \\ imp_res_tac BACKEND_INC_CONFIG_IMP \\ fs []
QED

Theorem repl_prog_isPREFIX:
  repl_prog ≼ FRONT compiler64_prog
Proof
  rewrite_tac [listTheory.isPREFIX_THM,repl_moduleProgTheory.repl_prog_def,
               compiler64ProgTheory.compiler64_prog_def,FRONT_CONS,
               locationTheory.unknown_loc_def]
  \\ EVAL_TAC
QED

val ffi_inst = type_of “basis_ffi _ _” |> dest_type |> snd |> hd

(*
  max_print_depth := 15
*)

Theorem evaluate_decs_compiler64_prog:
  s.compiler = compiler_inst x64_config ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v AST_DEC_v) ∧
  s.env_id_counter = (0,0,1) ∧ prog_syntax_ok compiler64_prog ∧
  has_repl_flag (TL cl) ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  s.compiler_state = BACKEND_INC_CONFIG_v conf ∧
  file_content fs «config_enc_str.txt» = SOME (encode_backend_config conf) ∧
  evaluate_decs (init_state (basis_ffi cl fs) with
                            <| clock := ck; eval_state := (SOME (EvalDecs s)) |>)
      init_env compiler64_prog = (s1,res) ⇒
  res ≠ Rerr (Rabort Rtype_error)
Proof
  rw [] \\ pop_assum mp_tac
  \\ ‘~NULL compiler64_prog’ by
   (once_rewrite_tac [compiler64_prog_def] \\ rewrite_tac [NULL])
  \\ drule BUTLAST_LAST
  \\ disch_then (once_rewrite_tac o single)
  \\ strip_tac
  \\ assume_tac (Decls_FRONT_compiler64_prog
       |> REWRITE_RULE [ml_progTheory.ML_code_env_def]
       |> Q.GEN ‘ffi’ |> Q.ISPEC ‘basis_ffi cl fs’
       |> Q.INST [‘eval_state_var’|->‘s’])
  \\ dxrule ml_progTheory.Decls_IMP_Prog
  \\ ‘prog_syntax_ok (FRONT compiler64_prog)’ by
    (irule ml_progTheory.prog_syntax_ok_isPREFIX
     \\ first_x_assum $ irule_at Any
     \\ Cases_on ‘compiler64_prog’ using SNOC_CASES
     \\ gvs [])
  \\ ‘prog_syntax_ok repl_prog’ by
    (irule ml_progTheory.prog_syntax_ok_isPREFIX
     \\ irule_at Any repl_prog_isPREFIX \\ fs [])
  \\ impl_tac >- fs [] \\ strip_tac
  \\ drule repl_types_repl_prog
  \\ disch_then drule
  \\ disch_then (qspec_then ‘encode_backend_config conf’ mp_tac)
  \\ impl_tac >-
   (fs [] \\ simp (DB.find "repl_moduleProg_st" |> map (#1 o #2))
    \\ simp (repl_prog_isPREFIX :: (DB.find "refs_def" |> map (#1 o #2)))
    \\ fs [repl_prog_st_def, ml_progTheory.init_state_def])
  \\ fs [repl_prog_st_def]
  \\ qpat_abbrev_tac ‘ppp = W8array _ :: _’ \\ pop_assum kall_tac
  \\ qpat_x_assum ‘Prog _ _ _ _ _’ kall_tac
  \\ qpat_x_assum ‘evaluate_decs _ _ _ = _’ kall_tac
  \\ strip_tac \\ fs [LAST_compiler64_prog]
  \\ qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
  (* calling main *)
  \\ fs [evaluate_decs_def,astTheory.pat_bindings_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [do_con_check_def]
  \\ rewrite_tac [main_v_def]
  \\ rewrite_tac [EVAL “semanticPrimitives$do_opapp
       [Recclosure env [(«main»,«u», e)] «main»; Conv NONE []]”] \\ simp []
  \\ IF_CASES_TAC >- (fs [] \\ rw [] \\ fs [combine_dec_result_def])
  \\ fs [dec_clock_def]
  (* inside main *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ IF_CASES_TAC >- (rw [] \\ fs [combine_dec_result_def])
  (* evaluate e_cl *)
  \\ fs [dec_clock_def]
  \\ qabbrev_tac ‘ev = (EvalDecs (s with env_id_counter := (0,1,1)))’
  \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> hd)
  \\ disch_then (qspec_then ‘SOME ev’ mp_tac)
  \\ impl_tac >- (fs [] \\ Cases_on ‘res_cl’ \\ fs [combine_dec_result_def])
  \\ strip_tac \\ fs []
  \\ Cases_on ‘res_cl = Rerr (Rabort Rtimeout_error)’
  >- (rw [] \\ fs [combine_dec_result_def])
  \\ fs []
  (* call compiler_has_repl_flag *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ assume_tac compiler64prog_has_repl_flag_v_thm
  \\ drule_all (Arrow_IMP |> INST_TYPE [“:'ffi”|->ffi_inst])
  \\ disch_then (qspec_then ‘(dec_clock (s_cl with eval_state := SOME ev))’ strip_assume_tac)
  \\ fs []
  \\ IF_CASES_TAC >- (rw[] \\ fs [combine_dec_result_def])
  \\ fs []
  \\ Cases_on ‘res' = Rerr (Rabort Rtimeout_error)’
  >- (rw [] \\ fs [combine_dec_result_def])
  \\ gvs []
  (* if *)
  \\ gvs [BOOL_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit,do_if_def]
  \\ fs [dec_clock_def]
  (* call run_interactive_repl *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rewrite_tac [run_interactive_repl_v_def,EVAL “semanticPrimitives$do_opapp
       [Recclosure env [(n, u, e)] n; cl_v]”] \\ simp []
  \\ IF_CASES_TAC >- (fs [] \\ rw [] \\ fs [combine_dec_result_def])
  \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [dec_clock_def]
  (* charsFrom *)
  \\ rename [‘do_opapp [REPL_charsFrom_v; _]’]
  \\ first_x_assum (qspecl_then [‘ck’,‘junk’] strip_assume_tac)
  \\ simp []
  \\ IF_CASES_TAC >- (fs [] \\ rw [] \\ fs [combine_dec_result_def])
  \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> hd)
  \\ disch_then (qspec_then ‘SOME ev’ mp_tac)
  \\ impl_tac >- (fs [] \\ Cases_on ‘res_pr’ \\ fs [combine_dec_result_def])
  \\ strip_tac \\ fs []
  \\ Cases_on ‘res_pr = Rerr (Rabort Rtimeout_error)’
  >- (rw [] \\ fs [combine_dec_result_def])
  \\ fs []
  (* decode_backend_config *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [dec_clock_def]
  \\ assume_tac decodeProgTheory.decode_backend_config_v_thm
  \\ drule_all (Arrow_IMP |> INST_TYPE [“:'ffi”|->ffi_inst])
  \\ disch_then (qspec_then ‘s_pr with <|clock := s_pr.clock − 1;
                               eval_state := SOME ev|>’ strip_assume_tac)
  \\ fs []
  \\ IF_CASES_TAC >- (rw[] \\ fs [combine_dec_result_def])
  \\ fs []
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’
  >- (rw [] \\ fs [combine_dec_result_def])
  \\ gvs []
  (* start_repl *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st8 env8’
  \\ qspecl_then
       [‘st8’,‘env8’,‘Short «start_repl»’,‘Short « v0»’,‘basis_ffi cl fs’,‘TL cl’] mp_tac
    (Q.GENL [‘st’,‘env’,‘start_repl_str’,‘arg_str’,‘ffi’,‘cl’,‘s1’,‘s’] evaluate_start_repl)
  \\ simp [Abbr‘st8’,Abbr‘env8’,Abbr‘ev’]
  \\ fs [backend_enc_decTheory.encode_backend_config_thm]
  \\ drule BACKEND_INC_CONFIG_TYPE_v \\ strip_tac
  \\ gvs []
  \\ disch_then drule
  \\ gvs []
  \\ impl_tac
  >-
   (CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [dec_clock_def]
    \\ irule repl_types_clock_refs
    \\ qsuff_tac ‘(s_pr with eval_state := NONE) = s_pr’ >- fs []
    \\ fs [semanticPrimitivesTheory.state_component_equality])
  \\ strip_tac \\ simp []
  \\ rename [‘res9 ≠ Rerr (Rabort Rtype_error)’]
  \\ Cases_on ‘res9 = Rerr (Rabort Rtype_error)’ >- fs [combine_dec_result_def]
  \\ fs []
  \\ reverse (Cases_on ‘res9’) \\ fs [] >- (rw [] \\ fs [combine_dec_result_def])
  \\ simp [pmatch_def] \\ rw [combine_dec_result_def] \\ fs []
QED

Theorem semantics_prog_compiler64_prog:
  s.compiler = compiler_inst x64_config ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v AST_DEC_v) ∧
  s.env_id_counter = (0,0,1) ∧ has_repl_flag (TL cl) ∧ wfcl cl ∧ wfFS fs ∧
  STD_streams fs ∧ hasFreeFD fs ∧ prog_syntax_ok compiler64_prog ∧
  s.compiler_state = BACKEND_INC_CONFIG_v conf ∧
  file_content fs «config_enc_str.txt» = SOME (encode_backend_config conf) ⇒
  Fail ∉ semantics_prog
           (init_state (basis_ffi cl fs) with eval_state := SOME (EvalDecs s))
           init_env compiler64_prog
Proof
  fs [IN_DEF,semanticsTheory.semantics_prog_def] \\ rpt strip_tac
  \\ mp_tac (Q.GENL [‘ck’,‘res’,‘s1’] evaluate_decs_compiler64_prog) \\ fs []
  \\ fs [semanticsTheory.evaluate_prog_with_clock_def]
  \\ pairarg_tac \\ gvs []
  \\ qexists_tac ‘k’ \\ fs []
QED
