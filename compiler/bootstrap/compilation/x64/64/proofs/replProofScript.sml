(*
  Verification of the function (called repl) that implements the REPL
*)
open preamble
open semanticsPropsTheory backendProofTheory x64_configProofTheory compiler64ProgTheory
open evaluateTheory
open semanticPrimitivesTheory ml_translatorTheory
open backendProofTheory

val _ = new_theory"replProof";

Definition decs_allowed_def:
  decs_allowed (s:ast$dec list) = T  (* TODO: fix *)
End

Definition compiler_inst_def:
  compiler_inst c = (λ(x,y,z).
                do
                  cfg <- v_fun_abs 𝕌(:inc_config) BACKEND_INC_CONFIG_v y;
                  (cfg2,bs,ws) <- compile_inc_progs_for_eval c (x,cfg,z);
                  SOME (BACKEND_INC_CONFIG_v cfg2,bs,ws)
                od)
End

Triviality mk_compiler_fun_from_ci_tuple:
  mk_compiler_fun_from_ci c = (λ(x,y,z). mk_compiler_fun_from_ci c (x,y,z))
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem no_closures_IMP_concrete_v:
  (∀v. no_closures v ⇒ concrete_v v) ∧
  (∀v. EVERY no_closures v ⇒ concrete_v_list v)
Proof
  ho_match_mp_tac concrete_v_ind \\ rw []
  \\ Cases_on ‘v’ \\ fs [ml_translatorTheory.no_closures_def, SF ETA_ss]
QED

Triviality EqualityType_concrete_v:
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
  nsLookup env.v (Short "env") = SOME (Env env1 id1) ⇒
  nsLookup env.v (Short "decs") = SOME decs_v ⇒
  nsLookup env.v (Short "s1") = SOME s1_v ⇒
  nsLookup env.v (Short "s2") = SOME s2_v ⇒
  nsLookup env.v (Short "bs") = SOME bs_v ⇒
  nsLookup env.v (Short "ws") = SOME ws_v ⇒
  decs_allowed decs ⇒
  evaluate st env [App Eval [Var (Short "env");  Var (Short "s1");
                             Var (Short "decs"); Var (Short "s2");
                             Var (Short "bs");   Var (Short "ws")]] =
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
            [Conv (SOME (TypeStamp "Compile_error" eval_res_stamp))
               [Litv (StrLit msg)]] ∧
        s1 = st with <|clock := st.clock − ck; refs := st.refs ++ junk|> ∨
        (∃f. res = Rerr (Rabort (Rffi_error f))) ∨
        (∃exn st7 ck1 ck2 s2_v.
           evaluate_decs (st with
             <|clock := st.clock − ck1; refs := st.refs ++ junk;
               eval_state := NONE|>) env1 decs = (st7,Rerr (Rraise exn)) ∧
           res = Rval [Conv (SOME (TypeStamp "Eval_exn" eval_res_stamp))
                        [exn; Conv NONE [s2_v; Litv (IntLit (&next_gen + 1))]]] ∧
           s1 = st7 with <| clock := st7.clock - ck2 ;
                            eval_state := SOME (EvalDecs
             (s with <|compiler_state := s2_v;
                env_id_counter := (cur_gen1,next_id1,next_gen1 + 1)|>)) |>) ∨
        (∃env2 st7 ck1 ck2 s2_v.
           evaluate_decs (st with
             <|clock := st.clock − ck1; refs := st.refs ++ junk;
               eval_state := NONE|>) env1 decs = (st7,Rval env2) ∧
           res = Rval [Conv (SOME (TypeStamp "Eval_result" eval_res_stamp))
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
             namespaceTheory.nsOptBind_def,do_app_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,do_con_check_def,build_conv_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [opn_lookup_def]
    \\ fs [add_decs_generation_def,reset_env_generation_def]
    \\ qexists_tac ‘junk’ \\ fs []
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
           namespaceTheory.nsOptBind_def,do_app_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_con_check_def,build_conv_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_con_check_def,build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [opn_lookup_def]
  \\ qexists_tac ‘junk’ \\ fs []
  \\ first_x_assum $ irule_at $ Pos hd
  \\ qexists_tac ‘2’ \\ fs []
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED

(*
omax_print_depth := 18
*)

Inductive repl_types:
[repl_types_init:]
  (∀ffi decs types (s:'ffi state) env.
     infertype_prog init_config decs = Success types ∧
     evaluate$evaluate_decs (init_state ffi) init_env decs = (s,Rval env) ⇒
     repl_types ffi (types,s,env)) ∧
[repl_types_skip:]
  (∀ffi types junk ck t e (s:'ffi state) env.
     repl_types ffi (types,s,res) ⇒
     repl_types ffi (types,s with <| refs := s.refs ++ junk ;
                                     clock := s.clock - ck ;
                                     next_type_stamp := s.next_type_stamp + t ;
                                     next_exn_stamp := s.next_exn_stamp + e |>,env)) ∧
[repl_types_eval:]
  (∀ffi types new_types (s:'ffi state) env new_env new_s.
     repl_types ffi (types,s,res) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rval new_env) ⇒
     repl_types ffi (new_types,new_s,new_env)) ∧
[repl_types_exn:]
  (∀ffi types new_types (s:'ffi state) env e new_s.
     repl_types ffi (types,s,res) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ⇒
     repl_types ffi (types,new_s,env))
End

val _ = export_theory();
