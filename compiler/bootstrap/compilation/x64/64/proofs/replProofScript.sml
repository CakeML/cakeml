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
        (∃exn st7 ck1 ck2 s2_v s2.
           evaluate_decs (st with
             <|clock := st.clock − ck1; refs := st.refs ++ junk;
               eval_state := NONE|>) env1 decs = (st7,Rerr (Rraise exn)) ∧
           BACKEND_INC_CONFIG_TYPE s2 s2_v ∧
           res = Rval [Conv (SOME (TypeStamp "Eval_exn" eval_res_stamp))
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
  \\ first_x_assum $ irule_at $ Pos hd
  \\ qexists_tac ‘2’ \\ fs []
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED

Datatype:
  simple_type = Bool | Str | Exn
End

Definition to_type_def:
  to_type Bool = Infer_Tapp [] Tbool_num ∧
  to_type Str = Infer_Tapp [] Tstring_num ∧
  to_type Exn = Infer_Tapp [] Texn_num
End

Definition check_ref_types_def:
  check_ref_types types (env :semanticPrimitives$v sem_env) (name,ty,loc) ⇔
    nsLookup types.inf_v name = SOME (0,Infer_Tapp [to_type ty] Tref_num) ∧
    nsLookup env.v name = SOME (Loc loc)
End

Inductive repl_types:
[repl_types_init:]
  (∀ffi rs decs types (s:'ffi state) env.
     infertype_prog init_config decs = Success types ∧
     evaluate$evaluate_decs (init_state ffi) init_env decs = (s,Rval env) ∧
     EVERY (check_ref_types types env) rs ⇒
     repl_types (ffi,rs) (types,s,env)) ∧
[repl_types_skip:]
  (∀ffi rs types junk ck t e (s:'ffi state) env.
     repl_types (ffi,rs) (types,s,env) ⇒
     repl_types (ffi,rs) (types,s with <| refs := s.refs ++ junk ;
                                     clock := s.clock - ck ;
                                     next_type_stamp := s.next_type_stamp + t ;
                                     next_exn_stamp := s.next_exn_stamp + e |>,env)) ∧
[repl_types_eval:]
  (∀ffi rs decs types new_types (s:'ffi state) env new_env new_s.
     repl_types (ffi,rs) (types,s,env) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rval new_env) ⇒
     repl_types (ffi,rs) (new_types,new_s,new_env)) ∧
[repl_types_exn:]
  (∀ffi rs decs types new_types (s:'ffi state) env e new_s.
     repl_types (ffi,rs) (types,s,env) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ⇒
     repl_types (ffi,rs) (types,new_s,env)) ∧
[repl_types_exn_assign:]
  (∀ffi rs decs types new_types (s:'ffi state) env e new_s name loc new_store.
     repl_types (ffi,rs) (types,s,env) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ∧
     MEM (name,Exn,loc) rs ∧
     store_assign loc (Refv e) new_s.refs = SOME new_store ⇒
     repl_types (ffi,rs) (types,new_s with refs := new_store,env)) ∧
[repl_types_str_assign:]
  (∀ffi rs types (s:'ffi state) env t name loc new_store.
     repl_types (ffi,rs) (types,s,env) ∧
     MEM (name,Str,loc) rs ∧
     store_assign loc (Refv (Litv (StrLit t))) s.refs = SOME new_store ⇒
     repl_types (ffi,rs) (types,s with refs := new_store,env))
End

Definition ref_lookup_ok_def:
  ref_lookup_ok refs (name:(string,string) id,ty,loc) =
    ∃v:semanticPrimitives$v.
      store_lookup loc refs = SOME (Refv v) ∧
      (ty = Bool ⇒ v = Boolv T ∨ v = Boolv F) ∧
      (ty = Str ⇒ ∃t. v = Litv (StrLit t))
End

Theorem repl_types_thm:
  ∀(ffi:'ffi ffi_state) rs types s env.
    repl_types (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog types decs = Success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  cheat
QED

Theorem repl_types_alt:
  repl_types (ffi,rs) (types,s,env) ∧
  infertype_prog types decs = Success new_t ⇒
  evaluate_decs s env decs ≠ (new_s,Rerr (Rabort Rtype_error))
Proof
  rpt strip_tac
  \\ imp_res_tac repl_types_thm \\ fs []
QED

Theorem repl_types_clock_refs:
  repl_types (ffi,rs) (types,st with eval_state := NONE,env1) ⇒
  repl_types (ffi,rs)
    (types, st with <| clock := st.clock − ck;
                       refs := st.refs ++ junk;
                       eval_state := NONE |>,env1)
Proof
  cheat (*
  strip_tac
  \\ drule repl_types_skip
  \\ disch_then (qspecl_then [‘junk’,‘ck’,‘0’,‘0’] mp_tac)
  \\ match_mp_tac (DECIDE “x = y ⇒ x ⇒ y”)
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [state_component_equality] *)
QED

Definition repl_rs_def:
  repl_rs = [(Long "REPL" (Short "isEOF"),Bool,5:num);
             (Long "REPL" (Short "nextString"),Str,6)]
  (* TODO: fix loc numbers and add exn ref *)
End

Theorem check_and_tweak:
  check_and_tweak (decs,types,input_str) = INR (safe_decs,new_types) ⇒
  infertype_prog types safe_decs = Success new_types ∧ decs_allowed safe_decs
Proof
  cheat
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
  cheat
QED

val _ = Parse.hide "types";
val _ = Parse.hide "types_v";

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
     INFER_INF_ENV_TYPE types types_v ∧
     STRING_TYPE input_str input_str_v ∧
     (HOL_STRING_TYPE --> SUM_TYPE STRING_TYPE (LIST_TYPE AST_DEC_TYPE)) parse parse_v ∧
     env_v = Conv NONE [Env env1 (env_id,0); Litv (IntLit (&env_id))] ∧
     conf_v = Conv NONE [s1_v; Litv (IntLit (&next_gen))] ∧
     repl_types (ffi,repl_rs) (types,st with eval_state := NONE,env1) ∧
     nsLookup env.v repl_str = SOME repl_v ⇒
     nsLookup env.v arg_str =
       SOME (Conv NONE [parse_v; types_v; conf_v; env_v; decs_v; input_str_v]) ⇒
     ∃res s1.
       evaluate st env [App Opapp [Var repl_str; Var arg_str]] = (s1,res) ∧
       res ≠ Rerr (Rabort Rtype_error)
Proof

  strip_tac \\ completeInduct_on ‘st.clock’
  \\ rpt strip_tac \\ gvs [PULL_FORALL]
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
  \\ rename [‘do_opapp [compiler64prog_check_and_tweak_v;_]’]
  \\ qmatch_goalsub_abbrev_tac ‘do_opapp [_; arg_v]’
  \\ assume_tac compiler64prog_check_and_tweak_v_thm
  \\ ‘PAIR_TYPE (LIST_TYPE AST_DEC_TYPE)
        (PAIR_TYPE INFER_INF_ENV_TYPE STRING_TYPE) (decs,types,input_str) arg_v’ by
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
    \\ unabbrev_all_tac
    \\ assume_tac compiler64prog_report_error_v_thm
    \\ drule_all Arrow_IMP
    \\ qmatch_goalsub_abbrev_tac ‘(st2, Rerr (Rabort Rtimeout_error))’
    \\ disch_then (qspec_then ‘dec_clock st2’ strip_assume_tac) \\ fs []
    \\ fs [] \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs [dec_clock_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,evaluate_Lit]
    (* recursive call *)
    \\ last_x_assum irule \\ gvs [Abbr‘st2’]
    \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
    \\ rpt (first_assum $ irule_at Any)
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule repl_types_clock_refs \\ fs [])
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
  \\ drule (evaluate_eval |> Q.INST [‘arg_str’|->‘"f"’]) \\ simp []
  \\ ‘nsLookup env6.v (Short "eval") = SOME eval_v’ by
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
    \\ unabbrev_all_tac
    \\ assume_tac compiler64prog_report_error_v_thm
    \\ ‘STRING_TYPE (strlit msg) (Litv (StrLit msg))’ by fs [STRING_TYPE_def]
    \\ drule_all Arrow_IMP
    \\ qmatch_goalsub_abbrev_tac ‘(st2, Rerr (Rabort Rtimeout_error))’
    \\ disch_then (qspec_then ‘dec_clock st2’ strip_assume_tac) \\ fs []
    \\ fs [] \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs [dec_clock_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,evaluate_Lit]
    (* recursive call *)
    \\ last_x_assum irule \\ gvs [Abbr‘st2’]
    \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
    \\ rpt (first_assum $ irule_at Any)
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule repl_types_clock_refs \\ fs [])
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
    (* call report_error *)
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
    \\ unabbrev_all_tac
    \\ assume_tac (compiler64prog_report_exn_v_thm
         |> INST_TYPE [“:'a”|->“:semanticPrimitives$v”] |> GEN_ALL)
    \\ pop_assum (qspec_then ‘λx v. x = v’ assume_tac)
    \\ ‘(λx v. x = v) exn exn’ by fs []
    \\ drule_all Arrow_IMP
    \\ qmatch_goalsub_abbrev_tac ‘(st2, Rerr (Rabort Rtimeout_error))’
    \\ disch_then (qspec_then ‘dec_clock st2’ strip_assume_tac) \\ fs []
    \\ fs [] \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs [dec_clock_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
             namespaceTheory.nsOptBind_def,evaluate_Lit]
    \\ drule evaluate_clock_decs \\ strip_tac \\ fs []
    (* recursive call *)
    \\ last_x_assum irule \\ gvs [Abbr‘st2’]
    \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
    \\ rpt (first_assum $ irule_at Any)
    \\ rewrite_tac [GSYM APPEND_ASSOC,integerTheory.INT_ADD_CALCULATE]
    \\ irule repl_types_clock_refs \\ fs []
    \\ irule repl_types_exn
    \\ first_assum $ irule_at (Pos hd)
    \\ irule_at Any evaluate_decs_with_NONE
    \\ first_assum $ irule_at Any \\ simp []
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule repl_types_clock_refs \\ simp [])
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
  \\ ‘repl_types (ffi,repl_rs) (new_types,st7 with eval_state := NONE,env2)’ by
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
  \\ ‘∃eof_n bv. isEOF_loc = Loc eof_n ∧
       store_lookup eof_n st7.refs = SOME (Refv (Boolv bv))’ by cheat
  \\ fs []
  (* evaluate if *)
  \\ rename [‘evaluate _ _ [If _ _ _]’]
  \\ simp [Once evaluate_def,evaluate_Var,namespaceTheory.nsOptBind_def,do_if_def]
  \\ IF_CASES_TAC THEN1 simp [evaluate_Con]
  \\ simp []
  (* let new_input = ... *)



  \\ cheat
QED

(*
max_print_depth := 12
*)

val _ = export_theory();
