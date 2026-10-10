(*
  Proves repl_types for the initial env and types from which the REPL starts.
*)
Theory repl_init
Ancestors
  ml_prog repl_types basis_ffi repl_init_envProg repl_moduleProg
  repl_init_types repl_inputRepresentation
Libs
  preamble ml_progLib helperLib

val _ = Parse.hide "types"

val _ = (max_print_depth := 12);

val th2 = Decls_repl_prog |> REWRITE_RULE [GSYM repl_prog_def,SNOC]
          |> CONV_RULE (RAND_CONV EVAL)
          |> Q.GEN ‘ffi’ |> Q.ISPEC ‘basis_ffi ext cl fs’
          |> REWRITE_RULE (APPEND::(DB.find "refs_def" |> map (#1 o #2)))

Overload repl_prog_env = (th2 |> concl |> rator |> rand);

Definition repl_prog_st_def:
  repl_prog_st ext cl fs = ^(th2 |> concl |> rand)
End

val th2 = REWRITE_RULE [GSYM repl_prog_st_def] th2;

Theorem repl_prog_st_input:
  repl_prog_st ext cl fs = input_repl_state (basis_ffi ext cl fs)
Proof
  simp [repl_prog_st_def,repl_inputInitTheory.input_repl_state_def] >>
  EVAL_TAC >>
  simp (APPEND :: (DB.find "refs_def" |> map (#1 o #2)))
QED

Theorem merge_env_intro:
  extend_dec_env = merge_env
Proof
  fs [FUN_EQ_THM,semanticPrimitivesTheory.extend_dec_env_def,merge_env_def]
QED

Definition the_Loc_def:
  the_Loc (semanticPrimitives$Loc _ n) = n
End

Overload repl_init_env =
  (repl_init_envProg_env_def |> concl
   |> find_term (can (match_term “Env _”)) |> rand);

Theorem repl_init_env_input:
  repl_init_env = repl_init_types$repl_prog_env
Proof
  simp [repl_init_typesTheory.repl_prog_env_def]
QED


Theorem evaluate_decs_append: (* TODO: move to evaluateProps *)
  ∀xs ys st env.
    evaluate_decs st env (xs ++ ys) =
    case evaluate_decs st env xs of
    | (st1,Rerr e) => (st1,Rerr e)
    | (st1,Rval env1) =>
        case evaluate_decs st1 (extend_dec_env env1 env) ys of
        | (st2,r) => (st2,combine_dec_result env1 r)
Proof
  Induct \\ fs [evaluateTheory.evaluate_decs_def,
    semanticPrimitivesTheory.extend_dec_env_def]
  >- (rw [] \\ CASE_TAC \\ Cases_on ‘r’
      \\ fs [semanticPrimitivesTheory.combine_dec_result_def])
  \\ once_rewrite_tac [evaluatePropsTheory.evaluate_decs_cons]
  \\ rw [] \\ CASE_TAC \\ fs []
  \\ rw [] \\ CASE_TAC \\ fs []
  \\ rw [] \\ CASE_TAC \\ fs []
  \\ rw [] \\ CASE_TAC \\ fs [semanticPrimitivesTheory.combine_dec_result_def]
  \\ fs [semanticPrimitivesTheory.extend_dec_env_def]
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
QED

Theorem app_frame[local]:
  app p f xs P Q ⇒ ∀H. app p f xs (P * H) (Q *+ H)
Proof
  rw []
  \\ drule_then irule cfAppTheory.app_wgframe
  \\ qexists_tac ‘H’ \\ fs []
  \\ fs [set_sepTheory.SEP_IMP_REFL,cfHeapsBaseTheory.SEP_IMPPOST_def]
  \\ Cases
  \\ fs [cfHeapsBaseTheory.STARPOST_def]
  \\ irule (cfHeapsBaseTheory.SEP_IMP_frame_single_l
     |> ONCE_REWRITE_RULE [set_sepTheory.STAR_COMM])
  \\ fs [set_sepTheory.SEP_IMP_def,set_sepTheory.emp_def,cfHeapsBaseTheory.GC_def]
  \\ rw [set_sepTheory.SEP_EXISTS_THM]
  \\ qexists_tac ‘K T’ \\ fs []
QED

Theorem app_frame_POSTv[local]:
  app p f xs P ($POSTv Q) ⇒ ∀H. app p f xs (P * H) (POSTv v. Q v * H)
Proof
  rw [] \\ drule_then (qspec_then ‘H’ mp_tac) app_frame
  \\ match_mp_tac (METIS_PROVE [] “b=c ⇒ b ⇒ c”)
  \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM,cfHeapsBaseTheory.POSTv_def]
  \\ fs [cfHeapsBaseTheory.POST_def]
  \\ fs [cfHeapsBaseTheory.STARPOST_def]
  \\ Cases \\ fs [set_sepTheory.SEP_CLAUSES]
QED

Theorem CommandLine_arguments_lemma[local] =
  CommandLineProofTheory.CommandLine_arguments_spec
  |> Q.GEN ‘uv’
  |> SIMP_RULE std_ss [ml_translatorTheory.UNIT_TYPE_def]
  |> MATCH_MP app_frame_POSTv
  |> Q.ISPEC ‘STDIO fs’
  |> SIMP_RULE (srw_ss()++helperLib.sep_cond_ss)
      [cfAppTheory.app_def,cfAppTheory.app_basic_def,
       cfDivTheory.POSTv_eq,PULL_EXISTS,set_sepTheory.cond_STAR,
       cfAppTheory.evaluate_to_heap_def]
  |> SIMP_RULE std_ss [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
  |> Q.GEN ‘p’ |> Q.ISPEC ‘(basis_proj1, basis_proj2)’ |> SPEC_ALL;

Theorem Repl_charsFrom_lemma[local] =
  charsFrom_spec |> UNDISCH
  |> MATCH_MP app_frame_POSTv
  |> Q.ISPEC ‘COMMANDLINE cl’
  |> SIMP_RULE (srw_ss()++helperLib.sep_cond_ss)
      [cfAppTheory.app_def,cfAppTheory.app_basic_def,
       cfDivTheory.POSTv_eq,PULL_EXISTS,set_sepTheory.cond_STAR,
       cfAppTheory.evaluate_to_heap_def]
  |> SIMP_RULE std_ss [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
  |> Q.GEN ‘p’ |> Q.ISPEC ‘(basis_proj1, basis_proj2)’ |> SPEC_ALL
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> Q.GEN ‘fname’ |> Q.SPEC ‘«config_enc_str.txt»’
  |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  |> UNDISCH |> UNDISCH
  |> Q.GEN ‘fnamev’ |> SIMP_RULE std_ss [EVAL “FILENAME «config_enc_str.txt» fnamev”]
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC];

Theorem repl_types_clock:
  repl_types catalogue slots T x (types,s,env) ==>
  !k. repl_types catalogue slots T x (types,s with clock := s.clock - k,env)
Proof
  rw [] >> PairCases_on `x` >>
  drule_then irule repl_types_skip_alt >> gs []
QED

Theorem repl_types_refs:
  repl_types catalogue slots T x (types,s,env) ==>
  !junk. repl_types catalogue slots T x (types,s with refs := s.refs ++ junk,env)
Proof
  rw [] >> PairCases_on `x` >>
  drule_then irule repl_types_skip_alt >> gs []
QED

Theorem extend_dec_env_empty:
  extend_dec_env <|v := nsEmpty; c := nsEmpty|> env = env
Proof
  EVAL_TAC
  \\ fs [semanticPrimitivesTheory.sem_env_component_equality]
  \\ Cases_on ‘env.v’ \\ Cases_on ‘env.c’
  \\ fs [namespaceTheory.nsAppend_def]
QED

Theorem parts_ok_basis_ffi:
  parts_ok (basis_ffi ext cls fs) (basis_proj1,basis_proj2)
Proof
  mp_tac basis_ffiTheory.parts_ok_basis_st
  \\ fs (DB.find "TextIOProg_st" |> map (#1 o #2))
QED

Theorem st2heap_basis:
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧
  (repl_prog_st ext cl fs).refs ≼ st.refs ∧
  (repl_prog_st ext cl fs).ffi = st.ffi ⇒
  ∃h_i h_k.
    SPLIT (st2heap (basis_proj1,basis_proj2) st) (h_i,h_k) ∧
    (COMMANDLINE cl * STDIO fs) h_i
Proof
  rw []
  \\ qsuff_tac ‘∃h_i.
        h_i SUBSET st2heap (basis_proj1,basis_proj2) st ∧
        (COMMANDLINE cl * STDIO fs) h_i’
  >- (rw [] \\ pop_assum $ irule_at Any
      \\ rename [‘SPLIT xx’] \\ qexists_tac ‘xx DIFF h_i’
      \\ fs [SUBSET_DEF,set_sepTheory.SPLIT_def,IN_DISJOINT,EXTENSION] \\ metis_tac [])
  \\ fs [set_sepTheory.STAR_def,PULL_EXISTS]
  \\ drule_at Any (DISCH_ALL STDIO_precond |> REWRITE_RULE [AND_IMP_INTRO])
  \\ disch_then (drule_at Any)
  \\ fs (DB.find "refs_def" |> map (#1 o #2))
  \\ disch_then $ irule_at Any
  \\ fs [CommandLineProofTheory.COMMANDLINE_def,set_sepTheory.cond_STAR]
  \\ fs [clFFITheory.cl_ffi_part_def]
  \\ fs [cfHeapsBaseTheory.IOx_def]
  \\ fs [cfHeapsBaseTheory.IO_def]
  \\ fs [GSYM clFFITheory.cl_ffi_part_def]
  \\ fs [set_sepTheory.SEP_EXISTS_THM,PULL_EXISTS,set_sepTheory.cond_STAR]
  \\ fs [set_sepTheory.one_def]
  \\ fs [set_sepTheory.SPLIT_def,PULL_EXISTS]
  \\ fs [EVAL “MAP FST (SND (SND fs_ffi_part))”]
  \\ qmatch_goalsub_abbrev_tac ‘Mem rr’
  \\ ‘∃v. LENGTH v ≥ 2052 ∧ Mem rr (W8array v) ∈ st2heap (basis_proj1,basis_proj2) st’ by
   (unabbrev_all_tac
    \\ fs [cfStoreTheory.st2heap_def,cfStoreTheory.store2heap_def]
    \\ fs [repl_prog_st_def]
    \\ every_case_tac \\ fs []
    \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘_ :: W8array (_::ys) :: _’
    \\ qexists_tac ‘0w::ys’ \\ fs [EVAL  “store2heap_aux 0 (W8array x :: xs)”]
    \\ unabbrev_all_tac \\ EVAL_TAC)
  \\ rpt (pop_assum $ irule_at Any)
  \\ fs [cfStoreTheory.st2heap_def,cfAppTheory.FFI_part_NOT_IN_store2heap]
  \\ simp [cfStoreTheory.ffi2heap_def]
  \\ unabbrev_all_tac
  \\ pop_assum mp_tac
  \\ simp [repl_prog_st_def]
  \\ disch_then (assume_tac o GSYM) \\ fs [parts_ok_basis_ffi]
  \\ fs [basis_proj2_def,SF DNF_ss]
  \\ fs [basis_proj1_def,SF DNF_ss]
  \\ Cases_on ‘(basis_ffi ext cl fs).ffi_state’ \\ fs []
  \\ fs [basis_ffi_def]
  \\ EVAL_TAC
QED

Theorem repl_types_repl_prog:
  Prog init_env
    (init_state (basis_ffi ext cl fs) with
     eval_state := SOME (EvalDecs (s with env_id_counter := ns))) xs env
    st ∧
  evaluate_decs
    (init_state (basis_ffi ext cl fs) with
     <|clock := ck; eval_state := SOME (EvalDecs s)|>) init_env (xs ++ ys) =
  (s1,res) ∧ s.env_id_counter = ns ∧ repl_prog ≼ xs ∧
  prog_syntax_ok repl_prog ∧
  (repl_prog_st ext cl fs).refs ≼ st.refs ∧
  (repl_prog_st ext cl fs).next_type_stamp ≤ st.next_type_stamp ∧
  (repl_prog_st ext cl fs).next_exn_stamp ≤ st.next_exn_stamp ∧
  st.ffi = (repl_prog_st ext cl fs).ffi ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧
  hasFreeFD fs ∧ file_content fs «config_enc_str.txt» = SOME content
  ⇒
  res = Rerr (Rabort Rtimeout_error) ∨
  ∃ck1 r1 env_cl e_cl s_cl res_cl.
    evaluate_decs (st with clock := ck1) (merge_env env init_env) ys =
    (s1,r1) ∧ combine_dec_result env r1 = res ∧
    repl_types repl_input_catalogue repl_input_slots T
      (basis_ffi ext cl fs,repl_rs)
      (repl_prog_types,st with <|eval_state := NONE; clock := ck1|>,
       repl_init_env) ∧
    do_opapp [CommandLine_arguments_v; Conv NONE []] = SOME (env_cl,e_cl) ∧
    evaluate (st with <|eval_state := NONE; clock := ck1 − entry_cost|>) env_cl
      [e_cl] = (s_cl,res_cl) ∧
    (res_cl ≠ Rerr (Rabort Rtimeout_error) ⇒
     ∃cl_v.
       LIST_TYPE STRING_TYPE (TL cl) cl_v ∧ res_cl = Rval [cl_v] ∧
       ∀ck junk. ∃env_pr e_pr res_pr s_pr.
         do_opapp [Repl_charsFrom_v; Litv (StrLit «config_enc_str.txt»)] =
         SOME (env_pr,e_pr) ∧
         evaluate
           (s_cl with
            <|clock := s_cl.clock − (ck + 3); refs := s_cl.refs ++ junk|>)
           env_pr [e_pr] = (s_pr,res_pr) ∧
         (res_pr ≠ Rerr (Rabort Rtimeout_error) ⇒
          ∃pr_v.
            res_pr = Rval [pr_v] ∧ LIST_TYPE CHAR content pr_v ∧
            repl_types repl_input_catalogue repl_input_slots T
              (basis_ffi ext cl fs,repl_rs)
              (repl_prog_types,s_pr,repl_init_env)))
Proof
  rpt strip_tac
  \\ gvs [evaluate_decs_append,merge_env_intro]
  \\ ‘(s with env_id_counter := s.env_id_counter) = s’ by
      fs [semanticPrimitivesTheory.eval_decs_state_component_equality]
  \\ fs [] \\ pop_assum kall_tac
  \\ qabbrev_tac ‘st4 = init_state (basis_ffi ext cl fs) with eval_state := SOME (EvalDecs s)’
  \\ qpat_x_assum ‘Prog init_env st4 _ _ _’ mp_tac
  \\ simp [Once Prog_def] \\ strip_tac
  \\ qmatch_asmsub_rename_tac
       `evaluate_decs (st4 with clock := initial_clock) init_env xs =
         (st with clock := final_clock,Rval env)`
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ fs []
  \\ namedCases_on `evaluate_decs (st4 with clock := ck) init_env xs`
       ["prefix_state prefix_result"] \\ gvs []
  \\ Cases_on `prefix_result = Rerr (Rabort Rtimeout_error)` >- gvs []
  \\ dxrule evaluatePropsTheory.evaluate_decs_add_to_clock
  \\ dxrule evaluatePropsTheory.evaluate_decs_add_to_clock
  \\ fs []
  \\ disch_then (qspec_then ‘ck’ assume_tac)
  \\ disch_then (qspec_then `initial_clock` assume_tac)
  \\ gvs []
  \\ `prefix_state = st with clock := prefix_state.clock` by gvs [semanticPrimitivesTheory.state_component_equality]
  \\ qpat_x_assum ‘_ = (s1,res)’ mp_tac
  \\ pop_assum (once_rewrite_tac o single)
  \\ CASE_TAC \\ strip_tac \\ gvs []
  \\ qexists_tac `prefix_state.clock` \\ fs []
  \\ simp [GSYM PULL_EXISTS]
  \\ conj_asm1_tac >- (
    qmatch_goalsub_rename_tac `st with <|clock := prefix_state.clock; eval_state := NONE|>` >>
    mp_tac (Q.ISPECL [`T`,`basis_ffi ext cl fs`] repl_input_initial_reachable) >>
    rewrite_tac [GSYM repl_prog_st_input,GSYM repl_init_env_input] >>
    strip_tac >> drule repl_types_set_clock >>
    disch_then (qspec_then `prefix_state.clock` assume_tac) >>
    irule repl_types_skip_alt >>
    qexists_tac `repl_prog_st ext cl fs with clock := prefix_state.clock` >>
    simp [] >> simp [repl_prog_st_def])
  \\ qmatch_goalsub_abbrev_tac ‘evaluate s12’
  \\ ‘∃h_i h_k.
        SPLIT (st2heap (basis_proj1,basis_proj2) s12) (h_i,h_k) ∧
        (COMMANDLINE cl * STDIO fs) h_i’ by
   (fs [cfStoreTheory.st2heap_def,Abbr‘s12’]
    \\ qpat_x_assum ‘st.ffi = _’ (assume_tac o GSYM)
    \\ fs [GSYM cfStoreTheory.st2heap_def]
    \\ drule_all st2heap_basis
    \\ strip_tac \\ first_x_assum $ irule_at $ Pos hd \\ fs [])
  \\ drule_all CommandLine_arguments_lemma
  \\ strip_tac \\ fs []
  \\ fs [cfAppTheory.evaluate_ck_def]
  \\ qmatch_asmsub_rename_tac
       `evaluate (s12 with clock := command_clock) command_env [command_exp] =
         (command_state,Rval [command_value])`
  \\ qmatch_asmsub_rename_tac
       `SPLIT (st2heap (basis_proj1,basis_proj2) s12) (initial_io_heap,frame_heap)`
  \\ qmatch_asmsub_rename_tac
       `SPLIT3 (st2heap (basis_proj1,basis_proj2) command_state)
         (command_io_heap,frame_heap,command_junk_heap)`
  \\ drule evaluatePropsTheory.evaluate_set_init_clock \\ fs []
  \\ disch_then $ qspec_then ‘s12.clock’ mp_tac \\ fs []
  \\ strip_tac \\ gvs []
  \\ rpt gen_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate s13’
  \\ drule Repl_charsFrom_lemma \\ simp []
  \\ `?h1 h2. SPLIT (st2heap (basis_proj1,basis_proj2) s13) (h1,h2) /\
              (COMMANDLINE cl * STDIO fs) h1`
  by (
    qpat_x_assum `SPLIT3 _ _` mp_tac \\ unabbrev_all_tac
    \\ qpat_x_assum `(COMMANDLINE cl * STDIO fs) command_io_heap` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [cfStoreTheory.st2heap_def,cfAppTheory.store2heap_append_many]
    \\ rename [‘x ∪ y ∪ z’]
    \\ fs [set_sepTheory.SPLIT_def,cfHeapsBaseTheory.SPLIT3_def]
    \\ rw [] \\ last_x_assum $ irule_at $ Pos last
    \\ qexists_tac `(frame_heap UNION command_junk_heap UNION y) DIFF command_io_heap`
    \\ fs [UNION_ASSOC]
    \\ fs [IN_DISJOINT,EXTENSION] \\ metis_tac [])
  \\ disch_then drule_all
  \\ strip_tac \\ fs []
  \\ fs [cfAppTheory.evaluate_ck_def]
  \\ drule evaluatePropsTheory.evaluate_set_init_clock \\ fs []
  \\ qmatch_asmsub_rename_tac
       `evaluate (s13 with clock := config_clock) config_env [config_exp] =
         (config_state,Rval [config_value])`
  \\ disch_then $ qspec_then ‘s13.clock’ mp_tac \\ fs []
  \\ strip_tac \\ gvs []
  \\ drule_then (qspec_then ‘1’ assume_tac) repl_types_clock \\ gvs []
  \\ assume_tac infertype_prog_inc_CommandLine_arguments
  \\ drule_then (qspec_then `command_clock+1` assume_tac) repl_types_set_clock
  \\ drule_then drule repl_types_eval \\ fs []
  \\ pop_assum kall_tac
  \\ simp [evaluateTheory.evaluate_decs_def,astTheory.pat_bindings_def]
  \\ simp [evaluateTheory.evaluate_def,
           semanticPrimitivesTheory.check_exp_constructors_def,
           semanticPrimitivesTheory.do_con_check_def]
  \\ simp [semanticPrimitivesTheory.build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [evaluateTheory.dec_clock_def,semanticPrimitivesTheory.pmatch_def,
         extend_dec_env_empty,Abbr‘s12’]
  \\ strip_tac
  \\ drule_then (qspec_then ‘junk’ assume_tac) repl_types_refs \\ fs []
  \\ drule_then (qspec_then `config_clock+1` assume_tac) repl_types_set_clock
  \\ assume_tac infertype_prog_inc_Repl_charsFrom
  \\ drule_then drule repl_types_eval \\ fs []
  \\ pop_assum kall_tac
  \\ simp [evaluateTheory.evaluate_decs_def,astTheory.pat_bindings_def]
  \\ simp [evaluateTheory.evaluate_def,
           semanticPrimitivesTheory.check_exp_constructors_def,
           semanticPrimitivesTheory.do_con_check_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [evaluateTheory.dec_clock_def,semanticPrimitivesTheory.pmatch_def,
         extend_dec_env_empty,Abbr‘s13’]
  \\ strip_tac
  \\ irule repl_types_set_clock
  \\ asm_rewrite_tac []
QED
