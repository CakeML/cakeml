(*
  Proves repl_types for the initial env and types from which the REPL starts.
*)
open preamble
     ml_progTheory ml_progLib repl_typesTheory basis_ffiTheory
     repl_init_envProgTheory repl_moduleProgTheory repl_init_typesTheory

val _ = new_theory "repl_init";

val _ = (max_print_depth := 12);

val th1 = repl_prog_types_thm
val th2 = Decls_repl_prog |> REWRITE_RULE [GSYM repl_prog_def,SNOC]

val _ = Parse.hide "types"

(*
Theorem imp_repl_types[local]:
  infertype_prog_inc (init_config,start_type_id) decs = Success types ⇒
  Decls init_env (init_state ffi) decs env s0 ⇒
  EVERY (check_ref_types (FST types) (extend_dec_env env init_env)) rs ⇒
  evaluate_decs (init_state ffi with clock := ck) init_env decs1 = (s,Rval env) ⇒
  isPREFIX decs decs1 ⇒
  ∃ck.
    repl_types T (ffi,rs) (types,s with clock := ck,extend_dec_env env init_env)
Proof
  rw [] \\ fs [Decls_def]
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ fs []
  \\ drule_all evaluatePropsTheory.evaluate_decs_add_to_clock
  \\ disch_then (qspec_then ‘ck1’ mp_tac) \\ fs []
  \\ ntac 2 (pop_assum mp_tac)
  \\ drule evaluatePropsTheory.evaluate_decs_add_to_clock
  \\ disch_then (qspec_then ‘ck’ mp_tac) \\ fs [] \\ rw []
  \\ fs [semanticPrimitivesTheory.state_component_equality]
  \\ irule_at Any repl_types_init
  \\ last_x_assum $ irule_at Any
  \\ last_x_assum $ irule_at Any
  \\ fs []
QED
*)

Theorem imp_repl_types[local]:
  infertype_prog_inc (init_config,start_type_id) decs = Success types ⇒
  Decls init_env (init_state ffi) decs env s0 ⇒
  EVERY (check_ref_types (FST types) (extend_dec_env env init_env)) rs ⇒
  evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,res) ⇒
  res = Rerr (Rabort Rtimeout_error) ∨
  res = Rval env ∧
  ∃ck.
    s = (s0 with clock := s.clock) ∧
    repl_types T (ffi,rs) (types,s0 with clock := ck,extend_dec_env env init_env)
Proof
  rw [] \\ fs [Decls_def]
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ fs []
  \\ drule_all evaluatePropsTheory.evaluate_decs_add_to_clock
  \\ disch_then (qspec_then ‘ck1’ mp_tac) \\ fs []
  \\ ntac 2 (pop_assum mp_tac)
  \\ drule evaluatePropsTheory.evaluate_decs_add_to_clock
  \\ disch_then (qspec_then ‘ck’ mp_tac) \\ fs [] \\ rw []
  \\ fs [semanticPrimitivesTheory.state_component_equality]
  \\ irule_at Any repl_types_init
  \\ last_x_assum $ irule_at Any
  \\ last_x_assum $ irule_at Any
  \\ fs []
QED

Theorem merge_env_intro:
  extend_dec_env = merge_env
Proof
  fs [FUN_EQ_THM,semanticPrimitivesTheory.extend_dec_env_def,merge_env_def]
QED

Definition the_Loc_def:
  the_Loc (semanticPrimitives$Loc n) = n
End

Definition repl_rs_def:
  repl_rs = [(Long "REPL" (Short "isEOF"),      Bool, the_Loc isEOF_loc);
             (Long "REPL" (Short "nextString"), Str,  the_Loc nextString_loc);
             (Long "REPL" (Short "exn"),        Exn,  the_Loc exn)]
End

Overload repl_init_env =
  (repl_init_envProg_env_def |> concl
   |> find_term (can (match_term “Env _”)) |> rand);

Theorem repl_rs_thm:
  EVERY (check_ref_types (FST repl_prog_types) repl_init_env) repl_rs
Proof
  fs [repl_rs_def,check_ref_types_def]
  \\ rewrite_tac [repl_prog_types_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ EVAL_TAC \\ fs [nextString_def,isEOF_def,the_Loc_def,exn_def]
QED

(*
Theorem repl_types_repl_prog =
  imp_repl_types
  |> C MATCH_MP th1
  |> C MATCH_MP th2
  |> REWRITE_RULE [merge_env_intro]
  |> C MATCH_MP repl_rs_thm;
*)

Theorem Decls_evaluate_decs_lemma:
  infertype_prog_inc (init_config,start_type_id) decs = Success types ⇒
  Decls init_env (init_state (basis_ffi cl fs)) decs env1 s_basis ⇒
  EVERY (check_ref_types (FST types) (extend_dec_env env1 init_env)) rs ⇒
  Decls init_env
    (init_state (basis_ffi cl fs) with
     eval_state := SOME (EvalDecs (s with env_id_counter := ns))) xs env st ∧
  evaluate_decs
    (init_state (basis_ffi cl fs) with
     <|clock := ck; eval_state := SOME (EvalDecs s)|>) init_env (xs ++ ys) = (s1,res) ∧
  s.env_id_counter = ns ∧
  isPREFIX s_basis.refs st.refs ∧
  s_basis.next_type_stamp ≤ st.next_type_stamp ∧
  s_basis.next_exn_stamp ≤ st.next_exn_stamp ∧
  st.ffi = s_basis.ffi ∧
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  file_content fs (strlit "config_enc_str.txt") = SOME content ⇒
  res = Rerr (Rabort Rtimeout_error) ∨
  ∃ck1 env_cl e_cl s_cl res_cl.
    evaluate_decs (st with clock := ck1) env ys = (s1,res) ∧
    repl_types T (basis_ffi cl fs,rs) (types,st with
      <| eval_state := NONE; clock := ck1 |>,extend_dec_env env1 init_env) ∧
    do_opapp [CommandLine_arguments_v; Conv NONE []] = SOME (env_cl,e_cl) ∧
    evaluate (st with <| eval_state := NONE; clock := ck1 - 2 |>) env_cl
      [e_cl] = (s_cl,res_cl) ∧
    (res_cl ≠ Rerr (Rabort Rtimeout_error) ⇒
     ∃cl_v.
       LIST_TYPE STRING_TYPE (TL cl) cl_v ∧ res_cl = Rval [cl_v] ∧
       ∀ck junk hello. ∃env_pr e_pr res_pr s_pr.
         do_opapp [REPL_charsFrom_v; Litv (StrLit "config_enc_str.txt")] =
           SOME (env_pr,e_pr) ∧
         evaluate (s_cl with
                    <|clock := s_cl.clock − (ck + 3);
                      refs := s_cl.refs ++ junk |>)
                   env_pr [e_pr] = (s_pr,res_pr) ∧
         (res_pr ≠ Rerr (Rabort Rtimeout_error) ⇒
          ∃pr_v.
            res_pr = Rval [pr_v] ∧ LIST_TYPE CHAR content pr_v ∧
            repl_types T (basis_ffi cl fs,rs) (types,s_pr,extend_dec_env env1 init_env)))
Proof
  cheat
QED

Theorem repl_types_repl_prog =
  Decls_evaluate_decs_lemma
  |> C MATCH_MP th1
  |> C MATCH_MP (th2 |> Q.GEN ‘ffi’ |> Q.ISPEC ‘basis_ffi cl fs’)
  |> REWRITE_RULE [merge_env_intro]
  |> C MATCH_MP repl_rs_thm (*
  |> SIMP_RULE (srw_ss()) (find "repl_moduleProg_st" |> map (fst o snd))
  |> SIMP_RULE (srw_ss()) (find "refs_def" |> map (fst o snd)) *)

val _ = export_theory();
