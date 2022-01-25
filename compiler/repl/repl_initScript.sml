(*
  Proves repl_types for the initial env and types from which the REPL starts.
*)
open preamble
     ml_progTheory ml_progLib repl_typesTheory
     repl_init_envProgTheory repl_moduleProgTheory repl_init_typesTheory

val _ = new_theory "repl_init";

val _ = (max_print_depth := 12);

val th1 = repl_prog_types_thm
val th2 = Decls_repl_prog |> REWRITE_RULE [GSYM repl_prog_def,SNOC]

val _ = Parse.hide "types"

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

Triviality merge_env_intro:
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

Theorem repl_rs_thm[local]:
  EVERY (check_ref_types (FST repl_prog_types) repl_init_env) repl_rs
Proof
  fs [repl_rs_def,check_ref_types_def]
  \\ rewrite_tac [repl_prog_types_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ EVAL_TAC \\ fs [nextString_def,isEOF_def,the_Loc_def,exn_def]
QED

Theorem repl_types_repl_prog =
  imp_repl_types
  |> C MATCH_MP th1
  |> C MATCH_MP th2
  |> REWRITE_RULE [merge_env_intro]
  |> C MATCH_MP repl_rs_thm;

val _ = export_theory();
