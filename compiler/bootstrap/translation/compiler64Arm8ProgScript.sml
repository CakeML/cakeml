(*
  Native ARM8 entry point for the 64-bit compiler.
*)
Theory compiler64Arm8Prog[no_sig_docs]
Ancestors
  compiler64MainProg basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

open preamble compiler64MainProgTheory compiler64HostTheory
     ml_translatorLib ml_translatorTheory
open cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];
val _ = translation_extends "compiler64MainProg";

Quote add_cakeml:
  fun main u = main_host (Hostarm8,u)
End

val main_v_def = fetch "-" "main_v_def";

Theorem main_spec:
  ~has_repl_flag (TL cl) /\ IS_SOME (stdin_content fs) ==>
  app (p:'ffi ffi_proj) main_v [Conv NONE []]
      (STDIO fs * COMMANDLINE cl)
      (POSTv uv. &UNIT_TYPE () uv *
       STDIO (full_compile_host HostArm8 (TL cl) (get_stdin fs) fs) *
       COMMANDLINE cl)
Proof
  strip_tac
  \\ xcf_with_def main_v_def
  \\ xlet `POSTv v. &COMPILER64HOST_COMPILER64_HOST_TYPE HostArm8 v *
                (STDIO fs * COMMANDLINE cl)`
  >- (
    simp [cfTheory.cf_con_def,semanticPrimitivesTheory.do_con_check_def,
          semanticPrimitivesTheory.build_conv_def,cfNormaliseTheory.exp2v_list_def,
          cfTheory.extend_env_rec_def,ml_progTheory.merge_env_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
    \\ simp [COMPILER64HOST_COMPILER64_HOST_TYPE_def]
    \\ irule cfHeapsTheory.local_elim
    \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ gvs []
  \\ xapp_spec main_host_spec
  \\ simp []
QED

Theorem main_whole_prog_spec:
  ~has_repl_flag (TL cl) /\ IS_SOME (stdin_content fs) ==>
  whole_prog_spec main_v cl fs NONE
    ((=) (full_compile_host HostArm8 (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ simp [basis_ffiTheory.whole_prog_spec_def]
  \\ qexists_tac `full_compile_host HostArm8 (TL cl) (get_stdin fs) fs`
  \\ reverse conj_tac
  >- simp [GSYM full_compile_host_with_numchars,with_same_numchars]
  \\ simp [SEP_CLAUSES]
  \\ irule (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH main_spec)))
  \\ simp []
  \\ qexistsl_tac [`emp`,`cl`,`fs`]
  \\ simp []
  \\ xsimpl
QED

Theorem dec_sides[local]:
  (peg_v_side <=> T) /\
  (peg_longv_side <=> T) /\
  (peg_uqconstructorname_side <=> T) /\
  (cmlpeg_side <=> T)
Proof
  fs [parserProgTheory.cmlpeg_side_def,parserProgTheory.peg_v_side_def,
      parserProgTheory.peg_longv_side_def,
      parserProgTheory.peg_uqconstructorname_side_def]
QED

val sem_thm = prove_sem_thm "main" "compiler64_arm8_prog" main_whole_prog_spec;
val compiler64_arm8_prog_def = fetch "-" "compiler64_arm8_prog_def";

Theorem semantics_compiler64_arm8_prog:
  ~has_repl_flag (TL cl) /\ IS_SOME (stdin_content fs) /\ wfcl cl /\ wfFS fs /\
  STD_streams fs ==>
  ?io_events.
    semantics_dec_list
      (init_state (basis_ffi ext cl fs) with
       eval_state := SOME (EvalDecs
         (eval_state_var with env_id_counter := (0,0,1))))
      init_env compiler64_arm8_prog (Terminate Success io_events) /\
    extract_fs ext (cl,fs) io_events =
      SOME (full_compile_host HostArm8 (TL cl) (get_stdin fs) fs)
Proof
  strip_tac
  \\ irule sem_thm
  \\ fs [dec_sides]
QED

val main_decls_thm = get_ml_prog_state ()
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def];

Theorem BUTLAST_compiler64_arm8_prog[local]:
  ^(mk_eq (concl main_decls_thm |> rator |> rator |> rand,
           ``BUTLAST compiler64_arm8_prog``))
Proof
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [compiler64_arm8_prog_def]))
  \\ CONV_TAC (RAND_CONV (PURE_REWRITE_CONV [listTheory.FRONT_CONS]))
  \\ rewrite_tac []
QED

Theorem Decls_FRONT_compiler64_arm8_prog =
  main_decls_thm
  |> CONV_RULE (PATH_CONV "llr" (REWR_CONV BUTLAST_compiler64_arm8_prog))
  |> CONV_RULE (RAND_CONV
       (EVAL THENC REWRITE_CONV (DB.find "_refs_def" |> map (#1 o #2)) THENC
        SIMP_CONV std_ss [APPEND_NIL,APPEND]))
  |> DISCH_ALL |> REWRITE_RULE [dec_sides];

Theorem LAST_compiler64_arm8_prog:
  LAST compiler64_arm8_prog =
    Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short «main»); Con NONE []])
Proof
  CONV_TAC (LAND_CONV
    (ONCE_REWRITE_CONV [compiler64_arm8_prog_def] THENC
     PURE_REWRITE_CONV [listTheory.LAST_CONS]))
  \\ REFL_TAC
QED

val _ = semantics_compiler64_arm8_prog |> check_thm;
val _ = Decls_FRONT_compiler64_arm8_prog |> check_thm;
val _ = LAST_compiler64_arm8_prog |> check_thm;
val _ = ml_translatorLib.reset_translation ();
