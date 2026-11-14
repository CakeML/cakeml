(*
  Native x64 entry point for the Pancake compiler.
*)
Theory pancake_compiler_x64Prog[no_sig_docs]
Ancestors
  pancake_compilerProg basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];
val _ = translation_extends "pancake_compilerProg";

Quote add_cakeml:
  fun main u = main_target (Pancakex64,u)
End

val main_v_def = fetch "-" "main_v_def";

val target_env_defs = let
  val ml_progLib.ML_code (_, env_defs, _, _) = get_ml_prog_state ()
  in List.filter (fn th =>
    #Thy (dest_thy_const (lhs (concl th))) = "pancake_compilerProg") env_defs end;

Theorem main_spec:
  IS_SOME (stdin_content fs) ==>
  app (p:'ffi ffi_proj) main_v [Conv NONE []]
      (STDIO fs * COMMANDLINE cl)
      (POSTv uv. &UNIT_TYPE () uv *
       STDIO (pancake_compiler$full_compile PancakeX64 (TL cl) (get_stdin fs) fs) *
       COMMANDLINE cl)
Proof
  strip_tac
  \\ xcf_with_def main_v_def
  \\ xlet `POSTv v. &PANCAKE_COMPILER_TARGET_TYPE PancakeX64 v *
                (STDIO fs * COMMANDLINE cl)`
  >- (
    simp [cfTheory.cf_con_def,semanticPrimitivesTheory.do_con_check_def,
          semanticPrimitivesTheory.build_conv_def,cfNormaliseTheory.exp2v_list_def,
          cfTheory.extend_env_rec_def,ml_progTheory.merge_env_def]
    \\ simp (target_env_defs @
         [ml_progTheory.write_simp,ml_progTheory.write_cons_simp,
          ml_progTheory.nsLookup_nsAppend_Short])
    \\ simp [PANCAKE_COMPILER_TARGET_TYPE_def]
    \\ irule cfHeapsTheory.local_elim
    \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ gvs []
  \\ xapp_spec main_target_spec
  \\ simp []
QED

Theorem main_whole_prog_spec:
  IS_SOME (stdin_content fs) ==>
  whole_prog_spec main_v cl fs NONE
    ((=) (pancake_compiler$full_compile PancakeX64 (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ simp [basis_ffiTheory.whole_prog_spec_def]
  \\ qexists_tac
       `pancake_compiler$full_compile PancakeX64 (TL cl) (get_stdin fs) fs`
  \\ reverse conj_tac
  >- simp [GSYM pancake_compilerTheory.full_compile_with_numchars,
           with_same_numchars]
  \\ simp [SEP_CLAUSES]
  \\ irule (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH main_spec)))
  \\ simp []
  \\ qexistsl_tac [`emp`, `cl`, `fs`]
  \\ simp [] \\ xsimpl
QED

val sem_thm = prove_sem_thm "main" "pancake_compiler_x64_prog" main_whole_prog_spec;
val pancake_compiler_x64_prog_def = fetch "-" "pancake_compiler_x64_prog_def";

Theorem semantics_pancake_compiler_x64_prog:
  IS_SOME (stdin_content fs) /\ wfcl cl /\ wfFS fs /\ STD_streams fs ==>
  sem_satisfies
    (semantics_dec_list
      (init_state (basis_ffi ext cl fs) with
       eval_state := SOME (EvalDecs
         (eval_state_var with env_id_counter := (0,0,1))))
      init_env pancake_compiler_x64_prog)
    (λbehaviour. ∃io_events.
       behaviour = Terminate Success io_events /\
       extract_fs ext (cl,fs) io_events =
         SOME (pancake_compiler$full_compile PancakeX64 (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ irule sem_thm
  \\ fs []
QED

val _ = semantics_pancake_compiler_x64_prog |> check_thm;
val _ = ml_translatorLib.reset_translation ();
