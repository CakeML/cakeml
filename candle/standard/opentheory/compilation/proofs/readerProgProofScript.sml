(*
  End-to-end correctness theorems for the OpenTheory article checker.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     readerProgTheory readerCompileTheory readerProofTheory
     readerSoundnessTheory;

val _ = new_theory "readerProgProof";

val reader_io_events_def = new_specification (
  "reader_io_events_def", ["reader_io_events"],
  reader_semantics
  |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (reader_sem, reader_output) =
  reader_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR;

val (reader_not_fail, reader_sem_sing) =
  MATCH_MP semantics_prog_Terminate_not_Fail reader_sem |> CONJ_PAIR;

val compile_correct_applied =
  MATCH_MP compile_correct reader_compiled
  |> SIMP_RULE (srw_ss()) [LET_THM, ml_progTheory.init_state_env_thm,
                           GSYM AND_IMP_INTRO]
  |> C MATCH_MP reader_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE [reader_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE [Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ (UNDISCH x64_machine_config_ok) (UNDISCH x64_init_ok))
  |> DISCH (#1 (dest_imp (concl x64_init_ok)))
  |> REWRITE_RULE [AND_IMP_INTRO];

Theorem reader_compiled_thm =
  CONJ compile_correct_applied reader_output
  |> DISCH_ALL
  |> check_thm;

(*
 * This makes the theorem prettier.
 * Does a good alternative already exist somewhere?
 *)

val installed_x64_def = Define `
  installed_x64 ((code, data, cfg) :
      (word8 list # word64 list # 64 lab_to_target$config))
    ffi mc ms
  <=>
    ?cbspace data_sp.
      is_x64_machine_config mc /\
      installed
        code cbspace
        data data_sp
        cfg.ffi_names
        ffi
        (heap_regs x64_backend_config.stack_conf.reg_names) mc ms
    `;

val reader_code_def = Define `
  reader_code = (code, data, config)
  `;

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U->bool``;

Theorem machine_code_sound:
   input_exists fs cl /\ wfcl cl /\ wfFS fs /\ STD_streams fs
   ==>
   (installed_x64 reader_code (basis_ffi cl fs) mc ms
    ==>
    machine_sem mc (basis_ffi cl fs) ms ⊆
      extend_with_resource_limit
        {Terminate Success (reader_io_events cl fs)}) /\
   ?fs_out hol_refs s.
      extract_fs fs (reader_io_events cl fs) = SOME fs_out /\
      (no_errors fs fs_out ==>
       reader_main fs init_refs (TL cl) = (fs_out, hol_refs, SOME s) /\
       hol_refs.the_context extends init_ctxt /\
       fs_out = add_stdout (flush_stdin (TL cl) fs)
                           (msg_success s hol_refs.the_context) /\
      !asl c.
        MEM (Sequent asl c) s.thms /\
        is_set_theory ^mem
        ==>
        (thyof hol_refs.the_context, asl) |= c)
Proof
  metis_tac [installed_x64_def, reader_code_def, reader_compiled_thm, PAIR,
              FST, SND, reader_success_stderr, input_exists_def,
              reader_sound]
QED

val _ = export_theory ();

