(*
  End-to-end correctness theorems for the OpenTheory article checker.
*)
Theory readerProgProof
Ancestors
  semanticsProps backendProof x64_configProof readerProg
  readerCompile readerProof readerSoundness
Libs
  preamble

val reader_terminate = UNDISCH_ALL reader_semantics
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [reader_compiled];

Theorem reader_compiled_thm =
  MATCH_MP compile_correct (cj 1 reader_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 reader_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 reader_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (UNDISCH is_x64_machine_config_IMP)
  |> SRULE [SF CONJ_ss] |> CONJUNCT2 |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> check_thm;

(*
 * This makes the theorem prettier.
 * Does a good alternative already exist somewhere?
 *)

Definition installed_x64_def:
  installed_x64 ((code, data, cfg) :
      (word8 list # num list # backend$config))
    mc ms ⇔
    ∃cbspace data_sp.
      is_x64_machine_config mc ∧
      installed
        code cbspace
        data data_sp
        cfg.lab_conf.ffi_names
        (heap_regs x64_backend_config.stack_conf.reg_names) mc
        cfg.lab_conf.shmem_extra ms
End

Definition reader_code_def:
  reader_code = (code, data, info)
End

val _ = Parse.hide "mem";
val mem = “mem: 'U -> 'U -> bool”;

Theorem machine_code_sound:
   input_exists fs cl ∧
   wfcl cl ∧
   wfFS fs ∧
   STD_streams fs ∧
   installed_x64 reader_code mc ms ⇒
   ∃io.
     machine_sem mc (basis_ffi ext cl fs) ms ⊆
       extend_with_resource_limit {Terminate Success io} ∧
     ∃fs_out hol_refs s.
       extract_fs ext (cl,fs) io = SOME fs_out ∧
       (no_errors fs fs_out ⇒
          reader_main fs init_refs (TL cl) = (fs_out, hol_refs, SOME s) ∧
          hol_refs.the_context extends init_ctxt ∧
          fs_out =
            flush_stdin_cl (TL cl)
              (add_stdout fs (concat (append (msg_success s hol_refs.the_context)))) ∧
       ∀asl c.
         MEM (Sequent asl c) s.thms ∧
         is_set_theory ^mem ⇒
           (thyof hol_refs.the_context, asl) |= c)
Proof
  rpt strip_tac
  \\ gvs [installed_x64_def, reader_code_def]
  \\ drule_at (Pos (el 2)) reader_compiled_thm
  \\ disch_then (qspecl_then [`fs`,`ext`,`cl`] mp_tac)
  \\ simp [] \\ strip_tac
  \\ goal_assum drule
  \\ `∃fs' refs s. reader_main fs init_refs (TL cl) = (fs',refs,s)`
         by metis_tac [PAIR]
  \\ gvs []
  \\ reverse (Cases_on `no_errors fs fs'`) >- simp []
  \\ drule reader_success_stderr
  \\ gvs [input_exists_def] \\ strip_tac \\ gvs []
  \\ drule reader_sound
  \\ simp []
QED
