open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     hello_ag32ProgTheory hello_ag32CompileTheory

val _ = new_theory"hello_ag32Proof";

val hello_outputs_def =
  new_specification("hello_outputs_def",["hello_outputs"],
  hello_semantics);

val (hello_sem,hello_output) = hello_outputs_def |> CONJ_PAIR
val (hello_not_fail,hello_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail hello_sem |> CONJ_PAIR

val ffi_names =
  ``config.ffi_names``
  |> (REWRITE_CONV[hello_ag32CompileTheory.config_def] THENC EVAL)

val hello_machine_config_def = Define`
  hello_machine_config r0 = <|
    target := ag32_target;
    ptr_reg := 1;
    len_reg := 2;
    ptr2_reg := 3;
    len2_reg := 4;
    callee_saved_regs := [60; 61; 62];
    ffi_names := ^(rand(rconc ffi_names));
    ffi_entry_pcs := [r0 + 64w];
    ccache_pc := r0 + 64w +  n2w ffi_offset;
    halt_pc := r0 + 64w + n2w (2 * ffi_offset) ;
    prog_addresses := { w | r0 + 64w + n2w (3 * ffi_offset) <=+ w ∧ w <+ r0 + (n2w (128 * 2 ** 10)) }
  |>`

val is_ag32_machine_config_hello_machine_config = Q.store_thm("is_ag32_machine_config_hello_machine_config",
  `is_ag32_machine_config (hello_machine_config r0)`, EVAL_TAC);

val hello_init_memory_def = Define`
  hello_init_memory (k:word32) = (0w:word8)`;

val hello_init_regs_def = Define`
  hello_init_regs (k:num) = (0w:word32)`;

val hello_init_ag32_state_def = Define`
  hello_init_ag32_state (r0:word32) = <|
    PC := r0 + 64w + n2w (3 * ffi_offset) ;
    MEM := hello_init_memory ;
    R := hello_init_regs o w2n
  |>`;

val hello_init_asm_state_def = Define`
  hello_init_asm_state (r0:word32) = <|
    be := F;
    lr := 0 ;
    failed := F ;
    align := 2 ;
    pc := r0 + 64w + n2w (3 * ffi_offset);
    mem := hello_init_memory ;
    mem_domain := (hello_machine_config r0).prog_addresses ;
    regs := hello_init_regs
  |>`;

val hello_good_init_state = Q.store_thm("hello_good_init_state",
  `aligned 2 r0 ⇒
   good_init_state (hello_machine_config r0) (hello_init_ag32_state r0)
     ag_ffi code 0 (hello_init_asm_state r0) m
       ({w | (hello_init_asm_state r0).regs 2 <=+ w ∧ w <+ (hello_init_asm_state r0).regs 4}
        ∪ bitmaps_dm) io_regs cc_regs`,
  strip_tac
  \\ simp[lab_to_targetProofTheory.good_init_state_def]
  \\ conj_tac
  >- (
    simp[asmPropsTheory.target_state_rel_def]
    \\ simp[EVAL``(hello_machine_config r0).target``]
    \\ conj_tac
    >- (
      simp[ag32_targetTheory.ag32_ok_def, hello_init_ag32_state_def]
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
          |> irule)
      \\ reverse conj_tac >- EVAL_TAC
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
          |> irule)
      \\ reverse conj_tac >- EVAL_TAC
      \\ fs[] )
    \\ conj_tac >- EVAL_TAC
    \\ conj_tac >- (EVAL_TAC \\ rw[])
    \\ EVAL_TAC \\ rw[] )
  \\ conj_tac
  >- (
    simp[lab_to_targetProofTheory.target_configured_def]
    \\ conj_tac >- EVAL_TAC
    \\ simp[EVAL``(hello_machine_config r0).target``]
    \\ simp[hello_init_asm_state_def]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ Cases
    \\ rewrite_tac[word_add_n2w]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ qx_gen_tac`m`
    \\ cheat (* target_configured needs to be fixed *) )
  \\ conj_tac >- EVAL_TAC
  \\ `r0 + 64w + 48w && 3w = 0w` by (
    fs[alignmentTheory.aligned_bitwise_and]
    \\ Cases_on`r0`
    \\ simp[word_add_n2w]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ qpat_x_assum`_ = 0w`mp_tac
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ simp[] )
  \\ `r0 + 64w + 48w && 1w = 0w` by (
    fs[alignmentTheory.aligned_bitwise_and]
    \\ Cases_on`r0`
    \\ simp[word_add_n2w]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_1]
    \\ qpat_x_assum`_ && n2w n = 0w`mp_tac
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ simp[]
    \\ DEP_ONCE_REWRITE_TAC[LESS_MOD]
    \\ conj_tac
    >- (
      match_mp_tac LESS_LESS_EQ_TRANS
      \\ qexists_tac`4`
      \\ simp[MOD_LESS] )
    \\ strip_tac
    \\ DEP_ONCE_REWRITE_TAC[LESS_MOD]
    \\ conj_tac
    >- (
      match_mp_tac LESS_LESS_EQ_TRANS
      \\ qexists_tac`2`
      \\ simp[MOD_LESS] )
    \\ fs[MOD_EQ_0_DIVISOR]
    \\ qexists_tac`2 * d`
    \\ simp[] )
  \\ conj_tac
  >- (
    rewrite_tac[lab_to_targetProofTheory.start_pc_ok_def]
    \\ conj_tac >- cheat (* word proof, may need to tweak prog_addresses? or add assums? *)
    \\ conj_tac >- cheat (* word proof, may need to tweak prog_addresses? or add assums? *)
    \\ conj_tac >- (EVAL_TAC \\ simp[])
    \\ conj_tac >- (EVAL_TAC \\ simp[])
    \\ conj_tac >- ( EVAL_TAC \\ fs[] )
    \\ rewrite_tac[EVAL``(hello_machine_config r0).ffi_names``]
    \\ reverse Cases >- rw[]
    \\ strip_tac
    \\ conj_tac >- cheat (* word proof, may need to tweak prog_addresses? or add assums? *)
    \\ conj_tac >- cheat (* word proof, may need to tweak prog_addresses? or add assums? *)
    \\ conj_tac >- cheat (* word proof, may need to tweak prog_addresses? or add assums? *)
    \\ EVAL_TAC \\ rw[] )
  \\ conj_tac >- ( EVAL_TAC \\ fs[] )
  \\ conj_tac >- (
    rw[asmPropsTheory.interference_ok_def]
    \\ simp[EVAL``(hello_machine_config r0).target``]
    \\ cheat (* set next_interfer to identity function? *) )
  \\ conj_tac >- cheat (* ffi - set ffi_interfer based on hello outputs and some function modeling the print call? *)
  \\ conj_tac >- cheat (* set ccache_interfer to identity function? *)
  \\ conj_tac >- cheat (* set hello_init_memory to contain the code at the right pc *)
  \\ conj_tac >- cheat (* code in memory again? *)
  \\ cheat);

val compile_correct_applied =
  MATCH_MP compile_correct hello_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP hello_not_fail
  |> C MATCH_MP ag32_backend_config_ok
  |> REWRITE_RULE[hello_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH ag32_machine_config_ok)(UNDISCH ag32_init_ok))
  |> DISCH(#1(dest_imp(concl ag32_init_ok)))
  |> C MATCH_MP is_ag32_machine_config_hello_machine_config
  |> Q.GEN`cbspace` |> Q.SPEC`0`
  |> Q.GEN`data_sp` |> Q.SPEC`0`
  |> Q.GEN`ms` |> SPEC(lhs(concl(SPEC_ALL hello_init_ag32_state)))

(*
val goal = compile_correct_applied |> concl |> dest_imp |> #1
set_goal([],goal)
CONV_TAC(PATH_CONV"llr"EVAL)
\\ rw[backendProofTheory.installed_def]
*)

val _ = export_theory();
