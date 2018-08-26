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

val LENGTH_code =
  ``LENGTH code``
  |> (REWRITE_CONV[hello_ag32CompileTheory.code_def] THENC listLib.LENGTH_CONV)

val LENGTH_data =
  ``LENGTH data``
  |> (REWRITE_CONV[hello_ag32CompileTheory.data_def] THENC listLib.LENGTH_CONV)

val memory_size_def = Define`
  memory_size = 128 * 2 ** 20`;

val heap_size_def = Define`
  heap_size = 120 * 2 ** 20`;

(*
  hz = heap_size is the heap+stack size in mebibytes
  r0 gives the lowest software-usable address
  r0 .. r0 + 64 is used by the FFI implementation
  r0 + 64 .. r0 + hzMiB is the CakeML heap+stack space
  r0 + hzMiB .. r0 + hzMiB + 4 * LENGTH data is the bitmaps
  r0 + hzMiB + 4 * LENGTH data is the FFI PC
  r0 + hzMiB + 4 * LENGTH data + 16 is the ccache PC
  r0 + hzMiB + 4 * LENGTH data + 32 is the halt PC
  r0 + hzMiB + 4 * LENGTH data + 48 is the initial PC
  r0 + hzMiB + 4 * LENGTH data + 48 .. r0 + hzMiB + 4 * LENGTH data + 48 + LENGTH code is the code
*)

val hello_machine_config_def = Define`
  hello_machine_config r0 = <|
    target := ag32_target;
    ptr_reg := 1;
    len_reg := 2;
    ptr2_reg := 3;
    len2_reg := 4;
    callee_saved_regs := [60; 61; 62];
    ffi_names := ^(rand(rconc ffi_names));
    ffi_entry_pcs := [r0 + n2w (heap_size + 4 * LENGTH data + 0 * ffi_offset)];
    ccache_pc      := r0 + n2w (heap_size + 4 * LENGTH data + 1 * ffi_offset);
    halt_pc        := r0 + n2w (heap_size + 4 * LENGTH data + 2 * ffi_offset);
    prog_addresses :=
      { w | r0 + 64w <=+ w ∧ w <+ r0 + n2w (heap_size + 4 * LENGTH data) } ∪
      { w | r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset) <=+ w ∧ w <+ r0 + (n2w memory_size) };
    next_interfer := K I ;
    ccache_interfer := K (λ(_,_,ms). ms with PC := (ms.R 0w))
  |>`

val is_ag32_machine_config_hello_machine_config = Q.store_thm("is_ag32_machine_config_hello_machine_config",
  `is_ag32_machine_config (hello_machine_config r0)`, EVAL_TAC);

val hello_init_memory_def = Define`
  hello_init_memory r0 (k:word32) =
     if r0 + n2w heap_size <=+ k ∧ k <+ r0 + n2w (heap_size + 4 * LENGTH data) then
       get_byte k (EL (w2n (k - (r0 + n2w heap_size))) data) F
     else if r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset) <=+ k ∧
             k <+ r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset + LENGTH code) then
       EL (w2n (k - (r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset)))) code
     else if r0 + 64w + 0w * bytes_in_word ≤ k ∧ k < r0 + 64w + 1w * bytes_in_word then
       get_byte k (r0 + n2w heap_size) F
     else if r0 + 64w + 1w * bytes_in_word ≤ k ∧ k < r0 + 64w + 2w * bytes_in_word then
       get_byte k (r0 + n2w heap_size + bytes_in_word * n2w (LENGTH data)) F
     else if r0 + 64w + 2w * bytes_in_word ≤ k ∧ k < r0 + 64w + 3w * bytes_in_word then
       get_byte k (r0 + n2w heap_size + bytes_in_word * n2w (LENGTH data)) F
     else if r0 + 64w + 3w * bytes_in_word ≤ k ∧ k < r0 + 64w + 4w * bytes_in_word then
       get_byte k (r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset + LENGTH code)) F
     else if r0 + 64w + 4w * bytes_in_word ≤ k ∧ k < r0 + 64w + 5w * bytes_in_word then
       get_byte k (r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset + LENGTH code)) F
     else (0w:word8)`;

val hello_init_regs_def = Define`
  hello_init_regs r0 (k:num) =
  if k = 2 then
    r0 + 64w
  else if k = 4 then
    r0 + n2w heap_size
  else (0w:word32)`;

val hello_init_ag32_state_def = Define`
  hello_init_ag32_state (r0:word32) = <|
    PC := r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset);
    MEM := hello_init_memory r0;
    R := hello_init_regs r0 o w2n
  |>`;

val hello_init_asm_state_def = Define`
  hello_init_asm_state (r0:word32) = <|
    be := F;
    lr := 0 ;
    failed := F ;
    align := 2 ;
    pc := (hello_init_ag32_state r0).PC;
    mem := (hello_init_ag32_state r0).MEM;
    mem_domain := (hello_machine_config r0).prog_addresses ;
    regs := hello_init_regs r0
  |>`;

val hello_good_init_state = Q.store_thm("hello_good_init_state",
  `aligned 2 r0 ∧ w2n r0 + memory_size < dimword(:32) ⇒
   good_init_state (hello_machine_config r0) (hello_init_ag32_state r0)
     ag_ffi code 0 (hello_init_asm_state r0)
     (λk. Word (bytes_to_word 4 0w (GENLIST (λn. hello_init_memory r0 (k + n2w n)) 4) 0w F))
       ({w | (hello_init_asm_state r0).regs 2 <=+ w ∧
             w <+ (hello_init_asm_state r0).regs 4}
        ∪ {w | r0 + n2w heap_size <=+ w ∧
               w <+ r0 + n2w(heap_size + 4 * LENGTH data) })
     io_regs (K(K NONE))`,
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
      \\ simp[LENGTH_data]
      \\ EVAL_TAC)
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
  \\ `r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset) && 3w = 0w` by (
    fs[alignmentTheory.aligned_bitwise_and]
    \\ Cases_on`r0`
    \\ simp[word_add_n2w]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ qpat_x_assum`_ = 0w`mp_tac
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ EVAL_TAC
    \\ simp[] )
  \\ `r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset) && 1w = 0w` by (
    fs[alignmentTheory.aligned_bitwise_and]
    \\ Cases_on`r0`
    \\ simp[word_add_n2w]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_1]
    \\ qpat_x_assum`_ && n2w n = 0w`mp_tac
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ EVAL_TAC
    \\ simp[LENGTH_data]
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
  \\ conj_tac >- (
    rewrite_tac[lab_to_targetProofTheory.start_pc_ok_def]
    \\ conj_tac >- (
      qpat_x_assum`_ < _`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,LENGTH_data] )
    \\ conj_tac >- (
      qpat_x_assum`_ < _`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,LENGTH_data] )
    \\ conj_tac >- (EVAL_TAC \\ simp[LENGTH_data])
    \\ conj_tac >- (EVAL_TAC \\ simp[LENGTH_data])
    \\ conj_tac >- (
      qpat_x_assum`_ && 1w = _` mp_tac
      \\ EVAL_TAC \\ fs[] )
    \\ rewrite_tac[EVAL``(hello_machine_config r0).ffi_names``]
    \\ reverse Cases >- rw[]
    \\ strip_tac
    \\ conj_tac >- (
      qpat_x_assum`_ < dimword _`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,LENGTH_data] )
    \\ conj_tac >- (
      qpat_x_assum`_ < dimword _`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,LENGTH_data] )
    \\ conj_tac >- (
      qpat_x_assum`_ < dimword _`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,LENGTH_data] )
    \\ EVAL_TAC \\ rw[LENGTH_data] )
  \\ conj_tac >- (
    qpat_x_assum`_ && 3w = _`mp_tac
    \\ EVAL_TAC \\ fs[LENGTH_data] )
  \\ conj_tac >- (
    rw[asmPropsTheory.interference_ok_def]
    \\ simp[EVAL``(hello_machine_config r0).target``]
    \\ simp[EVAL``(hello_machine_config r0).next_interfer``] )
  \\ conj_tac >- cheat (* ffi - set ffi_interfer based on hello outputs and some function modeling the print call? *)
  \\ conj_tac >- (
    EVAL_TAC \\ rw[]
    \\ cheat (* problem with combination of ag32_ok ag32_target.config.link_reg and ccache_interfer_ok *) )
  \\ conj_tac >- (
    EVAL_TAC
    \\ match_mp_tac data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ simp[]
    \\ gen_tac \\ strip_tac
    \\ qpat_x_assum`_ < dimword _`mp_tac
    \\ EVAL_TAC
    \\ Cases_on`r0`
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, LENGTH_code, LENGTH_data]
    \\ simp[GSYM word_add_n2w, WORD_LEFT_ADD_DISTRIB])
  \\ conj_tac >- cheat (* can this be proved from the previous conjunct? *)
  \\ conj_tac >- (
    qpat_x_assum`_ < dimword _`mp_tac
    \\ EVAL_TAC
    \\ simp[SUBSET_DEF, LENGTH_code, LENGTH_data]
    \\ Cases_on`r0` \\ fs[word_add_n2w]
    \\ strip_tac
    \\ simp[GSYM FORALL_AND_THM]
    \\ Cases
    \\ fs[word_lo_n2w, word_ls_n2w])
  \\ conj_tac >- (
    qpat_x_assum`_ < dimword _`mp_tac
    \\ EVAL_TAC
    \\ fs[LENGTH_code, LENGTH_data]
    \\ Cases_on`r0` \\ fs[word_add_n2w]
    \\ strip_tac
    \\ Cases
    \\ fs[word_ls_n2w, word_lo_n2w, word_slice_n2w]
    \\ cheat (* annoying word proofs: bitmap_dm is word addressable *))
  \\ conj_tac >- (
    rw[hello_init_asm_state_def,
       EVAL``(hello_machine_config r0).target.config``,
       EVAL``(hello_init_ag32_state r0).MEM``]
    \\ `∃i. (a = i + byte_align a) ∧ w2n i < 4`
    by (
      rw[alignmentTheory.byte_align_def]
      \\ rw[alignmentTheory.align_sub]
      \\ qexists_tac`(1 >< 0)a`
      \\ rw[]
      \\ Cases_on`a`
      \\ simp[word_extract_n2w]
      \\ qspecl_then[`1`,`0`,`n`]mp_tac bitTheory.BITSLT_THM2
      \\ simp[] )
    \\ first_assum(fn th => CONV_TAC(PATH_CONV"rllr"(REWR_CONV th)))
    \\ `4n = 2 ** 2` by rw[]
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ conj_tac >- EVAL_TAC
    \\ Cases_on`i`
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_bytes_to_word]
    \\ fs[]
    \\ conj_tac >- EVAL_TAC
    \\ Cases_on`n` \\ fs[ADD1,GSYM word_add_n2w] >- metis_tac[]
    \\ qmatch_goalsub_rename_tac`EL n _`
    \\ Cases_on`n` \\ fs[ADD1,GSYM word_add_n2w] >- metis_tac[]
    \\ qmatch_goalsub_rename_tac`EL n _`
    \\ Cases_on`n` \\ fs[ADD1,GSYM word_add_n2w] >- metis_tac[]
    \\ qmatch_goalsub_rename_tac`EL n _`
    \\ Cases_on`n` \\ fs[ADD1,GSYM word_add_n2w]
    \\ metis_tac[])
  \\ simp[LENGTH_code]);

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
  |> Q.GEN`ms` |> SPEC(lhs(concl(SPEC_ALL hello_init_ag32_state_def)))

(*
val goal = compile_correct_applied |> concl |> dest_imp |> #1
           |> curry mk_imp (#1(dest_imp(concl hello_good_init_state)))
(*
set_goal([],goal)
*)
val lemma = prove(
  disch_then assume_tac
  \\ CONV_TAC(PATH_CONV"llr"EVAL)
  \\ simp[backendProofTheory.installed_def]
  \\ simp[word_list_exists_def, set_sepTheory.SEP_CLAUSES, word_list_def]
  \\ simp[EVAL``(hello_machine_config r0).target.get_pc``]
  \\ assume_tac(UNDISCH hello_good_init_state)
  \\ asm_exists_tac \\ simp[]
  \\ pop_assum kall_tac
  \\ conj_tac
  >- (
    simp[IN_DISJOINT]
    \\ pop_assum mp_tac
    \\ EVAL_TAC
    \\ simp[LENGTH_code,LENGTH_data]
    \\ strip_tac
    \\ Cases
    \\ Cases_on`r0`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] )
  \\ conj_tac
  >- (
    rw[EVAL``(hello_init_asm_state r0).regs``, LENGTH_data]
    \\ rw[hello_init_regs_def]
    \\ cheat (* prove some memory lookup rewrites separately *) )
  \\ conj_tac
*)

val _ = export_theory();
