open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     hello_ag32ProgTheory hello_ag32CompileTheory

val _ = new_theory"hello_ag32Proof";

(* TODO: move *)

val imp_align_eq_0 = Q.store_thm("imp_align_eq_0",
  `w2n a < 2 ** p ⇒ (align p a= 0w)`,
  Cases_on`a` \\ fs[]
  \\ rw[alignmentTheory.align_w2n]
  \\ Cases_on`p = 0` \\ fs[]
  \\ `1 < 2 ** p` by fs[arithmeticTheory.ONE_LT_EXP]
  \\ `n DIV 2 ** p = 0` by fs[DIV_EQ_0]
  \\ fs[] );

val word_of_bytes_bytes_to_word = Q.store_thm("word_of_bytes_bytes_to_word",
  `∀be a bs k.
   LENGTH bs ≤ k ⇒
   (word_of_bytes be a bs = bytes_to_word k a bs 0w be)`,
  Induct_on`bs`
  >- (
    EVAL_TAC
    \\ Cases_on`k`
    \\ EVAL_TAC
    \\ rw[] )
  \\ rw[data_to_word_memoryProofTheory.word_of_bytes_def]
  \\ Cases_on`k` \\ fs[]
  \\ rw[data_to_word_memoryProofTheory.bytes_to_word_def]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ first_x_assum match_mp_tac
  \\ fs[]);

val bytes_in_mem_bytes_in_memory = Q.store_thm("bytes_in_mem_bytes_in_memory",
  `∀a bs m md k. bytes_in_mem a bs m md k ⇔ bytes_in_memory a bs m (md DIFF k)`,
  Induct_on`bs` \\ EVAL_TAC \\ rw[]
  \\ rw[EQ_IMP_THM]);

val read_bytearray_IMP_bytes_in_memory = Q.store_thm("read_bytearray_IMP_bytes_in_memory",
  `∀p n m ba m' md.
   (n = LENGTH ba) ∧ w2n p + n < dimword(:'a) ∧
   (∀k. (p <=+ k ∧ k <+ p + n2w n) ⇒ k ∈ md ∧ (m k = SOME (m' k))) ∧
   (read_bytearray (p:'a word) n m = SOME ba) ⇒
   bytes_in_memory p ba m' md`,
  Induct_on`ba` \\ rw[] >- EVAL_TAC
  \\ simp[asmSemTheory.bytes_in_memory_def]
  \\ fs[read_bytearray_def, CaseEq"option"]
  \\ first_assum(qspec_then`p`mp_tac)
  \\ impl_tac
  >- (
    simp[WORD_LOWER_EQ_REFL]
    \\ Cases_on`p`
    \\ simp[word_add_n2w, word_lo_n2w] \\ fs[] )
  \\ rw[]
  \\ first_x_assum irule
  \\ Cases_on`p` \\ fs[ADD1,word_add_n2w]
  \\ qexists_tac`m` \\ fs[]
  \\ Cases \\ strip_tac
  \\ first_x_assum irule
  \\ simp[WORD_LOWER_EQ_REFL, word_ls_n2w]
  \\ fs[word_lo_n2w, word_ls_n2w] \\ rfs[]);

(*
val align_eq_0_imp = Q.store_thm("align_eq_0_imp",
  `0 < p ⇒ ((align p a = 0w) ⇒ w2n a < 2 ** p)`,
  rw[alignmentTheory.align_w2n, dimword_def]
  \\ reverse(Cases_on`p ≤ dimindex(:'a)`)
  >- (
    qspec_then`a`assume_tac w2n_lt
    \\ fs[dimword_def]
    \\ irule LESS_LESS_EQ_TRANS
    \\ asm_exists_tac \\ fs[] )
  \\ fs[MOD_EQ_0_DIVISOR]
  \\ Cases_on`d` \\ fs[]
  >- (
    `1 < 2 ** p` by fs[ONE_LT_EXP]
    \\ fs[DIV_EQ_0] )
  \\ fs[MULT]
*)

val align_add_aligned_gen = Q.store_thm("align_add_aligned_gen",
  `∀a. aligned p a ⇒ (align p (a + b) = a + align p b)`,
  completeInduct_on`w2n b`
  \\ rw[]
  \\ Cases_on`w2n b < 2 ** p`
  >- (
    simp[alignmentTheory.align_add_aligned]
    \\ `align p b = 0w` by simp[imp_align_eq_0]
    \\ simp[] )
  \\ fs[NOT_LESS]
  \\ Cases_on`w2n b = 2 ** p`
  >- (
    `aligned p b` by(
      simp[alignmentTheory.aligned_def,alignmentTheory.align_w2n]
      \\ metis_tac[n2w_w2n] )
    \\ `aligned p (a + b)` by metis_tac[alignmentTheory.aligned_add_sub_cor]
    \\ fs[alignmentTheory.aligned_def])
  \\ fs[LESS_EQ_EXISTS]
  \\ qmatch_asmsub_rename_tac`w2n b = z + _`
  \\ first_x_assum(qspec_then`z`mp_tac)
  \\ impl_keep_tac >- fs[]
  \\ `z < dimword(:'a)` by metis_tac[w2n_lt, LESS_TRANS]
  \\ disch_then(qspec_then`n2w z`mp_tac)
  \\ impl_tac >- simp[]
  \\ strip_tac
  \\ first_assum(qspec_then`a + n2w (2 ** p)`mp_tac)
  \\ impl_tac >- fs[]
  \\ rewrite_tac[word_add_n2w, GSYM WORD_ADD_ASSOC]
  \\ Cases_on`b` \\ fs[GSYM word_add_n2w]
  \\ strip_tac
  \\ first_x_assum(qspec_then`n2w (2**p)`mp_tac)
  \\ impl_tac >- fs[stack_removeProofTheory.aligned_w2n]
  \\ simp[]);

val get_byte_word_of_bytes = Q.store_thm("get_byte_word_of_bytes",
  `good_dimindex(:'a) ⇒
   i < LENGTH ls ∧ LENGTH ls ≤ w2n (bytes_in_word:'a word) ⇒
  (get_byte (n2w i) (word_of_bytes be (0w:'a word) ls) be = EL i ls)`,
  strip_tac
  \\ `∃k. dimindex(:'a) DIV 8 = 2 ** k` by(
    fs[labPropsTheory.good_dimindex_def]
    \\ TRY(qexists_tac`2` \\ EVAL_TAC \\ NO_TAC)
    \\ TRY(qexists_tac`3` \\ EVAL_TAC \\ NO_TAC) )
  \\ strip_tac
  \\ Q.ISPECL_THEN[`be`,`0w`,`ls`,`2 ** k`]mp_tac word_of_bytes_bytes_to_word
  \\ impl_keep_tac >- (
    rfs[bytes_in_word_def, dimword_def]
    \\ fs[labPropsTheory.good_dimindex_def] \\ rfs[])
  \\ rw[]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_bytes_to_word]
  \\ rw[]);

val word_msb_align = Q.store_thm("word_msb_align",
  `p < dimindex(:'a) ⇒ (word_msb (align p w) = word_msb (w:'a word))`,
  rw[alignmentTheory.align_bitwise_and,word_msb]
  \\ rw[data_to_word_memoryProofTheory.word_bit_and]
  \\ rw[data_to_word_memoryProofTheory.word_bit_lsl]
  \\ rw[word_bit_test, MOD_EQ_0_DIVISOR, dimword_def]);

val get_byte_EL_words_of_bytes = Q.store_thm("get_byte_EL_words_of_bytes",
  `∀be ls.
   i < LENGTH ls ∧ w2n (bytes_in_word:'a word) * LENGTH ls ≤ dimword(:'a) ∧ good_dimindex(:'a) ⇒
   (get_byte (n2w i : α word)
      (EL (w2n (byte_align ((n2w i):α word)) DIV (w2n (bytes_in_word:α word)))
        (words_of_bytes be ls)) be = EL i ls)`,
  completeInduct_on`i`
  \\ Cases_on`ls`
  \\ rw[data_to_word_memoryProofTheory.words_of_bytes_def]
  \\ qmatch_goalsub_abbrev_tac`MAX 1 bw`
  \\ `0 < bw` by (
     fs[Abbr`bw`,labPropsTheory.good_dimindex_def]
     \\ EVAL_TAC \\ fs[dimword_def] )
  \\ `MAX 1 bw = bw` by rw[MAX_DEF] \\ fs[]
  \\ Cases_on`i < bw` \\ fs[]
  >- (
    `byte_align (n2w i) = 0w`
    by(
      simp[alignmentTheory.byte_align_def]
      \\ irule imp_align_eq_0
      \\ fs[labPropsTheory.good_dimindex_def,Abbr`bw`]
      \\ rfs[bytes_in_word_def,dimword_def] )
    \\ simp[ZERO_DIV]
    \\ DEP_REWRITE_TAC[UNDISCH get_byte_word_of_bytes]
    \\ fs[LENGTH_TAKE_EQ]
    \\ Cases_on`i` \\ fs[EL_TAKE] )
  \\ fs[NOT_LESS]
  \\ pop_assum (strip_assume_tac o SIMP_RULE std_ss [LESS_EQ_EXISTS])
  \\ `byte_align (n2w (bw + p)) = n2w bw + byte_align (n2w p)`
  by (
    simp[GSYM word_add_n2w]
    \\ simp[alignmentTheory.byte_align_def]
    \\ DEP_REWRITE_TAC[align_add_aligned_gen]
    \\ simp[Abbr`bw`]
    \\ CONV_TAC(REWR_CONV(GSYM alignmentTheory.byte_aligned_def))
    \\ (data_to_word_assignProofTheory.byte_aligned_bytes_in_word
        |> Q.GEN`w` |> Q.SPEC`1w` |> UNDISCH |> mp_tac)
    \\ simp[] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ conj_tac
  >- (
    simp[Abbr`bw`]
    \\ reverse conj_tac >- (
      fs[labPropsTheory.good_dimindex_def,
         bytes_in_word_def]
      \\ EVAL_TAC \\ fs[] \\ EVAL_TAC )
    \\ simp[alignmentTheory.byte_align_def]
    \\ DEP_REWRITE_TAC[word_msb_align]
    \\ conj_tac >- ( fs[labPropsTheory.good_dimindex_def])
    \\ simp[word_msb_n2w]
    \\ qmatch_assum_abbrev_tac`bw * r ≤ dimword _`
    \\ `r ≤ dimword (:'a) DIV bw` by fs[X_LE_DIV]
    \\ `p < dimword(:'a) DIV bw` by fs[]
    \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
    \\ fs[dimword_def, bytes_in_word_def]
    \\ fs[Abbr`bw`, labPropsTheory.good_dimindex_def]
    \\ rfs[] )
  \\ `bw < dimword(:'a)` by fs[Abbr`bw`, bytes_in_word_def]
  \\ simp[]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ simp[]
  \\ simp[EL_CONS,PRE_SUB1]
  \\ simp[GSYM word_add_n2w]
  \\ `n2w bw = byte_align (n2w bw)`
  by(
    fs[Abbr`bw`,bytes_in_word_def,alignmentTheory.byte_align_def]
    \\ fs[labPropsTheory.good_dimindex_def]
    \\ EVAL_TAC \\ fs[dimword_def] \\ EVAL_TAC )
  \\ pop_assum SUBST1_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ simp[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ first_x_assum(qspec_then`p`mp_tac)
  \\ simp[]
  \\ disch_then(qspecl_then[`be`,`DROP (bw-1)t`]mp_tac)
  \\ impl_tac >- fs[ADD1]
  \\ simp[EL_DROP]);

(*
val EL_words_of_bytes = Q.store_thm("EL_words_of_bytes",
  `8 ≤ dimindex(:'a) ⇒
   ∀be ls i.
   i < LENGTH ls ⇒
   (EL (i DIV (dimindex(:'a) DIV 8)) ((words_of_bytes be ls):'a word list) =
    word_of_bytes be 0w (TAKE (dimindex(:'a) DIV 8) (DROP i ls)))`
  strip_tac
  \\ recInduct data_to_word_memoryProofTheory.words_of_bytes_ind
  \\ rw[data_to_word_memoryProofTheory.words_of_bytes_def]
  \\ `w2n (bytes_in_word:'a word) = dimindex(:'a) DIV 8`
  by (
    rw[bytes_in_word_def, dimword_def, DIV_LT_X]
    \\ match_mp_tac LESS_LESS_EQ_TRANS
    \\ qexists_tac`2 ** dimindex(:'a)`
    \\ simp[X_LT_EXP_X] )
  \\ fs[]
  \\ `0 < dimindex(:'a)` by fs[]
  \\ `0 < dimindex(:'a) DIV 8` by fs[X_LT_DIV]
  \\ `MAX 1 (dimindex(:'a) DIV 8) = dimindex(:'a) DIV 8`
  by rw[MAX_DEF]
  \\ fs[]
  \\ Cases_on`i` \\ fs[ZERO_DIV]
  \\ simp[EL_CONS]
*)

(* -- *)


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
  hz = heap_size is the heap+stack size in mebibytes (including the unusable FFI bytes)
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

val hello_init_memory_words_def = zDefine`
  hello_init_memory_words r0 =
    REPLICATE (64 DIV 4) 0w ++
    [r0 + n2w heap_size
    ;r0 + n2w (heap_size + 4 * LENGTH data)
    ;r0 + n2w (heap_size + 4 * LENGTH data)
    ;r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset + LENGTH code)
    ;r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset + LENGTH code)] ++
    REPLICATE (heap_size DIV 4 - 5 - 64 DIV 4) 0w ++
    data ++
    REPLICATE 4 0w (* FFI code *) ++
    REPLICATE 4 0w (* ccache code *) ++
    REPLICATE 4 0w (* halt code *) ++
    words_of_bytes F code`;

val hello_init_memory_def = Define`
  hello_init_memory r0 (k:word32) =
     get_byte k (EL (w2n (byte_align k - r0) DIV 4) (hello_init_memory_words r0)) F`;

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
     (λk. Word (EL (w2n (k - r0) DIV 4) (hello_init_memory_words r0)))
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
    \\ conj_tac >- rw[hello_init_asm_state_def]
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
  \\ conj_asm1_tac >- (
    simp[targetSemTheory.code_loaded_def,
         hello_machine_config_def,
         hello_init_ag32_state_def,
         heap_size_def, memory_size_def, LENGTH_data,
         ag32_targetTheory.ag32_target_def]
    \\ match_mp_tac data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ simp[]
    \\ gen_tac \\ strip_tac
    \\ qpat_x_assum`_ < dimword _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ CONV_TAC(PATH_CONV"rlr" EVAL)
    \\ Cases_on`r0`
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, LENGTH_code, LENGTH_data]
    \\ strip_tac
    \\ CONV_TAC(PATH_CONV"lrr" EVAL)
    \\ rewrite_tac[hello_init_memory_def]
    \\ qmatch_goalsub_abbrev_tac`i + k`
    \\ `byte_aligned ((n2w k):word32)` by(
      simp[Abbr`k`, GSYM word_add_n2w, alignmentTheory.byte_aligned_def]
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
          |> irule)
      \\ fs[]
      \\ EVAL_TAC )
    \\ `n2w k = byte_align ((n2w k):word32)`
    by (
      fs[alignmentTheory.byte_aligned_def,
         alignmentTheory.byte_align_def,
         alignmentTheory.aligned_def] )
    \\ once_rewrite_tac[GSYM word_add_n2w]
    \\ first_assum(CONV_TAC o PATH_CONV"lrllrr" o REWR_CONV)
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ conj_tac >- EVAL_TAC
    \\ `byte_align (n2w i + n2w k) : word32 = byte_align (n2w i) + n2w k`
    by (
      once_rewrite_tac[WORD_ADD_COMM]
      \\ rewrite_tac[alignmentTheory.byte_align_def]
      \\ irule align_add_aligned_gen
      \\ fs[alignmentTheory.byte_aligned_def] )
    \\ once_asm_rewrite_tac[]
    \\ qunabbrev_tac`k`
    \\ rewrite_tac[WORD_ADD_SUB_SYM]
    \\ rewrite_tac[GSYM word_add_n2w]
    \\ rewrite_tac[WORD_ADD_ASSOC]
    \\ rewrite_tac[WORD_SUB_ADD]
    \\ DEP_REWRITE_TAC[w2n_add]
    \\ conj_tac
    >- (
      reverse conj_tac >- EVAL_TAC
      \\ simp[alignmentTheory.byte_align_def]
      \\ simp[alignmentTheory.align_w2n]
      \\ simp[multiwordTheory.d_word_msb]
      \\ DEP_REWRITE_TAC[LESS_MOD]
      \\ fs[NOT_LESS_EQUAL]
      \\ conj_tac
      \\ irule IMP_MULT_DIV_LESS
      \\ fs[] )
    \\ simp[ADD_DIV_RWT]
    \\ simp[hello_init_memory_words_def,EL_APPEND_EQN]
    \\ simp[LENGTH_data,heap_size_def]
    \\ `4 = w2n (bytes_in_word:32 word)` by EVAL_TAC
    \\ pop_assum SUBST1_TAC
    \\ irule get_byte_EL_words_of_bytes
    \\ simp[LENGTH_code, bytes_in_word_def]
    \\ EVAL_TAC)
  \\ conj_tac >- (
    fs[targetSemTheory.code_loaded_def]
    \\ simp[hello_init_asm_state_def, hello_init_ag32_state_def]
    \\ fs[hello_machine_config_def]
    \\ simp[bytes_in_mem_bytes_in_memory]
    \\ simp[hello_init_regs_def, heap_size_def, LENGTH_data,
            LENGTH_code, memory_size_def, lab_to_targetTheory.ffi_offset_def]
    \\ qmatch_goalsub_abbrev_tac`a ∪ b DIFF c`
    \\ `c = a`
    by (
      simp[Abbr`c`,Abbr`a`, EXTENSION]
      \\ Cases_on`r0`
      \\ Cases
      \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def]  )
    \\ fs[Abbr`c`]
    \\ simp[DIFF_SAME_UNION]
    \\ pop_assum kall_tac
    \\ fs[ag32_targetTheory.ag32_target_def, LENGTH_data, heap_size_def, memory_size_def,
          lab_to_targetTheory.ffi_offset_def, hello_init_ag32_state_def]
    \\ irule read_bytearray_IMP_bytes_in_memory
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[LENGTH_code,Abbr`a`,Abbr`b`]
    \\ Cases_on`r0` \\  fs[word_add_n2w]
    \\ Cases \\ fs[word_lo_n2w, word_ls_n2w])
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
    rw[hello_init_asm_state_def, hello_init_memory_def,
       EVAL``(hello_machine_config r0).target.config``,
       EVAL``(hello_init_ag32_state r0).MEM``] )
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

val goal = compile_correct_applied |> concl |> dest_imp |> #1
           |> curry mk_imp (#1(dest_imp(concl hello_good_init_state)))
(*
set_goal([],goal)
*)
val lemma = prove(goal,
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
    rw[EVAL``(hello_init_asm_state r0).regs``, LENGTH_data,
       hello_init_regs_def, bytes_in_word_def]
    \\ simp[hello_init_memory_words_def, EL_APPEND_EQN,
            heap_size_def, EL_REPLICATE, LENGTH_data] )
  \\ conj_tac
  >- (
    rw[EVAL``(hello_init_asm_state r0).regs``, LENGTH_data,
       hello_init_regs_def, bytes_in_word_def]
    \\ simp[hello_init_memory_words_def, EL_APPEND_EQN,
            heap_size_def, EL_REPLICATE, LENGTH_data] )
  \\ conj_tac
  >- (
    rw[EVAL``(hello_init_asm_state r0).regs``, LENGTH_data,
       hello_init_regs_def, bytes_in_word_def]
    \\ simp[hello_init_memory_words_def, EL_APPEND_EQN,
            heap_size_def, EL_REPLICATE, LENGTH_data, LENGTH_code]
    \\ EVAL_TAC \\ simp[LENGTH_data] )
  \\ conj_tac
  >- (
    rw[EVAL``(hello_init_asm_state r0).regs``, LENGTH_data,
       hello_init_regs_def, bytes_in_word_def]
    \\ simp[hello_init_memory_words_def, EL_APPEND_EQN,
            heap_size_def, EL_REPLICATE, LENGTH_data, LENGTH_code]
    \\ EVAL_TAC \\ simp[LENGTH_data] )
  \\ conj_tac
  >- cheat (* data is installed *)
  \\ EVAL_TAC
  \\ rewrite_tac[hello_ag32CompileTheory.config_def]
  \\ EVAL_TAC);

val hello_machine_sem =
  compile_correct_applied
  |> C MATCH_MP (UNDISCH lemma)
  |> DISCH_ALL
  |> curry save_thm "hello_machine_sem";

val _ = export_theory();
