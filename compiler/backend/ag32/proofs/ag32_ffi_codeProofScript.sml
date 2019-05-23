(*
  Verify the deep embeddings of the ag32 implementation of the CakeML
  basis FFI primitives.
*)
open preamble ag32_memoryTheory ag32_decompilerLib
local open blastLib ag32_targetProofTheory in end

val _ = new_theory"ag32_ffi_codeProof";

(* TODO: move *)

Theorem byte_aligned_imp:
   byte_aligned (x:word32) ⇒
   (((((31 >< 2) x):word30) @@ (0w:word2)) = x)
Proof
  rw[alignmentTheory.byte_aligned_def, alignmentTheory.aligned_def, alignmentTheory.align_def]
  \\ blastLib.FULL_BBLAST_TAC
QED

(* -- *)

val first_tac =
   rw[ag32_ffi_write_check_lengths_def,
      ag32_ffi_write_load_noff_def,
      ag32_ffi_write_check_conf_def,
      ag32_ffi_read_check_conf_def,
      ag32_ffi_read_load_lengths_def,
      ag32_ffi_read_check_length_def,
      ag32_ffi_read_set_id_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ imp_res_tac byte_aligned_imp \\ rfs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_check_lengths_code_def,
          ag32_ffi_write_load_noff_code_def,
          ag32_ffi_write_check_conf_code_def,
          ag32_ffi_read_check_conf_code_def,
          ag32_ffi_read_load_lengths_code_def,
          ag32_ffi_read_check_length_code_def,
          ag32_ffi_read_set_id_code_def,
          ag32Theory.Run_def];

fun next_tac n =
  let
    val sn = mk_var("s"^(Int.toString n), ``:ag32_state``)
  in
    rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
    \\ qmatch_goalsub_abbrev_tac`Next ^sn`
    \\ rw[ag32Theory.Next_def]
    \\ qmatch_goalsub_abbrev_tac`pc + 2w`
    \\ simp[GSYM get_mem_word_def]
    \\ `^sn.PC = s.PC + n2w(4 * ^(numSyntax.term_of_int n))`
    by ( simp[Abbr`^sn`,
              dfn'Normal_PC,
              dfn'LoadMEM_PC,
              dfn'LoadMEMByte_PC,
              dfn'Shift_PC,
              dfn'LoadConstant_PC] )
    \\ `byte_aligned ^sn.PC`
    by (
      simp[]
      \\ irule byte_aligned_add \\ simp[]
      \\ EVAL_TAC )
    \\ drule byte_aligned_imp
    \\ simp[]
    \\ disch_then kall_tac
    \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
    \\ last_assum(qspec_then`^(numSyntax.term_of_int n)`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ simp_tac(srw_ss())[ag32_ffi_write_check_conf_code_def,
                          ag32_ffi_write_load_noff_code_def,
                          ag32_ffi_write_check_lengths_code_def,
                          ag32_ffi_write_write_header_code_def,
                          ag32_ffi_write_num_written_code_def,
                          ag32_ffi_copy_code_def,
                          ag32_ffi_return_code_def,
                          ag32_ffi_read_check_conf_code_def,
                          ag32_ffi_read_load_lengths_code_def,
                          ag32_ffi_read_check_length_code_def,
                          ag32_ffi_read_set_id_code_def]
    \\ `^sn.MEM = s.MEM`
    by simp[Abbr`^sn`,
            dfn'Normal_MEM,
            dfn'LoadMEM_MEM,
            dfn'LoadMEMByte_MEM,
            dfn'Shift_MEM,
            dfn'LoadConstant_MEM]
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_targetProofTheory.Decode_Encode]
    \\ simp[ag32Theory.Run_def]
  end

Theorem ag32_ffi_return_code_thm:
   (∀k. k < LENGTH ag32_ffi_return_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_return_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_return s)
Proof
  rw[ag32_ffi_return_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ imp_res_tac byte_aligned_imp \\ rfs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_return_code_def, ag32Theory.Run_def]
  \\ EVERY (List.tabulate(8, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s9`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s9.PC = s.PC + n2w(4 * 9)`
  by ( simp[Abbr`s9`, ag32Theory.dfn'Interrupt_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s9.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_return_code_def]
  \\ `s9.MEM = s.MEM` by simp[Abbr`s9`,ag32Theory.dfn'Interrupt_def,ag32Theory.incPC_def]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM]
QED

Theorem ag32_ffi_copy_code_thm:
   ∀s.
   (∀k. k < LENGTH ag32_ffi_copy_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_copy_code)))
   ∧ byte_aligned s.PC
   ∧ w2n s.PC + 4 * LENGTH ag32_ffi_copy_code < dimword (:32)
   ∧ w2n (s.R 5w) + w2n (s.R 1w) < dimword(:32)
   ∧ DISJOINT { s.R 5w + n2w k | k | k < w2n (s.R 1w) }
              { s.PC + n2w k | k | k DIV 4 < LENGTH ag32_ffi_copy_code }
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_copy s)
Proof
  Induct_on`w2n(s.R 1w)` \\ rw[]
  >- (
    simp[Once ag32_ffi_copy_def]
    \\ Cases_on`s.R 1w` \\ fs[] \\ rw[]
    \\ qexists_tac`1` \\ rw[]
    \\ rw[ag32Theory.Next_def]
    \\ qmatch_goalsub_abbrev_tac`pc + 2w`
    \\ simp[GSYM get_mem_word_def]
    \\ last_assum(qspec_then`0`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ simp_tac(srw_ss())[]
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[byte_aligned_imp]
    \\ conj_tac >- rw[]
    \\ strip_tac \\ simp[Abbr`pc`]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_copy_code_def]
    \\ simp[ag32_targetProofTheory.Decode_Encode]
    \\ simp[ag32Theory.Run_def] )
  \\ simp[Once ag32_ffi_copy_def]
  \\ Cases_on`s.R 1w` \\ fs[]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s1`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s1.PC = s.PC + n2w (4 * 1)`
  by ( simp[Abbr`s1`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,
            ag32Theory.ALU_def,ag32Theory.incPC_def] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s1.MEM = s.MEM` by simp[Abbr`s1`, dfn'JumpIfZero_MEM]
  \\ first_assum(qspec_then`1`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ next_tac 2
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s3`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s3.PC = s.PC + n2w (4 * 3)`
  by ( simp[Abbr`s3`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s2.R 5w = s.R 5w`
  by (
    simp[Abbr`s2`]
    \\ simp[ag32Theory.incPC_def, ag32Theory.dfn'LoadMEMByte_def,
            ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ simp[Abbr`s1`]
      \\ simp[ag32Theory.dfn'JumpIfZero_def, ag32Theory.incPC_def,
              ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
              ag32Theory.ri2word_def, ag32Theory.ALU_def] )
  \\ `∀k. k < LENGTH ag32_ffi_copy_code ⇒
      (get_mem_word s3.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_copy_code))`
  by (
    qx_gen_tac`k`
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[Abbr`s3`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
    \\ fs[EVAL``LENGTH ag32_ffi_copy_code``]
    \\ Cases_on`s.R 5w` \\ Cases_on`s.PC` \\ fs[word_add_n2w]
    \\ IF_CASES_TAC \\ fs[IN_DISJOINT, DISJ_EQ_IMP, PULL_EXISTS]
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[DIV_LT_X]
         \\ disch_then(qspec_then`4 * k + 3`mp_tac) \\ simp[])
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[DIV_LT_X]
         \\ disch_then(qspec_then`4 * k + 2`mp_tac) \\ simp[])
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[DIV_LT_X]
         \\ disch_then(qspec_then`4 * k + 1`mp_tac) \\ simp[])
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[DIV_LT_X]
         \\ disch_then(qspec_then`4 * k + 0`mp_tac) \\ simp[]))
  \\ first_assum(qspec_then`3`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_copy_code_def]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s4`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s4.PC = s.PC + n2w (4 * 4)`
  by ( simp[Abbr`s4`, dfn'Normal_PC])
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s4.MEM = s3.MEM` by simp[Abbr`s4`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`4`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s5`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s5.PC = s.PC + n2w (4 * 5)`
  by ( simp[Abbr`s5`, dfn'Normal_PC])
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s5.MEM = s3.MEM` by simp[Abbr`s5`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`5`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s6`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s6.PC = s.PC + n2w (4 * 6)`
  by ( simp[Abbr`s6`, dfn'Normal_PC])
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s6.MEM = s3.MEM` by simp[Abbr`s6`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ qmatch_goalsub_abbrev_tac`_ = _ s7`
  \\ last_x_assum(qspec_then`s7`mp_tac)
  \\ impl_keep_tac
  >-(
    simp[Abbr`s7`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,ag32Theory.ALU_def]
    \\ simp[Abbr`s6`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s4`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s3`, ag32Theory.dfn'StoreMEMByte_def,ag32Theory.incPC_def]
    \\ simp[Abbr`s2`, ag32Theory.dfn'LoadMEMByte_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s1`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
            ag32Theory.ALU_def]
    \\ simp[ADD1,GSYM word_add_n2w])
  \\ `s7.MEM = s3.MEM` by simp[Abbr`s7`, dfn'JumpIfZero_MEM]
  \\ `s7.PC = s.PC`
  by ( simp[Abbr`s7`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,ag32Theory.ALU_def])
  \\ `s7.R 5w = s.R 5w + 1w`
  by(
    simp[Abbr`s7`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,ag32Theory.ALU_def]
    \\ simp[Abbr`s6`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s4`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s3`, ag32Theory.dfn'StoreMEMByte_def,ag32Theory.incPC_def])
  \\ disch_then match_mp_tac
  \\ simp[]
  \\ Cases_on`s.R 5w` \\ Cases_on`s7.R 1w` \\ fs[word_add_n2w]
  \\ fs[ADD1,IN_DISJOINT,GSYM word_add_n2w,DISJ_EQ_IMP,PULL_EXISTS]
  \\ rw[]
  \\ `k + 1 <n' + 1`by simp[]
  \\ first_x_assum drule
  \\ fs[word_add_n2w]
QED


fun simp0 ths g = asm_simp_tac (srw_ss() ++ ARITH_ss) ths g

fun rnwc_next n =
    let
      val ns = Int.toString n
      val ss = "s" ^ ns
    in
      ONCE_REWRITE_TAC [LET_THM] >>
      qmatch_abbrev_tac [QUOTE ("?k. FUNPOW Next k "^ss ^ " = _ " ^ ss)] >>
      BETA_TAC >>
      pop_assum mp_tac >>
      CONV_TAC (PATH_CONV "lrrr" (SIMP_CONV (srw_ss()) [
        ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def,
        ag32Theory.ri2word_def, ag32Theory.incPC_def, LET_THM,
        ag32Theory.dfn'JumpIfZero_def, ag32Theory.dfn'StoreMEMByte_def,
        ag32Theory.dfn'Shift_def, ag32Theory.dfn'StoreMEM_def,
        ag32Theory.dfn'LoadMEM_def, ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.dfn'JumpIfNotZero_def,
        ag32Theory.dfn'LoadConstant_def])) >> strip_tac
    end

val ltNumeral = Q.prove(
  ‘(x < NUMERAL (BIT2 n) ⇔ x < NUMERAL (BIT1 n) \/ x = NUMERAL (BIT1 n)) /\
   (x < NUMERAL (BIT1 n) ⇔
      x < PRE (NUMERAL (BIT1 n)) \/ x = PRE (NUMERAL (BIT1 n)))’,
  REWRITE_TAC[BIT1, BIT2, NUMERAL_DEF] >> simp[])

fun instn0 th i =
    first_assum (qspec_then [QUOTE (Int.toString i)]
                            (assume_tac o SIMP_RULE (srw_ss()) [th])) >>
    Q.REFINE_EXISTS_TAC ‘SUC k’ >>
    simp0[FUNPOW, ag32Theory.Next_def, GSYM get_mem_word_def] >>
    (if i > 0 then
       [QUOTE ("byte_aligned (s.PC + " ^ Int.toString (i * 4) ^ "w)")]
         by (irule byte_aligned_add >> simp[] >> EVAL_TAC) >>
       drule_then assume_tac byte_aligned_imp >> simp0[]
     else ALL_TAC) >>
    simp0[SimpLHS, LET_THM] >>
    (if i > 0 then ntac 2 (pop_assum kall_tac) else ALL_TAC)

val instn = instn0 ag32_ffi_read_num_written_code_def

val sub_common = Q.prove(
  ‘u <= v ⇒ ((x:word32) + (n2w u) = y + (n2w v) ⇔ x = y + n2w (v - u))’,
  strip_tac >> drule LESS_EQ_ADD_EXISTS >> rw[] >> simp[] >>
  REWRITE_TAC [GSYM word_add_n2w] >>
  REWRITE_TAC [WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL]);

fun glAbbr i =
  TRY (qpat_x_assum [QUOTE ("Abbrev (s" ^ Int.toString i ^ " = _)")]
            (fn th => REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])>>
       simp[combinTheory.UPDATE_def, sub_common]);

fun gmw0 tac i = let
  val is = Int.toString i
  val off = "(s.PC + " ^ Int.toString (4 * i) ^ "w)"
  val sg : term quotation  =
      [QUOTE ("get_mem_word s"^is^".MEM " ^ off ^
              " = get_mem_word s.MEM "^off)]
in
  sg
    by (EVERY (List.tabulate(i, (fn j => glAbbr(i - j)))) >>
        fs[get_mem_word_def] >> tac i) >>
  pop_assum (fn rwt0 =>
    mp_tac rwt0 >> simp0[] >>
    pop_assum (fn _ =>
      disch_then (fn rwt =>
         simp0[ag32_targetProofTheory.Decode_Encode, ag32Theory.Run_def, rwt])))
end

fun insthyp sel n f =
    sel (fn th =>
            map_every
              (fn q => qspec_then q mp_tac th)
              (List.tabulate (n, fn j => [QUOTE (Int.toString (f j))]))) >>
    simp_tac(srw_ss()) [sub_common] >> simp0[]

fun gmwtac i =
    insthyp last_x_assum 7 (fn j => 4*i + j - 3) >>
    (if i >= 14 then insthyp last_x_assum 7 (fn j => 4*i + j - 3)
     else ALL_TAC)
val gmw = gmw0 gmwtac

Theorem v2w_EQ0:
   v2w [b] = (0w : word32) ⇔ ~b
Proof
  Cases_on ‘b’ >> simp[]
QED

fun r3_unchanged i =
    let
      val ss = "s" ^ Int.toString i
      val ps = "s" ^ Int.toString (i - 1)
    in
      [QUOTE (ss ^ ".R 3w = " ^ ps ^ ".R 3w")]
        by simp[Abbr[QUOTE ss], combinTheory.UPDATE_def]
    end

fun print_tac msg g = (print (msg ^ "\n"); ALL_TAC g)
fun spc i =
    let
      val ss = "s" ^ Int.toString i
    in
      [QUOTE (ss ^ ".PC = s.PC + " ^ Int.toString (i * 4) ^ "w")]
         by simp[Abbr[QUOTE ss]]
    end
fun combined0 instn gmw i =
    let
      val is = Int.toString i
      val ss = "s" ^ is
    in
      print_tac ("Combined instruction #"^is) >>
      rnwc_next i >> spc i >>
      instn i >> gmw i
    end;
val combined = combined0 instn gmw

val _ = temp_overload_on ("align4",
  “λw:word32. (((31 >< 2) w) : 30 word @@ (0w : 2 word)) : word32”);

Theorem ag32_ffi_read_num_written_code_thm:
   s.R 3w ∉
     { s.PC + n2w k | k | k DIV 4 < LENGTH ag32_ffi_read_num_written_code } ∧
   align4 (w2w (n2w stdin_offset : 23 word)) ∉
        { s.PC + n2w k | k | k DIV 4 < LENGTH ag32_ffi_read_num_written_code } ∧
   (∀k. k < LENGTH ag32_ffi_read_num_written_code ⇒
          get_mem_word s.MEM (s.PC + n2w (4 * k)) =
          Encode (EL k ag32_ffi_read_num_written_code)) ∧
   byte_aligned s.PC
     ⇒
   ∃k. FUNPOW Next k s = ag32_ffi_read_num_written s
Proof
  strip_tac >>
  assume_tac (EVAL “LENGTH ag32_ffi_read_num_written_code”) >> fs[] >>
  instn 0 >>
  drule_then assume_tac byte_aligned_imp >>
  simp[ag32_targetProofTheory.Decode_Encode, ag32Theory.Run_def] >>
  ntac 2 (pop_assum kall_tac) >>
  simp0[ag32_ffi_read_num_written_def] >>

  combined 1 >> combined 2 >>
  ‘s2.R 3w = s.R 3w + 1w’
    by (glAbbr 2 >> simp[combinTheory.UPDATE_def] >> glAbbr 1) >>
  combined 3 >>

  rnwc_next 4 >> RULE_ASSUM_TAC (REWRITE_RULE [v2w_EQ0]) >>
  ‘s4.PC = s.PC + 16w ⇔ s3.R 8w < s3.R 1w’ by (simp[Abbr‘s4’] >> rw[]) >>
  simp0[] >> Cases_on ‘s3.R 8w < s3.R 1w’ >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  simp0[]
  >- (
   r3_unchanged 4 >> instn 4 >> gmw 4 >> combined 5 >>

   rnwc_next 6 >> RULE_ASSUM_TAC (REWRITE_RULE [v2w_EQ0]) >>
   ‘s6.PC = s.PC + 24w ⇔ s5.R 7w < s5.R 1w’ by (simp[Abbr‘s6’] >> rw[]) >>
   simp0[] >> Cases_on ‘s5.R 7w < s5.R 1w’ >>
   pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
   simp0[]
   >- (
    r3_unchanged 6 >> instn 6 >> gmw 6 >>
    EVERY (List.tabulate(11, fn i => combined (i + 7))) >>
    qexists_tac `0` >> simp[]
   ) >>
   r3_unchanged 6 >> rename [‘s7.PC ≠ s.PC + 24w’] >>
   ‘s7.PC = s.PC + 28w’ by simp[Abbr‘s7’] >> simp0[Once LET_THM] >>
   instn 7 >> gmw 7 >>
   EVERY (List.tabulate(10, (fn i => combined (i + 8)))) >>
   qexists_tac `0` >> simp[]
  ) >>
  r3_unchanged 4 >> rename [‘s5.PC ≠ s.PC + 16w’] >>
  ‘s5.PC = s.PC + 20w’ by simp[Abbr`s5`] >> instn 5 >> gmw 5 >>
  simp0[Once LET_THM] >>

  rnwc_next 6 >> RULE_ASSUM_TAC (REWRITE_RULE [v2w_EQ0]) >>
  ‘s6.PC = s.PC + 24w ⇔ s5.R 7w < s5.R 1w’ by (simp[Abbr‘s6’] >> rw[]) >>
  simp0[] >> Cases_on ‘s5.R 7w < s5.R 1w’ >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  simp0[]
  >- (
    r3_unchanged 6 >> instn 6 >> gmw 6 >>
    EVERY (List.tabulate(11, fn i => combined (i + 7))) >>
    qexists_tac `0` >> simp[]
  ) >>

  r3_unchanged 6 >> rename [‘s7.PC ≠ s.PC + 24w’] >>
  ‘s7.PC = s.PC + 28w’ by simp[Abbr‘s7’] >> simp0[Once LET_THM] >>
  instn 7 >> gmw 7 >>
  EVERY (List.tabulate(10, fn i => combined (i + 8))) >>
  qexists_tac `0` >> simp[]
QED

Theorem ag32_ffi_write_set_id_code_thm:
   (∀k. k < LENGTH ag32_ffi_write_set_id_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_set_id_code))) ∧
   byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_set_id s)
Proof
  rw[ag32_ffi_write_set_id_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`s1.PC`
  \\ `(s.PC + 4w = s1.PC) ∧ (s1.MEM = s.MEM)`
  by ( simp[Abbr`s1`, ag32Theory.dfn'Jump_def, ag32Theory.ALU_def,ag32Theory.ri2word_def] )
  \\ `byte_aligned s1.PC`
  by (
    first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ irule byte_aligned_add
    \\ simp[] \\ EVAL_TAC )
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`1`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`s2.PC`
  \\ `(s.PC + 8w = s2.PC) ∧ (s2.MEM = s.MEM)`
  by ( simp[Abbr`s2`, ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def]
       \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM) \\ simp[] )
  \\ `byte_aligned s2.PC`
  by (
    first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ irule byte_aligned_add
    \\ simp[] \\ EVAL_TAC )
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`2`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`s3.PC`
  \\ `(s.PC + n2w(3*4) = s3.PC) ∧ (s3.MEM = s.MEM)`
  by ( simp[Abbr`s3`, dfn'Normal_PC, dfn'Normal_MEM]
       \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM) \\ simp[] )
  \\ `byte_aligned s3.PC`
  by (
    first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ irule byte_aligned_add
    \\ simp[] \\ EVAL_TAC )
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`3`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ fs[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`s4.PC`
  \\ `(s.PC + n2w(4*4) = s4.PC) ∧ (s4.MEM = s.MEM)`
  by ( simp[Abbr`s4`, dfn'Normal_PC, dfn'Normal_MEM]
       \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM) \\ simp[] )
  \\ `byte_aligned s4.PC`
  by (
    first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ irule byte_aligned_add
    \\ simp[] \\ EVAL_TAC )
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`4`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ fs[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM]
QED

Theorem ag32_ffi_write_check_conf_code_thm:
   (∀k. k < LENGTH ag32_ffi_write_check_conf_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_check_conf_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_check_conf s)
Proof
  first_tac
  \\ EVERY (List.tabulate(34, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]
QED

Theorem ag32_ffi_write_load_noff_code_thm:
   (∀k. k < LENGTH ag32_ffi_write_load_noff_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_load_noff_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_load_noff s)
Proof
  first_tac
  \\ EVERY (List.tabulate(11, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]
QED

Theorem ag32_ffi_write_check_lengths_code_thm:
   (∀k. k < LENGTH ag32_ffi_write_check_lengths_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_check_lengths_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_check_lengths s)
Proof
  first_tac
  \\ EVERY (List.tabulate(9, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]
QED

Theorem ag32_ffi_write_write_header_code_thm:
   (∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_write_header_code)))
   ∧ (s.PC =
       n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint
            + 4 * (LENGTH ag32_ffi_write_set_id_code)
            + 4 * (LENGTH ag32_ffi_write_check_conf_code)
            + 4 * (LENGTH ag32_ffi_write_load_noff_code)
            + 4 * (LENGTH ag32_ffi_write_check_lengths_code)))
   ∧ (s.R 5w = n2w output_offset)
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_write_header s)
Proof
  rw[ag32_ffi_write_write_header_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_asm1_tac
  >- ( simp[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[] \\ rveq
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_write_header_code_def, ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s1`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s1.PC = s.PC + n2w(4 * 1)`
  by ( simp[Abbr`s1`, ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s1.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ `s1.R 5w = n2w (output_offset)`
  by ( simp[Abbr`s1`, ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s1.MEM (s.PC + n2w (4 * k)) =
     Encode (EL k ag32_ffi_write_write_header_code))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ qpat_x_assum`s1.R _  = _`mp_tac
    \\ simp[Abbr`s1`]
    \\ simp[ag32Theory.dfn'StoreMEM_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def]
    \\ DEP_REWRITE_TAC[byte_aligned_imp]
    \\ conj_tac >- ( EVAL_TAC )
    \\ simp[APPLY_UPDATE_THM]
    \\ qpat_x_assum`k < _` mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ ntac 2 strip_tac
    \\ simp[EVAL``output_offset``]
    \\ fs[word_add_n2w]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`1`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s2`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s2.PC = s.PC + n2w(4 * 2)`
  by ( simp[Abbr`s2`, dfn'Normal_PC] )
  \\ `byte_aligned s2.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`2`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s2.MEM = s1.MEM` by simp[Abbr`s2`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`2`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s3`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s3.PC = s.PC + n2w(4 * 3)`
  by ( simp[Abbr`s3`, dfn'Shift_PC] )
  \\ `byte_aligned s3.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`3`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s3.MEM = s1.MEM` by simp[Abbr`s3`, dfn'Shift_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`3`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s4`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s4.PC = s.PC + n2w(4 * 4)`
  by ( simp[Abbr`s4`, ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s4.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ `s3.R 5w = n2w (output_offset + 4)`
  by (
    simp[Abbr`s3`]
    \\ simp[ag32Theory.dfn'Shift_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.shift_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s2`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[GSYM word_add_n2w])
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s4.MEM (s.PC + n2w (4 * k)) =
     Encode (EL k ag32_ffi_write_write_header_code))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s4`]
    \\ simp[ag32Theory.dfn'StoreMEM_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def]
    \\ DEP_REWRITE_TAC[byte_aligned_imp]
    \\ conj_tac >- ( EVAL_TAC )
    \\ simp[APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ fs[word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ simp[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w])
  \\ first_assum(qspec_then`4`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s5`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s5.PC = s.PC + n2w(4 * 5)`
  by ( simp[Abbr`s5`, dfn'Normal_PC] )
  \\ `byte_aligned s5.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`5`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s5.MEM = s4.MEM` by simp[Abbr`s5`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s6`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s6.PC = s.PC + n2w(4 * 6)`
  by ( simp[Abbr`s6`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s6.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ `s5.R 5w = n2w (output_offset + 8)`
  by (
    simp[Abbr`s5`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s4`]
    \\ simp[ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
    \\ simp[GSYM word_add_n2w] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s6.MEM (s.PC + n2w (4 * k)) =
     Encode (EL k ag32_ffi_write_write_header_code))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s6`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def, APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ fs[word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s7`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s7.PC = s.PC + n2w(4 * 7)`
  by ( simp[Abbr`s7`, dfn'Normal_PC] )
  \\ `byte_aligned s7.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`7`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s7.MEM = s6.MEM` by simp[Abbr`s7`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s8`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s8.PC = s.PC + n2w(4 * 8)`
  by ( simp[Abbr`s8`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s8.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ `s7.R 5w = n2w (output_offset + 9)`
  by (
    simp[Abbr`s7`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s6`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
    \\ simp[GSYM word_add_n2w] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s8.MEM (s.PC + n2w (4 * k)) =
     Encode (EL k ag32_ffi_write_write_header_code))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s8`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def, APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ fs[word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`8`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s9`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s9.PC = s.PC + n2w(4 * 9)`
  by ( simp[Abbr`s9`, dfn'Normal_PC] )
  \\ `byte_aligned s9.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ `s9.MEM = s8.MEM` by simp[Abbr`s9`, dfn'Normal_MEM]
  \\ simp[]
  \\ first_assum(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s10`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s10.PC = s.PC + n2w(4 * 10)`
  by ( simp[Abbr`s10`, dfn'Shift_PC])
  \\ `byte_aligned s10.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`10`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s10.MEM = s8.MEM` by simp[Abbr`s10`, dfn'Shift_MEM]
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s11`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s11.PC = s.PC + n2w(4 * 11)`
  by ( simp[Abbr`s11`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s11.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ `s10.R 5w = n2w (output_offset + 10)`
  by (
    simp[Abbr`s10`]
    \\ simp[ag32Theory.dfn'Shift_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.shift_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s9`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s8`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[GSYM word_add_n2w] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s11.MEM (s.PC + n2w (4 * k)) =
     Encode (EL k ag32_ffi_write_write_header_code))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s11`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def, APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ fs[word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`11`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s12`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s12.PC = s.PC + n2w(4 * 12)`
  by ( simp[Abbr`s12`, dfn'Normal_PC] )
  \\ `byte_aligned s12.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`12`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s12.MEM = s11.MEM` by simp[Abbr`s12`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s13`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s13.PC = s.PC + n2w(4 * 13)`
  by ( simp[Abbr`s13`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s13.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ `s12.R 5w = n2w (output_offset + 11)`
  by (
    simp[Abbr`s12`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s11`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[GSYM word_add_n2w] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s13.MEM (s.PC + n2w (4 * k)) =
     Encode (EL k ag32_ffi_write_write_header_code))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s13`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def, APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ fs[word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`13`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32_ffi_write_write_header_code_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s14`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s14.PC = s.PC + n2w(4 * 14)`
  by ( simp[Abbr`s14`, dfn'Normal_PC] )
  \\ `byte_aligned s14.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ `s14.MEM = s13.MEM` by simp[Abbr`s14`, dfn'Normal_MEM]
  \\ simp[]
  \\ first_assum(qspec_then`14`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM]
QED

Theorem ag32_ffi_write_num_written_code_thm:
   (∀k. k < LENGTH ag32_ffi_write_num_written_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_num_written_code)))
   ∧ byte_aligned s.PC
   ∧ w2n s.PC + 4 * LENGTH ag32_ffi_write_num_written_code < dimword(:32)
   ∧ (∀k. k DIV 4 < LENGTH ag32_ffi_write_num_written_code ⇒ s.R 3w + 1w ≠ s.PC + n2w k)
   ∧ (∀k. k DIV 4 < LENGTH ag32_ffi_write_num_written_code ⇒ s.R 3w + 2w ≠ s.PC + n2w k)
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_num_written s)
Proof
  strip_tac
  \\ simp[ag32_ffi_write_num_written_def]
  \\ qmatch_goalsub_abbrev_tac`COND (t1.PC = t0.PC + 4w)`
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ last_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac >- rw[]
  \\ strip_tac \\ simp[Abbr`pc`]
  \\ disch_then kall_tac
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ qmatch_goalsub_abbrev_tac`dfn'Shift _ cs`
  \\ next_tac 1
  \\ simp[Abbr`t0`]
  \\ next_tac 2
  \\ `cs.PC = s.PC + n2w (4 * 4)`
  by (
    simp[Abbr`cs`]
    \\ rw[dfn'Normal_PC]
    \\ simp[Abbr`t1`]
    \\ fs[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def, ag32Theory.incPC_def, ag32Theory.ALU_def]
    \\ rw[] \\ fs[] \\ rfs[] )
  \\ qho_match_abbrev_tac`P t1`
  \\ `P cs` suffices_by (
    simp[Abbr`P`]
    \\ Cases_on`cs = t1` \\ simp[]
    \\ simp[Abbr`cs`]
    \\ CASE_TAC \\ fs[]
    \\ rw[]
    \\ qexists_tac`SUC m`
    \\ simp[FUNPOW]
    \\ simp[ag32Theory.Next_def]
    \\ qmatch_goalsub_abbrev_tac`pc + 2w`
    \\ simp[GSYM get_mem_word_def]
    \\ last_assum(qspec_then`3`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ simp_tac(srw_ss())[ag32_ffi_write_num_written_code_def]
    \\ `t1.MEM = s.MEM` by simp[Abbr`t1`,dfn'JumpIfZero_MEM]
    \\ simp[]
    \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
    \\ DEP_REWRITE_TAC[byte_aligned_imp]
    \\ conj_tac
    >- (
      irule byte_aligned_add
      \\ fs[]
      \\ EVAL_TAC )
    \\ strip_tac
    \\ simp[Abbr`pc`]
    \\ simp[ag32_targetProofTheory.Decode_Encode]
    \\ simp[ag32Theory.Run_def] )
  \\ simp[Abbr`P`]
  \\ `cs.MEM = s.MEM` by (
    simp[Abbr`cs`,Abbr`t1`]
    \\ rw[dfn'Normal_MEM, dfn'JumpIfZero_MEM] )
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ last_assum(qspec_then`4`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_num_written_code_def]
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac
  \\ simp[Abbr`pc`]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ next_tac 5
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s6`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ last_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s6.PC = s.PC + n2w (4 * 6)`
  by ( simp[Abbr`s6`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s5.R 3w = s.R 3w + 1w`
  by (
    simp[Abbr`s5`, ag32Theory.dfn'Shift_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`cs`, Abbr`t1`]
    \\ simp[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def, ag32Theory.ALU_def]
    \\ simp[ag32Theory.incPC_def, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def]
    \\ qmatch_goalsub_abbrev_tac`v2w [cnd]`
    \\ `s2.R 3w = s.R 3w + 1w`
    by(
      simp[Abbr`s2`, ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
      \\ simp[Abbr`s1`]
      \\ simp[ag32Theory.incPC_def, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
              ag32Theory.ri2word_def, ag32Theory.ALU_def]
      \\ simp[APPLY_UPDATE_THM] )
    \\ Cases_on`cnd` \\ rw[APPLY_UPDATE_THM] )
  \\ `∀k. k < LENGTH ag32_ffi_write_num_written_code ⇒
      (get_mem_word s6.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_write_num_written_code))`
  by (
    qx_gen_tac`k`
    \\ strip_tac
    \\ last_x_assum drule
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[Abbr`s6`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
    \\ fs[EVAL``LENGTH ag32_ffi_write_num_written_code``]
    \\ Cases_on`s.R 3w` \\ Cases_on`s.PC` \\ fs[word_add_n2w]
    \\ IF_CASES_TAC \\ fs[]
    >- ( last_x_assum(qspec_then`4 * k + 3`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( last_x_assum(qspec_then`4 * k + 2`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( last_x_assum(qspec_then`4 * k + 1`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( last_x_assum(qspec_then`4 * k + 0`mp_tac) \\ simp[DIV_LT_X] ) )
  \\ first_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s7`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ last_assum(qspec_then`7`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s7.PC = s.PC + n2w (4 * 7)`
  by ( simp[Abbr`s7`, dfn'Normal_PC] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ first_assum(qspec_then`7`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ `s7.MEM = s6.MEM` by simp[Abbr`s7`, dfn'Normal_MEM]
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s8`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s8.PC = s.PC + n2w (4 * 8)`
  by ( simp[Abbr`s8`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s7.R 3w = s.R 3w + 2w`
  by (
    simp[Abbr`s7`]
    \\ simp[ag32Theory.incPC_def, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ simp[Abbr`s6`]
      \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def])
  \\ `∀k. k < LENGTH ag32_ffi_write_num_written_code ⇒
      (get_mem_word s8.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_write_num_written_code))`
  by (
    qx_gen_tac`k`
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[Abbr`s8`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
    \\ fs[EVAL``LENGTH ag32_ffi_write_num_written_code``]
    \\ Cases_on`s.R 3w` \\ Cases_on`s.PC` \\ fs[word_add_n2w]
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`4 * k + 3`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`4 * k + 2`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`4 * k + 1`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`4 * k + 0`mp_tac) \\ simp[DIV_LT_X] ) )
  \\ first_assum(qspec_then`8`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s9`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s9.PC = s.PC + n2w (4 * 9)`
  by ( simp[Abbr`s9`, dfn'Normal_PC] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s9.MEM = s8.MEM` by simp[Abbr`s9`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s10`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s10.PC = s.PC + n2w (4 * 10)`
  by ( simp[Abbr`s10`, dfn'Normal_PC] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s10.MEM = s9.MEM` by simp[Abbr`s10`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`10`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM]
QED

Theorem ag32_ffi_write_code_thm:
   (∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_code))) ∧
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint)) ∧
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   bytes_in_memory (s.R 3w) (n1::n0::off1::off0::tll) s.MEM md ∧
   (w2n (s.R 4w) = 4 + LENGTH tll) ∧
   w2n (s.R 3w) + 4 + LENGTH tll < dimword(:32) ∧ (* not sure whether/why this is needed: can't get from bytes_in_memory? *)
   DISJOINT md { s.PC + n2w k | k | k DIV 4 < LENGTH ag32_ffi_write_code } ∧
   DISJOINT md { w | n2w startup_code_size <=+ w ∧ w <+ n2w heap_start_offset }
   (* ∧ md ⊆ { w | w | r0 <+ w ∧ r0 + w <=+ r0 + n2w memory_size }*)
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write s)
Proof
  rw[]
  \\ simp[ag32_ffi_write_def]
  \\ mp_tac ag32_ffi_write_set_id_code_thm
  \\ impl_tac
  >- (
    fs[ag32_ffi_write_code_def]
    \\ simp[EL_APPEND_EQN]
    \\ EVAL_TAC )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s1`
  \\ qspec_then`s1`mp_tac(Q.GEN`s`ag32_ffi_write_check_conf_code_thm)
  \\ mp_tac ag32_ffi_write_set_id_thm
  \\ impl_tac >- rw[]
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ last_x_assum mp_tac
  \\ qho_match_abbrev_tac`P s.MEM ⇒ _`
  \\ strip_tac
  \\ `P s1.MEM`
  by (
    fs[Abbr`P`]
    \\ simp[Abbr`s1`]
    \\ fs[ag32_ffi_write_code_def]
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
    \\ pop_assum mp_tac
    \\ EVAL_TAC \\ simp[]
    \\ fs[word_add_n2w] )
  \\ fs[Abbr`P`]
  \\ `byte_aligned s1.PC`
  by ( simp[Abbr`s1`] \\ EVAL_TAC )
  \\ impl_tac
  >- (
    simp[Abbr`s1`]
    \\ fs[ag32_ffi_write_code_def]
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w] )
  \\ strip_tac
  \\ qspec_then`s1`mp_tac(Q.GEN`s`ag32_ffi_write_check_conf_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s1`,APPLY_UPDATE_THM]
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(last_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM] \\ rw[]
    \\ drule_then drule
        (GEN_ALL asmPropsTheory.bytes_in_memory_all_pcs
         |> SIMP_RULE(srw_ss())[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
         |> CONV_RULE SWAP_FORALL_CONV |> Q.SPEC`0`
         |> SIMP_RULE(srw_ss())[])
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT, DISJ_EQ_IMP]
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ qpat_x_assum`_ = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s2`
  \\ `s2.MEM = s1.MEM` by simp[Abbr`s2`]
  \\ qspec_then`s2`mp_tac(Q.GEN`s`ag32_ffi_write_load_noff_code_thm)
  \\ `byte_aligned s2.PC` by (
    simp[Abbr`s2`]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ impl_tac
  >- (
    simp[]
    \\ simp[Abbr`s2`]
    \\ fs[ag32_ffi_write_code_def]
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code
                                  + LENGTH ag32_ffi_write_check_conf_code`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ `x = y` by (simp[Abbr`x`, Abbr`y`] \\ EVAL_TAC \\ simp[])
    \\ fs[])
  \\ strip_tac
  \\ qspec_then`s2`mp_tac(Q.GEN`s`ag32_ffi_write_load_noff_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,APPLY_UPDATE_THM]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(last_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM] \\ rw[]
    \\ drule_then (drule o SIMP_RULE(srw_ss())[])
        (GEN_ALL asmPropsTheory.bytes_in_memory_all_pcs
         |> SIMP_RULE(srw_ss())[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
         |> CONV_RULE SWAP_FORALL_CONV |> Q.SPEC`0`
         |> SIMP_RULE(srw_ss())[])
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT, DISJ_EQ_IMP]
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ qpat_x_assum`_ = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s3`
  \\ `s3.MEM = s1.MEM` by fs[Abbr`s3`, Abbr`s2`]
  \\ `byte_aligned s3.PC` by (
    simp[Abbr`s3`]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ simp[]
  \\ qspec_then`s3`mp_tac(Q.GEN`s`ag32_ffi_write_check_lengths_code_thm)
  \\ impl_tac
  >- (
    simp[]
    \\ fs[ag32_ffi_write_code_def]
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code
                                  + LENGTH ag32_ffi_write_check_conf_code
                                  + LENGTH ag32_ffi_write_load_noff_code`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ `x = y` by (simp[Abbr`x`, Abbr`y`, Abbr`s3`, Abbr`s2`] \\ EVAL_TAC \\ simp[])
    \\ fs[])
  \\ strip_tac
  \\ reverse IF_CASES_TAC
  >- (
    qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = s4`
    \\ `s4.MEM = s1.MEM` by fs[Abbr`s4`, ag32_ffi_write_check_lengths_MEM]
    \\ qmatch_goalsub_abbrev_tac`ag32_ffi_return s5`
    \\ qspec_then`s5`mp_tac(Q.GEN`s`ag32_ffi_return_code_thm)
    \\ qspec_then`s3`mp_tac (Q.GEN`s`ag32_ffi_write_check_lengths_PC)
    \\ simp[]
    \\ strip_tac
    \\ impl_tac
    >- (
      simp[Abbr`s5`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
      \\ `(s4.R 3w = s.R 3w) ∧ (s4.R 5w = n2w output_offset)`
      by (
        simp[Abbr`s4`, ag32_ffi_write_check_lengths_R]
        \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
        \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
        \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
        \\ EVAL_TAC \\ simp[])
      \\ reverse conj_tac
      >- (
        CONV_TAC(RAND_CONV EVAL)
        \\ simp[]
        \\ irule byte_aligned_add
        \\ simp[]
        \\ EVAL_TAC )
      \\ qx_gen_tac`j`
      \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_code
                                    - LENGTH ag32_ffi_return_code`mp_tac)
      \\ simp[ag32_ffi_write_code_def]
      \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`, EL_CONS, PRE_SUB1]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ disch_then(SUBST1_TAC o SYM)
      \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y = get_mem_word _ x`
      \\ `x = y` by (simp[Abbr`x`, Abbr`y`, Abbr`s3`, Abbr`s2`]
                     \\ simp[word_add_n2w] \\ EVAL_TAC )
      \\ simp[APPLY_UPDATE_THM, get_mem_word_def]
      \\ pop_assum kall_tac
      \\ simp[Abbr`y`]
      \\ EVAL_TAC \\ simp[]
      \\ simp[Abbr`s3`, Abbr`s2`]
      \\ simp[word_add_n2w]
      \\ EVAL_TAC
      \\ simp[]
      \\ fs[word_add_n2w]
      \\ qpat_x_assum`j < _`mp_tac \\ EVAL_TAC \\ strip_tac
      \\ simp[]
      \\ fs[bytes_in_memory_def]
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ simp[IN_DISJOINT]
      \\ EVAL_TAC
      \\ simp[DISJ_EQ_IMP]
      \\ ntac 2 strip_tac
      \\ res_tac
      \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ fs[word_ls_n2w,  word_lo_n2w]
      \\ rfs[])
    \\ strip_tac
    \\ pop_assum(SUBST1_TAC o SYM)
    \\ `s5 = Next (Next s4)`
    by (
      simp[ag32Theory.Next_def]
      \\ qmatch_goalsub_abbrev_tac`pc + 2w`
      \\ pop_assum mp_tac
      \\ DEP_ONCE_REWRITE_TAC[byte_aligned_imp]
      \\ conj_tac
      >- (
        CONV_TAC(RAND_CONV EVAL)
        \\ simp[]
        \\ irule byte_aligned_add
        \\ simp[]
        \\ EVAL_TAC )
      \\ simp[GSYM get_mem_word_def]
      \\ CONV_TAC(LAND_CONV EVAL) \\ simp[]
      \\ strip_tac \\ simp[Abbr`pc`]
      \\ first_assum(qspec_then`LENGTH ag32_ffi_write_set_id_code + (360 DIV 4)`mp_tac)
      \\ impl_tac >- EVAL_TAC
      \\ simp[]
      \\ qmatch_goalsub_abbrev_tac`get_mem_word s1mem pcc`
      \\ `pcc = s3.PC + 172w`
      by (
        simp[Abbr`pcc`, Abbr`s3`]
        \\ simp[Abbr`s2`,Abbr`s1`]
        \\ EVAL_TAC
        \\ simp[] )
      \\ qpat_x_assum`Abbrev(pcc = _)`kall_tac
      \\ pop_assum SUBST_ALL_TAC
      \\ simp[Abbr`s1`, ag32_targetProofTheory.Decode_Encode]
      \\ disch_then kall_tac
      \\ qmatch_goalsub_abbrev_tac`s6.MEM`
      \\ pop_assum mp_tac
      \\ CONV_TAC(PATH_CONV"lrr"EVAL)
      \\ strip_tac
      \\ qunabbrev_tac`s6`
      \\ simp[Q.SPEC`StoreMEMByte _`ag32Theory.Run_def]
      \\ simp[Abbr`s5`]
      \\ AP_THM_TAC
      \\ qmatch_goalsub_abbrev_tac`s5 = _`
      \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
      \\ DEP_ONCE_REWRITE_TAC[byte_aligned_imp]
      \\ conj_tac
      >- (
        CONV_TAC(RAND_CONV EVAL)
        \\ simp[]
        \\ irule byte_aligned_add
        \\ simp[]
        \\ EVAL_TAC )
      \\ `(s4.R 3w = s.R 3w)`
      by (
        simp[Abbr`s4`, ag32_ffi_write_check_lengths_R]
        \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
        \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
        \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
        \\ EVAL_TAC \\ simp[])
      \\ simp[Abbr`s3`, Abbr`s2`]
      \\ CONV_TAC(PATH_CONV"rrrr"EVAL)
      \\ simp[]
      \\ simp[Abbr`s1mem`]
      \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
      \\ CONV_TAC(PATH_CONV"rrr"EVAL)
      \\ fs[bytes_in_memory_def]
      \\ qpat_x_assum`s.R 3w ∈ md`mp_tac
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ simp[IN_DISJOINT]
      \\ simp[DISJ_EQ_IMP]
      \\ ntac 3 strip_tac
      \\ IF_CASES_TAC
      >- (
        rpt(first_x_assum drule)
        \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
        \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
        \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
        \\ fs[word_ls_n2w,  word_lo_n2w, word_add_n2w] \\ rfs[])
      \\ IF_CASES_TAC
      >- (
        rpt(first_x_assum drule)
        \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
        \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
        \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
        \\ fs[word_ls_n2w,  word_lo_n2w, word_add_n2w] \\ rfs[])
      \\ IF_CASES_TAC
      >- (
        rpt(first_x_assum drule)
        \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
        \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
        \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
        \\ fs[word_ls_n2w,  word_lo_n2w, word_add_n2w] \\ rfs[])
      \\ IF_CASES_TAC
      >- (
        rpt(first_x_assum drule)
        \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
        \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
        \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
        \\ fs[word_ls_n2w,  word_lo_n2w, word_add_n2w] \\ rfs[])
      \\ last_x_assum(qspec_then`LENGTH ag32_ffi_write_code - LENGTH ag32_ffi_return_code - 1`mp_tac)
      \\ impl_tac >- EVAL_TAC
      \\ CONV_TAC(PATH_CONV"lrr"EVAL)
      \\ CONV_TAC(PATH_CONV"lrlr"EVAL)
      \\ simp[]
      \\ simp[ag32_targetProofTheory.Decode_Encode]
      \\ simp[ag32Theory.Run_def,FUN_EQ_THM] )
    \\ pop_assum SUBST1_TAC
    \\ qpat_x_assum`_ = s4`(SUBST1_TAC o SYM)
    \\ fs[] \\ rfs[]
    \\ qpat_x_assum`FUNPOW Next _ _ = s3`(SUBST1_TAC o SYM)
    \\ qpat_x_assum`FUNPOW Next _ _ = s2`(SUBST1_TAC o SYM)
    \\ qpat_x_assum`FUNPOW Next _ _ = s1`(SUBST1_TAC o SYM)
    \\ simp[GSYM FUNPOW_ADD, GSYM FUNPOW]
    \\ metis_tac[])
  \\ qspec_then`s3`mp_tac(GEN_ALL ag32_ffi_write_check_lengths_thm)
  \\ qmatch_asmsub_abbrev_tac`7w =+ n2w off`
  \\ qmatch_asmsub_abbrev_tac`6w =+ v2w [cnd]`
  \\ qmatch_asmsub_abbrev_tac`1w =+ n2w n`
  \\ disch_then(qspecl_then[`off`,`n`,`LENGTH tll`,`cnd`]mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`s3`, Abbr`s2`, APPLY_UPDATE_THM]
    \\ simp[Abbr`off`, Abbr`n`]
    \\ simp[MarshallingTheory.w22n_def]
    \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[]
    \\ Cases_on`off0` \\ Cases_on`off1` \\ fs[]
    \\ fs[bytes_in_memory_def]
    \\ Cases_on`s1.R 4w` \\ fs[]
    \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
    \\ simp[word_add_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s4`
  \\ `s4.MEM = s1.MEM` by simp[Abbr`s4`]
  \\ qspec_then`s4`mp_tac(Q.GEN`s`ag32_ffi_write_write_header_code_thm)
  \\ impl_tac
  >- (
    reverse conj_tac
    >- (
      simp[Abbr`s1`] \\ fs[]
      \\ simp[Abbr`s4`, APPLY_UPDATE_THM]
      \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
      \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ simp[])
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code
                                  + LENGTH ag32_ffi_write_check_conf_code
                                  + LENGTH ag32_ffi_write_load_noff_code
                                  + LENGTH ag32_ffi_write_check_lengths_code`mp_tac)
    \\ impl_tac >- (
      pop_assum mp_tac
      \\ EVAL_TAC \\ rw[] )
    \\ simp[ag32_ffi_write_code_def]
    \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ `x = y` by (
      simp[Abbr`x`, Abbr`y`] \\ fs[]
      \\ simp[Abbr`s3`, Abbr`s2`, word_add_n2w])
    \\ fs[])
  \\ strip_tac
  \\ fs[]
  \\ qspec_then`s4`mp_tac(GEN_ALL ag32_ffi_write_write_header_thm)
  \\ disch_then(qspecl_then[`n1`,`n0`,`conf`]mp_tac)
  \\ reverse(Cases_on`cnd`)
  >- (
    fs[Abbr`s4`]
    \\ qpat_x_assum`_ MOD _ = _`mp_tac
    \\ EVAL_TAC )
  \\ qpat_x_assum`Abbrev(T = _)`mp_tac
  \\ simp[markerTheory.Abbrev_def] \\ strip_tac
  \\ impl_tac
  >- (
    simp[]
    \\ simp[Abbr`s4`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT, DISJ_EQ_IMP]
    \\ ntac 2 strip_tac
    \\ first_x_assum drule
    \\ EVAL_TAC
    \\ Cases_on`s.R 3w` \\ fs[]
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s5`
  \\ fs[]
  \\ qspec_then`s5`mp_tac(Q.GEN`s`ag32_ffi_write_num_written_code_thm)
  \\ `(∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word s5.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_code)))`
  by (
    qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j`mp_tac)
    \\ impl_tac >- fs[]
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[]
    \\ simp[APPLY_UPDATE_THM, get_mem_word_def, Abbr`s5`]
    \\ EVAL_TAC \\ simp[]
    \\ simp[Abbr`s3`, Abbr`s2`,Abbr`s4`,APPLY_UPDATE_THM]
    \\ fs[ word_add_n2w]
    \\ qpat_x_assum`j < _`mp_tac \\ EVAL_TAC \\ strip_tac
    \\ simp[]
    \\ fs[bytes_in_memory_def]
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT]
    \\ EVAL_TAC
    \\ simp[DISJ_EQ_IMP]
    \\ ntac 2 strip_tac
    \\ res_tac
    \\ `s1.R 3w = s.R 3w` by simp[Abbr`s1`,APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w,  word_lo_n2w]
    \\ rfs[]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ fs[]
    \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
  \\ impl_tac
  >- (
    conj_tac
    >- (
      qx_gen_tac`j`
      \\ strip_tac
      \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code
                                    + LENGTH ag32_ffi_write_check_conf_code
                                    + LENGTH ag32_ffi_write_load_noff_code
                                    + LENGTH ag32_ffi_write_check_lengths_code
                                    + LENGTH ag32_ffi_write_write_header_code`mp_tac)
      \\ impl_tac >- (
        pop_assum mp_tac
        \\ EVAL_TAC \\ rw[] )
      \\ simp[ag32_ffi_write_code_def]
      \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
      \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
      \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
      \\ `x = y` by (simp[Abbr`x`, Abbr`y`,Abbr`s5`,Abbr`s3`,Abbr`s2`, word_add_n2w])
      \\ fs[] )
    \\ simp[Abbr`s5`, APPLY_UPDATE_THM]
    \\ conj_tac
    >- (
      CONV_TAC(RAND_CONV EVAL)
      \\ simp[]
      \\ irule byte_aligned_add
      \\ simp[]
      \\ EVAL_TAC )
    \\ simp[Abbr`s3`, Abbr`s2`, Abbr`s4`, APPLY_UPDATE_THM, Abbr`s1`,word_add_n2w]
    \\ EVAL_TAC
    \\ simp[]
    \\ simp[GSYM IMP_CONJ_THM, GSYM FORALL_AND_THM]
    \\ qx_gen_tac`j` \\ strip_tac
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[DIV_LT_X]
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`n2w _ ∈ md`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT, DISJ_EQ_IMP]
    \\ EVAL_TAC \\ simp[]
    \\ ntac 3 strip_tac
    \\ res_tac
    \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ rfs[])
  \\ strip_tac
  \\ `s5.R 3w = s.R 3w`
  by ( simp[Abbr`s5`, Abbr`s4`, Abbr`s3`, Abbr`s2`, Abbr`s1`, APPLY_UPDATE_THM] )
  \\ qspec_then`s5`mp_tac(CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_write_num_written_thm))
  \\ simp[]
  \\ fs[bytes_in_memory_def]
  \\ `s4.R 3w = s.R 3w` by simp[Abbr`s4`, Abbr`s3`, Abbr`s2`, Abbr`s1`,APPLY_UPDATE_THM]
  \\ `s5.R 1w = n2w n`by simp[Abbr`s5`, Abbr`s4`, Abbr`s3`, APPLY_UPDATE_THM]
  \\ simp[]
  \\ disch_then(qspecl_then[`tll`,`n`,`md`]mp_tac)
  \\ impl_keep_tac
  >- (
    simp[]
    \\ simp[Abbr`s5`,APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      simp[Abbr`n`,MarshallingTheory.w22n_def]
      \\ Cases_on`n0` \\Cases_on`n1` \\ fs[] )
    \\ irule bytes_in_memory_change_mem
    \\ qexists_tac`s.MEM` \\ simp[]
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ simp[word_add_n2w] \\ fs[]
    \\ gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ simp[Abbr`s1`,APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, word_ls_n2w,word_lo_n2w]
    \\ drule (GEN_ALL asmPropsTheory.bytes_in_memory_all_pcs)
    \\ disch_then(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ qhdtm_assum`DISJOINT`mp_tac
    \\ simp_tac (srw_ss()) [IN_DISJOINT,DISJ_EQ_IMP]
    \\ ntac 2 strip_tac
    \\ first_x_assum drule
    \\ EVAL_TAC \\ simp[] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s6`
  \\ fs[]
  \\ qspec_then`s6`mp_tac ag32_ffi_copy_code_thm
  \\ `byte_aligned s6.PC`
  by (
    simp[Abbr`s6`]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[Abbr`s5`]
    \\ CONV_TAC(RAND_CONV EVAL)
    \\ simp[]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ `s6.R 5w = n2w (output_offset + 12)`
  by (
    simp[Abbr`s6`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, APPLY_UPDATE_THM])
  \\ `s6.R 1w = n2w (MIN n output_buffer_size)`
  by (
    simp[Abbr`s6`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, APPLY_UPDATE_THM])
  \\ `s6.PC = n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint +
                        4 * LENGTH ag32_ffi_write_set_id_code +
                        4 * LENGTH ag32_ffi_write_check_conf_code +
                        4 * LENGTH ag32_ffi_write_load_noff_code +
                        4 * LENGTH ag32_ffi_write_check_lengths_code +
                        4 * LENGTH ag32_ffi_write_write_header_code +
                        4 * LENGTH ag32_ffi_write_num_written_code )`
  by (simp[Abbr`s6`,Abbr`s5`,Abbr`s3`,Abbr`s2`,Abbr`s1`,word_add_n2w])
  \\ qmatch_asmsub_abbrev_tac`s6.PC = n2w wcoff`
  \\ `(∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word s6.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_code)))`
  by (
    qx_gen_tac`j`
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM ADD_ASSOC]
    \\ qmatch_asmsub_abbrev_tac`wcoff = _ + (_ + wcr)`
    \\ first_x_assum(qspec_then`j`mp_tac)
    \\ impl_tac >- (
      simp[Abbr`wcr`]
      \\ pop_assum mp_tac
      \\ EVAL_TAC \\ rw[] )
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ simp[get_mem_word_def,APPLY_UPDATE_THM,Abbr`s6`]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ simp[Abbr`y`,Abbr`wcoff`]
    \\ EVAL_TAC
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[GSYM word_add_n2w]
    \\ qpat_x_assum`n2w _ ∈ _`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp_tac (srw_ss()) [IN_DISJOINT,DISJ_EQ_IMP]
    \\ EVAL_TAC
    \\ ntac 2 strip_tac
    \\ first_x_assum drule
    \\ simp[]
    \\ simp[word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`j < _`mp_tac
    \\ EVAL_TAC
    \\ simp[])
  \\ impl_keep_tac
  >- (
    simp[]
    \\ reverse conj_tac
    >- (
      qpat_x_assum`Abbrev(wcoff = _)`mp_tac
      \\ EVAL_TAC
      \\ strip_tac \\ simp[Abbr`wcoff`]
      \\ conj_tac >- rw[MIN_DEF]
      \\ simp[IN_DISJOINT, PULL_FORALL, DISJ_EQ_IMP, PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[DIV_LT_X]
      \\ strip_tac
      \\ strip_tac
      \\ qpat_x_assum`_ = _`mp_tac
      \\ simp[] )
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM ADD_ASSOC]
    \\ qmatch_asmsub_abbrev_tac`wcoff = _ + (_ + wcr)`
    \\ first_x_assum(qspec_then`j + wcr DIV 4`mp_tac)
    \\ impl_tac >- (
      simp[Abbr`wcr`]
      \\ pop_assum mp_tac
      \\ EVAL_TAC \\ rw[] )
    \\ simp[ag32_ffi_write_code_def]
    \\ simp[EL_APPEND_EQN, GSYM LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`, Abbr`wcr`]
    \\ once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV]
    \\ simp[LEFT_ADD_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
    \\ `x = y` by (
      simp[Abbr`x`, Abbr`y`,Abbr`wcoff`,word_add_n2w]
      \\ EVAL_TAC \\ simp[GSYM word_add_n2w] )
    \\ simp[])
  \\ strip_tac
  \\ qspec_then`s6`mp_tac ag32_ffi_copy_thm
  \\ `s6.R 3w = s5.R 3w + 4w + n2w off`
  by (
    simp[Abbr`s6`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s4`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s3`, APPLY_UPDATE_THM] )
  \\ simp[]
  \\ disch_then(qspec_then`TAKE (MIN n output_buffer_size) (DROP off tll)`mp_tac)
  \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`COND cnd`
  \\ `cnd`
  by (
    fs[Abbr`s4`]
    \\ Cases_on`cnd` \\ fs[]
    \\ qpat_x_assum`_ MOD _ = _`mp_tac
    \\ EVAL_TAC )
  \\ qunabbrev_tac`cnd` \\ fs[]
  \\ impl_tac >- (
    reverse conj_tac
    >- (
      Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ EVAL_TAC
      \\ simp[MIN_DEF]
      \\ simp[IN_DISJOINT]
      \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ CCONTR_TAC \\ fs[]
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ EVAL_TAC
      \\ simp[IN_DISJOINT, DISJ_EQ_IMP]
      \\ strip_tac
      \\ first_x_assum drule
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ `tll = TAKE off tll ++ DROP off tll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL bytes_in_memory_APPEND))))
    \\ simp[] \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`TAKE kk ll`
    \\ `ll = TAKE kk ll ++ DROP kk ll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL bytes_in_memory_APPEND))))
    \\ strip_tac
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[Abbr`s6`]
    \\ gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ Cases_on`s.R 3w`
    \\ simp[word_add_n2w, MarshallingTheory.n2w2_def]
    \\ simp[word_ls_n2w, word_lo_n2w]
    \\ fs[]
    \\ rfs[Abbr`ll`]
    \\ `kk ≤ n` by simp[Abbr`kk`]
    \\ fs[LENGTH_TAKE_EQ])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s7`
  \\ fs[]
  \\ qspec_then`s7`mp_tac(Q.GEN`s`ag32_ffi_return_code_thm)
  \\ impl_tac >- (
    reverse conj_tac
    >- (
      simp[Abbr`s7`, Abbr`s6`, APPLY_UPDATE_THM, Abbr`wcoff`]
      \\ CONV_TAC(RAND_CONV EVAL) \\ simp[]
      \\ EVAL_TAC )
    \\ qx_gen_tac`j` \\ strip_tac
    \\ simp[Abbr`s7`]
    \\ `s6.R 2w = 36w` by simp[Abbr`s6`, APPLY_UPDATE_THM]
    \\ full_simp_tac std_ss [GSYM ADD_ASSOC]
    \\ qmatch_asmsub_abbrev_tac`wcoff = _ + (_ + wcr)`
    \\ qpat_x_assum`∀k. k < LENGTH ag32_ffi_write_code ⇒ _`
         (qspec_then`j + wcr DIV 4 + LENGTH ag32_ffi_copy_code + 2`mp_tac)
    \\ impl_tac >- (
      simp[Abbr`wcr`]
      \\ qpat_x_assum`j <_`mp_tac
      \\ EVAL_TAC \\ rw[] )
    \\ simp[ag32_ffi_write_code_def]
    \\ qpat_x_assum`j < _`mp_tac \\ strip_tac
    \\ simp[EL_APPEND_EQN, GSYM LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`, Abbr`wcr`]
    \\ once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV]
    \\ simp[LEFT_ADD_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
    \\ `x = y` by (
      simp[Abbr`x`, Abbr`y`,Abbr`wcoff`, word_add_n2w]
      \\ EVAL_TAC \\ simp[GSYM word_add_n2w] )
    \\ qpat_x_assum`Abbrev(y = _)`kall_tac
    \\ pop_assum(SUBST_ALL_TAC o SYM)
    \\ simp[get_mem_word_def,APPLY_UPDATE_THM]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ simp[Abbr`x`,Abbr`wcoff`]
    \\ EVAL_TAC
    \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[GSYM word_add_n2w]
    \\ qpat_x_assum`j < _`mp_tac \\ EVAL_TAC
    \\ simp[MIN_DEF])
  \\ strip_tac
  \\ rpt(qpat_x_assum`FUNPOW Next _ _ = _`(assume_tac o SYM))
  \\ fs[]
  \\ simp[GSYM FUNPOW_ADD]
  \\ metis_tac[]
QED

Theorem ag32_ffi_read_set_id_code_thm:
   (∀k. k < LENGTH ag32_ffi_read_set_id_code ⇒
         get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_set_id_code)) ∧ byte_aligned s.PC
     ⇒
   ∃k. FUNPOW Next k s = ag32_ffi_read_set_id s
Proof
  first_tac
  \\ EVERY (List.tabulate(1, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]
QED

Theorem ag32_ffi_read_check_conf_code_thm:
   (∀k. k < LENGTH ag32_ffi_read_check_conf_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_check_conf_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_read_check_conf s)
Proof
  first_tac
  \\ EVERY (List.tabulate(32, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]
QED

Theorem ag32_ffi_read_load_lengths_code_thm:
   (∀k. k < LENGTH ag32_ffi_read_load_lengths_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_load_lengths_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_read_load_lengths s)
Proof
  first_tac
  \\ EVERY (List.tabulate(10, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]
QED

Theorem ag32_ffi_read_check_length_code_thm:
   (∀k. k < LENGTH ag32_ffi_read_check_length_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_check_length_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_read_check_length s)
Proof
  first_tac
  \\ EVERY (List.tabulate(4, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]
QED

val ffi_code_start_offset_thm = EVAL “ffi_code_start_offset”
val ag32_ffi_read_entrypoint_thm = EVAL “ag32_ffi_read_entrypoint”

val codedefs = [ag32_ffi_read_code_def, ag32_ffi_read_set_id_code_def,
                ag32_ffi_read_check_conf_code_def,
                ag32_ffi_read_check_length_code_def,
                ag32_ffi_read_num_written_code_def,
                ag32_ffi_read_load_lengths_code_def]

val bytes_in_memory_update = Q.prove(
  ‘∀bs a. k ∉ md ∧ bytes_in_memory a bs mf md ⇒
          bytes_in_memory a bs ((k =+ v) mf) md’,
  Induct >> simp[bytes_in_memory_def] >>
  metis_tac[combinTheory.UPDATE_APPLY]);

val bytes_in_memory_prefix = Q.prove(
  ‘∀bs sfx a. bytes_in_memory a (bs ++ sfx) mf md ⇒
              bytes_in_memory a bs mf md’,
  Induct >> simp[bytes_in_memory_def] >> metis_tac[]);

val asm_write_bytearray_avoiding = Q.prove(
  ‘∀a bs.
     x ∉ {a + n2w i | i < LENGTH bs } ⇒ asm_write_bytearray a bs f x = f x’,
  simp[] >> Induct_on ‘bs’ >> simp[asm_write_bytearray_def] >>
  simp[combinTheory.UPDATE_def] >> rw[]
  >- (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[]) >>
  first_x_assum (qspec_then ‘SUC j’ (mp_tac o Q.GEN ‘j’)) >> simp[] >>
  strip_tac >> first_x_assum irule >> fs[GSYM word_add_n2w, ADD1]);

fun glAbbrs i = EVERY (List.tabulate(i, fn j => glAbbr (i - j)))

Theorem w22n_bound:
   ∀b1 b2. w22n [b1; b2] < 65536
Proof
  rw[MarshallingTheory.w22n_def] >>
  map_every (fn q => Q.ISPEC_THEN q mp_tac w2n_lt) [‘b1’, ‘b2’] >> simp[]
QED

val ltSUC = Q.prove(
  ‘x < SUC y ⇔ x = 0 ∨ ∃x0. x = SUC x0 ∧ x0 < y’,
  Cases_on ‘x’ >> simp[]);

val n2w_o_SUC = Q.prove(
  ‘n2w o SUC = word_add 1w o n2w’,
  simp[FUN_EQ_THM, ADD1, word_add_n2w]);

val word_add_o = Q.prove(
  ‘word_add m o (word_add n o f) = word_add (m + n) o f’,
  simp[FUN_EQ_THM]);



Theorem bytes_in_memory_GENLIST:
   ∀sz base f.
      bytes_in_memory base (GENLIST (m o word_add base o n2w) sz) m md ⇔
      ∀a. a < sz ⇒ base + n2w a ∈ md
Proof
  Induct >> simp[bytes_in_memory_def, GENLIST_CONS] >>
  simp[ltSUC, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM, ADD1,
       GSYM word_add_n2w, CONJ_ASSOC, n2w_o_SUC, word_add_o]
QED

val WORD_ADD_CANCEL_LBARE = Q.prove(
  ‘y ≤ x ⇒ (n2w x = n2w y + z ⇔ z = n2w (x - y))’,
  strip_tac >> eq_tac
  >- (disch_then (mp_tac o AP_TERM “(+) (- (n2w y) : α word)” ) >>
      simp_tac bool_ss [WORD_ADD_ASSOC, WORD_ADD_LINV] >> simp[] >>
      simp[WORD_LITERAL_ADD]) >>
  simp[word_add_n2w]);

val lbare' = CONV_RULE (PATH_CONV "rlr" (REWR_CONV EQ_SYM_EQ THENC
                                         LAND_CONV (REWR_CONV WORD_ADD_COMM)))
                       WORD_ADD_CANCEL_LBARE

val stupid1 = Q.prove(
‘∀i. i ∈ {0w;1w;2w;3w} ∧ w2n (a0 : word32)  < 4294967292 ⇒ a0 + i ≠ UINT_MAXw’,
simp[DISJ_IMP_THM, FORALL_AND_THM, RIGHT_AND_OVER_OR] >>
rpt conj_tac >> Q.ISPEC_THEN ‘a0’ mp_tac ranged_word_nchotomy >>
simp[PULL_EXISTS, word_add_n2w, word_eq_n2w, bitTheory.MOD_2EXP_MAX_def,
     bitTheory.MOD_2EXP_def])
  |> SIMP_RULE (srw_ss()) [RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM]
  |> CONJUNCTS
  |> map UNDISCH

fun w2nit i =
    w2n_plus1 |> Q.ISPEC [QUOTE ("(a0 + " ^ Int.toString i ^ "w : word32)")]
              |> SIMP_RULE (srw_ss()) (lbare' :: stupid1)
              |> SYM
val w2ns = List.tabulate (4, w2nit)
fun simpem [] = raise Fail ""
  | simpem [th] = SIMP_RULE (srw_ss() ++ ARITH_ss) [] th
  | simpem (th::ths) = simpem (map (SIMP_RULE (srw_ss()) [th]) ths)
val stupid = DISCH_ALL (simpem w2ns)

Theorem ag32_ffi_read_code_thm:
   (∀k. k < LENGTH ag32_ffi_read_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_read_code))) ∧
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_read_entrypoint)) ∧
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   bytes_in_memory (s.R 3w) (n1::n0::off1::off0::tll) s.MEM md ∧
   (w2n (s.R 4w) = 4 + LENGTH tll) ∧
   w2n (s.R 3w) + 4 + LENGTH tll < dimword(:32) ∧ (* not sure whether/why this is needed: can't get from bytes_in_memory? *)
   w2n (get_mem_word s.MEM (n2w stdin_offset)) ≤
     w2n (get_mem_word s.MEM (n2w (stdin_offset + 4))) ∧
   w2n (get_mem_word s.MEM (n2w (stdin_offset + 4))) ≤ stdin_size ∧
   w2n (s.R 3w + 4w) + output_buffer_size + 1 < 4294967296 ∧
   output_buffer_size + stdin_size + stdin_offset + 8 ≤ w2n (s.R 3w) ∧
   DISJOINT md { s.PC + n2w k | k | k DIV 4 < LENGTH ag32_ffi_read_code } ∧
   DISJOINT md { w | n2w startup_code_size <=+ w ∧ w <+ n2w heap_start_offset }
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_read s)
Proof
  simp0[ag32_ffi_read_def] >> strip_tac >>
  ‘s.R 3w ∈ md’
    by (qpat_assum ‘bytes_in_memory (s.R 3w) _ _ _’
          (mp_then (Pos hd) mp_tac bytes_in_memory_in_domain) >>
        disch_then (qspec_then ‘0’ mp_tac) >> simp[]) >>
  ‘∃k1. FUNPOW Next k1 s = ag32_ffi_read_set_id s’
    by (print_tac "read_code_thm: 1. read_set_id" >>
        irule ag32_ffi_read_set_id_code_thm >>
        fs[ag32_ffi_read_code_def, EL_APPEND1] >> EVAL_TAC) >>
  Q.REFINE_EXISTS_TAC ‘krest + k1’ >> simp0[FUNPOW_ADD] >>
  qmatch_abbrev_tac ‘∃krest. FUNPOW Next krest s1 = LET _ s1’ >>
  simp0 [Once LET_THM] >>
  assume_tac (EVAL “LENGTH ag32_ffi_read_set_id_code”) >>
  assume_tac (EVAL “LENGTH ag32_ffi_read_check_conf_code”) >>
  full_simp_tac(srw_ss())[ag32_ffi_read_set_id_thm, ffi_code_start_offset_thm,
                          FFI_codes_def] >>

  ‘∃k2. FUNPOW Next k2 s1 = ag32_ffi_read_check_conf s1’
    by (print_tac "read_code_thm: 2. read_check_conf" >>
        irule ag32_ffi_read_check_conf_code_thm >>
        simp[Abbr‘s1’] >>
        qmatch_abbrev_tac ‘_ ∧ byte_aligned _’ >> reverse conj_tac >- EVAL_TAC>>
        qx_gen_tac `k` >> strip_tac >>
        simp[ffi_code_start_offset_thm, ag32_ffi_read_entrypoint_thm] >>
        first_x_assum
          (qspec_then `k + LENGTH ag32_ffi_read_set_id_code` mp_tac) >>
        simp[ag32_ffi_read_entrypoint_thm, ffi_code_start_offset_thm,
             LEFT_ADD_DISTRIB, word_add_n2w] >> impl_tac
        >- (EVAL_TAC >> simp[]) >>
        simp[EL_APPEND1, EL_APPEND2, ag32_ffi_read_code_def] >>
        disch_then (SUBST1_TAC o SYM) >>
        irule get_mem_word_change_mem >>
        simp[combinTheory.UPDATE_def, word_add_n2w]) >>
  Q.REFINE_EXISTS_TAC ‘krest + k2’ >> simp0[FUNPOW_ADD] >>
  qmatch_abbrev_tac ‘∃krest. FUNPOW Next krest s2 = LET _ s2’ >>
  simp0[Once LET_THM] >>
  assume_tac (EVAL “LENGTH ag32_ffi_read_load_lengths_code”) >>
  ‘bytes_in_memory (s1.R 1w) conf s1.MEM md’
     by (simp[Abbr‘s1’, combinTheory.UPDATE_APPLY] >>
         irule bytes_in_memory_update >> simp[] >>
         qpat_x_assum `DISJOINT md _` mp_tac >> EVAL_TAC >>
         simp[DISJOINT_ALT] >> rpt strip_tac >>
         res_tac >> fs[]) >>
  drule_then mp_tac ag32_ffi_read_check_conf_thm >> impl_tac
  >- rw[Abbr`s1`, combinTheory.UPDATE_APPLY] >>
  disch_then strip_assume_tac >> pop_assum SUBST_ALL_TAC >>
  ‘∃k3. FUNPOW Next k3 s2 = ag32_ffi_read_load_lengths s2’
    by (print_tac "read_code_thm: 3. read_load_lengths" >>
        irule ag32_ffi_read_load_lengths_code_thm >>
        simp[Abbr`s2`, Abbr`s1`] >>
        qmatch_abbrev_tac ‘_ ∧ byte_aligned _’ >> reverse conj_tac >- EVAL_TAC>>
        qx_gen_tac `k` >>
        simp[ffi_code_start_offset_thm, ag32_ffi_read_entrypoint_thm] >>
        strip_tac >>
        first_x_assum
          (qspec_then ‘k + LENGTH ag32_ffi_read_set_id_code +
                       LENGTH ag32_ffi_read_check_conf_code’ mp_tac) >>
        simp[ag32_ffi_read_code_def, EL_APPEND1, EL_APPEND2] >>
        disch_then (SUBST1_TAC o SYM) >>
        simp[word_add_n2w, LEFT_ADD_DISTRIB, ag32_ffi_read_entrypoint_thm,
             ffi_code_start_offset_thm] >>
        irule get_mem_word_change_mem >>
        simp[combinTheory.UPDATE_APPLY, word_add_n2w]) >>
  Q.REFINE_EXISTS_TAC ‘krest + k3’ >> simp0[FUNPOW_ADD] >>
  qmatch_abbrev_tac ‘∃krest. FUNPOW Next krest s3 = LET _ s3’ >>
  simp0[Once LET_THM] >>
  assume_tac (EVAL “LENGTH ag32_ffi_read_check_length_code”) >>
  full_simp_tac(srw_ss()) [] >> rev_full_simp_tac(srw_ss()) [] >>
  print_tac "read_code_thm: 3a. calculate read_load_lengths effect" >>
  ‘bytes_in_memory (s2.R 3w) [n1;n0] s2.MEM md’
    by (simp[Abbr‘s2’, Abbr‘s1’, combinTheory.UPDATE_APPLY] >>
        irule bytes_in_memory_update >>
        qmatch_abbrev_tac ‘_ ∉ md ∧ bytes_in_memory _ _ _ md’ >>
        reverse conj_tac
        >- (irule bytes_in_memory_prefix >> simp[] >> metis_tac[]) >>
        qpat_x_assum `DISJOINT md _` mp_tac >> EVAL_TAC >>
        simp[DISJOINT_ALT] >> rpt strip_tac >>
        res_tac >> fs[]) >>
  drule (GEN_ALL ag32_ffi_read_load_lengths_thm) >>
  qabbrev_tac ‘in_off = get_mem_word s.MEM (n2w stdin_offset)’ >>
  qabbrev_tac ‘in_len = get_mem_word s.MEM (n2w (stdin_offset + 4))’ >>
  ‘get_mem_word s2.MEM (n2w stdin_offset) = in_off ∧
   get_mem_word s2.MEM (n2w (stdin_offset + 4)) = in_len’
     by (simp[Abbr‘s2’, Abbr‘s1’, Abbr‘in_off’, Abbr‘in_len’] >> EVAL_TAC) >>
  simp0[] >> disch_then (qspecl_then [‘w2n in_off’, ‘w2n in_len’] mp_tac) >>
  simp0[] >> markerLib.RM_ABBREV_TAC "s3" >>
  disch_then (REPEAT_TCL CHOOSE_THEN
               (ASSUME_TAC o
                CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def)))) >>

  ‘∃k4. FUNPOW Next k4 s3 = ag32_ffi_read_check_length s3’
    by (print_tac "read_code_thm: 4. read_check_length" >>
        irule ag32_ffi_read_check_length_code_thm >>
        EVERY (List.tabulate(3, fn j => glAbbr (3 - j))) >>
        qmatch_abbrev_tac ‘_ ∧ byte_aligned _’ >> reverse conj_tac >- EVAL_TAC>>
        qx_gen_tac `k` >>
        simp[ffi_code_start_offset_thm, ag32_ffi_read_entrypoint_thm] >>
        strip_tac >>
        first_x_assum
          (qspec_then ‘k + LENGTH ag32_ffi_read_set_id_code +
                       LENGTH ag32_ffi_read_check_conf_code +
                       LENGTH ag32_ffi_read_load_lengths_code’ mp_tac) >>
        simp[ag32_ffi_read_code_def, EL_APPEND1, EL_APPEND2] >>
        disch_then (SUBST_ALL_TAC o SYM) >>
        simp[ag32_ffi_read_entrypoint_thm, LEFT_ADD_DISTRIB, word_add_n2w] >>
        irule get_mem_word_change_mem >> simp[word_add_n2w]) >>

  Q.REFINE_EXISTS_TAC ‘krest + k4’ >> simp0[FUNPOW_ADD] >>
  qmatch_abbrev_tac ‘∃krest. FUNPOW Next krest s4 = LET _ s4’ >>
  simp0[Once LET_THM] >>
  assume_tac (EVAL “LENGTH ag32_ffi_read_check_length_code”) >>
  print_tac "read_code_thm: 4a. calculating read_check_length's effect" >>
  qmatch_asmsub_abbrev_tac `6w =+ v2w [LENGTH conf = cflen ∧ w82n conf = 0]` >>
  qabbrev_tac ‘cnd ⇔ LENGTH conf = cflen ∧ w82n conf = 0’ >>
  markerLib.UNABBREV_TAC "cflen" >>
  (ag32_ffi_read_check_length_thm
    |> Q.INST [‘n’ |-> ‘w2n (s3.R 1w)’, ‘ltll’ |-> ‘w2n (s3.R 4w)’,
               ‘s’ |-> ‘s3’]
    |> mp_tac) >>
  impl_tac
  >- (simp[Abbr‘s3’, combinTheory.UPDATE_APPLY, w2n_lt] >>
      simp[Abbr‘s2’, combinTheory.UPDATE_APPLY]) >>
  disch_then (qx_choosel_then [‘r4_4’, ‘r6_4’, ‘r8_4’, ‘cf4’, ‘ov4’] mp_tac) >>
  qmatch_goalsub_abbrev_tac ‘ag32_state_PC_fupd (K (if pcg then _ else _))’ >>
  disch_then SUBST_ALL_TAC >> full_simp_tac (srw_ss()) [] >>
  print_tac "read_code_thm: splitting on check_length's guard" >>
  reverse (Cases_on ‘pcg = T’)
  >- (‘pcg = F’ by fs[] >> COND_CASES_TAC >- rfs[Abbr‘s4’] >>
      first_assum
        (qspec_then ‘LENGTH ag32_ffi_read_set_id_code +
                     LENGTH ag32_ffi_read_check_conf_code +
                     LENGTH ag32_ffi_read_load_lengths_code +
                     LENGTH ag32_ffi_read_check_length_code +
                     LENGTH ag32_ffi_read_num_written_code +
                     LENGTH ag32_ffi_copy_code’ mp_tac)>>
      impl_tac >- simp[ag32_ffi_read_code_def] >>
      simp[ag32_ffi_read_entrypoint_thm] >>
      simp[ag32_ffi_read_code_def, EL_APPEND2, EL_APPEND1,
           ag32_ffi_copy_code_def, ag32_ffi_read_num_written_code_def] >>
      strip_tac >>
      Q.REFINE_EXISTS_TAC ‘SUC k’ >>
      simp0[FUNPOW, ag32Theory.Next_def, GSYM get_mem_word_def] >>
      ‘align4 s4.PC = s4.PC’
        by (EVERY (List.tabulate(4, fn j => glAbbr(4 - j))) >> EVAL_TAC) >>
      simp[] >>
      ‘get_mem_word s4.MEM s4.PC = get_mem_word s.MEM s4.PC’
        by (irule get_mem_word_change_mem >>
            EVERY (List.tabulate(4, fn j => glAbbr(4 - j))) >>
            simp[word_add_n2w, ag32_ffi_read_entrypoint_thm]) >>
      simp[] >> qmatch_assum_abbrev_tac ‘get_mem_word s.MEM pc = _’ >>
      ‘s4.PC = pc’ by (EVERY (List.tabulate(4, fn j => glAbbr(4 - j))) >>
                       simp[Abbr‘pc’] >> EVAL_TAC) >>
      UNABBREV_TAC "pc" >>
      simp[ag32_targetProofTheory.Decode_Encode, ag32Theory.Run_def] >>
      qmatch_abbrev_tac ‘∃k. FUNPOW Next k s5 = ag32_ffi_return s5’ >>
      irule ag32_ffi_return_code_thm >>
      print_tac "read_code_thm: return after guard was false" >>
      pop_assum mp_tac >>
      CONV_TAC (PATH_CONV "lrrr" (SIMP_CONV (srw_ss()) [
        ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def,
        ag32Theory.ri2word_def, ag32Theory.incPC_def, LET_THM,
        ag32Theory.dfn'JumpIfZero_def, ag32Theory.dfn'StoreMEMByte_def,
        ag32Theory.dfn'Shift_def, ag32Theory.dfn'StoreMEM_def,
        ag32Theory.dfn'LoadMEM_def,
        ag32Theory.dfn'LoadConstant_def])) >> strip_tac >>
      qmatch_abbrev_tac ‘_ ∧ byte_aligned _’ >> reverse conj_tac
      >- (simp[Abbr‘s5’] >> EVAL_TAC) >>
      qx_gen_tac ‘k’ >> strip_tac >>
      first_x_assum
        (qspec_then ‘LENGTH ag32_ffi_read_code -
                     LENGTH ag32_ffi_return_code + k’ mp_tac) >>
      simp[ag32_ffi_read_code_def, EL_APPEND1, EL_APPEND2] >>
      simp[ag32_ffi_copy_code_def, ag32_ffi_read_num_written_code_def,
           ag32_ffi_read_entrypoint_thm, LEFT_ADD_DISTRIB, word_add_n2w] >>
      simp[Abbr‘s5’, word_add_n2w] >> disch_then (SUBST1_TAC o SYM) >>
      irule get_mem_word_change_mem >>
      EVERY (List.tabulate(4, fn j => glAbbr(4 - j))) >>
      simp[word_add_n2w] >> rw[]
      >- (Q.UNDISCH_THEN ‘s.R 3w ∈ md’ mp_tac >>
          rpt (qpat_x_assum ‘DISJOINT _ _’ mp_tac) >> simp[DISJOINT_ALT] >>
          disch_then (fn th1 =>
            disch_then (fn th2 =>
              disch_then (fn th3 =>
                 mp_tac (MATCH_MP th1 th3) >>
                 mp_tac (MATCH_MP th2 th3)))) >>
          simp[startup_code_size_def, heap_start_offset_def,
               ffi_code_start_offset_thm, length_ag32_ffi_code_def] >>
          fs[ag32_ffi_return_code_def, word_ls_n2w, word_lo_n2w]) >>
      fs[ag32_ffi_return_code_def] >>
      qpat_x_assum ‘_ = _ MOD _’ mp_tac >> simp[]) >>
  print_tac "read_code_thm: guard = T - ffi_read_num_written" >>
  map_every UNABBREV_TAC ["pcg", "cnd"] >> full_simp_tac(srw_ss()) [] >>
  reverse COND_CASES_TAC >- (pop_assum mp_tac >> simp[Abbr‘s4’]) >>
  assume_tac (EVAL “LENGTH ag32_ffi_read_num_written_code”) >>
  ‘∃k5. FUNPOW Next k5 s4 = ag32_ffi_read_num_written s4’
    by (irule ag32_ffi_read_num_written_code_thm >> simp[] >>
        EVERY (List.tabulate(4, fn j => glAbbr(4 - j))) >>
        simp[ag32_ffi_read_entrypoint_thm] >> reverse (rpt conj_tac)
        >- (simp[stdin_offset_def, startup_code_size_def, cline_size_def,
                 word_add_n2w, DIV_LT_X] >> qx_gen_tac `k` >>
            intLib.ARITH_TAC)
        >- (simp[word_add_n2w, DIV_LT_X] >> qx_gen_tac ‘k’ >>
            REWRITE_TAC [DECIDE “p ∨ ¬q ⇔ q ⇒ p”] >> rpt strip_tac >>
            rpt (qpat_x_assum ‘DISJOINT _ _’
                    (mp_tac o Q.SPEC ‘s.R 3w’ o
                     SIMP_RULE (srw_ss()) [DISJOINT_ALT])) >>
            simp[word_ls_n2w, word_lo_n2w, word_add_n2w, startup_code_size_def,
                 heap_start_offset_def, ffi_code_start_offset_thm,
                 length_ag32_ffi_code_def])
        >- EVAL_TAC >>
        qx_gen_tac ‘k’ >> strip_tac >>
        first_x_assum (
          qspec_then
            ‘LENGTH (ag32_ffi_read_set_id_code ++
                     ag32_ffi_read_check_conf_code ++
                     ag32_ffi_read_load_lengths_code ++
                     ag32_ffi_read_check_length_code) + k’
            mp_tac) >>
        impl_tac >- (EVAL_TAC >> simp[]) >>
        simp[EL_APPEND2, EL_APPEND1, ag32_ffi_read_code_def,
            ag32_ffi_read_entrypoint_thm, LEFT_ADD_DISTRIB, word_add_n2w] >>
        disch_then (SUBST1_TAC o SYM) >>
        irule get_mem_word_change_mem >> simp[word_add_n2w]) >>
  Q.REFINE_EXISTS_TAC ‘krest + k5’ >> simp0[FUNPOW_ADD] >>
  qmatch_abbrev_tac ‘∃krest. FUNPOW Next krest s5 = _’ >>
  simp[] >>
  print_tac "read_code_thm: calculating effect of ffi_read_num_written" >>
  ‘bytes_in_memory (s4.R 3w) (n1::n0::off1::off0::tll) s4.MEM md’
    by (EVERY (List.tabulate(4, fn j => glAbbr(4 - j))) >>
        irule
          (SIMP_RULE bool_ss [combinTheory.UPDATE_def] bytes_in_memory_update)>>
        simp[] >> qpat_x_assum ‘DISJOINT _ _’ mp_tac >>
        simp[DISJOINT_ALT] >>
        disch_then (fn imp => disch_then (fn th => mp_tac (MATCH_MP imp th))) >>
        EVAL_TAC) >>
  drule (ag32_ffi_read_num_written_thm
           |> Q.GEN ‘k’
           |> Q.INST [‘n’ |-> ‘w2n (s4.R 1w)’, ‘off’ |-> ‘w2n (s4.R 5w)’,
                      ‘lcmo’ |-> ‘w2n (s4.R 7w)’]) >> simp[] >>
  impl_tac
  >- (glAbbrs 4 >> qspecl_then [‘n1’, ‘n0’] mp_tac w22n_bound >> simp[] >>
      fs[stdin_size_def]) >>
  disch_then (qx_choosel_then [‘r8_5’, ‘r4_5’, ‘cf5’, ‘ov5’] mp_tac) >>
  RM_ABBREV_TAC "s5" >>
  disch_then
    (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  assume_tac (EVAL “LENGTH ag32_ffi_copy_code”) >>
  print_tac "read_code_thm: ffi_copy" >>
  ‘∃k6. FUNPOW Next k6 s5 = ag32_ffi_copy s5’
    by (irule ag32_ffi_copy_code_thm >> reverse (rpt conj_tac)
        >- (simp[DISJOINT_ALT, PULL_EXISTS, ag32_ffi_copy_code_def, DIV_LT_X] >>
            glAbbrs 5 >> simp[word_add_n2w, ag32_ffi_read_entrypoint_thm] >>
            qx_gen_tac ‘k’ >> strip_tac >> qx_gen_tac ‘m’ >>
            REWRITE_TAC [DECIDE “p ∨ ¬q ⇔ q ⇒ p”] >> strip_tac >>
            fs[output_buffer_size_def] >>
            ONCE_REWRITE_TAC [WORD_ADD_COMM] >>
            asm_simp_tac (bool_ss ++ ARITH_ss) [GSYM word_add_n2w, sub_common]>>
            strip_tac >>
            Q.UNDISCH_THEN ‘s.R 3w ∈ md’ mp_tac >>
            rpt (qpat_x_assum ‘DISJOINT md _’ mp_tac) >> simp[DISJOINT_ALT] >>
            disch_then (fn i1 => disch_then (fn i2 => disch_then (fn th =>
              mp_tac (MATCH_MP i1 th) >> mp_tac (MATCH_MP i2 th)))) >>
            simp[word_ls_n2w, word_lo_n2w, startup_code_size_def,
                 heap_start_offset_def, word_add_n2w, ffi_code_start_offset_thm,
                 length_ag32_ffi_code_def])
        >- (glAbbrs 5 >> simp[MIN_DEF])
        >- (glAbbrs 5 >> EVAL_TAC)
        >- (glAbbrs 5 >> EVAL_TAC) >>
        qx_gen_tac ‘k’ >> glAbbrs 5 >> simp[] >> strip_tac >>
        first_x_assum (
          qspec_then
            ‘LENGTH (ag32_ffi_read_set_id_code ++
                     ag32_ffi_read_check_conf_code ++
                     ag32_ffi_read_load_lengths_code ++
                     ag32_ffi_read_check_length_code ++
                     ag32_ffi_read_num_written_code) + k’
            mp_tac) >> impl_tac
        >- (EVAL_TAC >> simp[]) >>
        simp[ag32_ffi_read_code_def, EL_APPEND1, EL_APPEND2,
             ag32_ffi_read_entrypoint_thm, LEFT_ADD_DISTRIB, word_add_n2w] >>
        disch_then (SUBST1_TAC o SYM) >> irule get_mem_word_change_mem >>
        simp[set_mem_word_def, word_add_n2w, stdin_offset_def,
             combinTheory.UPDATE_def, cline_size_def, startup_code_size_def,
             MarshallingTheory.n2w2_def, asm_write_bytearray_def] >>
        qx_gen_tac ‘m’ >> simp[sub_common, GSYM word_add_n2w] >>
        rw[] >>
        Q.UNDISCH_THEN ‘s.R 3w ∈ md’ mp_tac >>
        rpt (qpat_x_assum ‘DISJOINT md _’ mp_tac) >>
        simp[DISJOINT_ALT] >>
        disch_then (fn i1 => disch_then (fn i2 => disch_then (fn th =>
          mp_tac (MATCH_MP i1 th) >> mp_tac (MATCH_MP i2 th)))) >>
        simp[startup_code_size_def, heap_start_offset_def, word_add_n2w,
             word_lo_n2w, word_ls_n2w, ffi_code_start_offset_thm,
             length_ag32_ffi_code_def]) >>
  Q.REFINE_EXISTS_TAC ‘krest + k6’ >> simp[FUNPOW_ADD] >>
  qmatch_abbrev_tac ‘∃krest. FUNPOW Next krest s6 = ag32_ffi_return s6’ >>
  print_tac "read_code_thm: calculating copy effect" >>
  qabbrev_tac
    ‘written = GENLIST (s5.MEM o $+ (s5.R 3w) o n2w) (w2n (s5.R 1w))’ >>
  qspecl_then [‘{s5.R 3w + n2w a | a | a < w2n (s5.R 1w)}’, ‘s5’, ‘written’]
     mp_tac (GEN_ALL ag32_ffi_copy_thm) >>
  impl_tac
  >- (‘LENGTH written = w2n (s5.R 1w)’ by simp[Abbr‘written’] >> simp[] >>
      rpt conj_tac
      >- (simp[Abbr‘written’, bytes_in_memory_GENLIST] >> metis_tac[])
      >- (simp[DISJOINT_ALT, PULL_EXISTS] >> qx_gen_tac ‘a’ >>
          glAbbrs 5 >>
          simp[stdin_offset_def, cline_size_def, startup_code_size_def,
               output_buffer_size_def, word_add_n2w, word_ls_n2w] >>
          rpt strip_tac >> disj1_tac >>
          disch_then
            (mp_tac o CONV_RULE (LAND_CONV (REWR_CONV (GSYM n2w_w2n)))) >>
          simp[word_ls_n2w] >>
          fs[stdin_size_def, stupid, output_buffer_size_def, stdin_offset_def,
             cline_size_def, startup_code_size_def])
      >- (glAbbrs 5 >> fs[stupid, output_buffer_size_def] >> rfs[stupid] >>
          fs[MIN_DEF])
      >- (glAbbrs 5 >>
          fs[stdin_offset_def, output_buffer_size_def, cline_size_def,
             startup_code_size_def, stdin_size_def, MIN_DEF])) >>
  disch_then (qx_choosel_then [‘r1_6’, ‘r3_6’, ‘r5_6’, ‘r8_6’] SUBST_ALL_TAC)>>
  print_tac "read_code_thm: applying final return" >>
  irule ag32_ffi_return_code_thm >>

  qmatch_abbrev_tac ‘_ ∧ byte_aligned s6.PC’ >>
  reverse conj_tac >- (glAbbrs 6 >> EVAL_TAC) >>
  assume_tac (EVAL “LENGTH ag32_ffi_return_code”) >>
  qx_gen_tac ‘k’ >> simp[Abbr‘s6’] >> strip_tac >>
  first_x_assum (
    qspec_then
      ‘LENGTH (ag32_ffi_read_set_id_code ++
               ag32_ffi_read_check_conf_code ++
               ag32_ffi_read_load_lengths_code ++
               ag32_ffi_read_check_length_code ++
               ag32_ffi_read_num_written_code ++
               ag32_ffi_copy_code) + k + 1 (* for extra store byte instr. *)’
      mp_tac) >>
  impl_tac >- (EVAL_TAC >> simp[]) >>
  simp[ag32_ffi_read_code_def, EL_APPEND1, EL_APPEND2,
       ag32_ffi_read_entrypoint_thm, LEFT_ADD_DISTRIB, word_add_n2w] >>
  disch_then (SUBST1_TAC o SYM) >>
  qmatch_abbrev_tac `get_mem_word M1 A1 = get_mem_word s.MEM A2` >>
  `A1 = A2` by (simp[Abbr`A1`, Abbr`A2`] >> glAbbrs 5 >>
                simp[ag32_ffi_read_entrypoint_thm, word_add_n2w]) >>
  map_every UNABBREV_TAC ["A1", "A2"] >> simp[] >>
  irule get_mem_word_change_mem >>
  qx_gen_tac ‘m’ >> strip_tac >>
  UNABBREV_TAC "M1" >>
  qmatch_abbrev_tac `asm_write_bytearray base written f A = s.MEM A` >>
  ‘A ∉ { base + n2w i | i < LENGTH written}’
    by (simp[] >> qx_gen_tac `i` >> Cases_on `i < LENGTH written` >> simp[] >>
        simp[Abbr‘base’, Abbr‘A’] >> UNABBREV_TAC "written" >> fs[] >>
        pop_assum mp_tac >> glAbbrs 5 >>
        simp[word_add_n2w, output_buffer_size_def] >>
        simp[GSYM word_add_n2w, sub_common, Once EQ_SYM_EQ] >> strip_tac >>
        simp[word_add_n2w,
             CONV_RULE (PATH_CONV "rlr" (REWR_CONV EQ_SYM_EQ))
                       WORD_ADD_CANCEL_LBARE] >> strip_tac >>
        Q.UNDISCH_THEN ‘s.R 3w ∈ md’ mp_tac >>
        rpt (qpat_x_assum ‘DISJOINT md _’ mp_tac) >>
        simp[DISJOINT_ALT] >>
        disch_then (fn i1 => disch_then (fn i2 => disch_then (fn th =>
          mp_tac (MATCH_MP i1 th) >> mp_tac (MATCH_MP i2 th)))) >>
        simp[startup_code_size_def, heap_start_offset_def, word_add_n2w,
             word_lo_n2w, word_ls_n2w, ffi_code_start_offset_thm,
             length_ag32_ffi_code_def]) >>
  drule_then SUBST1_TAC asm_write_bytearray_avoiding >>
  simp[Abbr‘f’, Abbr‘A’] >> glAbbrs 5 >>
  simp[set_mem_word_def, word_add_n2w, stdin_offset_def,
       asm_write_bytearray_def,
       combinTheory.UPDATE_def, cline_size_def, startup_code_size_def,
       MarshallingTheory.n2w2_def] >>
  simp[sub_common, GSYM word_add_n2w] >> rw[] >>
  Q.UNDISCH_THEN ‘s.R 3w ∈ md’ mp_tac >>
  rpt (qpat_x_assum ‘DISJOINT md _’ mp_tac) >>
  simp[DISJOINT_ALT] >>
  disch_then (fn i1 => disch_then (fn i2 => disch_then (fn th =>
    mp_tac (MATCH_MP i1 th) >> mp_tac (MATCH_MP i2 th)))) >>
  simp[startup_code_size_def, heap_start_offset_def, word_add_n2w,
       word_lo_n2w, word_ls_n2w, ffi_code_start_offset_thm,
       length_ag32_ffi_code_def]
QED

val instn = instn0 (LIST_CONJ [ag32_ffi_get_arg_count_code_def,
                               ag32_ffi_get_arg_count_main_code_def,
                               ag32_ffi_return_code_def])

val ag32_ffi_return_LET = Q.prove(
  ‘ag32_ffi_return (LET f v) = LET (ag32_ffi_return o f) v’,
  simp[]);

val ag32_ffi_get_arg_count_entrypoint_thm =
    EVAL “ag32_ffi_get_arg_count_entrypoint”

val div_lemma = Q.prove(
  ‘0 < c ⇒ (c * x + y) DIV c = x + y DIV c ∧ (c * x) DIV c = x’,
  metis_tac[ADD_DIV_ADD_DIV, MULT_COMM, MULT_DIV]);

val gmw = gmw0 (fn i =>
                   simp0[ffi_code_start_offset_thm] >>
                   insthyp last_x_assum 4 (fn j => 4 * i + j))
val combined = combined0 instn gmw

Theorem ag32_ffi_get_arg_count_code_thm:
   s.R 3w ∉
     { s.PC + n2w k | k | k DIV 4 < LENGTH ag32_ffi_get_arg_count_code } ∧
   (∀k. k < LENGTH ag32_ffi_get_arg_count_code ⇒
      (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_get_arg_count_code))) ∧
   byte_aligned s.PC ∧
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_get_arg_count_entrypoint))
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_get_arg_count s)
Proof
  rw[ffi_code_start_offset_thm, ag32_ffi_get_arg_count_entrypoint_thm] >>
  assume_tac (EVAL “LENGTH ag32_ffi_get_arg_count_code”) >> fs[] >>
  instn 0 >>
  simp0 [ag32_ffi_get_arg_count_def, ag32_ffi_get_arg_count_main_def] >>
  simp0[Once LET_THM] >>
  simp0[ag32_ffi_return_LET, combinTheory.o_ABS_R] >>
  drule_then assume_tac byte_aligned_imp >>
  simp0[ag32_targetProofTheory.Decode_Encode, ag32Theory.Run_def] >>
  ntac 2 (pop_assum kall_tac) >>

  simp0[ffi_code_start_offset_thm] >>
  EVERY (List.tabulate(7, fn j => combined (j + 1))) >>
  simp[] >> irule ag32_ffi_return_code_thm >>
  qmatch_abbrev_tac ‘_ ∧ byte_aligned s8.PC’ >>
  pop_assum mp_tac >>
  simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def,
       ag32Theory.ri2word_def] >>
  strip_tac >>
  ‘s8.PC = s.PC + 32w’ by simp[Abbr‘s8’] >> simp[] >> reverse conj_tac
  >- EVAL_TAC >>
  qx_gen_tac ‘k’ >> strip_tac >>
  first_x_assum
    (qspec_then ‘k + LENGTH ag32_ffi_get_arg_count_main_code’ mp_tac) >>
  simp[EL_APPEND2, ag32_ffi_get_arg_count_code_def] >>
  simp[ag32_ffi_get_arg_count_code_def,
       ag32_ffi_get_arg_count_main_code_def, LEFT_ADD_DISTRIB, word_add_n2w] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [ag32_ffi_return_code_def]) >>
  simp[] >>
  disch_then (SUBST1_TAC o SYM) >>
  EVERY (List.tabulate(8, fn j => glAbbr (8 - j))) >>
  simp[startup_code_size_def] >>
  simp[get_mem_word_def, sub_common] >>
  simp[word_add_n2w] >>
  simp[GSYM word_add_n2w, sub_common] >>
  simp[word_add_n2w] >>
  first_x_assum (fn th =>
    qspec_then `4 * (k + 7) + 3` mp_tac th >>
    EVERY (List.tabulate(5,
     fn j => qspec_then [QUOTE ("4 * (k + 8) + " ^ Int.toString j)]
                        mp_tac th))) >>
  simp[div_lemma] >> simp[LEFT_ADD_DISTRIB, word_add_n2w]
QED

val instn = instn0 ag32_ffi_get_arg_length_setup_code_def

val gmw = gmw0 (fn i =>
                   simp0[ffi_code_start_offset_thm] >>
                   insthyp last_x_assum 4 (fn j => 4 * i + j))
val combined = combined0 instn gmw

Theorem ag32_ffi_get_arg_length_setup_code_thm:
   w2w (n2w (ffi_code_start_offset − 1) : 23 word) ∉
     { s.PC + n2w k | k |
       k DIV 4 < LENGTH ag32_ffi_get_arg_length_setup_code } ∧
   (∀k. k < LENGTH ag32_ffi_get_arg_length_setup_code ⇒
        get_mem_word s.MEM (s.PC + n2w (4 * k)) =
        Encode (EL k ag32_ffi_get_arg_length_setup_code)) ∧
   byte_aligned s.PC ⇒
   ∃k. FUNPOW Next k s = ag32_ffi_get_arg_length_setup s
Proof
  rw[ffi_code_start_offset_thm] >>
  assume_tac (EVAL “LENGTH ag32_ffi_get_arg_length_setup_code”) >> fs[] >>
  instn 0 >>
  simp0[ag32_ffi_get_arg_length_setup_def] >>
  drule_then assume_tac byte_aligned_imp >>
  simp0[ag32_targetProofTheory.Decode_Encode, ag32Theory.Run_def] >>
  ntac 2 (pop_assum kall_tac) >>

  EVERY (List.tabulate(10, fn j => (combined (j + 1)))) >>
  qexists_tac `0` >> simp[]
QED

val ag32_ffi_get_arg_length_loop1_code_def = Define‘
  ag32_ffi_get_arg_length_loop1_code =
    GENLIST (λi. EL (i + 2) ag32_ffi_get_arg_length_loop_code) 4
’;

val instn = instn0
              (CONV_RULE (RAND_CONV EVAL)
                         ag32_ffi_get_arg_length_loop1_code_def)
val combined = combined0 instn gmw

Theorem ag32_ffi_get_arg_length_loop1_code_thm:
   s.MEM (s.R 5w + n2w zoff) = 0w ∧
   (∀k. k < LENGTH ag32_ffi_get_arg_length_loop1_code ⇒
        get_mem_word s.MEM (s.PC + n2w (4 * k)) =
        Encode (EL k ag32_ffi_get_arg_length_loop1_code)) ∧
   byte_aligned s.PC ⇒
   ∃k. FUNPOW Next k s = ag32_ffi_get_arg_length_loop1 s
Proof
  assume_tac (EVAL “LENGTH ag32_ffi_get_arg_length_loop1_code”) >>
  map_every qid_spec_tac [‘s’, ‘zoff’] >> Induct >> simp[] >>
  rw[] >> instn 0 >> simp0[Once ag32_ffi_get_arg_length_loop1_def] >>
  drule_then assume_tac byte_aligned_imp >>
  simp0[ag32_targetProofTheory.Decode_Encode, ag32Theory.Run_def]
  >- ((* base case *)
      ‘(∀n. s.MEM (n2w n + s.R 5w) ≠ 0w) = F’
         by (simp[] >> qexists_tac `0` >> simp[]) >>
      pop_assum SUBST1_TAC >> simp0[] >>
      combined 1 >> combined 2 >> combined 3 >>
      qexists_tac `0` >> simp[] >>
      simp[Abbr‘s3’, Abbr‘s2’, Abbr‘s1’, combinTheory.UPDATE_def]) >>
  ‘(∀n. s.MEM (n2w n + s.R 5w) ≠ 0w) = F’
     by (simp[] >> qexists_tac `SUC zoff` >> simp[]) >>
  pop_assum SUBST1_TAC >> simp0[] >>
  EVERY (List.tabulate(3, fn j => combined (j + 1))) >>
  Cases_on ‘s3.R 8w = 0w’ >> simp0[] >- (qexists_tac `0` >> simp[]) >>
  rnwc_next 4 >> rfs[] >>
  first_x_assum irule >> glAbbrs 4 >> fs[ADD1, GSYM word_add_n2w]
QED

val loop_code_def' = Q.prove(
  ‘ag32_ffi_get_arg_length_loop_code =
     TAKE 2 ag32_ffi_get_arg_length_loop_code ++
     ag32_ffi_get_arg_length_loop1_code ++
     DROP 6 ag32_ffi_get_arg_length_loop_code’,
  EVAL_TAC)
  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                                     [ag32_ffi_get_arg_length_loop_code_def]))



val instn = instn0 loop_code_def'
val combined = combined0 instn gmw

val has_n_args_def = Define‘
  (has_n_args mem a 0 ⇔ T) ∧
  (has_n_args (mem : word32 -> word8) a (SUC n) ⇔
     ∃off. mem (a + n2w off) = 0w ∧
           (∀i. i < off ⇒ mem (a + n2w i) ≠ 0w) ∧
           has_n_args mem (a + n2w off + 1w) n)
’;

Theorem ag32_ffi_get_arg_length_loop_code_thm:
   has_n_args s.MEM (s.R 5w) argc ∧ w2n (s.R 6w) ≤ argc ∧
   (∀k. k < LENGTH ag32_ffi_get_arg_length_loop_code ⇒
        get_mem_word s.MEM (s.PC + n2w (4 * k)) =
        Encode (EL k ag32_ffi_get_arg_length_loop_code)) ∧
   byte_aligned s.PC ⇒
   ∃k. FUNPOW Next k s = ag32_ffi_get_arg_length_loop s
Proof
  ‘∃cnt. w2n (s.R 6w) = cnt’ by simp[] >>
  pop_assum mp_tac >> map_every qid_spec_tac [‘argc’, ‘s’, ‘cnt’] >> Induct >>
  rw[] >>
  assume_tac (EVAL “LENGTH ag32_ffi_get_arg_length_loop_code”) >> fs[] >>
  instn 0 >>
  simp0[Once ag32_ffi_get_arg_length_loop_def] >>
  drule_then assume_tac byte_aligned_imp >>
  simp0[ag32_targetProofTheory.Decode_Encode, ag32Theory.Run_def] >>
  ntac 2 (pop_assum kall_tac) >- (qexists_tac `0` >> simp[]) >>
  ‘s.R 6w ≠ 0w’ by (strip_tac >> fs[]) >> simp0[] >>
  combined 1 >> rev_full_simp_tac (srw_ss()) [] >>
  rnwc_next 2 >> spc 2 >>
  qmatch_abbrev_tac ‘∃k. FUNPOW Next k s2 = LET _ s3’ >>
  ‘∃c0. argc = SUC c0’ by (Cases_on ‘argc’ >> fs[]) >> pop_assum SUBST_ALL_TAC>>
  full_simp_tac (srw_ss()) [has_n_args_def] >>
  rename [‘has_n_args s.MEM (n2w zoff + s.R 5w + 1w) c0’] >>
  ‘s2.MEM (s2.R 5w + n2w zoff) = 0w’ by (glAbbrs 2 >> goal_assum drule)>>
  drule ag32_ffi_get_arg_length_loop1_code_thm >> impl_tac
  >- (qmatch_abbrev_tac ‘_ ∧ byte_aligned s2.PC’ >> reverse conj_tac
      >- (glAbbrs 2 >> irule byte_aligned_add >> simp[] >> EVAL_TAC) >>
      qx_gen_tac `k` >>
      assume_tac (EVAL “LENGTH ag32_ffi_get_arg_length_loop1_code”) >> rw[] >>
      first_x_assum (qspec_then ‘k + 2’ mp_tac) >>
      simp[LEFT_ADD_DISTRIB, word_add_n2w, loop_code_def', EL_CONS, PRE_SUB1,
           EL_APPEND1] >>
      disch_then (SUBST1_TAC o SYM) >> glAbbrs 2 >> simp[GSYM word_add_n2w]) >>
  disch_then (qx_choose_then ‘k2’ assume_tac) >>
  Q.REFINE_EXISTS_TAC ‘k + k2’ >> simp0[FUNPOW_ADD] >> simp0[Once LET_THM] >>
  rev_full_simp_tac (srw_ss()) [] >>
  ‘(OLEAST n. s2.MEM (s2.R 5w + n2w n) = 0w) = SOME zoff’
    by (glAbbrs 2 >> DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[] >>
        conj_tac >- (goal_assum drule) >> rw[] >>
        ‘¬(zoff < n) ∧ ¬(n < zoff)’ suffices_by simp[] >> metis_tac[]) >>
  qpat_x_assum ‘Abbrev (s3 = _)’ mp_tac >>
  simp0[ag32_ffi_get_arg_length_loop1_thm] >> strip_tac >>
  rename [‘FUNPOW Next k2 s2 = s6’] >> spc 6 >> instn 6 >> gmw 6 >>
  simp0[EL_APPEND1, EL_APPEND2, ag32_ffi_get_arg_length_loop1_code_def] >>
  combined 7 >>
  simp0[EL_APPEND1, EL_APPEND2, ag32_ffi_get_arg_length_loop1_code_def] >>
  rnwc_next 8 >> first_x_assum irule >> glAbbrs 8 >> reverse conj_tac
  >- (goal_assum drule >> simp[GSYM word_add_n2w]) >>
  Q.ISPEC_THEN ‘s.R 6w’ mp_tac ranged_word_nchotomy >> strip_tac >> fs[] >>
  simp[WORD_LITERAL_ADD]
QED

(* ag32_ffi_get_arg_length *)

(*
val (ag32_ffi_get_arg_length_setup_SPEC,
     ag32_ffi_get_arg_length_setup_decomp_def) = ag32_decompile
     ag32_ffi_get_arg_length_setup_code_def

val (ag32_ffi_get_arg_length_loop_SPEC,
     ag32_ffi_get_arg_length_loop_decomp_def) = ag32_decompile
     ag32_ffi_get_arg_length_loop_code_def
*)

val (ag32_ffi_get_arg_length_store_SPEC,
     ag32_ffi_get_arg_length_store_decomp_def) = ag32_decompile
     ag32_ffi_get_arg_length_store_code_def

Theorem ag32_ffi_get_arg_length_store_decomp_thm:
   FST(ag32_ffi_get_arg_length_store_decomp (s,md)) = ag32_ffi_get_arg_length_store s
Proof
  rw[ag32_ffi_get_arg_length_store_decomp_def]
  \\ rw[ag32_ffi_get_arg_length_store_def]
QED

val ag32_ffi_get_arg_length_store_FUNPOW_Next = let
  val th = ag32_ffi_get_arg_length_store_SPEC
  val code_def = ag32_ffi_get_arg_length_store_code_def
  in FUNPOW_Next_from_SPEC code_def th end;

(*
val ag32_ffi_get_arg_length_SPEC =
  SPEC_COMPOSE_RULE [ag32_ffi_get_arg_length_setup_SPEC,
                     ag32_ffi_get_arg_length_loop_SPEC,
                     ag32_ffi_get_arg_length_store_SPEC,
                     ag32_ffi_return_SPEC]

val ag32_ffi_get_arg_length_FUNPOW_Next = let
  val th = ag32_ffi_get_arg_length_SPEC
  val code_def = ag32_ffi_get_arg_length_code_def
                 |> SIMP_RULE std_ss [ag32_ffi_get_arg_length_setup_code_def,
                                      ag32_ffi_get_arg_length_loop_code_def,
                                      ag32_ffi_get_arg_length_store_code_def,
                                      ag32_ffi_return_code_def,APPEND]
  in FUNPOW_Next_from_SPEC code_def th end;

Theorem ag32_ffi_get_arg_length_setup_decomp_thm:
   FST(ag32_ffi_get_arg_length_setup_decomp (s,md)) = ag32_ffi_get_arg_length_setup s
Proof
  rw[ag32_ffi_get_arg_length_setup_decomp_def]
  \\ rw[ag32_ffi_get_arg_length_setup_def]
QED

Theorem ag32_ffi_get_arg_length_loop_decomp_thm
  `∀s. FST(ag32_ffi_get_arg_length_loop_decomp (s,md)) = ag32_ffi_get_arg_length_loop s`
  (recInduct ag32_ffi_get_arg_length_loop_ind
  \\ rw[]
  \\ rw[Once ag32_ffi_get_arg_length_loop_decomp_def]
  \\ rw[Once ag32_ffi_get_arg_length_loop_decomp_def]
  >- (
    pop_assum mp_tac
    \\ simp[Once ag32Theory.dfn'JumpIfZero_def]
    \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
    \\ strip_tac \\ fs[]
    \\ rw[Once ag32_ffi_get_arg_length_loop_def]
    \\ simp[Once ag32Theory.dfn'JumpIfZero_def]
    \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
    \\ simp[Once ag32Theory.dfn'JumpIfNotZero_def]
    \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
    \\ simp[Once ag32Theory.dfn'JumpIfZero_def]
    \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
*)

Theorem ag32_ffi_get_arg_length_code_thm:
   (∀k. k < LENGTH ag32_ffi_get_arg_length_code ⇒
      (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_get_arg_length_code))) ∧
   byte_aligned s.PC ∧
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_get_arg_length_entrypoint)) ∧
   bytes_in_memory (s.R 3w) [l0; l1] s.MEM md ∧
   n2w (ffi_code_start_offset -1) ∉ md ∧
   (∀j. j < 4 * LENGTH ag32_ffi_get_arg_length_code ⇒
        n2w (ffi_code_start_offset + ag32_ffi_get_arg_length_entrypoint + j)
        ∉ md) ∧
   w2n l0 + 256 * w2n l1 ≤ cline_size ∧
   LENGTH (SND (get_mem_arg ((n2w(ffi_code_start_offset - 1) =+ n2w(THE(ALOOKUP FFI_codes "get_arg_length"))) s.MEM)
     (n2w (startup_code_size + 4)) (w2n l0 + 256 * w2n l1))) < dimword(:32) ∧
   has_n_args ((n2w(ffi_code_start_offset - 1) =+ n2w(THE(ALOOKUP FFI_codes "get_arg_length"))) s.MEM)
     (n2w (startup_code_size + 4)) (w2n l0 + (256 * w2n l1) + 1)
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_get_arg_length s)
Proof
  rw[ag32_ffi_get_arg_length_def]
  \\ mp_tac ag32_ffi_get_arg_length_setup_code_thm
  \\ impl_tac
  >- (
    simp[]
    \\ conj_tac
    >- (
      EVAL_TAC \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ fs[DIV_LT_X] )
    \\ fs[]
    \\ rw[]
    \\ fs[ag32_ffi_get_arg_length_code_def]
    \\ last_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- simp[]
    \\ disch_then kall_tac
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[] )
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_length_loop s1`
  \\ qspec_then`s1`mp_tac(Q.GENL[`s`,`argc`]ag32_ffi_get_arg_length_loop_code_thm)
  \\ drule ag32_ffi_get_arg_length_setup_thm
  \\ simp[] \\ strip_tac
  \\ qunabbrev_tac`s1`
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_get_arg_length_setup s = s1`
  \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`has_n_args _ _ argc`
  \\ disch_then(qspec_then`argc`mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ DEP_REWRITE_TAC[LESS_MOD]
    \\ simp[]
    \\ conj_tac
    >- (
      simp[Abbr`argc`]
      \\ Cases_on`l0` \\ Cases_on`l1` \\ fs[] )
    \\ reverse conj_tac >- EVAL_TAC
    \\ qx_gen_tac`j` \\ strip_tac
    \\ last_x_assum(qspec_then`j + LENGTH ag32_ffi_get_arg_length_setup_code`mp_tac)
    \\ simp[ag32_ffi_get_arg_length_code_def, LEFT_ADD_DISTRIB, word_add_n2w]
    \\ strip_tac
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ simp[EL_APPEND2, EL_APPEND1]
    \\ qpat_x_assum`j < _`mp_tac
    \\ EVAL_TAC \\ simp[])
  \\ strip_tac
  \\ qspecl_then[`s1`,`argc-1`]mp_tac(Q.GENL[`s`,`index`]ag32_ffi_get_arg_length_loop_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s1`]
    \\ simp[APPLY_UPDATE_THM]
    \\ DEP_REWRITE_TAC[LESS_MOD]
    \\ fs[Abbr`argc`, EVAL``cline_size``]
    \\ qhdtm_x_assum`has_n_args`mp_tac
    \\ qmatch_goalsub_abbrev_tac`has_n_args _ _ index1`
    \\ qmatch_asmsub_abbrev_tac`index ≤ 2048`
    \\ `index1 = SUC index` by simp[Abbr`index1`, Abbr`index`]
    \\ simp[has_n_args_def, APPLY_UPDATE_THM]
    \\ strip_tac
    \\ qexists_tac`off`
    \\ simp[] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_get_arg_length_loop _ = s2`
  \\ simp[]
  \\ (ag32_ffi_get_arg_length_store_FUNPOW_Next
    |> SIMP_RULE std_ss [ag32_ffi_get_arg_length_store_decomp_thm]
    |> Q.GENL[`s`,`md`]
    |> qspec_then`s2`mp_tac)
  \\ simp[EVAL``LENGTH ag32_ffi_get_arg_length_store_code``]
  \\ simp[ag32_ffi_get_arg_length_store_decomp_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.ri2word_def, ag32Theory.incPC_def,
          ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def,
          ag32Theory.dfn'Shift_def, ag32Theory.shift_def, APPLY_UPDATE_THM]
  \\ simp[ag32_progTheory.mem_unchanged_def, APPLY_UPDATE_THM]
  \\ disch_then(qspec_then`UNIV DIFF {s2.PC + n2w k | k | k DIV 4 < 5}`mp_tac)
  \\ simp[DIV_LT_X, IN_DISJOINT, DISJ_EQ_IMP]
  \\ impl_tac
  >- (
    simp[Abbr`s2`, APPLY_UPDATE_THM]
    \\ pop_assum kall_tac
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ pop_assum kall_tac
    \\ qpat_x_assum`_ = _`kall_tac
    \\ rewrite_tac[CONJ_ASSOC]
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[PULL_EXISTS]
    \\ reverse conj_tac
    >- (
      qx_gen_tac`j`
      \\ strip_tac
      \\ last_x_assum(qspec_then`j + LENGTH ag32_ffi_get_arg_length_setup_code + LENGTH ag32_ffi_get_arg_length_loop_code`mp_tac)
      \\ simp[ag32_ffi_get_arg_length_code_def, LEFT_ADD_DISTRIB, word_add_n2w]
      \\ fs[EVAL``LENGTH ag32_ffi_get_arg_length_store_code``]
      \\ strip_tac
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ simp[EL_APPEND2, EL_APPEND1]
      \\ qpat_x_assum`j < _`mp_tac
      \\ fs[EVAL``LENGTH ag32_ffi_get_arg_length_store_code``, EL_APPEND1, EL_APPEND2]
      \\ EVAL_TAC \\ simp[])
    \\ simp[GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM]
    \\ qx_gen_tac`j` \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`s.R 3w = r3`
    \\ `s.R 3w ∈ md` by fs[bytes_in_memory_def]
    \\ fs[word_add_n2w]
    \\ fs(map EVAL [``LENGTH ag32_ffi_get_arg_length_loop_code``,``LENGTH ag32_ffi_get_arg_length_setup_code``])
    \\ fs(map EVAL [``ag32_ffi_get_arg_length_entrypoint``,``ffi_code_start_offset``])
    \\ fs[EVAL``LENGTH ag32_ffi_get_arg_length_store_code``]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      fs[Abbr`r3`]
      \\ first_x_assum(qspec_then`j + 4 * (LENGTH ag32_ffi_get_arg_length_setup_code + LENGTH ag32_ffi_get_arg_length_loop_code)`mp_tac)
      \\ fs(map EVAL [``LENGTH ag32_ffi_get_arg_length_loop_code``,``LENGTH ag32_ffi_get_arg_length_setup_code``])
      \\ simp[EVAL``LENGTH ag32_ffi_get_arg_length_code``] )
    \\ IF_CASES_TAC \\ fs[]
    \\ fs[Abbr`r3`]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w] \\ rfs[]
    \\ Cases_on`n = dimword(:32) -1` \\ fs[]
    \\ first_x_assum(qspec_then`j + 4 * (LENGTH ag32_ffi_get_arg_length_setup_code + LENGTH ag32_ffi_get_arg_length_loop_code) -1`mp_tac)
    \\ fs(map EVAL [``LENGTH ag32_ffi_get_arg_length_loop_code``,``LENGTH ag32_ffi_get_arg_length_setup_code``])
    \\ simp[EVAL``LENGTH ag32_ffi_get_arg_length_code``]
    \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`n + 1 = j + z`
    \\ `n = j + z - 1` by fs[]
    \\ fs[Abbr`z`])
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_return s3`
  \\ qspec_then`s3`mp_tac(Q.GEN `s`ag32_ffi_return_code_thm)
  \\ impl_tac
  >- (
    qmatch_asmsub_abbrev_tac`4w =+ n2w (n + 1)`
    \\ qspec_then`s2`mp_tac(Q.GENL[`s`]ag32_ffi_get_arg_length_store_thm)
    \\ impl_tac
    >- (
      simp[Abbr`s2`, APPLY_UPDATE_THM]
      \\ simp[Abbr`n`, Abbr`argc`]
      \\ simp[Abbr`s1`, APPLY_UPDATE_THM] )
    \\ strip_tac \\ fs[]
    \\ pop_assum kall_tac
    \\ simp[Abbr`s3`]
    \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ reverse conj_tac >- EVAL_TAC
    \\ qx_gen_tac`j`
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ strip_tac
    \\ last_x_assum(qspec_then`j + (LENGTH ag32_ffi_get_arg_length_setup_code +
                                    LENGTH ag32_ffi_get_arg_length_loop_code +
                                    LENGTH ag32_ffi_get_arg_length_store_code)` mp_tac)
    \\ simp[ag32_ffi_get_arg_length_code_def]
    \\ simp[EL_APPEND1, EL_APPEND2]
    \\ disch_then(SUBST1_TAC o SYM)
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ simp[word_add_n2w, LEFT_ADD_DISTRIB]
    \\ EVAL_TAC
    \\ pop_assum mp_tac
    \\ EVAL_TAC
    \\ simp[]
    \\ strip_tac
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w] \\ rfs[]
    \\ fs(map EVAL [``LENGTH ag32_ffi_get_arg_length_code``])
    \\ fs(map EVAL [``ag32_ffi_get_arg_length_entrypoint``,``ffi_code_start_offset``])
    \\ Cases_on`n = dimword(:32) -1` \\ fs[]
    \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[]
    \\ TRY (
      qmatch_asmsub_abbrev_tac`z = n + 1`
      \\ `n = z - 1` by simp[]
      \\ fs[Abbr`z`] \\ rveq \\ fs[] )
    \\ qmatch_asmsub_abbrev_tac`s.R 3w = n2w (4 * j + z)`
    \\ qmatch_asmsub_abbrev_tac`n2w (_ + y) ∉ md`
    \\ first_x_assum(qspec_then`4 * j + z - y`mp_tac)
    \\ simp[Abbr`z`, Abbr`y`]
    \\ fs[bytes_in_memory_def])
  \\ strip_tac
  \\ pop_assum(SUBST1_TAC o SYM)
  \\ qpat_x_assum`_ = s3`(SUBST1_TAC o SYM)
  \\ fs[]
  \\ qpat_x_assum`FUNPOW _ _ _ = s2`(SUBST1_TAC o SYM)
  \\ qpat_x_assum`FUNPOW _ _ _ = s1`(SUBST1_TAC o SYM)
  \\ simp_tac(srw_ss())[GSYM FUNPOW_ADD]
  \\ metis_tac[]
QED

(* ag32_ffi_get_arg *)

val (ag32_ffi_get_arg_setup_SPEC,
     ag32_ffi_get_arg_setup_decomp_def) = ag32_decompile
     ag32_ffi_get_arg_setup_code_def

val (ag32_ffi_get_arg_find_SPEC,
     ag32_ffi_get_arg_find_decomp_def) = ag32_decompile
     ag32_ffi_get_arg_find_code_def

val (ag32_ffi_get_arg_store_SPEC,
     ag32_ffi_get_arg_store_decomp_def) = ag32_decompile
     ag32_ffi_get_arg_store_code_def

val ag32_ffi_get_arg_SPEC =
  SPEC_COMPOSE_RULE [ag32_ffi_get_arg_setup_SPEC,
                     ag32_ffi_get_arg_find_SPEC,
                     ag32_ffi_get_arg_store_SPEC,
                     ag32_ffi_return_SPEC]

val ag32_ffi_get_arg_FUNPOW_Next = let
  val th = ag32_ffi_get_arg_SPEC
  val code_def = ag32_ffi_get_arg_code_def
                 |> SIMP_RULE std_ss [ag32_ffi_get_arg_setup_code_def,
                                      ag32_ffi_get_arg_find_code_def,
                                      ag32_ffi_get_arg_store_code_def,
                                      ag32_ffi_return_code_def,APPEND]
  in FUNPOW_Next_from_SPEC code_def th end;

Theorem ag32_ffi_get_arg_setup_decomp_thm:
   FST(ag32_ffi_get_arg_setup_decomp (s,md)) = ag32_ffi_get_arg_setup s
Proof
  rw[ag32_ffi_get_arg_setup_decomp_def]
  \\ rw[ag32_ffi_get_arg_setup_def]
QED

Theorem ag32_ffi_get_arg_find_decomp1_thm:
   ∀s.
    (∃n. s.MEM (s.R 5w + n2w n) = 0w) ⇒
    (ag32_ffi_get_arg_find_decomp1 s = ag32_ffi_get_arg_find1 s)
Proof
  recInduct ag32_ffi_get_arg_find1_ind
  \\ rw[]
  \\ rw[Once ag32_ffi_get_arg_find_decomp_def] \\ fs[]
  >- (
    pop_assum mp_tac
    \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.incPC_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def, APPLY_UPDATE_THM,
            ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'JumpIfNotZero_def]
    \\ simp[Once ag32_ffi_get_arg_find1_def]
    \\ IF_CASES_TAC
    >- (
      first_x_assum(qspec_then`0`mp_tac)
      \\ simp[]
      \\ Cases_on`s.MEM (s.R 5w)`
      \\ simp[w2w_n2w, bitTheory.BITS_ZERO3] \\ fs[] )
    \\ strip_tac
    \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.incPC_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def, APPLY_UPDATE_THM,
            ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'JumpIfNotZero_def] )
  \\ pop_assum mp_tac
  \\ fs[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.incPC_def,
        ag32Theory.ri2word_def, ag32Theory.ALU_def, APPLY_UPDATE_THM,
        ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'JumpIfNotZero_def]
  \\ strip_tac
  \\ simp[Once ag32_ffi_get_arg_find1_def]
  \\ fs[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.incPC_def,
        ag32Theory.ri2word_def, ag32Theory.ALU_def, APPLY_UPDATE_THM,
        ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'JumpIfNotZero_def]
  \\ fs[AND_IMP_INTRO]
  \\ IF_CASES_TAC \\ fs[]
  \\ first_x_assum irule
  \\ qexists_tac`dimword(:32)-1 + n`
  \\ simp[]
  \\ Cases_on`s.R 5w` \\ fs[word_add_n2w]
  \\ last_x_assum(SUBST1_TAC o SYM)
  \\ AP_TERM_TAC
  \\ simp[]
QED

Theorem ag32_ffi_get_arg_find_decomp_thm:
   ∀s. (∃n. s.MEM (s.R 5w + n2w n) = 0w) ⇒ (FST(ag32_ffi_get_arg_find_decomp (s,md)) = ag32_ffi_get_arg_find s)
Proof
  recInduct ag32_ffi_get_arg_find_ind
  \\ rw[]
  \\ rw[Once ag32_ffi_get_arg_find_decomp_def]
  >- rw[Once ag32_ffi_get_arg_find_def]
  \\ fs[]
  \\ simp[Once ag32_ffi_get_arg_find_def]
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- (
    simp[ag32Theory.dfn'JumpIfZero_def
        ,ag32Theory.dfn'Normal_def, ag32Theory.norm_def
        ,ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
    \\ simp[ag32_ffi_get_arg_find1_thm]
    \\ simp[whileTheory.OLEAST_def]
    \\ IF_CASES_TAC \\ fs[]
    \\ simp[APPLY_UPDATE_THM]
    \\ simp[word_add_n2w]
    \\ qmatch_goalsub_abbrev_tac`n2w (_ + (x + 1))`
    \\ `x ≤ n`
    by (
      simp[Abbr`x`]
      \\ numLib.LEAST_ELIM_TAC
      \\ conj_tac >- metis_tac[]
      \\ rw[]
      \\ CCONTR_TAC \\ fs[NOT_LESS_EQUAL] )
    \\ qexists_tac`n + dimword(:32) -1 - x`
    \\ last_x_assum(SUBST1_TAC o SYM)
    \\ AP_TERM_TAC
    \\ simp[] )
  \\ disch_then(SUBST1_TAC o SYM)
  \\ DEP_REWRITE_TAC[ag32_ffi_get_arg_find_decomp1_thm]
  \\ simp[ag32Theory.dfn'JumpIfZero_def]
  \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
  \\ metis_tac[]
QED

Theorem ag32_ffi_get_arg_store_decomp_thm:
   ∀s.
    (∃n. s.MEM (s.R 5w + n2w n) = 0w ∧
         ∀i. i ≤ n ⇒ s.R 3w ≠ s.R 5w + n2w i) ⇒
    FST(ag32_ffi_get_arg_store_decomp (s,md)) = ag32_ffi_get_arg_store s
Proof
  recInduct ag32_ffi_get_arg_store_ind
  \\ rw[]
  \\ rw[Once ag32_ffi_get_arg_store_decomp_def]
  >- (
    rw[Once ag32_ffi_get_arg_store_def]
    \\ fs[DISJ_EQ_IMP]
    \\ first_x_assum drule
    \\ rw[] \\ res_tac \\ fs[] )
  \\ fs[]
  \\ simp[Once ag32_ffi_get_arg_store_def]
  \\ last_x_assum mp_tac
  \\ impl_tac
  >- metis_tac[]
  \\ impl_tac
  >- (
    fs[ag32Theory.dfn'JumpIfZero_def
        ,ag32Theory.dfn'Normal_def, ag32Theory.norm_def
        ,ag32Theory.dfn'StoreMEMByte_def, ag32Theory.dfn'LoadMEMByte_def
        ,APPLY_UPDATE_THM
        ,ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
    \\ qexists_tac`n-1`
    \\ reverse conj_tac
    >- rw[]
    \\ Cases_on`n` \\ fs[] \\ rfs[]
    \\ fs[ADD1, GSYM word_add_n2w]
    \\ rw[]
    \\ `F` suffices_by rw[]
    \\ pop_assum mp_tac
    \\ rw[]
    \\ Cases_on`s.R 5w` \\ fs[word_add_n2w, LESS_OR_EQ]
    \\ fsrw_tac[DNF_ss][] \\ fs[] )
  \\ disch_then(SUBST1_TAC o SYM)
  \\ rw[]
  \\ fs[DISJ_EQ_IMP]
  \\ first_x_assum drule
  \\ strip_tac
  \\ first_x_assum drule
  \\ simp[]
QED

Theorem ag32_ffi_get_arg_find_decomp1_pre':
   ∀off s.
     s.MEM (s.R 5w + n2w off) = 0w ⇒ ag32_ffi_get_arg_find_decomp1_pre s
Proof
  Induct >> simp[Once ag32_ffi_get_arg_find_decomp_def] >>
  simp[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,
       ag32Theory.ALU_def, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
       ag32Theory.incPC_def, ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'JumpIfNotZero_def,
       combinTheory.UPDATE_def] >>
  qx_gen_tac ‘s’ >> strip_tac >>
  Cases_on ‘w2w (s.MEM (s.R 5w)) = (0w : word32)’ >> simp[] >>
  first_x_assum irule >> simp[] >> fs[ADD1, GSYM word_add_n2w]
QED

Theorem ag32_ffi_get_arg_find_decomp_pre':
   ∀c md s.
     has_n_args s.MEM (s.R 5w) c ∧ w2n (s.R 6w) ≤ c ⇒
     ag32_ffi_get_arg_find_decomp_pre (s,md)
Proof
  Induct >> simp[Once ag32_ffi_get_arg_find_decomp_def] >>
  simp[has_n_args_def, PULL_EXISTS] >> rpt strip_tac >>
  Cases_on ‘s.R 6w = 0w’ >> simp[] >>
  simp[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,
       ag32Theory.ALU_def, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
       ag32Theory.incPC_def] >>
  reverse conj_tac
  >- (irule ag32_ffi_get_arg_find_decomp1_pre' >> simp[] >> goal_assum drule) >>
  first_x_assum irule >>
  qmatch_goalsub_abbrev_tac ‘ag32_ffi_get_arg_find_decomp1 s1’ >>
  ‘s1.MEM (s1.R 5w + n2w off) = 0w’ by simp[Abbr‘s1’] >>
  drule_then assume_tac
    (SIMP_RULE bool_ss [PULL_EXISTS] ag32_ffi_get_arg_find_decomp1_thm)>>
  simp[] >>
  ‘(OLEAST n. s1.MEM (s1.R 5w + n2w n) = 0w) = SOME off’
    by (DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >> simp[Abbr`s1`] >>
        conj_tac >- goal_assum drule >> qx_gen_tac `n` >> strip_tac >>
        ‘¬(n < off) ∧ ¬(off < n)’ suffices_by simp[] >> metis_tac[]) >>
   simp[ag32_ffi_get_arg_find1_thm, combinTheory.UPDATE_def] >>
   reverse conj_tac >- simp[Abbr‘s1’, GSYM word_add_n2w] >>
   simp[Abbr‘s1’] >>
   Q.ISPEC_THEN ‘s.R 6w’ mp_tac ranged_word_nchotomy >> rw[] >> fs[] >>
   simp[WORD_LITERAL_ADD]
QED

Theorem SND_ag32_ffi_get_arg_find_decomp:
   ∀p. (∃n. (FST p).MEM ((FST p).R 5w + n2w n) = 0w) ⇒ SND (ag32_ffi_get_arg_find_decomp p) = SND p
Proof
  simp[FORALL_PROD]
  \\ recInduct ag32_ffi_get_arg_find_ind
  \\ rw[]
  \\ rw[Once ag32_ffi_get_arg_find_decomp_def]
  \\ fs[]
  \\ DEP_REWRITE_TAC[ag32_ffi_get_arg_find_decomp1_thm]
  \\ conj_tac
  >- (
    simp[ag32Theory.dfn'JumpIfZero_def]
    \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
    \\ metis_tac[] )
  \\ first_x_assum irule
  \\ simp[ag32Theory.dfn'JumpIfZero_def
      ,ag32Theory.dfn'Normal_def, ag32Theory.norm_def
      ,ag32Theory.ALU_def, ag32Theory.ri2word_def, ag32Theory.incPC_def]
  \\ simp[ag32_ffi_get_arg_find1_thm]
  \\ simp[whileTheory.OLEAST_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ simp[APPLY_UPDATE_THM]
  \\ simp[word_add_n2w]
  \\ qmatch_goalsub_abbrev_tac`n2w (_ + (x + 1))`
  \\ `x ≤ n`
  by (
    simp[Abbr`x`]
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ rw[]
    \\ CCONTR_TAC \\ fs[NOT_LESS_EQUAL] )
  \\ qexists_tac`n + dimword(:32) -1 - x`
  \\ last_x_assum(SUBST1_TAC o SYM)
  \\ AP_TERM_TAC
  \\ simp[]
QED

val ag32_ffi_get_arg_setup_decomp_thm' = Q.prove(
  ‘ag32_ffi_get_arg_setup_decomp (s,md) = (ag32_ffi_get_arg_setup s, md)’,
  Cases_on ‘ag32_ffi_get_arg_setup_decomp (s,md)’ >> simp[] >>
  mp_tac ag32_ffi_get_arg_setup_decomp_thm >> simp[] >>
  fs[ag32_ffi_get_arg_setup_decomp_def]);

val ag32_ffi_get_arg_setup_decomp_pre' =
    let
      open ag32Theory
    in
      (SIMP_CONV (srw_ss()) [ag32_ffi_get_arg_setup_decomp_def, LET_THM,
                             dfn'StoreMEMByte_def, FFI_codes_def,
                             ri2word_def, dfn'LoadConstant_def,
                             incPC_def, ffi_code_start_offset_thm,
                             combinTheory.UPDATE_def,
                             ag32_progTheory.mem_unchanged_def] THENC
       SIMP_CONV (bool_ss ++ COND_elim_ss) [
         CONV_RULE EVAL
          (ASSUME “n2w (THE (ALOOKUP FFI_codes "get_arg") +
                        ffi_code_start_offset - 4) ∈ md : word32 set”)])
        “ag32_ffi_get_arg_setup_decomp_pre(s,md)” |> EQT_ELIM |> DISCH_ALL
    end

Theorem ag32_ffi_get_arg_store_decomp_pre':
   ∀n md s.
     (s.MEM (s.R 5w + n2w n) = 0w) ∧
     (∀i. i ≤ n ⇒ s.R 3w ≠ s.R 5w + n2w i) ∧
     (∀i. i ≤ n ⇒ s.R 3w + n2w i ∈ md)
     ⇒
     ag32_ffi_get_arg_store_decomp_pre (s,md)
Proof
  Induct >> simp[Once ag32_ffi_get_arg_store_decomp_def]
  >- (
    rw[ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def,
       APPLY_UPDATE_THM, ag32Theory.ri2word_def] )
  \\ rw[]
  \\ rw[ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def,
        APPLY_UPDATE_THM, ag32Theory.ri2word_def]
  \\ qmatch_goalsub_abbrev_tac`zz  ∨ _`
  \\ Cases_on`zz` \\ simp[]
  \\ fs[markerTheory.Abbrev_def]
  \\ simp[ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def,
          ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def,
          ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
          ag32Theory.dfn'StoreMEMByte_def,
          APPLY_UPDATE_THM, ag32Theory.ri2word_def]
  \\ reverse conj_tac
  >- (
    simp[ag32_progTheory.mem_unchanged_def]
    \\ rw[APPLY_UPDATE_THM] \\ fs[]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[])
  \\ first_x_assum irule
  \\ simp[APPLY_UPDATE_THM]
  \\ conj_tac
  >- (
    rw[]
    \\ first_x_assum(qspec_then`SUC i`mp_tac)
    \\ simp[GSYM word_add_n2w, ADD1] )
  \\ fs[ADD1, GSYM word_add_n2w]
  \\ rw[]
  \\ last_x_assum(qspec_then`n+1`mp_tac)
  \\ simp[GSYM word_add_n2w]
QED

Theorem ag32_ffi_get_arg_code_thm:
   (∀k. k < LENGTH ag32_ffi_get_arg_code ⇒
      (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_get_arg_code))) ∧
   byte_aligned s.PC ∧
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_get_arg_entrypoint)) ∧
   bytes_in_memory (s.R 3w) [l0; l1] s.MEM md ∧
   n2w (ffi_code_start_offset - 1) ∉ md ∧
   256 * w2n l1 + w2n l0 ≤ cline_size ∧
   (let m1 = ((n2w (ffi_code_start_offset - 1) =+ (n2w (THE (ALOOKUP FFI_codes "get_arg")))) s.MEM) in
    let a = (n2w (startup_code_size + 4)) in
    let index = (256 * w2n l1 + w2n l0) in
    let start = if 0 < index then FST (get_mem_arg m1 a (index-1)) + 1w else a in
    has_n_args m1 a (SUC index) ∧
    ∃n. m1 (start + n2w n) = 0w ∧
        (∀i. i ≤ n ⇒ s.R 3w ≠ start + n2w i) ∧
        (∀i. i ≤ n ⇒ s.R 3w + n2w i ∉ {s.PC + n2w k | k | k < 4 * LENGTH ag32_ffi_get_arg_code }))
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_get_arg s)
Proof
  simp[ag32_ffi_get_arg_def]
  \\ strip_tac
  \\ qabbrev_tac`fmd = COMPL {s.PC + n2w k | k | k < 4 * LENGTH ag32_ffi_get_arg_code }`
  \\ qspec_then`fmd`mp_tac(GSYM (Q.GEN`md`ag32_ffi_get_arg_setup_decomp_thm))
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_find s1`
  \\ qspecl_then[`fmd`,`s1`]mp_tac (Q.GEN`md`ag32_ffi_get_arg_find_decomp_thm)
  \\ drule (GEN_ALL ag32_ffi_get_arg_setup_thm)
  \\ impl_tac >- simp[]
  \\ strip_tac
  \\ qpat_x_assum`_ = s1`SUBST_ALL_TAC
  \\ qunabbrev_tac`s1`
  \\ qmatch_asmsub_abbrev_tac`_ = s1`
  \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`has_n_args s1mem a`
  \\ `s1mem = s1.MEM` by simp[Abbr`s1`]
  \\ fs[Abbr`s1mem`]
  \\ `a = s1.R 5w` by simp[Abbr`s1`, APPLY_UPDATE_THM]
  \\ fs[Abbr`a`]
  \\ impl_keep_tac >- (
    fs[has_n_args_def]
    \\ asm_exists_tac
    \\ simp[])
  \\ disch_then(assume_tac o SYM) \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_store s2`
  \\ qspecl_then[`fmd`,`s2`]mp_tac (Q.GEN`md`ag32_ffi_get_arg_store_decomp_thm)
  \\ qmatch_asmsub_abbrev_tac`6w =+ n2w index`
  \\ qspec_then`s1`mp_tac(Q.GENL[`s`]ag32_ffi_get_arg_find_thm)
  \\ impl_tac
  >- (
    fs[]
    \\ reverse conj_tac >- metis_tac[]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM] )
  \\ strip_tac
  \\ qpat_x_assum`_ = s2`SUBST_ALL_TAC
  \\ qunabbrev_tac`s2`
  \\ qmatch_asmsub_abbrev_tac`_ = s2`
  \\ simp[]
  \\ impl_tac >- (
    `s2.MEM = s1.MEM` by simp[Abbr`s2`]
    \\ `s2.R 3w = s.R 3w` by simp[Abbr`s2`,Abbr`s1`,APPLY_UPDATE_THM]
    \\ fs[]
    \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
    \\ qexists_tac`n`
    \\ simp[] )
  \\ disch_then(assume_tac o SYM) \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`FST p2 = s2`
  \\ `(s2,fmd) = p2`
  by (
    qpat_x_assum`_ = s2`(SUBST1_TAC o SYM)
    \\ simp[Abbr`p2`, quantHeuristicsTheory.FST_PAIR_EQ]
    \\ DEP_REWRITE_TAC[SND_ag32_ffi_get_arg_find_decomp]
    \\ simp[] \\ fs[]
    \\ metis_tac[] )
  \\ qpat_x_assum`_ = FST _`mp_tac
  \\ qpat_assum`_ = p2` SUBST1_TAC
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`FST p1 = s1`
  \\ `(s1,fmd) = p1`
  by (
    qpat_x_assum`_ = s1`(SUBST1_TAC o SYM)
    \\ simp[Abbr`p1`, quantHeuristicsTheory.FST_PAIR_EQ]
    \\ simp[ag32_ffi_get_arg_setup_decomp_def] )
  \\ qpat_x_assum`Abbrev(p2 = _)`mp_tac
  \\ first_assum SUBST1_TAC
  \\ strip_tac
  \\ simp[Abbr`p1`, Abbr`p2`]
  \\ match_mp_tac ag32_ffi_get_arg_FUNPOW_Next
  \\ simp[EVAL``LENGTH ag32_ffi_get_arg_code``, CONJ_ASSOC]
  \\ reverse conj_tac
  >- (
    simp[Abbr`fmd`, IN_DISJOINT, DIV_LT_X, EVAL``LENGTH ag32_ffi_get_arg_code``]
    \\ metis_tac[] )
  \\ simp[GSYM CONJ_ASSOC]
  \\ qpat_x_assum`(s1,fmd) = _`(assume_tac o SYM) \\ fs[]
  \\ qpat_x_assum`(s2,fmd) = _`(assume_tac o SYM) \\ fs[]
  \\ conj_tac >- (
    irule ag32_ffi_get_arg_store_decomp_pre'
    \\ `s2.MEM = s1.MEM` by simp[Abbr`s2`]
    \\ `s2.R 3w = s.R 3w` by simp[Abbr`s2`,Abbr`s1`,APPLY_UPDATE_THM]
    \\ qexists_tac`n`
    \\ simp[GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM, CONJ_ASSOC]
    \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
    \\ simp[Abbr`fmd`] \\ rfs[] )
  \\ conj_tac
  >- (
    irule ag32_ffi_get_arg_setup_decomp_pre'
    \\ simp[Abbr`fmd`]
    \\ EVAL_TAC
    \\ rw[]
    \\ CCONTR_TAC
    \\ fs[] \\ fs[] )
  \\ irule ag32_ffi_get_arg_find_decomp_pre'
  \\ qexists_tac`SUC index`
  \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
  \\ fs[EVAL``cline_size``]
QED

(* ag32_ffi_open_in *)

val ag32_ffi_open_in_fail_code_def = Define `
  ag32_ffi_open_in_fail_code = ag32_ffi_fail_code "open_in"`
    |> REWRITE_RULE [ag32_ffi_fail_code_def]

val (ag32_ffi_open_in_fail_SPEC,
     ag32_ffi_open_in_fail_decomp_def) = ag32_decompile
     ag32_ffi_open_in_fail_code_def

val ag32_ffi_open_in_SPEC =
  SPEC_COMPOSE_RULE [ag32_ffi_open_in_fail_SPEC,
                     ag32_ffi_return_SPEC]

val ag32_ffi_open_in_FUNPOW_Next = let
  val th = ag32_ffi_open_in_SPEC
  val code_def = ag32_ffi_open_in_code_def
                 |> SIMP_RULE std_ss [ag32_ffi_fail_code_def,
                                      ag32_ffi_return_code_def,APPEND]
  val th = FUNPOW_Next_from_SPEC code_def th
  val ag32_ffi_open_in_intro = prove(
    ``ag32_ffi_return (FST (ag32_ffi_open_in_fail_decomp (s,md))) =
      ag32_ffi_open_in s``,
    fs [ag32_ffi_open_in_fail_decomp_def,ag32_ffi_open_in_def,
        ag32_ffi_return_def,ag32_ffi_fail_def])
  in REWRITE_RULE [ag32_ffi_open_in_intro] th  end;

val ag32_ffi_open_in_entrypoint_thm = EVAL “ag32_ffi_open_in_entrypoint”

Theorem ag32_ffi_open_in_code_thm:
   (∀k. k < LENGTH ag32_ffi_open_in_code ⇒
          get_mem_word s.MEM (s.PC + n2w (4 * k)) =
          Encode (EL k ag32_ffi_open_in_code)) ∧
   byte_aligned s.PC ∧
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_open_in_entrypoint)) ∧
   s.R 3w ∉ { s.PC + n2w n | n < 4 * LENGTH ag32_ffi_open_in_code}
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_open_in s)
Proof
  strip_tac >>
  irule ag32_ffi_open_in_FUNPOW_Next \\ fs [] >>
  assume_tac (EVAL “LENGTH ag32_ffi_open_in_code”) >>
  simp[] >>
  simp[ag32_ffi_open_in_fail_decomp_def, ag32Theory.dfn'LoadConstant_def,
       ag32_progTheory.mem_unchanged_def, ag32Theory.dfn'StoreMEMByte_def,
       ag32Theory.incPC_def, ag32Theory.ri2word_def, combinTheory.UPDATE_def] >>
  simp[FFI_codes_def,
       combinTheory.UPDATE_def, ffi_code_start_offset_thm] >>
  qmatch_goalsub_abbrev_tac ‘COND ((n2w n) = _) 6w (s.MEM _)’ >>
  qexists_tac ‘{n2w n; s.R 3w}’ >>
  simp[Abbr‘n’, ag32_ffi_open_in_entrypoint_thm, DIV_LT_X, word_add_n2w] >>
  reverse conj_tac >- intLib.ARITH_TAC >>
  rfs[ag32_ffi_open_in_entrypoint_thm, ffi_code_start_offset_thm,
      word_add_n2w] >> fs[]
QED

(* ag32_ffi_open_out *)

val ag32_ffi_open_out_fail_code_def = Define `
  ag32_ffi_open_out_fail_code = ag32_ffi_fail_code "open_out"`
    |> REWRITE_RULE [ag32_ffi_fail_code_def]

val (ag32_ffi_open_out_fail_SPEC,
     ag32_ffi_open_out_fail_decomp_def) = ag32_decompile
     ag32_ffi_open_out_fail_code_def

val ag32_ffi_open_out_SPEC =
  SPEC_COMPOSE_RULE [ag32_ffi_open_out_fail_SPEC,
                     ag32_ffi_return_SPEC]

val ag32_ffi_open_out_fail_FUNPOW_Next = let
  val th = ag32_ffi_open_out_SPEC
  val code_def = ag32_ffi_open_out_code_def
                 |> SIMP_RULE std_ss [ag32_ffi_fail_code_def,
                                      ag32_ffi_return_code_def,APPEND]
  val th = FUNPOW_Next_from_SPEC code_def th
  val ag32_ffi_open_out_intro = prove(
    ``ag32_ffi_return (FST (ag32_ffi_open_out_fail_decomp (s,md))) =
      ag32_ffi_open_out s``,
    fs [ag32_ffi_open_out_fail_decomp_def,ag32_ffi_open_out_def,
        ag32_ffi_return_def,ag32_ffi_fail_def])
  in REWRITE_RULE [ag32_ffi_open_out_intro] th  end;

val ag32_ffi_open_out_entrypoint_thm = EVAL “ag32_ffi_open_out_entrypoint”
Theorem ag32_ffi_open_out_code_thm:
   (∀k. k < LENGTH ag32_ffi_open_out_code ⇒
      (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_open_out_code))) ∧
   byte_aligned s.PC ∧
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_open_out_entrypoint)) ∧
   s.R 3w ∉ {s.PC + n2w n | n < 4 * LENGTH ag32_ffi_open_out_code}
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_open_out s)
Proof
  strip_tac >>
  irule ag32_ffi_open_out_fail_FUNPOW_Next >>
  assume_tac (EVAL “LENGTH ag32_ffi_open_out_code”) >>
  fs [ag32_ffi_open_out_entrypoint_thm, ffi_code_start_offset_thm] >>
  simp[ag32_ffi_open_out_fail_decomp_def, ag32Theory.dfn'LoadConstant_def,
       ag32_progTheory.mem_unchanged_def, ag32Theory.dfn'StoreMEMByte_def,
       ag32Theory.incPC_def, ag32Theory.ri2word_def, combinTheory.UPDATE_def,
       FFI_codes_def, ffi_code_start_offset_thm] >>
  qmatch_goalsub_abbrev_tac ‘COND ((n2w n) = _) 7w (s.MEM _)’ >>
  qexists_tac ‘{n2w n; s.R 3w}’ >>
  simp[Abbr‘n’, DIV_LT_X, word_add_n2w] >>
  reverse conj_tac >- intLib.ARITH_TAC >>
  rfs[ag32_ffi_open_out_entrypoint_thm, ffi_code_start_offset_thm,
      word_add_n2w]
QED

(* ag32_ffi_close *)

val ag32_ffi_close_fail_code_def = Define `
  ag32_ffi_close_fail_code = ag32_ffi_fail_code "close"`
    |> REWRITE_RULE [ag32_ffi_fail_code_def]

val (ag32_ffi_close_fail_SPEC,
     ag32_ffi_close_fail_decomp_def) = ag32_decompile
     ag32_ffi_close_fail_code_def

val ag32_ffi_close_SPEC =
  SPEC_COMPOSE_RULE [ag32_ffi_close_fail_SPEC,
                     ag32_ffi_return_SPEC]

val ag32_ffi_close_fail_FUNPOW_Next = let
  val th = ag32_ffi_close_SPEC
  val code_def = ag32_ffi_close_code_def
                 |> SIMP_RULE std_ss [ag32_ffi_fail_code_def,
                                      ag32_ffi_return_code_def,APPEND]
  val th = FUNPOW_Next_from_SPEC code_def th
  val ag32_ffi_close_intro = prove(
    ``ag32_ffi_return (FST (ag32_ffi_close_fail_decomp (s,md))) =
      ag32_ffi_close s``,
    fs [ag32_ffi_close_fail_decomp_def,ag32_ffi_close_def,
        ag32_ffi_return_def,ag32_ffi_fail_def])
  in REWRITE_RULE [ag32_ffi_close_intro] th end

Theorem ag32_ffi_close_code_thm:
   (∀k. k < LENGTH ag32_ffi_close_code ⇒
      (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_close_code))) ∧
   byte_aligned s.PC ∧
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_close_entrypoint)) ∧
   s.R 3w ∉ { s.PC + n2w n | n < 4 * LENGTH ag32_ffi_close_code}
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_close s)
Proof
  strip_tac
  \\ irule ag32_ffi_close_fail_FUNPOW_Next
  \\ simp [EVAL ``LENGTH ag32_ffi_close_code``]
  \\ fs [theorem "ag32_ffi_close_fail_decomp_pre_def",
         ag32_progTheory.mem_unchanged_def, PULL_FORALL,
         ag32Theory.dfn'LoadConstant_def,
         ag32Theory.dfn'StoreMEMByte_def,
         ag32Theory.incPC_def,
         ag32Theory.ri2word_def,
         combinTheory.UPDATE_def,
         EVAL ``THE (ALOOKUP FFI_codes "close")``,
         EVAL ``ffi_code_start_offset``,
         EVAL ``ag32_ffi_close_entrypoint``,
         EVAL ``LENGTH ag32_ffi_close_code``]
  \\ qmatch_goalsub_abbrev_tac `COND (n2w n = _) _`
  \\ qexists_tac `{n2w n; s.R 3w}`
  \\ rfs [Abbr `n`, DIV_LT_X]
  \\ rw [word_add_n2w, DISJ_EQ_IMP]
  \\ strip_tac \\ fs []
QED

(* ag32_ffi_ *)


Theorem ag32_ffi__code_thm:
   (∀k. k < LENGTH ag32_ffi__code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi__code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_ s)
Proof
  rw[ag32_ffi__def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ imp_res_tac byte_aligned_imp \\ rfs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi__code_def, ag32Theory.Run_def]
  \\ EVERY (List.tabulate(1, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]
  \\ simp[EVAL``EL 1 ag32_ffi__code``]
QED

val ag32_ffi__entrypoint_thm = EVAL “ag32_ffi__entrypoint”

(* mk_jump_ag32 *)

Theorem mk_jump_ag32_code_thm:
   (s.PC = n2w (ffi_jumps_offset + ffi_offset * (LENGTH ffi_names - (index + 1)))) ∧
   (INDEX_OF nm ffi_names = SOME index) ∧
   (ALOOKUP ffi_entrypoints nm = SOME epc) ∧
   (∀k. k < 4 ⇒
     (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
      EL k (mk_jump_ag32_code ffi_names nm)))
   ⇒
   ∃k ov cf r5.
     (FUNPOW Next k s =
      s with <| PC := n2w (ffi_code_start_offset + epc)
              ; R := ((5w =+ r5) s.R)
              ; CarryFlag := cf
              ; OverflowFlag := ov |>)
Proof
  rw[]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- fs[]
  \\ simp_tac(srw_ss())[]
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_asm1_tac
  >- ( simp[]
       \\ simp[GSYM word_add_n2w]
       \\ irule byte_aligned_add
       \\ conj_tac >- EVAL_TAC
       \\ simp[alignmentTheory.byte_aligned_def, GSYM addressTheory.ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w]
       \\ EVAL_TAC \\ simp[])
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ disch_then kall_tac
  \\ simp[mk_jump_ag32_code_def]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`1`mp_tac)
  \\ impl_tac >- fs[]
  \\ simp_tac(srw_ss())[]
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_asm1_tac
  >- ( irule byte_aligned_add \\ fs[] \\ EVAL_TAC)
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ disch_then kall_tac
  \\ simp[mk_jump_ag32_code_def]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'LoadUpperConstant_def, ag32Theory.incPC_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`2`mp_tac)
  \\ impl_tac >- fs[]
  \\ simp_tac(srw_ss())[]
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_asm1_tac
  >- ( irule byte_aligned_add \\ fs[] \\ EVAL_TAC)
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ disch_then kall_tac
  \\ simp[mk_jump_ag32_code_def]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Jump_def, ag32Theory.ALU_def, ag32Theory.ri2word_def]
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[Once EXISTS_NUM] \\ disj1_tac
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 5w = _ then r5 else _`
  \\ qexists_tac`r5` \\ rw[]
  \\ fs[FFI_codes_def]
  \\ fs[GSYM find_index_INDEX_OF]
  \\ imp_res_tac find_index_LESS_LENGTH \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`off - epc`
  \\ qmatch_goalsub_abbrev_tac`n2w (ffi_jumps_offset + st)`
  \\ `off = ffi_jumps_offset + st + 8 - ffi_code_start_offset`
  by ( simp[Abbr`off`] \\ EVAL_TAC \\ simp[] )
  \\ qpat_x_assum`Abbrev(off = _)`kall_tac
  \\ qho_match_abbrev_tac`_ + -1w * (lc (n2w (off - epc))) + _ = _`
  \\ `lc (n2w (off - epc)) = n2w (off - epc)` by (
    qpat_x_assum`off = _`kall_tac
    \\ simp[Abbr`lc`]
    \\ blastLib.BBLAST_TAC )
  \\ pop_assum SUBST_ALL_TAC
  \\ rewrite_tac[WORD_SUB_INTRO, word_mul_n2w]
  \\ DEP_REWRITE_TAC[GSYM n2w_sub]
  \\ conj_asm1_tac
  >- ( simp[] \\ EVAL_TAC \\ simp[] )
  \\ simp_tac std_ss [word_add_n2w]
  \\ AP_TERM_TAC
  \\ qmatch_goalsub_abbrev_tac`a - b`
  \\ `a + 8 = b + epc + ffi_code_start_offset` suffices_by rw[]
  \\ `ffi_code_start_offset ≤ a + 8 `
  by ( simp[Abbr`a`] \\ EVAL_TAC \\ simp[Abbr`st`] )
  \\ `epc ≤ off` suffices_by simp[Abbr`b`]
  \\ simp[Abbr`a`]
  \\ EVAL_TAC
  \\ simp[Abbr`st`]
  \\ EVAL_TAC
  \\ simp[LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB]
  \\ qpat_x_assum`_ = SOME epc`mp_tac
  \\ EVAL_TAC
  \\ rpt(IF_CASES_TAC \\ simp[])
QED

val _ = export_theory();
