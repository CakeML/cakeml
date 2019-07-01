(*
  Define the memory layout for running CakeML programs on Silver, and implement
  the startup code, the FFI jumps, and the CakeML basis's primitive FFI calls
  in Silver machine code. Also define shallow embeddings of the FFI primitives
  and prove theorems summarising their effects.
*)

open preamble
local open
  ag32Theory ag32_targetTheory
  asmSemTheory asmPropsTheory
  mlstringTheory MarshallingTheory
  lab_to_targetTheory blastLib
in end

val _ = new_theory"ag32_memory";

(* TODO: move *)

val get_mem_word_def = Define`
  get_mem_word (m:word32->word8) (pc:word32) : word32 =
  (m (pc + 3w) @@
   ((m (pc + 2w) @@
     ((m (pc + 1w) @@
       m (pc)) : word16)) :word24))`;

val set_mem_word_def = Define`
  set_mem_word (a:word32) (w:word32) : (word32->word8) -> (word32->word8) =
    ((a =+ (((7 >< 0) w):word8)) o
    ((a + 1w =+ (((15 >< 8) w):word8)) o
    ((a + 2w =+ (((23 >< 16) w):word8)) o
    ((a + 3w =+ (((31 >< 24) w):word8))))))`;

Theorem set_mem_word_neq:
    x ≠ k ∧
  x +1w ≠ k ∧
  x +2w ≠ k ∧
  x +3w ≠ k ⇒
  set_mem_word x y m k = m k
Proof
  EVAL_TAC>>fs[]
QED

(* TODO: copied from stack_allocProofTheory *)
Theorem good_dimindex_32:
   (byte_aligned (w:word32) <=>
     ((w && 3w) = 0w))
Proof
  fs [alignmentTheory.byte_aligned_def,alignmentTheory.aligned_bitwise_and]
QED

Theorem get_mem_word_set_mem_word:
   byte_aligned a ∧ byte_aligned x ⇒
   (get_mem_word (set_mem_word a w m) x =
    if a = x then w else get_mem_word m x)
Proof
  rw[get_mem_word_def,set_mem_word_def]>>
  fs[APPLY_UPDATE_THM]
  >-
    (rpt
    (IF_CASES_TAC>- (
      CCONTR_TAC>>
      qpat_x_assum`a = _` mp_tac>>
      blastLib.BBLAST_TAC))>>
    blastLib.BBLAST_TAC)
  >>
  fs[good_dimindex_32]>>
  (rpt
    (IF_CASES_TAC>- (
      CCONTR_TAC>> pop_assum kall_tac>>
      blastLib.FULL_BBLAST_TAC))>>
    blastLib.BBLAST_TAC)
QED

Theorem get_mem_word_asm_write_bytearray_UNCHANGED_LT:
    (pc <+ a) ∧
  (pc+1w <+ a) ∧
  (pc+2w <+ a) ∧
  (pc+3w <+ a) ∧
  w2n a + LENGTH ls < dimword(:32)
  ⇒
  get_mem_word
    (asm_write_bytearray a ls m) pc =
  get_mem_word m pc
Proof
  rw[]>>
  imp_res_tac asm_write_bytearray_unchanged>>
  fs[get_mem_word_def]
QED

Theorem get_mem_word_UPDATE:
    pc ≠ k ∧
  pc+1w ≠ k ∧
  pc+2w ≠ k ∧
  pc+3w ≠ k
  ⇒
  get_mem_word
    ((k =+ v) m) pc =
  get_mem_word m pc
Proof
  rw[]>>
  fs[get_mem_word_def] >>
  fs[APPLY_UPDATE_THM]
QED

Theorem get_mem_word_change_mem:
   (∀k. k < 4 ⇒ (m1 (pc + n2w k) = m2 (pc + n2w k))) ⇒
   (get_mem_word m1 pc = get_mem_word m2 pc)
Proof
  srw_tac[DNF_ss][get_mem_word_def, NUMERAL_LESS_THM]
QED

Theorem dfn'Normal_PC:
   (dfn'Normal x s).PC = s.PC + 4w
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Normal_def]
  \\ rw[ag32Theory.norm_def]
  \\ simp[ag32Theory.ALU_def]
  \\ PURE_TOP_CASE_TAC \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'Normal_MEM:
   (dfn'Normal x s).MEM = s.MEM
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Normal_def]
  \\ rw[ag32Theory.norm_def]
  \\ simp[ag32Theory.ALU_def]
  \\ PURE_TOP_CASE_TAC \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'JumpIfZero_PC:
   ((dfn'JumpIfZero (fSnd,Reg i,Imm w,Reg r) s).PC =
      if s.R r = 0w then s.PC + s.R i else s.PC + 4w) /\
   ((dfn'JumpIfZero (fSnd,Imm v,Imm w,Reg r) s).PC =
      if s.R r = 0w then s.PC + sw2sw v else s.PC + 4w) /\
   ((dfn'JumpIfZero (fSnd,Imm v,Imm w,Imm x) s).PC =
      if sw2sw x = 0w:word32 then s.PC + sw2sw v else s.PC + 4w)
Proof
  rw[ag32Theory.dfn'JumpIfZero_def,ag32Theory.ALU_def,ag32Theory.ri2word_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'JumpIfZero_MEM:
   (dfn'JumpIfZero x s).MEM = s.MEM
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'JumpIfZero_def]
  \\ simp[ag32Theory.incPC_def,ag32Theory.ALU_def]
  \\ rpt (every_case_tac \\ fs [])
QED

Theorem dfn'JumpIfNotZero_PC:
   ((dfn'JumpIfNotZero (fSnd,Reg i,Imm w,Reg r) s).PC =
      if s.R r <> 0w then s.PC + s.R i else s.PC + 4w) /\
   ((dfn'JumpIfNotZero (fSnd,Imm v,Imm w,Reg r) s).PC =
      if s.R r <> 0w then s.PC + sw2sw v else s.PC + 4w) /\
   ((dfn'JumpIfNotZero (fSnd,Imm v,Imm w,Imm x) s).PC =
      if sw2sw x <> 0w:word32 then s.PC + sw2sw v else s.PC + 4w)
Proof
  rw[ag32Theory.dfn'JumpIfNotZero_def,ag32Theory.ALU_def,ag32Theory.ri2word_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'JumpIfNotZero_MEM:
   (dfn'JumpIfNotZero x s).MEM = s.MEM
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'JumpIfNotZero_def]
  \\ simp[ag32Theory.incPC_def,ag32Theory.ALU_def]
  \\ rpt (every_case_tac \\ fs [])
QED

Theorem dfn'Interrupt_PC:
   ((dfn'Interrupt s).PC = s.PC + 4w)
Proof
  rw[ag32Theory.dfn'Interrupt_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'Interrupt_MEM:
   ((dfn'Interrupt s).MEM = s.MEM)
Proof
  rw[ag32Theory.dfn'Interrupt_def,ag32Theory.incPC_def]
QED

Theorem dfn'Jump_MEM:
   ((dfn'Jump x s).MEM = s.MEM)
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Jump_def,ag32Theory.ALU_def]
  \\ every_case_tac \\ fs []
QED

Theorem dfn'LoadMEM_PC:
   (dfn'LoadMEM x s).PC = s.PC + 4w
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadMEM_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'LoadMEM_MEM:
   (dfn'LoadMEM x s).MEM = s.MEM
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadMEM_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'StoreMEMByte_PC:
   (dfn'StoreMEMByte x s).PC = s.PC + 4w
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'StoreMEMByte_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'LoadMEMByte_PC:
   (dfn'LoadMEMByte x s).PC = s.PC + 4w
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadMEMByte_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'LoadMEMByte_MEM:
   (dfn'LoadMEMByte x s).MEM = s.MEM
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadMEMByte_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'Shift_PC:
   (ag32$dfn'Shift x s).PC = s.PC + 4w
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Shift_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'Shift_MEM:
   (ag32$dfn'Shift x s).MEM = s.MEM
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Shift_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'LoadConstant_PC:
   (ag32$dfn'LoadConstant x s).PC = s.PC + 4w
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'LoadConstant_MEM:
   (ag32$dfn'LoadConstant x s).MEM = s.MEM
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32Theory.incPC_def]
QED

Theorem dfn'JumpIfZero_MEM:
   (ag32$dfn'JumpIfZero x s).MEM = s.MEM
Proof
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def]
  \\ PURE_TOP_CASE_TAC \\ fs[ag32Theory.incPC_def] \\ rw[]
QED

(* -- *)

val memory_size_def = Define`
  memory_size = 128n * 10 ** 6`;

val cline_size_def = Define`
  cline_size = 2 * 1024n`;

val stdin_size_def = Define`
  stdin_size = 5 * 1024 * 1024n`;

val output_buffer_size_def = Define`
  output_buffer_size = 2048n`;

val heap_size_def = Define`
  heap_size = 100 * 1024 * 1024n`;

val startup_code_size_def = Define`
  startup_code_size = 240n`;

(* Memory Layout:

  +-------------------+
  | * CakeML data     |
  +-------------------+  about 23MB left for these
  | * CakeML code     |
  +-------------------+
  | * FFI call jumps  |  <= 176 ((9 + 2) * 16) bytes
  +-------------------+
  | CakeML stack/heap |  heap_size bytes (~100Mb)
  +-------------------+  <- heap_start_offset
  | --- (padding) --- |  (will arrange for this to be 0)
  +-------------------+
  | FFI code          |  (4 * LENGTH ag32_ffi_code) bytes (~640b)
  +-------------------+
  | FFI call id       |  4 bytes (as a word)
  +-------------------+
  | output buffer     |  output_buffer_size bytes (~2Kb)
  +-------------------+
  | output length     |  4 bytes
  +-------------------+
  | output id         |  8 bytes (* ridiculously overpowered... *)
  +-------------------+
  | + stdin           |  stdin_size bytes (~5Mb)
  +-------------------+
  | + stdin length    |  4 bytes
  +-------------------+
  | stdin pointer     |  4 bytes
  +-------------------+
  | + cline args      |  cline_size bytes (~1024b)
  +-------------------+
  | + cline arg count |  4 bytes (as a word)
  +-------------------+  <- startup_code_size
  | ---- padding ---- |
  +-------------------+
  | * startup code    |  (LENGTH startup_code) bytes (~72b, ≤216b (18*12))
  +-------------------+

  The starred items depend on the output of the compiler;
  the other items are boilerplate for every application.
  The plussed items are set by the host before execution.
*)

val FFI_codes_def = Define`
  FFI_codes =
    [
    ("", 0n)
    ;("get_arg_count", 1n)
    ;("get_arg_length", 2n)
    ;("get_arg", 3n)
    ;("read", 4n)
    ;("write", 5n)
    ;("open_in", 6n)
    ;("open_out", 7n)
    ;("close", 8n)
    (*;("exit", 9n)*)
    ]`;

val stdin_offset_def = Define`
  stdin_offset = startup_code_size + 4 + cline_size`;

val output_offset_def = Define`
  output_offset = stdin_offset + 4 + 4 + stdin_size`;

val ffi_code_start_offset_def = Define`
  ffi_code_start_offset =
    output_offset + 8 + 4 + output_buffer_size + 4`;

val length_ag32_ffi_code = Define`
  length_ag32_ffi_code = 1272n`;

val heap_start_offset_def = Define`
  heap_start_offset =
    ffi_code_start_offset + length_ag32_ffi_code`;

val ffi_jumps_offset_def = Define`
  ffi_jumps_offset =
    heap_start_offset + heap_size`;

val ag32_ffi_return_code_def = Define`
  ag32_ffi_return_code = [
   Normal (fAdd, 1w, Imm 0w, Imm 0w);
   Normal (fSnd, 2w, Imm 0w, Imm 0w);
   Normal (fSnd, 3w, Imm 0w, Imm 0w);
   Normal (fSnd, 4w, Imm 0w, Imm 0w);
   Normal (fSnd, 5w, Imm 0w, Imm 0w);
   Normal (fSnd, 6w, Imm 0w, Imm 0w);
   Normal (fSnd, 7w, Imm 0w, Imm 0w);
   Normal (fSnd, 8w, Imm 0w, Imm 0w);
   Interrupt;
   Jump (fSnd, 0w, Reg 0w)]`;

val ag32_ffi_return_def = Define`
  ag32_ffi_return s =
  let s = dfn'Normal (fAdd, 1w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 2w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 3w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 4w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 5w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 6w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 7w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 8w, Imm 0w, Imm 0w) s in
  let s = dfn'Interrupt s in
  let s = dfn'Jump (fSnd, 0w, Reg 0w) s in
  s`;

Theorem ag32_ffi_return_thm:
   (ag32_ffi_return s =
    s with <| PC := s.R 0w;
              R := ((0w =+ s.PC + n2w (4 * LENGTH ag32_ffi_return_code))
                   ((1w =+ 0w)
                   ((2w =+ 0w)
                   ((3w =+ 0w)
                   ((4w =+ 0w)
                   ((5w =+ 0w)
                   ((6w =+ 0w)
                   ((7w =+ 0w)
                   ((8w =+ 0w) s.R)))))))));
              io_events := SNOC s.MEM s.io_events;
              OverflowFlag := F;
              CarryFlag := F |>)
Proof
  rw[ag32_ffi_return_def]
  \\ rw[ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        ag32Theory.norm_def, ag32Theory.ALU_def,
        ag32Theory.dfn'Interrupt_def, ag32Theory.dfn'Jump_def]
  \\ rw[ag32Theory.ag32_state_component_equality, APPLY_UPDATE_THM, FUN_EQ_THM]
  >- EVAL_TAC
  \\ rw[] \\ fs[]
  \\ EVAL_TAC
QED

val ag32_ffi_copy_code_def = Define`
  ag32_ffi_copy_code = [
     JumpIfZero (fSnd, Reg 2w, Imm 0w, Reg 1w);
     LoadMEMByte (8w, Reg 3w);
     StoreMEMByte (Reg 8w, Reg 5w);
     Normal (fInc, 3w, Reg 3w, Imm 1w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);
     Normal (fDec, 1w, Reg 1w, Imm 1w);
     JumpIfZero (fSnd, Imm (4w * -6w), Imm 0w, Imm 0w)]`;

val ag32_ffi_copy_def = tDefine"ag32_ffi_copy"`
  ag32_ffi_copy s0 =
  let s = dfn'JumpIfZero (fSnd, Reg 2w, Imm 0w, Reg 1w) s0 in
  if (s0.R 1w = 0w) then s else
  let s = dfn'LoadMEMByte (8w, Reg 3w) s in
  let s = dfn'StoreMEMByte (Reg 8w, Reg 5w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s0 = dfn'Normal (fDec, 1w, Reg 1w, Imm 1w) s in
  let s = dfn'JumpIfZero (fSnd, Imm (4w * -6w), Imm 0w, Imm 0w) s0 in
  ag32_ffi_copy s`
  (wf_rel_tac`measure (λs. w2n (s.R 1w))`
   \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def,
         ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
         ag32Theory.dfn'LoadConstant_def,
         ag32Theory.dfn'StoreMEMByte_def, ag32Theory.dfn'LoadMEMByte_def,
         ag32Theory.ri2word_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
   \\ Cases_on`s0.R 1w` \\ fs[]
   \\ Cases_on`n` \\ fs[]
   \\ simp[ADD1, GSYM word_add_n2w]);

Theorem ag32_ffi_copy_thm:
   ∀s written.
   bytes_in_memory (s.R 3w) written s.MEM md ∧ (w2n (s.R 1w) = LENGTH written) ∧
   DISJOINT md { w | s.R 5w <=+ w ∧ w <+ s.R 5w + n2w (LENGTH written) } ∧
   w2n (s.R 5w) + LENGTH written < dimword(:32) ∧
   w2n (s.R 3w) + LENGTH written < dimword(:32)
   ⇒
   ∃r1 r3 r5 r8.
   (ag32_ffi_copy s =
    s with <| PC := s.PC + s.R 2w;
              R := ((1w =+ r1)
                   ((3w =+ r3)
                   ((5w =+ r5)
                   ((8w =+ r8) s.R))));
              MEM := asm_write_bytearray (s.R 5w) written s.MEM |>)
Proof
  Induct_on`w2n (s.R 1w)` \\ rw[]
  >- (
    qpat_x_assum`0 = _`(assume_tac o SYM)
    \\ fs[read_bytearray_def, bytes_in_memory_def] \\ rw[]
    \\ rw[asm_write_bytearray_def]
    \\ rw[Once ag32_ffi_copy_def, ag32Theory.dfn'LoadConstant_def,
          ag32Theory.incPC_def, APPLY_UPDATE_THM]
    \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def, ag32Theory.ri2word_def,
          ag32Theory.incPC_def, APPLY_UPDATE_THM]
    \\ rw[ag32Theory.ag32_state_component_equality]
    \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ metis_tac[] )
  \\ fs[]
  \\ qpat_x_assum`SUC _ = _`(assume_tac o SYM)
  \\ Cases_on`written`
  \\ fs[read_bytearray_def, bytes_in_memory_def]
  \\ rw[] \\ fs[CaseEq"option"] \\ rw[]
  \\ rw[Once ag32_ffi_copy_def, ag32Theory.dfn'LoadConstant_def,
        ag32Theory.incPC_def, APPLY_UPDATE_THM] \\ fs[]
  \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
        ag32Theory.incPC_def, ag32Theory.ri2word_def,
        ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_copy s'`
  \\ first_x_assum(qspec_then`s'`mp_tac)
  \\ simp[Abbr`s'`, APPLY_UPDATE_THM]
  \\ impl_keep_tac
  >- (
    Cases_on`s.R 1w` \\ fs[]
    \\ simp[ADD1]
    \\ simp[GSYM word_add_n2w] )
  \\ rveq
  \\ disch_then(qspec_then`t`mp_tac)
  \\ impl_tac
  >- (
    fs[]
    \\ reverse conj_asm2_tac
    >- (
      fs[IN_DISJOINT, DISJ_EQ_IMP]
      \\ Cases_on`s.R 5w`
      \\ fs[ADD1, word_add_n2w]
      \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ gen_tac \\ strip_tac
      \\ first_x_assum drule
      \\ rw[]
      \\ Cases_on`s.R 1w` \\ rfs[word_add_n2w]
      \\ Cases_on`n''` \\ fs[ADD1, GSYM word_add_n2w]
      \\ first_x_assum match_mp_tac
      \\ Cases_on`x`
      \\ fs[word_ls_n2w] \\ rw[]
      \\ fs[word_add_n2w, word_ls_n2w]
      \\ Cases_on`n + 1 = dimword(:32)` \\ fs[]
      \\ `n + 1 < dimword(:32)` by fs[] \\ fs[])
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM]
    \\ rw[]
    \\ Cases_on`s.R 1w` \\ fs[] \\ rfs[]
    \\ Cases_on`n'` \\ fs[ADD1, GSYM word_add_n2w] \\ rw[]
    \\ rfs[] \\ rw[]
    \\ fs[IN_DISJOINT, DISJ_EQ_IMP]
    \\ drule (GEN_ALL asmPropsTheory.bytes_in_memory_all_pcs)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac) \\ simp[]
    \\ disch_then drule
    \\ strip_tac
    \\ last_x_assum drule
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w] \\ rfs[]
    \\ fs[word_lo_n2w] )
  \\ rw[]
  \\ rw[]
  \\ rw[ag32Theory.ag32_state_component_equality]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ map_every qexists_tac[`r1`,`r3`,`r5`,`r8`]
  \\ reverse conj_tac >- rw[]
  \\ rw[asm_write_bytearray_def, APPLY_UPDATE_THM]
  >- (
    irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 1w` \\ fs[ADD1]
    \\ Cases_on`s.R 5w` \\ fs[word_add_n2w]
    \\ fs[word_lo_n2w, word_ls_n2w]
    \\ blastLib.BBLAST_TAC )
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ rw[APPLY_UPDATE_THM]
QED

(* exit
   PC is ffi_code_start_offset

val ag32_ffi_exit_entrypoint_def = Define`
  ag32_ffi_exit_entrypoint = 0n`;

val ag32_ffi_exit_def = Define`
  ag32_ffi_exit s =
    let s = dfn'Jump(fAdd, 5w, Imm 4w) s in
    let s = incPC () (s with R := (6w =+ w2w(((22 >< 0)(n2w (ffi_code_start_offset+4) :word32)):23 word)) s.R) in
    let s = incPC () (s with R := (6w =+ bit_field_insert 31 23 (((31 >< 23)(n2w (ffi_code_start_offset+4) :word32)):9 word) (s.R 6w)) s.R) in
    let s = incPC () (s with R := (5w =+ (s.R 5w) - (s.R 6w)) s.R) in
    let s = incPC () (s with MEM := ((s.R 5w) =+ 0w) s.MEM) in
    let s = incPC () (s with R := (5w =+ 0w) s.R) in
    let s = incPC () (s with R := (6w =+ 0w) s.R) in
    let s = incPC () (s with R := (7w =+ 0w) s.R) in
    let s = incPC () (s with <| R := (8w =+ 0w) s.R; OverflowFlag := F; CarryFlag := F|>) in
    let s = incPC () (s with io_events := s.io_events ++ [s.MEM]) in
    s`;

val ag32_ffi_exit_code_def = Define`
  ag32_ffi_exit_code =
    [Jump (fAdd, 5w, Imm 4w);
     LoadConstant(6w, F, (22 >< 0)((n2w (ffi_code_start_offset+4)):word32));
     LoadUpperConstant(6w, (31 >< 23)((n2w (ffi_code_start_offset+4)):word32));
     Normal (fSub, 5w, Reg 5w, Reg 6w);
     StoreMEMByte (Imm 0w, Reg 5w);
     Normal(fSnd, 5w, Imm 0w, Imm 0w);
     Normal(fSnd, 6w, Imm 0w, Imm 0w);
     Normal(fSnd, 7w, Imm 0w, Imm 0w);
     Normal(fAdd, 8w, Imm 0w, Imm 0w);
     Interrupt]`;
*)

(* "" ffi
  PC is ffi_code_start_offset
 *)
val ag32_ffi__entrypoint_def = Define`
  ag32_ffi__entrypoint = 0n`;

val ag32_ffi__def = Define`
  ag32_ffi_ s =
  let s = dfn'Normal (fAdd, 5w, Imm 0w, Imm 0w) s in
  dfn'Jump (fSnd, 0w, Reg 0w) s`

val ag32_ffi__code_def = Define`
  ag32_ffi__code =
    [
    Normal (fAdd, 5w, Imm 0w, Imm 0w);
    Jump (fSnd, 0w, Reg 0w)]`;

(* get_arg_count
   PC is ffi_code_start_offset
         + 4 * LENGTH ag32_ffi__code
   pointer is in r3 *)

val ag32_ffi_get_arg_count_entrypoint_def = Define`
  ag32_ffi_get_arg_count_entrypoint =
  ag32_ffi__entrypoint + 4 * LENGTH ag32_ffi__code`;

val ag32_ffi_get_arg_count_main_code_def = Define`
  ag32_ffi_get_arg_count_main_code =
    [LoadConstant(5w, F, n2w (ffi_code_start_offset - 1));
     StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "get_arg_count"))), Reg 5w);
     LoadConstant(5w, F, n2w startup_code_size);
     LoadMEM(5w, Reg 5w);
     StoreMEMByte (Reg 5w, Reg 3w);
     Shift (shiftLR, 5w, Reg 5w, Imm 8w);
     Normal (fInc, 3w, Reg 3w, Imm 0w);
     StoreMEMByte (Reg 5w, Reg 3w)]`;

val ag32_ffi_get_arg_count_code_def = Define`
  ag32_ffi_get_arg_count_code =
    ag32_ffi_get_arg_count_main_code
    ++ ag32_ffi_return_code`;

val ag32_ffi_get_arg_count_main_def = Define`
  ag32_ffi_get_arg_count_main s =
  let s = dfn'LoadConstant(5w, F, n2w (ffi_code_start_offset - 1)) s in
  let s = dfn'StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "get_arg_count"))), Reg 5w) s in
  let s = dfn'LoadConstant(5w, F, n2w startup_code_size) s in
  let s = dfn'LoadMEM(5w, Reg 5w) s in
  let s = dfn'StoreMEMByte (Reg 5w, Reg 3w) s in
  let s = dfn'Shift (shiftLR, 5w, Reg 5w, Imm 8w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 0w) s in
  let s = dfn'StoreMEMByte (Reg 5w, Reg 3w) s in
  s`;

Theorem ag32_ffi_get_arg_count_main_thm:
   (get_mem_word s.MEM (n2w startup_code_size) = n2w len) ∧ len < 256 * 256
   ⇒
   ∃r3 r5.
    (ag32_ffi_get_arg_count_main s =
     s with <| PC := s.PC + n2w (4 * (LENGTH ag32_ffi_get_arg_count_main_code));
               MEM :=
                 asm_write_bytearray (s.R 3w) [n2w len; n2w (len DIV 256)]
                   (((n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes "get_arg_count"))) s.MEM);
               R := ((3w =+ r3) ((5w =+ r5) s.R)) |>)
Proof
  rw[ag32_ffi_get_arg_count_main_def]
  \\ rw[ag32Theory.dfn'StoreMEM_def, ag32Theory.dfn'LoadMEM_def, ag32Theory.ri2word_def,
        ag32Theory.dfn'LoadConstant_def, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def,
        ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
        ag32Theory.incPC_def, ag32Theory.ri2word_def,
        ag32Theory.ALU_def,ag32Theory.dfn'Shift_def,ag32Theory.shift_def]
  \\ EVAL_TAC
  \\ simp[APPLY_UPDATE_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ fs[get_mem_word_def, EVAL``startup_code_size``]
  \\ qexists_tac`s.R 3w + 1w` \\ simp[]
  \\ qexists_tac`n2w len >>>8` \\ simp[]
  \\ strip_tac>>
  IF_CASES_TAC>>fs[]
  >- (
    `s.R 3w ≠ x` by
      blastLib.FULL_BBLAST_TAC>>
    simp[]>>
    `len DIV 256 < 256` by
      (DEP_REWRITE_TAC [DIV_LT_X]>>fs[])>>
    qspecl_then [`len`,`8n`] assume_tac (INST_TYPE [alpha|->``:32``] n2w_DIV)>>
    rfs[]>>
    blastLib.FULL_BBLAST_TAC)>>
  IF_CASES_TAC>>fs[]>>
  simp[word_extract_n2w,bitTheory.BITS_THM]
QED

val ag32_ffi_get_arg_count_def = Define`
  ag32_ffi_get_arg_count s =
  let s = ag32_ffi_get_arg_count_main s in
  ag32_ffi_return s`;

(* get_arg_length
   PC is ffi_code_start_offset
         + ag32_ffi_get_arg_count_entrypoint
         + 4 * LENGTH ag32_ffi_get_arg_count_code
   r3 contains pointer to byte array with the arg index: [index % 256, index / 256]
   the array should afterwards contain the length of the arg at index (in the same format) *)

val ag32_ffi_get_arg_length_entrypoint_def = Define`
  ag32_ffi_get_arg_length_entrypoint =
  ag32_ffi_get_arg_count_entrypoint + 4 * LENGTH ag32_ffi_get_arg_count_code`;

val ag32_ffi_get_arg_length_setup_code_def = Define`
  ag32_ffi_get_arg_length_setup_code =
    [LoadConstant(5w, F, n2w (ffi_code_start_offset - 1));
     StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "get_arg_length"))), Reg 5w);
     LoadConstant(5w, F, (n2w (startup_code_size + 4))); (* r5 contains pointer *)
     LoadMEMByte(6w, Reg 3w);
     Normal(fInc, 3w, Reg 3w, Imm 1w);
     LoadMEMByte(7w, Reg 3w);
     Shift(shiftLL, 7w, Reg 7w, Imm 8w);
     Normal(fDec, 3w, Reg 3w, Imm 1w);
     Normal(fInc, 6w, Reg 6w, Imm 1w);
     Normal(fAdd, 6w, Reg 6w, Reg 7w); (* r6 contains index+1 *)
     LoadConstant(7w, F, n2w (4 * 8))]`;

val ag32_ffi_get_arg_length_loop_code_def = Define`
  ag32_ffi_get_arg_length_loop_code =
  (* decompiler version:
    [JumpIfZero (fSnd,Imm (4w * 7w),Imm 0w,Imm 0w);
     Normal (fSnd,4w,Reg 4w,Imm 0w);
     LoadMEMByte (8w,Reg 5w);
     Normal (fInc,5w,Reg 5w,Imm 1w);
     Normal (fInc,4w,Reg 4w,Imm 1w);
     JumpIfNotZero (fSnd,Imm (4w * -3w),Imm 0w,Reg 8w);
     Normal (fDec,6w,Reg 6w,Imm 1w);
     JumpIfNotZero (fSnd,Imm (4w * -6w),Imm 0w,Reg 6w)]
  *)
    [JumpIfZero (fSnd, Reg 7w, Imm 0w, Reg 6w);
     Normal (fSnd, 4w, Reg 4w, Imm 0w);
     LoadMEMByte (8w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);
     Normal (fInc, 4w, Reg 4w, Imm 1w);
     JumpIfNotZero (fSnd, Imm (4w * -3w), Imm 0w, Reg 8w);
     Normal (fDec, 6w, Reg 6w, Imm 1w);
     JumpIfZero (fSnd, Imm (4w * -7w), Imm 0w, Imm 0w)]`;

val ag32_ffi_get_arg_length_store_code_def = Define`
  ag32_ffi_get_arg_length_store_code =
    [Normal (fDec, 4w, Reg 4w, Imm 1w);
     StoreMEMByte(Reg 4w, Reg 3w);
     Shift(shiftLR, 4w, Reg 4w, Imm 8w);
     Normal(fInc, 3w, Reg 3w, Imm 1w);
     StoreMEMByte(Reg 4w, Reg 3w)]`;

val ag32_ffi_get_arg_length_code_def = Define`
  ag32_ffi_get_arg_length_code =
    ag32_ffi_get_arg_length_setup_code ++
    ag32_ffi_get_arg_length_loop_code ++
    ag32_ffi_get_arg_length_store_code ++
    ag32_ffi_return_code`;

val ag32_ffi_get_arg_length_setup_def = Define`
  ag32_ffi_get_arg_length_setup s =
  let s = dfn'LoadConstant(5w, F, n2w (ffi_code_start_offset - 1)) s in
  let s = dfn'StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "get_arg_length"))), Reg 5w) s in
  let s = dfn'LoadConstant(5w, F, (n2w (startup_code_size + 4))) s in
  let s = dfn'LoadMEMByte(6w, Reg 3w) s in
  let s = dfn'Normal(fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte(7w, Reg 3w) s in
  let s = dfn'Shift(shiftLL, 7w, Reg 7w, Imm 8w) s in
  let s = dfn'Normal(fDec, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'Normal(fInc, 6w, Reg 6w, Imm 1w) s in
  let s = dfn'Normal(fAdd, 6w, Reg 6w, Reg 7w) s in
  let s = dfn'LoadConstant(7w, F, n2w (4 * 8)) s in
  s`;

Theorem ag32_ffi_get_arg_length_setup_thm:
   bytes_in_memory (s.R 3w) [l0; l1] s.MEM md ∧ n2w(ffi_code_start_offset - 1) ∉ md
   ⇒
   ∃ov cf.
   (ag32_ffi_get_arg_length_setup s =
    s with <|
      MEM := ((n2w (ffi_code_start_offset - 1)) =+ n2w(THE(ALOOKUP FFI_codes "get_arg_length"))) s.MEM;
      PC := s.PC + n2w (4 * LENGTH ag32_ffi_get_arg_length_setup_code);
      R := ((5w =+ n2w (startup_code_size + 4))
           ((6w =+ n2w (256 * w2n l1 + w2n l0 + 1))
           ((7w =+ n2w (4 * 8)) s.R)));
      CarryFlag := cf; OverflowFlag := ov |>)
Proof
  rw[ag32_ffi_get_arg_length_setup_def]
  \\ simp[ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.incPC_def,
        ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def, ag32Theory.ri2word_def,
        ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
        ag32Theory.dfn'LoadConstant_def,
        ag32Theory.dfn'StoreMEMByte_def, APPLY_UPDATE_THM]
  \\ fs[bytes_in_memory_def, w2w_n2w, EVAL``ffi_code_start_offset``]
  \\ IF_CASES_TAC \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`w2w (A) +  (w2w(B) <<8)`
  \\ simp[w2w_def,GSYM word_add_n2w]
  \\ fs[WORD_MUL_LSL]
  \\ simp[GSYM word_mul_n2w]
QED

val ag32_ffi_get_arg_length_loop1_def = tDefine"ag32_ffi_get_arg_length_loop1"`
  ag32_ffi_get_arg_length_loop1 s =
    if (∀n. s.MEM (s.R 5w + n2w n) ≠ 0w) then s else
    let s = dfn'LoadMEMByte (8w, Reg 5w) s in
    let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
    let s0 = dfn'Normal (fInc, 4w, Reg 4w, Imm 1w) s in
    let s = dfn'JumpIfNotZero (fSnd, Imm (4w * -3w), Imm 0w, Reg 8w) s0 in
    if (s0.R 8w = 0w) then s else ag32_ffi_get_arg_length_loop1 s`
  (wf_rel_tac`measure (λs. LEAST n. (s.MEM (s.R 5w + n2w n) = 0w))`
   \\ rw[ag32Theory.dfn'LoadMEMByte_def,
         ag32Theory.incPC_def,
         ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def, ag32Theory.ri2word_def,
         ag32Theory.dfn'JumpIfNotZero_def]
   \\ fs[APPLY_UPDATE_THM]
   \\ Cases_on`s.R 5w` \\ fs[word_add_n2w]
   \\ numLib.LEAST_ELIM_TAC
   \\ Cases_on`n` \\ fs[] \\ rfs[ADD1]
   \\ conj_tac >- (qexists_tac`n''` \\ simp[])
   \\ rw[]
   \\ numLib.LEAST_ELIM_TAC
   \\ conj_tac >- (qexists_tac`n''+1` \\ simp[])
   \\ rw[]
   \\ Cases_on`n'''` \\ fs[ADD1]
   \\ Cases_on`n` \\ fs[ADD1]
   \\ `¬(n'''' < n''' + 1)` by metis_tac[ADD_ASSOC,ADD_COMM]
   \\ fs[NOT_LESS]);

Theorem ag32_ffi_get_arg_length_loop1_thm:
   ag32_ffi_get_arg_length_loop1 s =
   case OLEAST n. s.MEM (s.R 5w + n2w n) = 0w of
     NONE => s
   | SOME n =>
     s with <| PC := s.PC + n2w (4 * 4);
               R := ((8w =+ 0w)
                    ((4w =+ s.R 4w + n2w (n+1))
                    ((5w =+ s.R 5w + n2w (n+1)) s.R))) |>
Proof
  reverse(rw[whileTheory.OLEAST_def])
  >- (
    rw[Once ag32_ffi_get_arg_length_loop1_def]
    \\ fs[] \\ metis_tac[] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- (qexists_tac`n` \\ simp[])
  \\ pop_assum kall_tac
  \\ qid_spec_tac`s`
  \\ Induct_on`n`
  >- (
    rw[]
    \\ simp[Once ag32_ffi_get_arg_length_loop1_def]
    \\ IF_CASES_TAC
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
    \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
            ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.dfn'LoadMEMByte_def,
            ag32Theory.dfn'JumpIfNotZero_def,
            APPLY_UPDATE_THM]
    \\ simp[ag32Theory.ag32_state_component_equality]
    \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ rw[] \\ fs[] )
  \\ rw[]
  \\ simp[Once ag32_ffi_get_arg_length_loop1_def]
  \\ IF_CASES_TAC
  >- ( first_x_assum(qspec_then`SUC n`mp_tac) \\ rw[] )
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
          ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.dfn'LoadMEMByte_def,
          ag32Theory.dfn'JumpIfNotZero_def,
          APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    first_x_assum(qspec_then`0`mp_tac)
    \\ impl_tac >- simp[]
    \\ strip_tac
    \\ Cases_on`s.MEM (s.R 5w)` \\ fs[w2w_n2w]
    \\ qspecl_then[`7`,`0`,`n'`]mp_tac bitTheory.BITSLT_THM
    \\ strip_tac \\ fs[]
    \\ fs[bitTheory.BITS_ZERO3] )
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_length_loop1 s'`
  \\ first_x_assum(qspec_then`s'`mp_tac)
  \\ simp[Abbr`s'`, APPLY_UPDATE_THM]
  \\ impl_tac
  >- (
    fs[ADD1, GSYM word_add_n2w] \\ rw[]
    \\ first_x_assum(qspec_then`m+1`mp_tac)
    \\ rw[GSYM word_add_n2w] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM, ADD1, GSYM word_add_n2w]
QED

val ag32_ffi_get_arg_length_loop_def = tDefine"ag32_ffi_get_arg_length_loop"`
  ag32_ffi_get_arg_length_loop s0 =
  let s = dfn'JumpIfZero (fSnd, Reg 7w, Imm 0w, Reg 6w) s0 in
  if (s0.R 6w = 0w) then s else
  let s = dfn'Normal (fSnd, 4w, Reg 4w, Imm 0w) s in
  let s = ag32_ffi_get_arg_length_loop1 s in
  let s = dfn'Normal (fDec, 6w, Reg 6w, Imm 1w) s in
  let s = dfn'JumpIfZero (fSnd, Imm (4w * -7w), Imm 0w, Imm 0w) s in
  ag32_ffi_get_arg_length_loop s`
  (wf_rel_tac`measure (λs. w2n (s.R 6w))`
   \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def,
         ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
         ag32Theory.dfn'LoadConstant_def,
         ag32Theory.dfn'StoreMEMByte_def, ag32Theory.dfn'LoadMEMByte_def,
         ag32Theory.ri2word_def, ag32Theory.incPC_def, APPLY_UPDATE_THM,
         ag32_ffi_get_arg_length_loop1_thm]
   \\ CASE_TAC \\ simp[APPLY_UPDATE_THM]
   \\ Cases_on`s0.R 6w` \\ fs[]
   \\ Cases_on`n` \\ fs[ADD1, GSYM word_add_n2w]);

val get_next_mem_arg_def = tDefine"get_next_mem_arg"`
  get_next_mem_arg (m:word32->word8) a acc =
    if m a = 0w ∨ ∀n. m (a + n2w n) ≠ 0w then (a, REVERSE acc)
    else get_next_mem_arg m (a + 1w) (m a :: acc)`
  (wf_rel_tac`measure(λ(m,a,acc). LEAST n. m (a + n2w n) = 0w)`
   \\ rw[]
   \\ numLib.LEAST_ELIM_TAC
   \\ Cases_on`n` \\ fs[ADD1]
   \\ conj_tac >- (qexists_tac`n'` \\ fs[GSYM word_add_n2w])
   \\ rw[]
   \\ numLib.LEAST_ELIM_TAC
   \\ conj_tac >- metis_tac[]
   \\ rw[]
   \\ fs[GSYM word_add_n2w]
   \\ Cases_on`n''` \\ fs[ADD1, GSYM word_add_n2w]
   \\ `¬(n' + 1 < n''' + 1)` by metis_tac[word_add_n2w, WORD_ADD_ASSOC]
   \\ fs[NOT_LESS]
   \\ `¬(n' < n)` by metis_tac[word_add_n2w, WORD_ADD_ASSOC]
   \\ fs[NOT_LESS]
   \\ `¬(n''' < n)` by metis_tac[word_add_n2w, WORD_ADD_ASSOC]
   \\ fs[NOT_LESS]);

val get_next_mem_arg_ind = theorem"get_next_mem_arg_ind";

Theorem get_next_mem_arg_LEAST:
   ∀m a acc. get_next_mem_arg m a acc =
    case OLEAST n. m (a + n2w n) = 0w of
    | NONE => (a, REVERSE acc)
    | SOME n => (a + n2w n, REVERSE acc ++ (GENLIST (λn. m (a + n2w n)) n))
Proof
  recInduct get_next_mem_arg_ind
  \\ rw[]
  \\ simp[Once get_next_mem_arg_def]
  \\ Cases_on`m a = 0w` \\ fs[]
  >- (
    simp[whileTheory.OLEAST_def]
    \\ IF_CASES_TAC \\ fs[]
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ gen_tac \\ strip_tac
    \\ Cases_on`n'` \\ fs[]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ IF_CASES_TAC
  >- ( simp[whileTheory.OLEAST_def] )
  \\ fs[]
  \\ simp[whileTheory.OLEAST_def]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- (
    Cases_on`n` \\ fs[]
    \\ fs[ADD1, GSYM word_add_n2w] )
  \\ IF_CASES_TAC \\ fs[]
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ gen_tac \\ strip_tac
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ gen_tac \\ strip_tac
  \\ qmatch_goalsub_rename_tac`_::_ _ n1 = _ _ n2`
  \\ `n2 = n1 + 1` suffices_by (
    simp[GSYM word_add_n2w]
    \\ simp[GSYM ADD1, GENLIST_CONS]
    \\ simp[o_DEF, ADD1, GSYM word_add_n2w] )
  \\ Cases_on`n2` \\ fs[ADD1]
  \\ fs[GSYM word_add_n2w]
  \\ qmatch_goalsub_rename_tac`n2 = n1`
  \\ `¬(n1 + 1 < n2 + 1)` by metis_tac[word_add_n2w, WORD_ADD_ASSOC]
  \\ `¬(n2 < n1)` by metis_tac[]
  \\ fs[]
QED

val get_mem_arg_def = Define`
  (get_mem_arg m a 0 = get_next_mem_arg m a []) ∧
  (get_mem_arg m a (SUC n) =
   let (a, _) = get_next_mem_arg m a [] in
     get_mem_arg m (a+1w) n)`;

Theorem ag32_ffi_get_arg_length_loop_thm:
   (s.R 6w = n2w (index+1)) ∧ index ≤ cline_size ∧
   (s.R 7w = n2w (4 * 8)) ∧
   (∃n. s.MEM (s.R 5w + n2w n) = 0w)
   ⇒
   ∃r8 r6 r5.
   (ag32_ffi_get_arg_length_loop s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_get_arg_length_loop_code);
              R := ((8w =+ r8)
                   ((4w =+ n2w (LENGTH (SND (get_mem_arg s.MEM (s.R 5w) index)) + 1))
                   ((6w =+ r6)
                   ((5w =+ r5) s.R)))) |>)
Proof
  qid_spec_tac`s`
  \\ Induct_on`index`
  >- (
    rw[]
    \\ simp[Once ag32_ffi_get_arg_length_loop_def]
    \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
            ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.dfn'JumpIfZero_def,
            ag32Theory.dfn'JumpIfNotZero_def, ag32_ffi_get_arg_length_loop1_thm,
            APPLY_UPDATE_THM]
    \\ CASE_TAC \\ simp[APPLY_UPDATE_THM]
    \\ fs[whileTheory.OLEAST_def]
    \\ simp[Once ag32_ffi_get_arg_length_loop_def, APPLY_UPDATE_THM]
    \\ simp[ag32Theory.dfn'JumpIfZero_def, ag32Theory.incPC_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[ag32Theory.ag32_state_component_equality]
    \\ simp[get_mem_arg_def] \\ rveq
    \\ simp[EVAL``ag32_ffi_get_arg_length_loop_code``]
    \\ qexists_tac`0w`
    \\ qexists_tac`0w`
    \\ qmatch_goalsub_abbrev_tac`5w =+ r5`
    \\ qexists_tac`r5`
    \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ rw[] \\ fs[]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ simp[get_next_mem_arg_LEAST, whileTheory.OLEAST_def]
    \\ IF_CASES_TAC \\ fs[])
  \\ rw[]
  \\ simp[Once ag32_ffi_get_arg_length_loop_def]
  \\ fs[EVAL``cline_size``]
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
          ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.dfn'JumpIfZero_def,
          ag32Theory.dfn'JumpIfNotZero_def, ag32_ffi_get_arg_length_loop1_thm,
          APPLY_UPDATE_THM]
  \\ CASE_TAC \\ simp[APPLY_UPDATE_THM]
  \\ fs[whileTheory.OLEAST_def]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_length_loop s'`
  \\ first_x_assum(qspec_then`s'`mp_tac)
  \\ simp[Abbr`s'`, APPLY_UPDATE_THM, ADD1, GSYM word_add_n2w]
  \\ impl_tac
  >- (
    rveq
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ rw[]
    \\ Cases_on`s.R 5w` \\ fs[word_add_n2w]
    \\ qexists_tac`dimword(:32)-1`
    \\ simp[]
    \\ fs[GSYM word_add_n2w]
    \\ EVAL_TAC \\ fs[word_add_n2w]
    \\ metis_tac[n2w_mod,EVAL``dimword(:32)``])
  \\ strip_tac \\ simp[]
  \\ pop_assum kall_tac
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qexists_tac`r8`
  \\ qexists_tac`r6`
  \\ qexists_tac`r5`
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[] \\ fs[]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[get_mem_arg_def, GSYM ADD1, UNCURRY]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp[get_next_mem_arg_LEAST, whileTheory.OLEAST_def]
  \\ IF_CASES_TAC \\ fs[]
QED

val ag32_ffi_get_arg_length_store_def = Define`
  ag32_ffi_get_arg_length_store s =
  let s = dfn'Normal (fDec, 4w, Reg 4w, Imm 1w) s in
  let s = dfn'StoreMEMByte(Reg 4w, Reg 3w) s in
  let s = dfn'Shift(shiftLR, 4w, Reg 4w, Imm 8w) s in
  let s = dfn'Normal(fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'StoreMEMByte(Reg 4w, Reg 3w) s in
  s`;

Theorem ag32_ffi_get_arg_length_store_thm:
   (s.R 4w = n2w (n+1)) ∧
   n < dimword(:32)
   ⇒
   ∃r4 r3.
   (ag32_ffi_get_arg_length_store s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_get_arg_length_store_code);
              R := ((4w =+ r4)
                   ((3w =+ r3) s.R));
              MEM := (((s.R 3w) =+ (n2w n))
                     (((s.R 3w + 1w) =+ (n2w (n DIV 256))) s.MEM)) |>)
Proof
  rw[ag32_ffi_get_arg_length_store_def]
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
          ag32Theory.incPC_def, ag32Theory.ALU_def,
          ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
          ag32Theory.dfn'StoreMEMByte_def,
          APPLY_UPDATE_THM]
  \\ rw[ag32Theory.ag32_state_component_equality]
  \\ qmatch_goalsub_abbrev_tac`4w =+ r4`
  \\ qmatch_goalsub_abbrev_tac`3w =+ r3`
  \\ qexists_tac`r4` \\ qexists_tac`r3`
  \\ simp[ag32_ffi_get_arg_length_store_code_def]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[Abbr`r3`] \\ fs[Abbr`r4`, GSYM word_add_n2w]
  >- (
    Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ qmatch_asmsub_rename_tac`m < _`
    \\ Cases_on`m = dimword(:32)-1` \\ fs[] )
  >- (
      qspecl_then [`n`,`8n`] mp_tac (INST_TYPE [alpha|->``:32``] n2w_DIV)>>
      simp[]>>
      blastLib.FULL_BBLAST_TAC)
  \\ blastLib.FULL_BBLAST_TAC
QED

val ag32_ffi_get_arg_length_def = Define`
  ag32_ffi_get_arg_length s =
    let s = ag32_ffi_get_arg_length_setup s in
    let s = ag32_ffi_get_arg_length_loop s in
    let s = ag32_ffi_get_arg_length_store s in
    ag32_ffi_return s`;

(* get_arg *)

val ag32_ffi_get_arg_entrypoint_def = Define`
  ag32_ffi_get_arg_entrypoint =
  ag32_ffi_get_arg_length_entrypoint + 4 * LENGTH ag32_ffi_get_arg_length_code`;

val ag32_ffi_get_arg_setup_code_def = Define`
  ag32_ffi_get_arg_setup_code =
    [LoadConstant(5w, F, n2w (ffi_code_start_offset - 1));
     StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "get_arg"))), Reg 5w);
     LoadConstant(5w, F, (n2w (startup_code_size + 4))); (* r5 contains pointer *)
     LoadMEMByte(6w, Reg 3w);
     Normal(fInc, 3w, Reg 3w, Imm 1w);
     LoadMEMByte(7w, Reg 3w);
     Shift(shiftLL, 7w, Reg 7w, Imm 8w);
     Normal(fDec, 3w, Reg 3w, Imm 1w);
     Normal(fAdd, 6w, Reg 6w, Reg 7w)] (* r6 contains index *)`;

val ag32_ffi_get_arg_find_code_def = Define`
  ag32_ffi_get_arg_find_code =
    [JumpIfZero (fSnd, Imm (4w * 6w), Imm 0w, Reg 6w);
     LoadMEMByte (8w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);
     JumpIfNotZero (fSnd, Imm (4w * -2w), Imm 0w, Reg 8w);
     Normal (fDec, 6w, Reg 6w, Imm 1w);
     JumpIfZero (fSnd, Imm (4w * -5w), Imm 0w, Imm 0w)]`;

val ag32_ffi_get_arg_store_code_def = Define`
  ag32_ffi_get_arg_store_code =
    [LoadMEMByte (8w, Reg 5w);
     JumpIfZero (fSnd, Imm (4w * 5w), Imm 0w, Reg 8w);
     StoreMEMByte(Reg 8w, Reg 3w);
     Normal(fInc, 3w, Reg 3w, Imm 1w);
     Normal(fInc, 5w, Reg 5w, Imm 1w);
     JumpIfZero (fSnd, Imm (4w * -5w), Imm 0w, Imm 0w)]`;

val ag32_ffi_get_arg_code_def = Define`
  ag32_ffi_get_arg_code =
    ag32_ffi_get_arg_setup_code ++
    ag32_ffi_get_arg_find_code ++
    ag32_ffi_get_arg_store_code ++
    ag32_ffi_return_code`;

val ag32_ffi_get_arg_setup_def = Define`
  ag32_ffi_get_arg_setup s =
  let s = dfn'LoadConstant(5w, F, n2w (ffi_code_start_offset - 1)) s in
  let s = dfn'StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "get_arg"))), Reg 5w) s in
  let s = dfn'LoadConstant(5w, F, (n2w (startup_code_size + 4))) s in
  let s = dfn'LoadMEMByte(6w, Reg 3w) s in
  let s = dfn'Normal(fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte(7w, Reg 3w) s in
  let s = dfn'Shift(shiftLL, 7w, Reg 7w, Imm 8w) s in
  let s = dfn'Normal(fDec, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'Normal(fAdd, 6w, Reg 6w, Reg 7w) s in
  s`;

Theorem ag32_ffi_get_arg_setup_thm:
   bytes_in_memory (s.R 3w) [l0; l1] s.MEM md ∧ n2w(ffi_code_start_offset - 1) ∉ md
   ⇒
   ∃r7 ov cf.
   (ag32_ffi_get_arg_setup s =
    s with <|
      MEM := ((n2w (ffi_code_start_offset - 1)) =+ n2w(THE(ALOOKUP FFI_codes "get_arg"))) s.MEM;
      PC := s.PC + n2w (4 * LENGTH ag32_ffi_get_arg_setup_code);
      R := ((5w =+ n2w (startup_code_size + 4))
           ((6w =+ n2w (256 * w2n l1 + w2n l0))
           ((7w =+ r7) s.R)));
      CarryFlag := cf; OverflowFlag := ov |>)
Proof
  rw[ag32_ffi_get_arg_setup_def]
  \\ simp[ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.incPC_def,
        ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def, ag32Theory.ri2word_def,
        ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
        ag32Theory.dfn'LoadConstant_def,
        ag32Theory.dfn'StoreMEMByte_def, APPLY_UPDATE_THM]
  \\ fs[bytes_in_memory_def, w2w_n2w, EVAL``ffi_code_start_offset``]
  \\ IF_CASES_TAC \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_goalsub_abbrev_tac`7w =+ r7`
  \\ qexists_tac`r7`
  \\ EVAL_TAC
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[] \\ fs[Abbr`r7`]
  \\ qmatch_goalsub_abbrev_tac`w2w (A) +  (w2w(B) <<8)`
  \\ simp[w2w_def,GSYM word_add_n2w]
  \\ fs[WORD_MUL_LSL]
  \\ simp[GSYM word_mul_n2w]
QED

val ag32_ffi_get_arg_find1_def = tDefine"ag32_ffi_get_arg_find1"`
  ag32_ffi_get_arg_find1 s =
    if (∀n. s.MEM (s.R 5w + n2w n) ≠ 0w) then s else
    let s = dfn'LoadMEMByte (8w, Reg 5w) s in
    let s0 = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
    let s = dfn'JumpIfNotZero (fSnd, Imm (4w * -2w), Imm 0w, Reg 8w) s0 in
    if (s0.R 8w = 0w) then s else ag32_ffi_get_arg_find1 s`
  (wf_rel_tac`measure (λs. LEAST n. (s.MEM (s.R 5w + n2w n) = 0w))`
   \\ rw[ag32Theory.dfn'LoadMEMByte_def,
         ag32Theory.incPC_def,
         ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def, ag32Theory.ri2word_def,
         ag32Theory.dfn'JumpIfNotZero_def]
   \\ fs[APPLY_UPDATE_THM]
   \\ Cases_on`s.R 5w` \\ fs[word_add_n2w]
   \\ numLib.LEAST_ELIM_TAC
   \\ Cases_on`n` \\ fs[] \\ rfs[ADD1]
   \\ conj_tac >- (qexists_tac`n''` \\ simp[])
   \\ rw[]
   \\ numLib.LEAST_ELIM_TAC
   \\ conj_tac >- (qexists_tac`n''+1` \\ simp[])
   \\ rw[]
   \\ Cases_on`n'''` \\ fs[ADD1]
   \\ Cases_on`n` \\ fs[ADD1]
   \\ `¬(n'''' < n''' + 1)` by metis_tac[ADD_ASSOC,ADD_COMM]
   \\ fs[NOT_LESS]);

Theorem ag32_ffi_get_arg_find1_thm:
   ag32_ffi_get_arg_find1 s =
   case OLEAST n. s.MEM (s.R 5w + n2w n) = 0w of
     NONE => s
   | SOME n =>
     s with <| PC := s.PC + n2w (4 * 3);
               R := ((8w =+ 0w)
                    ((5w =+ s.R 5w + n2w (n+1)) s.R)) |>
Proof
  reverse(rw[whileTheory.OLEAST_def])
  >- (
    rw[Once ag32_ffi_get_arg_find1_def]
    \\ fs[] \\ metis_tac[] )
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- (qexists_tac`n` \\ simp[])
  \\ pop_assum kall_tac
  \\ qid_spec_tac`s`
  \\ Induct_on`n`
  >- (
    rw[]
    \\ simp[Once ag32_ffi_get_arg_find1_def]
    \\ IF_CASES_TAC
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
    \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
            ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.dfn'LoadMEMByte_def,
            ag32Theory.dfn'JumpIfNotZero_def,
            APPLY_UPDATE_THM]
    \\ simp[ag32Theory.ag32_state_component_equality]
    \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ rw[] \\ fs[] )
  \\ rw[]
  \\ simp[Once ag32_ffi_get_arg_find1_def]
  \\ IF_CASES_TAC
  >- ( first_x_assum(qspec_then`SUC n`mp_tac) \\ rw[] )
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
          ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.dfn'LoadMEMByte_def,
          ag32Theory.dfn'JumpIfNotZero_def,
          APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    first_x_assum(qspec_then`0`mp_tac)
    \\ impl_tac >- simp[]
    \\ strip_tac
    \\ Cases_on`s.MEM (s.R 5w)` \\ fs[w2w_n2w]
    \\ qspecl_then[`7`,`0`,`n'`]mp_tac bitTheory.BITSLT_THM
    \\ strip_tac \\ fs[]
    \\ fs[bitTheory.BITS_ZERO3] )
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_find1 s'`
  \\ first_x_assum(qspec_then`s'`mp_tac)
  \\ simp[Abbr`s'`, APPLY_UPDATE_THM]
  \\ impl_tac
  >- (
    fs[ADD1, GSYM word_add_n2w] \\ rw[]
    \\ first_x_assum(qspec_then`m+1`mp_tac)
    \\ rw[GSYM word_add_n2w] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM, ADD1, GSYM word_add_n2w]
QED

val ag32_ffi_get_arg_find_def = tDefine"ag32_ffi_get_arg_find"`
  ag32_ffi_get_arg_find s0 =
  let s = dfn'JumpIfZero (fSnd, Imm (4w * 6w), Imm 0w, Reg 6w) s0 in
  if (s0.R 6w = 0w) then s else
  let s = ag32_ffi_get_arg_find1 s in
  let s = dfn'Normal (fDec, 6w, Reg 6w, Imm 1w) s in
  let s = dfn'JumpIfZero (fSnd, Imm (4w * -5w), Imm 0w, Imm 0w) s in
  ag32_ffi_get_arg_find s`
  (wf_rel_tac`measure (λs. w2n (s.R 6w))`
   \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def,
         ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
         ag32Theory.dfn'LoadConstant_def,
         ag32Theory.dfn'StoreMEMByte_def, ag32Theory.dfn'LoadMEMByte_def,
         ag32Theory.ri2word_def, ag32Theory.incPC_def, APPLY_UPDATE_THM,
         ag32_ffi_get_arg_find1_thm]
   \\ CASE_TAC \\ simp[APPLY_UPDATE_THM]
   \\ Cases_on`s0.R 6w` \\ fs[]
   \\ Cases_on`n` \\ fs[ADD1, GSYM word_add_n2w]);

Theorem ag32_ffi_get_arg_find_thm:
   (s.R 6w = n2w (index)) ∧ index ≤ cline_size ∧
   (∃n. s.MEM (s.R 5w + n2w n) = 0w)
   ⇒
   ∃r8 r6.
   (ag32_ffi_get_arg_find s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_get_arg_find_code);
              R := ((8w =+ r8)
                   ((5w =+ if 0 < index then FST (get_mem_arg s.MEM (s.R 5w) (index-1)) + 1w else s.R 5w)
                   ((6w =+ r6) s.R))) |>)
Proof
  qid_spec_tac`s`
  \\ Induct_on`index`
  >- (
    rw[]
    \\ simp[Once ag32_ffi_get_arg_find_def]
    \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
            ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.dfn'JumpIfZero_def,
            ag32Theory.dfn'JumpIfNotZero_def, ag32_ffi_get_arg_find1_thm,
            APPLY_UPDATE_THM]
    \\ simp[ag32Theory.ag32_state_component_equality]
    \\ simp[EVAL``ag32_ffi_get_arg_find_code``]
    \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ qexists_tac`s.R 8w`
    \\ qexists_tac`s.R 6w`
    \\ rw[] \\ fs[])
  \\ rw[]
  \\ simp[Once ag32_ffi_get_arg_find_def]
  \\ fs[EVAL``cline_size``]
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
          ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.dfn'JumpIfZero_def,
          ag32Theory.dfn'JumpIfNotZero_def, ag32_ffi_get_arg_find1_thm,
          APPLY_UPDATE_THM]
  \\ CASE_TAC \\ simp[APPLY_UPDATE_THM] \\ fs[whileTheory.OLEAST_def]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_find s'`
  \\ first_x_assum(qspec_then`s'`mp_tac)
  \\ simp[Abbr`s'`, APPLY_UPDATE_THM, ADD1, GSYM word_add_n2w]
  \\ impl_tac
  >- (
    rveq
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ rw[]
    \\ Cases_on`s.R 5w` \\ fs[word_add_n2w]
    \\ qexists_tac`dimword(:32)-1`
    \\ simp[]
    \\ fs[GSYM word_add_n2w]
    \\ EVAL_TAC \\ fs[word_add_n2w]
    \\ metis_tac[n2w_mod,EVAL``dimword(:32)``])
  \\ strip_tac \\ simp[]
  \\ pop_assum kall_tac
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qexists_tac`r8`
  \\ qexists_tac`r6`
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ gen_tac
  \\ IF_CASES_TAC \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- (
    rw[]
    \\ rw[get_mem_arg_def]
    \\ rw[get_next_mem_arg_LEAST]
    \\ rw[whileTheory.OLEAST_def]
    \\ fs[] )
  \\ rw[] \\ fs[]
  \\ Cases_on`index` \\ fs[get_mem_arg_def]
  \\ simp[UNCURRY]
  \\ simp[get_next_mem_arg_LEAST, whileTheory.OLEAST_def]
  \\ IF_CASES_TAC \\ fs[]
QED

val ag32_ffi_get_arg_store_def = tDefine"ag32_ffi_get_arg_store"`
  ag32_ffi_get_arg_store s =
  if ¬(∃n. (s.MEM (s.R 5w + n2w n) = 0w) ∧ (∀i. i ≤ n ⇒ s.R 3w ≠ s.R 5w + n2w i)) then s else
  let s0 = dfn'LoadMEMByte (8w, Reg 5w) s in
  let s = dfn'JumpIfZero (fSnd, Imm (4w * 5w), Imm 0w, Reg 8w) s0 in
  if s0.R 8w = 0w then s else
  let s = dfn'StoreMEMByte(Reg 8w, Reg 3w) s in
  let s = dfn'Normal(fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'Normal(fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'JumpIfZero (fSnd, Imm (4w * -5w), Imm 0w, Imm 0w) s in
  ag32_ffi_get_arg_store s`
  (wf_rel_tac`measure(λs. LEAST n. (s.MEM (s.R 5w + n2w n) = 0w))`
   \\ rw[ag32Theory.dfn'LoadMEMByte_def,
         ag32Theory.incPC_def,
         ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def, ag32Theory.ri2word_def,
         ag32Theory.dfn'StoreMEMByte_def,
         ag32Theory.dfn'JumpIfZero_def]
   \\ fs[APPLY_UPDATE_THM]
   \\ numLib.LEAST_ELIM_TAC
   \\ Cases_on`n` \\ fs[] \\ rfs[ADD1]
   \\ Cases_on`s.R 5w` \\ fs[word_add_n2w]
   \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
   \\ conj_tac
   >- (
     qexists_tac`n'` \\ fs[]
     \\ rw[] \\ fs[]
     \\ first_x_assum(qspec_then`n'+1`mp_tac)
     \\ rw[] )
   \\ gen_tac \\ strip_tac
   \\ numLib.LEAST_ELIM_TAC
   \\ conj_tac >- metis_tac[]
   \\ rw[]
   \\ fs[CaseEq"bool"]
   >- (
     Cases_on`s.MEM (n2w n)`
     \\ fs[w2w_n2w, word_extract_n2w]
     \\ qspecl_then[`7`,`0`]mp_tac bitTheory.BITSLT_THM
     \\ rw[] \\ fs[]
     \\ fs[bitTheory.BITS_ZERO3] )
   \\ `¬(n''' + 1 < n'''')` by metis_tac[ADD_ASSOC, ADD_COMM]
   \\ Cases_on`n''''` \\ fs[ADD1, NOT_LESS]
   \\ Cases_on`n''''' < n'''` \\ fs[]
   \\ first_x_assum drule
   \\ simp[]
   \\ Cases_on`s.MEM (n2w n)`
   \\ fs[w2w_n2w, word_extract_n2w]
   \\ qspecl_then[`7`,`0`]mp_tac bitTheory.BITSLT_THM
   \\ simp[]
   \\ fs[bitTheory.BITS_ZERO3]
   \\ `¬(n' + 1 < n''''' + 1)` by metis_tac[ADD_COMM, ADD_ASSOC]
   \\ fs[NOT_LESS]
   \\ last_x_assum(qspec_then`n'''''+1`mp_tac)
   \\ simp[]);

Theorem ag32_ffi_get_arg_store_thm:
   ((OLEAST n. s.MEM (s.R 5w + n2w n) = 0w) = SOME n) ∧
   (∀i. i ≤ n ⇒ s.R 5w + n2w i ≠ s.R 3w) ∧ Abbrev(w2n (s.R 3w) + n < dimword(:32))
   ⇒
   ∃r8 r5 r3.
   (ag32_ffi_get_arg_store s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_get_arg_store_code);
              R := ((8w =+ r8)
                   ((5w =+ r5)
                   ((3w =+ r3) s.R)));
              MEM := asm_write_bytearray (s.R 3w) (GENLIST (λn. s.MEM (s.R 5w + n2w n)) n) s.MEM |>)
Proof
  qid_spec_tac`s`
  \\ Induct_on`n` \\ rw[]
  >- (
    simp[Once ag32_ffi_get_arg_store_def]
    \\ fs[whileTheory.OLEAST_def]
    \\ qpat_x_assum`_ = 0n`mp_tac
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ gen_tac \\ strip_tac
    \\ strip_tac \\ rveq \\ fs[]
    \\ IF_CASES_TAC
    >- (
      first_x_assum(qspec_then`0`mp_tac)
      \\ simp[] )
    \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
            ag32Theory.incPC_def, ag32Theory.ALU_def,
            ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
            ag32Theory.dfn'StoreMEMByte_def, ag32Theory.dfn'LoadMEMByte_def,
            ag32Theory.dfn'JumpIfZero_def,
            APPLY_UPDATE_THM]
    \\ simp[ag32Theory.ag32_state_component_equality]
    \\ simp[asm_write_bytearray_def]
    \\ EVAL_TAC
    \\ qexists_tac`0w`
    \\ qexists_tac`s.R 5w`
    \\ qexists_tac`s.R 3w`
    \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM])
  \\ simp[Once ag32_ffi_get_arg_store_def]
  \\ IF_CASES_TAC
  >- (
    fs[whileTheory.OLEAST_def]
    \\ first_assum(qspec_then`n'`mp_tac)
    \\ simp_tac(srw_ss())[DISJ_EQ_IMP]
    \\ impl_tac >- fs[] \\ strip_tac
    \\ `¬(i ≤ SUC n)` by metis_tac[]
    \\ fs[NOT_LESS_EQUAL]
    \\ `SUC n < n'` by fs[]
    \\ first_assum(qspec_then`n`mp_tac)
    \\ simp_tac(srw_ss())[DISJ_EQ_IMP]
    \\ impl_tac >- (
      qpat_x_assum`_ = SUC _`mp_tac
      \\ numLib.LEAST_ELIM_TAC
      \\ conj_tac >- metis_tac[]
      \\ rw[] \\ fs[NOT_LESS_EQUAL]
      \\ strip_tac \\ rveq
      \\ `¬(n < SUC n)` by metis_tac[]
      \\ fs[] )
    \\ strip_tac
    \\ Cases_on`i < dimword(:32)` \\ fs[]
    \\ `¬(i' ≤ SUC n)` by metis_tac[]
    \\ fs[] )
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ri2word_def,
          ag32Theory.incPC_def, ag32Theory.ALU_def,
          ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
          ag32Theory.dfn'StoreMEMByte_def, ag32Theory.dfn'LoadMEMByte_def,
          ag32Theory.dfn'JumpIfZero_def,
          APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    Cases_on`s.MEM (s.R 5w)` \\ fs[w2w_n2w]
    \\ qspecl_then[`7`,`0`]mp_tac bitTheory.BITSLT_THM
    \\ disch_then(qspec_then`n'`mp_tac)
    \\ strip_tac \\ fs[]
    \\ fs[bitTheory.BITS_ZERO3, NOT_LESS_EQUAL, DISJ_EQ_IMP] \\ rw[]
    \\ fs[whileTheory.OLEAST_def]
    \\ qpat_x_assum`_ = SUC _`mp_tac
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ rw[] \\ fs[NOT_LESS_EQUAL]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_store s'`
  \\ last_x_assum(qspec_then`s'`mp_tac)
  \\ fs[whileTheory.OLEAST_def]
  \\ qpat_x_assum`_ = SUC _`mp_tac
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ gen_tac >> strip_tac
  \\ strip_tac \\ rveq
  \\ impl_tac
  >- (
    simp[Abbr`s'`, APPLY_UPDATE_THM]
    \\ simp[GSYM CONJ_ASSOC]
    \\ conj_tac
    >- (
      qexists_tac`n`
      \\ rw[] \\ fs[ADD1, GSYM word_add_n2w]
      \\ last_x_assum(qspec_then`n+1`mp_tac)
      \\ simp[GSYM word_add_n2w] )
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac
    >- (
      qexists_tac`n`
      \\ rw[] \\ fs[ADD1, GSYM word_add_n2w]
      \\ last_x_assum(qspec_then`n+1`mp_tac)
      \\ simp[GSYM word_add_n2w] )
    \\ gen_tac \\ strip_tac
    \\ fs[ADD1, GSYM word_add_n2w]
    \\ fs[DISJ_EQ_IMP]
    \\ `¬(n' < n + 1)` by metis_tac[]
    \\ fs[CaseEq"bool"]
    >- (
      Cases_on`s.MEM (s.R 5w)` \\ fs[w2w_n2w]
      \\ qspecl_then[`7`,`0`]mp_tac bitTheory.BITSLT_THM
      \\ disch_then(qspec_then`n''''`mp_tac)
      \\ strip_tac \\ fs[]
      \\ fs[bitTheory.BITS_ZERO3, NOT_LESS_EQUAL]
      \\ fs[word_extract_n2w]
      \\ fs[bitTheory.BITS_ZERO3, NOT_LESS_EQUAL] )
    \\ `¬(n''' + 1 < n + 1)` by metis_tac[word_add_n2w, WORD_ADD_ASSOC, WORD_ADD_COMM]
    \\ fs[NOT_LESS]
    \\ Cases_on`n''' ≤ n` \\ fs[NOT_LESS_EQUAL]
    >- ( Cases_on`s.R 3w` \\ fs[word_add_n2w,markerTheory.Abbrev_def] )
    \\ first_x_assum drule
    \\ simp[DISJ_EQ_IMP]
    \\ rw[]
    \\ last_x_assum(qspec_then`n+1`mp_tac)
    \\ simp[GSYM word_add_n2w] )
  \\ strip_tac
  \\ simp[]
  \\ pop_assum kall_tac
  \\ simp[Abbr`s'`, APPLY_UPDATE_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qexists_tac`r8`
  \\ qexists_tac`r5`
  \\ qexists_tac`r3`
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[]
  \\ rw[GENLIST_CONS]
  \\ simp[asm_write_bytearray_def, o_DEF, ADD1, GSYM word_add_n2w]
  \\ simp[APPLY_UPDATE_THM] \\ rw[]
  >- (
    irule asm_write_bytearray_unchanged_alt
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.MEM (s.R 5w)` \\ fs[w2w_n2w]
    \\ qspecl_then[`7`,`0`]mp_tac bitTheory.BITSLT_THM
    \\ simp[word_extract_n2w]
    \\ fs[bitTheory.BITS_ZERO3]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w] \\ rw[]
    \\ Cases_on`k < n` \\ fs[]
    \\ qmatch_goalsub_rename_tac`m ≠ _`
    \\ Cases_on`k + m + 1 < dimword(:32)` \\ fs[]
    \\ fs[markerTheory.Abbrev_def] )
  \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray a bs m x = _ _ bs' m' _`
  \\ `bs = bs'`
  by (
    simp[Abbr`bs`,Abbr`bs'`]
    \\ simp[LIST_EQ_REWRITE]
    \\ simp[Abbr`m`, Abbr`m'`, APPLY_UPDATE_THM]
    \\ rw[]
    \\ last_x_assum(qspec_then`x'+1`mp_tac)
    \\ simp[ADD1, GSYM word_add_n2w] )
  \\ qpat_x_assum`Abbrev(bs = _)`kall_tac
  \\ simp[Abbr`bs'`]
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ simp[Abbr`m'`,Abbr`m`,APPLY_UPDATE_THM]
QED

val ag32_ffi_get_arg_def = Define`
  ag32_ffi_get_arg s =
    let s = ag32_ffi_get_arg_setup s in
    let s = ag32_ffi_get_arg_find s in
    let s = ag32_ffi_get_arg_store s in
    ag32_ffi_return s`;

(* read *)

val ag32_ffi_read_entrypoint_def = Define`
  ag32_ffi_read_entrypoint =
  ag32_ffi_get_arg_entrypoint + 4 * LENGTH ag32_ffi_get_arg_code`;

val ag32_ffi_read_set_id_code_def = Define`
  ag32_ffi_read_set_id_code =
    [LoadConstant(5w, F, n2w (ffi_code_start_offset - 1));
     StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "read"))), Reg 5w)]`;

(* TODO: this would be shorter and maybe simpler using LoadMEM rather than LoadMEMByte *)
val ag32_ffi_read_check_conf_code_def = Define`
  ag32_ffi_read_check_conf_code = [
     Normal (fEqual, 6w, Reg 2w, Imm 8w); (* r6 = (LENGTH conf = 8) *)
     Normal (fSub, 4w, Reg 4w, Imm 4w);   (* r4 = LENGTH tll *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf7 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf7 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf7 = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf6::conf5...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf6 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf6 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..6} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf5::conf4...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf5 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf5 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..5} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf4::conf3...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf4 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf4 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..4} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf3::conf2...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf3 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf3 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..3} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf2::conf1::conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf2 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf2 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..2} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf1::conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf1 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf1 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..1} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf0 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf0 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w)]   (* r6 = (LENGTH conf = 8) ∧ w82n conf = 0 *)`;

val ag32_ffi_read_load_lengths_code_def = Define`
  ag32_ffi_read_load_lengths_code = [     (* r3 -> n1::n0::... *)
     LoadMEMByte (1w, Reg 3w);            (* r1 = [0w; 0w; 0w; n1] *)
     Shift (shiftLL, 1w, Reg 1w, Imm 8w); (* r1 = [0w; 0w; n1; 0w] *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> n0::... *)
     LoadMEMByte (8w, Reg 3w);            (* r8 = [0w; 0w; 0w; n0] *)
     Normal (fXor, 1w, Reg 1w, Reg 8w);   (* r1 = [0w; 0w; n1; n0] (= w22n [n1; n0]) *)
     Normal (fDec, 3w, Reg 3w, Imm 1w);   (* r3 -> n1::n0::... *)
     LoadConstant (8w, F, n2w (stdin_offset)); (* r8 = stdin_offset *)
     LoadMEM (5w, Reg 8w);                (* r5 = off *)
     Normal (fAdd, 8w, Reg 8w, Imm 4w);   (* r8 = stdin_offset + 4 *)
     LoadMEM (7w, Reg 8w);                (* r7 = LENGTH content *)
     Normal (fSub, 7w, Reg 7w, Reg 5w)]   (* r7 = LENGTH content - off *)`;

val ag32_ffi_read_check_length_code_def = Define`
  ag32_ffi_read_check_length_code = [
     Normal (fLower, 8w, Reg 4w, Reg 1w); (* r8 = LENGTH tll < w22n [n1; n0] *)
     Normal (fSub, 8w, Imm 1w, Reg 8w);   (* r8 = ¬(LENGTH tll < w22n [n1; n0] *)
     Normal (fAnd, 6w, Reg 6w, Reg 8w);   (* r6 = (LENGTH conf = 8) ∧ w82n conf < 3 ∧
                                                  w22n [n1; n0] ≤ LENGTH tll *)
     LoadConstant (4w, F, 4w * 26w);
     JumpIfZero (fAnd, Reg 4w, Reg 6w, Reg 8w)]`;

val ag32_ffi_read_num_written_code_def = Define`
  ag32_ffi_read_num_written_code = [
     StoreMEMByte(Imm 0w, Reg 3w);        (* r3 -> 0w::n0::pad1::pad2::tll *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> n0::pad1::pad2::tll *)
     LoadConstant (8w, F, n2w (output_buffer_size+1)); (* r8 = output_buffer_size+1 *)
     JumpIfZero (fLess, Imm 8w, Reg 8w, Reg 1w);  (* skip if ¬(output_buffer_size+1 < w22n [n1; n0]) *)
     Normal (fSnd, 1w, Reg 1w, Reg 8w);   (* r1 = MIN (output_buffer_size+1) n *)
     JumpIfZero (fLess, Imm 8w, Reg 7w, Reg 1w);  (* skip if ¬(LENGTH content - off < MIN (output_buffer_size+1) n) *)
     Normal (fSnd, 1w, Reg 1w, Reg 7w);   (* r1 = MIN n (MIN (LENGTH content - off) (output_buffer_size+1)) *)
     Shift (shiftLR, 8w, Reg 1w, Imm 8w); (* r8 = r1 DIV 256 *)
     StoreMEMByte (Reg 8w, Reg 3w);       (* r3 -> k1::pad1::pad2::tll *)
     Normal (fInc, 4w, Reg 3w, Imm 1w);   (* r4 -> pad1::pad2::tll *)
     StoreMEMByte (Reg 1w, Reg 4w);       (* r4 -> k0::pad2::tll *)
     Normal (fAdd, 8w, Reg 5w, Reg 1w);   (* r8 = off + k *)
     LoadConstant (2w, F, n2w stdin_offset); (* r2 = stdin_offset *)
     StoreMEM (Reg 8w, Reg 2w);           (* stdin pointer updated *)
     Normal (fAdd, 2w, Reg 2w, Imm 8w);   (* r2 -> stdin *)
     Normal (fAdd, 3w, Reg 2w, Reg 5w);   (* r3 -> DROP off stdin *)
     Normal (fAdd, 5w, Reg 4w, Imm 2w);   (* r5 -> tll *)
     LoadConstant (2w, F, 4w * 8w)]`;     (* r2 = 4*8 *)

val ag32_ffi_read_code_def = Define`
  ag32_ffi_read_code =
     ag32_ffi_read_set_id_code ++
     ag32_ffi_read_check_conf_code ++
     ag32_ffi_read_load_lengths_code ++
     ag32_ffi_read_check_length_code ++
     ag32_ffi_read_num_written_code ++
     ag32_ffi_copy_code ++
     [ StoreMEMByte (Imm 1w, Reg 3w) ] ++
     ag32_ffi_return_code`;

val ag32_ffi_read_set_id_def = Define`
  ag32_ffi_read_set_id s =
    let s = dfn'LoadConstant (5w, F, n2w (ffi_code_start_offset - 1)) s in
    let s = dfn'StoreMEMByte (Imm (n2w(THE(ALOOKUP FFI_codes "read"))), Reg 5w) s in
    s`;

Theorem ag32_ffi_read_set_id_thm:
     (ag32_ffi_read_set_id s =
      s with <| PC := s.PC + 8w;
                R := ((5w =+ n2w (ffi_code_start_offset - 1)) s.R);
                MEM := ((n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes "read"))) s.MEM |>)
Proof
  rw[ag32_ffi_read_set_id_def]
  \\ rw[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def]
  \\ rw[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.ri2word_def,
        ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ EVAL_TAC
QED

val ag32_ffi_read_check_conf_def = Define`
  ag32_ffi_read_check_conf s =
   let s = dfn'Normal (fEqual, 6w, Reg 2w, Imm 8w) s in
   let s = dfn'Normal (fSub, 4w, Reg 4w, Imm 4w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in s`;

Theorem ag32_ffi_read_check_conf_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧ (w2n (s.R 2w) = LENGTH conf)
   ⇒
   ∃ov cf r1 r2 r7.
   (ag32_ffi_read_check_conf s =
    s with <| R := ((6w =+ v2w[(LENGTH conf = 8) ∧ (w82n conf = 0)])
                   ((2w =+ (if (LENGTH conf = 8) ∧ (w82n conf = 0) then n2w (w82n conf) else r2))
                   ((4w =+ s.R 4w - 4w)
                   ((1w =+ r1)
                   ((7w =+ r7) s.R)))));
              PC := s.PC + n2w (4 * LENGTH ag32_ffi_read_check_conf_code);
              OverflowFlag := ov;
              CarryFlag := cf |>)
Proof
  rewrite_tac[ag32_ffi_read_check_conf_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fEqual`,`6w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fSub`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss()) [ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fEqual`,`7w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fAnd`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ ntac 25 (
    CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
    \\ simp_tac (srw_ss()) [Once LET_THM])
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[ag32_ffi_read_check_conf_code_def]
  \\ simp[APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ qexists_tac`s.R 1w + 7w`
  \\ qexists_tac`w2w (s.MEM (s.R 1w + 7w))`
  \\ qmatch_goalsub_abbrev_tac`if 7w = _ then r7 else _`
  \\ qexists_tac`r7`
  \\ reverse(Cases_on`LENGTH conf = 8`) \\ fs[]
  >- ( Cases_on`s.R 2w` \\ fs[] \\ rw[] \\ fs[] )
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ rveq
  \\ fs[bytes_in_memory_def] \\ rveq
  \\ simp[MarshallingTheory.w82n_def, LEFT_ADD_DISTRIB]
  \\ Cases_on`s.R 2w` \\ fs[] \\ rveq
  \\ Cases \\ fs[]
  \\ Cases_on`7=n` \\ fs[]
  \\ Cases_on`4=n` \\ fs[]
  \\ Cases_on`1=n` \\ fs[]
  \\ rfs[Abbr`r7`]
  \\ Cases_on`s.R 1w` \\ fs[]
  \\ Cases_on`2=n` \\ fs[]
  >- (
    rw[]
    \\ rw[GSYM word_add_n2w]
    \\ qmatch_asmsub_rename_tac`s.R 1w = n2w r1`
    \\ Cases_on`s.MEM (n2w r1)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 1w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 3w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 5w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 4w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 2w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 6w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 7w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`n` \\ fs[] )
  \\ Cases_on`6=n` \\ fs[]
  \\ rveq \\ rw[]
  \\ qmatch_asmsub_rename_tac`s.R 1w = n2w r1`
  \\ Cases_on`s.MEM (n2w r1)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 6w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 1w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 2w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 3w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 7w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 5w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 4w)` \\ fs[]
  \\ simp[w2w_n2w]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ qspecl_then[`7`,`0`]mp_tac bitTheory.BITSLT_THM
  \\ rw[]
  \\ TRY (
    qmatch_goalsub_rename_tac`BITS 7 0 m < _`
    \\ first_x_assum(qspec_then`m`mp_tac)
    \\ rw[] )
  \\ rw[bitTheory.BITS_ZERO3]
  \\ Cases_on`n` \\ fs[]
  \\ Cases_on`n'` \\ fs[]
  \\ Cases_on`n''` \\ fs[]
  \\ Cases_on`n'''` \\ fs[]
  \\ Cases_on`n''''` \\ fs[]
  \\ Cases_on`n''''''` \\ fs[]
  \\ Cases_on`n'''''''` \\ fs[]
  \\ Cases_on`n'''''` \\ fs[]
  \\ Cases_on`n` \\ fs[]
  \\ Cases_on`n'` \\ fs[]
  \\ simp[ADD1]
  \\ simp[word_lt_n2w]
  \\ qspecl_then[`31`,`n+3`]mp_tac bitTheory.NOT_BIT_GT_TWOEXP
  \\ simp[]
QED

val ag32_ffi_read_load_lengths_def = Define`
  ag32_ffi_read_load_lengths s =
  let s = dfn'LoadMEMByte (1w, Reg 3w) s in
  let s = dfn'Shift (shiftLL, 1w, Reg 1w, Imm 8w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte (8w, Reg 3w) s in
  let s = dfn'Normal (fXor, 1w, Reg 1w, Reg 8w) s in
  let s = dfn'Normal (fDec, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadConstant (8w, F, n2w (stdin_offset)) s in
  let s = dfn'LoadMEM (5w, Reg 8w) s in
  let s = dfn'Normal (fAdd, 8w, Reg 8w, Imm 4w) s in
  let s = dfn'LoadMEM (7w, Reg 8w) s in
  let s = dfn'Normal (fSub, 7w, Reg 7w, Reg 5w) s in
  s`;

Theorem ag32_ffi_read_load_lengths_thm:
   bytes_in_memory (s.R 3w) [n1; n0] s.MEM md ∧
   (get_mem_word s.MEM (n2w stdin_offset) = n2w off) ∧
   (get_mem_word s.MEM (n2w (stdin_offset + 4)) = n2w len) ∧ off ≤ len ∧ len ≤ stdin_size
   ⇒
   ∃ov cf r8.
   (ag32_ffi_read_load_lengths s =
    s with <| R := ((8w =+ r8)
                   ((5w =+ n2w(off))
                   ((7w =+ n2w(len - off))
                   ((1w =+ n2w(w22n[n1; n0])) s.R))));
              PC := s.PC + n2w (4 * LENGTH ag32_ffi_read_load_lengths_code);
              OverflowFlag := ov;
              CarryFlag := cf |>)
Proof
  rewrite_tac[ag32_ffi_read_load_lengths_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def,
        ag32Theory.ri2word_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.shift_def,
        ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`,`3w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fXor`,`1w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fDec`,`3w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [ag32Theory.dfn'LoadMEM_def, ag32Theory.incPC_def]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fAdd`,`8w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fSub`,`7w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8`
  \\ qhdtm_x_assum`get_mem_word`mp_tac
  \\ qhdtm_x_assum`get_mem_word`mp_tac
  \\ simp[get_mem_word_def, Abbr`r8`]
  \\ EVAL_TAC \\ rw[word_add_n2w, word_mul_n2w]
  \\ fs[EVAL``stdin_size``]
  \\ rw[] \\ fs[bytes_in_memory_def]
  >- (
    qmatch_goalsub_abbrev_tac`(len + p) MOD n = _`
    \\ `(len + p) MOD n = ((n+1) * len + p) MOD n`
    by (
      DEP_REWRITE_TAC[ADD_MOD]
      \\ simp[Abbr`n`] )
    \\ pop_assum SUBST1_TAC
    \\ `p = (n - 1) * off` by simp[Abbr`p`,Abbr`n`]
    \\ qpat_x_assum`Abbrev(p = _)`kall_tac
    \\ pop_assum SUBST1_TAC
    \\ rewrite_tac[RIGHT_ADD_DISTRIB, RIGHT_SUB_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac`x MOD n`
    \\ `x = n * (len + off) + (len - off)`
    by ( simp[Abbr`x`, LEFT_ADD_DISTRIB, Abbr`n`] )
    \\ pop_assum SUBST1_TAC
    \\ pop_assum kall_tac
    \\ `(n * (len + off) + (len - off)) MOD n = (0 + (len - off)) MOD n`
    by ( DEP_REWRITE_TAC[ADD_MOD] \\ simp[Abbr`n`] )
    \\ pop_assum SUBST1_TAC
    \\ simp[Abbr`n`] )
  \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[]
  \\ simp[w2w_n2w]
  \\ simp[bitTheory.BITS_ZERO3]
  \\ rw[GSYM word_add_n2w, GSYM word_mul_n2w]
  \\ simp[WORD_MUL_LSL]
  \\ DEP_REWRITE_TAC[GSYM WORD_ADD_XOR]
  \\ match_mp_tac (blastLib.BBLAST_PROVE
      ``w1 <+ 256w ==> (0w = (w1 && 256w * w2:word32))``)
  \\ fs [WORD_LO]
QED

val ag32_ffi_read_check_length_def = Define`
  ag32_ffi_read_check_length s =
   let s = dfn'Normal (fLower, 8w, Reg 4w, Reg 1w) s in
   let s = dfn'Normal (fSub, 8w, Imm 1w, Reg 8w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 8w) s in
   let s = dfn'LoadConstant (4w, F, 4w * 26w) s in
   let s = dfn'JumpIfZero (fAnd, Reg 4w, Reg 6w, Reg 8w) s in
   s`;

Theorem ag32_ffi_read_check_length_thm:
   (s.R 1w = n2w n) ∧ (s.R 4w = n2w ltll) ∧ (s.R 6w = v2w [cnd])
   ∧ ltll < dimword(:32) ∧ n < dimword(:32)
   ⇒
   ∃r4 r6 r8 cf ov.
   (ag32_ffi_read_check_length s =
    s with <| PC := if cnd ∧ n ≤ ltll
                    then s.PC + n2w (4 * LENGTH ag32_ffi_read_check_length_code)
                    else s.PC + n2w (4 * (LENGTH ag32_ffi_read_check_length_code + 25)) ;
              R := ((8w =+ r8)
                   ((6w =+ r6)
                   ((4w =+ r4) s.R)));
              CarryFlag := cf;
              OverflowFlag := ov |>)
Proof
  strip_tac
  \\ simp[ag32_ffi_read_check_length_def]
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.incPC_def,
          ag32Theory.ri2word_def, ag32Theory.norm_def,
          ag32Theory.dfn'LoadConstant_def, ag32Theory.dfn'JumpIfZero_def,
          ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`COND b1`
  \\ qmatch_goalsub_abbrev_tac`if b2 then _  + _ else _`
  \\ `b1 = ¬b2`
  by (
    unabbrev_all_tac
    \\ Cases_on`cnd` \\ fs[]
    \\ simp[NOT_LESS_EQUAL]
    \\ fs [WORD_LO]
    \\ Cases_on `ltll < n` \\ fs [])
  \\ qpat_x_assum`Abbrev(b1 = _)`kall_tac
  \\ simp[] \\ rveq
  \\ IF_CASES_TAC
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[ag32_ffi_read_check_length_code_def]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 4w = _ then r4 else _`
  \\ qexists_tac`r4`
  \\ qmatch_goalsub_abbrev_tac`if 6w = _ then r6 else _`
  \\ qexists_tac`r6`
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8`
  \\ rw[] \\ fs[]
QED

val ag32_ffi_read_num_written_def = Define`
  ag32_ffi_read_num_written s =
   let s = dfn'StoreMEMByte(Imm 0w, Reg 3w) s in
   let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
   let s0 = dfn'LoadConstant (8w, F, n2w (output_buffer_size+1)) s in
   let s = dfn'JumpIfZero (fLess, Imm 8w, Reg 8w, Reg 1w) s0 in
   let s0 = if s.PC = s0.PC + 4w then dfn'Normal (fSnd, 1w, Reg 1w, Reg 8w) s else s in
   let s = dfn'JumpIfZero (fLess, Imm 8w, Reg 7w, Reg 1w) s0 in
   let s = if s.PC = s0.PC + 4w then dfn'Normal (fSnd, 1w, Reg 1w, Reg 7w) s else s in
   let s = dfn'Shift (shiftLR, 8w, Reg 1w, Imm 8w) s in
   let s = dfn'StoreMEMByte (Reg 8w, Reg 3w) s in
   let s = dfn'Normal (fInc, 4w, Reg 3w, Imm 1w) s in
   let s = dfn'StoreMEMByte (Reg 1w, Reg 4w) s in
   let s = dfn'Normal (fAdd, 8w, Reg 5w, Reg 1w) s in
   let s = dfn'LoadConstant (2w, F, n2w stdin_offset) s in
   let s = dfn'StoreMEM (Reg 8w, Reg 2w) s in
   let s = dfn'Normal (fAdd, 2w, Reg 2w, Imm 8w) s in
   let s = dfn'Normal (fAdd, 3w, Reg 2w, Reg 5w) s in
   let s = dfn'Normal (fAdd, 5w, Reg 4w, Imm 2w) s in
   let s = dfn'LoadConstant (2w, F, 4w * 8w) s in
   s`;

Theorem ag32_ffi_read_num_written_thm:
   bytes_in_memory (s.R 3w) (n1::n0::pad1::pad2::tll) s.MEM md ∧
   (s.R 1w = n2w n) ∧
   (s.R 5w = n2w off) ∧
   (s.R 7w = n2w lcmo) ∧
   (k = MIN n (MIN lcmo (output_buffer_size+1)))
   ∧ n < dimword(:31) ∧ lcmo < dimword(:31)
   ⇒
   ∃r8 r4 cf ov.
   (ag32_ffi_read_num_written s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_read_num_written_code);
              MEM := set_mem_word (n2w stdin_offset) (n2w (off + k))
                       (asm_write_bytearray (s.R 3w) (0w::(n2w2 k)) s.MEM);
              R := ((8w =+ r8)
                   ((4w =+ r4)
                   ((3w =+ n2w (stdin_offset + 8 + off))
                   ((5w =+ s.R 3w + 4w)
                   ((2w =+ 4w * 8w)
                   ((1w =+ n2w k) s.R))))));
              CarryFlag := cf;
              OverflowFlag := ov |>)
Proof
  rewrite_tac[ag32_ffi_read_num_written_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'StoreMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def, ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`,`3w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'LoadConstant_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'JumpIfZero_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac`if cnd then _ else _`
  \\ qmatch_asmsub_abbrev_tac`cnd = ((if cnd' then _ else _).PC = _)`
  \\ `cnd = ¬cnd'` by ( rw[Abbr`cnd`,Abbr`cnd'`] )
  \\ qpat_x_assum`Abbrev(cnd = _)`kall_tac \\ rveq
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss())[]))
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fSnd`,`1w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac `LET _ s0`
  \\ qmatch_asmsub_abbrev_tac`Abbrev(s0 = if _ then _ else s1)`
  \\ `s0 = s1 with R := ((1w =+ n2w (MIN n (output_buffer_size+1))) s1.R)`
  by (
    simp[Abbr`s0`,Abbr`s1`,ag32Theory.ag32_state_component_equality,COND_RAND,Abbr`cnd'`]
    \\ simp[v2w_sing, GSYM COND_RAND,APPLY_UPDATE_THM,FUN_EQ_THM]
    \\ rw[] \\ fs[APPLY_UPDATE_THM]
    \\ pop_assum mp_tac \\ rw[]
    \\ fs[w2w_n2w, EVAL``output_buffer_size``,word_lt_n2w] \\ rfs[]
    \\ rw[MIN_DEF]
    \\ fs [bitTheory.BIT_def,bitTheory.BITS_THM]
    \\ rfs[LESS_DIV_EQ_ZERO] )
  \\ qpat_x_assum`Abbrev(s0 = _ )`kall_tac
  \\ pop_assum SUBST_ALL_TAC
  \\ simp_tac(srw_ss())[Abbr`s1`]
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qunabbrev_tac`cnd'`
  \\ qmatch_goalsub_abbrev_tac`if cnd' then _ else _`
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac`if cnd then _ else _`
  \\ `cnd = ¬cnd'` by ( rw[Abbr`cnd`,Abbr`cnd'`] )
  \\ qpat_x_assum`Abbrev(cnd = _)`kall_tac \\ rveq
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss())[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac `LET _ s0`
  \\ qmatch_asmsub_abbrev_tac`Abbrev(s0 = if _ then _ else s1)`
  \\ `s0 = s1 with R := ((1w =+ n2w (MIN n (MIN lcmo (output_buffer_size+1)))) s1.R)`
  by (
    simp[Abbr`s0`,Abbr`s1`,ag32Theory.ag32_state_component_equality,COND_RAND,Abbr`cnd'`]
    \\ simp[v2w_sing, GSYM COND_RAND,APPLY_UPDATE_THM,FUN_EQ_THM]
    \\ `¬BIT 31 n ∧ ¬BIT 31 lcmo` by (
      fs [bitTheory.BIT_def,bitTheory.BITS_THM] \\ rfs[LESS_DIV_EQ_ZERO] )
    \\ rw[] \\ fs[APPLY_UPDATE_THM] \\ rfs[]
    \\ pop_assum mp_tac \\ rw[]
    \\ fs[MIN_DEF] \\ rw[] \\ fs[word_lt_n2w, EVAL``output_buffer_size``] \\ rfs[]
    \\ fs[] )
  \\ qpat_x_assum`Abbrev(s0 = _ )`kall_tac
  \\ pop_assum SUBST_ALL_TAC
  \\ simp_tac(srw_ss())[Abbr`s1`]
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def, ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`,`4w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fAdd`,`8w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'StoreMEM_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def, ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fAdd`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[EVAL``4 * LENGTH ag32_ffi_read_num_written_code``]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ fs[EVAL``output_buffer_size``,EVAL``stdin_offset``]
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8` \\ simp[Abbr`r8`]
  \\ qmatch_goalsub_abbrev_tac`if 4w = _ then r4 else _`
  \\ qexists_tac`r4` \\ simp[Abbr`r4`]
  \\ (reverse conj_tac >- (rw[] \\ fs[word_add_n2w]))
  \\ simp[set_mem_word_def, APPLY_UPDATE_THM]
  \\ simp[asm_write_bytearray_def, MarshallingTheory.n2w2_def, APPLY_UPDATE_THM]
  \\ rw[] \\ fs[word_add_n2w] \\ fs[addressTheory.WORD_EQ_ADD_CANCEL]
  >- blastLib.BBLAST_TAC
  \\ match_mp_tac (blastLib.BBLAST_PROVE
      ``w <+ 256w:word32 /\ (k = w2w w) ==> ((7 >< 0) w = k:word8)``)
  \\ rewrite_tac [w2w_def,w2n_lsr,WORD_LO]
  \\ fs [DIV_LT_X]
QED

val ag32_ffi_read_def = Define`
  ag32_ffi_read s =
  let s = ag32_ffi_read_set_id s in
  let s = ag32_ffi_read_check_conf s in
  let s0 = ag32_ffi_read_load_lengths s in
  let s = ag32_ffi_read_check_length s0 in
  let s =
    if s.PC = s0.PC + n2w (4 * LENGTH ag32_ffi_read_check_length_code) then
      let s = ag32_ffi_read_num_written s in
      let s = ag32_ffi_copy s in s
    else
      dfn'StoreMEMByte (Imm 1w, Reg 3w) s
  in
    ag32_ffi_return s`;

(* write
   PC is ffi_code_start_offset + ag32_ffi_write_entrypoint
   r1 contains pointer to byte array (conf) with the output id
   r2 contains length of r1 (should be 8)
   r3 contains pointer to byte array n1::n0::off1::off0::tll
   r4 contains LENGTH tll + 4
   postconditions:
     * written (THE (ALOOKUP FFI_codes "write")) at (n2w (ffi_code_start_offset - 1))
     * if the following conditions hold
         - r2 contains 8
         - w82n conf ≤ 2
         - w22n [off1; off0] ≤ LENGTH tll
         - w22n [n1; n0] ≤ LENGTH tll - w22n [off1; off0]
       then
         - write 0w::n2w2(k) to array pointed by r3
         - write conf ++ [0w;0w;n1;n0] ++ (TAKE k (DROP (w22n [off1; off0]) tll))
           to n2w output_offset
         where k = MIN (w22n [n1; n0]) output_buffer_size
       else
         - write 1w to the first byte pointed by r3
         - do not touch anything else in memory
     * r1,..,r8 are set to 0 and carry and overflow unset
     * exit happens at the end of the code, by jumping to r0
*)

val ag32_ffi_write_entrypoint_def = Define`
  ag32_ffi_write_entrypoint =
  ag32_ffi_read_entrypoint + 4 * LENGTH ag32_ffi_read_code`;

val ag32_ffi_write_set_id_code_def = Define`
  ag32_ffi_write_set_id_code =
    [Jump (fAdd, 5w, Imm 4w);
     LoadConstant(6w, F, n2w (ag32_ffi_write_entrypoint + 4));
     Normal (fSub, 5w, Reg 5w, Reg 6w);   (* r5 = ffi_code_start_offset *)
     Normal (fDec, 5w, Reg 5w, Imm 0w);
     StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "write"))), Reg 5w)]`;

val ag32_ffi_write_check_conf_code_def = Define`
  ag32_ffi_write_check_conf_code = [
     Normal (fEqual, 6w, Reg 2w, Imm 8w); (* r6 = (LENGTH conf = 8) *)
     Normal (fSub, 4w, Reg 4w, Imm 4w);   (* r4 = LENGTH tll *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf7 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf7 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf7 = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf6::conf5...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf6 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf6 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..6} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf5::conf4...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf5 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf5 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..5} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf4::conf3...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf4 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf4 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..4} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf3::conf2...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf3 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf3 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..3} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf2::conf1::conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf2 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf2 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..2} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf1::conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf1 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf1 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..1} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf0 *)
     Normal (fLess, 7w, Reg 2w, Imm 3w);  (* r7 = conf0 < 3 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ w82n conf < 3 *)
     Normal (fLess, 7w, Imm 0w, Reg 2w);  (* r7 = 0 < conf0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w)]   (* r6 = (LENGTH conf = 8) ∧ 0 < w82n conf < 3 *)`;

val ag32_ffi_write_load_noff_code_def = Define`
  ag32_ffi_write_load_noff_code = [       (* r3 -> n1::n0::off1::off0::... *)
     LoadMEMByte (1w, Reg 3w);            (* r1 = [0w; 0w; 0w; n1] *)
     Shift (shiftLL, 1w, Reg 1w, Imm 8w); (* r1 = [0w; 0w; n1; 0w] *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> n0::off1::off0::... *)
     LoadMEMByte (8w, Reg 3w);            (* r8 = [0w; 0w; 0w; n0] *)
     Normal (fXor, 1w, Reg 1w, Reg 8w);   (* r1 = [0w; 0w; n1; n0] (= w22n [n1; n0]) *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> off1::off0::... *)
     LoadMEMByte (7w, Reg 3w);            (* r7 = [0w; 0w; 0w; off1] *)
     Shift (shiftLL, 7w, Reg 7w, Imm 8w); (* r7 = [0w; 0w; off1; 0w] *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> off0::... *)
     LoadMEMByte (8w, Reg 3w);            (* r8 = [0w; 0w; 0w; off0] *)
     Normal (fXor, 7w, Reg 7w, Reg 8w);   (* r7 = [0w; 0w; off1; off0] (= w22n [off1; off0]) *)
     Normal (fSub, 3w, Reg 3w, Imm 3w)]   (* r3 -> n1::n0::off1::off0::... *)`;

val ag32_ffi_write_check_lengths_code_def = Define`
  ag32_ffi_write_check_lengths_code = [
     Normal (fLower, 8w, Reg 4w, Reg 7w); (* r8 = LENGTH tll < w22n [off1; off0] *)
     Normal (fSub, 8w, Imm 1w, Reg 8w);   (* r8 = ¬(LENGTH tll < w22n [off1; off0] *)
     Normal (fAnd, 6w, Reg 6w, Reg 8w);   (* r6 = (LENGTH conf = 8) ∧ w82n conf < 3 ∧
                                                  w22n [off1; off0] ≤ LENGTH tll *)
     Normal (fSub, 4w, Reg 4w, Reg 7w);   (* r4 = LENGTH tll - w22n [off1; off0] *)
     Normal (fLower, 8w, Reg 4w, Reg 1w); (* r8 = LENGTH tll - w22n [off1; off0] < w22n [n1; n0] *)
     Normal (fSub, 8w, Imm 1w, Reg 8w);   (* r8 = ¬(LENGTH tll - w22n [off1; off0] < w22n [n1; n0] *)
     LoadConstant(4w, F, n2w ((ffi_code_start_offset - 1) - output_offset));
     Normal (fSub, 5w, Reg 5w, Reg 4w);   (* r5 = output_offset *)
     LoadConstant (4w, F, 4w * 34w);
     JumpIfZero (fAnd, Reg 4w, Reg 6w, Reg 8w)]`;

val ag32_ffi_write_write_header_code_def = Define`
  ag32_ffi_write_write_header_code = [
     StoreMEM (Imm 0w, Reg 5w);
     Normal (fAdd, 5w, Reg 5w, Imm 4w);   (* r5 = output_offset + 4 *)
     Shift (shiftLL, 2w, Reg 2w, Imm 24w);(* r2 = [conf0; 0w; 0w; 0w] *)
     StoreMEM (Reg 2w, Reg 5w);
     Normal (fAdd, 5w, Reg 5w, Imm 4w);   (* r5 = output_offset + 8 *)
     StoreMEMByte (Imm 0w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);   (* r5 = output_offset + 9 *)
     StoreMEMByte (Imm 0w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);   (* r5 = output_offset + 10 *)
     Shift (shiftLR, 2w, Reg 1w, Imm 8w); (* r2 = [0w; 0w; 0w; n1] *)
     StoreMEMByte (Reg 2w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);   (* r5 = output_offset + 11 *)
     StoreMEMByte (Reg 1w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);   (* r5 = output_offset + 12 *)
     StoreMEMByte (Imm 0w, Reg 3w)]`;

val ag32_ffi_write_num_written_code_def = Define`
  ag32_ffi_write_num_written_code = [
     (* calculate k and write to mutable array *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> n0::off1::off0::tll *)
     LoadConstant (8w, F, n2w output_buffer_size); (* r8 = output_buffer_size *)
     JumpIfZero (fLess, Imm 8w, Reg 8w, Reg 1w);  (* skip if ¬(output_buffer_size < w22n [n1; n0]) *)
     Normal (fSnd, 1w, Reg 1w, Reg 8w);   (* r1 = MIN output_buffer_size (w22n [n1; n0]) *)
     Shift (shiftLR, 8w, Reg 1w, Imm 8w); (* r8 = r1 DIV 256 *)
     StoreMEMByte (Reg 8w, Reg 3w);
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> off1::off0::tll *)
     StoreMEMByte (Reg 1w, Reg 3w);
     Normal (fAdd, 3w, Reg 3w, Imm 2w);
     Normal (fAdd, 3w, Reg 3w, Reg 7w);   (* r3 -> DROP off tll *)
     LoadConstant (2w, F, 4w * 9w)]`;

val ag32_ffi_write_code_def = Define`
  ag32_ffi_write_code =
     ag32_ffi_write_set_id_code ++
     ag32_ffi_write_check_conf_code ++
     ag32_ffi_write_load_noff_code ++
     ag32_ffi_write_check_lengths_code ++
     ag32_ffi_write_write_header_code ++
     ag32_ffi_write_num_written_code ++
     ag32_ffi_copy_code ++
     [ (* error case *)
      StoreMEMByte (Imm 1w, Reg 3w);
      StoreMEMByte (Imm 1w, Reg 5w) ] ++
     ag32_ffi_return_code`;

val ag32_ffi_write_set_id_def = Define`
  ag32_ffi_write_set_id s =
    let s = dfn'Jump (fAdd, 5w, Imm 4w) s in
    let s = dfn'LoadConstant (6w, F, n2w (ag32_ffi_write_entrypoint + 4)) s in
    let s = dfn'Normal (fSub, 5w, Reg 5w, Reg 6w) s in
    let s = dfn'Normal (fDec, 5w, Reg 5w, Imm 0w) s in
    let s = dfn'StoreMEMByte (Imm (n2w(THE(ALOOKUP FFI_codes "write"))), Reg 5w) s in
    s`;

Theorem ag32_ffi_write_set_id_thm:
   (s.PC = n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint))
    ⇒
    ∃cf ov r6.
     (ag32_ffi_write_set_id s =
      s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_set_id_code);
                R := ((6w =+ r6) ((5w =+ (n2w (ffi_code_start_offset - 1))) s.R));
                CarryFlag := cf;
                OverflowFlag := ov;
                MEM := ((n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes "write"))) s.MEM |>)
Proof
  rw[ag32_ffi_write_set_id_def]
  \\ rw[ag32Theory.dfn'Jump_def, ag32Theory.ALU_def, ag32Theory.ri2word_def]
  \\ qmatch_goalsub_abbrev_tac`n2w off`
  \\ rw[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def]
  \\ rw[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def,
        ag32Theory.ri2word_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.ri2word_def,
        ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ rw[ag32Theory.ag32_state_component_equality, APPLY_UPDATE_THM, FUN_EQ_THM, Abbr`off`]
  \\ EVAL_TAC
  \\ rw[]
  \\ metis_tac[]
QED

val ag32_ffi_write_check_conf_def = Define`
  ag32_ffi_write_check_conf s =
   let s = dfn'Normal (fEqual, 6w, Reg 2w, Imm 8w) s in
   let s = dfn'Normal (fSub, 4w, Reg 4w, Imm 4w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fLess, 7w, Reg 2w, Imm 3w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fLess, 7w, Imm 0w, Reg 2w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   s`;

Theorem ag32_ffi_write_check_conf_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧ (w2n (s.R 2w) = LENGTH conf)
   ⇒
   ∃ov cf r1 r2 r7.
   (ag32_ffi_write_check_conf s =
    s with <| R := ((6w =+ v2w[(LENGTH conf = 8) ∧ w82n conf < 3 ∧ 0 < w82n conf])
                   ((2w =+ (if (LENGTH conf = 8) ∧ w82n conf < 3 ∧ 0 < w82n conf then n2w (w82n conf) else r2))
                   ((4w =+ s.R 4w - 4w)
                   ((1w =+ r1)
                   ((7w =+ r7) s.R)))));
              PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_check_conf_code);
              OverflowFlag := ov;
              CarryFlag := cf |>)
Proof
  rewrite_tac[ag32_ffi_write_check_conf_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fEqual`,`6w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fSub`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss()) [ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fEqual`,`7w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fAnd`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ ntac 25 (
    CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
    \\ simp_tac (srw_ss()) [Once LET_THM])
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[ag32_ffi_write_check_conf_code_def]
  \\ simp[APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ qexists_tac`s.R 1w + 7w`
  \\ qexists_tac`w2w (s.MEM (s.R 1w + 7w))`
  \\ qmatch_goalsub_abbrev_tac`if 7w = _ then r7 else _`
  \\ qexists_tac`r7`
  \\ reverse(Cases_on`LENGTH conf = 8`) \\ fs[]
  >- ( Cases_on`s.R 2w` \\ fs[] \\ rw[] \\ fs[] )
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ rveq
  \\ fs[bytes_in_memory_def] \\ rveq
  \\ simp[MarshallingTheory.w82n_def, LEFT_ADD_DISTRIB]
  \\ Cases_on`s.R 2w` \\ fs[] \\ rveq
  \\ Cases \\ fs[]
  \\ Cases_on`7=n` \\ fs[]
  \\ Cases_on`4=n` \\ fs[]
  \\ Cases_on`1=n` \\ fs[]
  \\ rfs[Abbr`r7`]
  \\ Cases_on`s.R 1w` \\ fs[]
  \\ Cases_on`2=n` \\ fs[]
  >- (
    rw[]
    \\ rw[GSYM word_add_n2w]
    \\ qmatch_asmsub_rename_tac`s.R 1w = n2w r1`
    \\ Cases_on`s.MEM (n2w r1)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 1w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 3w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 5w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 4w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 2w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 6w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 7w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`n` \\ fs[] )
  \\ Cases_on`6=n` \\ fs[]
  \\ rveq \\ rw[]
  \\ qmatch_asmsub_rename_tac`s.R 1w = n2w r1`
  \\ Cases_on`s.MEM (n2w r1)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 6w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 1w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 2w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 3w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 7w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 5w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 4w)` \\ fs[]
  \\ simp[w2w_n2w]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ qspecl_then[`7`,`0`]mp_tac bitTheory.BITSLT_THM
  \\ rw[]
  \\ TRY (
    qmatch_goalsub_rename_tac`BITS 7 0 m < _`
    \\ first_x_assum(qspec_then`m`mp_tac)
    \\ rw[] )
  \\ rw[bitTheory.BITS_ZERO3]
  \\ Cases_on`n` \\ fs[]
  \\ Cases_on`n'` \\ fs[]
  \\ Cases_on`n''` \\ fs[]
  \\ Cases_on`n'''` \\ fs[]
  \\ Cases_on`n''''` \\ fs[]
  \\ Cases_on`n''''''` \\ fs[]
  \\ Cases_on`n'''''''` \\ fs[]
  \\ Cases_on`n'''''` \\ fs[]
  \\ Cases_on`n` \\ fs[]
  \\ Cases_on`n'` \\ fs[]
  \\ simp[ADD1]
  \\ simp[word_lt_n2w]
  \\ qspecl_then[`31`,`n+3`]mp_tac bitTheory.NOT_BIT_GT_TWOEXP
  \\ simp[]
QED

Theorem ag32_ffi_write_check_conf_MEM:
   (ag32_ffi_write_check_conf s).MEM = s.MEM
Proof
  rw[ag32_ffi_write_check_conf_def, dfn'Normal_MEM, dfn'LoadMEMByte_MEM]
QED

Theorem ag32_ffi_write_check_conf_PC:
   (ag32_ffi_write_check_conf s).PC = s.PC + 140w
Proof
  rw[ag32_ffi_write_check_conf_def, dfn'Normal_PC, dfn'LoadMEMByte_PC]
QED

Theorem ag32_ffi_write_check_conf_R:
   ((ag32_ffi_write_check_conf s).R 3w = s.R 3w) ∧
   ((ag32_ffi_write_check_conf s).R 5w = s.R 5w)
Proof
  rw[ag32_ffi_write_check_conf_def,
     ag32Theory.dfn'Normal_def, ag32Theory.ri2word_def,
     ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.norm_def,
     ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
     ag32Theory.dfn'LoadConstant_def, ag32Theory.dfn'JumpIfZero_def,
     APPLY_UPDATE_THM]
QED

val ag32_ffi_write_load_noff_def = Define`
  ag32_ffi_write_load_noff s =
  let s = dfn'LoadMEMByte (1w, Reg 3w) s in
  let s = dfn'Shift (shiftLL, 1w, Reg 1w, Imm 8w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte (8w, Reg 3w) s in
  let s = dfn'Normal (fXor, 1w, Reg 1w, Reg 8w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte (7w, Reg 3w) s in
  let s = dfn'Shift (shiftLL, 7w, Reg 7w, Imm 8w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte (8w, Reg 3w) s in
  let s = dfn'Normal (fXor, 7w, Reg 7w, Reg 8w) s in
  let s = dfn'Normal (fSub, 3w, Reg 3w, Imm 3w) s in
  s`;

Theorem ag32_ffi_write_load_noff_thm:
   bytes_in_memory (s.R 3w) (n1::n0::off1::off0::tll) s.MEM md
   ⇒
   ∃r8 ov cf.
   (ag32_ffi_write_load_noff s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_load_noff_code);
              OverflowFlag := ov;
              CarryFlag := cf;
              R := ((8w =+ r8)
                   ((1w =+ n2w (w22n [n1; n0]))
                   ((7w =+ n2w (w22n [off1; off0])) s.R))) |>)
Proof
  rewrite_tac[ag32_ffi_write_load_noff_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[`1w`]ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`shiftLL`,`1w`]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`8w`]ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fXor`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`7w`]ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`shiftLL`,`7w`]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8`
  \\ conj_tac >- EVAL_TAC
  \\ rw[MarshallingTheory.w22n_def,Abbr`r8`] \\ fs[]
  >- (
    Cases_on`off0` \\ Cases_on`off1` \\ fs[]
    \\ fs[bytes_in_memory_def] \\ rw[]
    \\ simp[w2w_n2w]
    \\ simp[bitTheory.BITS_ZERO3]
    \\ rw[GSYM word_add_n2w, GSYM word_mul_n2w]
    \\ simp[WORD_MUL_LSL]
    \\ DEP_REWRITE_TAC[GSYM WORD_ADD_XOR]
    \\ match_mp_tac (blastLib.BBLAST_PROVE
        ``w1 <+ 256w ==> (0w = (w1 && 256w * w2:word32))``)
    \\ fs [WORD_LO] )
  \\ fs[bytes_in_memory_def]
  \\ rw[]
  \\ Cases_on`s.MEM (s.R 1w)` \\ fs[]
  \\ Cases_on`s.MEM (s.R 3w)` \\ fs[]
  \\ Cases_on`s.MEM (s.R 3w + 1w)` \\ fs[]
  \\ simp[WORD_MUL_LSL]
  \\ simp[w2w_n2w]
  \\ simp[bitTheory.BITS_ZERO3]
  \\ DEP_REWRITE_TAC[GSYM WORD_ADD_XOR]
  \\ simp[GSYM word_mul_n2w, GSYM word_add_n2w]
  \\ match_mp_tac (blastLib.BBLAST_PROVE
      ``w1 <+ 256w ==> (0w = (w1 && 256w * w2:word32))``)
  \\ fs [WORD_LO]
QED

Theorem ag32_ffi_write_load_noff_MEM:
   (ag32_ffi_write_load_noff s).MEM = s.MEM
Proof
  rw[ag32_ffi_write_load_noff_def, dfn'Normal_MEM, dfn'LoadMEMByte_MEM, dfn'Shift_MEM]
QED

Theorem ag32_ffi_write_load_noff_PC:
   (ag32_ffi_write_load_noff s).PC = s.PC + 48w
Proof
  rw[ag32_ffi_write_load_noff_def, dfn'Normal_PC, dfn'LoadMEMByte_PC, dfn'Shift_PC]
QED

Theorem ag32_ffi_write_load_noff_R:
   ((ag32_ffi_write_load_noff s).R 3w = s.R 3w) ∧
   ((ag32_ffi_write_load_noff s).R 5w = s.R 5w)
Proof
  rw[ag32_ffi_write_load_noff_def,
     ag32Theory.dfn'Normal_def, ag32Theory.ri2word_def,
     ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.norm_def,
     ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
     ag32Theory.dfn'LoadConstant_def, ag32Theory.dfn'JumpIfZero_def,
     APPLY_UPDATE_THM]
QED

val ag32_ffi_write_check_lengths_def = Define`
  ag32_ffi_write_check_lengths s =
  let s = dfn'Normal (fLower, 8w, Reg 4w, Reg 7w) s in
  let s = dfn'Normal (fSub, 8w, Imm 1w, Reg 8w) s in
  let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 8w) s in
  let s = dfn'Normal (fSub, 4w, Reg 4w, Reg 7w) s in
  let s = dfn'Normal (fLower, 8w, Reg 4w, Reg 1w) s in
  let s = dfn'Normal (fSub, 8w, Imm 1w, Reg 8w) s in
  let s = dfn'LoadConstant(4w, F, n2w ((ffi_code_start_offset - 1) - output_offset)) s in
  let s = dfn'Normal (fSub, 5w, Reg 5w, Reg 4w) s in
  let s = dfn'LoadConstant (4w, F, 4w * 34w) s in
  let s = dfn'JumpIfZero (fAnd, Reg 4w, Reg 6w, Reg 8w) s in
  s`;

Theorem ag32_ffi_write_check_lengths_thm:
   (s.R 5w = n2w (ffi_code_start_offset - 1)) ∧
   (s.R 4w = n2w ltll) ∧ (s.R 7w = n2w off) ∧ (s.R 1w = n2w n) ∧ (s.R 6w = v2w [cnd]) ∧
   off < dimword(:16) ∧ n < dimword(:16) ∧ ltll < dimword (:32)
   ⇒
   ∃r4 r6 r8 cf ov.
   (ag32_ffi_write_check_lengths s =
    s with <| PC := if cnd ∧ off ≤ ltll ∧ n ≤ ltll - off
                    then s.PC + n2w (4 * LENGTH ag32_ffi_write_check_lengths_code)
                    else s.PC + n2w (4 * (LENGTH ag32_ffi_write_check_lengths_code + 33)) ;
              R := ((8w =+ r8)
                   ((4w =+ r4)
                   ((5w =+ n2w output_offset)
                   ((6w =+ r6) s.R))));
              CarryFlag := cf;
              OverflowFlag := ov |>)
Proof
  strip_tac
  \\ simp[ag32_ffi_write_check_lengths_def]
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.ri2word_def,
          ag32Theory.norm_def, ag32Theory.ALU_def, ag32Theory.incPC_def,
          ag32Theory.dfn'LoadConstant_def, APPLY_UPDATE_THM]
  \\ simp[ag32Theory.dfn'JumpIfZero_def,ag32Theory.ri2word_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`COND b1`
  \\ qmatch_goalsub_abbrev_tac`if b2 then _  + _ else _`
  \\ `b1 = ¬b2`
  by (
    unabbrev_all_tac
    \\ Cases_on`cnd` \\ fs[]
    \\ simp[NOT_LESS_EQUAL]
    \\ fs [WORD_LO]
    \\ Cases_on `ltll < off` \\ fs []
    \\ fs [NOT_LESS]
    \\ simp_tac std_ss [addressTheory.WORD_SUB_INTRO,addressTheory.word_arith_lemma2]
    \\ fs [] \\ rw [v2w_sing])
  \\ qpat_x_assum`Abbrev(b1 = _)`kall_tac
  \\ simp[] \\ rveq
  \\ IF_CASES_TAC
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[ag32_ffi_write_check_lengths_code_def]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 4w = _ then r4 else _`
  \\ qexists_tac`r4`
  \\ qmatch_goalsub_abbrev_tac`if 6w = _ then r6 else _`
  \\ qexists_tac`r6`
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8`
  \\ rw[] \\ fs[]
  \\ EVAL_TAC \\ simp[]
QED

Theorem ag32_ffi_write_check_lengths_MEM:
   (ag32_ffi_write_check_lengths s).MEM = s.MEM
Proof
  rw[ag32_ffi_write_check_lengths_def, dfn'Normal_MEM, dfn'LoadConstant_MEM,
     dfn'JumpIfZero_MEM]
QED

Theorem ag32_ffi_write_check_lengths_PC:
   (ag32_ffi_write_check_lengths s).PC ∈
    { s.PC + n2w (4 * LENGTH ag32_ffi_write_check_lengths_code );
      s.PC + n2w (4 * (LENGTH ag32_ffi_write_check_lengths_code + 33)) }
Proof
  reverse (
    rw[ag32_ffi_write_check_lengths_def, dfn'Normal_PC, dfn'LoadConstant_PC,
       ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def,
       ag32Theory.ri2word_def, ag32Theory.incPC_def ] )
  >- EVAL_TAC
  \\ rw[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ EVAL_TAC
QED

Theorem ag32_ffi_write_check_lengths_R:
   ((ag32_ffi_write_check_lengths s).R 3w = s.R 3w) ∧
   ((ag32_ffi_write_check_lengths s).R 5w = s.R 5w - n2w ((ffi_code_start_offset - 1) - output_offset))
Proof
  rw[ag32_ffi_write_check_lengths_def,
     ag32Theory.dfn'Normal_def, ag32Theory.ri2word_def,
     ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.norm_def,
     ag32Theory.dfn'LoadConstant_def, ag32Theory.dfn'JumpIfZero_def,
     APPLY_UPDATE_THM]
  \\ EVAL_TAC
QED

val ag32_ffi_write_write_header_def = Define`
  ag32_ffi_write_write_header s =
  let s = dfn'StoreMEM (Imm 0w, Reg 5w) s in
  let s = dfn'Normal (fAdd, 5w, Reg 5w, Imm 4w) s in
  let s = dfn'Shift (shiftLL, 2w, Reg 2w, Imm 24w) s in
  let s = dfn'StoreMEM (Reg 2w, Reg 5w) s in
  let s = dfn'Normal (fAdd, 5w, Reg 5w, Imm 4w) s in
  let s = dfn'StoreMEMByte (Imm 0w, Reg 5w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'StoreMEMByte (Imm 0w, Reg 5w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'Shift (shiftLR, 2w, Reg 1w, Imm 8w) s in
  let s = dfn'StoreMEMByte (Reg 2w, Reg 5w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'StoreMEMByte (Reg 1w, Reg 5w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'StoreMEMByte (Imm 0w, Reg 3w) s in
  s`;

Theorem ag32_ffi_write_write_header_thm:
   (s.R 5w = n2w output_offset) ∧
   (LENGTH conf = 8) ∧ (w82n conf < 3) ∧ (s.R 2w = n2w (w82n conf)) ∧
   (s.R 1w = n2w (w22n [n1; n0])) ∧ (s.R 3w ≠ n2w output_offset)
   ⇒
   ∃r2 ov cf.
   (ag32_ffi_write_write_header s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_write_header_code);
              R := ((5w =+ n2w (output_offset + 12))
                   ((2w =+ r2) s.R));
              MEM :=
                (((s.R 3w) =+ 0w)
                 (asm_write_bytearray (n2w output_offset) (conf ++ [0w; 0w; n1; n0]) s.MEM));
              OverflowFlag := ov;
              CarryFlag := cf |>)
Proof
  rewrite_tac[ag32_ffi_write_write_header_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'StoreMEM_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac`adr + 2w`
  \\ `adr = n2w output_offset`
  by (
    simp[Abbr`adr`]
    \\ EVAL_TAC
    \\ blastLib.BBLAST_TAC
    \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.aligned_bitwise_and]
    \\ blastLib.FULL_BBLAST_TAC )
  \\ qpat_x_assum`Abbrev(adr = _)`kall_tac
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fAdd`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`shiftLL`]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ rveq
  \\ qmatch_goalsub_abbrev_tac`adr + 2w`
  \\ `adr = n2w (output_offset + 4)`
  by (
    simp[Abbr`adr`]
    \\ EVAL_TAC
    \\ blastLib.BBLAST_TAC
    \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.aligned_bitwise_and]
    \\ blastLib.FULL_BBLAST_TAC )
  \\ qpat_x_assum`Abbrev(adr = _)`kall_tac \\ rveq
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'StoreMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[APPLY_UPDATE_THM]
  \\ simp[ag32Theory.ag32_state_component_equality, APPLY_UPDATE_THM]
  \\ simp[ag32_ffi_write_write_header_code_def]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 2w = _ then r2 else _`
  \\ qexists_tac`r2`
  \\ reverse conj_tac
  >- ( rw[] \\ fs[] \\ rw[GSYM word_add_n2w] )
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ rveq
  \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ simp[EVAL``output_offset``]
  \\ fs[memory_size_def, word_add_n2w]
  \\ Cases
  \\ IF_CASES_TAC >- fs[]
  \\ simp_tac std_ss []
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ simp[MarshallingTheory.w22n_def, GSYM word_add_n2w, GSYM word_mul_n2w]
    \\ Cases_on`n0` \\ fs[] \\ rveq
    \\ blastLib.BBLAST_TAC )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[Abbr`r2`]
    \\ simp[MarshallingTheory.w22n_def, GSYM word_add_n2w, GSYM word_mul_n2w]
    \\ Cases_on`n1` \\ fs[] \\ rveq
    \\ fs [GSYM w2w_def]
    \\ match_mp_tac (blastLib.BBLAST_PROVE
        ``w <+ 256w:word32 /\ (k = w2w w) ==> ((7 >< 0)
          ((256w * w + w2w (n0:word8)) ⋙ 8) = k:word8)``)
    \\ fs [w2w_def,WORD_LO])
  \\ IF_CASES_TAC
  >- ( full_simp_tac std_ss [n2w_11] \\ rfs[] )
  \\ IF_CASES_TAC
  >- ( full_simp_tac std_ss [n2w_11] \\ rfs[] )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''''''` \\ fs[] \\ rw[]
    \\ match_mp_tac (blastLib.BBLAST_PROVE
         ``w <+ 256w:word32 /\ (k = w2w w) ==> ((31 >< 24) (w ≪ 24) = k:word8)``)
    \\ fs [WORD_LO,w2w_def])
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''''''` \\ fs[] \\ rw[]
    \\ blastLib.BBLAST_TAC)
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''''''` \\ fs[] \\ rw[]
    \\ blastLib.BBLAST_TAC)
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''''''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''''''` \\ fs[] \\ rw[]
    \\ blastLib.BBLAST_TAC)
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[] )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[] )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n` \\ fs[] )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[])
  \\ simp[]
QED

Theorem ag32_ffi_write_write_header_PC:
   (ag32_ffi_write_write_header s).PC = s.PC + n2w(4 * LENGTH ag32_ffi_write_write_header_code)
Proof
  rw[ag32_ffi_write_write_header_def]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ EVAL_TAC
QED

Theorem ag32_ffi_write_write_header_R:
   ((ag32_ffi_write_write_header s).R 3w = s.R 3w)
Proof
  rw[ag32_ffi_write_write_header_def]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Shift_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Shift_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
QED

val ag32_ffi_write_num_written_def = Define`
  ag32_ffi_write_num_written s =
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s0 = dfn'LoadConstant (8w, F, n2w output_buffer_size) s in
  let s = dfn'JumpIfZero (fLess, Imm 8w, Reg 8w, Reg 1w) s0 in
  let s = if s.PC = s0.PC + 4w then dfn'Normal (fSnd, 1w, Reg 1w, Reg 8w) s else s in
  let s = dfn'Shift (shiftLR, 8w, Reg 1w, Imm 8w) s in
  let s = dfn'StoreMEMByte (Reg 8w, Reg 3w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'StoreMEMByte (Reg 1w, Reg 3w) s in
  let s = dfn'Normal (fAdd, 3w, Reg 3w, Imm 2w) s in
  let s = dfn'Normal (fAdd, 3w, Reg 3w, Reg 7w) s in
  let s = dfn'LoadConstant (2w, F, 4w * 9w) s in
  s`;

Theorem ag32_ffi_write_num_written_thm:
   bytes_in_memory (s.R 3w) (0w::n0::off1::off0::tll) s.MEM md ∧
   (s.R 1w = n2w n) ∧ (k = MIN n output_buffer_size) ∧ n < dimword(:16)
   ⇒
   ∃r8 cf ov.
   (ag32_ffi_write_num_written s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_num_written_code);
              MEM := asm_write_bytearray (s.R 3w) (0w::(n2w2 k)) s.MEM;
              R := ((8w =+ r8)
                   ((3w =+ s.R 3w + 4w + s.R 7w)
                   ((2w =+ 4w * 9w)
                   ((1w =+ n2w k) s.R))));
              CarryFlag := cf;
              OverflowFlag := ov |>)
Proof
  rewrite_tac[ag32_ffi_write_num_written_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'LoadConstant_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'JumpIfZero_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac`if cnd then _ else _`
  \\ qmatch_asmsub_abbrev_tac`cnd = ((if cnd' then _ else _).PC = _)`
  \\ `cnd = ¬cnd'` by ( rw[Abbr`cnd`,Abbr`cnd'`] )
  \\ qpat_x_assum`Abbrev(cnd = _)`kall_tac
  \\ qunabbrev_tac`cnd'`
  \\ rveq
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss())[]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def, ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'StoreMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def, ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[Once COND_RAND]
  \\ simp[Once COND_RATOR]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[EVAL``4 * LENGTH ag32_ffi_write_num_written_code``]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`v2w [cnd] = 0w`
  \\ fs[EVAL``output_buffer_size``]
  \\ rfs[word_lt_n2w]
  \\ `¬BIT 31 n` by
    fs [bitTheory.BIT_def,bitTheory.BITS_THM,LESS_DIV_EQ_ZERO] \\ fs[]
  \\ `MIN n 2048 = if cnd then 2048 else n` by rw[Abbr`cnd`,MIN_DEF]
  \\ fs[] \\ rveq
  \\ fs[bytes_in_memory_def]
  \\ fs[CaseEq"option"] \\ rveq
  \\ Cases_on`s.R 3w`
  \\ Cases_on`cnd` \\ fs[markerTheory.Abbrev_def]
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8` \\ simp[Abbr`r8`]
  \\ (reverse conj_tac >- (rw[] \\ fs[]))
  \\ rw[MarshallingTheory.n2w2_def, asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ fs[] \\ rfs[word_add_n2w]
  \\ TRY (
    Cases_on`n' + 1 < dimword(:32)` \\ fs[]
    \\ `n' + 1  =dimword(:32)` by fs[]
    \\ fs[] \\ NO_TAC)
  \\ TRY (
    Cases_on`n' + 2 < dimword(:32)` \\ fs[]
    \\ Cases_on`n' = dimword(:32) - 1` \\ fs[]
    \\ Cases_on`n' = dimword(:32) - 2` \\ fs[]
    \\ NO_TAC)
  >- blastLib.BBLAST_TAC
  \\ fs [NOT_LESS]
  \\ match_mp_tac (blastLib.BBLAST_PROVE
      ``w <+ 256w:word32 /\ (k = w2w w) ==> ((7 >< 0) w = k:word8)``)
  \\ rewrite_tac [w2w_def,w2n_lsr,WORD_LO]
  \\ fs [DIV_LT_X]
QED

val ag32_ffi_write_def = Define`
  ag32_ffi_write s =
  let s = ag32_ffi_write_set_id s in
  let s = ag32_ffi_write_check_conf s in
  let s0 = ag32_ffi_write_load_noff s in
  let s = ag32_ffi_write_check_lengths s0 in
  let s =
    if s.PC = s0.PC + n2w (4 * LENGTH ag32_ffi_write_check_lengths_code) then
      let s = ag32_ffi_write_write_header s in
      let s = ag32_ffi_write_num_written s in
              ag32_ffi_copy s
    else
      let s = dfn'StoreMEMByte (Imm 1w, Reg 3w) s in
              dfn'StoreMEMByte (Imm 1w, Reg 5w) s
  in ag32_ffi_return s`;

(* returns error code 1 after writing the appropriate ffi *)
val ag32_ffi_fail_def = Define`
  ag32_ffi_fail ffiname s =
  let s = dfn'LoadConstant(5w, F, n2w (ffi_code_start_offset - 1)) s in
  let s = dfn'StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes ffiname))), Reg 5w) s in
  let s = dfn'StoreMEMByte (Imm 1w, Reg 3w) s in
  s`

val ag32_ffi_fail_code_def = Define`
  ag32_ffi_fail_code ffiname =
    [LoadConstant(5w, F, n2w (ffi_code_start_offset - 1));
     StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes ffiname))), Reg 5w);
     StoreMEMByte(Imm 1w, Reg 3w)]`

(* open_in *)
val ag32_ffi_open_in_entrypoint_def = Define`
  ag32_ffi_open_in_entrypoint =
  ag32_ffi_write_entrypoint + 4 * LENGTH ag32_ffi_write_code`;

val ag32_ffi_open_in_def = Define`
  ag32_ffi_open_in s =
 let s = ag32_ffi_fail "open_in" s in
  ag32_ffi_return s`;

val ag32_ffi_open_in_code_def = Define`
  ag32_ffi_open_in_code = ag32_ffi_fail_code "open_in" ++ ag32_ffi_return_code`

(* open_out *)

val ag32_ffi_open_out_entrypoint_def = Define`
  ag32_ffi_open_out_entrypoint =
  ag32_ffi_open_in_entrypoint + 4 * LENGTH ag32_ffi_open_in_code`;

val ag32_ffi_open_out_def = Define`
  ag32_ffi_open_out s =
 let s = ag32_ffi_fail "open_out" s in
  ag32_ffi_return s`;

val ag32_ffi_open_out_code_def = Define`
  ag32_ffi_open_out_code = ag32_ffi_fail_code "open_out" ++ ag32_ffi_return_code`

(* close *)

val ag32_ffi_close_entrypoint_def = Define`
  ag32_ffi_close_entrypoint =
  ag32_ffi_open_out_entrypoint + 4 * LENGTH ag32_ffi_open_out_code`;

val ag32_ffi_close_def = Define`
  ag32_ffi_close s =
 let s = ag32_ffi_fail "close" s in
  ag32_ffi_return s`;

val ag32_ffi_close_code_def = Define`
  ag32_ffi_close_code = ag32_ffi_fail_code "close" ++ ag32_ffi_return_code`

(* FFI jumps
  - get byte array (length,pointer)s in (len_reg,ptr_reg) and (len2_reg,ptr2_reg) (these are r1-r4)
  - get return address in link_reg (r0)
  - PC is ffi_jumps_offset + ffi_offset * index
  conventions on return (see ag32_ffi_interfer_def):
    r0 is the end of this ffi's code (i.e., entrypoint of the next ffi's code)
    r1-r8 are 0w
    overflow and carry are false
*)

val ffi_entrypoints_def = Define`
  ffi_entrypoints = [
    ("", ag32_ffi__entrypoint);
    ("get_arg_count", ag32_ffi_get_arg_count_entrypoint);
    ("get_arg_length", ag32_ffi_get_arg_length_entrypoint);
    ("get_arg", ag32_ffi_get_arg_entrypoint);
    ("read", ag32_ffi_read_entrypoint);
    ("write", ag32_ffi_write_entrypoint);
    ("open_in", ag32_ffi_open_in_entrypoint);
    ("open_out", ag32_ffi_open_out_entrypoint);
    ("close", ag32_ffi_close_entrypoint)
    (*
    ("exit", ag32_ffi_exit_entrypoint);
    *)
    ]`;

val ffi_exitpcs_def = Define`
  ffi_exitpcs = [
    ("", ffi_code_start_offset + ag32_ffi_get_arg_count_entrypoint);
    ("get_arg_count", ffi_code_start_offset + ag32_ffi_get_arg_length_entrypoint);
    ("get_arg_length", ffi_code_start_offset + ag32_ffi_get_arg_entrypoint);
    ("get_arg", ffi_code_start_offset + ag32_ffi_read_entrypoint);
    ("read", ffi_code_start_offset + ag32_ffi_write_entrypoint);
    ("write", ffi_code_start_offset + ag32_ffi_open_in_entrypoint);
    ("open_in", ffi_code_start_offset + ag32_ffi_open_out_entrypoint);
    ("open_out", ffi_code_start_offset + ag32_ffi_close_entrypoint);
    ("close", heap_start_offset)
    (*
    ("exit", ffi_code_start_offset + ag32_ffi_get_arg_count_entrypoint);
    *)
    ]`;

val mk_jump_ag32_code_def = Define`
  mk_jump_ag32_code ffi_names name =
    let index = THE (INDEX_OF name ffi_names) in
    let entrypoint = THE (ALOOKUP ffi_entrypoints name) in
    let dist_to_ffi_code =
      8 + ffi_offset * (LENGTH ffi_names - 1 - index) +
      heap_size + length_ag32_ffi_code - entrypoint in
    [Encode(LoadConstant(5w, F, (22 >< 0)((n2w dist_to_ffi_code):word32)));
     Encode(LoadUpperConstant(5w, (31 >< 23)((n2w dist_to_ffi_code):word32)));
     Encode(Jump (fSub, 5w, Reg 5w));
     0w]`;

Theorem EL_FLAT_MAP_mk_jump_ag32_code:
   ∀ls index.
   (INDEX_OF nm ls = SOME index) ∧ k < 4 ⇒
   (EL (4 * index + k) (FLAT (MAP (mk_jump_ag32_code nmns) ls)) =
    EL k (mk_jump_ag32_code nmns nm))
Proof
  Induct
  >- ( rw[GSYM find_index_INDEX_OF, find_index_def] )
  \\ rw[GSYM find_index_INDEX_OF, find_index_def]
  >- (
    rw[EL_APPEND_EQN]
    \\ fs[mk_jump_ag32_code_def] )
  \\ qhdtm_x_assum`find_index`mp_tac
  \\ simp[Once find_index_shift_0]
  \\ strip_tac
  \\ fs[find_index_INDEX_OF]
  \\ simp[EL_APPEND_EQN]
  \\ simp[Once mk_jump_ag32_code_def]
  \\ simp[Once mk_jump_ag32_code_def]
  \\ simp[LEFT_ADD_DISTRIB]
QED

val ccache_jump_ag32_code_def = Define`
  ccache_jump_ag32_code = [Encode (Jump (fSnd, 0w, Reg 0w)); 0w; 0w; 0w]`;

val halt_jump_ag32_code_def = Define`
  halt_jump_ag32_code = [Encode (Jump (fAdd, 0w, Imm 0w)); 0w; 0w; 0w]`;

val ag32_ffi_jumps_def = Define`
  ag32_ffi_jumps ffi_names =
    FLAT (MAP (mk_jump_ag32_code ffi_names) (REVERSE ffi_names)) ++ ccache_jump_ag32_code ++ halt_jump_ag32_code`;

val LENGTH_ag32_ffi_jumps =
  ``LENGTH (ag32_ffi_jumps nms)``
  |> SIMP_CONV(srw_ss()++LET_ss)
      [LENGTH_FLAT,MAP_MAP_o,o_DEF,mk_jump_ag32_code_def,ag32_ffi_jumps_def,
       Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  |> CONV_RULE(RAND_CONV EVAL)
  |> curry save_thm "LENGTH_ag32_ffi_jumps"

val ag32_ffi_code_def = Define`
  ag32_ffi_code =
    MAP Encode (
      ag32_ffi__code ++
      ag32_ffi_get_arg_count_code ++
      ag32_ffi_get_arg_length_code ++
      ag32_ffi_get_arg_code ++
      ag32_ffi_read_code ++
      ag32_ffi_write_code ++
      ag32_ffi_open_in_code ++
      ag32_ffi_open_out_code ++
      ag32_ffi_close_code
      (*
      ag32_ffi_exit_code ++
      *)
      )`;

val LENGTH_ag32_ffi_code = ``LENGTH ag32_ffi_code`` |> EVAL
  |> curry save_thm "LENGTH_ag32_ffi_code"

Theorem LENGTH_ag32_ffi_code_check:
   4 * LENGTH ag32_ffi_code = length_ag32_ffi_code
Proof
  simp[LENGTH_ag32_ffi_code] \\ EVAL_TAC
QED

val code_start_offset_def = Define`
  code_start_offset num_ffis =
    ffi_jumps_offset +
    ffi_offset *
    (2 (* halt and ccache *) + num_ffis)`;

val startup_asm_code_def = Define`
  startup_asm_code
    (* r1: temp reg *)
    (* r2: heap start reg: should be left with heap start address *)
    (* r3: temp reg - only required because of large immediates *)
    (* r4: heap end reg: should be left with heap end address *)
    (* desired initial words of heap:
         w0: bitmaps_ptr
         w1: bitmaps_ptr + bitmaps_length
         w2: bitmaps_ptr + bitmaps_length + bitmaps_buffer_length
         w3: code_buffer_ptr
         w4: code_buffer_ptr + code_buffer_length
       for now, we simply assume code_buffer_length and bitmaps_buffer_length are 0 (no Install)
       therefore, in our layout, we want to set things as follows:
       --------------- <- w1, w2
         CakeML data
       --------------- <- w0, w3, w4
         CakeML code
       --------------- <- start PC
    *)
    num_ffis (code_length:word32) bitmaps_length =
    (*
      r2 <- heap_start_offset
      r4 <- code_start_offset num_ffis
      r1 <- code_length
      r4 <- r4 + r1
      m[r2+0] <- r4
      m[r2+3] <- r4
      m[r2+4] <- r4
      r1 <- bitmaps_length
      r4 <- r1 + r4
      m[r2+1] <- r4
      m[r2+2] <- r4
      r1 <- heap_size
      r4 <- r2 + r1
      r1 <- code_start_offset num_ffis
      jump r1
    *)
    [Inst (Const 2 (n2w heap_start_offset));
     Inst (Const 4 (n2w (code_start_offset num_ffis)));
     Inst (Const 1 code_length);
     Inst (Arith (Binop Add 4 4 (Reg 1)));
     Inst (Mem Store 4 (Addr 2 (0w * bytes_in_word)));
     Inst (Mem Store 4 (Addr 2 (3w * bytes_in_word)));
     Inst (Mem Store 4 (Addr 2 (4w * bytes_in_word)));
     Inst (Const 1 bitmaps_length);
     Inst (Arith (Binop Add 4 1 (Reg 4)));
     Inst (Mem Store 4 (Addr 2 (1w * bytes_in_word)));
     Inst (Mem Store 4 (Addr 2 (2w * bytes_in_word)));
     Inst (Const 1 (n2w heap_size));
     Inst (Arith (Binop Add 4 2 (Reg 1)));
     Inst (Const 1 (n2w (code_start_offset num_ffis)));
     JumpReg 1]`;

val LENGTH_startup_asm_code = save_thm("LENGTH_startup_asm_code",
  ``LENGTH (startup_asm_code n cl bl)`` |> EVAL);

val startup_code_def = Define`
  startup_code ffi_len code_len data_len =
    FLAT (MAP ag32_enc (startup_asm_code ffi_len (n2w code_len) (n2w (4* data_len))))`

val init_memory_words_def = Define`
  init_memory_words code data ffis cl stdin =
  let sc = startup_code (LENGTH ffis) (LENGTH code) (LENGTH data) in
  (* startup code *)
  words_of_bytes F sc ++
  (* pad startup code to size *)
  REPLICATE ((startup_code_size - LENGTH sc) DIV 4) 0w ++
  (* command line *)
  [n2w (LENGTH cl)] ++
  words_of_bytes F (PAD_RIGHT 0w cline_size (FLAT (MAP (SNOC 0w) (MAP (MAP (n2w o ORD) o explode) cl)))) ++
  [0w] ++
  (* stdin *)
  [n2w (LENGTH stdin)] ++
  words_of_bytes F (PAD_RIGHT 0w stdin_size (MAP (n2w o ORD) stdin)) ++
  (* output *)
  REPLICATE ((8 + 4 + output_buffer_size + 4) DIV 4) 0w ++
  (* ffis *)
  ag32_ffi_code ++
  (* heap *)
  REPLICATE (heap_size DIV 4) 0w ++
  (* FFIs *)
  ag32_ffi_jumps ffis ++
  words_of_bytes F code ++
  data (* ++ padding of 0w out to memory_size: not included here *)
  `

val init_memory_def = Define`
  init_memory code data ffis (cl,stdin) k =
  get_byte k (EL (w2n (byte_align k) DIV 4) (init_memory_words code data ffis cl stdin)) F`

val _ = export_theory();
