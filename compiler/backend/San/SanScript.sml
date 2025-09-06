(*
* A simple instantiation of machin_config for sanity check share memory access
*)
Theory San
Ancestors
  targetSem riscv_target riscv ffi bitstring asmProps
Libs
  preamble

(* the bool is used as indicating whether the pc is accessing shared memory *)
Definition san_prog_asm_def:
  san_prog_asm = [
    F, (Inst (Const 5 0w));
    T, (Inst (Mem Load 6 (Addr 5 20000w)));
    F, (Inst (Arith (Binop Add 7 6 (Imm 1w))));
    T, (Inst (Mem Store 7 (Addr 5 20008w)));
    F, (Jump (-32w: word64))] (* jump to the halt pc *)
End

Definition asm2ast_def:
  asm2ast = MAP (\(b,asm). (b,riscv_ast asm))
End

Definition asts_encode_def:
  asts_encode = MAP (\(b,ast). (b,FLAT $ MAP riscv_encode ast))
End

Definition add_halt_and_ccache_def:
  add_halt_and_ccache = (++) (GENLIST (K (F,GENLIST (K 0w) ffi_offset)) 2)
End

Definition san_flat_def:
  (san_flat [] n = ([],[],[])) /\
  (san_flat ((F,xs)::xss) n =
    let (pcs,pcs',prog) = san_flat xss (n+LENGTH xs) in
    (pcs,pcs',xs++prog)) /\
  (san_flat ((T,xs)::xss) n =
    let (pcs,pcs',prog) = san_flat xss (n+LENGTH xs) in
    (n::pcs,n+LENGTH xs::pcs', xs++prog))
End

Definition san_enc_result_def:
    san_enc_result =
      flip san_flat 0 o add_halt_and_ccache o asts_encode $
      asm2ast san_prog_asm
End

Definition san_ffi_pcs_def:
  san_ffi_pcs = MAP n2w o FST $ san_enc_result
End

Definition  san_end_ffi_pcs_def:
  san_end_ffi_pcs = MAP n2w o FST o SND $ san_enc_result
End

Definition san_program_def:
  san_program = ((SND o SND $ san_enc_result):word8 list)
End

Definition san_ffi_interfer_def:
  san_ffi_interfer info_func = K (\((n:num),bytes,state).
    if n = 0 then
      let (nb,ad,reg,new_pc) = info_func n in
      state with
      <|c_gpr := (\pid r.
          if pid = state.procID /\ r = n2w reg
          then (word_of_bytes F 0w bytes)
          else state.c_gpr pid r);
        c_PC := (state.procID =+ new_pc) state.c_PC |>
    else if n = 1 then
      let (_,_,_,new_pc) = info_func n in
        state with
      <|c_PC := (state.procID =+ new_pc) state.c_PC |>
    else state)
End

Definition san_mmio_info_def:
  san_mmio_info =
    let max_size = dimindex (:64) DIV 8 in
    ((0:num) =+ (n2w max_size,Addr 5 20000w,(6:num),EL 0 san_end_ffi_pcs)) $
    (1 =+ (n2w max_size,Addr 5 20008w,7,EL 1 san_end_ffi_pcs)) $
    K ARB
End

val san_ffi_pcs_simp = CONV_RULE (SIMP_CONV (srw_ss()) [san_ffi_pcs_def]) $
  EVAL ``san_ffi_pcs``;
val san_end_pcs_simp = EVAL ``san_end_ffi_pcs``;

Definition san_config_def:
  san_config =
  <| prog_addresses := {x | x < 1000w} DELETE 0w DELETE n2w ffi_offset
   ; shared_addresses := {a| 20000w <= a /\ a < 20016w}
   ; ffi_entry_pcs := san_ffi_pcs
   ; ffi_names := ["MappedRead";"MappedWrite"]
   ; ptr_reg := ARB
   ; len_reg := ARB
   ; ptr2_reg := ARB
   ; len2_reg := ARB
   ; ffi_interfer := san_ffi_interfer
      (san_mmio_info: num -> word8 # 64 addr # num # word64)
   ; next_interfer := K I
   ; halt_pc := n2w ffi_offset
   ; ccache_pc := 0w
   ; ccache_interfer :=ARB
   ; target := riscv_target
   ; mmio_info := san_mmio_info|>
End

Definition san_oracle_def:
  san_oracle s () l1 l2 =
    Oracle_return ()
      (PAD_RIGHT 0w (LENGTH l2) [20w])
End

Definition san_init_ffi_state_def:
  san_init_ffi_state =
    <|oracle := san_oracle;
      ffi_state := ();
      io_events := []|>
End

Definition san_init_pc_def:
  san_init_pc = n2w $ ffi_offset * 2
End

Definition word_EL_def:
  word_EL l start w = if w2n (w - start) < LENGTH l
          then EL (w2n (w - start)) l else 0w
End

Definition san_procID_def:
  san_procID = 0w
End

Definition san_MCSR_def:
  san_MCSR = (san_procID =+
      <|mstatus := <| VM := 0w |>;
      mcpuid := <|ArchBase := 2w |> |>) ARB
End

Definition san_init_machine_state_def:
  san_init_machine_state =
    ARB with
    <|c_PC := (san_procID =+ san_init_pc) (K 0w);
      procID := san_procID;
      MEM8 := word_EL san_program 0w;
      c_MCSR := san_MCSR;
      exception := NoException;
      c_NextFetch := (san_procID =+ NONE) ARB|>
End

Definition san_result_def:
  san_result n =
  evaluate san_config san_init_ffi_state n san_init_machine_state
End

val riscv_inst_defs = map (fst o snd) $
  filter (fn n => substring (snd (fst n),0, 4) = "dfn'") $
  filter (fn n => snd (snd n) = Def) $ DB.match ["riscv"] ``_``;

val _ = computeLib.add_funs
  [Encode_def,Itype_def,Stype_def,UJtype_def,opc_def,word_concat_def,v2w_def];

val san_program_simp = EVAL ``san_program``;

fun encoded_bytes_in_mem_tac inst offset =
  qpat_abbrev_tac `_x = encoded_bytes_in_mem _ _ _ _` \\
  `_x` by (
    qunabbrev_tac `_x` \\
    gvs[encoded_bytes_in_mem_def,riscv_config_def] \\
    qexistsl [inst, offset] \\
    simp [EVAL $ Parse.Term inst, EVAL $ Parse.Term offset] \\
    fs[riscv_enc_def,LIST_BIND_def,riscv_ast_def] \\
    EVAL_TAC \\
    simp[DELETE_applied,DIFF_DEF]) \\
  qunabbrev_tac `_x` \\
  simp[];

val riscv_ok_tac = simp[
  EVAL ``ffi_offset``, riscv_ok_def,aligned_w2n,APPLY_UPDATE_THM];

val decode_conv =
  SIMP_CONV (srw_ss()) [Decode_def,boolify32_def,LET_DEF] THENC
  EVAL;

fun pattern_conv pat conv_f = DEPTH_CONV
  (fn tm =>
    if is_comb tm andalso is_const(fst(dest_comb tm)) andalso
      dest_const(fst(dest_comb tm)) = dest_const pat
    then conv_f tm
    else ALL_CONV tm);

val next_state_conv = EVAL THENC
  SIMP_CONV (srw_ss())
    [rawReadInst_def,translateAddr_def,vmType_def,MCSR_def,
     APPLY_UPDATE_THM,PC_def,LET_DEF,word_EL_def,boolify8_def] THENC
  SIMP_CONV (srw_ss())
    [write'Skip_def,word_EL_def,word_concat_def] THENC
  pattern_conv ``Decode`` decode_conv THENC
  SIMP_CONV (srw_ss())
    ([Run_def,GPR_def,write'GPR_def,write'gpr_def,LET_THM,branchTo_def,
      write'NextFetch_def,asImm20_def,word_concat_def,PC_def,word_bit_def]
      @ riscv_inst_defs) THENC
  SIMP_CONV (srw_ss())
    [NextFetch_def,write'PC_def,Skip_def,APPLY_UPDATE_THM,gpr_def,PC_def];

val next_state_tac = qpat_abbrev_tac `_y = riscv_next _` \\
  pop_assum(assume_tac o (CONV_RULE (RAND_CONV (RHS_CONV next_state_conv)))) \\
  qunabbrev_tac `_y`;

val san_prog_addr_simp =
  ``{x | x < 1000w} DELETE 0w DELETE n2w ffi_offset DIFF
  flip MEM san_ffi_pcs`` |> (EVAL THENC
  SIMP_CONV (srw_ss()) [DELETE_applied,DIFF_DEF]);

val san_mmio_info_simp = EVAL ``san_mmio_info``;

val valid_mapped_read_tac =
  qpat_abbrev_tac `_r = is_valid_mapped_read _ _ _ _ _ _ _ _` \\
  `_r` by (
    qunabbrev_tac `_r` \\
    simp[is_valid_mapped_read_def] \\
    simp[riscv_config_def, riscv_enc_def,riscv_ast_def,LIST_BIND_def] \\
    EVAL_TAC \\
    simp[EXTENSION,DELETE_DEF]
  ) \\
  qunabbrev_tac `_r`;

val valid_mapped_write_tac =
 qpat_abbrev_tac `_w = is_valid_mapped_write _ _ _ _ _ _ _ _` \\
  `_w` by (
    qunabbrev_tac `_w` \\
    simp[is_valid_mapped_write_def] \\
    simp[riscv_config_def, riscv_enc_def,riscv_ast_def,LIST_BIND_def] \\
    EVAL_TAC \\
    simp[EXTENSION,DELETE_DEF]
  ) \\
  qunabbrev_tac `_w`;

Theorem san_io_event_length:
  LENGTH (SND(SND(san_result 10))).io_events = 2
Proof
  simp[san_result_def, Once evaluate_def]\\
  rewrite_tac[san_config_def,san_init_pc_def,san_procID_def,
    san_init_machine_state_def,san_MCSR_def] \\
  simp[PC_def,riscv_target_def,APPLY_UPDATE_THM,san_ffi_pcs_def,
    san_ffi_pcs_simp,EVAL ``n2w (2 * ffi_offset)``,san_prog_addr_simp,
    san_end_pcs_simp, EVAL ``ffi_offset``] \\
  encoded_bytes_in_mem_tac `SND $ EL 0 san_prog_asm` `0` \\
  simp[apply_oracle_def] \\
  next_state_tac \\
  riscv_ok_tac \\
  rewrite_tac[word_EL_def,san_program_simp] \\
  simp[Once evaluate_def,APPLY_UPDATE_THM] \\
  simp[find_index_def, san_ffi_pcs_simp] \\
  simp[san_mmio_info_simp,APPLY_UPDATE_THM] \\
  valid_mapped_read_tac \\
  simp[call_FFI_def,san_init_ffi_state_def,san_oracle_def] \\
  simp[length_pad_right,
    EVAL ``LENGTH (addr2w8list (20000w:word64))``] \\
  simp[apply_oracle_def,san_ffi_interfer_def,APPLY_UPDATE_THM] \\
  simp[Once evaluate_def,APPLY_UPDATE_THM] \\
  encoded_bytes_in_mem_tac `SND $ EL 2 san_prog_asm` `0` \\
  simp[apply_oracle_def,shift_seq_def] \\
  next_state_tac \\
  riscv_ok_tac \\
  simp[Once evaluate_def,APPLY_UPDATE_THM] \\
  simp[find_index_def,san_ffi_pcs_simp] \\
  simp[san_mmio_info_simp,APPLY_UPDATE_THM] \\
  valid_mapped_write_tac \\
  simp[call_FFI_def,san_init_ffi_state_def,san_oracle_def] \\
  simp[length_pad_right,
    EVAL ``LENGTH (addr2w8list 20008w)``,
    EVAL ``LENGTH (w2wlist_le 21w 8)``] \\
  simp[apply_oracle_def,shift_seq_def] \\
  simp[Once evaluate_def,APPLY_UPDATE_THM] \\
  encoded_bytes_in_mem_tac `SND $ EL 4 san_prog_asm` `0` \\
  simp[apply_oracle_def,shift_seq_def] \\
  next_state_tac \\
  riscv_ok_tac \\
  simp[Once evaluate_def, APPLY_UPDATE_THM]
QED

Theorem leq_2_cases:
  x <= (2:num) <=> x = 1 \/ x = 0 \/ x = 2
Proof
  simp[LE]
QED

Theorem lt_2_cases:
  x < (2:num) ==> x = 1 \/ x = 0
Proof
  simp[LT]
QED

Theorem san_mmio_pcs_min_index_0:
  SOME 0 = mmio_pcs_min_index ["MappedRead";"MappedWrite"]
Proof
  fs[mmio_pcs_min_index_def] \\
  irule some_intro \\
  rw[] >- (
    `x = 1 \/ x = 0 \/ x = 2` by metis_tac[leq_2_cases] \\ fs[] \\
    first_x_assum $ qspec_then `1` mp_tac \\
    simp[]
  ) >- (
    qexists `0` \\
    rw[] \\
    Cases_on `j` \\ simp[] \\
    Cases_on `n` \\ simp[]
  )
QED

Theorem san_start_pc_ok:
  start_pc_ok san_config 32w
Proof
  rw[start_pc_ok_def] \\
  fs[san_config_def, EVAL ``ffi_offset``] \\
  qexists `0` \\
  fs[san_mmio_pcs_min_index_0] \\
  rw[san_ffi_pcs_def,san_ffi_pcs_simp,san_mmio_info_def,
    san_prog_addr_simp,DISJOINT_DEF] \\
  fs[DELETE_DEF,DIFF_DEF,san_end_pcs_simp,INTER_applied,EXTENSION,
    APPLY_UPDATE_THM] \\
  drule lt_2_cases \\
  rw[DISJ_IMP_THM] \\
  fs[WORD_LE,WORD_LT]
QED

Theorem san_ffi_interfer_ok:
  ffi_interfer_ok (32w: word64) ARB san_config
Proof
  rw[ffi_interfer_ok_def,san_config_def] \\
  gvs[GSYM san_mmio_pcs_min_index_0] \\
  drule lt_2_cases \\
  rw[DISJ_IMP_THM,san_mmio_info_simp,APPLY_UPDATE_THM,san_ffi_interfer_def] \\
  fs[target_state_rel_def,riscv_ok_def, aligned_w2n,
    APPLY_UPDATE_THM,riscv_config_def,riscv_target_def]
QED

