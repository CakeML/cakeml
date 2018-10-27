(*
  Define the Sliver machine configuration.
  This includes the FFI interference oracle.
*)
open preamble ag32_memoryTheory ag32_configProofTheory
local open targetSemTheory ag32_targetTheory in end

val _ = new_theory"ag32_machine_config";

val ag32_prog_addresses_def = Define`
  ag32_prog_addresses num_ffis LENGTH_code LENGTH_data r0 =
    { w | r0 + n2w heap_start_offset <=+ w ∧ w <+ r0 + n2w (heap_start_offset + heap_size) } ∪
    { w | r0 + n2w (code_start_offset num_ffis) <=+ w ∧
          w <+ r0 + n2w (code_start_offset num_ffis + LENGTH_code + 4 * LENGTH_data) } `;

val ag32_startup_addresses_def = Define`
  ag32_startup_addresses r0 =
      { w | r0 <=+ w ∧ w <+ r0 + n2w startup_code_size } ∪
      { w | r0 + n2w heap_start_offset <=+ w ∧ w <+ r0 + n2w (heap_start_offset + 4 * 5) }`;

val ag32_ccache_interfer_def = Define`
  ag32_ccache_interfer num_ffis r0 (_,_,ms) =
    ms with <| PC := (ms.R 0w) ;
               R := (0w =+ r0 + n2w (ffi_jumps_offset + num_ffis * ffi_offset + 4)) ms.R |>`;

val ag32_ffi_write_mem_update_def = Define`
  ag32_ffi_write_mem_update name r0 conf bytes new_bytes mem =
    if (name = "write") then
      if (HD new_bytes = 0w) then
        case bytes of (n1 :: n0 :: off1 :: off0 :: tll) =>
          let k = MIN (w22n [n1; n0]) output_buffer_size in
          let written = TAKE k (DROP (w22n [off1; off0]) tll) in
            asm_write_bytearray (r0 + n2w output_offset) (conf ++ [0w;0w;n1;n0] ++ written) mem
      else ((r0 + n2w output_offset) =+ 1w) mem
    else mem`;

val ag32_ffi_interfer_def = Define`
  ag32_ffi_interfer ffi_names md r0 (index,new_bytes,ms) =
    let name = EL index ffi_names in
    let new_mem = ((r0 + n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes name))) ms.MEM in
    let new_mem = asm_write_bytearray (ms.R 3w) new_bytes new_mem in
    let new_mem =
      ag32_ffi_write_mem_update name r0
        (THE (read_bytearray (ms.R 1w) (w2n (ms.R 2w)) (λa. if a ∈ md then SOME (ms.MEM a) else NONE)))
        (THE (read_bytearray (ms.R 3w) (w2n (ms.R 4w)) (λa. if a ∈ md then SOME (ms.MEM a) else NONE)))
        new_bytes new_mem in
    let exitpc = THE (ALOOKUP ffi_exitpcs name) in
        ms with
          <| PC := (ms.R 0w) ;
             R := ((0w =+ r0 + n2w exitpc)
                   ((1w =+ 0w)
                   ((2w =+ 0w)
                   ((3w =+ 0w)
                   ((4w =+ 0w)
                   ((5w =+ 0w)
                   ((6w =+ 0w)
                   ((7w =+ 0w)
                   ((8w =+ 0w) (ms.R)))))))))) ;
             CarryFlag := F ;
             OverflowFlag := F ;
             io_events := ms.io_events ++ [new_mem] ;
             MEM := new_mem |>`;

val ag32_machine_config_def = Define`
  ag32_machine_config ffi_names LENGTH_code LENGTH_data r0 =
  let num_ffis = LENGTH ffi_names in
  let md = ag32_prog_addresses num_ffis LENGTH_code LENGTH_data r0 in
  <|
    target := ag32_target;
    ptr_reg := 1;
    len_reg := 2;
    ptr2_reg := 3;
    len2_reg := 4;
    callee_saved_regs := [60; 61; 62];
    ffi_names := ffi_names ;
    ffi_entry_pcs := REVERSE (GENLIST (λi. r0 + n2w (ffi_jumps_offset + i * ffi_offset)) num_ffis);
    ccache_pc     := r0 + n2w (ffi_jumps_offset + (num_ffis + 0) * ffi_offset);
    halt_pc       := r0 + n2w (ffi_jumps_offset + (num_ffis + 1) * ffi_offset);
    prog_addresses := md ;
    next_interfer := K I ;
    ccache_interfer := K (ag32_ccache_interfer num_ffis r0) ;
    ffi_interfer := K (ag32_ffi_interfer ffi_names md r0)
  |>`

val is_ag32_machine_config_ag32_machine_config = Q.store_thm("is_ag32_machine_config_ag32_machine_config",
  `is_ag32_machine_config (ag32_machine_config a b c r0)`, EVAL_TAC);

val ag32_ffi_mem_domain_def = Define`
  ag32_ffi_mem_domain r0 =
    { w | r0 + n2w startup_code_size <=+ w ∧
          w <+ r0 + n2w ffi_code_start_offset }`;

val ag32_ffi_mem_domain_DISJOINT_prog_addresses = Q.store_thm("ag32_ffi_mem_domain_DISJOINT_prog_addresses",
  `num_ffis ≤ LENGTH FFI_codes ∧
   w2n (r0:word32) + memory_size < dimword (:32) ∧
   code_start_offset num_ffis + lc + ld ≤ memory_size
   ⇒
   DISJOINT (ag32_ffi_mem_domain r0) (ag32_prog_addresses num_ffis lc ld r0)`,
  EVAL_TAC
  \\ Cases_on`r0`
  \\ strip_tac
  \\ simp[IN_DISJOINT, PULL_FORALL]
  \\ rpt Cases
  \\ fs[LEFT_ADD_DISTRIB]
  \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w]
  \\ rfs[]);

val _ = export_theory();
