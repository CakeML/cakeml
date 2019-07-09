(*
  Define the Sliver machine configuration.
  This includes the FFI interference oracle.
*)
open preamble ag32_memoryTheory ag32_configProofTheory
local open asmSemTheory targetSemTheory ag32_targetTheory in end

val _ = new_theory"ag32_machine_config";

val ag32_init_asm_state_def = Define`
  ag32_init_asm_state mem md = <|
    be := F;
    lr := 0 ;
    failed := F ;
    align := 2 ;
    pc := 0w;
    mem := mem;
    mem_domain := md ;
    regs := K 0w
  |>`;

val ag32_prog_addresses_def = Define`
  ag32_prog_addresses num_ffis LENGTH_code LENGTH_data =
    { w | n2w heap_start_offset <=+ w ∧ w <+ n2w (heap_start_offset + heap_size) } ∪
    { w | n2w (code_start_offset num_ffis) <=+ w ∧
          w <+ n2w (code_start_offset num_ffis + LENGTH_code + 4 * LENGTH_data) } `;

val ag32_startup_addresses_def = Define`
  ag32_startup_addresses =
      { w | w <+ n2w startup_code_size } ∪
      { w | n2w heap_start_offset <=+ w ∧ w <+ n2w (heap_start_offset + 4 * 5) }`;

val ag32_ccache_interfer_def = Define`
  ag32_ccache_interfer num_ffis (_,_,ms) =
    ms with <| PC := (ms.R 0w) ;
               R := (0w =+ n2w (ffi_jumps_offset + num_ffis * ffi_offset + 4)) ms.R |>`;

val ag32_ffi_mem_update_def = Define`
  ag32_ffi_mem_update name conf bytes new_bytes mem =
    if (name = "write") then
      if (HD new_bytes = 0w) then
        case bytes of (n1 :: n0 :: off1 :: off0 :: tll) =>
          let k = MIN (w22n [n1; n0]) output_buffer_size in
          let written = TAKE k (DROP (w22n [off1; off0]) tll) in
            asm_write_bytearray (n2w output_offset) (conf ++ [0w;0w;n1;n0] ++ written) mem
      else ((n2w output_offset) =+ 1w) mem
    else if (name = "read") then
      case new_bytes of (zz :: k1 :: k0 :: _) =>
        if (zz = 0w) then
          set_mem_word (n2w stdin_offset)
            (get_mem_word mem (n2w stdin_offset) + n2w (w22n [k1; k0])) mem
        else mem
    else mem`;

val ag32_ffi_interfer_def = Define`
  ag32_ffi_interfer ffi_names md (index,new_bytes,ms) =
    let name = EL index ffi_names in
    let exitpc = THE (ALOOKUP ffi_exitpcs name) in
    if name = "" then
      ms with <| PC := (ms.R 0w) ;
                 R := ((0w =+ n2w exitpc) ((5w =+ 0w) (ms.R)));
                 CarryFlag := F;
                 OverflowFlag := F
               |>
    else
    let new_mem = ((n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes name))) ms.MEM in
    let new_mem = asm_write_bytearray (ms.R 3w) new_bytes new_mem in
    let new_mem =
      ag32_ffi_mem_update name
        (THE (read_bytearray (ms.R 1w) (w2n (ms.R 2w)) (λa. if a ∈ md then SOME (ms.MEM a) else NONE)))
        (THE (read_bytearray (ms.R 3w) (w2n (ms.R 4w)) (λa. if a ∈ md then SOME (ms.MEM a) else NONE)))
        new_bytes new_mem in
      ms with
        <| PC := (ms.R 0w) ;
           R := ((0w =+ n2w exitpc)
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
  ag32_machine_config ffi_names LENGTH_code LENGTH_data =
  let num_ffis = LENGTH ffi_names in
  let md = ag32_prog_addresses num_ffis LENGTH_code LENGTH_data in
  <|
    target := ag32_target;
    ptr_reg := 1;
    len_reg := 2;
    ptr2_reg := 3;
    len2_reg := 4;
    callee_saved_regs := [60; 61; 62];
    ffi_names := ffi_names ;
    ffi_entry_pcs := REVERSE (GENLIST (λi. n2w (ffi_jumps_offset + i * ffi_offset)) num_ffis);
    ccache_pc     := n2w (ffi_jumps_offset + (num_ffis + 0) * ffi_offset);
    halt_pc       := n2w (ffi_jumps_offset + (num_ffis + 1) * ffi_offset);
    prog_addresses := md ;
    next_interfer := K I ;
    ccache_interfer := K (ag32_ccache_interfer num_ffis) ;
    ffi_interfer := K (ag32_ffi_interfer ffi_names md)
  |>`

Theorem is_ag32_machine_config_ag32_machine_config:
   is_ag32_machine_config (ag32_machine_config a b c)
Proof
EVAL_TAC
QED

val ag32_ffi_mem_domain_def = Define`
  ag32_ffi_mem_domain =
    { w | n2w startup_code_size <=+ (w:word32) ∧
          w <+ n2w ffi_code_start_offset }`;

Theorem ag32_ffi_mem_domain_DISJOINT_prog_addresses:
   num_ffis ≤ LENGTH FFI_codes ∧
   code_start_offset num_ffis + lc + ld ≤ memory_size
   ⇒
   DISJOINT (ag32_ffi_mem_domain) (ag32_prog_addresses num_ffis lc ld)
Proof
  EVAL_TAC
  \\ strip_tac
  \\ simp[IN_DISJOINT, PULL_FORALL]
  \\ rpt Cases
  \\ fs[LEFT_ADD_DISTRIB]
  \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w]
  \\ rfs[]
QED

val _ = export_theory();
