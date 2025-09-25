(*
  Define the compiler configuration for wasm
*)
open preamble backendTheory

val _ = new_theory"wasm_config";

Definition wasm_names_def[compute]:
  wasm_names = LN:num num_map
End

val eval = rhs o concl o EVAL
val min32 = eval ``sw2sw (INT_MINw: word32) : word64``
val max32 = eval ``sw2sw (INT_MAXw: word32) : word64``

Definition wasm_config_def:
  wasm_config =
   <| ISA            := Wasm
    ; reg_count      := 32
    ; fp_reg_count   := 0
    ; avoid_regs     := []
    ; link_reg       := NONE
    ; two_reg_arith  := F
    ; big_endian     := F
    ; valid_imm      := \b i. T
    ; addr_offset    := (^min32, ^max32)
    ; byte_offset    := (^min32, ^max32)
    ; jump_offset    := (^min32, ^max32)
    ; cjump_offset   := (^min32, ^max32)
    ; loc_offset     := (^min32, ^max32)
    ; code_alignment := 0
    |> : 64 asm_config
End

val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=2; col_oracle := [] |>``

val wasm_data_conf = “<| tag_bits := 4
                       ; len_bits := 4
                       ; pad_bits := 2
                       ; len_size := 32
                       ; has_div := T
                       ; has_longdiv := F
                       ; has_fp_ops := F
                       ; has_fp_tern := F
                       ; be := F
                       ; call_empty_ffi := F
                       ; gc_kind := Simple|>”

val wasm_word_conf = ``<| bitmaps_length := 0; stack_frame_size := LN |>``
val wasm_stack_conf = ``<|jump:=T;reg_names:=wasm_names|>``
val wasm_lab_conf = ``<|pos:=0;ffi_names:=NONE;labels:=LN;sec_pos_len:=[];asm_conf:=wasm_config;init_clock:=5;hash_size:=104729n;shmem_extra:=[]|>``

Definition wasm_backend_config_def:
  wasm_backend_config =
             <|source_conf := prim_src_config;
               clos_conf := ^(clos_conf);
               bvl_conf := ^(bvl_conf);
               data_conf := ^(wasm_data_conf);
               word_to_word_conf := ^(word_to_word_conf);
               word_conf := ^(wasm_word_conf);
               stack_conf := ^(wasm_stack_conf);
               lab_conf := ^(wasm_lab_conf);
               symbols := [];
               tap_conf := default_tap_config;
               exported := []
               |>
End

val _ = export_theory();
