open preamble targetSemTheory riscv_targetTheory;

val _ = new_theory "San";

(* a simple instantiation of machin_config for sanity check *)

val san_asm_config = Define`
  san_asm_config =
    <| ISA            : architecture
     ; encode         : 'a asm -> word8 list
     ; big_endian     : bool
     ; code_alignment : num
     ; link_reg       : num option
     ; avoid_regs     : num list
     ; reg_count      : num
     ; fp_reg_count   : num  (* set to 0 if float not available *)
     ; two_reg_arith  : bool
     ; valid_imm      : (binop + cmp) -> 'a word -> bool
     ; addr_offset    : 'a word # 'a word
     ; byte_offset    : 'a word # 'a word
     ; jump_offset    : 'a word # 'a word
     ; cjump_offset   : 'a word # 'a word
     ; loc_offset     : 'a word # 'a word
     |>`

val san_target = Define`
  san_target =
  <| config : 'a asm_config
   ; next : 'b -> 'b
   ; get_pc : 'b -> 'a word
   ; get_reg : 'b -> num -> 'a word
   ; get_fp_reg : 'b -> num -> word64
   ; get_byte : 'b -> 'a word -> word8
   ; state_ok : 'b -> bool
   ; proj : 'a word set -> 'b -> 'c
   |>`

val san_config = Define`
  san_config =
  <| prog_addresses :=
   ; ffi_entry_pcs := 
   ; ffi_names := ["MappedRead";"MappedWrite"]
   ; ptr_reg := ARB
   ; len_reg := ARB
   ; ptr2_reg := ARB
   ; len2_reg := ARB
   ; ffi_interfer := 
   ; next_interfer := 
   ; halt_pc := 
   ; ccache_pc :=
   ; ccache_interfer :=
   ; target := riscv_target
   |>`;

val () = export_theory ()
