(*
* A simple instantiation of machin_config for sanity check
*)
open preamble targetSemTheory riscv_targetTheory riscvTheory;

val _ = new_theory "San";
(*
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
   |>`*)

val riscv_alt_enc_def = Define`
  riscv_alt_enc =
  FLAT o (MAP riscv_encode) o riscv_ast`;

val riscv_enc_whole_def = Define`
  riscv_enc_whole =
  FLAT o (MAP riscv_alt_enc)`;

(* the bool is used as indicating whether the pc is accessing shared memory *)
val san_prog_asm_def = Define`
  san_prog_asm = [
    F, (Inst (Const 5 0w));
    T, (Inst (Mem Load 6 (Addr 5 20000w)));
    F, (Inst (Arith (Binop Add 7 6 (Imm 1w))));
    T, (Inst (Mem Store 7 (Addr 5 20008w)));
    F, (JumpReg 5)]`; (* jump to the halt pc *)

val asm2ast_def = Define`
  asm2ast = MAP (\(b,asm). (b,riscv_ast asm))`;

val asts_encode_def = Define`
  asts_encode = MAP (\(b,ast). (b,FLAT $ MAP riscv_encode ast))`;

val add_halt_and_ccache_def = Define`
  add_halt_and_ccache = (++) (GENLIST (K (F,GENLIST (K 0w) ffi_offset)) 2)`;

val san_flat_def = Define`
  (san_flat [] n = ([],[],[])) /\
  (san_flat ((F,xs)::xss) n =
    let (pcs,pcs',prog) = san_flat xss (n+LENGTH xs) in
    (pcs,pcs',xs++prog)) /\
  (san_flat ((T,xs)::xss) n =
    let (pcs,pcs',prog) = san_flat xss (n+LENGTH xs) in
    (n::pcs,n+LENGTH xs::pcs', xs++prog))`;

val san_result_def = Define`
    san_result =
      flip san_flat 0 o add_halt_and_ccache o asts_encode $
      asm2ast san_prog_asm`;

val san_ffi_pcs_def = Define`
  san_ffi_pcs = MAP n2w o FST $ san_result`;

val san_end_ffi_pcs_def = Define`
  san_end_ffi_pcs = MAP n2w o FST o SND $ san_result`;

val san_program_def = Define`
  san_program = SND o SND $ san_result`;

val san_ffi_interfer_def = Define`
  san_ffi_interfer info_func = K (\((n:num),bytes,state).
    if n = 0 then
      let (nb,ad,reg,new_pc) = info_func n in
      state with
      <|c_gpr := (\pid r.
          if pid = state.procID /\ r = n2w reg
          then 20w
          else state.c_gpr pid r);
        c_PC := (state.procID =+ new_pc) state.c_PC |>
    else state)`;

val san_mmio_info_def = Define`
  san_mmio_info =
    let max_size = dimindex (:64) DIV 8 in
    ((0:num) =+ (n2w max_size,20000w,(6:num),EL 0 san_end_ffi_pcs)) $
    (1 =+ (n2w max_size,20008w,7,EL 1 san_end_ffi_pcs)) $
    K ARB`;

val san_config_def = Define`
  san_config =
  <| prog_addresses := {x | x < 1000w}
   ; ffi_entry_pcs := san_ffi_pcs
   ; ffi_names := ["MappedRead";"MappedWrite"]
   ; ptr_reg := ARB
   ; len_reg := ARB
   ; ptr2_reg := ARB
   ; len2_reg := ARB
   ; ffi_interfer := san_ffi_interfer 
    (san_mmio_info: num -> word8 # word64 # num # word64)
   ; next_interfer := K I
   ; halt_pc := 0w
   ; ccache_pc := n2w ffi_offset
   ; ccache_interfer :=ARB
   ; target := riscv_target
   ; mmio_info := san_mmio_info|>`;

val san_init_ffi_state = Define``;
val san_init_machine_state = Define``;

