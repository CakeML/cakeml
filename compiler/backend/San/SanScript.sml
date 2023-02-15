(*
* A simple instantiation of machin_config for sanity check
*)
open preamble targetSemTheory riscv_targetTheory riscvTheory;

val _ = new_theory "San";

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

val san_enc_result_def = Define`
    san_enc_result =
      flip san_flat 0 o add_halt_and_ccache o asts_encode $
      asm2ast san_prog_asm`;

val san_ffi_pcs_def = Define`
  san_ffi_pcs = MAP n2w o FST $ san_enc_result`;

val san_end_ffi_pcs_def = Define`
  san_end_ffi_pcs = MAP n2w o FST o SND $ san_enc_result`;

val san_program_def = Define`
  san_program = SND o SND $ san_enc_result`;

val san_ffi_interfer_def = Define`
  san_ffi_interfer info_func = K (\((n:num),bytes,state).
    if n = 0 then
      let (nb,ad,reg,new_pc) = info_func n in
      state with
      <|c_gpr := (\pid r.
          if pid = state.procID /\ r = n2w reg
          then n2w (bytes2num bytes)
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

val san_oracle_def = Define`
  san_oracle s () l1 l2 =
    Oracle_return () 
      (PAD_RIGHT 0w (LENGTH l2) [20w])`; 

val san_init_ffi_state_def = Define`
  san_init_ffi_state =
    <|oracle := san_oracle;
      ffi_state := ();
      io_events := []|>`;

val san_init_pc_def = Define`
  san_init_pc = n2w $ ffi_offset * 2`;

val word_EL_def = Define`
  word_EL l start w = EL (w2n (w - start)) l`;

val san_init_machine_state_def = Define`
  san_init_machine_state =
    ARB with
    <|c_PC := (0w =+ san_init_pc) ARB;
      procID := 0w;
      MEM8 := word_EL san_program 0w|>`;

val san_result_def = Define`
  san_result n =
  evaluate san_config san_init_ffi_state n san_init_machine_state`;

val all_riscv_Defs = map fst o filter (fn n => snd n = Def ) o 
  map snd $ DB.match ["riscv"] ``_``;

val _ = computeLib.add_funs all_riscv_Defs;

EVAL ``san_program``;
EVAL ``san_result 0``;
(* EVAL ``san_result 1``; *)
