open preamble ffiTheory asmPropsTheory;

val _ = new_theory "targetSem";

(* -- execute target machine with interference from environment -- *)

val () = Datatype `
  machine_result = Halt outcome | Error | TimeOut `;

val _ = Datatype `
  machine_config =
   <| prog_addresses : ('a word) set
    (* FFI-specific configurations *)
    ; ffi_entry_pcs : ('a word) list
    ; ffi_names : string list
    ; ptr_reg : num
    ; len_reg : num
    (* major interference by FFI calls *)
    ; ffi_interfer : num -> num # word8 list # 'b -> 'b
    ; callee_saved_regs : num list
    (* minor interference during execution *)
    ; next_interfer : num -> 'b -> 'b
    (* program exits successfully at halt_pc *)
    ; halt_pc : 'a word
    (* target next-state function etc. *)
    ; target : ('a,'b,'c) target
    |>`

val apply_oracle_def = Define `
  apply_oracle oracle x =
    (oracle (0:num) x, shift_seq 1 oracle)`

val evaluate_def = Define `
  evaluate mc (ffi:'ffi ffi_state) k (ms:'a) =
    if k = 0 then (TimeOut,ms,ffi)
    else
      if mc.target.get_pc ms IN mc.prog_addresses then
        let ms1 = mc.target.next ms in
        let (ms2,new_oracle) = apply_oracle mc.next_interfer ms1 in
        let mc = mc with next_interfer := new_oracle in
          if EVERY mc.target.state_ok [ms;ms1;ms2] then
            evaluate mc ffi (k - 1) ms2
          else
            (Error,ms,ffi)
      else if mc.target.get_pc ms = mc.halt_pc then
        (if mc.target.get_reg ms mc.ptr_reg = 0w
         then Halt Success else Halt Resource_limit_hit,ms,ffi)
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => (Error,ms,ffi)
        | SOME ffi_index =>
          case read_bytearray (mc.target.get_reg ms mc.ptr_reg)
                 (w2n (mc.target.get_reg ms mc.len_reg))
                 (\a. if a IN mc.prog_addresses
                      then SOME (mc.target.get_byte ms a) else NONE) of
          | NONE => (Error,ms,ffi)
          | SOME bytes =>
            let (new_ffi,new_bytes) = call_FFI ffi (EL ffi_index mc.ffi_names) bytes(*TODO:wrong*) bytes in
            let (ms1,new_oracle) = apply_oracle mc.ffi_interfer (ffi_index,new_bytes,ms) in
            let mc = mc with ffi_interfer := new_oracle in
              if new_ffi.final_event <> NONE
              then (Halt (FFI_outcome (THE new_ffi.final_event)),ms,new_ffi)
              else evaluate mc new_ffi (k - 1:num) ms1`

val machine_sem_def = Define `
  (machine_sem mc st ms (Terminate t io_list) <=>
     ?k ms' st'.
       evaluate mc st k ms = (Halt t,ms',st') ∧
       st'.io_events = io_list) /\
  (machine_sem mc st ms (Diverge io_trace) <=>
     (!k. ?ms' st'.
            evaluate mc st k ms = (TimeOut,ms',st') ∧
            st'.final_event = NONE) /\
     lprefix_lub
       (IMAGE
         (\k. fromList (SND (SND (evaluate mc st k ms))).io_events) UNIV)
       io_trace) /\
  (machine_sem mc st ms Fail <=>
     ?k. FST (evaluate mc st k ms) = Error)`

(* define what it means for code to be loaded and ready to run *)

val code_loaded_def = Define`
  code_loaded (bytes:word8 list) (mc:(α,β,γ)machine_config) (ms:β) <=>
    read_bytearray (mc.target.get_pc ms) (LENGTH bytes)
      (\a. if a IN mc.prog_addresses
           then SOME (mc.target.get_byte ms a) else NONE) = SOME bytes
    (* ... and a few more things that will become clear during the proof *)`;

val _ = export_theory();
