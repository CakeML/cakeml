open preamble ffiTheory asmPropsTheory;

val _ = new_theory "targetSem";

(* -- execute target machine with interference from environement -- *)

val () = Datatype `
  machine_result = Halt outcome | Error | TimeOut `;

val _ = Datatype `
  machine_config =
   <| prog_addresses : ('a word) set
    (* FFI-specific configurations *)
    ; ffi_entry_pcs : ('a word) list
    ; ptr_reg : num
    ; len_reg : num
    (* major interference by FFI calls *)
    ; ffi_interfer : num -> num -> word8 list -> 'b -> 'b
    ; callee_saved_regs : num list
    (* minor interference during exeuction *)
    ; next_interfer : num -> 'b -> 'b
    (* program exits successfully at halt_pc *)
    ; halt_pc : 'a word
    (* target next-state function etc. *)
    ; target : ('a,'b,'c) target
    |>`

val evaluate_def = Define `
  evaluate config (ffi:'ffi ffi_state) k (ms:'a) =
    if k = 0 then (TimeOut,ms,ffi)
    else
      if config.target.get_pc ms IN config.prog_addresses then
        let ms1 = config.target.next ms in
        let ms2 = config.next_interfer 0 ms1 in
        let config = config with next_interfer :=
                       shift_seq 1 config.next_interfer in
          if EVERY config.target.state_ok [ms;ms1;ms2] then
            evaluate config ffi (k - 1) ms2
          else
            (Error,ms,ffi)
      else if config.target.get_pc ms = config.halt_pc then
        (if config.target.get_reg ms config.ptr_reg = 0w
         then Halt Success else Halt Resource_limit_hit,ms,ffi)
      else
        case find_index (config.target.get_pc ms) config.ffi_entry_pcs 0 of
        | NONE => (Error,ms,ffi)
        | SOME ffi_index =>
          case read_bytearray (config.target.get_reg ms config.ptr_reg)
                 (w2n (config.target.get_reg ms config.len_reg))
                 (\a. if a IN config.prog_addresses
                      then SOME (config.target.get_byte ms a) else NONE) of
          | NONE => (Error,ms,ffi)
          | SOME bytes =>
            let do_ffi = config.ffi_interfer 0 ffi_index in
            let config = config with ffi_interfer :=
                           shift_seq 1 config.ffi_interfer in
            let (new_ffi,new_bytes) = call_FFI ffi ffi_index bytes in
              if new_ffi.final_event <> NONE
              then (Halt (FFI_outcome (THE new_ffi.final_event)),ms,new_ffi)
              else evaluate config new_ffi (k - 1:num) (do_ffi new_bytes ms)`

val _ = ParseExtras.temp_tight_equality()

val machine_sem_def = Define `
  (machine_sem config st ms (Terminate t io_list) <=>
     ?k ms' st'.
       evaluate config st k ms = (Halt t,ms',st') ∧
       st'.io_events = io_list) /\
  (machine_sem config st ms (Diverge io_trace) <=>
     (!k. ?ms' st'.
            evaluate config st k ms = (TimeOut,ms',st') ∧
            st'.final_event = NONE) /\
     lprefix_lub
       (IMAGE
         (\k. fromList (SND (SND (evaluate config st k ms))).io_events) UNIV)
       io_trace) /\
  (machine_sem config st ms Fail <=>
     ?k. FST (evaluate config st k ms) = Error)`

(* define what it means for code to be loaded and ready to run *)

val code_loaded_def = Define`
  code_loaded (bytes:word8 list) (mc:(α,β,γ)machine_config) (ms:β) <=>
    read_bytearray (mc.target.get_pc ms) (LENGTH bytes)
      (\a. if a IN mc.prog_addresses
           then SOME (mc.target.get_byte ms a) else NONE) = SOME bytes
    (* ... and a few more things that will become clear during the proof *)`;

val _ = export_theory();
