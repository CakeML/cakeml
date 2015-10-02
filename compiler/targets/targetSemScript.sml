open preamble ffiTheory asmPropsTheory;

val _ = new_theory "targetSem";

(* TODO: move? *)

val _ = Parse.temp_overload_on("list_find",``λx ls. find_index x ls 0``);

val read_bytearray_def = Define `
  (read_bytearray a 0 get_byte = SOME []) /\
  (read_bytearray a (SUC n) get_byte =
     case get_byte a of
     | NONE => NONE
     | SOME b => case read_bytearray (a+1w) n get_byte of
                 | NONE => NONE
                 | SOME bs => SOME (b::bs))`

val shift_seq_def = Define `
  shift_seq k s = \i. s (i + k:num)`;

(* -- *)

(* -- execute target machine with interference from environement -- *)

val () = Datatype `
  error_type = Internal | IO_mismatch | Limit `

val () = Datatype `
  machine_result = Result | TimeOut | Error error_type `;

val _ = Datatype `
  machine_config =
   <| prog_addresses : ('a word) set
    (* FFI-specific configurations *)
    ; ffi_entry_pcs : ('a word) list
    ; ptr_reg : num
    ; len_reg : num
    (* major interference by FFI calls *)
    ; ffi_interfer : num -> num -> word8 list -> 'b -> 'b
    (* minor interference during exeuction *)
    ; next_interfer : num -> 'b -> 'b
    (* program exits successfully at halt_pc *)
    ; halt_pc : 'a word
    (* assembly configuration *)
    ; asm_config : 'a asm_config
    (* target next-state fuction etc. *)
    ; f : ('a,'b,'c) target_funs
    |>`

val evaluate_def = Define `
  evaluate config (ffi:'ffi ffi_state) k (ms:'a) =
    if k = 0 then (TimeOut,ms,ffi)
    else
      if config.f.get_pc ms IN config.prog_addresses then
        let ms1 = config.f.next ms in
        let ms2 = config.next_interfer 0 ms1 in
        let config = config with next_interfer :=
                       shift_seq 1 config.next_interfer in
          if EVERY config.f.state_ok [ms;ms1;ms2] then
            evaluate config ffi (k - 1) ms2
          else
            (Error Internal,ms,ffi)
      else if config.f.get_pc ms = config.halt_pc then
        (if config.f.get_reg ms config.ptr_reg = 0w
         then Result else Error Limit,ms,ffi)
      else
        case list_find (config.f.get_pc ms) config.ffi_entry_pcs of
        | NONE => (Error Internal,ms,ffi)
        | SOME ffi_index =>
          case read_bytearray (config.f.get_reg ms config.ptr_reg)
                 (w2n (config.f.get_reg ms config.len_reg))
                 (\a. if a IN config.prog_addresses
                      then SOME (config.f.get_byte ms a) else NONE) of
          | NONE => (Error Internal,ms,ffi)
          | SOME bytes =>
            let do_ffi = config.ffi_interfer 0 ffi_index in
            let config = config with ffi_interfer :=
                           shift_seq 1 config.ffi_interfer in
            let (new_ffi,new_bytes) = call_FFI ffi ffi_index bytes in
              if new_ffi.ffi_failed then (Error IO_mismatch,ms,new_ffi) else
                evaluate config new_ffi (k - 1:num) (do_ffi new_bytes ms)`

val _ = ParseExtras.temp_tight_equality()

val machine_result_def = Define`
  (machine_result Success = Result) ∧
  (machine_result FFI_error = Error IO_mismatch) ∧
  (machine_result Resource_limit_hit = Error Limit)`;

val machine_sem_def = Define `
  (machine_sem config st ms (Terminate t io_list) <=>
     ?k ms' st'.
       evaluate config st k ms = (machine_result t,ms',st') ∧
       REVERSE st'.io_events = io_list) /\
  (machine_sem config st ms (Diverge io_trace) <=>
     (!k. ?ms' st' n.
            evaluate config st k ms = (TimeOut,ms',st') ∧
            LTAKE n io_trace = SOME (REVERSE st'.io_events)) /\
     (!n io_list. LTAKE n io_trace = SOME io_list ⇒
        ?k. REVERSE (SND(SND(evaluate config st k ms))).io_events = io_list)) /\
  (machine_sem config st ms Fail <=>
     ?k. FST (evaluate config st k ms) = Error Internal)`

(* Note: we need to prove that every well-typed program has some
   behaviour, i.e. machine_sem config ms should never be the empty set
   for well-typed programs. *)

(* The semantics that was defined above is exact regarding to the IO
   traces it accepts. In some proofs, it might be easier to use a less
   exact semantics. The following variant admits any extension of an
   divergent I/O trace. *)

val imprecise_machine_sem_def = Define `
  (imprecise_machine_sem config st ms (Terminate t io_list) <=>
     ?k ms' st'.
       evaluate config st k ms = (machine_result t,ms',st') ∧
       REVERSE st'.io_events = io_list) /\
  (imprecise_machine_sem config st ms (Diverge io_trace) <=>
     (!k. ∃ms' st' n.
       evaluate config st k ms = (TimeOut,ms',st') ∧
       LTAKE n io_trace = SOME (REVERSE st'.io_events)))`

(* define what it means for code to be loaded and ready to run *)

val code_loaded_def = Define`
  code_loaded (bytes:word8 list) (mc:(α,β,γ)machine_config) (ms:β) <=>
    read_bytearray (mc.f.get_pc ms) (LENGTH bytes)
      (\a. if a IN mc.prog_addresses
           then SOME (mc.f.get_byte ms a) else NONE) = SOME bytes
    (* ... and a few more things that will become clear during the proof *)`;

val _ = export_theory();
