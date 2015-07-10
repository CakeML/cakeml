open preamble ffiTheory asmTheory;

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
  error_type = Internal | IO_mismatch `

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
  evaluate config io k (ms:'a) =
    if k = 0 then (TimeOut,ms,io)
    else
      if config.f.get_pc ms IN config.prog_addresses then
        let ms1 = config.f.next ms in
        let ms2 = config.next_interfer 0 ms1 in
        let config = config with next_interfer :=
                       shift_seq 1 config.next_interfer in
          if EVERY config.f.state_ok [ms;ms1;ms2] then
            evaluate config io (k - 1) ms2
          else
            (Error Internal,ms,io)
      else if config.f.get_pc ms = config.halt_pc then
        (Result,ms,io)
      else
        case list_find (config.f.get_pc ms) config.ffi_entry_pcs of
        | NONE => (Error Internal,ms,io)
        | SOME ffi_index =>
          case read_bytearray (config.f.get_reg ms config.ptr_reg)
                 (w2n (config.f.get_reg ms config.len_reg))
                 (\a. if a IN config.prog_addresses
                      then SOME (config.f.get_byte ms a) else NONE) of
          | NONE => (Error Internal,ms,io)
          | SOME bytes =>
            let ffi = config.ffi_interfer 0 ffi_index in
            let config = config with ffi_interfer :=
                           shift_seq 1 config.ffi_interfer in
            let (new_bytes,new_io) = call_FFI ffi_index bytes io in
              if new_io = NONE then (Error IO_mismatch,ms,new_io) else
                evaluate config new_io (k - 1:num) (ffi new_bytes ms)`


(* -- observable -- *)

val machine_sem_def = Define `
  (machine_sem config ms (Terminate io_list) =
     ?k ms'.
       (evaluate config (SOME (fromList io_list)) k ms = (Result,ms',SOME LNIL))) /\
  (machine_sem config ms (Diverge io_trace) =
     (!k. (FST (evaluate config (SOME io_trace) k ms) = TimeOut)) /\
     (!io. LPREFIX io io_trace /\ io <> io_trace ==>
           ?k. (FST (evaluate config (SOME io) k ms) <> TimeOut))) /\
  (machine_sem config ms Fail =
     ?k io. FST (evaluate config io k ms) = Error Internal)`

(* Note: we need to prove that every well-typed program has some
   behaviour, i.e. machine_sem config ms should never be the empty set
   for well-typed programs. *)

(* The semantics that was defined above is exact regarding to the IO
   traces it accepts. In some proofs, it might be easier to use a less
   exact semantics. The following variant admits any extension of an
   divergent I/O trace. *)

val imprecise_machine_sem_def = Define `
  (imprecise_machine_sem config ms (Terminate io_list) =
     ?k ms'.
       evaluate config (SOME (fromList io_list)) k ms = (Result,ms',SOME LNIL)) /\
  (imprecise_machine_sem config ms (Diverge io_trace) =
     !k. (FST (evaluate config (SOME io_trace) k ms) = TimeOut))`

val _ = export_theory();
