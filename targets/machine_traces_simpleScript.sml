open HolKernel Parse boolLib bossLib;

open wordsTheory asmTheory llistTheory ffi_simpleTheory;

val _ = new_theory "machine_traces_simple";

val () = Datatype `
  trace_part =
      Internal_step_from 'a
    | FFI_call 'a num (word8 list) (word8 list)`

val _ = temp_type_abbrev("machine_trace",``:num->('a trace_part)``);

val has_array_def = Define `
  (has_array s a [] <=> T) /\
  (has_array s a (b::bs) <=>
     a IN s.mem_domain /\ (s.mem a = b) /\ has_array s (a+1w) bs)`;

val set_pc_def = Define `
  set_pc w s = s with pc := w`;

val write_array_def = Define `
  (write_array a [] s = s) /\
  (write_array a (b::bs) s =
     write_array (a + 1w) bs s with mem := (a =+ b) s.mem)`

val is_FFI_def = Define `
  (is_FFI (FFI_call _ _ _ _) = T) /\
  (is_FFI _ = F)`

val get_state_def = Define `
  (get_state (FFI_call s _ _ _) = s) /\
  (get_state (Internal_step_from s) = s)`;

val () = Datatype `
  ffi_config =
    <| link_reg : num ;
       arg_reg : num ;
       ffi_entry_pc : ('a word) list |>`

val () = Datatype `
  trace_config =
    <| next : 'a -> 'a ;
       proj : 'a -> 'b ;
       ffi_conf : 'c ffi_config ;
       asm_machine_rel : 'd asm_state -> 'a -> bool |>`

val trace_ok_def = Define `
  trace_ok c init_state (t:'a machine_trace) <=>
    (* every machine state relates to some asm_state *)
    (!i. ?x. c.asm_machine_rel x (get_state (t i))) /\
    (* first state must be the init state *)
    (get_state (t 0) = init_state) /\
    (* consequtive states are related by the machine next-state
       functions, but may differ arbitrarily on non-projected parts *)
    (!n s1.
       (t n = Internal_step_from s1) ==>
       (c.proj (c.next s1) = c.proj (get_state (t (n+1))))) /\
    (* entry into FFI passes pointer to array correctly etc. *)
    (!n s1 k w1 w2 x1.
       (t n = FFI_call s1 k w1 w2) /\ c.asm_machine_rel x1 s1 ==>
       k < LENGTH c.ffi_conf.ffi_entry_pc /\
       (x1.pc = EL k c.ffi_conf.ffi_entry_pc) /\
       has_array x1 (x1.regs c.ffi_conf.arg_reg) w1) /\
    (* how returning FFI call updates states *)
    (!n s1 k w1 w2 x1 x2.
       (t n = FFI_call s1 k w1 w2) /\ c.asm_machine_rel x1 s1 /\
       c.asm_machine_rel x2 (get_state (t (n+1))) ==>
       (LENGTH w1 = LENGTH w2) /\
       (x2 = write_array (x1.regs c.ffi_conf.arg_reg) w2
               (set_pc (x1.regs c.ffi_conf.link_reg) x1)))`

(* top-level behaviour *)

val dest_FFI_call_def = Define `
  (dest_FFI_call (FFI_call _ n w1 w2) = SOME (IO_event n (ZIP (w1,w2)))) /\
  (dest_FFI_call _ = NONE)`

val fromSeq_def = Define `
  fromSeq f = LUNFOLD (\i. SOME (i+1, f i)) 0`

val mc_sem_def = Define `
  mc_sem c init_state (Behaviour io_trace) <=>
    ?t. trace_ok c init_state t /\
        (io_trace =
         LMAP (THE o dest_FFI_call)
           (LFILTER (IS_SOME o dest_FFI_call) (fromSeq t)))`

val _ = export_theory();
