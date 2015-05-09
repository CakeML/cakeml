open HolKernel Parse boolLib bossLib;

open wordsTheory asmTheory llistTheory;

val _ = new_theory "machine_traces";

val () = Datatype `
  trace_part =
      Internal_step_from 'a
    | FFI_call 'a num (word8 list) (word8 list)
    | FFI_no_return 'a num (word8 list)`

val _ = temp_type_abbrev("machine_trace",``:('a trace_part) llist``);

val () = Datatype `
  ffi_config =
    <| link_reg : num ;
       arg_reg : num ;
       ffi_entry_pc : ('a word) list |>`

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

val calling_convention_respected_def = Define `
  calling_convention_respected c (s1:'a asm_state) n w1 w2 s2 <=>
    n < LENGTH c.ffi_entry_pc /\
    has_array s1 (s1.regs c.arg_reg) w1 /\
    (LENGTH w1 = LENGTH w2) /\
    (s2 = write_array (s1.regs c.arg_reg) w2 (set_pc (s1.regs c.link_reg) s1))`;

val is_FFI_def = Define `
  (is_FFI (FFI_call _ _ _ _) = T) /\
  (is_FFI (FFI_no_return _ _ _) = T) /\
  (is_FFI _ = F)`

val get_state_def = Define `
  (get_state (FFI_call s _ _ _) = s) /\
  (get_state (FFI_no_return s _ _) = s) /\
  (get_state (Internal_step_from s) = s)`;

val trace_ok_def = Define `
  trace_ok init_state next proj (t:'a machine_trace) ffi_conf R <=>
    (* every machine state relates to some asm_state *)
    (!i p. (LNTH i t = SOME p) ==> ?x. R x (get_state p)) /\
    (* first state must be the init state *)
    (?p. (LNTH 0 t = SOME p) /\ (get_state p = init_state)) /\
    (* the FFI_no_return element can only appear at the end of a
       finite trace, a finite trace does not need to end in FFI_no_return *)
    (!i s n w.
       (LNTH i t = SOME (FFI_no_return s n w)) ==>
       (LLENGTH t = SOME (i+1))) /\
    (* consequtive states are related by the machine next-state
       functions, but may differ arbitrarily on non-projected parts *)
    (!n s1 p.
       (LNTH n t = SOME (Internal_step_from s1)) /\
       (LNTH (n+1) t = SOME p) ==>
       (proj (next s1) = proj (get_state p))) /\
    (* state-FFI-state i.e. how returning FFI call updates states *)
    (!n s1 p k w1 w2 x1 x2.
       (LNTH n t = SOME (FFI_call s1 k w1 w2)) /\ R x1 s1 /\
       (LNTH (n+1) t = SOME p) /\ R x2 (get_state p) ==>
       calling_convention_respected ffi_conf x1 n w1 w2 x2)`

val _ = export_theory();
