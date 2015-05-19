open HolKernel Parse boolLib bossLib;
open wordsTheory lcsymtacs ffiTheory asmTheory;

val _ = new_theory "target_sem";

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
    (* target next-state fuction *)
    ; next : 'b -> 'b
    (* minor interference during exeuction *)
    ; next_interfer : num -> 'b -> 'b
    (* relation between asm states and machine states *)
    ; state_rel : 'a asm_state -> 'b -> bool
    (* program exits successfully at halt_pc *)
    ; halt_pc : 'a word
    |>`

val list_find_def = Define `
  (list_find x [] = NONE) /\
  (list_find x (y::ys) =
     if x = y then SOME (0:num) else
       case list_find x ys of
       | NONE => NONE
       | SOME n => SOME (n+1))`

val read_bytearray_def = Define `
  (read_bytearray a 0 s = SOME []) /\
  (read_bytearray a (SUC n) s =
     if ~(a IN s.mem_domain) then NONE else
       case read_bytearray (a+1w) n s of
       | SOME bytes => SOME ((s.mem a)::bytes)
       | _ => NONE)`

val write_bytearray_def = Define `
  (write_bytearray a [] s = s) /\
  (write_bytearray a (b::bs) s =
     let s' = write_bytearray (a+1w) bs s in
       s' with mem := (a =+ b) s'.mem)`

val mEval_def = Define `
  mEval config io k (ms:'a) =
    if k = 0 then (TimeOut,ms,io)
    else
      case some s. config.state_rel s ms of
      | NONE => (Error Internal,ms,io)
      | SOME s =>
         if s.pc IN config.prog_addresses then
           mEval config io (k - 1)
             (config.next_interfer k (config.next ms))
         else if s.pc = config.halt_pc then
           (Result,ms,io)
         else
           case list_find s.pc config.ffi_entry_pcs of
           | NONE => (Error Internal,ms,io)
           | SOME ffi_index =>
             case read_bytearray (s.regs config.ptr_reg)
                    (w2n (s.regs config.len_reg)) s of
             | NONE => (Error Internal,ms,io)
             | SOME bytes =>
               case call_FFI ffi_index bytes io of
               | NONE => (Error IO_mismatch,ms,io)
               | SOME (new_bytes,new_io) =>
                   mEval config new_io (k - 1)
                     (config.ffi_interfer k ffi_index new_bytes ms)`

(* -- observable -- *)

val LPREFIX_def = Define `
  LPREFIX l1 l2 =
    case toList l1 of
    | NONE => (l1 = l2)
    | SOME xs =>
        case toList l2 of
        | NONE => LTAKE (LENGTH xs) l2 = SOME xs
        | SOME ys => isPREFIX xs ys`

val machine_sem_def = Define `
  (machine_sem config ms (Terminate io_list) =
     ?k ms'.
       (mEval config (fromList io_list) k ms = (Result,ms',LNIL))) /\
  (machine_sem config ms (Diverge io_trace) =
     (!k. (FST (mEval config io_trace k ms) = TimeOut)) /\
     (!io. LPREFIX io io_trace /\ io <> io_trace ==>
           ?k. (FST (mEval config io k ms) <> TimeOut))) /\
  (machine_sem config ms Fail =
     ?k io. FST (mEval config io k ms) = Error Internal)`

(* Note: we need to prove that every well-typed program has some
   behaviour, i.e. machine_sem config ms should never be the empty set
   for well-typed programs. *)

(* The semantics that was defined above is exact regarding to the IO
   traces it accepts. In some proofs, it might be easier to use a less
   exact semantics. The following variant admits any extension of an
   divergent I/O trace. *)

val imprecise_machine_sem_def = Define `
  (imprecise_machine_sem config ms (Terminate io_list) =
     ?k ms' io'.
       (mEval config (fromList io_list) k ms = (Result,ms',io')) /\
       (LLENGTH io' = SOME 0)) /\
  (imprecise_machine_sem config ms (Diverge io_trace) =
     !k. (FST (mEval config io_trace k ms) = TimeOut))`

val mEval_LAPPEND_io = prove(
  ``!k ms io_trace.
      (FST (mEval config io_trace k ms) = TimeOut) ==>
      (FST (mEval config (LAPPEND io_trace l) k ms) = TimeOut)``,
  cheat
(*
  Induct THEN1 (ONCE_REWRITE_TAC [mEval_def] \\ fs [])
  \\ ONCE_REWRITE_TAC [mEval_def] \\ fs []
  \\ Cases_on `some s. config.state_rel s ms` \\ fs []
  \\ Cases_on `x.pc IN config.prog_addresses` \\ fs []
  \\ Cases_on `x.pc = config.halt_pc` \\ fs []
  \\ Cases_on `list_find x.pc config.ffi_entry_pcs` \\ fs []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `LPOP io_trace` \\ fs []
  \\ Q.MATCH_ASSUM_RENAME_TAC `LPOP io_trace = SOME i`
  \\ fs [LPOP_def]
  \\ `(io_trace = [||]) ∨ ∃h t. io_trace = h:::t` by
          METIS_TAC [llistTheory.llist_CASES] \\ fs []
  \\ SRW_TAC [] [] \\ Cases_on `h` \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
*)
);

val imprecise_machine_sem_LAPPEND = store_thm(
   "imprecise_machine_sem_LAPPEND",
  ``(Diverge io_trace) IN machine_sem config ms ==>
    !l. (Diverge (LAPPEND io_trace l)) IN
             imprecise_machine_sem config ms``,
  fs [IN_DEF,machine_sem_def,imprecise_machine_sem_def]
  \\ METIS_TAC [mEval_LAPPEND_io]);

val _ = export_theory();
