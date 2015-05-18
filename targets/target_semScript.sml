open HolKernel Parse boolLib bossLib;
open wordsTheory lcsymtacs ffiTheory asmTheory;

val _ = new_theory "target_sem";

(* -- execute target machine with interference from environement -- *)

val () = Datatype `
  error_type = Internal | IO_too_short | IO_wrong_input | IO_too_long `

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
     if x = y then SOME 0 else
       case list_find x ys of
       | NONE => NONE
       | SOME n => SOME (n+1))`

val has_bytearray_def = Define `
  (has_bytearray w [] s <=> T) /\
  (has_bytearray w (b::bs) s <=>
     w IN s.mem_domain /\ (s.mem w = b) /\
     has_bytearray (w+1w) bs s)`

val LPOP_def = Define `
  LPOP ll =
    case LHD ll of NONE => NONE | SOME x => SOME (x, THE (LTL ll))`;

val mEval_def = Define `
  mEval config io k (ms:'a) =
    if k = 0 then (TimeOut,ms,io) else
      case some s. config.state_rel s ms of
      | NONE => (Error Internal,ms,io)
      | SOME s =>
         if s.pc IN config.prog_addresses then
           mEval config io (k - 1)
             (config.next_interfer k (config.next ms))
         else if s.pc = config.halt_pc then
           (Result,ms,io)
         else case list_find s.pc config.ffi_entry_pcs of
           | NONE => (Error Internal,ms,io)
           | SOME i =>
               case LPOP io of
               | NONE => (Error IO_too_short,ms,io)
               | SOME (IO_event n bs,io) =>
                  if n <> i then
                    (Error IO_wrong_input,ms,io)
                  else if w2n (s.regs config.len_reg) <> LENGTH bs then
                    (Error IO_wrong_input,ms,io)
                  else if has_bytearray (s.regs config.ptr_reg)
                           (MAP FST bs) s then
                    (Error IO_wrong_input,ms,io)
                  else
                    mEval config io (k - 1)
                      (config.ffi_interfer k n (MAP SND bs) ms)`

(* -- observable -- *)

val () = Datatype `
  observable = Terminate fin_io_trace
             | Diverge io_trace `;

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
     ?k ms' io'.
       (mEval config (fromList io_list) k ms = (Result,ms',io')) /\
       (LLENGTH io' = SOME 0)) /\
  (machine_sem config ms (Diverge io_trace) =
     (!k. (FST (mEval config io_trace k ms) = TimeOut)) /\
     (!io. LPREFIX io io_trace /\ io <> io_trace ==>
           ?k. (FST (mEval config io k ms) <> TimeOut)))`

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
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []);

val imprecise_machine_sem_LAPPEND = store_thm(
   "imprecise_machine_sem_LAPPEND",
  ``(Diverge io_trace) IN machine_sem config ms ==>
    !l. (Diverge (LAPPEND io_trace l)) IN
             imprecise_machine_sem config ms``,
  fs [IN_DEF,machine_sem_def,imprecise_machine_sem_def]
  \\ METIS_TAC [mEval_LAPPEND_io]);

val _ = export_theory();
