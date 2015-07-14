open preamble ffiTheory targetSemTheory;

val _ = new_theory"targetProps";

(* TODO: move? *)

val call_FFI_LAPPEND = prove(
  ``(call_FFI x' x (SOME io_trace) = (q,SOME r)) ==>
    (call_FFI x' x (SOME (LAPPEND io_trace l)) = (q,SOME (LAPPEND r l)))``,
  fs [call_FFI_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [LET_DEF]
  \\ SRW_TAC [] [] \\ fs [llistTheory.LAPPEND]
  \\ `(io_trace = [||]) \/ ?h t. io_trace = h:::t` by
          METIS_TAC [llistTheory.llist_CASES]
  \\ fs [] \\ SRW_TAC [] [] \\ fs []);

(* -- *)

val evaluate_LAPPEND_io = prove(
  ``!k ms io_trace config.
      (FST (evaluate config (SOME io_trace) k ms) = TimeOut) ==>
      (FST (evaluate config (SOME (LAPPEND io_trace l)) k ms) = TimeOut)``,
  Induct THEN1 (ONCE_REWRITE_TAC [evaluate_def] \\ fs [])
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ fs [] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [LET_DEF]
  \\ SRW_TAC [] [] \\ fs [] \\ fs []
  \\ Cases_on `call_FFI x' x (SOME io_trace)` \\ fs []
  \\ Cases_on `r` \\ fs []
  \\ IMP_RES_TAC call_FFI_LAPPEND
  \\ fs [] \\ SRW_TAC [] []);

val imprecise_machine_sem_LAPPEND = store_thm(
   "imprecise_machine_sem_LAPPEND",
  ``(Diverge io_trace) IN machine_sem config ms ==>
    !l. (Diverge (LAPPEND io_trace l)) IN
             imprecise_machine_sem config ms``,
  fs [IN_DEF,machine_sem_def,imprecise_machine_sem_def]
  \\ METIS_TAC [evaluate_LAPPEND_io]);

val _ = export_theory();
