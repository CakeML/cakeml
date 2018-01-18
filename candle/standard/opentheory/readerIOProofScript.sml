open preamble readerTheory readerIOTheory readerProofTheory ml_monadBaseTheory
     holKernelTheory holKernelProofTheory

val readLine_wrap_thm = Q.store_thm("readLine_wrap_thm",
  `READER_STATE defs s /\
   STATE defs refs /\
   readLine_wrap l s refs = (res, refs')
   ==>
   ?ds.
     STATE (ds ++ defs) refs' /\
     !s. res = Success (INR s) ==> READER_STATE (ds ++ defs) s`,
  rw [readLine_wrap_def, handle_Fail_def, st_ex_bind_def, st_ex_return_def,
      case_eq_thms]
  \\ metis_tac [readLine_thm]);

val readLines_def = readerIOTheory.readLines_def
val readLines_ind = readerIOTheory.readLines_ind

val readLines_thm = Q.store_thm("readLines_thm",
  `!s lines res c c' defs.
     STATE defs c.holrefs /\
     READER_STATE defs s /\
     readLines s lines c = (res, c')
     ==>
     ?ds x.
       res = Success x /\
       STATE (ds ++ defs) c'.holrefs /\
       !s n. x = INR s ==> READER_STATE (ds ++ defs) s`,
  recInduct readLines_ind \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [readLines_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ CASE_TAC \\ fs []
  >- (rw [] \\ qexists_tac `[]` \\ fs [])
  \\ rw [] \\ fs []
  >- metis_tac [next_line_thm]
  \\ fs [case_eq_thms, liftM_def, print_err_def] \\ pairarg_tac \\ fs [] \\ rw []
  \\ TRY FULL_CASE_TAC \\ fs [] \\ rw []
  \\ drule (GEN_ALL readLine_wrap_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ TRY (fs [readLine_wrap_def, handle_Fail_def, st_ex_return_def, st_ex_bind_def, case_eq_thms] \\ rw [] \\ fs [])
  \\ qmatch_asmsub_abbrev_tac `readLines _ _ c1`
  \\ `STATE (ds++defs) c1.holrefs` by fs [Abbr `c1`]
  \\ imp_res_tac next_line_thm \\ fs []
  \\ first_x_assum drule
  \\ rpt (disch_then drule) \\ rw []
  \\ metis_tac []);

val READER_STATE_init_state = Q.store_thm("READER_STATE_init_state[simp]",
  `READER_STATE defs init_state`,
  rw [READER_STATE_def, init_state_def, STATE_def, lookup_def]);

val reader_main_thm = Q.store_thm("reader_main_thm",
  `reader_main () (c with holrefs := init_refs) = (res, c')
   ==>
   res = Success () /\
   ?ds. STATE ds c'.holrefs`,
  rw [reader_main_def, st_ex_bind_def, st_ex_return_def, case_eq_thms,
      arguments_def, inputLinesFrom_def, print_err_def, print_def, bool_case_eq,
      COND_RATOR, liftM_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ imp_res_tac set_reader_ctxt_ok \\ fs []
  \\ TRY
   (rw [STATE_def, CONTEXT_def]
    \\ EVAL_TAC \\ fs []
    \\ NO_TAC)
  \\ qmatch_asmsub_abbrev_tac `readLines _ ls c1`
  \\ `STATE defs c1.holrefs` by fs [Abbr`c1`]
  \\ drule (GEN_ALL readLines_thm)
  \\ disch_then (qspecl_then [`init_state`,`ls`] mp_tac) \\ fs [] \\ rw []
  \\ asm_exists_tac \\ fs []);

(*

 `VALID_HEAP s /\
  STDIO c.stdio s /\
  HOL_REFS c.holrefs s /\
  CL c.cl s /\
  reader_main () (c with holrefs := init_refs) = (res, c')
  ==>
  res = Success () /\
  STDIO c'.stdio s /\
  HOL_REFS c'.holrefs s /\
  CL c'.cl s`

  ???

*)

val _ = export_theory ();

