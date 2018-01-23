open preamble
     readerTheory readerProofTheory
     readerIOTheory
     holKernelTheory holKernelProofTheory
     ml_monadBaseTheory
     TextIOProofTheory CommandLineProofTheory

val _ = new_theory "readerIOProof"

(* ------------------------------------------------------------------------- *)
(* Monadic I/O reader preserves invariants                                   *)
(* ------------------------------------------------------------------------- *)

(*
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
  >- (qexists_tac `[]` \\ fs [])
  \\ metis_tac [readLine_thm]);

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
  \\ fs [readLine_wrap_def, handle_Fail_def, st_ex_return_def,
         st_ex_bind_def, case_eq_thms]
  \\ rw [] \\ fs [] \\ rfs [] \\ fs [case_eq_thms] \\ rw [] \\ fs []
  \\ qmatch_asmsub_abbrev_tac `readLines _ _ c1`
  \\ `STATE (ds++defs) c1.holrefs` by fs [Abbr `c1`]
  \\ imp_res_tac next_line_thm \\ fs []
  \\ first_x_assum drule
  \\ rpt (disch_then drule) \\ rw []
  \\ metis_tac []);

(* TODO move *)
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
*)

(* ------------------------------------------------------------------------- *)
(* Monadic I/O reader satisfies I/O specification                            *)
(* ------------------------------------------------------------------------- *)

val readLine_wrap_correct = Q.store_thm("readLine_wrap_correct",
  `readLine_wrap line s refs = (res, refs_out) /\
   process_line s refs line = res_p
   ==>
   case res of
     Success (INL s) (* Error *) => res_p = (INR s, refs_out)
   | Success (INR s) (* Ok *)    => res_p = (INL s, refs_out)
   | _ => F (* Does not happen *)`,
  rw [readLine_wrap_def, handle_Fail_def, st_ex_bind_def, st_ex_return_def,
      process_line_def, case_eq_thms] \\ fs []);

val readLine_EQ = Q.store_thm("readLine_EQ",
  `readLine_wrap line s refs = (res1, t1) /\
   ~invalid_line line /\
   readLine (fix_fun_typ (str_prefix line)) s refs = (res2, t2)
   ==>
   t1 = t2 /\
   case res1 of
     Success (INL e) => res2 = Failure (Fail e)
   | Success (INR s) => res2 = Success s
   | _ => F`,
  rw [readLine_wrap_def, st_ex_bind_def, st_ex_return_def, handle_Fail_def,
      case_eq_thms] \\ fs []);

val readLine_wrap_invalid_line = Q.store_thm("readLine_wrap_invalid_line",
  `invalid_line h ==> readLine_wrap h s c = (Success (INR s), c)`,
  rw [readLine_wrap_def, st_ex_return_def]);

val readLines_EQ = Q.store_thm("readLines_EQ",
  `!s line c res1 c_out res2 refs.
     readLines s line c = (res1, c_out) /\
     readLines line s c.holrefs = (res2, refs)
     ==>
     refs = c_out.holrefs /\
     res1 = Success () /\
     case res2 of
       Success (_,n) => c_out.stdio = add_stdout c.stdio (msg_success n)
     | Failure (Fail e) => c_out.stdio = add_stderr c.stdio e
     | _ => F`,
  recInduct readLines_ind \\ rw []
  \\ ntac 2 (pop_assum mp_tac)
  \\ once_rewrite_tac [readLines_def, readerTheory.readLines_def]
  \\ CASE_TAC \\ fs [st_ex_bind_def, st_ex_return_def, handle_Fail_def,
                     raise_Fail_def]
  \\ TRY (rw [print_def, liftM_def] \\ rw [] \\ NO_TAC)
  \\ rw [case_eq_thms, bool_case_eq, COND_RATOR]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [liftM_def, print_err_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ TRY (qpat_x_assum `(_,_) = _` (assume_tac o GSYM))
  \\ imp_res_tac readLine_wrap_invalid_line \\ fs [] \\ rw []
  \\ imp_res_tac readLine_EQ \\ fs [] \\ rw []
  \\ first_x_assum drule \\ simp []);

val readFile_correct = Q.store_thm("readFile_correct",
  `readFile fname c = (res, c_out) /\
   read_file c.stdio c.holrefs fname = (fs, refs)
   ==>
   res = Success () /\ fs = c_out.stdio /\ refs = c_out.holrefs`,
  rw [readFile_def, read_file_def, st_ex_bind_def, st_ex_return_def,
      case_eq_thms]
  \\ every_case_tac \\ fs []
  \\ fs [liftM_def, print_err_def, print_def, inputLinesFrom_def] \\ rw []
  \\ rename1 `readLines lines init_state`
  \\ imp_res_tac readLines_EQ \\ fs [] \\ rw [] \\ rfs [])

val _ = export_theory ();

