(*
  Verification of the OpenTheory article checker expressed using an IO
  monad for the basis.
*)
open preamble
     readerTheory readerProofTheory
     readerIOTheory
     holKernelTheory holKernelProofTheory
     ml_monadBaseTheory
     TextIOProofTheory CommandLineProofTheory

val _ = new_theory "readerIOProof"

(* ------------------------------------------------------------------------- *)
(* Wrappers are ok                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem readLine_wrap_thm:
   READER_STATE defs s /\
   STATE defs refs /\
   readLine_wrap (l, s) refs = (res, refs')
   ==>
   ?ds x.
     res = Success x /\
     STATE (ds ++ defs) refs' /\
     !s. x = INR s ==> READER_STATE (ds ++ defs) s
Proof
  rw [readLine_wrap_def, handle_Fail_def, st_ex_bind_def,
      st_ex_return_def, case_eq_thms]
  \\ fs []
  \\ metis_tac [readLine_thm, APPEND_NIL]
QED

Theorem init_reader_wrap_thm:
   init_reader_wrap () init_refs = (res, refs')
   ==>
   ?defs x.
     res = Success x /\
     STATE defs refs'
Proof
  rw [init_reader_wrap_def, handle_Fail_def, st_ex_bind_def, st_ex_return_def,
      case_eq_thms] \\ fs []
  \\ metis_tac [init_reader_ok]
QED

(* ------------------------------------------------------------------------- *)
(* Monadic I/O reader preserves invariants                                   *)
(* ------------------------------------------------------------------------- *)

Theorem ffi_msg_simp[simp]:
   ffi_msg msg s = (Success (), s)
Proof
  rw [ffi_msg_def, st_ex_return_def]
QED

Theorem readLines_thm:
   !s lines res st st1 defs.
     STATE defs st.holrefs /\
     READER_STATE defs s /\
     readLines s lines st = (res, st1)
     ==>
     ?ds x.
       res = Success () /\
       STATE (ds ++ defs) st1.holrefs
Proof
  recInduct readLines_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once readLines_def]
  \\ fs [st_ex_return_def, st_ex_bind_def, liftM_def]
  \\ Cases_on `lines` \\ fs []
  >-
   (rw [print_def, state_refs_component_equality, context_def,
        get_the_context_def]
    \\ metis_tac [APPEND_NIL])
  \\ CASE_TAC
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ rw [case_eq_thms] \\ fs [] THENL
    [ALL_TAC, imp_res_tac readLine_wrap_thm \\ fs []]
  \\ drule (GEN_ALL readLine_wrap_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ fs [readLine_wrap_def, handle_Fail_def, st_ex_return_def,
         st_ex_bind_def, case_eq_thms]
  \\ fs [bool_case_eq, COND_RATOR, case_eq_thms] \\ rw [] \\ fs []
  \\ drule (GEN_ALL next_line_thm) \\ rw []
  \\ `st with holrefs := st.holrefs = st`
    by fs [state_refs_component_equality]
  \\ fs [liftM_def, print_err_def] \\ rw [] THENL
    [metis_tac [APPEND_ASSOC],
     ALL_TAC,
     metis_tac []]
  \\ qmatch_asmsub_abbrev_tac `readLines _ _ c1`
  \\ `STATE (ds++defs) c1.holrefs` by fs [Abbr `c1`]
  \\ first_x_assum drule
  \\ rpt (disch_then drule) \\ rw []
  \\ metis_tac []
QED

Theorem readMain_thm:
   readMain () (c with holrefs := init_refs) = (res, c')
   ==>
   res = Success () /\
   ?ds. STATE ds c'.holrefs
Proof
  rw [readMain_def, st_ex_bind_def, st_ex_return_def, case_eq_thms,
      arguments_def, inputLinesFrom_def, print_err_def, print_def, bool_case_eq,
      COND_RATOR, liftM_def, readFile_def]
  \\ pop_assum mp_tac
  \\ reverse (Cases_on `TL c.cl`) \\ fs []
  >-
   (rpt (PURE_TOP_CASE_TAC \\ fs [])
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ imp_res_tac init_reader_wrap_thm \\ fs []
    \\ qmatch_asmsub_abbrev_tac `readLines _ ls st`
    \\ `STATE defs st.holrefs` by fs [Abbr`st`]
    \\ `READER_STATE defs init_state` by fs [READER_STATE_init_state]
    \\ drule (GEN_ALL readLines_thm)
    \\ rpt (disch_then drule) \\ rw [])
  >-
   (
    rpt (PURE_TOP_CASE_TAC \\ fs [])
    \\ TRY (pairarg_tac \\ fs []) \\ rw []
    \\ imp_res_tac init_reader_wrap_thm \\ fs []
    \\ fs [EVAL ``?ds. STATE ds init_refs`` |> SIMP_RULE (srw_ss()) []]
    >- metis_tac []
    >- metis_tac []
    \\ qmatch_asmsub_abbrev_tac `readLines _ ls c1`
    \\ `STATE defs c1.holrefs` by fs [Abbr`c1`]
    \\ `READER_STATE defs init_state` by fs [READER_STATE_init_state]
    \\ drule (GEN_ALL readLines_thm)
    \\ rpt (disch_then drule) \\ rw []
    \\ metis_tac [])
  \\ rw []
  \\ fs [EVAL ``?ds. STATE ds init_refs`` |> SIMP_RULE (srw_ss()) []]
QED

(* ------------------------------------------------------------------------- *)
(* Monadic I/O reader satisfies I/O specification                            *)
(* ------------------------------------------------------------------------- *)

Theorem readLine_wrap_correct:
   readLine_wrap (line, s) refs = (res, refs_out) /\
   process_line s refs line = res_p
   ==>
   case res of
     Success (INL s) (* Error *) => res_p = (INR s, refs_out)
   | Success (INR s) (* Ok *)    => res_p = (INL s, refs_out)
   | _ => F (* Does not happen *)
Proof
  rw [readLine_wrap_def, handle_Fail_def, st_ex_bind_def, st_ex_return_def,
      process_line_def, case_eq_thms] \\ fs []
QED

Theorem readLine_EQ:
   readLine_wrap (line, s) refs = (res1, t1) /\
   ~invalid_line line /\
   readLine (unescape_ml (fix_fun_typ (str_prefix line))) s refs = (res2, t2)
   ==>
   t1 = t2 /\
   case res1 of
     Success (INL e) => res2 = Failure (Fail e)
   | Success (INR s) => res2 = Success s
   | _ => F
Proof
  rw [readLine_wrap_def, st_ex_bind_def, st_ex_return_def, handle_Fail_def,
      case_eq_thms] \\ fs []
QED

Theorem readLine_wrap_invalid_line:
   invalid_line h ==> readLine_wrap (h, s) c = (Success (INR s), c)
Proof
  rw [readLine_wrap_def, st_ex_return_def]
QED

Theorem readLines_EQ:
   !s line c res1 c_out res2 refs.
     readLines s line c = (res1, c_out) /\
     readLines line s c.holrefs = (res2, refs)
     ==>
     refs = c_out.holrefs /\
     res1 = Success () /\
     case res2 of
       Success (s,_) =>
         c_out.stdio = add_stdout c.stdio (msg_success s refs.the_context)
     | Failure (Fail e) => c_out.stdio = add_stderr c.stdio e
     | _ => F
Proof
  recInduct readLines_ind \\ rw []
  \\ pop_assum mp_tac \\ simp [Once readerTheory.readLines_def]
  \\ pop_assum mp_tac \\ simp [Once readLines_def]
  \\ `!x. x with holrefs := x.holrefs = x`
    by fs [state_refs_component_equality]
  \\ Cases_on `lines` \\ fs []
  \\ fs [st_ex_return_def, st_ex_bind_def, handle_Fail_def, raise_Fail_def]
  \\ rw [print_def, print_err_def, liftM_def, context_def,
         get_the_context_def]
  \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [case_eq_thms] \\ rw []
  \\ TRY (Cases_on `res` \\ fs [])
  \\ TRY (Cases_on `res2` \\ fs [])
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ imp_res_tac readLine_wrap_invalid_line \\ fs [] \\ rw []
  \\ imp_res_tac readLine_EQ \\ fs [] \\ rw []
  \\ first_x_assum drule \\ simp []
QED

Theorem readFile_correct:
   readFile fname c = (res, c_out) /\
   read_file c.stdio c.holrefs fname = (succ, fs, refs, fstate)
   ==>
   res = Success () /\ fs = c_out.stdio /\ refs = c_out.holrefs
Proof
  rw [readFile_def, read_file_def, st_ex_bind_def, st_ex_return_def,
      case_eq_thms]
  \\ TRY (Cases_on `lines` \\ fs [])
  \\ fs [liftM_def, print_err_def, print_def, inputLinesFrom_def] \\ rw []
  \\ imp_res_tac readLines_EQ \\ fs [] \\ rfs []
QED

Theorem readMain_correct:
   readMain () c = (res, c_out) /\
   reader_main c.stdio c.holrefs (TL c.cl) = (succ, fs, refs, fstate)
   ==>
   res = Success () /\ fs = c_out.stdio
Proof
  simp [readMain_def, st_ex_bind_def, case_eq_thms, arguments_def, liftM_def,
        print_err_def, init_reader_wrap_def, handle_Fail_def, st_ex_return_def,
        st_ex_bind_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  >- (rw [reader_main_def, state_refs_component_equality] \\ fs [])
  \\ TRY pairarg_tac \\ fs []
  \\ fs [case_eq_thms] \\ rw [] \\ fs []
  \\ rfs [state_refs_component_equality, reader_main_def]
  >-
   (rename1 `readFile h st`
    \\ Cases_on `read_file st.stdio st.holrefs h`
    \\ PairCases_on `r`
    \\ imp_res_tac readFile_correct)
  \\ drule (GEN_ALL readFile_correct) \\ fs []
QED

(* ------------------------------------------------------------------------- *)
(* Preserving the commandline is crucial                                     *)
(* ------------------------------------------------------------------------- *)

Theorem readLines_COMMANDLINE_pres:
   !s line sr res tr.
     readLines s line sr = (res, tr)
     ==>
     tr.cl = sr.cl
Proof
  recInduct readLines_ind
  \\ gen_tac \\ Cases \\ strip_tac
  \\ rw [Once readLines_def, print_def, liftM_def, st_ex_bind_def,
         st_ex_return_def]
  \\ fs []
  \\ pairarg_tac \\ fs [case_eq_thms] \\ rw []
  \\ qpat_x_assum `_ = (res,tr)` mp_tac
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ rw [UNCURRY] \\ fs []
  \\ first_x_assum drule \\ fs []
QED

Theorem readMain_COMMANDLINE_pres:
   readMain () c = (res, d)
   ==>
   c.cl = d.cl
Proof
  simp [readMain_def, st_ex_bind_def, st_ex_return_def, case_eq_thms,
        readFile_def, liftM_def, arguments_def, print_err_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ fs [ELIM_UNCURRY] \\ rw [] \\ fs []
  \\ drule readLines_COMMANDLINE_pres \\ fs []
QED

val _ = export_theory ();
