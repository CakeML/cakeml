(*
  Deeply embedded CakeML program that implements an OpenTheory article
  checker.
*)
open preamble basis
     ml_monadBaseTheory ml_monad_translatorLib cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory
     readerProofTheory prettyTheory
     reader_commonProgTheory reader_initTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "reader_commonProg"

(* TODO: move *)
Theorem fastForwardFD_ADELKEY_same[simp]:
  forwardFD fs fd n with infds updated_by ADELKEY fd =
  fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

(* TODO: move *)
Theorem validFileFD_forwardFD:
  validFileFD fd (forwardFD fs x y).infds ⇔ validFileFD fd fs.infds
Proof
  rw [forwardFD_def, validFileFD_def, AFUPDKEY_ALOOKUP]
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ rename1 ‘_ = SOME xx’ \\ PairCases_on ‘xx’ \\ rw []
QED

(* -------------------------------------------------------------------------
 * Reading lines into commands
 * ------------------------------------------------------------------------- *)

(*
 * Line splitter for b_inputAllTokensFrom.
 *)

Definition is_newline_def:
  is_newline c ⇔ c = #"\n"
End

(*
 * Obtain a list of commands from an instream. Avoids keeping the entire
 * string in memory by calling inputLine repeatedly.
 *
 * This can be used with input from stdin, since there are no buffered
 * instreams for stdin (yet).
 *)

val _ = (append_prog o process_topdecs) ‘
  fun l2c_aux acc ins =
    case TextIO.inputLine ins of
      None => List.rev acc
    | Some ln => l2c_aux (tokenize ln::acc) ins;
  ’;

Definition l2c_aux_sem_def:
  (l2c_aux_sem acc [] = REVERSE acc) ∧
  (l2c_aux_sem acc (h::t) = l2c_aux_sem (tokenize (implode h)::acc) t)
End

Theorem l2c_aux_sem_MAP:
  ∀acc ls.
    l2c_aux_sem acc ls = REVERSE acc ++ MAP (tokenize o implode) ls
Proof
  Induct_on ‘ls’
  \\ rw [l2c_aux_sem_def]
QED

Theorem l2c_aux_spec:
  ∀n fs fd fdv ls lsv.
    INSTREAM fd fdv ∧
    get_file_content fs fd = SOME (content, n) ∧
    get_mode fs fd = SOME ReadMode ⇒
    LIST_TYPE READER_COMMAND_TYPE ls lsv ⇒
      app (p: 'ffi ffi_proj) l2c_aux_v
        [lsv; fdv]
        (STDIO fs)
        (POSTv v.
          &LIST_TYPE READER_COMMAND_TYPE (l2c_aux_sem ls (linesFD fs fd)) v *
          STDIO (fastForwardFD fs fd))
Proof
  Induct_on ‘linesFD fs fd’
  >-
   (rpt strip_tac
    \\ qpat_x_assum ‘[] = _’ (assume_tac o SYM)
    \\ xcf "l2c_aux" (get_ml_prog_state ())
    \\ ‘IS_SOME (get_file_content fs fd)’
      by fs []
    \\ ‘lineFD fs fd = NONE’
      by fs [linesFD_nil_lineFD_NONE]
    \\ xlet_auto
    >- xsimpl
    \\ fs [OPTION_TYPE_def, l2c_aux_sem_def]
    \\ xmatch
    \\ xapp_spec (INST_TYPE [alpha |-> “:command”]
                            ListProgTheory.reverse_v_thm)
    \\ instantiate
    \\ simp [lineFD_NONE_lineForwardFD_fastForwardFD]
    \\ xsimpl)
  \\ rpt strip_tac
  \\ xcf "l2c_aux" (get_ml_prog_state ())
  \\ qpat_x_assum ‘_::_ = _’ (assume_tac o SYM)
  \\ drule linesFD_cons_imp
  \\ strip_tac \\ rveq \\ fs []
  \\ xlet_auto >- xsimpl
  \\ fs [OPTION_TYPE_def, l2c_aux_sem_MAP]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xapp
  \\ qexists_tac ‘emp’
  \\ xsimpl
  \\ Q.REFINE_EXISTS_TAC ‘x::xs’
  \\ simp [LIST_TYPE_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ Q.LIST_EXISTS_TAC [‘lineForwardFD fs fd’, ‘fd’] \\ simp []
  \\ drule get_file_content_lineForwardFD_forwardFD \\ rw []
  \\ xsimpl
  \\ metis_tac [APPEND_ASSOC, CONS_APPEND]
QED

val _ = (append_prog o process_topdecs) ‘
  fun l2c ins = l2c_aux [] ins;
  ’;

Theorem l2c_spec:
  INSTREAM fd fdv ∧
  get_file_content fs fd = SOME (content, n) ∧
  get_mode fs fd = SOME ReadMode ⇒
    app (p: 'ffi ffi_proj) l2c_v
      [fdv]
      (STDIO fs)
      (POSTv v.
        &LIST_TYPE READER_COMMAND_TYPE
          (MAP (tokenize o implode) (linesFD fs fd)) v *
        STDIO (fastForwardFD fs fd))
Proof
  strip_tac
  \\ xcf "l2c" (get_ml_prog_state ())
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xapp
  \\ Q.LIST_EXISTS_TAC [‘emp’, ‘[]’]
  \\ instantiate
  \\ simp [l2c_aux_sem_MAP, PULL_EXISTS, LIST_TYPE_def]
  \\ xsimpl
QED

val _ = (append_prog o process_topdecs) ‘
  fun l2c_from fnm =
    let
      val ins = TextIO.openIn fnm
      val cmds = l2c ins
      val _ = TextIO.closeIn ins
    in
      Some cmds
    end
    handle TextIO.BadFileName => None
  ’;

(*
 * This is the drop-in replacement for b_inputAllTokensFrom for
 * stdin operation. Now, readLines (from readerTheory) can be used
 * both for stdin, buffered I/O, and with the monadIO version.
 *)

Theorem l2c_from_spec:
  FILENAME f fv ∧
  hasFreeFD fs ⇒
    app (p: 'ffi ffi_proj) l2c_from_v
      [fv]
      (STDIO fs)
      (POSTv sv.
        &OPTION_TYPE (LIST_TYPE READER_COMMAND_TYPE)
          (if inFS_fname fs f then
             SOME (MAP tokenize (all_lines fs f))
           else
             NONE) sv *
        STDIO fs)
Proof
  strip_tac
  \\ xcf "l2c_from" (get_ml_prog_state ())
  \\ ‘CARD (set (MAP FST fs.infds)) < fs.maxFD’
    by fs []
  \\ reverse (Cases_on ‘STD_streams fs’)
  >-
   (fs [STDIO_def]
    \\ xpull)
  \\ reverse (Cases_on ‘consistentFS fs’)
  >-
   (fs [STDIO_def, IOFS_def, wfFS_def]
    \\ xpull
    \\ fsrw_tac [SATISFY_ss] [consistentFS_def])
  \\ reverse IF_CASES_TAC
  >-
   (xhandle ‘POSTe ev.
              &BadFileName_exn ev *
              &(¬inFS_fname fs f) *
              STDIO fs’
    >- (xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl)
    \\ fs [BadFileName_exn_def]
    \\ xcases
    \\ xcon
    \\ simp [OPTION_TYPE_def]
    \\ xsimpl)
  \\ qmatch_goalsub_abbrev_tac ‘$POSTv Q’
  \\ xhandle ‘$POSTv Q’ \\ xsimpl
  \\ qunabbrev_tac ‘Q’
  \\ xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl
  \\ imp_res_tac nextFD_ltX
  \\ progress inFS_fname_ALOOKUP_EXISTS
  \\ progress ALOOKUP_inFS_fname_openFileFS_nextFD
  \\ rfs[]
  \\ pop_assum (qspec_then ‘0’ strip_assume_tac)
  \\ qmatch_assum_abbrev_tac ‘validFD fd fso’
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ ‘?c. get_file_content fso fd = SOME (c, 0)’
    by fs [get_file_content_def, validFD_def, Abbr ‘fso’, openFileFS_inode_tbl]
  \\ ‘get_mode fso fd = SOME ReadMode’
  by fs [Abbr ‘fso’, openFileFS_def, get_mode_def, get_file_content_fsupdate]
  \\ xlet_auto
  >- xsimpl
  \\ xlet_auto_spec (SOME closeIn_STDIO_spec)
  >-
   (xsimpl
    \\ ‘¬(fd = 0 ∨ fd = 1 ∨ fd = 2)’
      suffices_by fs []
    \\ fs [STD_streams_def]
    \\ metis_tac [nextFD_NOT_MEM, ALOOKUP_MEM])
  >-
   (xsimpl
    \\ simp [validFileFD_def]
    \\ drule ALOOKUP_inFS_fname_openFileFS_nextFD
    \\ rfs[]
    \\ fsrw_tac [SATISFY_ss] [Abbr ‘fso’])
  \\ xcon
  \\ simp [OPTION_TYPE_def]
  \\ fs [get_file_content_def, Abbr ‘fso’, openFileFS_inode_tbl]
  \\ imp_res_tac linesFD_openFileFS_nextFD \\ rfs []
  \\ first_x_assum (qspec_then ‘ReadMode’ mp_tac) \\ strip_tac \\ fs []
  \\ fs [MAP_MAP_o]
  \\ xsimpl
  \\ fsrw_tac [ETA_ss] [o_DEF, implode_explode]
  \\ qmatch_goalsub_abbrev_tac ‘STDIO fs'’
  \\ ‘fs' = fs’
    suffices_by (rw [] \\ xsimpl)
  \\ unabbrev_all_tac
  \\ fs [openFileFS_ADELKEY_nextFD]
QED

(* ------------------------------------------------------------------------- *)
(* CakeML wrapper                                                            *)
(* ------------------------------------------------------------------------- *)

val _ = (append_prog o process_topdecs) `
  fun process_line st ln =
    Inl (readline st (tokenize ln))
    handle Kernel.Fail e => Inr e
  `;

Theorem process_line_spec:
  READER_STATE_TYPE st stv ∧
  STRING_TYPE ln lnv ⇒
    app (p: 'ffi ffi_proj) process_line_v
    [stv; lnv]
    (HOL_STORE refs)
    (POSTv stv.
       HOL_STORE (SND (process_line st refs ln)) *
       &SUM_TYPE READER_STATE_TYPE STRING_TYPE
         (FST (process_line st refs ln)) stv)
Proof
  xcf "process_line" (get_ml_prog_state())
  \\ simp [process_line_def]
  \\ CASE_TAC
  \\ reverse CASE_TAC \\ fs[]
  >- (
    CASE_TAC \\ fs[]
    \\ qmatch_asmsub_rename_tac `(Failure (Fail err),refs')`
    \\ xhandle `POSTe ev. &HOL_EXN_TYPE (Fail err) ev * HOL_STORE refs'`
    >- (
      xlet_auto >- xsimpl
      \\ xlet_auto \\ xsimpl )
    \\ xcases
    \\ fs[HOL_EXN_TYPE_def]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xcon \\ xsimpl
    \\ fs[SUM_TYPE_def] )
  \\ qmatch_goalsub_abbrev_tac `$POSTv Qval`
  \\ xhandle`$POSTv Qval` \\ xsimpl
  \\ qunabbrev_tac`Qval`
  \\ xlet_auto >- xsimpl
  \\ xlet_auto \\ xsimpl
  \\ xcon
  \\ xsimpl
  \\ fs[SUM_TYPE_def]
QED

val _ = (append_prog o process_topdecs) `
  fun process_lines ins st0 =
    case TextIO.inputLine ins of
      None => TextIO.print (msg_success st0 (Kernel.context ()))
    | Some ln =>
      (case process_line st0 ln of
         Inl st1 => process_lines ins (next_line st1)
       | Inr e => TextIO.output TextIO.stdErr (line_fail st0 e))
  `;

Theorem process_lines_spec:
   ∀n st stv refs.
     READER_STATE_TYPE st stv ∧
     INSTREAM fd fdv ∧
     fd ≤ maxFD ∧
     fd ≠ 1 ∧
     fd ≠ 2 ∧
     STD_streams fs ∧
     get_file_content fs fd = SOME (content, n) ∧
     get_mode fs fd = SOME ReadMode ⇒
       app (p:'ffi ffi_proj) process_lines_v
         [fdv; stv]
         (STDIO fs * HOL_STORE refs)
         (POSTv u.
           &UNIT_TYPE () u *
           process_lines fd st refs fs (MAP implode (linesFD fs fd)))
Proof
  Induct_on`linesFD fs fd`
  >- (
    rpt strip_tac
    \\ qpat_x_assum`[] = _`(assume_tac o SYM)
    \\ xcf"process_lines"(get_ml_prog_state())
    \\ `IS_SOME (get_file_content fs fd)` by fs []
    \\ `lineFD fs fd = NONE` by fs [linesFD_nil_lineFD_NONE]
    \\ simp[process_lines_def]
    \\ xlet_auto >- xsimpl
    \\ xmatch
    \\ fs[OPTION_TYPE_def]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ xlet `POSTv updv.
               &LIST_TYPE UPDATE_TYPE refs.the_context updv *
               STDIO (lineForwardFD fs fd) * HOL_STORE refs`
    >-
     (xapp
      \\ simp [context_def, get_the_context_def]
      \\ xsimpl
      \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `refs`
      \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ xsimpl
    \\ simp [lineFD_NONE_lineForwardFD_fastForwardFD]
    \\ qexists_tac `HOL_STORE refs` \\ xsimpl
    \\ instantiate
    \\ qexists_tac `fastForwardFD fs fd`
    \\ xsimpl )
  \\ rpt strip_tac
  \\ xcf"process_lines"(get_ml_prog_state())
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM)
  \\ imp_res_tac linesFD_cons_imp
  \\ rveq \\ fs[] \\ rveq
  \\ qmatch_assum_rename_tac`lineFD fs fd = SOME ln`
  \\ xlet_auto >- xsimpl
  \\ xmatch
  \\ fs [OPTION_TYPE_def]
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ xlet_auto >- (
    xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`refs` \\ xsimpl )
  \\ xmatch
  \\ Cases_on`process_line st refs (implode ln)` \\ fs[]
  \\ qmatch_assum_rename_tac`SUM_TYPE _ _ sm _`
  \\ Cases_on`sm` \\ fs[SUM_TYPE_def]
  THENL [
    reverse conj_tac >- (EVAL_TAC \\ rw [])
    \\ conj_tac >- (EVAL_TAC \\ rw [semanticPrimitivesTheory.same_type_def]),
    reverse conj_tac >- (EVAL_TAC \\ rw [])
    \\ reverse conj_tac >- (EVAL_TAC \\ rw []) ]
  >- (
    xlet_auto >- xsimpl
    \\ qmatch_asmsub_abbrev_tac `STRING_TYPE fl sv`
    \\ xapp
    \\ simp[process_lines_def]
    \\ xsimpl
    \\ `STD_streams (lineForwardFD fs fd)` by simp[STD_streams_lineForwardFD]
    \\ asm_exists_tac
    \\ simp[]
    \\ qexists_tac`emp` \\ xsimpl
    \\ qmatch_asmsub_rename_tac`(INL st',refs')`
    \\ Q.LIST_EXISTS_TAC [`next_line st'`, `refs'`, `fd`]
    \\ xsimpl
    \\ imp_res_tac get_file_content_lineForwardFD_forwardFD
    \\ simp[get_file_content_forwardFD] )
  \\ xlet_auto >- xsimpl
  \\ xapp_spec output_STDIO_spec
  \\ simp[process_lines_def]
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ qmatch_asmsub_rename_tac`(INR msg,refs')`
  \\ qexists_tac`HOL_STORE refs'` \\ xsimpl
  \\ `STD_streams fs'` by simp[STD_streams_lineForwardFD,Abbr`fs'`]
  \\ drule STD_streams_stderr \\ strip_tac
  \\ fs[stdo_def]
  \\ simp[get_file_content_def,UNCURRY,PULL_EXISTS,get_mode_def]
  \\ `2 <= 255n` by simp[] \\ asm_exists_tac
  \\ instantiate \\ xsimpl
  \\ conj_tac >- fs [OUTSTREAM_def, GSYM stdErr_def, stderr_v_thm]
  \\ simp[insert_atI_end |> Q.GEN`l2` |> Q.ISPEC`explode s`
          |> SIMP_RULE (srw_ss())[LENGTH_explode]]
  \\ simp[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ (conj_tac >- metis_tac[STD_streams_stderr])
  \\ rw[stdo_def,up_stdo_def,LENGTH_explode]
  \\ xsimpl
QED

(* Apply the reader on a list of lines. *)

val _ = (append_prog o process_topdecs) `
  fun process_list ls s =
    case ls of
      [] => TextIO.print (msg_success s (Kernel.context ()))
    | l::ls =>
      (case process_line s l of
         Inl s => process_list ls (next_line s)
       | Inr e => TextIO.output TextIO.stdErr (line_fail s e))
  `;

val _ = (append_prog o process_topdecs) `
  fun read_stdin () =
    let
      val ls = TextIO.inputLines TextIO.stdIn
    in
      process_list ls init_state
    end;
  `;

val _ = (append_prog o process_topdecs) `
  fun read_file file =
    let
      val ins = TextIO.openIn file
    in
      process_lines ins init_state;
      TextIO.closeIn ins
    end
    handle TextIO.BadFileName =>
      TextIO.output TextIO.stdErr (msg_bad_name file)
  `;

Theorem readLines_process_lines:
  ∀ls st refs res r fs.
    readLines st ls refs = (res,r) ⇒
    ∃n.
      process_lines fd st refs fs ls =
      case res of
      | (Success (s,_)) =>
          STDIO (add_stdout (fastForwardFD fs fd)
                            (msg_success s r.the_context)) *
          HOL_STORE r
      | (Failure (Fail e)) =>
          STDIO (add_stderr (forwardFD fs fd n) e) *
          HOL_STORE r
Proof
  Induct \\ rw[process_lines_def]
  >- ( fs[Once readLines_def,st_ex_return_def] \\ rw[] )
  \\ pop_assum mp_tac
  \\ simp[Once readLines_def, handle_Fail_def, raise_Fail_def, st_ex_bind_def]
  \\ simp [process_line_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs []
  >-
   (strip_tac
    \\ first_x_assum drule
    \\ disch_then(qspec_then`lineForwardFD fs fd`strip_assume_tac) \\ fs []
    \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
    \\ simp[forwardFD_o]
    \\ metis_tac [])
  \\ CASE_TAC \\ fs []
  \\ rw [] \\ fs []
  \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
  \\ metis_tac []
QED

Theorem readLines_process_list:
  ∀ls s refs res r fs.
    readLines s ls refs = (res,r) ⇒
  ∃n.
    process_list fs s refs ls =
    case res of
    | (Success (s,_)) =>
        STDIO (add_stdout fs (msg_success s r.the_context)) *
        HOL_STORE r
    | (Failure (Fail e)) =>
        STDIO (add_stderr fs e) *
        HOL_STORE r
Proof
  Induct \\ rw [process_list_def]
  \\ pop_assum mp_tac
  \\ rw [Once readLines_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def,
         handle_Fail_def]
  \\ fs [process_line_def]
  \\ rpt (PURE_CASE_TAC \\ fs []) \\ rw []
QED

Theorem process_list_spec:
  ∀ls lsv s sv fs refs.
    STD_streams fs ∧
    LIST_TYPE STRING_TYPE ls lsv ∧
    READER_STATE_TYPE s sv ⇒
      app (p:'ffi ffi_proj) process_list_v
        [lsv; sv]
        (STDIO fs * HOL_STORE refs)
        (POSTv u. &UNIT_TYPE () u * process_list fs s refs ls)
Proof
  Induct \\ rw []
  >-
   (fs [LIST_TYPE_def]
    \\ xcf "process_list" (get_ml_prog_state ())
    \\ xmatch
    \\ xlet_auto
    >- (xcon \\ xsimpl)
    \\ fs [process_list_def]
    \\ xlet `POSTv rv.
               SEP_EXISTS refs' r.
                 STDIO fs *
                 HOL_STORE refs' *
                 &(context () refs = (Success r,refs')) *
                 &LIST_TYPE UPDATE_TYPE r rv`
    >-
     (xapp
      \\ xsimpl
      \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qexists_tac `refs`
      \\ xsimpl
      \\ rw [context_def, get_the_context_def] \\ fs []
      \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ fs [context_def, get_the_context_def]
    \\ xsimpl
    \\ instantiate
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs`
    \\ xsimpl)
  \\ fs [LIST_TYPE_def]
  \\ xcf "process_list" (get_ml_prog_state ())
  \\ xmatch
  \\ xlet_auto
  >-
   (xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `refs`
    \\ xsimpl)
  \\ simp [process_list_def]
  \\ CASE_TAC \\ fs []
  \\ reverse CASE_TAC \\ fs []
  >-
   (fs [SUM_TYPE_def]
    \\ xmatch
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_STDIO_spec
    \\ xsimpl
    \\ qexists_tac `HOL_STORE r`
    \\ HINT_EXISTS_TAC
    \\ xsimpl
    \\ drule STD_streams_stderr
    \\ rw [stdo_def, get_file_content_def, get_mode_def, PULL_EXISTS, UNCURRY]
    \\ asm_exists_tac \\ fs [OUTSTREAM_stderr]
    \\ xsimpl
    \\ simp [insert_atI_end
            |> Q.GEN`l2` |> Q.ISPEC `explode out`
            |> SIMP_RULE (srw_ss()) [LENGTH_explode]]
    \\ simp[add_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ fs [STD_streams_stderr]
    \\ rw [stdo_def, up_stdo_def, LENGTH_explode]
    \\ xsimpl)
  \\ fs [SUM_TYPE_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ last_x_assum xapp_spec
  \\ xsimpl
  \\ instantiate
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `r`
  \\ xsimpl
QED

Theorem read_stdin_spec:
  UNIT_TYPE () uv ∧
  (?inp. stdin fs inp 0) ⇒
    app (p: 'ffi ffi_proj) read_stdin_v [uv]
      (STDIO fs * HOL_STORE refs)
      (POSTv u.
        &UNIT_TYPE () u *
        STDIO (FST (read_stdin fs refs)) *
        HOL_STORE (FST (SND (read_stdin fs refs))))
Proof
  xcf "read_stdin" (get_ml_prog_state ())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ fs [UNIT_TYPE_def]
  \\ xmatch
  \\ xlet `POSTv fcv.
             &LIST_TYPE STRING_TYPE
               (MAP (λx. implode x ^ implode "\n")
                    (splitlines (DROP 0 inp))) fcv *
            STDIO (fastForwardFD fs 0) *
            HOL_STORE refs`
  >-
   (simp []
    \\ xapp
    \\ imp_res_tac stdin_get_file_content
    \\ instantiate
    \\ fs [INSTREAM_stdin, get_mode_def, PULL_EXISTS, stdin_def]
    \\ xsimpl)
  \\ `STD_streams (fastForwardFD fs 0)` by rw [STD_streams_fastForwardFD]
  \\ xapp
  \\ instantiate
  \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `init_state`
  \\ simp [RIGHT_EXISTS_AND_THM]
  \\ conj_tac
  >- fs [READER_STATE_TYPE_def, init_state_def, init_state_v_thm]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `refs`
  \\ xsimpl
  \\ rw []
  >- fs [UNIT_TYPE_def]
  \\ simp [read_stdin_def]
  \\ CASE_TAC \\ fs []
  \\ drule (GEN_ALL readLines_process_list)
  \\ disch_then (qspec_then `fastForwardFD fs 0` mp_tac) \\ rw []
  \\ rpt CASE_TAC \\ fs []
  \\ fs [stdin_def, all_lines_def, lines_of_def, strcat_thm] \\ rfs []
  \\ xsimpl
QED

Theorem read_file_spec:
  FILENAME fnm fnv ∧
  hasFreeFD fs ⇒
    app (p: 'ffi ffi_proj) read_file_v [fnv]
      (STDIO fs * HOL_STORE refs)
      (POSTv u.
        &UNIT_TYPE () u *
        STDIO (FST (read_file fs refs fnm)) *
        HOL_STORE (FST (SND (read_file fs refs fnm))))
Proof
  xcf "read_file" (get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[])
  \\ simp[read_file_def]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs fnm) *
      STDIO fs * HOL_STORE refs`
    >- ( xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl )
    \\ fs[BadFileName_exn_def]
    \\ xcases
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_STDIO_spec
    \\ xsimpl
    \\ drule STD_streams_stderr \\ strip_tac
    \\ fs[stdo_def]
    \\ simp[get_file_content_def,UNCURRY,PULL_EXISTS,get_mode_def]
    \\ `2 <= 255n` by simp[] \\ asm_exists_tac
    \\ instantiate \\ xsimpl
    \\ conj_tac >- fs [GSYM stdErr_def, OUTSTREAM_def, stderr_v_thm]
    \\ simp[insert_atI_end |> Q.GEN`l2` |> Q.ISPEC`explode s`
            |> SIMP_RULE (srw_ss())[LENGTH_explode]]
    \\ simp[add_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ (conj_tac >- metis_tac[STD_streams_stderr])
    \\ rw[stdo_def,up_stdo_def,LENGTH_explode]
    \\ xsimpl)
  \\ CASE_TAC \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`$POSTv Qval`
  \\ xhandle`$POSTv Qval` \\ xsimpl
  \\ qunabbrev_tac`Qval`
  \\ xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl
  \\ qspecl_then [`fs.maxFD`,`fs`] mp_tac (GEN_ALL nextFD_leX)
  \\ impl_tac \\ fs [] \\ rw []
  \\ progress inFS_fname_ALOOKUP_EXISTS
  \\ drule ALOOKUP_inFS_fname_openFileFS_nextFD
  \\ qmatch_assum_rename_tac`ALOOKUP _.files _ = SOME ino`
  \\ disch_then (qspecl_then [`fnm`,`ino`, `0`,`ReadMode`] mp_tac) \\ rw []
  \\ qmatch_asmsub_abbrev_tac`ALOOKUP fs'.infds fd`
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ `get_file_content fs' fd = SOME (content,0)`
    by simp[get_file_content_def,Abbr`fs'`]
  \\ imp_res_tac STD_streams_nextFD
  \\ drule (GEN_ALL STD_streams_openFileFS)
  \\ disch_then (qspecl_then [`ReadMode`,`fnm`, `0`] assume_tac)
  \\ assume_tac init_state_v_thm
  \\ `get_mode fs' fd = SOME ReadMode` by fs [get_mode_def]
  \\ `fd ≠ 1 ∧ fd ≠ 2` by rfs[]
  \\ xlet_auto_spec
    (SOME (Q.SPECL [`fs'`,`fs.maxFD`]
          (Q.GENL [`fs`, `maxFD`] process_lines_spec)))
  \\ xsimpl
  \\ xapp_spec closeIn_STDIO_spec
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ qexists_tac `fd`
  \\ xsimpl
  \\ rfs []
  \\ drule (GEN_ALL readLines_process_lines)
  \\ disch_then(qspecl_then[`fd`,`fs'`]strip_assume_tac)
  \\ simp[linesFD_openFileFS_nextFD,Abbr`fd`,MAP_MAP_o,o_DEF, Abbr`fs'`]
  \\ CASE_TAC
  >-
   (CASE_TAC \\ fs []
    \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac `STDIO fs'`
    \\ qexists_tac `fs'`
    \\ simp [Abbr `fs'`, add_stdout_fastForwardFD]
    \\ drule (GEN_ALL openFileFS_ADELKEY_nextFD)
    \\ disch_then (qspecl_then [`0`,`ReadMode`,`fnm`] mp_tac) \\ rw []
    \\ qmatch_goalsub_abbrev_tac `add_stdout _ str1`
    \\ `1 <> nextFD fs` by fs []
    \\ drule (GEN_ALL add_stdo_ADELKEY)
    \\ disch_then
      (qspecl_then [`str1`,`"stdout"`,`openFileFS fnm fs ReadMode 0`] mp_tac)
    \\ rw []
    \\ drule (GEN_ALL linesFD_openFileFS_nextFD)
    \\ disch_then (qspec_then `ReadMode` mp_tac) \\ rw []
    \\ fs [validFileFD_def]
    \\ xsimpl)
  \\ CASE_TAC \\ fs[]
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ qexists_tac`fs'` \\ xsimpl
  \\ simp[Abbr`fs'`, add_stdo_forwardFD]
  \\ `2 <> nextFD fs` by fs []
  \\ drule openFileFS_ADELKEY_nextFD
  \\ disch_then (qspecl_then [`0`,`ReadMode`,`fnm`] mp_tac)
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac `add_stderr _ str1`
  \\ drule add_stdo_ADELKEY
  \\ disch_then
    (qspecl_then [`str1`,`"stderr"`,`openFileFS fnm fs ReadMode 0`] mp_tac)
  \\ simp [validFileFD_forwardFD]
  \\ rw [validFileFD_def]
  \\ xsimpl
QED

val _ = (append_prog o process_topdecs) `
  fun reader_main u =
    let
      val _ = init_reader ()
    in
      case CommandLine.arguments () of
        [] => read_stdin ()
      | [file] => read_file file
      | _ => TextIO.output TextIO.stdErr msg_usage
      end
  `;

Theorem reader_main_spec:
  (∃s. init_reader () refs = (Success (), s)) ∧
  input_exists fs cl ⇒
    app (p:'ffi ffi_proj) reader_main_v
      [Conv NONE []]
      (COMMANDLINE cl * STDIO fs * HOL_STORE refs)
      (POSTv u.
        &UNIT_TYPE () u *
        STDIO (FST (reader_main fs refs (TL cl))))
Proof
  xcf "reader_main" (get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on `wfcl cl`)
  >- (fs [COMMANDLINE_def] \\ xpull)
  \\ simp [reader_main_def]
  \\ xlet_auto
  >- (xcon \\ xsimpl)
  \\ xlet `POSTv u. STDIO fs * HOL_STORE s * &UNIT_TYPE () u * COMMANDLINE cl`
  \\ xsimpl
  >-
   (xapp
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `refs`
    \\ xsimpl \\ fs [])
  \\ xlet_auto
  >- (xcon \\ xsimpl)
  \\ xlet_auto_spec (SOME CommandLineProofTheory.CommandLine_arguments_spec)
  >- xsimpl
  \\ CASE_TAC \\ fs [LIST_TYPE_def]
  >-
   (xmatch
    \\ xlet_auto
    >- (xcon \\ xsimpl)
    \\ xapp
    \\ xsimpl
    \\ instantiate
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `s`
    \\ xsimpl \\ fs [])
  \\ reverse CASE_TAC \\ fs [LIST_TYPE_def]
  >-
   (xmatch
    \\ IF_CASES_TAC
    >- (pop_assum mp_tac \\ EVAL_TAC)
    \\ reverse conj_tac
    >- (EVAL_TAC \\ fs [])
    \\ reverse conj_tac
    >- (EVAL_TAC \\ fs [])
    \\ xapp_spec output_stderr_spec
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `msg_usage`
    \\ simp [msg_usage_v_thm]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs`
    \\ xsimpl \\ fs [])
  \\ xmatch
  \\ IF_CASES_TAC
  >- (pop_assum mp_tac \\ EVAL_TAC)
  \\ reverse conj_tac
  >- (EVAL_TAC \\ fs [])
  \\ xapp
  \\ Cases_on `cl` \\ fs [wfcl_def, FILENAME_def, validArg_def]
  \\ xsimpl
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `s`
  \\ xsimpl \\ fs []
QED

(* ------------------------------------------------------------------------- *)
(* whole_prog_spec                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem reader_whole_prog_spec:
   input_exists fs cl ⇒
     whole_prog_spec reader_main_v cl fs (SOME (HOL_STORE init_refs))
       ((=) (FST (reader_main fs init_refs (TL cl))))
Proof
  rw [whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac `fs1 = _ with numchars := _`
  \\ qexists_tac `fs1` \\ fs [Abbr`fs1`]
  \\ reverse conj_tac
  >-
   (fs [reader_main_def, read_file_def, read_stdin_def]
    \\ rpt (PURE_CASE_TAC \\ fs [])
    \\ fs [GSYM add_stdo_with_numchars, with_same_numchars]
    \\ metis_tac [fastForwardFD_with_numchars, with_same_numchars])
  \\ irule (reader_main_spec
            |> UNDISCH |> MATCH_MP app_wgframe
            |> MP_CANON |> DISCH_ALL
            |> SIMP_RULE (srw_ss()) [])
  \\ xsimpl \\ instantiate
  \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `init_refs` \\ xsimpl
  \\ Cases_on `init_reader () init_refs`
  \\ drule init_reader_success \\ rw []
QED

val _ = add_user_heap_thm HOL_STORE_init_precond;

val st = get_ml_prog_state ();
val name = "reader_main";
val spec = UNDISCH reader_whole_prog_spec;
val (sem_thm,prog_tm) = whole_prog_thm st name spec
val reader_prog_def = Define `reader_prog = ^prog_tm`

val reader_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM reader_prog_def]
  |> DISCH_ALL
  |> ONCE_REWRITE_RULE [AND_IMP_INTRO]
  |> REWRITE_RULE
    [EVAL ``hasFreeFD fs``
     |> CONV_RULE (RHS_CONV (SIMP_CONV std_ss []))
     |> ONCE_REWRITE_RULE [CONJ_COMM] |> GSYM
     |> CONV_RULE (LHS_CONV (ONCE_REWRITE_CONV [CONJ_COMM]))]
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> curry save_thm "reader_semantics";

val _ = export_theory ();

