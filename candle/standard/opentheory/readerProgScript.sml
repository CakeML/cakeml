open preamble basis
     ml_monadBaseTheory ml_monad_translatorLib cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory
     readerProofTheory prettyTheory
     reader_commonProgTheory reader_initTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "reader_commonProg"

(* TODO: move *)
val fastForwardFD_A_DELKEY_same = Q.store_thm (
  "fastForwardFD_A_DELKEY_same[simp]",
  `forwardFD fs fd n with infds updated_by A_DELKEY fd =
   fs with infds updated_by A_DELKEY fd`,
  fs [forwardFD_def, IO_fs_component_equality]);

(* ------------------------------------------------------------------------- *)
(* CakeML wrapper                                                            *)
(* ------------------------------------------------------------------------- *)

val _ = (append_prog o process_topdecs) `
  fun process_line st0 ln =
    if invalid_line ln
    then Inl st0
    else Inl (readline (unescape_ml (fix_fun_typ (str_prefix ln))) st0)
         handle Kernel.Fail e => Inr e`;

val process_line_spec = Q.store_thm("process_line_spec",
  `READER_STATE_TYPE st stv ∧ STRING_TYPE ln lnv
   ==>
   app (p: 'ffi ffi_proj) ^(fetch_v "process_line" (get_ml_prog_state()))
   [stv; lnv]
   (HOL_STORE refs)
   (POSTv stv.
      HOL_STORE (SND(process_line st refs ln)) *
      &SUM_TYPE READER_STATE_TYPE STRING_TYPE
        (FST(process_line st refs ln)) stv)`,
  xcf "process_line" (get_ml_prog_state())
  \\ xlet_auto >- xsimpl
  \\ simp[process_line_def]
  \\ xif \\ fs []
  >- ( xcon \\ xsimpl \\ fs[SUM_TYPE_def] )
  \\ CASE_TAC
  \\ reverse CASE_TAC \\ fs[]
  >- (
    CASE_TAC \\ fs[]
    \\ qmatch_asmsub_rename_tac`(Failure (Fail err),refs')`
    \\ xhandle`POSTe ev. &HOL_EXN_TYPE (Fail err) ev * HOL_STORE refs'`
    >- (
      xlet_auto >- xsimpl
      \\ xlet_auto \\ xsimpl
      \\ xlet_auto \\ xsimpl
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
  \\ xlet_auto \\ xsimpl
  \\ xlet_auto \\ xsimpl
  \\ xcon \\ xsimpl
  \\ fs[SUM_TYPE_def] );

val _ = (append_prog o process_topdecs) `
  fun process_lines ins st0 =
    case TextIO.inputLine ins of
      None => TextIO.print (msg_success st0 (Kernel.context ()))
    | Some ln =>
      (case process_line st0 ln of
         Inl st1 => process_lines ins (next_line st1)
       | Inr e => TextIO.output TextIO.stdErr (line_fail st0 e))`;

val process_lines_spec = Q.store_thm("process_lines_spec",
  `!n st stv refs.
     READER_STATE_TYPE st stv /\
     FD fd fdv /\ fd <= maxFD /\ fd <> 1 /\ fd <> 2 /\
     STD_streams fs /\
     get_file_content fs fd = SOME (content, n)
     ==>
     app (p:'ffi ffi_proj) ^(fetch_v "process_lines" (get_ml_prog_state ()))
       [fdv; stv]
       (STDIO fs * HOL_STORE refs)
       (POSTv u.
         &UNIT_TYPE () u *
         process_lines fd st refs fs (MAP implode (linesFD fs fd)))`,
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
  \\ (reverse conj_tac >- (EVAL_TAC \\ rw[]))
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
    \\ qexists_tac`next_line st'` \\ qexists_tac`refs'`
    \\ qexists_tac`fd` \\ xsimpl
    \\ imp_res_tac get_file_content_lineForwardFD_forwardFD
    \\ simp[get_file_content_forwardFD] )
  \\ (reverse conj_tac >- (EVAL_TAC \\ rw[]))
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
  \\ simp[get_file_content_def,UNCURRY,PULL_EXISTS]
  \\ `2 <= 255n` by simp[] \\ asm_exists_tac
  \\ instantiate \\ xsimpl
  \\ conj_tac >- fs [FD_def, GSYM stdErr_def, stderr_v_thm]
  \\ simp[insert_atI_end |> Q.GEN`l2` |> Q.ISPEC`explode s`
          |> SIMP_RULE (srw_ss())[LENGTH_explode]]
  \\ simp[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ (conj_tac >- metis_tac[STD_streams_stderr])
  \\ rw[stdo_def,up_stdo_def,LENGTH_explode]
  \\ xsimpl);

val _ = (append_prog o process_topdecs) `
  fun read_file file =
    let
      val ins = TextIO.openIn file
    in
      process_lines ins init_state;
      TextIO.close ins
    end
    handle TextIO.BadFileName =>
      TextIO.output TextIO.stdErr (msg_bad_name file)`;

val readLines_process_lines = Q.store_thm("readLines_process_lines",
  `∀ls st refs res r fs.
   readLines ls st refs = (res,r) ⇒
   ∃n.
     process_lines fd st refs fs ls =
     case res of
     | (Success (s,_)) =>
         STDIO (add_stdout (fastForwardFD fs fd) (msg_success s r.the_context)) *
         HOL_STORE r
     | (Failure (Fail e)) =>
         STDIO (add_stderr (forwardFD fs fd n) e) *
         HOL_STORE r`,
  Induct \\ rw[process_lines_def]
  >- ( fs[Once readLines_def,st_ex_return_def] \\ rw[] )
  \\ pop_assum mp_tac
  \\ simp[Once readLines_def, handle_Fail_def, raise_Fail_def, st_ex_bind_def]
  \\ simp [process_line_def]
  \\ CASE_TAC \\ fs[]
  >-
   (strip_tac
    \\ first_x_assum drule
    \\ disch_then(qspec_then`lineForwardFD fs fd`strip_assume_tac) \\ fs []
    \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
    \\ simp[forwardFD_o]
    \\ metis_tac [])
  \\ CASE_TAC \\ fs []
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
  \\ metis_tac []);

val read_file_spec = Q.store_thm("read_file_spec",
  `FILENAME fnm fnv /\ hasFreeFD fs
   ==>
   app (p: 'ffi ffi_proj) ^(fetch_v "read_file" (get_ml_prog_state())) [fnv]
     (STDIO fs * HOL_STORE refs)
     (POSTv u.
       &UNIT_TYPE () u *
       STDIO (FST (SND (read_file fs refs fnm))) *
       HOL_STORE (SND (SND (read_file fs refs fnm))))`,
  xcf "read_file" (get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ simp[read_file_def]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs (File fnm)) *
      STDIO fs * HOL_STORE refs`
    >- ( xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl )
    \\ fs[BadFileName_exn_def]
    \\ xcases
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_STDIO_spec
    \\ xsimpl
    \\ drule STD_streams_stderr \\ strip_tac
    \\ fs[stdo_def]
    \\ simp[get_file_content_def,UNCURRY,PULL_EXISTS]
    \\ `2 <= 255n` by simp[] \\ asm_exists_tac
    \\ instantiate \\ xsimpl
    \\ conj_tac >- fs [GSYM stdErr_def, FD_def, stderr_v_thm]
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
  \\ qspecl_then [`maxFD`,`fs`] mp_tac (GEN_ALL nextFD_leX)
  \\ impl_tac \\ fs [] \\ rw []
  \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
  \\ pop_assum (qspec_then`0`mp_tac) \\ rw []
  \\ qmatch_asmsub_abbrev_tac`ALOOKUP fs'.infds fd`
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ `get_file_content fs' fd = SOME (content,0)`
    by simp[get_file_content_def,Abbr`fs'`]
  \\ imp_res_tac STD_streams_nextFD
  \\ imp_res_tac STD_streams_openFileFS
  \\ pop_assum(qspecl_then[`fnm`,`0`]assume_tac)
  \\ `fd ≠ 1 ∧ fd ≠ 2` by rfs[]
  \\ assume_tac init_state_v_thm
  \\ xlet_auto_spec (SOME (Q.SPEC `fs'` (Q.GEN`fs`process_lines_spec)))
  \\ xsimpl
  \\ xapp_spec close_STDIO_spec
  \\ instantiate
  \\ rfs[]
  \\ drule (GEN_ALL readLines_process_lines)
  \\ disch_then(qspecl_then[`fd`,`fs'`]strip_assume_tac)
  \\ simp[Abbr`fs'`,linesFD_openFileFS_nextFD,Abbr`fd`,MAP_MAP_o,o_DEF]
  \\ CASE_TAC
  >- (
    CASE_TAC
    \\ xsimpl
    \\ qexists_tac`HOL_STORE r` \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
    \\ qexists_tac`fs'` \\ xsimpl
    \\ simp[Abbr`fs'`]
    \\ simp[add_stdout_fastForwardFD] \\ rw [] \\ fs []
    \\ drule (GEN_ALL openFileFS_A_DELKEY_nextFD)
    \\ disch_then (qspecl_then [`0`,`fnm`] mp_tac) \\ rw []
    \\ `1 <> nextFD fs` by fs []
    \\ qmatch_goalsub_abbrev_tac `add_stdout _ str1`
    \\ imp_res_tac add_stdo_A_DELKEY
    \\ first_x_assum
      (qspecl_then [`str1`,`"stdout"`, `openFileFS fnm fs 0`] mp_tac)
    \\ xsimpl )
  \\ CASE_TAC \\ fs[]
  \\ xsimpl
  \\ qexists_tac`HOL_STORE r` \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ qexists_tac`fs'` \\ xsimpl
  \\ simp[Abbr`fs'`]
  \\ simp[add_stdo_forwardFD] \\ rw []
  \\ `2 <> nextFD fs` by fs [] \\ fs []
  \\ drule (GEN_ALL openFileFS_A_DELKEY_nextFD)
  \\ disch_then (qspecl_then [`0`,`fnm`] mp_tac) \\ rw []
  \\ imp_res_tac add_stdo_A_DELKEY
  \\ qmatch_goalsub_abbrev_tac `add_stderr _ str1`
  \\ first_x_assum
    (qspecl_then [`str1`,`"stderr"`,`openFileFS fnm fs 0`] mp_tac)
  \\ xsimpl);

val _ = (append_prog o process_topdecs) `
  fun reader_main u =
    case CommandLine.arguments () of
      [file] => ((init_reader (); read_file file)
                 handle Kernel.Fail e =>
                   TextIO.output TextIO.stdErr (msg_axioms e))
    | _      => TextIO.output TextIO.stdErr msg_usage`;

val reader_main_spec = Q.store_thm("reader_main_spec",
  `hasFreeFD fs
   ==>
   app (p:'ffi ffi_proj) ^(fetch_v "reader_main" (get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs * HOL_STORE refs)
     (POSTv u.
       &UNIT_TYPE () u *
       STDIO (FST (SND (reader_main fs refs (TL cl)))))`,
  xcf "reader_main" (get_ml_prog_state())
  \\ fs [reader_main_def]
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse (Cases_on `wfcl cl`) >- (simp[COMMANDLINE_def] \\ xpull)
  \\ fs [wfcl_def]
  \\ xlet_auto_spec (SOME CommandLineProofTheory.CommandLine_arguments_spec)
  >-
   (qexists_tac `STDIO fs * HOL_STORE refs`
    \\ xsimpl)
  \\ reverse (Cases_on `STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ Cases_on `TL cl` \\ fs [LIST_TYPE_def]
  >-
   (xmatch
    \\ xapp_spec output_stderr_spec
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `msg_usage`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs` \\ xsimpl
    \\ fs [msg_usage_v_thm, UNIT_TYPE_def])
  \\ reverse (Cases_on `t`) \\ fs [LIST_TYPE_def]
  >-
   (xmatch
    \\ xapp_spec output_stderr_spec
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `msg_usage`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs`
    \\ xsimpl
    \\ fs [msg_usage_v_thm, UNIT_TYPE_def])
  \\ xmatch
  \\ Cases_on `init_reader () refs` \\ fs []
  \\ drule init_reader_spec
  \\ disch_then (qspec_then `refs` strip_assume_tac)
  \\ reverse (Cases_on `q`) \\ fs []
  \\ qmatch_goalsub_abbrev_tac `$POSTv Q`
  >-
   (
    Cases_on `b` \\ fs []
    \\ xhandle
      `POST Q (\ev. &HOL_EXN_TYPE (Fail m) ev *
                    HOL_STORE r *
                    COMMANDLINE cl *
                    STDIO fs) (\x y z. &F)`
    \\ xsimpl
    >-
     (xlet_auto >- (xcon \\ xsimpl)
      \\ xlet_auto \\ xsimpl
      \\ fs [UNIT_TYPE_def] \\ rveq
      \\ xapp
      \\ xsimpl)
    \\ fs [HOL_EXN_TYPE_def]
    \\ xcases
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_stderr_spec \\ xsimpl
    \\ instantiate
    \\ unabbrev_all_tac \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs` \\ xsimpl)
  \\ xhandle `$POSTv Q` \\ xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto \\ xsimpl
  >- (fs [UNIT_TYPE_def] \\ rveq \\ xapp \\ xsimpl)
  \\ xapp
  \\ unabbrev_all_tac \\ rw [] \\ xsimpl
  \\ instantiate \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `r` \\ xsimpl
  \\ Cases_on `cl` \\ fs [] \\ rveq
  \\ fs [implode_def, FILENAME_def, validArg_def]
  \\ asm_exists_tac
  \\ xsimpl);

(* ------------------------------------------------------------------------- *)
(* whole_prog_spec                                                           *)
(* ------------------------------------------------------------------------- *)

val reader_whole_prog_spec = Q.store_thm("reader_whole_prog_spec",
  `hasFreeFD fs
   ==>
   whole_prog_spec ^(fetch_v "reader_main" (get_ml_prog_state()))
     cl fs (SOME (HOL_STORE init_refs))
     ((=) (FST (SND (reader_main fs init_refs (TL cl)))))`,
  rw [whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac `fs1 = _ with numchars := _`
  \\ qexists_tac `fs1` \\ fs [Abbr`fs1`]
  \\ reverse conj_tac
  >-
   (fs [reader_main_def, read_file_def]
    \\ every_case_tac
    \\ fs [GSYM add_stdo_with_numchars, with_same_numchars])
  \\ irule
    (DISCH_ALL ((MP_CANON (MATCH_MP app_wgframe (UNDISCH reader_main_spec)))))
  \\ xsimpl \\ instantiate
  \\ xsimpl
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ qexists_tac `init_refs` \\ xsimpl
  \\ qexists_tac `cl` \\ xsimpl);

val _ = add_user_heap_thm HOL_STORE_init_precond;

val st = get_ml_prog_state ();
val name = "reader_main";
val spec = UNDISCH reader_whole_prog_spec;
val (sem_thm,prog_tm) = whole_prog_thm st name spec
val reader_prog_def = Define `reader_prog = ^prog_tm`

val semantics_reader_prog =
  sem_thm
  |> REWRITE_RULE[GSYM reader_prog_def]
  |> DISCH_ALL
  |> ONCE_REWRITE_RULE [AND_IMP_INTRO]
  |> ONCE_REWRITE_RULE (* hasFreeFD gets simplified away in wps and its ugly *)
    [EVAL ``hasFreeFD fs``
     |> CONV_RULE (RHS_CONV (SIMP_CONV std_ss []))
     |> ONCE_REWRITE_RULE [CONJ_COMM] |> GSYM]
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> curry save_thm "semantics_reader_prog";

val _ = export_theory ();

