open preamble basis
     ml_monadBaseTheory ml_monad_translatorLib cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory
     readerProofTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "ml_hol_kernelProg"

(* TODO: move *)
val fastForwardFD_A_DELKEY_same = Q.store_thm("fastForwardFD_A_DELKEY_same[simp]",
  `forwardFD fs fd n with infds updated_by A_DELKEY fd =
   fs with infds updated_by A_DELKEY fd`,
  fs [forwardFD_def, IO_fs_component_equality]);

(* --- Translate readerTheory ---------------------------------------------- *)

val _ = translate init_state_def
val _ = translate mk_BN_def
val _ = translate mk_BS_def
val _ = translate insert_def
val _ = translate delete_def
val _ = translate lookup_def
val _ = translate push_def
val _ = translate insert_dict_def
val _ = translate delete_dict_def
val _ = translate first_def
val _ = translate stringTheory.isDigit_def

val _ = (use_mem_intro := true)
val tymatch_ind = save_thm("tymatch_ind",REWRITE_RULE[GSYM rev_assocd_thm]holSyntaxExtraTheory.tymatch_ind)
val _ = add_preferred_thy"-";
val r = translate (REWRITE_RULE[GSYM rev_assocd_thm]holSyntaxExtraTheory.tymatch_def)
val _ = (use_mem_intro := false)
val r = translate OPTION_MAP_DEF
val r = translate holSyntaxExtraTheory.match_type_def

val _ = m_translate find_axiom_def
val _ = m_translate getNum_def
val _ = m_translate getName_def
val _ = m_translate getList_def
val _ = m_translate getTypeOp_def
val _ = m_translate getType_def
val _ = m_translate getConst_def
val _ = m_translate getVar_def
val _ = m_translate getTerm_def
val _ = m_translate getThm_def
val _ = m_translate pop_def
val _ = m_translate peek_def
val _ = m_translate getPair_def
val _ = m_translate getNvs_def
val _ = m_translate getCns_def
val _ = m_translate getTys_def
val _ = m_translate getTms_def
val _ = m_translate readLine_def

val readline_side = Q.store_thm("readline_side",
  `!st1 l s. readline_side st1 l s <=> T`,
  rw [fetch "-" "readline_side_def"] \\ intLib.COOPER_TAC)
  |> update_precondition;

val readline_spec = save_thm (
  "readline_spec",
  mk_app_of_ArrowP ``p: 'ffi ffi_proj`` (theorem "readline_v_thm"));

val _ = translate fix_fun_typ_def
val _ = translate line_Fail_def

val _ = translate ind_name_def
val _ = translate ind_ty_def
val _ = translate select_name_def
val _ = translate select_tm_def
val _ = translate select_const_def
val _ = translate mk_reader_ctxt_def
val _ = m_translate set_reader_ctxt_def

val set_reader_ctxt_spec = save_thm (
  "set_reader_ctxt_spec",
  mk_app_of_ArrowP ``p: 'ffi ffi_proj`` (theorem "set_reader_ctxt_v_thm"));

(* --- CakeML wrapper ------------------------------------------------------ *)

val msg_success_def = Define `
  msg_success lines = concat
    [ strlit"OK! "
    ; mlint$toString lines
    ; strlit" lines.\n" ]`

val msg_usage_def = Define `msg_usage = strlit"Usage: reader <article>\n"`

val msg_bad_name_def = Define `
  msg_bad_name s = concat
    [strlit"Bad filename: "; s; strlit".\n"]
  `;

val _ = translate msg_success_def
val _ = translate msg_usage_def
val _ = translate msg_bad_name_def

val process_line_def = Define`
  process_line st refs ln =
    if invalid_line ln then (INL st, refs) else
    case readLine (fix_fun_typ (str_prefix ln)) st refs
    of (Success st, refs) => (INL st, refs)
     | (Failure (Fail s), refs) => (INR s, refs)`;

val r = translate str_prefix_def;

val r = translate invalid_line_def;
val r = Q.prove(
  `∀x. invalid_line_side x ⇔ T`,
  EVAL_TAC \\ rw[]) |> update_precondition;

val _ = (append_prog o process_topdecs) `
  fun process_line st0 ln =
    if invalid_line ln
    then Inl st0
    else Inl (readline (fix_fun_typ (str_prefix ln)) st0)
         handle Fail e => Inr e`;

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
  \\ xcon \\ xsimpl
  \\ fs[SUM_TYPE_def] );

val process_lines_def = Define`
  (process_lines loc fd st refs fs [] = STDIO (add_stdout (fastForwardFD fs fd) (msg_success (loc-1))) * HOL_STORE refs) ∧
  (process_lines loc fd st refs fs (ln::ls) =
   case process_line st refs ln of
   | (INL st,refs) => process_lines (loc+1) fd st refs (lineForwardFD fs fd) ls
   | (INR e,refs)  => STDIO (add_stderr (lineForwardFD fs fd) (line_Fail loc e)) * HOL_STORE refs)`;

val _ = (append_prog o process_topdecs) `
  fun process_lines loc ins st0 =
    case TextIO.inputLine ins of
      NONE => TextIO.print (msg_success (loc-1))
    | SOME ln =>
      (case process_line st0 ln of
         Inl st1 => process_lines (loc+1) ins st1
       | Inr e => TextIO.output TextIO.stdErr (line_fail loc e))`;

val process_lines_spec = Q.store_thm("process_lines_spec",
  `!n st stv refs loc locv.
     READER_STATE_TYPE st stv /\
     WORD8 (n2w fd) fdv /\ fd <= 255 /\ fd <> 1 /\ fd <> 2 /\
     INT loc locv /\
     STD_streams fs /\
     get_file_content fs fd = SOME (content, n)
     ==>
     app (p:'ffi ffi_proj) ^(fetch_v"process_lines"(get_ml_prog_state())) [locv;fdv;stv]
       (STDIO fs * HOL_STORE refs)
       (POSTv u.
         &UNIT_TYPE () u *
         process_lines loc fd st refs fs (MAP implode (linesFD fs fd)))`,
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
    \\ xlet_auto >- xsimpl
    \\ xlet_auto \\ xsimpl
    \\ xapp
    \\ xsimpl
    \\ simp[lineFD_NONE_lineForwardFD_fastForwardFD]
    \\ qexists_tac`HOL_STORE refs` \\ xsimpl
    \\ instantiate
    \\ qexists_tac`fastForwardFD fs fd`
    \\ xsimpl )
  \\ rpt strip_tac
  \\ xcf"process_lines"(get_ml_prog_state())
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM)
  \\ imp_res_tac linesFD_cons_imp
  \\ rveq \\ fs[] \\ rveq
  \\ qmatch_assum_rename_tac`lineFD fs fd = SOME ln`
  \\ xlet_auto >- xsimpl
  \\ xmatch
  \\ fs[OPTION_TYPE_def]
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
    \\ qexists_tac`st'` \\ qexists_tac`refs'`
    \\ qexists_tac `loc+1`
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
  \\ conj_tac >- metis_tac[stderr_v_thm,stdErr_def]
  \\ simp[insert_atI_end |> Q.GEN`l2` |> Q.ISPEC`explode s` |> SIMP_RULE (srw_ss())[LENGTH_explode]]
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
      (* Alternatively we can count lines from 0 *)
      process_lines 1 ins init_state;
      TextIO.close ins
    end
    (* Presuming that openIn will raise only this *)
    handle TextIO.BadFileName =>
      TextIO.output TextIO.stdErr (msg_bad_name file)`;

val readLines_process_lines = Q.store_thm("readLines_process_lines",
  `∀ls loc st refs res r fs.
   readLines loc ls st refs = (res,r) ⇒
   ∃n.
     process_lines loc fd st refs fs ls =
     case res of
     | (Success (_,m)) => STDIO (add_stdout (fastForwardFD fs fd) (msg_success m)) * HOL_STORE r
     | (Failure (Fail e)) => STDIO (add_stderr (forwardFD fs fd n) e) * HOL_STORE r`,
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

val read_file_def = Define`
  read_file fs refs fnm =
    (if inFS_fname fs (File fnm) then
       (case readLines 1 (all_lines fs (File fnm)) init_state refs of
        | (Success (_,n), refs) => (add_stdout fs (msg_success n), refs)
        | (Failure (Fail e), refs) => (add_stderr fs e, refs))
     else (add_stderr fs (msg_bad_name fnm), refs))`;

val read_file_spec = Q.store_thm("read_file_spec",
  `FILENAME fnm fnv /\ hasFreeFD fs
   ==>
   app (p: 'ffi ffi_proj) ^(fetch_v "read_file" (get_ml_prog_state())) [fnv]
     (STDIO fs * HOL_STORE refs)
     (POSTv u.
       &UNIT_TYPE () u *
       STDIO (FST(read_file fs refs fnm)) *
       HOL_STORE (SND(read_file fs refs fnm)))`,
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
    \\ conj_tac >- metis_tac[stderr_v_thm,stdErr_def]
    \\ simp[insert_atI_end |> Q.GEN`l2` |> Q.ISPEC`explode s` |> SIMP_RULE (srw_ss())[LENGTH_explode]]
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
  \\ imp_res_tac nextFD_leX
  \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
  \\ pop_assum(qspec_then`0`mp_tac) \\ rw[]
  \\ qmatch_asmsub_abbrev_tac`ALOOKUP fs'.infds fd`
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ `get_file_content fs' fd = SOME (content,0)` by simp[get_file_content_def,Abbr`fs'`]
  \\ imp_res_tac STD_streams_nextFD
  \\ imp_res_tac STD_streams_openFileFS
  \\ pop_assum(qspecl_then[`fnm`,`0`]assume_tac)
  \\ `fd ≠ 1 ∧ fd ≠ 2` by rfs[]
  \\ assume_tac (fetch"-""init_state_v_thm")
  \\ xlet_auto_spec (SOME (Q.SPEC`fs'`(Q.GEN`fs`process_lines_spec)))
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
    \\ first_x_assum (qspecl_then [`str1`,`"stdout"`, `openFileFS fnm fs 0`] mp_tac)
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
  \\ first_x_assum (qspecl_then [`str1`,`"stderr"`,`openFileFS fnm fs 0`] mp_tac)
  \\ xsimpl);

val set_reader_ctxt_no_exc = Q.store_thm("set_reader_ctxt_no_exc[simp]",
  `set_reader_ctxt () refs <> (Failure err, refs')`,
  rw [set_reader_ctxt_def, st_ex_bind_def, st_ex_return_def,
      get_the_term_constants_def, get_the_type_constants_def,
      get_the_context_def, set_the_term_constants_def,
      set_the_type_constants_def, set_the_context_def]);

val _ = (append_prog o process_topdecs) `
  fun reader_main u =
    case CommandLine.arguments () of
      [file] => (set_reader_ctxt (); read_file file)
    | _      => TextIO.output TextIO.stdErr msg_usage`;

val reader_main_def = Define `
   reader_main fs refs cl =
       case cl of
         [fnm] => FST (read_file fs (SND (set_reader_ctxt () refs)) fnm)
       | _ => add_stderr fs msg_usage`;

val reader_main_spec = Q.store_thm("reader_main_spec",
  `hasFreeFD fs
   ==>
   app (p:'ffi ffi_proj) ^(fetch_v "reader_main" (get_ml_prog_state()))
     [Conv NONE []]
     (STDIO fs * COMMANDLINE cl * HOL_STORE refs)
     (POSTv u.
       &UNIT_TYPE () u *
       STDIO (reader_main fs refs (TL cl)) *
       COMMANDLINE cl)`,
  xcf "reader_main" (get_ml_prog_state())
  \\ fs [reader_main_def]
  \\ Cases_on `set_reader_ctxt () refs` \\ fs [] \\ Cases_on `q` \\ fs []
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ fs [UNIT_TYPE_def]
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
    \\ fs [theorem"msg_usage_v_thm", UNIT_TYPE_def])
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
    \\ fs [theorem"msg_usage_v_thm", UNIT_TYPE_def])
  \\ xmatch
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ drule set_reader_ctxt_spec
  \\ disch_then (qspec_then `refs` strip_assume_tac)
  \\ xlet_auto \\ xsimpl
  >- (xapp \\ xsimpl \\ fs [UNIT_TYPE_def])
  \\ xapp
  \\ instantiate \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `r` \\ xsimpl
  \\ Cases_on `cl` \\ fs [] \\ rveq
  \\ fs [implode_def, FILENAME_def, validArg_def]
  \\ asm_exists_tac
  \\ rw [UNIT_TYPE_def]
  \\ xsimpl);

val STD_streams_reader_main = Q.store_thm("STD_streams_reader_main",
  `STD_streams fs ⇒ STD_streams (reader_main fs refs cl)`,
  rw[reader_main_def]
  \\ every_case_tac
  \\ rw[STD_streams_add_stderr]
  \\ rw[read_file_def,STD_streams_add_stderr]
  \\ CASE_TAC \\ rw[STD_streams_add_stderr]
  \\ CASE_TAC \\ rw[STD_streams_add_stderr,STD_streams_add_stdout]
  \\ CASE_TAC \\ rw[STD_streams_add_stderr,STD_streams_add_stdout]
  \\ fs[]);

val init_refs_def = Define`
  init_refs =
   <|the_type_constants := init_type_constants;
     the_term_constants := init_term_constants;
     the_axioms := init_axioms;
     the_context := init_context|>`;

val name = "reader_main"
val spec =
  reader_main_spec
  |> UNDISCH
  |> SIMP_RULE std_ss [STDIO_def]
  |> add_basis_proj
  |> Q.GEN`refs` |> Q.SPEC`init_refs`;
val st = get_ml_prog_state();

(* TODO: where should this go? *)
val HOL_STORE_init_precond = Q.store_thm("HOL_STORE_init_precond",
  `HOL_STORE init_refs
   {Mem (1+(LENGTH(stdin_refs++stdout_refs++stderr_refs++init_type_constants_refs)))
        (Refv init_type_constants_v);
    Mem (2+(LENGTH(stdin_refs++stdout_refs++stderr_refs++init_type_constants_refs++init_term_constants_refs)))
        (Refv init_term_constants_v);
    Mem (3+(LENGTH(stdin_refs++stdout_refs++stderr_refs++init_type_constants_refs++init_term_constants_refs++init_axioms_refs)))
        (Refv init_axioms_v);
    Mem (4+(LENGTH(stdin_refs++stdout_refs++stderr_refs++init_type_constants_refs++init_term_constants_refs++init_axioms_refs++init_context_refs)))
        (Refv init_context_v)}`,
  qmatch_goalsub_abbrev_tac`1 + l1`
  \\ qmatch_goalsub_abbrev_tac`2 + l2`
  \\ qmatch_goalsub_abbrev_tac`3 + l3`
  \\ qmatch_goalsub_abbrev_tac`4 + l4`
  \\ rw[HOL_STORE_def,ml_monad_translatorBaseTheory.REF_REL_def,init_refs_def]
  \\ rw[STAR_def,SEP_EXISTS_THM]
  \\ qmatch_goalsub_abbrev_tac`Mem (l1+1) v1`
  \\ qmatch_goalsub_abbrev_tac`Mem (l2+2) v2`
  \\ qmatch_goalsub_abbrev_tac`Mem (l3+3) v3`
  \\ qmatch_goalsub_abbrev_tac`Mem (l4+4) v4`
  \\ qexists_tac`{Mem(l1+1)v1;Mem(l2+2)v2;Mem(l3+3)v3}`
  \\ qexists_tac`{Mem(l4+4)v4}`
  \\ `l1+1 < l2+2` by simp[Abbr`l1`,Abbr`l2`]
  \\ `l2+2 < l3+3` by simp[Abbr`l2`,Abbr`l3`]
  \\ `l3+3 < l4+4` by simp[Abbr`l3`,Abbr`l4`]
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,EVAL``the_context``,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_context_v`
    \\ simp[init_context_v_thm]
    \\ fs[Abbr`l4`]
    \\ SPLIT_TAC )
  \\ qexists_tac`{Mem(l1+1)v1;Mem(l2+2)v2}`
  \\ qexists_tac`{Mem(l3+3)v3}`
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,EVAL``the_axioms``,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_axioms_v`
    \\ simp[init_axioms_v_thm]
    \\ fs[Abbr`l3`]
    \\ SPLIT_TAC )
  \\ qexists_tac`{Mem(l1+1)v1}`
  \\ qexists_tac`{Mem(l2+2)v2}`
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,EVAL``the_term_constants``,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_term_constants_v`
    \\ simp[init_term_constants_v_thm]
    \\ fs[Abbr`l2`]
    \\ SPLIT_TAC ) \\
  rw[REF_def,SEP_EXISTS_THM,EVAL``the_type_constants``,cond_STAR,
     ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
  \\ rw[cond_def]
  \\ qexists_tac`init_type_constants_v`
  \\ simp[init_type_constants_v_thm]
  \\ fs[Abbr`l1`]
  \\ SPLIT_TAC );
(* -- *)

val () = hprop_heap_thms := HOL_STORE_init_precond :: (!hprop_heap_thms)

val (sem_thm,prog_tm) = call_thm st name spec

val reader_prog_def = Define `reader_prog = ^prog_tm`

val semantics_reader_prog =
  sem_thm
  |> REWRITE_RULE[GSYM reader_prog_def]
  |> DISCH_ALL
  |> CONV_RULE(LAND_CONV EVAL)
  |> SIMP_RULE (srw_ss())[AND_IMP_INTRO,STD_streams_reader_main,GSYM CONJ_ASSOC]
  |> curry save_thm "semantics_reader_prog";

val _ = export_theory ();
