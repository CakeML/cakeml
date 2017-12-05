open preamble basis
     ml_monadBaseTheory ml_monad_translatorLib cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "ml_hol_kernelProg"

val exc_case_eq = prove_case_eq_thm{case_def=exc_case_def,nchotomy=exc_nchotomy};
val term_case_eq = prove_case_eq_thm{case_def=holSyntaxTheory.term_case_def,nchotomy=holSyntaxTheory.term_nchotomy};

val pop_not_clash = Q.store_thm("pop_not_clash[simp]",
  `pop x y ≠ (Failure (Clash tm),refs)`,
  EVAL_TAC \\ rw[] \\ EVAL_TAC);

val getNum_not_clash = Q.store_thm("getNum_not_clash[simp]",
  `getNum x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getVar_not_clash = Q.store_thm("getVar_not_clash[simp]",
  `getVar x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getTerm_not_clash = Q.store_thm("getTerm_not_clash[simp]",
  `getTerm x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getThm_not_clash = Q.store_thm("getThm_not_clash[simp]",
  `getThm x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val dest_type_not_clash = Q.store_thm("dest_type_not_clash[simp]",
  `dest_type x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val mk_fun_ty_not_clash = Q.store_thm("mk_fun_ty_not_clash[simp]",
  `mk_fun_ty t a r ≠ (Failure(Clash tm),refs)`,
  Cases_on`t` \\ EVAL_TAC
  \\ rw[pair_case_eq,exc_case_eq,raise_Fail_def,st_ex_return_def]
  \\ CCONTR_TAC \\ fs[bool_case_eq,COND_RATOR] \\ rw[]);

val type_of_not_clash = Q.store_thm("type_of_not_clash[simp]",
  `∀x y. type_of x y ≠ (Failure (Clash tm),refs)`,
  recInduct type_of_ind
  \\ rw[]
  \\ rw[Once type_of_def,st_ex_bind_def,raise_Fail_def,pair_case_eq,exc_case_eq]
  \\ CASE_TAC \\ fs[st_ex_return_def,pair_case_eq,exc_case_eq]
  \\ CCONTR_TAC \\ fs[pair_case_eq] \\ rw[] \\ fs[] \\ rfs[]
  \\ every_case_tac \\ fs[] \\ rfs[]);

val mk_abs_not_clash = Q.store_thm("mk_abs_not_clash[simp]",
  `mk_abs x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC \\ CASE_TAC \\ fs[]);

val mk_comb_not_clash = Q.store_thm("mk_comb_not_clash[simp]",
  `mk_comb x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ rw[mk_comb_def,st_ex_bind_def,pair_case_eq,exc_case_eq]
  \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[raise_Fail_def,st_ex_return_def]);

val mk_eq_not_clash = Q.store_thm("mk_eq_not_clash[simp]",
  `mk_eq x y ≠ (Failure(Clash tm),refs)`,
  Cases_on`x` \\ rw[mk_eq_def,st_ex_bind_def,try_def,otherwise_def,pair_case_eq,exc_case_eq]
  \\ CCONTR_TAC \\ fs[st_ex_return_def,raise_Fail_def] \\ rw[]);

val ABS_not_clash = Q.store_thm("ABS_not_clash[simp]",
  `ABS x y z ≠ (Failure (Clash tm),refs)`,
  Cases_on`y` \\ EVAL_TAC
  \\ every_case_tac \\ fs[st_ex_bind_def,pair_case_eq,exc_case_eq]
  \\ rw[raise_Fail_def]
  \\ CCONTR_TAC
  \\ fs[st_ex_return_def] \\ rveq \\ fs[]);

val readLine_not_clash = Q.store_thm("readLine_not_clash[simp]",
  `readLine x y z ≠ (Failure (Clash tm),refs)`,
  strip_tac \\
  fs[readLine_def,st_ex_bind_def,pair_case_eq,exc_case_eq,st_ex_return_def,option_caseeq,
     bool_case_eq,UNCURRY,COND_RATOR]
  \\ rveq \\ fs[] \\ rw[]
  \\ cheat);

val readLines_not_clash = Q.store_thm("readLines_not_clash[simp]",
  `∀ls x y tm refs. readLines ls x y ≠ (Failure (Clash tm),refs)`,
  recInduct readLines_ind
  \\ rw[]
  \\ rw[Once readLines_def]
  \\ CASE_TAC \\ fs[st_ex_return_def]
  \\ simp[st_ex_bind_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ CCONTR_TAC \\ fs[]);

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
val r = m_translate readLine_def

val readline_side = Q.store_thm("readline_side",
  `!st1 l s. readline_side st1 l s <=> T`,
  rw [fetch "-" "readline_side_def"] \\ intLib.COOPER_TAC)
  |> update_precondition;

val readline_spec = save_thm (
  "readline_spec",
  mk_app_of_ArrowP ``p: 'ffi ffi_proj`` (theorem "readline_v_thm"));

(* --- CakeML wrapper ------------------------------------------------------ *)

val msg_usage_def = Define `msg_usage = strlit"Usage: reader <article>\n"`

val msg_bad_name_def = Define `
  msg_bad_name s = concat
    [strlit"Bad filename: "; s; strlit".\n"]
  `;

val msg_failure_def = Define `
  msg_failure loc = concat
    [strlit"Reader threw exception: "; loc; strlit".\n"]
  `;

val _ = translate msg_usage_def
val _ = translate msg_bad_name_def
val _ = translate msg_failure_def

val str_prefix_def = Define `
  str_prefix str = extract str 0 (SOME (strlen str - 1))`;

val invalid_line_def = Define`
  invalid_line str ⇔ (strlen str) ≤ 1n ∨ strsub str 0 = #"#"`;

val process_line_def = Define`
  process_line st refs ln =
    if invalid_line ln then (INL st, refs) else
    case readLine (str_prefix ln) st refs
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
    else Inl (readline (str_prefix ln) st0)
         handle Fail e => Inr e`;

val process_line_spec = Q.store_thm("process_line_spec",
  `STATE_TYPE st stv ∧ STRING_TYPE ln lnv
   ==>
   app (p: 'ffi ffi_proj) ^(fetch_v "process_line" (get_ml_prog_state()))
   [stv; lnv]
   (HOL_STORE refs)
   (POSTv stv.
      HOL_STORE (SND(process_line st refs ln)) *
      &SUM_TYPE STATE_TYPE STRING_TYPE
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
  \\ xcon \\ xsimpl
  \\ fs[SUM_TYPE_def] );

val process_lines_def = Define`
  (process_lines fd st refs fs [] = STDIO (add_stdout (fastForwardFD fs fd) "OK!\n") * HOL_STORE refs) ∧
  (process_lines fd st refs fs (ln::ls) =
   case process_line st refs ln of
   | (INL st,refs) => process_lines fd st refs (lineForwardFD fs fd) ls
   | (INR e,refs)  => STDIO (add_stderr (lineForwardFD fs fd) (explode (msg_failure e))) * HOL_STORE refs)`;

val _ = (append_prog o process_topdecs) `
  fun process_lines ins st0 =
    case TextIO.inputLine ins of
      NONE => TextIO.print "OK!\n"
    | SOME ln =>
      (case process_line st0 ln of
         Inl st1 => process_lines ins st1
       | Inr e => TextIO.output TextIO.stdErr (msg_failure e))`;

val process_lines_spec = Q.store_thm("process_lines_spec",
  `!n st stv refs.
     STATE_TYPE st stv /\
     WORD8 (n2w fd) fdv /\ fd <= 255 /\ fd <> 1 /\ fd <> 2 /\
     STD_streams fs /\
     get_file_content fs fd = SOME (content, n)
     ==>
     app (p:'ffi ffi_proj) ^(fetch_v"process_lines"(get_ml_prog_state())) [fdv;stv]
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
    \\ xapp
    \\ xsimpl
    \\ simp[lineFD_NONE_lineForwardFD_fastForwardFD]
    \\ qexists_tac`HOL_STORE refs` \\ xsimpl
    \\ qexists_tac`fastForwardFD fs fd`
    \\ xsimpl)
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
    xapp
    \\ simp[process_lines_def]
    \\ xsimpl
    \\ `STD_streams (lineForwardFD fs fd)` by simp[STD_streams_lineForwardFD]
    \\ asm_exists_tac
    \\ simp[]
    \\ qexists_tac`emp` \\ xsimpl
    \\ qmatch_asmsub_rename_tac`(INL st',refs')`
    \\ qexists_tac`st'` \\ qexists_tac`refs'`
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
  \\ simp[insert_atI_end]
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
    (* Presuming that openIn will raise only this *)
    handle TextIO.BadFileName =>
      TextIO.output TextIO.stdErr (msg_bad_name file)`;

val readLines_process_lines = Q.store_thm("readLines_process_lines",
  `∀ls st refs res r fs.
   readLines (MAP str_prefix (FILTER ($~ o invalid_line) ls)) st refs = (res,r) ⇒
   ∃n.
     process_lines fd st refs fs ls =
     case res of
     | (Success _) => STDIO (add_stdout (fastForwardFD fs fd) "OK!\n") * HOL_STORE r
     | (Failure (Fail e)) => STDIO (add_stderr (forwardFD fs fd n) (explode (msg_failure e))) * HOL_STORE r`,
  Induct
  \\ rw[process_lines_def]
  >- ( fs[Once readLines_def,st_ex_return_def] \\ rw[] )
  >- (
    rw[process_line_def]
    \\ pop_assum mp_tac
    \\ simp[Once readLines_def]
    \\ rw[st_ex_bind_def]
    \\ CASE_TAC \\ fs[]
    \\ CASE_TAC \\ fs[]
    >- (
      first_x_assum drule
      \\ disch_then(qspec_then`lineForwardFD fs fd`strip_assume_tac)
      \\ simp[]
      \\ CASE_TAC
      \\ CASE_TAC \\ fs[]
      \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
      \\ simp[forwardFD_o]
      \\ metis_tac[] )
    \\ rveq \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
    \\ simp[]
    \\ metis_tac[] )
  \\ rw[process_line_def]
  \\ first_x_assum drule
  \\ disch_then(qspec_then`lineForwardFD fs fd`strip_assume_tac)
  \\ simp[]
  \\ CASE_TAC
  \\ CASE_TAC \\ fs[]
  \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
  \\ simp[forwardFD_o]
  \\ metis_tac[] );

val read_file_def = Define`
  read_file fs refs fnm =
    (if inFS_fname fs (File fnm) then
       (case readLines (MAP str_prefix (FILTER ($~ o invalid_line) (all_lines fs (File fnm))))
               init_state refs of
        | (Success _, refs) => (add_stdout fs "OK!\n", refs)
        | (Failure (Fail e), refs) => (add_stderr fs (explode (msg_failure e)), refs))
     else (add_stderr fs (explode (msg_bad_name fnm)), refs))`;

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
    \\ simp[insert_atI_end]
    \\ simp[add_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ (conj_tac >- metis_tac[STD_streams_stderr])
    \\ rw[stdo_def,up_stdo_def,LENGTH_explode]
    \\ xsimpl)
  \\ CASE_TAC \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`$POSTv Qval`
  \\ xhandle`$POSTv Qval` \\ xsimpl
  \\ qunabbrev_tac`Qval`
  \\ xlet_auto_spec (SOME openIn_STDIO_spec)
  \\ xsimpl
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
    xsimpl
    \\ qexists_tac`HOL_STORE r` \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
    \\ qexists_tac`fs'` \\ xsimpl
    \\ simp[Abbr`fs'`]
    \\ simp[add_stdout_fastForwardFD]
    \\ cheat
    (* openFileFS_A_DELKEY_nextFD *) )
  \\ CASE_TAC \\ fs[]
  \\ xsimpl
  \\ qexists_tac`HOL_STORE r` \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ qexists_tac`fs'` \\ xsimpl
  \\ simp[Abbr`fs'`]
  \\ simp[add_stdo_forwardFD]
  \\ cheat
  (* forwardFD version of fastForwardFD_A_DELKEY_same? *)
  );

val _ = (append_prog o process_topdecs) `
  fun reader_main u =
    case CommandLine.arguments () of
      [file] => read_file file
    | _      => TextIO.output TextIO.stdErr msg_usage`;

val main_spec = Q.store_thm("main_spec",
  `TODO`,
  cheat
  );

val st = get_ml_prog_state ();
val name = "reader_main"
val spec = main_spec |> SIMP_RULE std_ss [STDIO_def] |> add_basis_proj;
val (semantics_thm, prog_tm) = call_thm st name spec

val reader_prog_def = Define `reader_prog = ^prog_tm`

val _ = export_theory ();
