(*
  cat program example: concatenate and print lines from files.

  Simple version that operates one character at a time.
*)
Theory catProg
Ancestors
  cfApp TextIOProof basis_ffi
Libs
  preamble basis basisFunctionsLib

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = translation_extends"basisProg";

Quote add_cakeml:
  fun print_stream is =
    case TextIO.input1 is of
      None => ()
    | Some c => (TextIO.output1 TextIO.stdOut c; print_stream is)
End

Quote add_cakeml:
  fun do_onefile fname = let
    val is = TextIO.openIn fname
  in print_stream is; TextIO.closeIn is end
End

(* Prints one file, ignoring it if it does not exist. *)
Quote add_cakeml:
  fun cat1 f = do_onefile f handle TextIO.BadFileName => ()
End

Quote add_cakeml:
  fun cat fnames = case fnames of
    [] => ()
  | f::fs => (do_onefile f; cat fs)
End

Quote add_cakeml:
  fun cat_main _ = cat (CommandLine.arguments())
End

val st = get_ml_prog_state ();

Theorem print_stream_spec:
  ∀p is fs fd s.
    app (p:'ffi ffi_proj) print_stream_v [is]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (POSTv u.
         STDIO (add_stdout (fastForwardFD fs fd) (implode s)) *
         INSTREAM_STR fd is "" (fastForwardFD fs fd) *
         &(UNIT_TYPE () u))
Proof
  Induct_on ‘s’ \\ rpt strip_tac
  \\ xcf "print_stream" st
  >-
   (once_rewrite_tac [STDIO_STD_streams] \\ xpull
    \\ drule INSTREAM_STR_fd_neq
    \\ disch_then $ once_rewrite_tac o sing \\ xpull
    \\ xlet
       ‘POSTv chv. SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_STR fd is "" (forwardFD fs fd k) *
          &(OPTION_TYPE CHAR NONE chv)’
    >-
     (xapp_spec input1_spec_str
      \\ qexistsl [‘emp’, ‘""’, ‘fs’, ‘fd’] \\ xsimpl)
    \\ gvs [OPTION_TYPE_def]
    \\ xmatch \\ xcon \\ xsimpl
    \\ simp [implode_def]
    \\ DEP_REWRITE_TAC [add_stdout_nil, STD_streams_fastForwardFD] \\ xsimpl
    \\ simp [INSTREAM_STR_fastForwardFD])
  \\ once_rewrite_tac [STDIO_STD_streams] \\ xpull
  \\ drule INSTREAM_STR_fd_neq
  \\ disch_then $ once_rewrite_tac o sing \\ xpull
  \\ rename [‘INSTREAM_STR _ _ (c::rest)’]
  \\ xlet
       ‘POSTv chv. SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_STR fd is rest (forwardFD fs fd k) *
          &(OPTION_TYPE CHAR (SOME c) chv)’
  >-
   (xapp_spec input1_spec_str
    \\ qexistsl [‘emp’, ‘c::rest’, ‘fs’, ‘fd’] \\ xsimpl)
  \\ gvs [OPTION_TYPE_def]
  \\ xmatch
  \\ xlet ‘POSTv uv.
             &UNIT_TYPE () uv *
             STDIO (add_stdout (forwardFD fs fd k) (str c)) *
             INSTREAM_STR fd is rest (forwardFD fs fd k)’
  >-
   (xapp_spec output1_stdOut_spec
    \\ qexistsl
       [‘INSTREAM_STR fd is rest (forwardFD fs fd k)’,
        ‘forwardFD fs fd k’, ‘c’]
    \\ simp [] \\ xsimpl)
  \\ once_rewrite_tac [INSTREAM_STR_get_file_content] \\ xpull
  \\ xapp
  \\ qexistsl [‘emp’, ‘add_stdout (forwardFD fs fd k) (str c)’, ‘fd’]
  \\ xsimpl
  \\ ‘STD_streams (forwardFD fs fd k)’ by
    (DEP_REWRITE_TAC [STD_streams_forwardFD] \\ simp [])
  \\ ‘STD_streams (fastForwardFD fs fd)’ by
    (DEP_REWRITE_TAC [STD_streams_fastForwardFD] \\ simp [])
  \\ conj_tac
  >- (DEP_REWRITE_TAC [INSTREAM_STR_add_stdout] \\ simp [] \\ xsimpl)
  \\ conj_tac >- (DEP_REWRITE_TAC [STD_streams_add_stdout] \\ simp [])
  \\ DEP_REWRITE_TAC [GSYM add_stdout_fastForwardFD]
  \\ conj_tac >- simp []
  \\ DEP_REWRITE_TAC [fastForwardFD_forwardFD]
  \\ conj_tac >- simp []
  \\ drule STD_streams_stdout \\ strip_tac
  \\ drule_then assume_tac add_stdo_o \\ simp []
  \\ simp [implode_cons_str] \\ xsimpl
  \\ DEP_REWRITE_TAC [INSTREAM_STR_add_stdout]
  \\ simp [] \\ xsimpl
QED

Theorem do_onefile_spec:
  FILENAME fnm fnv ∧ hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) do_onefile_v [fnv]
    (STDIO fs)
    (POSTve
     (λu. SEP_EXISTS content.
        &(UNIT_TYPE () u) *
        &(file_content fs fnm = SOME content) *
        STDIO (add_stdout fs (implode content)))
     (λe. &BadFileName_exn e *
          &(~inFS_fname fs fnm) *
          STDIO fs))
Proof
  rpt strip_tac
  \\ xcf "do_onefile" st
  \\ once_rewrite_tac [STDIO_consistentFS] \\ xpull
  \\ once_rewrite_tac [STDIO_STD_streams] \\ xpull
  \\ drule_then assume_tac STD_streams_nextFD
  \\ drule_then assume_tac nextFD_maxFD
  \\ Cases_on ‘inFS_fname fs fnm’
  >-
   (drule_all inFS_fname_file_content_SOME \\ strip_tac
    \\ rename [‘file_content _ _ = SOME content’]
    \\ drule_all_then assume_tac validFileFD_nextFD
    \\ xlet_auto_spec (SOME openIn_spec_str) >- xsimpl
    \\ qmatch_goalsub_abbrev_tac ‘INSTREAM_STR fd₁ _ _ fs₁’
    \\ xlet ‘POSTv u.
               STDIO (add_stdout (fastForwardFD fs₁ fd₁) (implode content)) *
               INSTREAM_STR fd₁ is "" (fastForwardFD fs₁ fd₁) *
               &(UNIT_TYPE () u)’
    >- (xapp \\ qexistsl [‘emp’, ‘content’, ‘fs₁’, ‘fd₁’] \\ xsimpl)
    \\ xapp_spec closeIn_spec_str \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac ‘STDIO fs₂’
    \\ qexistsl [‘emp’, ‘""’, ‘fs₂’, ‘fd₁’] \\ xsimpl
    \\ unabbrev_all_tac \\ simp []
    \\ conj_tac >-
     (DEP_REWRITE_TAC [
         INSTREAM_STR_add_stdout,
         STD_streams_fastForwardFD,
         STD_streams_openFileFS
       ]
      \\ xsimpl)
    \\ DEP_REWRITE_TAC [STD_streams_add_stdout]
    \\ simp [consistentFS_add_stdout]
    \\ DEP_REWRITE_TAC [add_stdout_fastForwardFD, STD_streams_openFileFS]
    \\ simp[GSYM add_stdo_ADELKEY, openFileFS_ADELKEY_nextFD]
    \\ xsimpl)
  \\ xlet_auto_spec (SOME openIn_STDIO_spec) >- xsimpl
  \\ xsimpl
QED

Definition file_contents_def:
  file_contents fnm fs =
    implode (THE (ALOOKUP fs.inode_tbl (File (THE (ALOOKUP fs.files fnm)))))
End

Theorem file_contents_add_stdout:
   STD_streams fs ⇒
   file_contents fnm (add_stdout fs out) = file_contents fnm fs
Proof
  rw[file_contents_def,add_stdo_def,up_stdo_def,fsFFITheory.fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC
  \\ simp[AFUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ rw[]
  \\ metis_tac[STD_streams_def,SOME_11,PAIR,FST,fsFFITheory.inode_distinct]
QED

Definition catfiles_string_def:
  catfiles_string fs fns =
    concat (MAP (λfnm. file_contents fnm fs) fns)
End

Theorem cat_spec0[local]:
  ∀fns fnsv fs.
     LIST_TYPE FILENAME fns fnsv ∧
     EVERY (inFS_fname fs) fns ∧
     hasFreeFD fs
    ⇒
     app (p:'ffi ffi_proj) cat_v [fnsv]
       (STDIO fs)
       (POSTv u.
          &UNIT_TYPE () u *
          STDIO (add_stdout fs (catfiles_string fs fns)))
Proof
  Induct >>
  rpt strip_tac >> xcf "cat" st >>
  fs[LIST_TYPE_def] >>
  (reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull))
  >- (xmatch >> xret >> simp[catfiles_string_def, file_contents_def] >>
      imp_res_tac STD_streams_stdout >>
      imp_res_tac add_stdo_nil >> xsimpl) >>
  reverse(Cases_on`consistentFS fs`)
  >-(fs[STDIO_def,IOFS_def,wfFS_def] \\ xpull \\ fs[consistentFS_def] \\ res_tac)
  >> xmatch >>
  progress inFS_fname_ALOOKUP_EXISTS >>
  xlet_auto_spec(SOME (SPEC_ALL do_onefile_spec))
  >- xsimpl
  >- xsimpl >>
  xapp \\
  xsimpl \\
  rw[catfiles_string_def] \\
  qmatch_goalsub_abbrev_tac`STDIO fs0` >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac`fs0` \\ xsimpl \\
  imp_res_tac STD_streams_stdout \\
  imp_res_tac add_stdo_o \\
  simp[Abbr`fs0`] \\
  simp[Once file_contents_def,SimpR``(==>>)``,concat_cons] \\
  simp[file_contents_add_stdout] \\ xsimpl \\
  gvs [file_content_def, AllCaseEqs()] \\ xsimpl
QED

Theorem cat_spec =
  cat_spec0 |> SIMP_RULE (srw_ss()) []

Definition catfile_string_def:
  catfile_string fs fnm =
    if inFS_fname fs fnm then file_contents fnm fs
    else (strlit"")
End

Theorem cat1_spec:
   !fnm fnmv.
     FILENAME fnm fnmv /\ hasFreeFD fs ==>
     app (p:'ffi ffi_proj) cat1_v [fnmv]
       (STDIO fs)
       (POSTv u.
          &UNIT_TYPE () u *
          STDIO (add_stdout fs (catfile_string fs fnm)))
Proof
  rpt strip_tac >>
  xcf "cat1" st >>
  xhandle ‘POSTve
             (λu. SEP_EXISTS content.
                &(UNIT_TYPE () u) *
                &(file_content fs fnm = SOME content) *
                STDIO (add_stdout fs (implode content)))
             (λe. &BadFileName_exn e *
                &(~inFS_fname fs fnm) *
                STDIO fs)’ >> fs[]
  >- (xapp >> fs[])
  >- (xsimpl >> rpt strip_tac >>
      gvs [file_content_def, AllCaseEqs()] >>
      imp_res_tac ALOOKUP_SOME_inFS_fname >>
      simp[catfile_string_def, file_contents_def] >>
      xsimpl) >>
  fs [BadFileName_exn_def] >> xcases >> xret >> xsimpl >>
  simp[catfile_string_def] >>
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xsimpl) >>
  imp_res_tac STD_streams_stdout >>
  imp_res_tac add_stdo_nil >>
  xsimpl
QED

Theorem cat_main_spec:
   EVERY (inFS_fname fs) (TL cl) ∧ hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) cat_main_v [Conv NONE []]
     (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv * (STDIO (add_stdout fs (catfiles_string fs (TL cl)))
                                    * (COMMANDLINE cl)))
Proof
  strip_tac
  \\ xcf "cat_main" st
  \\ xmatch
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (simp[COMMANDLINE_def] \\ xpull)
  \\ fs[wfcl_def]
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ instantiate
  \\ xsimpl
  \\ fs[EVERY_MAP,EVERY_MEM]
  \\ match_mp_tac LIST_TYPE_mono
  \\ simp[MAP_TL,NULL_EQ]
  \\ instantiate
  \\ Cases_on`cl` \\ fs[]
  \\ simp[MEM_MAP,FILENAME_def,PULL_EXISTS]
  \\ fs[validArg_def,EVERY_MEM]
QED

Theorem cat_whole_prog_spec:
   EVERY (inFS_fname fs) (TL cl) ∧ hasFreeFD fs ⇒
   whole_prog_spec cat_main_v cl fs NONE
    ((=) (add_stdout fs (catfiles_string fs (TL cl))))
Proof
  disch_then assume_tac
  \\ simp[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH cat_main_spec)))
  \\ xsimpl
QED

val name = "cat_main"
val (semantics_thm,prog_tm) = whole_prog_thm st name (UNDISCH cat_whole_prog_spec)
Definition cat_prog_def:
  cat_prog = ^prog_tm
End

Theorem cat_semantics_thm =
  semantics_thm |> ONCE_REWRITE_RULE[GSYM cat_prog_def]
  |> DISCH_ALL |> SIMP_RULE(srw_ss())[AND_IMP_INTRO,GSYM CONJ_ASSOC]
