open preamble basis

val _ = new_theory "iocatProg"


val _ = translation_extends"basisProg";

val st = get_ml_prog_state;
val basis_st = get_ml_prog_state;

val _ = process_topdecs`
  fun pipe_2048 fd1 fd2 =
  let val nr = TextIO.read fd1 2048 in
    if nr = 0 then 0 else (TextIO.write fd2 nr 0; nr) end`
 |> append_prog

(* to ensure preserving standard STREAMS, fd1 cannot be a std output *)
val pipe_2048_spec = Q.store_thm("pipe_2048_spec",
 `!fs fd1 fd2 fnm1 fnm2 fd1v fd2v pos1 c1 c2.
  fd1 <> fd2 /\ fnm1 <> fnm2 /\
  FD fd1 fd1v /\ FD fd2 fd2v /\
  ALOOKUP fs.infds fd1 = SOME(fnm1,pos1) /\
  ALOOKUP fs.infds fd2 = SOME(fnm2,LENGTH c2) /\
  ALOOKUP fs.files fnm1 = SOME c1 /\ ALOOKUP fs.files fnm2 = SOME c2 /\
  fnm1 ≠ IOStream(strlit "stdout") ∧ fnm1 ≠ IOStream(strlit "stderr")
  ==>
  app (p:'ffi ffi_proj) ^(fetch_v "pipe_2048" (st())) [fd1v;fd2v]
       (STDIO fs)
       (POSTv nrv. SEP_EXISTS nr. &NUM nr nrv *
            &(nr <= MIN 2048 (LENGTH c1 - pos1)) *
            &((nr = 0) = (eof fd1 fs = SOME T)) *
            STDIO (fsupdate (fsupdate fs fd1 0 (pos1 + nr) c1)
                            fd2 0 (LENGTH c2 +nr)
                            (c2 ++ TAKE nr (DROP pos1 c1))))`,
  xcf "pipe_2048" (st()) >> fs[STDIO_def,IOFS_def,IOFS_iobuff_def] >> xpull >>
  rename [`W8ARRAY _ bdef`] >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_rename_tac`h1::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1::h2::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1::h2::h3::t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1::h2::h3::h4::t` >>
  PURE_REWRITE_TAC[GSYM iobuff_loc_def] >>
  (* xlet_auto picks the wrong fd here *)
  xlet_auto_spec (SOME (Q.SPECL[`fs with numchars := ll`,`fd1`, `fd1v`, `2048`] read_spec))
  >-(rw[get_file_content_def] >> xsimpl >> rw[]  >> instantiate  >> xsimpl)
  >-(rw[get_file_content_def] >> xsimpl)
  >-(rw[get_file_content_def] >> xsimpl) >>
  xlet_auto >- xsimpl >>
  `get_file_content fs fd1 = SOME(c1,pos1)`
    by (fs[get_file_content_def] >> pairarg_tac >> fs[] >> rfs[]) >>
  `get_file_content fs fd2 = SOME(c2,LENGTH c2)`
    by (fs[get_file_content_def] >> pairarg_tac >> fs[]) >>
  xif >-(xlit >> xsimpl >> fs[bumpFD_def] >> qexists_tac`THE (LTL ll)` >>
          imp_res_tac ALOOKUP_validFD >> fs[fsupdate_unchanged] >>
        `fs with numchars := THE (LTL ll) =
         (fs with numchars := ll) with numchars := THE (LTL ll)` by fs[] >>
         first_x_assum (fn thm => PURE_REWRITE_TAC[thm]) >>
        fs[wfFS_def,liveFS_def,live_numchars_def] >>
        cases_on`ll` >> imp_res_tac always_thm >> fs[] >>
        qmatch_abbrev_tac`IOx fs_ffi_part fs1 ==>> IOx fs_ffi_part fs2 * GC` >>
        `fs2 = fs1` suffices_by xsimpl >> unabbrev_all_tac >>
        cases_on`fs` >> fs[fsFFITheory.IO_fs_numchars_fupd,
                           ALIST_FUPDKEY_unchanged,IO_fs_infds_fupd]) >>
  qmatch_goalsub_abbrev_tac`IOx _ fs'` >>
 `get_file_content fs' fd2 = SOME(c2,LENGTH c2)`
   by fs[Abbr`fs'`,get_file_content_def,bumpFD_def,ALIST_FUPDKEY_ALOOKUP] >>
  PURE_REWRITE_TAC[GSYM iobuff_loc_def] >>
  xlet_auto_spec (SOME (Q.SPECL[`nr`, `fs'`,`fd2`] write_spec))
  >-(fs[iobuff_loc_def,Abbr`fs'`,liveFS_bumpFD,liveFS_def,validFD_bumpFD,
        validFD_numchars,ALOOKUP_validFD] >> xsimpl) >>
  xvar >> fs[IOFS_def,IOFS_iobuff_def,MAP_MAP_o,CHR_w2n_n2w_ORD] >>
  fs[get_file_content_def] >> rpt(pairarg_tac >> fs[]) >>
  xsimpl >> rw[] >> instantiate >> rfs[eof_def] >>
  qexists_tac`THE (LDROP k (THE (LTL ll)))` >> rw[Abbr`fs'`]
  >-(fs[fsupdate_numchars] >> irule wfFS_fsupdate >> conj_tac
     >-(irule wfFS_fsupdate >> conj_tac
        >-(fs[wfFS_def] >> imp_res_tac NOT_LFINITE_DROP_LFINITE >>
           cases_on`ll` >> fs[liveFS_def,live_numchars_def,always_DROP] >>
           imp_res_tac NOT_LFINITE_DROP >> first_x_assum(assume_tac o Q.SPEC`k`)  >>
           strip_tac >-(fs[] >> imp_res_tac NOT_LFINITE_DROP_LFINITE) >>
           irule always_DROP >> imp_res_tac always_thm >>
           fs[always_DROP])
        >-(fs[MEM_MAP] >> qexists_tac`(fd1,(fnm'',off''))` >> rfs[FST,ALOOKUP_MEM]))
     >-(fs[fsupdate_def] >> fs[MEM_MAP] >> qexists_tac`(fd2,(fnm',STRLEN c2))` >>
        fs[ALOOKUP_MEM,FST]))
  >-(irule STD_streams_fsupdate >> conj_tac
     >-(irule STD_streams_fsupdate >> rw[] >> metis_tac[STD_streams_def,PAIR,FST,SND,SOME_11])
     >> fs[fsupdate_def,ALIST_FUPDKEY_ALOOKUP]) >>
  qmatch_abbrev_tac`IOx fs_ffi_part fs1 ==>> IOx fs_ffi_part fs2 * GC` >>
  `fs2 = fs1` suffices_by xsimpl >> unabbrev_all_tac >>
  fs[ALIST_FUPDKEY_ALOOKUP,insert_atI_end,TAKE_APPEND,TAKE_TAKE, fsupdate_def,
     bumpFD_def,ALIST_FUPDKEY_unchanged] >> rw[]
  >- rfs[get_file_content_def]
  >-(qmatch_abbrev_tac`f xx = f yy` >>
     `xx = yy` suffices_by fs[] >> unabbrev_all_tac >> fs[ALIST_FUPDKEY_eq])
     );

(* implementation of cat using low-level IO functions *)
val _ = process_topdecs `
  fun do_onefile fd = if pipe_2048 fd TextIO.stdOut > 0 then do_onefile fd else ();
  fun cat fnames =
    case fnames of
      [] => ()
    | f::fs => (let val fd = TextIO.openIn f in
                      do_onefile fd; TextIO.close fd; cat fs end)
` |> append_prog


val do_onefile_spec = Q.store_thm(
  "do_onefile_spec",
  `∀content pos fnm fd fdv fs out.
      FD fd fdv /\
      ALOOKUP fs.infds fd = SOME (fnm,pos) /\
      ALOOKUP fs.files fnm = SOME content /\
      fnm <> IOStream(strlit "stdout") /\ fnm <> IOStream(strlit "stderr") /\
      pos <= STRLEN content /\
      fd <> 1 /\ fd <> 2 /\ stdout fs out ⇒
      app (p:'ffi ffi_proj) ^(fetch_v "do_onefile" (st())) [fdv]
       (STDIO fs)
       (POSTv u. &UNIT_TYPE () u *
              STDIO (up_stdout (fsupdate fs fd 0 (LENGTH content) content)
                               (strcat out (implode (DROP pos content)))))`,
  NTAC 5 strip_tac >>
  `?N. STRLEN content - pos <= N`
    by (qexists_tac`STRLEN content - pos` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`pos` >>
  Induct_on`N` >> strip_tac >> cases_on`STRLEN content = pos` >> fs[] >>
  xcf "do_onefile" (st()) >> fs[stdo_def,up_stdo_def] >>
  (xlet_auto_spec(SOME(Q.SPECL [`fs`,`fd`,`1`] pipe_2048_spec))
   >-(xsimpl >> rw[] \\ TRY instantiate \\ xsimpl \\
      fs[FD_def,GSYM stdOut_def,stdout_v_thm])
   >> xlet_auto >- xsimpl >> xif)
  >-(instantiate >> xcon >>
     fs[eof_def] >> pairarg_tac >> fs[] >> rfs[] >>
     `pos >= LENGTH contents` by fs[] >> imp_res_tac DROP_NIL >> xsimpl) >>
  first_x_assum (assume_tac o Q.SPEC`pos +nr`) >> rfs[]
  >-(xapp >> xsimpl >> qmatch_goalsub_abbrev_tac`STDIO fs'` >>
     map_every qexists_tac [`GC`,`strcat out (implode (TAKE nr (DROP pos content)))`,`fs'`] >>
     rw[Abbr`fs'`] >> fs[fsupdate_def,ALIST_FUPDKEY_ALOOKUP] >> xsimpl >>
     qmatch_abbrev_tac`STDIO xx ==>> STDIO yy` >>
     `xx = yy` suffices_by xsimpl >> unabbrev_all_tac >> rw[]
     >-(fs[ALIST_FUPDKEY_unchanged,ALIST_FUPDKEY_comm,ALIST_FUPDKEY_o] >>
        qmatch_abbrev_tac`_ _ f1 ll = _ _  f2 ll'` >>
        `ll = ll'`  suffices_by (unabbrev_all_tac >>fs[ALIST_FUPDKEY_eq]) >>
        unabbrev_all_tac >> fs[GSYM DROP_DROP_T,ALIST_FUPDKEY_eq])
     >-(fs[ALIST_FUPDKEY_comm,ALIST_FUPDKEY_o] >>
        qmatch_abbrev_tac`_ _ f1 ll = _ _  f2 ll'` >>
        `ll = ll'`  by (unabbrev_all_tac >> fs[ALIST_FUPDKEY_eq]) >>
        unabbrev_all_tac >> fs[] >> irule ALIST_FUPDKEY_eq >> rw[] >>
        cases_on`v` >> rw[]))
  >-(`nr = 0` by fs[] >> fs[eof_def] >> pairarg_tac >> fs[] >>
    `pos' = STRLEN content`  by (rfs[] >> fs[]) >> fs[]));

(* TODO: move *)
val file_contents_def = Define `
  file_contents fnm fs = implode (THE (ALOOKUP fs.files fnm))`
(* -- *)

val catfiles_string_def = Define`
  catfiles_string fs fns =
    concat (MAP (λfnm. file_contents (File fnm) fs) fns)
`;

val cat_spec0 = Q.prove(
  `∀fns fnsv fs.
     LIST_TYPE FILENAME fns fnsv ∧
     EVERY ((inFS_fname fs) o File) fns ∧
     hasFreeFD fs
    ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "cat" (get_ml_prog_state())) [fnsv]
       (STDIO fs)
       (POSTv u.
          &UNIT_TYPE () u *
          STDIO (add_stdout fs (catfiles_string fs fns)))`,
  Induct >> rpt strip_tac >> xcf "cat" (get_ml_prog_state()) >>
  fs[LIST_TYPE_def] >>
  (cases_on `¬ STD_streams fs` >- (fs[STDIO_def] >> xpull) >> fs[])
  >- (xmatch >> xcon >>
      imp_res_tac STD_streams_stdout \\
      fs[catfiles_string_def,get_file_content_def] >>
      imp_res_tac add_stdo_nil \\ xsimpl) >>
  fs[FILENAME_def] >>
  xmatch >> progress inFS_fname_ALOOKUP_EXISTS >>
  xlet_auto_spec(SOME(Q.SPECL[`h`,`v2_1`,`fs` ] openIn_STDIO_spec)) >>
  xsimpl >> imp_res_tac nextFD_ltX >> rfs[] >>
  `nextFD fs <> 0 /\ nextFD fs <> 1 /\ nextFD fs <> 2`
    by(metis_tac[STD_streams_def,ALOOKUP_MEM,nextFD_NOT_MEM]) >>
  `∃out. ALOOKUP fs.infds 1 = SOME (IOStream(strlit "stdout"),STRLEN out) ∧
         ALOOKUP fs.files (IOStream(strlit "stdout")) = SOME out` by metis_tac[STD_streams_def] \\
  `ALOOKUP (openFileFS h fs 0).infds 1 = SOME (IOStream(strlit "stdout"),STRLEN out)`
    by(fs[openFileFS_def] >> CASE_TAC >> fs[] >> CASE_TAC >> fs[openFile_def] >>
       `r.infds = (nextFD fs,File h,0) :: fs.infds` by fs[IO_fs_component_equality] >>
       fs[] >> CASE_TAC >> metis_tac[nextFD_NOT_MEM]) >>
  xlet_auto_spec (SOME(Q.SPECL[`content`,`0`, `File h`,`nextFD fs`, `wv`,
                               `openFileFS h fs 0`,`implode out`] do_onefile_spec))
  >-(xsimpl >> fs[wfFS_openFileFS,openFileFS_files,stdo_def] >>
     fs[ALOOKUP_inFS_fname_openFileFS_nextFD]) >>
  qmatch_goalsub_abbrev_tac `STDIO fs'` >>
  xlet_auto_spec (SOME (Q.SPECL[`nextFD fs`,`fs'`] close_STDIO_spec))
  >- xsimpl
  >- (xsimpl >> fs[InvalidFD_exn_def,Abbr`fs'`,up_stdo_def] >>
      irule ALOOKUP_validFD >>
     fs[fsupdate_def,ALIST_FUPDKEY_ALOOKUP,ALOOKUP_inFS_fname_openFileFS_nextFD] >>
     progress ALOOKUP_SOME_inFS_fname >> progress nextFD_ltX >>
     progress ALOOKUP_inFS_fname_openFileFS_nextFD >>
     rfs[ALOOKUP_inFS_fname_openFileFS_nextFD])
  >- xsimpl >>
  xapp >> xsimpl >> simp[Abbr`fs'`] >>
  qmatch_goalsub_abbrev_tac `STDIO fs'` >>
  map_every qexists_tac [`GC`,`fs'`] >>
  simp[Abbr`fs'`,catfiles_string_def, file_contents_def] >> xsimpl >>
  conj_tac >- (
    fs[up_stdo_def] >>
    `!ls fs0. EVERY ((inFS_fname fs0) o File) ls <=>
              EVERY (\s. File s ∈ FDOM (alist_to_fmap fs0.files)) ls`
       by(Induct >> rw[inFS_fname_def]) >> fs[] >>
    rw[] >>
    fs[fsupdate_def,ALIST_FUPDKEY_ALOOKUP,openFileFS_files,A_DELKEY_nextFD_openFileFS,
       A_DELKEY_ALIST_FUPDKEY_comm,ALOOKUP_inFS_fname_openFileFS_nextFD] ) >>
  qmatch_goalsub_abbrev_tac`add_stdout fs'`
  \\ `fs' = up_stdout fs (implode (out ++ content))`
  by (
    fs[Abbr`fs'`,up_stdo_def,IO_fs_component_equality,fsupdate_def,
       openFileFS_numchars,openFileFS_files,ALIST_FUPDKEY_ALOOKUP,
       ALOOKUP_inFS_fname_openFileFS_nextFD,A_DELKEY_ALIST_FUPDKEY_comm,
       A_DELKEY_nextFD_openFileFS,ALIST_FUPDKEY_unchanged] ) \\
  qunabbrev_tac`fs'` \\ pop_assum SUBST_ALL_TAC \\
  qmatch_goalsub_abbrev_tac`ALOOKUP fs'.files _` \\
  `fs'.files = ALIST_FUPDKEY (IOStream (strlit "stdout")) (λ_. out++content) fs.files` by (
    fs[Abbr`fs'`,up_stdo_def,fsupdate_def,ALOOKUP_inFS_fname_openFileFS_nextFD,
       ALIST_FUPDKEY_ALOOKUP,K_DEF,ALIST_FUPDKEY_unchanged]) \\
  qunabbrev_tac`fs'` \\ pop_assum SUBST_ALL_TAC \\
  simp[ALIST_FUPDKEY_ALOOKUP] \\
  qmatch_goalsub_abbrev_tac`MAP f` \\
  qmatch_goalsub_abbrev_tac`_::(MAP f' _)` \\
  `f = f'` by (
    rw[Abbr`f`,Abbr`f'`,FUN_EQ_THM]
    \\ CASE_TAC ) \\
  qunabbrev_tac`f` \\
  pop_assum SUBST_ALL_TAC \\
  `up_stdout fs (implode (out ++ content)) = add_stdout fs (implode content)`  by (
    rw[add_stdo_def] \\
    SELECT_ELIM_TAC \\
    simp[strcat_thm] \\
    metis_tac[stdo_UNICITY_R,stdo_def,SOME_11,PAIR,explode_implode,LENGTH_explode] )
  \\ pop_assum SUBST_ALL_TAC
  \\ `∃out. stdout fs out` by metis_tac[STD_streams_stdout]
  \\ imp_res_tac add_stdo_o
  \\ simp[concat_cons]
  \\ xsimpl);

val cat_spec = save_thm(
  "cat_spec",
  cat_spec0 |> SIMP_RULE (srw_ss()) [])

val cat_main = process_topdecs`
  fun cat_main _ = cat (CommandLine.arguments())`;
val _ = append_prog cat_main;

val cat_main_spec = Q.store_thm("cat_main_spec",
  `EVERY ((inFS_fname fs) o File) (TL cl) ∧ hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"cat_main" (st())) [Conv NONE []]
     (STDIO fs * COMMANDLINE cl )
     (POSTv uv. &UNIT_TYPE () uv *
       (STDIO (add_stdout fs (catfiles_string fs (TL cl))))
       * COMMANDLINE cl)`,
  strip_tac
  \\ xcf "cat_main" (st())
  \\ xmatch
  \\ xlet_auto >-(xcon >> xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (simp[COMMANDLINE_def] \\ xpull)
  \\ fs[wfcl_def]
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ instantiate
  \\ xsimpl
  \\ match_mp_tac LIST_TYPE_mono
  \\ instantiate
  \\ simp[FILENAME_def]
  \\ fs[EVERY_MEM,validArg_def]
  \\ Cases_on`cl` \\ fs[]);

val st = st();

val cat_whole_prog_spec = Q.store_thm("cat_whole_prog_spec",
  `EVERY (inFS_fname fs o File) (TL cl) ∧ hasFreeFD fs ⇒
   whole_prog_spec ^(fetch_v"cat_main"st) cl fs NONE
    ((=) (add_stdout fs (catfiles_string fs (TL cl))))`,
  disch_then assume_tac
  \\ simp[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH cat_main_spec)))
  \\ xsimpl);

val name = "cat_main"
val (semantics_thm,prog_tm) = whole_prog_thm st name (UNDISCH cat_whole_prog_spec)
val cat_prog_def = Define`cat_prog = ^prog_tm`;

val cat_semantics_thm =
  semantics_thm |> ONCE_REWRITE_RULE[GSYM cat_prog_def]
  |> DISCH_ALL |> SIMP_RULE(srw_ss())[AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> curry save_thm "cat_semantics_thm";

val _ = export_theory();
