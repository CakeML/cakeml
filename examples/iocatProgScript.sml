open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib cfLetAutoLib
     mlstringTheory mlcommandLineProgTheory mlw8arrayProgTheory
     fsioConstantsProgTheory fsioProgTheory basisFunctionsLib fsioProgLib 
     fsFFITheory fsFFIProofTheory

val _ = new_theory "iocatProg"

val _ = translation_extends"fsioProg";

val st = get_ml_prog_state;
val basis_st = get_ml_prog_state;

val A_DELKEY_ALIST_FUPDKEY_comm = Q.store_thm("A_DELKEY_ALIST_FUPDKEY_comm",
 `!ls f x y. x <> y ==> 
  A_DELKEY x (ALIST_FUPDKEY y f ls) = (ALIST_FUPDKEY y f (A_DELKEY x ls))`,
  Induct >>  rw[A_DELKEY_def,ALIST_FUPDKEY_def] >>
  cases_on`h` >> fs[ALIST_FUPDKEY_def] >> TRY CASE_TAC >> fs[A_DELKEY_def]);

val _ = process_topdecs`
  fun pipe_255 fd1 fd2 = 
  let val nr = IO.read fd1 (Word8.fromInt 255) in
    if nr = 0 then 0 else (IO.write fd2 nr 0; nr) end`
 |> append_prog

(* to ensure preserving standard STREAMS, fd1 cannot be a std output
*  and fd2 cannot be a non standard FD on standard outputs *)
val pipe_255_spec = Q.store_thm("pipe_255_spec",
 `!fs fd1 fd2 fnm1 fnm2 fd1v fd2v pos1 c1 c2.
  fd1 <> fd2 /\ fnm1 <> fnm2 /\ fd1 <= 255 /\ fd2 <= 255 /\
  WORD (n2w fd1 :word8) fd1v /\ WORD (n2w fd2 :word8) fd2v /\
  ALOOKUP fs.infds fd1 = SOME(fnm1,pos1) /\
  ALOOKUP fs.infds fd2 = SOME(fnm2,LENGTH c2) /\
  ALOOKUP fs.files fnm1 = SOME c1 /\ ALOOKUP fs.files fnm2 = SOME c2 /\
  fnm1 ≠ IOStream(strlit "stdout") ∧ fnm1 ≠ IOStream(strlit "stderr") /\
  (fd2 >= 3 ==> (fnm2 <> IOStream(strlit "stdout") /\ fnm2 <> IOStream(strlit "stderr")))
  ==>
  app (p:'ffi ffi_proj) ^(fetch_v "pipe_255" (st())) [fd1v;fd2v]
       (STDIO fs)
       (POSTv nrv. SEP_EXISTS nr. &NUM nr nrv *
            &(nr <= MIN 255 (LENGTH c1 - pos1)) *
            &((nr = 0) = (eof fd1 fs = SOME T)) *
            STDIO (fsupdate (fsupdate fs fd1 0 (pos1 + nr) c1)
                            fd2 0 (LENGTH c2 +nr) 
                            (c2 ++ TAKE nr (DROP pos1 c1))))`,
  xcf "pipe_255" (st()) >> fs[STDIO_def,IOFS_def,IOFS_iobuff_def] >> xpull >>
  xlet_auto >- xsimpl >>
  rename [`W8ARRAY _ bdef`] >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: t'` >>
  Cases_on `t'` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: h3 :: rest` >>
  PURE_REWRITE_TAC[GSYM iobuff_loc_def] >>
  (* xlet_auto picks the wrong fd here *)
  xlet_auto_spec (SOME (Q.SPECL[`fs with numchars := ll`,`fd1`,`255w`] read_spec))
  >-(rw[get_file_content_def] >> xsimpl >> rw[]  >> instantiate  >> xsimpl)
  >-(rw[get_file_content_def] >> xsimpl) >>
  xlet_auto >- xsimpl >>
  `get_file_content fs fd1 = SOME(c1,pos1)`
    by (fs[get_file_content_def] >> pairarg_tac >> fs[] >> rfs[]) >>
  `get_file_content fs fd2 = SOME(c2,LENGTH c2)`
    by (fs[get_file_content_def] >> pairarg_tac >> fs[]) >>
  xif >-(xlit >> xsimpl >> fs[bumpFD_def] >> qexists_tac`THE (LTL ll)` >>
        strip_tac >- fs[eof_def] >>
          imp_res_tac ALOOKUP_validFD >> fs[fsupdate_unchanged] >>
        `fs with numchars := THE (LTL ll) = 
         (fs with numchars := ll) with numchars := THE (LTL ll)` by fs[] >>
         first_x_assum (fn thm => PURE_REWRITE_TAC[thm]) >>
        fs[wfFS_def,liveFS_def] >>
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
  >-(fs[fsupdate_numchars] >> irule wfFS_fsupdate
     >-(irule wfFS_fsupdate
        >-(fs[wfFS_def] >> imp_res_tac NOT_LFINITE_DROP_LFINITE >>
           cases_on`ll` >> fs[liveFS_def,always_DROP] >>
           imp_res_tac NOT_LFINITE_DROP >> first_x_assum(assume_tac o Q.SPEC`k`)  >>
           strip_tac >-(fs[] >> imp_res_tac NOT_LFINITE_DROP_LFINITE) >>
           irule always_DROP >> imp_res_tac always_thm >> 
           fs[always_DROP])
        >-(fs[MEM_MAP] >> qexists_tac`(fd1,(fnm'',off''))` >> rfs[FST,ALOOKUP_MEM]))
     >-(fs[fsupdate_def] >> fs[MEM_MAP] >> qexists_tac`(fd2,(fnm',STRLEN c2))` >> 
        fs[ALOOKUP_MEM,FST]))
  >-(irule STD_streams_fsupdate
     >-(irule STD_streams_fsupdate >> rw[] >> NTAC 3 (fs[STD_streams_def]))
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
  fun do_onefile fd = if pipe_255 fd (IO.stdout()) > 0 then do_onefile fd else ();
  fun cat fnames =
    case fnames of
      [] => ()
    | f::fs => (let val fd = IO.openIn f in
                      do_onefile fd; IO.close fd; cat fs end)
` |> append_prog


val do_onefile_spec = Q.store_thm(
  "do_onefile_spec",
  `∀content pos fnm fd fdv fs out.
      WORD (n2w fd: word8) fdv /\ fd <= 255 /\
      ALOOKUP fs.infds fd = SOME (fnm,pos) /\
      ALOOKUP fs.files fnm = SOME content /\
      fnm <> IOStream(strlit "stdout") /\ fnm <> IOStream(strlit "stderr") /\
      pos <= STRLEN content /\ 
      fd <> 1 /\ fd <> 2 /\ stdout fs out ⇒
      app (p:'ffi ffi_proj) ^(fetch_v "do_onefile" (st())) [fdv]
       (STDIO fs)
       (POSTv u. &UNIT_TYPE () u *
              STDIO (up_stdout (out ++ DROP pos content) 
                              (fsupdate fs fd 0 (LENGTH content) content)))`,
  NTAC 5 strip_tac >>
  `?N. STRLEN content - pos <= N` 
    by (qexists_tac`STRLEN content - pos` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`pos` >>
  Induct_on`N` >> strip_tac >> cases_on`STRLEN content = pos` >> fs[] >>
  xcf "do_onefile" (st()) >> fs[stdout_def,up_stdout_def] >>
  (xlet_auto >-(xcon >> xsimpl) >> xlet_auto >- xsimpl >>
   xlet_auto_spec(SOME(Q.SPECL [`fs`,`fd`,`1`] pipe_255_spec))
   >-(xsimpl >> rw[] >> instantiate >> xsimpl) >> xlet_auto >- xsimpl >> xif)
  >-(instantiate >> xcon >>
     fs[eof_def] >> pairarg_tac >> fs[] >> rfs[] >>
     `pos >= LENGTH contents` by fs[] >> imp_res_tac DROP_NIL >> xsimpl) >>
  first_x_assum (assume_tac o Q.SPEC`pos +nr`) >> rfs[]
  >-(xapp >> xsimpl >> qmatch_goalsub_abbrev_tac`STDIO fs'` >>
     map_every qexists_tac [`GC`,`out ++ TAKE nr (DROP pos content)`,`fs'`] >>
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
        cases_on`v'` >> rw[]))
  >-(`nr = 0` by fs[] >> fs[eof_def] >> pairarg_tac >> fs[] >>
    `pos' = STRLEN content`  by (rfs[] >> fs[]) >> fs[]));

val file_contents_def = Define `
  file_contents fnm fs = THE (ALOOKUP fs.files fnm)`

val catfiles_string_def = Define`
  catfiles_string fs fns =
    FLAT (MAP (λfnm. file_contents (File fnm) fs) fns)
`;

val cat_spec0 = Q.prove(
  `∀fns fnsv fs out.
     LIST_TYPE FILENAME fns fnsv ∧
     EVERY ((inFS_fname fs) o File) fns ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 256
    ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "cat" (get_ml_prog_state())) [fnsv]
       (STDIO fs * &stdout fs out)
       (POSTv u.
          &UNIT_TYPE () u *
          STDIO (up_stdout (out ++ catfiles_string fs fns) fs))`,
  Induct >> rpt strip_tac >> xcf "cat" (get_ml_prog_state()) >>
  fs[LIST_TYPE_def,stdout_def] >> xpull
  >- (xmatch >> xcon >> fs[up_stdout_def,fsupdate_unchanged,catfiles_string_def,
                           get_file_content_def] >> xsimpl) >>
  fs[FILENAME_def] >>
  xmatch >> progress inFS_fname_ALOOKUP_EXISTS >>
  cases_on `¬ STD_streams fs` >- (fs[STDIO_def] >> xpull) >> fs[] >>
  xlet_auto_spec(SOME(Q.SPECL[`h`,`v2_1`,`fs` ] openIn_STDIO_spec)) >>
  xsimpl >> progress nextFD_ltX >>
 `nextFD fs <> 0 /\ nextFD fs <> 1 /\ nextFD fs <> 2`
    by(fs[STD_streams_def] >> imp_res_tac ALOOKUP_MEM >> 
       metis_tac[nextFD_NOT_MEM]) >>
  `ALOOKUP (openFileFS h fs 0).infds 1 = SOME (IOStream(strlit "stdout"),STRLEN out)`
    by(fs[openFileFS_def] >> CASE_TAC >> fs[] >> cases_on`x` >> fs[openFile_def] >>
       `r.infds = (nextFD fs,File h,0) :: fs.infds` by fs[IO_fs_component_equality] >>
       fs[] >> CASE_TAC >> metis_tac[nextFD_NOT_MEM]) >>
  xlet_auto_spec (SOME(Q.SPECL[`content`,`0`, `File h`,`nextFD fs`, `wv`,
                               `openFileFS h fs 0`,`out`] do_onefile_spec))
  >-(xsimpl >> fs[wfFS_openFileFS,openFileFS_files,stdout_def] >>
     fs[ALOOKUP_inFS_fname_openFileFS_nextFD]) >>
  qmatch_goalsub_abbrev_tac `STDIO fs'` >>
  xlet_auto_spec (SOME (Q.SPECL[`nextFD fs`,`fs'`] close_STDIO_spec)) >> 
  xsimpl  >> fs[InvalidFD_exn_def,Abbr`fs'`,up_stdout_def]
  >-(irule ALOOKUP_validFD >>
     fs[fsupdate_def,ALIST_FUPDKEY_ALOOKUP,ALOOKUP_inFS_fname_openFileFS_nextFD] >>
     progress ALOOKUP_SOME_inFS_fname >> progress nextFD_ltX >>
     progress ALOOKUP_inFS_fname_openFileFS_nextFD >> 
     rfs[ALOOKUP_inFS_fname_openFileFS_nextFD]) >>
  xapp >> xsimpl >>
  qmatch_goalsub_abbrev_tac `STDIO fs'` >>
  map_every qexists_tac [`GC`,`out ++ file_contents (File h)  fs`,`fs'`] >>
  simp[Abbr`fs'`,catfiles_string_def, file_contents_def] >> xsimpl >>
  rw[] >>
  fs[fsupdate_def,ALIST_FUPDKEY_ALOOKUP,openFileFS_files,A_DELKEY_nextFD_openFileFS,
     A_DELKEY_ALIST_FUPDKEY_comm,ALOOKUP_inFS_fname_openFileFS_nextFD] >>
  `!ls fs0. EVERY ((inFS_fname fs0) o File) ls <=> 
            EVERY (\s. File s ∈ FDOM (alist_to_fmap fs0.files)) ls`
     by(Induct >> rw[inFS_fname_def]) >> fs[] >>
  qmatch_abbrev_tac`STDIO fs1 ==>> STDIO fs2` >>
  `fs2 = fs1` suffices_by xsimpl >> unabbrev_all_tac >>
  fs[insert_atI_end,TAKE_APPEND,TAKE_TAKE, fsupdate_def,ALIST_FUPDKEY_o,
     ALIST_FUPDKEY_unchanged,ALIST_FUPDKEY_ALOOKUP,openFileFS_numchars] >> rw[]
  >>(irule ALIST_FUPDKEY_eq >> fs[] >>
     rpt(qmatch_goalsub_abbrev_tac `_ l1 = _ l2` >>
     `l1 = l2` suffices_by fs[] >> unabbrev_all_tac) >>
     rw[MAP_EQ_f] >> rpt CASE_TAC >> imp_res_tac EVERY_MEM >> fs[]));

val cat_spec = save_thm(
  "cat_spec",
  cat_spec0 |> SIMP_RULE (srw_ss()) [])

val cat_main = process_topdecs`
  fun cat_main _ = cat (Commandline.arguments())`;
val _ = append_prog cat_main;

val hasFreeFD_def = Define
    `hasFreeFD fs = (CARD (set (MAP FST fs.infds)) < 256)`;

val cat_main_spec = Q.store_thm("cat_main_spec",
  `EVERY ((inFS_fname fs) o File) (MAP implode (TL cl)) ∧ hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"cat_main" (st())) [Conv NONE []]
     (STDIO fs * & stdout fs out * COMMANDLINE cl )
     (POSTv uv. &UNIT_TYPE () uv * 
       (STDIO (up_stdout (out ++ (catfiles_string fs (MAP implode (TL cl)))) fs))
       * COMMANDLINE cl)`,
  strip_tac
  \\ xcf "cat_main" (st()) \\ xpull
  \\ xmatch
  \\ xlet_auto >-(xcon >> xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (simp[COMMANDLINE_def] \\ xpull)
  \\ fs[wfcl_def]
  \\ xlet`POSTv av. &LIST_TYPE STRING_TYPE (MAP implode (TL cl)) av * STDIO fs * COMMANDLINE cl`
  >-(xapp \\ xsimpl \\ simp[MAP_TL] \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`cl` \\ xsimpl )
  \\ xapp
  \\ instantiate
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ map_every qexists_tac[`out`]
  \\ xsimpl
  \\ fs[EVERY_MAP,EVERY_MEM,hasFreeFD_def]
  \\ match_mp_tac LIST_TYPE_mono
  \\ instantiate
  \\ simp[MEM_MAP,FILENAME_def,PULL_EXISTS,explode_implode]
  \\ fs[commandLineFFITheory.validArg_def,EVERY_MEM,implode_def,EVERY_MAP]
  \\ Cases_on`cl` \\ fs[]);

val spec = cat_main_spec |> SPEC_ALL |> UNDISCH_ALL
            |> SIMP_RULE std_ss [Once STAR_ASSOC,fsioConstantsProgTheory.STDIO_def] 
            |> add_basis_proj;
val name = "cat_main"

val (semantics_thm,prog_tm) = call_thm (st()) name spec
val cat_prog_def = Define`cat_prog = ^prog_tm`;

val cat_semantics_thm =
  semantics_thm
  |> ONCE_REWRITE_RULE[GSYM cat_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[inFS_fname_def,LENGTH]
  |> curry save_thm "cat_semantics_thm";

val _ = export_theory();
