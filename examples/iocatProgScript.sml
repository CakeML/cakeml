(*
  Faster cat: process 2048 chars at a time.
*)
open preamble basis

val _ = new_theory "iocatProg"

val _ = translation_extends"basisProg";

val st = get_ml_prog_state;
val basis_st = get_ml_prog_state;

(* implementation of cat using copy *)
val _ = process_topdecs `
  fun cat fnames =
    case fnames of
      [] => ()
    | f::fs => (let val fd = TextIO.openIn f in
                      TextIO.copy fd TextIO.stdOut; TextIO.closeIn fd; cat fs end)
` |> append_prog

(* TODO: move *)
val file_contents_def = Define `
  file_contents fnm fs =
    implode (THE (ALOOKUP fs.inode_tbl (File (THE (ALOOKUP fs.files fnm)))))`
(* -- *)

val catfiles_string_def = Define`
  catfiles_string fs fns =
    concat (MAP (λfnm. file_contents fnm fs) fns)
`;

val cat_spec0 = Q.prove(
  `∀fns fnsv fs.
     LIST_TYPE FILENAME fns fnsv ∧
     EVERY (inFS_fname fs) fns ∧
     hasFreeFD fs
    ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "cat" (get_ml_prog_state())) [fnsv]
       (STDIO fs)
       (POSTv u.
          &UNIT_TYPE () u*
          STDIO (add_stdout fs (catfiles_string fs fns)))`,
 (
  Induct >> rpt strip_tac >> xcf "cat" (get_ml_prog_state()) >>
  fs[LIST_TYPE_def] >>
  (cases_on `¬ STD_streams fs` >- (fs[STDIO_def] >> xpull) >> fs[]) >>
  (reverse(Cases_on`consistentFS fs`)
    >-(fs[STDIO_def,IOFS_def] >> xpull >> fs[wfFS_def,consistentFS_def] >> res_tac))
  >- (xmatch >> xcon >>
      imp_res_tac STD_streams_stdout \\
      fs[catfiles_string_def,get_file_content_def] >>
      imp_res_tac add_stdo_nil \\ xsimpl) >>
  fs[FILENAME_def] >>
  xmatch >> progress (GEN_ALL inFS_fname_ALOOKUP_EXISTS) >>
  xlet_auto_spec(SOME(Q.SPECL[`h`,`v2_1`,`fs` ] openIn_STDIO_spec)) >>
  xsimpl >> imp_res_tac nextFD_ltX >> rfs[] >>
  `nextFD fs <> 0 /\ nextFD fs <> 1 /\ nextFD fs <> 2`
    by(metis_tac[STD_streams_def,ALOOKUP_MEM,nextFD_NOT_MEM]) >>
  `∃out. ALOOKUP fs.infds 1 = SOME (UStream(strlit "stdout"),WriteMode,STRLEN out) ∧
         ALOOKUP fs.inode_tbl (UStream(strlit "stdout")) = SOME out` by metis_tac[STD_streams_def] \\
  `ALOOKUP (openFileFS h fs ReadMode 0).infds 1 = SOME (UStream(strlit "stdout"),WriteMode,STRLEN out)`
    by(fs[openFileFS_def] >> CASE_TAC >> fs[] >> CASE_TAC >> fs[openFile_def] >>
       `r.infds = (nextFD fs,File iname,ReadMode,0) :: fs.infds` by fs[IO_fs_component_equality] >>
       fs[] >> CASE_TAC >> metis_tac[nextFD_NOT_MEM]) >>
  xlet_auto_spec (SOME(Q.SPECL[`File ino`,`UStream (strlit "stdout")`,`content`,
                               `nextFD fs`,`1`,`0`,`out`] copy_spec))
  >-(xsimpl >> fs[wfFS_openFileFS,openFileFS_inode_tbl,stdo_def] >>
     fs[ALOOKUP_inFS_fname_openFileFS_nextFD,OUTSTREAM_def,stdout_v_thm,GSYM stdOut_def]) >>
  qmatch_goalsub_abbrev_tac `STDIO fs'` >>
  drule (Q.SPECL [`fs'`, `h`, `ino`] ALOOKUP_inFS_fname_openFileFS_nextFD) >> rw[] >>
  xlet_auto_spec (SOME closeIn_STDIO_spec)
  >- (xsimpl >> fs[fsupdate_maxFD,Abbr`fs'`])
  >- (xsimpl >> fs[InvalidFD_exn_def,Abbr`fs'`,up_stdo_def] >>
      simp[validFileFD_def]
      \\ drule (GEN_ALL ALOOKUP_inFS_fname_openFileFS_nextFD)
      \\ simp[]) >>
  xapp >> xsimpl >> simp[Abbr`fs'`] >>
  qmatch_goalsub_abbrev_tac `STDIO fs'` >>
  map_every qexists_tac [`GC`,`fs'`] >>
  simp[Abbr`fs'`,catfiles_string_def, file_contents_def,fsupdate_fastForwardFD_comm] >> xsimpl >>
  conj_tac >- (
    `!ls fs0. consistentFS fs0 ==> (EVERY (inFS_fname fs0) ls ⇔
              EVERY (\s. s ∈ FDOM (alist_to_fmap fs0.files)) ls)`
       by(Induct >> fs[consistentFS_def,MEM_MAP,inFS_fname_def] >> rw[] >>
          EQ_TAC  >> rw[] >> fs[inFS_fname_def]
          >-(imp_res_tac ALOOKUP_EXISTS_IFF >>
             qmatch_assum_abbrev_tac`MEM (xx,yy) fs0.files` >>
             qexists_tac`(xx,yy)` >> fs[])
          >- res_tac
          >-(fs[MEM_FST_ALOOKUP_SOME])
          >- res_tac) >> fs[] >> rw[]
    >- fs[fsupdate_def,AFUPDKEY_ALOOKUP,openFileFS_files,ADELKEY_nextFD_openFileFS,
         ADELKEY_AFUPDKEY,ALOOKUP_inFS_fname_openFileFS_nextFD,ADELKEY_fastForwardFD_elim]
    >- fs[fsupdate_def,AFUPDKEY_ALOOKUP,openFileFS_files,ADELKEY_nextFD_openFileFS,
         ADELKEY_AFUPDKEY,ALOOKUP_inFS_fname_openFileFS_nextFD,ADELKEY_fastForwardFD_elim]
    >-(qmatch_goalsub_abbrev_tac`inFS_fname fs1` >>
       `consistentFS fs1`
        by (unabbrev_all_tac >> fs[consistentFS_def,fsupdate_def,openFileFS_def] >>
            rw[] >> res_tac) >>
       res_tac >> fs[Abbr`fs1`])) >>
  qmatch_goalsub_abbrev_tac`add_stdout fs'`
  \\ `fs' = up_stdout fs (implode (out ++ content))`
  by (
    fs[Abbr`fs'`,up_stdo_def,IO_fs_component_equality,fsupdate_def,
       openFileFS_numchars,openFileFS_inode_tbl,AFUPDKEY_ALOOKUP,openFileFS_files,
       ALOOKUP_inFS_fname_openFileFS_nextFD,ADELKEY_AFUPDKEY,
       ADELKEY_nextFD_openFileFS,AFUPDKEY_unchanged] ) \\
  qunabbrev_tac`fs'` \\ pop_assum SUBST_ALL_TAC \\
  qmatch_goalsub_abbrev_tac`ALOOKUP fs'.inode_tbl _` \\
  `fs'.inode_tbl = AFUPDKEY (UStream (strlit "stdout")) (λ_. out++content) fs.inode_tbl` by (
    fs[Abbr`fs'`,up_stdo_def,fsupdate_def,ALOOKUP_inFS_fname_openFileFS_nextFD,
       AFUPDKEY_ALOOKUP,K_DEF,AFUPDKEY_unchanged]) \\
  qunabbrev_tac`fs'` \\ pop_assum SUBST_ALL_TAC \\
  simp[AFUPDKEY_ALOOKUP] \\
  qmatch_goalsub_abbrev_tac`MAP f` \\
  qmatch_goalsub_abbrev_tac`_::(MAP f' _)` \\
  `f = f'` by (
    rw[Abbr`f`,Abbr`f'`,FUN_EQ_THM]
    \\ CASE_TAC \\ fs[up_stdo_files,fsupdate_files,openFileFS_files]
    ) \\
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
  \\ xsimpl));

val cat_spec = save_thm(
  "cat_spec",
  cat_spec0 |> SIMP_RULE (srw_ss()) [])

val cat_main = process_topdecs`
  fun cat_main _ = cat (CommandLine.arguments())`;
val _ = append_prog cat_main;

Theorem cat_main_spec:
   EVERY (inFS_fname fs) (TL cl) ∧ hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"cat_main" (st())) [Conv NONE []]
     (STDIO fs * COMMANDLINE cl )
     (POSTv uv. &UNIT_TYPE () uv *
       (STDIO (add_stdout fs (catfiles_string fs (TL cl))))
       * COMMANDLINE cl)
Proof
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
  \\ Cases_on`cl` \\ fs[]
QED

val st = st();

Theorem cat_whole_prog_spec:
   EVERY (inFS_fname fs) (TL cl) ∧ hasFreeFD fs ⇒
   whole_prog_spec ^(fetch_v"cat_main"st) cl fs NONE
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
val cat_prog_def = Define`cat_prog = ^prog_tm`;

val cat_semantics_thm =
  semantics_thm |> ONCE_REWRITE_RULE[GSYM cat_prog_def]
  |> DISCH_ALL |> SIMP_RULE(srw_ss())[AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> curry save_thm "cat_semantics_thm";

val _ = export_theory();
