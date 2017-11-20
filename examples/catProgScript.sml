open preamble basis

val _ = new_theory "catProg"

val _ = translation_extends"basisProg";

val _ = process_topdecs `
  fun do_onefile fname =
    let
      val fd = TextIO.openIn fname
      fun recurse () =
        (TextIO.print_char (TextIO.read_char fd); recurse ())
        handle TextIO.EndOfFile => ()
    in
      recurse () ;
      TextIO.close fd
    end

  fun cat fnames =
    case fnames of
      [] => ()
    | f::fs => (do_onefile f ; cat fs)
` |> append_prog

(* TODO: move *)
val SEP_EXISTS_UNWIND1 = Q.store_thm("SEP_EXISTS_UNWIND1",
  `(SEP_EXISTS x. &(a = x) * P x) = P a`,
  rw[Once FUN_EQ_THM,SEP_EXISTS_THM,STAR_def,Once EQ_IMP_THM,cond_def,SPLIT_def]);

val SEP_EXISTS_UNWIND2 = Q.store_thm("SEP_EXISTS_UNWIND2",
  `(SEP_EXISTS x. &(x = a) * P x) = P a`,
  rw[Once FUN_EQ_THM,SEP_EXISTS_THM,STAR_def,Once EQ_IMP_THM,cond_def,SPLIT_def]);
(* -- *)

val do_onefile_spec = Q.store_thm(
  "do_onefile_spec",
  `∀fnm fnv fs.
      FILENAME fnm fnv ∧ hasFreeFD fs
    ⇒
      app (p:'ffi ffi_proj) ^(fetch_v "do_onefile" (get_ml_prog_state())) [fnv]
       (STDIO fs)
       (POST
         (\u. SEP_EXISTS content.
              &UNIT_TYPE () u *
              &(ALOOKUP fs.files (File fnm) = SOME content) *
              STDIO (add_stdout fs content))
         (\e. &BadFileName_exn e *
              &(~inFS_fname fs (File fnm)) *
              STDIO fs))`,
  rpt strip_tac >> xcf "do_onefile" (get_ml_prog_state()) >>
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull) \\
  xlet_auto_spec (SOME (SPEC_ALL openIn_STDIO_spec))
  >- xsimpl
  >- xsimpl
  \\ imp_res_tac nextFD_leX
  \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
  \\ pop_assum(qspec_then`0`strip_assume_tac)
  \\ imp_res_tac STD_streams_nextFD
  \\ qabbrev_tac`fd = nextFD fs` \\
  progress inFS_fname_ALOOKUP_EXISTS >>
  xfun_spec `recurse`
    `!m n fs00 uv.
       UNIT_TYPE () uv ∧ m = LENGTH content - n ∧ n ≤ LENGTH content ∧
       STD_streams fs00 ∧ get_file_content fs00 fd = SOME (content, n)
         ==>
       app p recurse [uv]
         (STDIO fs00)
         (POSTv u.
            &UNIT_TYPE () u *
            STDIO (add_stdout (fastForwardFD fs00 fd) (DROP n content)))`
  >- (Induct
      >- ((* base case *)
          rpt strip_tac >> `n = LENGTH content` by simp[] >> fs[] >> rveq >>
          xapp >> fs[UNIT_TYPE_def] >> xmatch >>
          imp_res_tac get_file_content_eof >> fs[] >>
          xhandle`POSTe e. &EndOfFile_exn e * STDIO fs00`
          >- ( xlet_auto \\ xsimpl \\ simp[bumpFD_0] \\ xsimpl )
          \\ xcases \\ fs[EndOfFile_exn_def]
          \\ reverse conj_tac >- (EVAL_TAC \\ fs[])
          \\ xcon
          \\ imp_res_tac STD_streams_stdout
          \\ simp[DROP_LENGTH_NIL,add_stdout_fastForwardFD]
          \\ imp_res_tac add_stdo_nil \\ xsimpl
          \\ simp[fastForwardFD_0]
          \\ xsimpl) >>
      rpt strip_tac >> fs[] >> last_assum xapp_spec >>
      qpat_x_assum `UNIT_TYPE () _` mp_tac >> simp[UNIT_TYPE_def] >>
      strip_tac >> xmatch >>
      imp_res_tac get_file_content_eof >> rfs[] >>
      qho_match_abbrev_tac`cf_handle _ _ _ _ (POSTv v. post v)` \\
      xhandle`POSTv v. post v` \\ simp[Abbr`post`]
      >- (
        xlet_auto \\ xsimpl \\
        xlet_auto_spec (SOME (Q.SPEC`forwardFD fs00 fd 1`(Q.GEN`fs`print_char_spec)))
        >- xsimpl
        \\ xlet_auto >- ( xcon \\ xsimpl )
        \\ xapp
        \\ qmatch_goalsub_abbrev_tac`STDIO fs01`
        \\ map_every qexists_tac [`emp`,`n+1`,`fs01`]
        \\ xsimpl
        \\ simp[Abbr`fs01`,STD_streams_add_stdout,
                STD_streams_forwardFD,get_file_content_add_stdout]
        \\ simp[add_stdo_forwardFD,add_stdout_fastForwardFD,
                STD_streams_forwardFD,STD_streams_fastForwardFD,STD_streams_add_stdout]
        \\ simp[fastForwardFD_forwardFD,get_file_content_add_stdout,STD_streams_add_stdout]
        \\ simp[UNIT_TYPE_def]
        \\ imp_res_tac STD_streams_stdout
        \\ imp_res_tac add_stdo_o
        \\ xsimpl
        \\ simp[DROP_CONS_EL,ADD1]
        \\ xsimpl)
      \\ xsimpl ) >>
  xlet_auto >- (xret >> xsimpl) >>
  (* calling recurse *)
  (*
  srw_tac[star_ss][SEP_EXISTS_UNWIND1]
  \\ first_x_assum(qspecl_then[`LENGTH content`,`0`]mp_tac)
  \\ simp[UNIT_TYPE_def]
  \\ simp[fsFFITheory.get_file_content_def,PULL_EXISTS,FORALL_PROD]
  \\ disch_then(first_assum o (mp_then (Pos (el 2)) mp_tac))
  \\ simp[STD_streams_openFileFS] \\ strip_tac
  (* TODO: xlet_auto fails here - not enough information for the heuristics   *)
  *)
  xlet `POSTv u3. &(u3 = Conv NONE []) *
                  STDIO (add_stdout (fastForwardFD (openFileFS fnm fs 0) fd) content)`
  >- (xapp >>
      simp[fsFFITheory.get_file_content_def,PULL_EXISTS,EXISTS_PROD] >>
      goal_assum(first_assum o (mp_then (Pos (el 3)) mp_tac)) >>
      xsimpl >>
      fs[UNIT_TYPE_def,STD_streams_openFileFS]) >>
  (* calling close *)
  xapp_spec close_STDIO_spec >>
  xsimpl >> instantiate >>
  qmatch_goalsub_abbrev_tac`STDIO fs0` >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac`fs0` \\ xsimpl \\
  simp[Abbr`fs0`,UNIT_TYPE_def,add_stdout_fastForwardFD,STD_streams_openFileFS] \\
  simp[GSYM add_stdo_A_DELKEY,Abbr`fd`,openFileFS_A_DELKEY_nextFD] \\
  xsimpl);

val file_contents_def = Define `
  file_contents fnm fs = THE (ALOOKUP fs.files (File fnm))`

val file_contents_add_stdout = Q.store_thm("file_contents_add_stdout",
  `STD_streams fs ⇒
   file_contents fnm (add_stdout fs out) = file_contents fnm fs`,
  rw[file_contents_def,add_stdo_def,up_stdo_def,fsFFITheory.fsupdate_def]
  \\ CASE_TAC \\ CASE_TAC
  \\ simp[ALIST_FUPDKEY_ALOOKUP]
  \\ TOP_CASE_TAC \\ rw[]
  \\ metis_tac[STD_streams_def,SOME_11,PAIR,FST,fsFFITheory.inode_distinct]);

val catfiles_string_def = Define`
  catfiles_string fs fns =
    FLAT (MAP (λfnm. file_contents fnm fs) fns)
`;

val cat_spec0 = Q.prove(
  `∀fns fnsv fs.
     LIST_TYPE FILENAME fns fnsv ∧
     EVERY (inFS_fname fs o File) fns ∧
     hasFreeFD fs
    ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "cat" (get_ml_prog_state())) [fnsv]
       (STDIO fs)
       (POSTv u.
          &UNIT_TYPE () u *
          STDIO (add_stdout fs (catfiles_string fs fns)))`,
  Induct >>
  rpt strip_tac >> xcf "cat" (get_ml_prog_state()) >>
  fs[LIST_TYPE_def] >>
  (reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull))
  >- (xmatch >> xret >> simp[catfiles_string_def, file_contents_def] >>
      imp_res_tac STD_streams_stdout >>
      imp_res_tac add_stdo_nil >> xsimpl) >>
  xmatch >>
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
  simp[Once file_contents_def,SimpR``(==>>)``] \\
  simp[file_contents_add_stdout] \\ xsimpl)

val cat_spec = save_thm(
  "cat_spec",
  cat_spec0 |> SIMP_RULE (srw_ss()) [])

val _ = process_topdecs `
  fun cat1 f =
    (do_onefile f)
    handle TextIO.BadFileName => ()
` |> append_prog

val catfile_string_def = Define `
  catfile_string fs fnm =
    if inFS_fname fs (File fnm) then file_contents fnm fs
    else []`

val cat1_spec = Q.store_thm (
  "cat1_spec",
  `!fnm fnmv.
     FILENAME fnm fnmv /\ hasFreeFD fs ==>
     app (p:'ffi ffi_proj) ^(fetch_v "cat1" (get_ml_prog_state())) [fnmv]
       (STDIO fs)
       (POSTv u.
          &UNIT_TYPE () u *
          STDIO (add_stdout fs (catfile_string fs fnm)))`,
  xcf "cat1" (get_ml_prog_state()) >>
  xhandle `POST
             (\u. SEP_EXISTS content. &UNIT_TYPE () u *
               &(ALOOKUP fs.files (File fnm) = SOME content) *
               STDIO (add_stdout fs content))
             (\e. &BadFileName_exn e * &(~inFS_fname fs (File fnm)) *
                  STDIO fs)` >> fs[]
  >- ((*xapp_prepare_goal*) xapp >> fs[])
  >- (xsimpl >> rpt strip_tac >>
      imp_res_tac ALOOKUP_SOME_inFS_fname >>
      simp[catfile_string_def, file_contents_def] >>
      xsimpl) >>
  fs [BadFileName_exn_def] >> xcases >> xret >> xsimpl >>
  simp[catfile_string_def] >>
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xsimpl) >>
  imp_res_tac STD_streams_stdout >>
  imp_res_tac add_stdo_nil >>
  xsimpl
);

val cat_main = process_topdecs`
  fun cat_main _ = cat (CommandLine.arguments())`;
val _ = append_prog cat_main;

val st = get_ml_prog_state();

val cat_main_spec = Q.store_thm("cat_main_spec",
  `EVERY (inFS_fname fs o File) (MAP implode (TL cl)) ∧ hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"cat_main"st) [Conv NONE []]
     (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv * (STDIO (add_stdout fs (catfiles_string fs (MAP implode (TL cl))))
                                    * (COMMANDLINE cl)))`,
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
  \\ fs[validArg_def,EVERY_MEM]);

val spec = cat_main_spec |> SPEC_ALL |> UNDISCH_ALL
            |> SIMP_RULE std_ss [STDIO_def] |> add_basis_proj;
val name = "cat_main"
val (semantics_thm,prog_tm) = call_thm st name spec
val cat_prog_def = Define`cat_prog = ^prog_tm`;

val cat_semantics_thm =
  semantics_thm
  |> ONCE_REWRITE_RULE[GSYM cat_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[STD_streams_add_stdout,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> curry save_thm "cat_semantics_thm";

val _ = export_theory();
