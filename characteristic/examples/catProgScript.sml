open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib
     mlstringTheory rofsFFITheory mlfileioProgTheory
     ioProgTheory basisFunctionsLib ioProgLib

val _ = new_theory "catProg"

val _ = translation_extends"ioProg";

val _ = process_topdecs `
  fun do_onefile fname =
    let
      val fd = FileIO.openIn fname
      fun recurse () =
        case FileIO.fgetc fd of
            NONE => ()
          | SOME c => (CharIO.write c; recurse ())
    in
      recurse () ;
      FileIO.close fd
    end

  fun cat fnames =
    case fnames of
      [] => ()
    | f::fs => (do_onefile f ; cat fs)
` |> append_prog

val do_onefile_spec = Q.store_thm(
  "do_onefile_spec",
  `∀fnm fnv fs out.
      FILENAME fnm fnv ∧
      CARD (FDOM (alist_to_fmap fs.infds)) < 255
    ⇒
      app (p:'ffi ffi_proj) ^(fetch_v "do_onefile" (get_ml_prog_state())) [fnv]
       (ROFS fs * STDOUT out)
       (POST
         (\u. SEP_EXISTS content.
              &UNIT_TYPE () u *
              &(ALOOKUP fs.files fnm = SOME content) *
              ROFS fs * STDOUT (out ++ content))
         (\e. &BadFileName_exn e *
              &(~inFS_fname fs fnm) *
              ROFS fs * STDOUT out))`,
  rpt strip_tac >> xcf "do_onefile" (get_ml_prog_state()) >>
  xlet `POST
          (\fdv.
            &(WORD (n2w (nextFD fs) : word8) fdv ∧
              validFD (nextFD fs) (openFileFS fnm fs) ∧
              inFS_fname fs fnm) *
            ROFS (openFileFS fnm fs) * STDOUT out)
          (\e.
            &(BadFileName_exn e ∧ ~inFS_fname fs fnm) *
            ROFS fs * STDOUT out)`
  >- (xapp >> fs[] >> instantiate >> xsimpl)
  >- xsimpl >>
  qabbrev_tac `fd = nextFD fs` >>
  qabbrev_tac `fs0 = openFileFS fnm fs` >>
  `ALOOKUP fs0.infds fd = SOME (fnm, 0)` by
    (UNABBREV_ALL_TAC >>
     fs [validFD_def, openFileFS_def, openFile_def] >>
     progress inFS_fname_ALOOKUP_EXISTS >> fs [] >>
     rfs[nextFD_ltX] >> NO_TAC) >>
  progress inFS_fname_ALOOKUP_EXISTS >>
  xfun_spec `recurse`
    `!m n fs00 out00 uv.
       UNIT_TYPE () uv ∧ m = LENGTH content - n ∧ n ≤ LENGTH content ∧
       fs00.files = fs.files ∧
       ALOOKUP fs00.infds fd = SOME (fnm, n)
         ==>
       app p recurse [uv]
         (ROFS fs00 * STDOUT out00)
         (POSTv u.
            &UNIT_TYPE () u *
            ROFS (fs00 with <|
                     infds updated_by
                           ALIST_FUPDKEY fd (I ## K (LENGTH content))
                   |>) * STDOUT (out00 ++ DROP n content))`
  >- (Induct
      >- ((* base case *)
          rpt strip_tac >> `n = LENGTH content` by simp[] >> fs[] >> rveq >>
          xapp >> fs[UNIT_TYPE_def] >> xmatch >>
          xlet `POSTv av.
                  &OPTION_TYPE CHAR NONE av * ROFS fs00 * STDOUT out00`
          >- (rveq >> xapp >> xsimpl >> instantiate >>
              `fd < 256` by simp[Abbr`fd`, nextFD_ltX] >> simp[] >>
              xsimpl >> map_every qexists_tac [`STDOUT out00`, `fs00`] >> xsimpl >>
              conj_tac
              >- (simp[validFD_def, EXISTS_PROD, MEM_MAP] >>
                  metis_tac[EXISTS_PROD, PAIR, ALOOKUP_EXISTS_IFF]) >>
              `FDchar fd fs00 = NONE` by simp[FDchar_def] >>
              `bumpFD fd fs00 = fs00` by simp[bumpFD_def] >>
              xsimpl) >>
          fs[OPTION_TYPE_def] >> xmatch >> xret >>
          simp[DROP_LENGTH_NIL] >>
          `fs00 with <| infds updated_by
                              ALIST_FUPDKEY fd (I ## K (LENGTH content)) |> = fs00`
            by (simp[RO_fs_component_equality] >>
                irule ALIST_FUPDKEY_unchanged >> simp[]) >> simp[] >>
          xsimpl) >>
      rpt strip_tac >> fs[] >> last_assum xapp_spec >>
      qpat_x_assum `UNIT_TYPE () _` mp_tac >> simp[UNIT_TYPE_def] >>
      strip_tac >> xmatch >>
      xlet `POSTv av. &OPTION_TYPE CHAR (FDchar fd fs00) av *
                      ROFS (bumpFD fd fs00) * STDOUT out00`
      >- (xapp >> xsimpl >> instantiate >>
          `fd < 256` by simp[Abbr`fd`, nextFD_ltX] >> simp[] >>
          xsimpl >> map_every qexists_tac [`STDOUT out00`, `fs00`] >> xsimpl >>
          simp[validFD_def, MEM_MAP, EXISTS_PROD] >>
          metis_tac[EXISTS_PROD, PAIR, ALOOKUP_EXISTS_IFF]) >>
      `∃c. FDchar fd fs00 = SOME c` by (irule neof_FDchar >> simp[eof_def] >> NO_TAC) >>
      fs[OPTION_TYPE_def] >> rveq >> xmatch >>
      qabbrev_tac `fs01 = bumpFD fd fs00` >>
      xlet `POSTv u. &UNIT_TYPE () u * ROFS fs01 * STDOUT (out00 ++ [c])`
      >- (xapp >> xsimpl >> instantiate >> xsimpl >>
          map_every qexists_tac [`ROFS fs01`,`out00`] >> xsimpl) >>
      xlet `POSTv bv. &UNIT_TYPE () bv * ROFS fs01 * STDOUT (out00 ++ [c])`
      >- (xret >> xsimpl) >>
      first_x_assum xapp_spec >>
      map_every qexists_tac [`emp`, `out00 ++ [c]`, `n + 1`, `fs01`] >> simp[] >> xsimpl >>
      simp[UNIT_TYPE_def] >> reverse conj_tac
      >- (qmatch_abbrev_tac `ROFS fs1 * STDOUT s1 ==>> ROFS fs2 * STDOUT s2 * GC` >>
          `fs2 = fs1 ∧ s1 = s2` suffices_by xsimpl >>
          UNABBREV_ALL_TAC >> simp[RO_fs_component_equality, bumpFD_def] >>
          conj_tac
          >- (simp[ALIST_FUPDKEY_o, combinTheory.o_DEF] >>
              rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
              simp[FUN_EQ_THM, FORALL_PROD]) >>
          `n < LENGTH content` by simp[] >>
          `c = EL n content` suffices_by metis_tac[DROP_CONS_EL,ADD1] >>
          fs[FDchar_def] >> rfs[] >> rveq >> fs[]>> rfs[]) >> conj_tac
      >- simp[Abbr`fs01`, bumpFD_def]
      >- simp[Abbr`fs01`, bumpFD_def, ALIST_FUPDKEY_ALOOKUP]) >>
  xlet `POSTv u2. &UNIT_TYPE () u2 * ROFS fs0 * STDOUT out`
  >- (xret >> xsimpl) >>
  (* calling recurse *)
  xlet `POSTv u3. &UNIT_TYPE () u3 *
                  ROFS (fs0 with <|
                           infds updated_by
                              ALIST_FUPDKEY fd (I ## K (LENGTH content))
                         |>) * STDOUT (out ++ content)`
  >- (xapp >> map_every qexists_tac [`emp`, `out`, `0`, `fs0`] >> simp[] >>
      xsimpl >>
      fs[] >>
      simp[Abbr`fs0`, openFileFS_def, openFile_def, Abbr`fd`, nextFD_ltX]) >>
  (* calling close *)
  xapp >> xsimpl >> instantiate >>
  `fd < 256` by (fs[] >> simp[Abbr`fd`, nextFD_ltX] >> NO_TAC) >> simp[] >>
  map_every qexists_tac [`STDOUT (out ++ content)`,
    `fs0 with <| infds updated_by ALIST_FUPDKEY fd (I ## K (LENGTH content)) |>`
  ] >> simp[] >> xsimpl >> conj_tac
  >- (simp[validFD_def, EXISTS_PROD, MEM_MAP] >>
      metis_tac[EXISTS_PROD, ALOOKUP_EXISTS_IFF, PAIR]) >>
  rpt strip_tac >>
  qmatch_abbrev_tac `ROFS fs1 ==>> ROFS fs2 * GC` >>
  `fs1 = fs2` suffices_by xsimpl >> UNABBREV_ALL_TAC >>
  simp[RO_fs_component_equality, openFileFS_def, openFile_def] >> fs[] >>
  simp[nextFD_ltX] >>
  simp[A_DELKEY_def, ALIST_FUPDKEY_def, FILTER_EQ_ID, EVERY_MEM,
       FORALL_PROD, nextFD_NOT_MEM]);

val file_contents_def = Define `
  file_contents fnm fs = THE (ALOOKUP fs.files fnm)`

val catfiles_string_def = Define`
  catfiles_string fs fns =
    FLAT (MAP (λfnm. file_contents fnm fs) fns)
`;

val cat_spec0 = Q.prove(
  `∀fns fnsv fs out.
     LIST_TYPE FILENAME fns fnsv ∧
     EVERY (inFS_fname fs) fns ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 255
    ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "cat" (get_ml_prog_state())) [fnsv]
       (ROFS fs * STDOUT out)
       (POSTv u.
          &UNIT_TYPE () u *
          ROFS fs *
          STDOUT (out ++ catfiles_string fs fns))`,
  Induct >>
  rpt strip_tac >> xcf "cat" (get_ml_prog_state()) >>
  fs[LIST_TYPE_def]
  >- (xmatch >> xret >> simp[catfiles_string_def, file_contents_def] >> xsimpl >>
      qmatch_abbrev_tac `ROFS fs1 ==>> ROFS fs2 * GC` >>
      `fs1 = fs2` suffices_by xsimpl >>
      UNABBREV_ALL_TAC >> simp[RO_fs_component_equality]) >>
  xmatch >>
  progress inFS_fname_ALOOKUP_EXISTS >>
  rename1 `ALOOKUP fs.files _ = SOME cnts` >>
  xlet `POSTv uv.
         &UNIT_TYPE () uv * ROFS fs *
         STDOUT (out ++ cnts)`
  >- (xapp >> xsimpl >> instantiate >> map_every qexists_tac[`emp`,`out`] >> xsimpl) >>
  xapp >>
  map_every qexists_tac
    [`emp`, `out ++ cnts`, `fs`] >>
  simp[] >> xsimpl >>
  qmatch_abbrev_tac `STDOUT fs1 ==>> STDOUT fs2 * GC` >>
  `fs1 = fs2` suffices_by xsimpl >> UNABBREV_ALL_TAC >>
  simp[catfiles_string_def, file_contents_def])

val cat_spec = save_thm(
  "cat_spec",
  cat_spec0 |> SIMP_RULE (srw_ss()) [])

val _ = process_topdecs `
  fun cat1 f =
    (do_onefile f)
    handle FileIO.BadFileName => ()
` |> append_prog

val catfile_string_def = Define `
  catfile_string fs fnm =
    if inFS_fname fs fnm then file_contents fnm fs
    else []`

val cat1_spec = Q.store_thm (
  "cat1_spec",
  `!fnm fnmv.
     FILENAME fnm fnmv /\
     CARD (FDOM (alist_to_fmap fs.infds)) < 255 ==>
     app (p:'ffi ffi_proj) ^(fetch_v "cat1" (get_ml_prog_state())) [fnmv]
       (ROFS fs * STDOUT out)
       (POSTv u.
          &UNIT_TYPE () u * ROFS fs *
          STDOUT (out ++ catfile_string fs fnm))`,
  xcf "cat1" (get_ml_prog_state()) >>
  xhandle `POST
             (\u. SEP_EXISTS content. &UNIT_TYPE () u *
               &(ALOOKUP fs.files fnm = SOME content) *
               ROFS fs *
               STDOUT (out ++ content))
             (\e. &BadFileName_exn e * &(~inFS_fname fs fnm) *
                  ROFS fs * STDOUT out)` >> fs[]
  >- ((*xapp_prepare_goal*) xapp >> fs[])
  >- (xsimpl >> rpt strip_tac >>
      qmatch_abbrev_tac `STDOUT fs1 ==>> STDOUT fs2` >>
      `fs1 = fs2` suffices_by xsimpl >> UNABBREV_ALL_TAC >>
      simp[ catfile_string_def, file_contents_def] >>
      progress ALOOKUP_SOME_inFS_fname >> fs []) >>
  fs [BadFileName_exn_def] >> xcases >> xret >> xsimpl >>
      qmatch_abbrev_tac `STDOUT fs1 ==>> STDOUT fs2 * GC` >>
      `fs1 = fs2` suffices_by xsimpl >> UNABBREV_ALL_TAC >>
      simp[catfile_string_def, file_contents_def]
);

val cat_main = process_topdecs`
  fun cat_main wildcard = cat (Commandline.arguments())`;
val _ = append_prog cat_main;

val st = get_ml_prog_state();

val cat_main_spec = Q.store_thm("cat_main_spec",
  `cl ≠ [] ∧ EVERY validArg cl ∧ LENGTH (FLAT cl) + LENGTH cl ≤ 256 ∧
  (* TODO: package the above assumptions up better? e.g. inside COMMANDLINE *)
   EVERY (inFS_fname fs) (MAP implode (TL cl)) ∧
   CARD (set (MAP FST fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"cat_main"st) [Conv NONE []]
     (STDOUT out * ROFS fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv * (STDOUT (out ++ (catfiles_string fs (MAP implode (TL cl))))
                                    * (ROFS fs * COMMANDLINE cl)))`,
  strip_tac
  \\ xcf "cat_main" st
  \\ xmatch
  \\ xlet`POSTv uv. &UNIT_TYPE () uv * STDOUT out * ROFS fs * COMMANDLINE cl`
  >- (xcon \\ xsimpl)
  \\ xlet`POSTv av. &LIST_TYPE STRING_TYPE (MAP implode (TL cl)) av * STDOUT out * ROFS fs * COMMANDLINE cl`
  >- (
    xapp (* TODO: this fails in obscure ways if 'ffi is replaced by 'a in the goal. this is too fragile *)
    \\ instantiate
    \\ xsimpl
    \\ simp[MAP_TL,NULL_EQ,LENGTH_FLAT,MAP_MAP_o,o_DEF]
    \\ Q.ISPECL_THEN[`STRLEN`]mp_tac SUM_MAP_PLUS
    \\ disch_then(qspecl_then[`K 1`,`cl`]mp_tac)
    \\ simp[MAP_K_REPLICATE,SUM_REPLICATE,GSYM LENGTH_FLAT])
  \\ xapp
  \\ instantiate
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ map_every qexists_tac[`out`]
  \\ xsimpl
  \\ fs[EVERY_MAP,EVERY_MEM]
  \\ match_mp_tac LIST_TYPE_mono
  \\ instantiate
  \\ simp[MEM_MAP,FILENAME_def,PULL_EXISTS,explode_implode]
  \\ fs[commandLineFFITheory.validArg_def,EVERY_MEM,implode_def,EVERY_MAP]
  \\ Cases_on`cl` \\ fs[]);

val spec = cat_main_spec |> SPEC_ALL |> UNDISCH_ALL
            |> SIMP_RULE std_ss [Once STAR_ASSOC] |> add_basis_proj;
val name = "cat_main"
val (semantics_thm,prog_tm) = call_thm st name spec
val cat_prog_def = Define`cat_prog = ^prog_tm`;

val cat_semantics_thm =
  semantics_thm
  |> ONCE_REWRITE_RULE[GSYM cat_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[wfFS_def,inFS_fname_def]
  |> curry save_thm "cat_semantics_thm";

val _ = export_theory();
