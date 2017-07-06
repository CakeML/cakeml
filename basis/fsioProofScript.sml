open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory fsFFITheory fsFFIProofTheory fsioProgTheory 
     cfLetAutoLib cfLetAutoTheory optionMonadTheory cfHeapsBaseTheory
     mlw8arrayProgTheory mlstringProgTheory cfMainTheory
    
val _ = new_theory"fsioProof";

val _ = translation_extends "fsioProg";
val _ = monadsyntax.add_monadsyntax();

val WORD_UNICITY_R = Q.store_thm("WORD_UNICITY_R[xlet_auto_match]",
`!f fv fv'. WORD (f :word8) fv ==> (WORD f fv' <=> fv' = fv)`, fs[WORD_def]);

val IOFS_iobuff_def = Define`
  IOFS_iobuff =
    SEP_EXISTS v. W8ARRAY iobuff_loc v * cond (LENGTH v = 258) `;

val IOFS_def = Define `
  IOFS fs = IOx fs_ffi_part fs * &(wfFS fs)`

val IOFS_precond = Q.store_thm("IOFS_precond",
  `wfFS fs ⇒
   IOFS fs
    {FFI_part (encode fs) (mk_ffi_next fs_ffi_part) (MAP FST (SND(SND fs_ffi_part))) events}`,
  rw[IOFS_def,cfHeapsBaseTheory.IOx_def,fs_ffi_part_def,cfHeapsBaseTheory.IO_def,one_def]
  \\ rw[set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,set_sepTheory.SEP_CLAUSES]);

val iobuff_loc = EVAL``iobuff_loc`` |> curry save_thm "iobuff_loc"

val _ = export_rewrites["iobuff_loc"]

val IOFS_iobuff_HPROP_INJ = Q.store_thm("IOFS_iobuff_HPROP_INJ[hprop_inj]",
`!fs1 fs2. HPROP_INJ (IOFS fs1) (IOFS fs2) (fs2 = fs1)`,
  rw[HPROP_INJ_def, IOFS_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM,
     HCOND_EXTRACT] >>
  fs[IOFS_def, IOx_def, fs_ffi_part_def] >>
  EQ_TAC >> rpt DISCH_TAC >> IMP_RES_TAC FRAME_UNIQUE_IO >> fs[]);

val BadFileName_exn_def = Define `
  BadFileName_exn v =
    (v = Conv (SOME ("BadFileName", TypeExn (Long "IO" (Short "BadFileName")))) [])`

val BadFileName_UNICITY = Q.store_thm("BadFileName_UNICITY[xlet_auto_match]",
`!v1 v2. BadFileName_exn v1 ==> (BadFileName_exn v2 <=> v2 = v1)`,
  fs[BadFileName_exn_def]);

val InvalidFD_exn_def = Define `
  InvalidFD_exn v =
    (v = Conv (SOME ("InvalidFD", TypeExn (Long "IO" (Short "InvalidFD")))) [])`

val InvalidFD_UNICITY = Q.store_thm("InvalidFD_UNICITY[xlet_auto_match]",
`!v1 v2. InvalidFD_exn v1 ==> (InvalidFD_exn v2 <=> v2 = v1)`,
  fs[InvalidFD_exn_def]);

val EndOfFile_exn_def = Define `
  EndOfFile_exn v =
    (v = Conv (SOME ("EndOfFile", TypeExn (Long "IO" (Short "EndOfFile")))) [])`

val EndOfFile_UNICITY = Q.store_thm("EndOfFile_UNICITY[xlet_auto_match]",
`!v1 v2. EndOfFile_exn v1 ==> (EndOfFile_exn v2 <=> v2 = v1)`,
  fs[EndOfFile_exn_def]);

val FILENAME_def = Define `
  FILENAME s sv =
    (STRING_TYPE s sv ∧
     ¬MEM (CHR 0) (explode s) ∧
     strlen s < 256)
`;

val filename_tac = metis_tac[FILENAME_def,EqualityType_NUM_BOOL,EqualityType_def];

val FILENAME_UNICITY_R = Q.store_thm("FILENAME_UNICITY_R[xlet_auto_match]",
`!f fv fv'. FILENAME f fv ==> (FILENAME f fv' <=> fv' = fv)`, filename_tac);

val FILENAME_UNICITY_L = Q.store_thm("FILENAME_UNICITY_L[xlet_auto_match]",
`!f f' fv. FILENAME f fv ==> (FILENAME f' fv <=> f' = f)`, filename_tac);

val FILENAME_STRING_UNICITY_R =
  Q.store_thm("FILENAME_STRING_UNICITY_R[xlet_auto_match]",
  `!f fv fv'. FILENAME f fv ==> (STRING_TYPE f fv' <=> fv' = fv)`,
  filename_tac);

val FILENAME_STRING_UNICITY_L =
  Q.store_thm("FILENAME_STRING_UNICITY_L[xlet_auto_match]",
  `!f f' fv. FILENAME f fv ==> (STRING_TYPE f' fv <=> f' = f)`, filename_tac);

val STRING_FILENAME_UNICITY_R =
  Q.store_thm("STRING_FILENAME_UNICITY_R[xlet_auto_match]",
  `!f fv fv'. STRING_TYPE f fv ==> 
    (FILENAME f fv' <=> fv' = fv /\ ¬MEM #"\^@" (explode f) /\ strlen f < 256)`,
  filename_tac);

val STRING_FILENAME_UNICITY_L =
  Q.store_thm("STRING_FILENAME_UNICITY_L[xlet_auto_match]",
  `!f f' fv. STRING_TYPE f fv ==>
    (FILENAME f' fv <=> f' = f /\ ¬MEM #"\^@" (explode f) /\ strlen f < 256)`, 
  filename_tac);

val basis_st = get_ml_prog_state;

val copyi_spec = Q.store_thm(
  "copyi_spec",
  `∀n nv cs csv a av.
     NUM n nv /\ n + LENGTH cs <= LENGTH a /\ LIST_TYPE CHAR cs csv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "IO.copyi" (basis_st()))
       [av; nv; csv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) *
                 W8ARRAY av (insert_atI (MAP (n2w o ORD) cs) n a))`,
  Induct_on `cs` >> fs[LIST_TYPE_def, LENGTH_NIL] >>
  xcf "IO.copyi" (basis_st()) >> xmatch
  >-(xcon >> xsimpl >> simp[insert_atI_NIL]) >>
  rpt(xlet_auto >- (xsimpl)) >> xapp >> xsimpl >> 
  fs[NUM_def,GSYM LUPDATE_insert_commute,LUPDATE_commutes,insert_atI_app,
     insert_atI_NIL,insert_atI_CONS] >>
  instantiate);

val copyi_nts_spec = Q.store_thm(
  "copyi_nts_spec",
  `∀n nv cs csv a av.
     NUM n nv /\ n + LENGTH cs < LENGTH a /\ LIST_TYPE CHAR cs csv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "IO.copyi_nts" (basis_st()))
       [av; nv; csv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) *
                 W8ARRAY av (insert_atI (MAP (n2w o ORD) cs ++ [0w]) n a))`,
  Induct_on `cs` >> fs[LIST_TYPE_def, LENGTH_NIL] >>
  xcf "IO.copyi_nts" (basis_st()) >> xmatch
  >-(xlet_auto >-(xsimpl) >>
     xapp >> xsimpl >> simp[insert_atI_NIL] >> xsimpl >>
     instantiate >> simp[insert_atI_NIL,insert_atI_CONS]) >>
  rpt(xlet_auto >- (xsimpl)) >> xapp >> xsimpl >> 
  fs[NUM_def] >> instantiate >>
  fs[GSYM LUPDATE_insert_commute,LUPDATE_commutes,insert_atI_app,
     insert_atI_NIL,insert_atI_CONS]);

val str_to_w8array_spec = Q.store_thm(
  "str_to_w8array_spec",
  `∀s sv a av.
     LENGTH (explode s) < LENGTH a ∧ STRING_TYPE s sv ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "IO.str_to_w8array" (basis_st())) [av; sv]
       (W8ARRAY av a)
       (POSTv v.
          cond (UNIT_TYPE () v) *
          W8ARRAY av (insert_atI (MAP (n2w o ORD) (explode s) ++ [0w]) 0 a))`,
  rpt strip_tac >> xcf "IO.str_to_w8array" (basis_st()) >>
  xlet_auto >- xsimpl >> xapp >> simp[]);

val openIn_spec = Q.store_thm(
  "openIn_spec",
  `∀s sv fs.
     FILENAME s sv ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 255 ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "IO.openIn" (basis_st()))
       [sv]
       (IOFS fs * IOFS_iobuff)
       (POST
          (\wv. &(WORD (n2w (nextFD fs) :word8) wv ∧
                  validFD (nextFD fs) (openFileFS s fs 0) ∧
                  inFS_fname fs s) *
                IOFS (openFileFS s fs 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s) * IOFS fs))`,
  xcf "IO.openIn" (basis_st()) >>
  fs[FILENAME_def, strlen_def, IOFS_def, IOFS_iobuff_def] >> 
  xpull >> rename [`W8ARRAY _ fnm0`] >>
  qmatch_goalsub_abbrev_tac`catfs fs` >>
  fs[iobuff_loc_def] >> xlet_auto
  >- (xsimpl >> Cases_on`s` \\ fs[]) >>
  qabbrev_tac `fnm = insert_atI (MAP (n2w o ORD) (explode s) ++ [0w]) 0 fnm0` >>
  qmatch_goalsub_abbrev_tac`catfs fs' * _` >>
  Cases_on `inFS_fname fs s`
  >- (xlet `POSTv u2.
            &(UNIT_TYPE () u2 /\ nextFD fs < 255 /\
              validFD (nextFD fs) (openFileFS s fs 0)) *
            W8ARRAY iobuff_loc (LUPDATE 0w 0 (LUPDATE (n2w (nextFD fs)) 1 fnm)) *
            catfs fs'`
    >- (simp[Abbr`catfs`,Abbr`fs'`] >>
        xffi >> simp[fsioProgTheory.iobuff_loc_def] >>
        simp[fsFFITheory.fs_ffi_part_def,IOx_def] >>
        qmatch_goalsub_abbrev_tac`IO st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`ns`,`f`,`encode (openFileFS s fs 0)`,`st`] 
        >> xsimpl >>
        simp[Abbr`f`,Abbr`st`,Abbr`ns`, mk_ffi_next_def,
             ffi_open_in_def, decode_encode_FS, Abbr`fnm`,
             getNullTermStr_insert_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
             implode_explode, LENGTH_explode] >>
        `∃content. ALOOKUP fs.files s = SOME content`
          by (fs[inFS_fname_def, ALOOKUP_EXISTS_IFF, MEM_MAP, EXISTS_PROD] >>
              metis_tac[]) >>
        csimp[nextFD_ltX, openFileFS_def, openFile_def, validFD_def]) >>
    xlet_auto
    >- (xsimpl >> csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insert_atI, LENGTH_explode]) >>
    fs[iobuff_loc_def] >> xlet_auto
    >- (xsimpl >> rw[Abbr`fnm`,LENGTH_insert_atI,LENGTH_explode,iobuff_loc,HD_LUPDATE]) >>
    xlet_auto >- (xsimpl) >> xif
    >-(xapp >> simp[fsioProgTheory.iobuff_loc_def] >> xsimpl >>
    fs[EL_LUPDATE,Abbr`fnm`,LENGTH_insert_atI,LENGTH_explode,wfFS_openFile,Abbr`fs'`]) >>
    xlet_auto >- (xcon >> xsimpl)
    >- (xraise >> xsimpl >>
        sg `0 < LENGTH (LUPDATE (n2w (nextFD fs)) 1 fnm)`
        >-(
	  fs[] >> fs[markerTheory.Abbrev_def] >> fs[] >>
	  `0 + LENGTH (MAP (n2w ∘ ORD) (explode s) ++ [0w]) <= LENGTH fnm0` 
        by (fs[LENGTH_explode]) >>
	  fs[LENGTH_insert_atI]) >>
        IMP_RES_TAC HD_LUPDATE >> fs[])) >>
  xlet `POSTv u2.
            &UNIT_TYPE () u2 * catfs fs *
            W8ARRAY iobuff_loc (LUPDATE 255w 0 fnm)`
  >- (simp[Abbr`catfs`,Abbr`fs'`] >> xffi >> simp[iobuff_loc_def] >>
      simp[fsFFITheory.fs_ffi_part_def,IOx_def] >>
      qmatch_goalsub_abbrev_tac`IO st f ns` >>
      CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`ns`,`f`,`st`,`st`] >> xsimpl >>
      simp[Abbr`f`,Abbr`st`,Abbr`ns`, mk_ffi_next_def,
	   ffi_open_in_def, decode_encode_FS, Abbr`fnm`,
	   getNullTermStr_insert_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
	   dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
	   implode_explode, LENGTH_explode] >>
      simp[not_inFS_fname_openFile]) >>      
  xlet_auto >-(xsimpl) >> fs[iobuff_loc] >> xlet_auto
  >- (xsimpl >> csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insert_atI, LENGTH_explode]) >>
  xlet_auto >-(xsimpl) >> xif
  >-(xapp >> xsimpl >> irule FALSITY >>
     sg `0 < LENGTH fnm`
     >-(fs[markerTheory.Abbrev_def] >>
        `0 + LENGTH (MAP (n2w ∘ ORD) (explode s) ++ [0w]) <= LENGTH fnm0` 
            by (fs[LENGTH_explode]) >>
        fs[LENGTH_insert_atI]) >>
     fs[HD_LUPDATE])>>
  xlet_auto >-(xcon >> xsimpl) >> xraise >> xsimpl >> simp[BadFileName_exn_def]);

(* openOut, openAppend here *)

val validFD_ALOOKUP = Q.store_thm("validFD_ALOOKUP",
  `validFD fd fs ==> ?v. ALOOKUP fs.infds fd = SOME v`,
  rw[validFD_def] >> cases_on`ALOOKUP fs.infds fd` >> fs[ALOOKUP_NONE]);

val close_spec = Q.store_thm(
  "close_spec",
  `∀(fdw:word8) fdv fs.
     WORD fdw fdv ⇒  
     app (p:'ffi ffi_proj) ^(fetch_v "IO.close" (basis_st())) [fdv]
       (IOFS fs * IOFS_iobuff)
       (POST (\u. &(UNIT_TYPE () u /\ validFD (w2n fdw) fs) *
                 IOFS (fs with infds updated_by A_DELKEY (w2n fdw)))
             (\e. &(InvalidFD_exn e /\ ¬ validFD (w2n fdw) fs) * IOFS fs))`,
  xcf "IO.close" (basis_st()) >> simp[IOFS_def, IOFS_iobuff_def] >> xpull >>
  rename [`W8ARRAY _ buf`] >> cases_on`buf` >> fs[] >>
  xlet_auto >- xsimpl >> fs[LUPDATE_def] >>
  xlet`POSTv uv. &(UNIT_TYPE () uv) *
        W8ARRAY iobuff_loc ((if validFD (w2n fdw) fs then 1w else 0w) ::t) *
        IOFS (if validFD (w2n fdw) fs then (fs with infds updated_by A_DELKEY (w2n fdw)) 
                                      else fs)`
  >-(xffi >> simp[iobuff_loc_def,IOFS_def,fsFFITheory.fs_ffi_part_def,IOx_def] >>
     qmatch_goalsub_abbrev_tac`IO st f ns` >> xsimpl >>
     qmatch_goalsub_abbrev_tac`wfFS fs' ∧ _` >>
     CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
     map_every qexists_tac[`ns`,`f`,`encode fs'`,`st`] >> xsimpl >>
     unabbrev_all_tac >> CASE_TAC >> rw[] >>
     fs[mk_ffi_next_def, ffi_close_def, decode_encode_FS,
        getNullTermStr_insert_atI, ORD_BOUND, ORD_eq_0,
        dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
        implode_explode, LENGTH_explode,closeFD_def,LUPDATE_def] 
      >-(imp_res_tac validFD_ALOOKUP >> cases_on`fs` >> fs[IO_fs_infds_fupd])
      >-(fs[validFD_def] >> imp_res_tac ALOOKUP_NONE >> fs[])) >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  CASE_TAC >> xif >> instantiate
  >-(xcon >> fs[IOFS_def] >> xsimpl) >>
  xlet_auto >-(xcon >> xsimpl) >>
  xraise >> fs[InvalidFD_exn_def,IOFS_def] >> xsimpl);
      
val writei_spec = Q.store_thm("writei_spec",
 `liveFS fs ⇒ wfFS fs ⇒ validFD (w2n fd) fs ⇒ 0 < n ⇒
  w2n fd < 255 ⇒ LENGTH rest = 255 ⇒ i + n <= 255 ⇒
  get_file_content fs (w2n fd) = SOME(content, pos) ⇒
  WORD (fd:word8) fdv ⇒ WORD (n2w n:word8) nv ⇒ WORD (n2w i:word8) iv ⇒
  bc = h1 :: h2 :: h3 :: rest ⇒ 
  app (p:'ffi ffi_proj) ^(fetch_v "IO.writei" (basis_st())) [fdv;nv;iv]
  (IOFS fs * W8ARRAY iobuff_loc bc) 
  (POST
    (\nwv. SEP_EXISTS nw. &(NUM nw nwv) * &(nw > 0) * &(nw <= n) *
           W8ARRAY iobuff_loc (0w :: n2w nw :: n2w i :: rest) *
           IOFS(fsupdate fs (w2n fd) (1 + Lnext_pos fs.numchars) (pos + nw)
                         (insert_atI (TAKE nw (MAP (CHR o w2n) (DROP i rest))) pos
                                    content)))
    (\e. &(InvalidFD_exn e) * W8ARRAY iobuff_loc (1w:: n2w n::rest) * &(F) *
         IOFS (fs with numchars:= THE(LDROP (1 + Lnext_pos fs.numchars) fs.numchars))))`,
  strip_tac >> fs[liveFS_def] >> `?ll. fs.numchars = ll` by simp[]  >> fs[] >>
  `liveFS fs` by fs[liveFS_def] >> FIRST_X_ASSUM MP_TAC >> FIRST_X_ASSUM MP_TAC >> 
  qid_spec_tac `bc`>> qid_spec_tac `h3` >>  qid_spec_tac `h2` >> qid_spec_tac `h1` >> 
  qid_spec_tac `fs` >> FIRST_X_ASSUM MP_TAC >> qid_spec_tac `ll` >> 
  HO_MATCH_MP_TAC always_eventually_ind >>
  xcf "IO.writei" (basis_st()) >> fs[iobuff_loc_def]>>
  `ll = fs.numchars` by simp[] >> fs[]
(* next el is <> 0 *)
  >-(sg`Lnext_pos fs.numchars = 0`   
     >-(fs[Lnext_pos_def,Once Lnext_def,liveFS_def,always_thm] >>
        cases_on`fs.numchars` >> fs[]) >>
     NTAC 3 (xlet_auto >-(simp[LUPDATE_def] >> xsimpl)) >>
     xlet`POSTv uv. &(UNIT_TYPE () uv) *
            W8ARRAY iobuff_loc (0w:: n2w (MIN n k) :: n2w i :: rest) *
            IOFS (fsupdate fs (w2n fd) 1 (MIN n k + pos)
                          (TAKE pos content ++ 
                           TAKE (MIN n k) (MAP (CHR o w2n) (DROP i rest)) ++ 
                           DROP (MIN n k + pos) content))`
     >-(qmatch_goalsub_abbrev_tac` _ * _ * IOFS fs'` >>
        xffi >> xsimpl >>
        fs[iobuff_loc,IOFS_def,IOx_def,fs_ffi_part_def,
               mk_ffi_next_def] >>
        qmatch_goalsub_abbrev_tac`IO st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`ns`,`f`,`encode fs'`,`st`] >>
        xsimpl >>
        fs[Abbr`f`,Abbr`st`,Abbr`ns`,mk_ffi_next_def,
           ffi_write_def,decode_encode_FS,MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
           dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
           HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,write_def,
           get_file_content_def] >>
        pairarg_tac >> xsimpl >>
        `MEM (w2n fd) (MAP FST fs.infds)` by (metis_tac[MEM_MAP]) >>
        rw[] >> TRY(metis_tac[wfFS_fsupdate]) >>
        EVAL_TAC >>
        qmatch_goalsub_abbrev_tac`_ /\ _ = SOME(xx, _ yy)` >>
        qexists_tac`(xx,yy)` >> xsimpl >> fs[Abbr`xx`,Abbr`yy`] >>
        qexists_tac`(MIN n k, fs')` >> xsimpl >>
        qexists_tac`(fnm, off)` >> fs[] >> rfs[] >>
        cases_on`fs.numchars` >> fs[Abbr`fs'`,fsupdate_def]) >>
     qmatch_goalsub_abbrev_tac` _ * IOFS fs'` >>
     qmatch_goalsub_abbrev_tac`W8ARRAY _ (_::m:: n2w i :: rest)` >>
     fs[iobuff_loc_def] >>
     NTAC 3 (xlet_auto >- xsimpl) >>
     xif >> fs[FALSE_def] >> instantiate >>
     NTAC 3 (xlet_auto >- xsimpl) >>
     xif >> fs[FALSE_def] >> instantiate >> xvar >> xsimpl >>
     instantiate >> fs[Abbr`fs'`,MIN_DEF,insert_atI_def] >> xsimpl) >>
 (* next element is 0 *)
  cases_on`fs.numchars` >- fs[liveFS_def] >> fs[] >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  xlet`POSTv uv. &(UNIT_TYPE () uv) * W8ARRAY iobuff_loc (0w:: 0w :: n2w i :: rest) *
        IOFS (fsupdate fs (w2n fd) 1 pos
                          (TAKE pos content ++ 
                           TAKE 0 (MAP (CHR o w2n) (DROP i rest)) ++ 
                           DROP pos content))`
  >-(qmatch_goalsub_abbrev_tac` _ * _ * IOFS fs'` >>
    xffi >> xsimpl >>
    fs[iobuff_loc,IOFS_def,IOx_def,fs_ffi_part_def,
           mk_ffi_next_def] >>
    qmatch_goalsub_abbrev_tac`IO st f ns` >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`ns`,`f`,`encode fs'`,`st`] >>
    xsimpl >>
    fs[Abbr`f`,Abbr`st`,Abbr`ns`,mk_ffi_next_def,
       ffi_write_def,decode_encode_FS,MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
       dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
       HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,write_def,
       get_file_content_def] >>
    pairarg_tac >> xsimpl >>
    `MEM (w2n fd) (MAP FST fs.infds)` by (metis_tac[MEM_MAP]) >>
    rw[] >> TRY(metis_tac[wfFS_fsupdate]) >>
    EVAL_TAC >>
    qexists_tac`(0w::0w::n2w i::rest,fs')` >> fs[] >>
    qexists_tac`(0, fs')` >> fs[Abbr`fs'`,fsupdate_def] >>
    qexists_tac`(fnm, off)` >> fs[] >> rfs[]) >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  xif >> fs[FALSE_def] >> instantiate >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  xif >> fs[TRUE_def] >> instantiate >>
  qmatch_goalsub_abbrev_tac` _ * IOFS fs'` >>
  xapp >> xsimpl >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  qexists_tac`fs'` >> xsimpl >>
  (* hypotheses for induction call *)
  sg`t = fs'.numchars` >-(fs[Abbr`fs'`,fsupdate_def,LDROP_1]) >> 
  sg`fs' = fs with numchars := t`
  >-(imp_res_tac validFD_ALOOKUP >> fs[wfFS_def,Abbr`fs'`,fsupdate_def] >>
     fs[IO_fs_component_equality] >> fs[wfFS_def,get_file_content_def] >>
     pairarg_tac >> fs[ALIST_FUPDKEY_unchanged,LDROP_1]) >>
  fs[Abbr`fs'`,get_file_content_def,liveFS_def,fsupdate_def,LDROP_1,
     wfFS_fsupdate,validFD_def] >>
  pairarg_tac >> fs[ALIST_FUPDKEY_unchanged] >>
  rw[] >> instantiate >>
  `Lnext_pos (0:::t) = SUC(Lnext_pos t)` by 
    (fs[Lnext_pos_def,Once Lnext_def,liveFS_def]) >>
  fs[ADD] >> xsimpl);

val insert_atI_insert_atI = Q.store_thm("insert_atI_insert_atI",
  `pos2 = pos1 + LENGTH c1 ==>
    insert_atI c2 pos2 (insert_atI c1 pos1 l) = insert_atI (c1 ++ c2) pos1 l`,
    rw[insert_atI_def,TAKE_SUM,TAKE_APPEND,LENGTH_TAKE_EQ,LENGTH_DROP,
       GSYM DROP_DROP_T,DROP_LENGTH_TOO_LONG,DROP_LENGTH_NIL_rwt]
    >> fs[DROP_LENGTH_NIL_rwt,LENGTH_TAKE,DROP_APPEND1,TAKE_APPEND,TAKE_TAKE,
       DROP_DROP_T,DROP_APPEND2,TAKE_LENGTH_TOO_LONG,TAKE_SUM,LENGTH_DROP]);

val write_spec = Q.store_thm("write_spec",
 `!n fs i pos h1 h2 h3 rest bc fdv nv iv fd content.
  liveFS fs ⇒ wfFS fs ⇒ validFD (w2n fd) fs ⇒
  w2n fd < 255 ⇒ LENGTH rest = 255 ⇒ i + n <= 255 ⇒
  get_file_content fs (w2n fd) = SOME(content, pos) ⇒
  WORD (fd:word8) fdv ⇒ NUM n nv ⇒ NUM i iv ⇒
  bc = h1 :: h2 :: h3 :: rest ⇒ 
  app (p:'ffi ffi_proj) ^(fetch_v "IO.write" (basis_st())) [fdv;nv;iv]
  (IOFS fs * W8ARRAY iobuff_loc bc) 
  (POSTv nwv. SEP_EXISTS k. IOFS_iobuff *
     IOFS(fsupdate fs (w2n fd) k (pos + n)
                   (insert_atI (TAKE n (MAP (CHR o w2n) (DROP i rest))) pos
                                    content)))`,
  strip_tac >>
  `?N. n <= N` by (qexists_tac`n` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`n` >>
  Induct_on`N` >>
  xcf "IO.write" (basis_st())
  >>(xlet_auto >- xsimpl >> xif
	 >-(TRY instantiate >> xcon >>
		simp[IOFS_iobuff_def] >> xsimpl >> qexists_tac`0` >>
	    fs[fsupdate_unchanged,insert_atI_def] >> xsimpl)) >>
  NTAC 2 (xlet_auto >- xsimpl) >>
  PURE_REWRITE_TAC[GSYM iobuff_loc_def] >>
  xlet_auto >> xsimpl
  >-(simp[iobuff_loc_def] >> xsimpl >> rw[] >> instantiate >> xsimpl) >> 
  xlet_auto >- xsimpl >> reverse xif
  >-(xcon >> xsimpl >> fs[IOFS_iobuff_def] >> xsimpl >>
	 qexists_tac`(Lnext_pos fs.numchars + 1)` >> `nw = n` by fs[] >> xsimpl) >>
  NTAC 2 (xlet_auto >- xsimpl) >>
  qmatch_goalsub_abbrev_tac`IOFS fs'` >>
  `n - nw<= N` by fs[] >>
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPECL[`n-nw`]) >> rfs[] >>
  FIRST_X_ASSUM(ASSUME_TAC o Q.SPECL[`fs'`,`nw + i`,`pos+nw`]) >>
  FIRST_X_ASSUM xapp_spec >> xsimpl >> instantiate >>
  qexists_tac`insert_atI (TAKE nw (MAP (CHR ∘ w2n) (DROP i rest))) pos content` >>
  NTAC 4 (strip_tac >-(
		  fs[Abbr`fs'`,liveFS_def,LDROP_1, wfFS_fsupdate,validFD_def,
			 always_DROP,ALIST_FUPDKEY_ALOOKUP,get_file_content_def,wfFS_fsupdate] >>
		  pairarg_tac >> fs[fsupdate_def,always_DROP,ALIST_FUPDKEY_ALOOKUP])) >>
  rw[] >> qexists_tac`Lnext_pos fs.numchars + 1 + x` >> 
  fs[fsupdate_o,Abbr`fs'`,insert_atI_insert_atI] >>
  qmatch_abbrev_tac`_ (_ _ _ _ _ (_ c1 _ _)) ==>> _ (_ _ _ _ _ (_ c2 _ _)) * _` >>
  `c1 = c2` suffices_by xsimpl >> fs[Abbr`c1`,Abbr`c2`] >>
  PURE_REWRITE_TAC[Once (Q.SPECL [`i`,`nw`] ADD_COMM)] >>
  fs[Once ADD_COMM,GSYM DROP_DROP_T,take_drop_partition,MAP_DROP]);

val write_char_spec = Q.store_thm("write_char_spec",
  `!(fd :word8) fdv c cv bc content pos.
    liveFS fs ⇒ wfFS fs ⇒
    validFD (w2n fd) fs ⇒ w2n fd < 255 ⇒
    get_file_content fs (w2n fd) = SOME(content, pos) ⇒
    CHAR c cv ⇒ WORD fd fdv ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "IO.write_char" (basis_st())) [fdv; cv]
    (IOFS fs * IOFS_iobuff) 
    (POSTv uv. 
      &UNIT_TYPE () uv * IOFS_iobuff * SEP_EXISTS k.
      IOFS (fsupdate fs (w2n fd) k (pos+1) (insert_atI [c] pos content)))`,
  xcf "IO.write_char" (basis_st()) >> fs[IOFS_iobuff_def] >> 
  xpull >> rename [`W8ARRAY _ bdef`] >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: t'` >>
  Cases_on `t'` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: h3 :: rest'` >>
  Cases_on `rest'` >> fs[] >> qmatch_goalsub_abbrev_tac`h1::h2::h3::h4::rest` >>
  simp[EVAL ``LUPDATE rr 2 (zz :: tt)``, EVAL ``LUPDATE rr 1 (zz :: tt)``,
       EVAL ``LUPDATE rr 3 (uu :: zz :: tt)``, LUPDATE_def] >>
  PURE_REWRITE_TAC[GSYM iobuff_loc_def] >>
  xlet_auto
  >-(PURE_REWRITE_TAC[GSYM iobuff_loc_def] >> xsimpl >> 
     rw[] >> qexists_tac`x` >> xsimpl) >>
     (* instantiate fails here *)
  xcon >> fs[IOFS_iobuff_def] >> xsimpl >> rw[] >>
  fs[CHR_ORD,LESS_MOD,ORD_BOUND] >> qexists_tac`k` >> xsimpl);

val output_spec = Q.store_thm("output_spec",
  `!s (fd :word8) fdv sv fs content pos. 
    WORD fd fdv ⇒ validFD (w2n fd) fs ⇒ 
    STRING_TYPE s sv ⇒
    liveFS fs ⇒ w2n fd < 255 ⇒  wfFS fs ⇒
    (get_file_content fs (w2n fd) = SOME(content, pos)) ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "IO.output" (basis_st())) [fdv; sv]
    (IOFS fs * IOFS_iobuff)  
    (POSTv uv. &(UNIT_TYPE () uv) * IOFS_iobuff * 
       SEP_EXISTS k. IOFS (fsupdate fs (w2n fd) k (pos + (strlen s))
                                    (insert_atI (explode s) pos content)))`,
  strip_tac >>
  `?n. strlen s <= n` by (qexists_tac`strlen s` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`s` >>
  Induct_on`n` >>
  xcf "IO.output" (basis_st()) >> fs[IOFS_iobuff_def] >>
  xpull >> rename [`W8ARRAY _ buff`] >>
  Cases_on `buff` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: rest'` >>
  Cases_on `rest'` >> fs[] >> qmatch_goalsub_abbrev_tac`h1::h2::h3::rest` >>
  (xlet_auto >- xsimpl) >>
  (xif >-(xcon >> xsimpl >> qexists_tac`0` >>
         fs[fsupdate_unchanged,insert_atI_NIL] >> xsimpl))
  >-(cases_on`s` >> fs[strlen_def]) >>
  fs[insert_atI_def] >>
  sg`STRLEN (explode (substring s 0 255)) + 3 ≤ 258`
  >- (fs[LENGTH_explode,substring_def] >> CASE_TAC >>
      fs[substring_def,LENGTH_extract_aux,MIN_DEF]) >>
  NTAC 4 (xlet_auto >- xsimpl) >>
  fs[insert_atI_def] >> PURE_REWRITE_TAC[GSYM iobuff_loc_def] >>
  xlet_auto >> xsimpl
  >-(PURE_REWRITE_TAC[GSYM iobuff_loc_def] >> xsimpl >>
     rw[] >> cases_on`s` >> cases_on`s'` >>
     fs[substring_def,LENGTH_extract_aux,implode_def,strlen_def,MIN_DEF] >>
     qexists_tac`x` >> xsimpl) >> 
     (* instantiate fails here *)
  xlet_auto >-(xcon >> xsimpl) >>
  sg`OPTION_TYPE NUM NONE (Conv (SOME ("NONE",TypeId (Short "option"))) [])`
  >- fs[OPTION_TYPE_def] >>
  xlet_auto >- xsimpl >>
  qmatch_goalsub_abbrev_tac`fsupdate fs _ _ pos' content'` >>
  qmatch_goalsub_abbrev_tac`IOFS fs'` >>
  xapp >> fs[IOFS_iobuff_def] >> xsimpl >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac [`content'`,`fd`,`fs'`,`pos'`] >>
  instantiate >> xsimpl >>
  `strlen s <> 0` by (cases_on`s` >> cases_on`s'` >> fs[])>>
  fs[get_file_content_def] >> pairarg_tac >> rw[] >>
  fs[Abbr`fs'`,Abbr`pos'`,Abbr`content'`,liveFS_def,
     fsupdate_def,LDROP_1, wfFS_fsupdate,validFD_def,always_DROP,
     LENGTH_extract_aux,ALIST_FUPDKEY_ALOOKUP,extract_def,strlen_extract_le,
     substring_def,LENGTH_extract_aux,MIN_DEF] >> xsimpl
  >-(CASE_TAC >> CASE_TAC >> fs[implode_def,LENGTH_extract_aux]) >>
  qexists_tac`x' + k` >> fs[insert_atI_def] >>
  qmatch_abbrev_tac`IOFS fs1 ==>> IOFS fs2 * GC` >>
  `fs1 = fs2` suffices_by xsimpl >> fs[Abbr`fs1`,Abbr`fs2`] >>
  cases_on`s` >>
  rw[] >> fs[ALIST_FUPDKEY_o,LENGTH_extract_aux,MAP_MAP_o,CHR_w2n_n2w_ORD,
             LENGTH_explode,LENGTH_TAKE_EQ, LENGTH_extract_aux,strlen_def,
             TAKE_APPEND,TAKE_LENGTH_TOO_LONG,extract_aux_eq,extract_aux_DROP] >> 
  TRY(MATCH_MP_TAC ALIST_FUPDKEY_eq >> fs[LENGTH_TAKE]) 
  >-(`STRLEN s' = 255` by fs[] >> fs[DROP_LENGTH_TOO_LONG])
  >-(`255 <= STRLEN s'` by fs[] >> fs[extract_aux_TAKE] >>
     fs[DROP_LENGTH_TOO_LONG,LENGTH_TAKE_EQ,LENGTH_extract_aux,LENGTH_APPEND] >>
     CASE_TAC >> fs[DROP_APPEND,DROP_LENGTH_TOO_LONG,DROP_DROP_T,LENGTH_TAKE_EQ])
  >-(fs[LDROP_ADD] >> CASE_TAC >> fs[] >>
     sg`?v. LDROP k fs.numchars = SOME v`
     >-(imp_res_tac always_NOT_LFINITE >>
        fs[LFINITE_DROP,NOT_LFINITE_DROP,always_NOT_LFINITE]) >>
     fs[]));

val read_spec = Q.store_thm("read_spec",
  `validFD (w2n fd) fs ⇒ w2n fd < 255 ⇒
   WORD (fd:word8) fdv ⇒ WORD (n:word8) nv ⇒ 
   LENGTH rest = 256 ⇒  w2n n <= 255 ⇒ 
   wfFS fs ⇒  get_file_content fs (w2n fd) = SOME(content, pos) ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "IO.read" (basis_st())) [fdv;nv]
   (W8ARRAY iobuff_loc (h1 :: h2 :: rest) * IOFS fs)
   (POSTv uv. 
      &(UNIT_TYPE () uv) * 
      SEP_EXISTS nr. &(nr <= MIN (w2n n) (LENGTH content - pos) /\
                      (nr = 0 ⇔ eof (w2n fd) fs = SOME T ∨ w2n n = 0)) * 
      IOFS (bumpFD (w2n fd) fs nr) *
      W8ARRAY iobuff_loc (0w :: n2w nr :: 
        MAP (n2w o ORD) (TAKE nr (DROP pos content))++DROP nr rest))`,
   xcf "IO.read" (basis_st()) >> 
   NTAC 2 (xlet_auto >- (fs[LUPDATE_def] >> xsimpl)) >>
   simp[LUPDATE_def,EVAL ``LUPDATE rr 1 (zz :: tt)``] >>
   xffi >> xsimpl >>
   fs[iobuff_loc,IOFS_def,IOx_def,fs_ffi_part_def, mk_ffi_next_def] >>
   qmatch_goalsub_abbrev_tac`IO st f ns` >>
   CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
   map_every qexists_tac[`ns`,`f`] >>
   xsimpl >>
   fs[Abbr`f`,Abbr`st`,Abbr`ns`,mk_ffi_next_def,
      ffi_read_def,decode_encode_FS,MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
      dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
      HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,read_def,
      get_file_content_def] >>
   pairarg_tac >> xsimpl >> fs[] >>
   cases_on`fs.numchars` >> fs[wfFS_def] >>
   qmatch_goalsub_abbrev_tac`k = _ MOD 256` >> qexists_tac`k` >>
   fs[MIN_LE,eof_def,Abbr`k`] >> rfs[] >> metis_tac[]);



val read_char_spec = Q.store_thm("read_char_spec",
  `!(fd :word8) fdv content pos.
    WORD fd fdv ⇒ validFD (w2n fd) fs ⇒ w2n fd < 255 ⇒
    wfFS fs ⇒  get_file_content fs (w2n fd) = SOME(content, pos) ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "IO.read_char" (basis_st())) [fdv]
    (IOFS fs * IOFS_iobuff) 
    (POST (\cv. &(WORD (n2w (ORD (EL pos content)):word8) cv /\
                eof (w2n fd) fs = SOME F) *
                IOFS_iobuff * IOFS (bumpFD (w2n fd) fs 1))
          (\e.  &(EndOfFile_exn e /\ eof (w2n fd) fs = SOME T) *
                IOFS_iobuff * IOFS(bumpFD (w2n fd) fs 0)))`,
  xcf "IO.read_char" (basis_st()) >> fs[IOFS_iobuff_def] >> 
  xpull >> rename [`W8ARRAY _ bdef`] >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: t'` >>
  Cases_on `t'` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: h3 :: rest` >>
  xlet_auto >- xsimpl >>
  PURE_REWRITE_TAC[GSYM iobuff_loc_def] >>
  xlet_auto >-(fs[iobuff_loc_def] >> xsimpl >> rw[] >> instantiate >> xsimpl)>>
  NTAC 3 (xlet_auto >- xsimpl) >>
  xif >> instantiate >>
  NTAC 3 (xlet_auto >- xsimpl) >>
  xif >-(xlet_auto >- (xcon >> xsimpl) >> xraise >> 
         fs[EndOfFile_exn_def,eof_def,get_file_content_def] >> xsimpl) >>
  xapp >> xsimpl >>
  `nr = 1` by fs[] >> fs[] >> xsimpl >> 
  fs[take1_drop,eof_def,get_file_content_def] >> pairarg_tac >> fs[]);

(* Standard IO *)

(* standatd nput has file descriptor 0 *)
val STDIN_def = Define`
    STDIN input = IOFS_iobuff * SEP_EXISTS fs pos. IOFS fs * &liveFS fs *
      &(get_file_content fs 0 = SOME(input, pos))` 

(* standatd output has file descriptor 1 and the position is at the end *)
val STDOUT_def = Define`
    STDOUT output = IOFS_iobuff * SEP_EXISTS fs. IOFS fs * &liveFS fs *
      &(get_file_content fs 1 = SOME(output,LENGTH output))` 

(* standatd error has file descriptor 2 and the position is at the end *)
val STDERR_def = Define`
    STDERR output = IOFS_iobuff * SEP_EXISTS fs. IOFS fs * &liveFS fs *
      &(get_file_content fs 2 = SOME(output,LENGTH output))` 

val encode_fds_11 = Q.store_thm("encode_fds_11",
  `encode_fds l1 = encode_fds l2 ⇒ l1 = l2`,
  rw[] >> `decode_fds (encode_fds l1) = decode_fds(encode_fds l2)` by fs[] >>
  fs[decode_encode_fds]);

val encode_files_11 = Q.store_thm("encode_files_11",
  `encode_files l1 = encode_files l2 ⇒ l1 = l2`,
  rw[] >> 
  `decode_files (encode_files l1) = decode_files(encode_files l2)` by fs[] >>
  fs[decode_encode_files]);

val UNIQUE_IOFS = Q.store_thm("UNIQUE_IOFS",
`!s. VALID_HEAP s ==> !fs1 fs2 H1 H2. (IOFS fs1 * H1) s /\
                                      (IOFS fs2 * H2) s ==> fs1 = fs2`,
  rw[IOFS_def,IOFS_def,cfHeapsBaseTheory.IOx_def, fs_ffi_part_def,
     GSYM STAR_ASSOC,encode_def] >>
  IMP_RES_TAC FRAME_UNIQUE_IO >> 
  fs[encode_files_11,encode_fds_11,IO_fs_component_equality]);

val STDIN_FFI_part_hprop = Q.store_thm("STDIN_FFI_part_hprop",
  `FFI_part_hprop (STDIN x)`,
  rw [STDIN_def,IOFS_def,
      cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
      fs_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    cfHeapsBaseTheory.W8ARRAY_def,IOFS_iobuff_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR,STAR_def]
  \\ imp_res_tac SPLIT_SUBSET >> fs[SUBSET_DEF]
  \\ metis_tac[]);

val STDOUT_FFI_part_hprop = Q.store_thm("STDOUT_FFI_part_hprop",
  `FFI_part_hprop (STDOUT x)`,
  rw [STDOUT_def,IOFS_def,
      cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
      fs_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    cfHeapsBaseTheory.W8ARRAY_def,IOFS_iobuff_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR,STAR_def]
  \\ imp_res_tac SPLIT_SUBSET >> fs[SUBSET_DEF]
  \\ metis_tac[]);
  
val STDERR_FFI_part_hprop = Q.store_thm("STDERR_FFI_part_hprop",
  `FFI_part_hprop (STDERR x)`,
  rw [STDERR_def,IOFS_def,
      cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
      fs_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    cfHeapsBaseTheory.W8ARRAY_def,IOFS_iobuff_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR,STAR_def]
  \\ imp_res_tac SPLIT_SUBSET >> fs[SUBSET_DEF]
  \\ metis_tac[]);
open mllistProgTheory

(* `(UNIT_TYPE --> WORD) (\u. 0w) (^(fetch_v "IO.stdin" (basis_st())))` *)

val stdin_spec = Q.store_thm("stdin_spec",
  `UNIT_TYPE () uv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "IO.stdin" (basis_st())) [uv]
   (emp) (POSTv v. &WORD (0w:word8) v)`,
  xcf "IO.stdin" (basis_st()) >> xmatch >> fs[UNIT_TYPE_def] >>
  rw[] >-(xapp >> xsimpl) >> EVAL_TAC);

val stdout_spec = Q.store_thm("stdout_spec",
  `UNIT_TYPE () uv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "IO.stdout" (basis_st())) [uv]
   (emp) (POSTv v. &WORD (1w:word8) v)`,
  xcf "IO.stdout" (basis_st()) >> xmatch >> fs[UNIT_TYPE_def] >>
  rw[] >-(xapp >> xsimpl) >> EVAL_TAC);

val stderr_spec = Q.store_thm("stderr_spec",
  `UNIT_TYPE () uv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "IO.stderr" (basis_st())) [uv]
   (emp) (POSTv v. &WORD (2w:word8) v)`,
  xcf "IO.stderr" (basis_st()) >> xmatch >> fs[UNIT_TYPE_def] >>
  rw[] >-(xapp >> xsimpl) >> EVAL_TAC);

(* use earlier *)
val get_file_content_validFD = Q.store_thm("get_file_content_validFD",
  `get_file_content fs fd = SOME(c,p) ⇒ validFD fd fs`,
  fs[get_file_content_def,validFD_def] >> rw[] >> pairarg_tac >>
  imp_res_tac ALOOKUP_MEM >> fs[ALOOKUP_MEM,MEM_MAP] >> instantiate);

val liveFS_fsupdate = Q.store_thm("liveFS_fsupdate",
  `liveFS fs ⇒ liveFS (fsupdate fs fd k i c)`,
  fs[liveFS_def,fsupdate_def,always_DROP]);

val get_file_content_fsupdate = Q.store_thm("get_file_content_fsupdate",
  `get_file_content fs fd = SOME u ⇒
  get_file_content (fsupdate fs fd x i c) fd = SOME(c,i)`,
  rw[get_file_content_def, fsupdate_def] >>
  pairarg_tac >> fs[ALIST_FUPDKEY_ALOOKUP]);

val get_file_content_fsupdate_unchanged = Q.store_thm(
  "get_file_content_fsupdate_unchanged",
  `get_file_content fs fd = SOME u ⇒ 
   ALOOKUP fs.infds fd = SOME (fnm,pos) ⇒ 
   ALOOKUP fs.infds fd' = SOME (fnm',pos') ⇒ fnm ≠ fnm' ⇒
  get_file_content (fsupdate fs fd' x i c) fd = SOME u`,
  rw[get_file_content_def, fsupdate_def] >>
  pairarg_tac >> fs[ALIST_FUPDKEY_ALOOKUP] >>
  rpt(CASE_TAC >> fs[]));

val insert_atI_end = Q.store_thm("insert_atI_end",
  `insert_atI l1 (LENGTH l2) l2 = l2 ++ l1`,
  simp[insert_atI_def,DROP_LENGTH_TOO_LONG]);

val print_spec = Q.store_thm("print_spec",
  `!s sv fs output. 
    STRING_TYPE s sv ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "IO.print" (basis_st())) [sv]
    (STDOUT output)  
    (POSTv uv. &(UNIT_TYPE () uv) * STDOUT (STRCAT output (explode s)))`,
  xcf "IO.print" (basis_st()) >> fs[STDOUT_def,IOFS_def] >> xpull >>
  xlet_auto >-(xcon >> xsimpl) >> xlet_auto >- xsimpl >>
  xapp >> fs[get_file_content_validFD,IOFS_def] >> xsimpl >> instantiate >>
  fs[get_file_content_validFD,IOFS_def] >> xsimpl >> rw[] >> instantiate >>
  fs[wfFS_fsupdate,liveFS_fsupdate,get_file_content_fsupdate,insert_atI_end,
     LENGTH_explode] >> xsimpl);

open mlcommandLineProgTheory
(*---------------------------------------------------------------------------*)
(* GENERALISED FFI *)

val basis_ffi_oracle_def = Define `
  basis_ffi_oracle =
    \name (cls,fs) bytes.
     if name = "write" then
       case ffi_write bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "read" then
       case ffi_read bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "getArgs" then
       case ffi_getArgs bytes cls of
       | SOME (bytes,cls) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "open_in" then
       case ffi_open_in bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "open_out" then
       case ffi_open_out bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     if name = "close" then
       case ffi_close bytes fs of
       | SOME (bytes,fs) => Oracle_return (cls,fs) bytes
       | _ => Oracle_fail else
     Oracle_fail`

(* standard streams are initialized *)
val basis_ffi_def = Define `
  basis_ffi (inp: string) (cls: string list) files numchars =
    <| oracle := basis_ffi_oracle
     ; ffi_state := (cls,
        (<| files := ((strlit "stdin",inp)::(strlit "stdout","")::(strlit "stderr","")::files);
            infds := [(0,strlit "stdin",0);(1,strlit "stdout",0);(2,strlit "stderr",0)];
            numchars := numchars |> : IO_fs))
     ; final_event := NONE
     ; io_events := [] |>`;

val basis_proj1_def = Define `
  basis_proj1 = (\(cls, fs).
    FEMPTY |++ ((mk_proj1 commandLine_ffi_part cls) ++ (mk_proj1 fs_ffi_part fs)))`;

val basis_proj2_def = Define `
  basis_proj2 =
    [mk_proj2 commandLine_ffi_part;
     mk_proj2 fs_ffi_part]`;

(* TODO useful? *)
val basis_proj1_read = Q.store_thm("basis_proj1_read",
  `basis_proj1 ffi ' "read" = encode (SND ffi)`,
  PairCases_on`ffi` \\ EVAL_TAC);

val basis_proj1_write = Q.store_thm("basis_proj1_write",
  `basis_proj1 ffi ' "write" = encode(SND ffi)`,
  PairCases_on`ffi` \\ EVAL_TAC);

(* extracts the list of file descriptors linked to a given file name *)
val extract_fds_def = Define`
 (extract_fds fname [] = if fname = "stdin" then [0w] else
                         if fname = "stdout" then [1w] else
                         if fname = "stderr" then [2w] else []) ∧
 (extract_fds fname ((IO_event name bytes)::xs) =
 if name = "open" ∧  getNullTermStr (MAP FST bytes) = SOME fname
 then SND(HD(TL bytes)) :: extract_fds fname xs else
 if name = "close" then FILTER (\fd. fd <> FST(HD bytes)) (extract_fds fname xs)
 else extract_fds fname xs)`;

 (* TODO: ghere  *)

val extract_file_def = Define `
  (extract_file fname [] = SOME "") ∧ 
  (extract_file fname ((IO_event name bytes)::xs) =
     case extract_file fname xs of
     | NONE => NONE
     | SOME rest => 
         if name ≠ "write" ∨ ¬ MEM (FST(HD bytes)) (extract_fds fname xs)
         then SOME rest else
         if LENGTH bytes <> 258 then NONE else
         if SND(HD bytes) = 0w then SOME rest else
           let nw = w2n(SND(HD(TL bytes))) in
           let i = w2n(FST(HD(TL(TL bytes)))) in
           SOME(MAP (CHR o w2n o SND) (TAKE nw (DROP (3 + i) bytes)) ++ rest))`

val extract_file_APPEND = Q.store_thm("extract_output_APPEND",
  `!xs ys.
      extract_file fname (xs ++ ys) =
      case extract_file fname ys of
      | NONE => NONE
      | SOME rest => case extract_file fname xs of
                     | NONE => NONE
                     | SOME front => SOME (front ++ rest)`,
  Induct \\ fs [APPEND,extract_file_def] \\ rw []
  THEN1 (every_case_tac \\ fs [])
  \\ Cases_on `h` \\ fs [extract_file_def,MEM_APPEND]
  cheat
  \\ rpt (CASE_TAC \\ fs []));

val extract_err_APPEND = Q.store_thm("extract_err_APPEND",
  `!xs ys.
      extract_err (xs ++ ys) =
      case extract_err ys of
      | NONE => NONE
      | SOME rest => case extract_err xs of
                     | NONE => NONE
                     | SOME front => SOME (front ++ rest)`,
  Induct \\ fs [APPEND,extract_err_def] \\ rw []
  THEN1 (every_case_tac \\ fs [])
  \\ Cases_on `h` \\ fs [extract_err_def]
  \\ rpt (CASE_TAC \\ fs []));
(*-------------------------------------------------------------------------------------------------*)

(*The following thms are used to automate the proof of the SPLIT of the heap in ioProgLib*)
val append_hprop = Q.store_thm ("append_hprop",
  `A s1 /\ B s2 ==> DISJOINT s1 s2 ==> (A * B) (s1 ∪ s2)`,
  rw[set_sepTheory.STAR_def] \\ SPLIT_TAC
);

val SPLIT_exists = Q.store_thm ("SPLIT_exists",
  `(A * B) s /\ s ⊆ C
    ==> (?h1 h2. SPLIT C (h1, h2) /\ (A * B) h1)`,
  rw[]
  \\ qexists_tac `s` \\ qexists_tac `C DIFF s`
  \\ SPLIT_TAC
);

val append_emp_err = Q.store_thm("append_emp_err",
  `app (p:'ffi ffi_proj) fv xs P (POSTv uv. (A uv) * STDOUT x * STDERR y)
    ==> app p fv xs P (POSTv uv. (A uv) * STDOUT x * STDERR y * emp)`,
  rw[set_sepTheory.SEP_CLAUSES]);

val append_emp_out = Q.store_thm("append_emp_out",
   `app (p:'ffi ffi_proj) fv xs P (POSTv uv. (A uv) * STDOUT x)
    ==> app p fv xs P (POSTv uv. (A uv) * STDOUT x * emp)`,
  rw[set_sepTheory.SEP_CLAUSES]);

val append_STDERR = Q.store_thm("append_STDERR",
  `app (p:'ffi ffi_proj) fv xs P (POSTv uv. (A uv) * STDOUT x * P')
  ==> app p fv xs (P * STDERR y) (POSTv uv. (A uv) * STDOUT x * STDERR y * P')`,
  rw[]
  \\ qmatch_abbrev_tac `app p fv xs H Q`
  \\ `H ==>> P * STDERR y` by (rw[] \\ fs[SEP_IMP_REFL])
  \\ imp_res_tac app_wgframe
  \\ `(POSTv uv. A uv * STDOUT x * P') *+ STDERR y ==+> Q *+ GC`
       suffices_by (fs[])
  \\ rw[Abbr `Q`]
  \\ rw[cfHeapsBaseTheory.GC_def,cfHeapsBaseTheory.STARPOST_def,
       cfHeapsBaseTheory.SEP_IMPPOST_def,set_sepTheory.SEP_CLAUSES]
  \\ rw[SEP_IMP_def,SEP_EXISTS,set_sepTheory.SEP_CLAUSES]
  \\ qexists_tac`emp`
  \\ rw[set_sepTheory.SEP_CLAUSES]
  \\ fs[cfHeapsBaseTheory.POSTv_def]
  \\ every_case_tac \\ fs[set_sepTheory.SEP_CLAUSES]
  \\ metis_tac[STAR_COMM,STAR_ASSOC]
  );

val append_SEP_EXISTS = Q.store_thm("append_SEP_EXISTS",
  `app (p:'ffi ffi_proj) fv xs P (POSTv uv. (A uv) * STDOUT a * STDERR b * Q) ==>
   app p fv xs P (POSTv uv. (A uv) * (SEP_EXISTS x y. &(x = a /\ y = b) * STDOUT x * STDERR y) * Q)`,
  qmatch_abbrev_tac`_ (_ X) ==> _ (_ Y)`
  \\ `X = Y` suffices_by rw[]
  \\ unabbrev_all_tac
  \\ simp[FUN_EQ_THM,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ CONV_TAC(PATH_CONV"bbrbbllr"(REWR_CONV STAR_COMM))
  \\ simp[cond_STAR,GSYM STAR_ASSOC]
  \\ simp[AC STAR_ASSOC STAR_COMM]);

val emp_precond = Q.store_thm("emp_precond",
  `emp {}`, EVAL_TAC);

(*-------------------------------------------------------------------------------------------------*)
(*These theorems are need to be remade to use cfMain for projs, oracle or ffi that aren't basis_ffi*)

val file_content_of_ffi_def = Define`
  file_content_of_ffi fd ffi = SOME(FST(THE(get_file_content (THE (fsFFI$decode ffi)) fd)))`

(*RTC_call_FFI_rel_IMP_basis_events show that extracting output from two ffi_states will use the
  same function if the two states are related by a series of FFI_calls. If this is the case for
  your oracle (and projs), then this proof should be relatively similar. Note
  that to make the subsequent proofs similar one should show an equivalence between
  extract_output and proj1  *)
val RTC_call_FFI_rel_IMP_basis_events = Q.store_thm ("RTC_call_FFI_rel_IMP_basis_events",
  `!st st'. call_FFI_rel^* st st' ==>
  st.oracle = basis_ffi_oracle ==>
  (extract_output st.io_events = file_content_of_ffi 1 (basis_proj1 st.ffi_state ' "write") ==>
   extract_output st'.io_events = file_content_of_ffi 1 (basis_proj1 st'.ffi_state ' "write")) ∧ 
  (extract_err st.io_events = file_content_of_ffi 2 (basis_proj1 st.ffi_state ' "write") ==>
   extract_err st'.io_events = file_content_of_ffi 2 (basis_proj1 st'.ffi_state ' "write"))`, 
   cheat);
  HO_MATCH_MP_TAC RTC_INDUCT \\ rw [] \\ fs [file_content_of_ffi_def]
  \\ fs [evaluatePropsTheory.call_FFI_rel_def]
  \\ fs [ffiTheory.call_FFI_def]
  \\ Cases_on `st.final_event = NONE` \\ fs [] \\ rw []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `f` \\ fs []
  \\ fs [extract_output_APPEND,extract_output_def,basis_proj1_write,
         extract_err_APPEND,extract_err_def] \\ rfs []
  \\ first_x_assum match_mp_tac
  \\ qpat_x_assum`_ = Oracle_return _ _`mp_tac
  \\ simp[basis_ffi_oracle_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rw[]
  \\ fs[fsFFITheory.ffi_write_def,OPTION_CHOICE_EQUALS_OPTION,write_def,option_eq_some]
     \\  rpt(full_case_tac \\ fs[option_eq_some] \\ rw[])
  \\ rpt(pairarg_tac \\ fs[])
  rfs[get_file_content_fsupdate,get_file_content_fsupdate_unchanged]
  find"fsupdate"
  find"Oracle_return";
  \\
  \\ rpt(pairarg_tac \\ fs[])
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ simp[n2w_ORD_CHR_w2n |> SIMP_RULE(srw_ss())[o_THM,FUN_EQ_THM]]
);
(*extract_output_basis_ffi shows that the first condition for the previous theorem holds for the
  init_state ffi  *)
val extract_output_basis_ffi = Q.store_thm ("extract_output_basis_ffi",
  `extract_output (init_state (basis_ffi inp cls fs ll)).ffi.io_events = 
   file_content_of_ffi 1 
     (basis_proj1 (init_state (basis_ffi inp cls fs ll)).ffi.ffi_state ' "write")
  `,
  rw[ml_progTheory.init_state_def, extract_output_def, basis_ffi_def,
     basis_proj1_write, cfHeapsBaseTheory.destStr_def, FUPDATE_LIST_THM,
     FAPPLY_FUPDATE_THM,file_content_of_ffi_def,get_file_content_def]);

val extract_err_basis_ffi = Q.store_thm ("extract_err_basis_ffi",
  `extract_err (init_state (basis_ffi inp cls fs ll)).ffi.io_events = 
   file_content_of_ffi 2 
     (basis_proj1 (init_state (basis_ffi inp cls fs ll)).ffi.ffi_state ' "write")`,
  rw[ml_progTheory.init_state_def, extract_err_def, basis_ffi_def,
     basis_proj1_write, cfHeapsBaseTheory.destStr_def,get_file_content_def,
     FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM,file_content_of_ffi_def]);

(*call_main_thm_basis uses call_main_thm2 to get Semantics_prog, and then uses the previous two
  theorems to prove the outcome of extract_output. If RTC_call_FFI_rel_IMP* uses proj1, after
  showing that post-condition which gives effects your programs output is an FFI_part and
  assuming that parts_ok is satisfied, an assumption about proj1 and the ffi_state should be
  derived which should fit the function on some st.ffi_state which returns extract_output on
  st.io_events  *)

fun mk_main_call s =
(* TODO: don't use the parser so much here? *)
  ``Tdec (Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;


val call_main_thm_basis = Q.store_thm("call_main_thm_basis",
`!fname fv.
 ML_code env1 (init_state (basis_ffi inp cls fs ll)) prog NONE env2 st2 ==>
   lookup_var fname env2 = SOME fv ==>
  app (basis_proj1, basis_proj2) fv [Conv NONE []] P
    (POSTv uv. &UNIT_TYPE () uv * (SEP_EXISTS x y. &R x y * STDOUT x * STDERR y) * Q) ==>
  no_dup_mods (SNOC ^main_call prog) (init_state (basis_ffi inp cls fs ll)).defined_mods /\
  no_dup_top_types (SNOC ^main_call prog) (init_state (basis_ffi inp cls fs ll)).defined_types ==>
  (?h1 h2. SPLIT (st2heap (basis_proj1, basis_proj2) st2) (h1,h2) /\ P h1)
  ==>
    ∃io_events x y. R x y /\
    semantics_prog (init_state (basis_ffi inp cls fs ll)) env1
      (SNOC ^main_call prog) (Terminate Success io_events) /\
    extract_output io_events = SOME x /\
    extract_err    io_events = SOME y`,
    rw[]
    \\ `app (basis_proj1,basis_proj2) fv [Conv NONE []] P (POSTv uv.
          &UNIT_TYPE () uv * ((SEP_EXISTS x y. &R x y * STDOUT x * STDERR y) * Q))` by (fs[STAR_ASSOC])
    \\ drule (GEN_ALL call_main_thm2)
    \\ rpt(disch_then drule)
    \\ qmatch_goalsub_abbrev_tac`FFI_part_hprop X`
    \\ `FFI_part_hprop X`
    by(simp[Abbr`X`]
       \\ match_mp_tac FFI_part_hprop_STAR \\ disj1_tac
       \\ ho_match_mp_tac FFI_part_hprop_SEP_EXISTS \\ rw[]
       \\ ho_match_mp_tac FFI_part_hprop_SEP_EXISTS \\ rw[]
       \\ metis_tac[STDOUT_FFI_part_hprop, FFI_part_hprop_STAR])
    \\ disch_then (qspecl_then [`h2`, `h1`] mp_tac) \\ rw[Abbr`X`]
    \\ fs[SEP_EXISTS_THM,SEP_CLAUSES]
    \\ `R x y` by metis_tac[cond_STAR,STAR_ASSOC,STAR_COMM]
    \\ map_every qexists_tac [`st3.ffi.io_events`,`x`,`y`]
    \\ `file_content_of_ffi 1 (basis_proj1 st3.ffi.ffi_state ' "write") = SOME x /\
        file_content_of_ffi 2 (basis_proj1 st3.ffi.ffi_state ' "write") = SOME y`
        suffices_by
      (imp_res_tac RTC_call_FFI_rel_IMP_basis_events
       \\ fs[extract_output_basis_ffi, extract_err_basis_ffi,
            ml_progTheory.init_state_def, basis_ffi_def])
    \\ fs[basis_proj1_write, STDOUT_def,STDERR_def, cfHeapsBaseTheory.IO_def,
          cfHeapsBaseTheory.IOx_def, set_sepTheory.SEP_CLAUSES,
          set_sepTheory.SEP_EXISTS_THM, fsFFITheory.fs_ffi_part_def,IOFS_def]
    \\ fs[GSYM set_sepTheory.STAR_ASSOC] \\ fs[Once STAR_def]
    \\ fs[set_sepTheory.one_STAR]
    \\ qmatch_assum_abbrev_tac`ffip ∈ v`
    \\ fs[Once set_sepTheory.STAR_ASSOC]
    \\ NTAC 3 (fs[Once set_sepTheory.STAR_def])
    \\ fs [set_sepTheory.one_STAR]
    \\ qmatch_assum_abbrev_tac`ffip2 ∈ v''''`
    \\ `ffip ∈ (st2heap (basis_proj1,basis_proj2) st3)` by cfHeapsBaseLib.SPLIT_TAC
    \\ `ffip2 ∈ (st2heap (basis_proj1,basis_proj2) st3)` by cfHeapsBaseLib.SPLIT_TAC
    \\ fs [cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap,
           Abbr`ffip`, Abbr`ffip2`]
    \\ fs [cfStoreTheory.ffi2heap_def,file_content_of_ffi_def]
    \\ Cases_on `parts_ok st3.ffi (basis_proj1, basis_proj2)`
    \\ fs[FLOOKUP_DEF, MAP_MAP_o, n2w_ORD_CHR_w2n, basis_proj1_write]

    \\ FIRST_X_ASSUM(ASSUME_TAC o Q.SPEC`"write"`)
    \\ FIRST_X_ASSUM(ASSUME_TAC o Q.SPEC`"write"`)
    \\ fs[basis_proj1_write,STAR_def,cond_def]
);

val basis_ffi_length_thms = save_thm("basis_ffi_length_thms", LIST_CONJ
[stdinFFITheory.ffi_getChar_length,
 stdoutFFITheory.ffi_putChar_length,
 stderrFFITheory.ffi_putChar_err_length,
 commandLineFFITheory.ffi_getArgs_length,
 rofsFFITheory.ffi_open_length,
 rofsFFITheory.ffi_fgetc_length,
 rofsFFITheory.ffi_close_length,
 rofsFFITheory.ffi_isEof_length]);

val basis_ffi_part_defs = save_thm("basis_ffi_part_defs", LIST_CONJ
[stdinFFITheory.stdin_ffi_part_def,
 stdoutFFITheory.stdout_ffi_part_def,
 stderrFFITheory.stderr_ffi_part_def,
 commandLineFFITheory.commandLine_ffi_part_def,
 rofsFFITheory.rofs_ffi_part_def]);

(* This is used to show to show one of the parts of parts_ok for the state after a spec *)
val oracle_parts = Q.store_thm("oracle_parts",
  `!st. st.ffi.oracle = basis_ffi_oracle /\ MEM (ns, u) basis_proj2 /\ MEM m ns /\ u m bytes (basis_proj1 x ' m) = SOME (new_bytes, w)
    ==> (?y. st.ffi.oracle m x bytes = Oracle_return y new_bytes /\ basis_proj1 x |++ MAP (\n. (n,w)) ns = basis_proj1 y)`,
  simp[basis_proj2_def,basis_proj1_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[cfHeapsBaseTheory.mk_proj1_def,
        cfHeapsBaseTheory.mk_proj2_def,
        basis_ffi_oracle_def,basis_ffi_part_defs]
  \\ rw[] \\ fs[FUPDATE_LIST_THM,FAPPLY_FUPDATE_THM]
  \\ TRY (
     CASE_TAC \\ fs[cfHeapsBaseTheory.mk_ffi_next_def]
  \\ CASE_TAC \\ fs[fmap_eq_flookup,FLOOKUP_UPDATE]
  \\ rw[] )
  \\ disj2_tac
  \\ CCONTR_TAC \\ fs[] \\ rfs[]
);

(*This is an example of how to show parts_ok for a given state -- could be automate and put in ioProgLib.sml *)
val parts_ok_basis_st = Q.store_thm("parts_ok_basis_st",
  `parts_ok (auto_state_1 (basis_ffi inp cls fs)).ffi (basis_proj1, basis_proj2)` ,
  qmatch_goalsub_abbrev_tac`st.ffi`
  \\ `st.ffi.oracle = basis_ffi_oracle`
  by( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC)
  \\ rw[cfStoreTheory.parts_ok_def]
  \\ TRY ( simp[Abbr`st`] \\ EVAL_TAC \\ NO_TAC )
  \\ TRY ( imp_res_tac oracle_parts \\ rfs[] \\ NO_TAC)
  \\ qpat_x_assum`MEM _ basis_proj2`mp_tac
  \\ simp[basis_proj2_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj2_def]
  \\ TRY (qpat_x_assum`_ = SOME _`mp_tac)
  \\ simp[basis_proj1_def,basis_ffi_part_defs,cfHeapsBaseTheory.mk_proj1_def,FUPDATE_LIST_THM]
  \\ rw[] \\ rw[] \\ pairarg_tac \\ fs[FLOOKUP_UPDATE] \\ rw[]
  \\ fs[FAPPLY_FUPDATE_THM,cfHeapsBaseTheory.mk_ffi_next_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ EVERY (map imp_res_tac (CONJUNCTS basis_ffi_length_thms)) \\ fs[]
  \\ srw_tac[DNF_ss][]
);

(* TODO: Move these to somewhere relevant *)
val extract_output_not_putChar = Q.prove(
    `!xs name bytes. name <> "putChar" ==>
      extract_output (xs ++ [IO_event name bytes]) = extract_output xs`,
      rw[extract_output_APPEND, extract_output_def] \\ Cases_on `extract_output xs` \\ rw[]
);

val extract_err_not_putChar_err = Q.prove(
    `!xs name bytes. name <> "putChar_err" ==>
      extract_err (xs ++ [IO_event name bytes]) = extract_err xs`,
      rw[extract_err_APPEND, extract_err_def] \\ Cases_on `extract_err xs` \\ rw[]
);

val extract_output_FILTER = Q.store_thm("extract_output_FILTER",
  `!st. extract_output st.ffi.io_events = extract_output (FILTER (ffi_has_index_in ["putChar"]) st.ffi.io_events)`,
  Cases_on `st` \\ Cases_on `f` \\ Induct_on `l'` \\ fs[]
  \\ simp_tac std_ss [Once CONS_APPEND, extract_output_APPEND]
  \\ fs[] \\ rw[extract_output_def] \\ full_case_tac
  \\ Cases_on `extract_output (FILTER (ffi_has_index_in ["putChar"]) l')` \\ fs[]
  \\ simp_tac std_ss [Once CONS_APPEND, extract_output_APPEND] \\ fs[]
  \\ Cases_on `h` \\ Cases_on `s = "putChar"` \\ fs[cfStoreTheory.ffi_has_index_in_def, extract_output_def]
);

val extract_err_FILTER = Q.store_thm("extract_err_FILTER",
  `!st. extract_err st.ffi.io_events = extract_err (FILTER (ffi_has_index_in ["putChar_err"]) st.ffi.io_events)`,
  Cases_on `st` \\ Cases_on `f` \\ Induct_on `l'` \\ fs[]
  \\ simp_tac std_ss [Once CONS_APPEND, extract_err_APPEND]
  \\ fs[] \\ rw[extract_err_def] \\ full_case_tac
  \\ Cases_on `extract_err (FILTER (ffi_has_index_in ["putChar_err"]) l')` \\ fs[]
  \\ simp_tac std_ss [Once CONS_APPEND, extract_err_APPEND] \\ fs[]
  \\ Cases_on `h` \\ Cases_on `s = "putChar_err"` \\
  fs[cfStoreTheory.ffi_has_index_in_def, extract_err_def]
);

val UNION_DIFF_3 = Q.store_thm("UNION_DIFF_3",
  `!a b c. (DISJOINT a b /\ DISJOINT a c /\ DISJOINT b c) \/
    (DISJOINT b a /\ DISJOINT c a /\ DISJOINT c b) ==>
    (a ∪ b ∪ c DIFF b DIFF c) = a`,
    SPLIT_TAC
);


val star_delete_heap_imp = Q.store_thm("star_delete_heap_imp",
  `((A * B * C):hprop) h /\ A s1 /\ B s2 /\ C s3
    /\ (!a b. C a /\ C b ==> a = b)
    /\ (!a b. B a /\ B b ==> a = b)
    /\ (!a b. A a /\ A b ==> a = b)
    ==>
    (A * B) (h DIFF s3) /\ (A * C) (h DIFF s2) /\
    (B * C) (h DIFF s1) /\ A (h DIFF s2 DIFF s3) /\
    B (h DIFF s1 DIFF s3) /\ C (h DIFF s1 DIFF s2)`,
    rw[set_sepTheory.STAR_def]
    \\ `v = s3` by fs[] \\ rw[]
    \\ `v' = s2` by fs[] \\ rw[]
    \\ `u' = s1` by fs[] \\ rw[]
    \\ TRY (instantiate \\ SPLIT_TAC \\ NO_TAC)
    \\ fs[SPLIT_def]  \\ rw[] \\ fs[]
    \\ imp_res_tac UNION_DIFF_3 \\ rw[] \\ fs[DISJOINT_SYM] \\ rfs[]
    \\ metis_tac[UNION_COMM, UNION_ASSOC]
);


val _ = export_theory();

