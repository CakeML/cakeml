open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory fsFFITheory fsFFIProofTheory fsioProgTheory 
     cfLetAutoLib cfLetAutoTheory optionMonadTheory cfHeapsBaseTheory
     mlw8arrayProgTheory mlstringProgTheory
    
val _ = new_theory"fsioProof";

val _ = translation_extends "fsioProg";
val _ = monadsyntax.add_monadsyntax();
val IOFS_iobuff_def = Define`
  IOFS_iobuff =
    SEP_EXISTS v. W8ARRAY iobuff_loc v * cond (LENGTH v = 258)
`;

val IOFS_def = Define `
  IOFS fs = IOx fs_ffi_part fs * &(wfFS fs)`

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

val fsupdate_unchanged = Q.store_thm("fsupdate_unchanged",
 `get_file_content fs fd = SOME(content, pos) ==> validFD fd fs ==>
    fsupdate fs fd 0 pos content = fs`,
    fs[fsupdate_def,get_file_content_def,validFD_def,IO_fs_component_equality]>>
    rw[] >> pairarg_tac >> fs[ALIST_FUPDKEY_unchanged] >> rw[]);

val basis_st = get_ml_prog_state;
(* TODO: move copy/str_to_w8array elsewhere? *)

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

(* TODO: add xlet_auto_match tag *)
val eq_word8_v_thm =
  mlbasicsProgTheory.eq_v_thm
  |> DISCH_ALL
  |> C MATCH_MP (ml_translatorTheory.EqualityType_NUM_BOOL
                 |> CONJUNCTS |> el 4)
                 |> Q.INST_TYPE [`:α` |->`:8`];
val eq_num_v_thm =
  mlbasicsProgTheory.eq_v_thm
  |> DISCH_ALL
  |> C MATCH_MP (ml_translatorTheory.EqualityType_NUM_BOOL
                 |> CONJUNCTS |> el 1)
                 |> Q.INST_TYPE [`:α` |->`:8`];


val WORD_UNICITY_R = Q.store_thm("WORD_UNICITY_R[xlet_auto_match]",
`!f fv fv'. WORD (f :word8) fv ==> (WORD f fv' <=> fv' = fv)`, fs[WORD_def]);

val openIn_spec = Q.store_thm(
  "openIn_spec",
  `∀s sv fs.
     FILENAME s sv ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 255 ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "IO.open_in" (basis_st()))
       [sv]
       (IOFS fs * IOFS_iobuff)
       (POST
          (\wv. &(WORD (n2w (nextFD fs) :word8) wv ∧
                  validFD (nextFD fs) (openFileFS s fs 0) ∧
                  inFS_fname fs s) *
                IOFS (openFileFS s fs 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s) * IOFS fs))`,
  xcf "IO.open_in" (basis_st()) >>
  fs[FILENAME_def, strlen_def, IOFS_def, IOFS_iobuff_def] >> 
  xpull >>
  rename [`W8ARRAY _ fnm0`] >>
  qmatch_goalsub_abbrev_tac`catfs fs` >>
  fs[iobuff_loc_def] >>
  xlet_auto
  >- (xsimpl >> Cases_on`s` \\ fs[]) >>
  qabbrev_tac `fnm = insert_atI (MAP (n2w o ORD) (explode s) ++ [0w]) 0 fnm0` >>
  qmatch_goalsub_abbrev_tac`catfs fs' * _` >>
  Cases_on `inFS_fname fs s`
  >- (
    xlet `POSTv u2.
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
    fs[iobuff_loc_def] >>
    xlet_auto
    >- (xsimpl >> rw[Abbr`fnm`,LENGTH_insert_atI,LENGTH_explode,iobuff_loc,HD_LUPDATE]) >>
    xlet_auto >- (xsimpl) >>
    xif
    >-(
       xapp >> simp[fsioProgTheory.iobuff_loc_def] >> xsimpl >>
    fs[EL_LUPDATE,Abbr`fnm`,LENGTH_insert_atI,LENGTH_explode,wfFS_openFile,Abbr`fs'`]) >>
    xlet_auto
    >- (xcon >> xsimpl)
    >- (xraise >> xsimpl >>
        sg `0 < LENGTH (LUPDATE (n2w (nextFD fs)) 1 fnm)`
        >-(
	  fs[] >> fs[markerTheory.Abbrev_def] >> fs[] >>
	  `0 + LENGTH (MAP (n2w ∘ ORD) (explode s) ++ [0w]) <= LENGTH fnm0` by (fs[LENGTH_explode]) >>
	  fs[LENGTH_insert_atI]
        ) >>
        IMP_RES_TAC HD_LUPDATE >> fs[]
      )
  ) >>
  xlet `POSTv u2.
            &UNIT_TYPE () u2 * catfs fs *
            W8ARRAY iobuff_loc (LUPDATE 255w 0 fnm)`
  >- (
      simp[Abbr`catfs`,Abbr`fs'`] >> xffi >> simp[iobuff_loc_def] >>
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
  xlet_auto >-(xsimpl) >>
  fs[iobuff_loc] >>
  xlet_auto
  >- (xsimpl >> csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insert_atI, LENGTH_explode]) >>
  xlet_auto >-(xsimpl) >>
  xif
  >-(
     xapp >> xsimpl >> irule FALSITY >>
     sg `0 < LENGTH fnm`
     >-(
       fs[markerTheory.Abbrev_def] >>
       `0 + LENGTH (MAP (n2w ∘ ORD) (explode s) ++ [0w]) <= LENGTH fnm0` by (fs[LENGTH_explode]) >>
       fs[LENGTH_insert_atI]
     ) >>
     fs[HD_LUPDATE])>>
  xlet_auto >-(xcon >> xsimpl) >>
  xraise >> xsimpl >>
  simp[BadFileName_exn_def]);

val (eventually_rules,eventually_ind,eventually_cases) = Hol_reln`
  (!ll. P ll ==> eventually P ll) /\
  (!h t. ¬P (h:::t) /\ eventually P t ==> eventually P (h:::t)) `;

val eventually_thm = store_thm(
  "eventually_thm",
  ``(eventually P [||] = P [||]) /\
    (eventually P (h:::t) = (P (h:::t) \/(¬ P (h:::t) /\ eventually P t)))``,
  CONJ_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [eventually_cases])) THEN
  SRW_TAC [][]);

val _ = export_rewrites ["eventually_thm"]

val (always_rules,always_ind,always_cases) = Hol_reln`
  (!h t. (P (h ::: t) /\ always P t) ==> always P (h ::: t)) `;

val always_thm = store_thm(
  "always_thm",
  ``!h t. always P (h ::: t) = (P (h ::: t) /\ always P t) /\
    ¬ always P [||]``,
  rw[Once always_cases] >> rw[Once always_cases]);
val _ = export_rewrites ["always_thm"]

val always_eventually = Q.store_thm("always_eventually", 
  `!ll. always (eventually P) ll ==> 
    ?k. (P (THE (LDROP k ll)) /\ always(eventually P) (THE(LDROP k ll)))`,
    HO_MATCH_MP_TAC always_ind >> 
    rw[always_thm,eventually_thm] >>
    qexists_tac`SUC k` >> fs[LDROP]);

val always_eventually_ind = Q.store_thm("always_eventually_ind",
  `(!ll. (P ll \/ (¬ P ll /\ Q (THE(LTL ll)))) ==> Q ll) ==>
   !ll. always(eventually P) ll ==> Q ll`,
   strip_tac >> HO_MATCH_MP_TAC always_ind >> rw[] >> fs[] >>
   cases_on`P (h:::t)` >> fs[]);

val always_DROP = Q.store_thm("always_DROP",
  `!ll. always P ll ==> always P (THE(LDROP k ll))`,
  Induct_on`k` >> cases_on`ll` >> fs[always_thm,LDROP]);
  
(* the filesystem will always eventually allow to write something *)
val liveFS_def = Define`
    liveFS fs = 
        always (eventually (\ll. ?k. LHD ll = SOME k /\ k <> 0)) fs.numchars`

val always_NOT_LFINITE = Q.store_thm("always_NOT_LFINITE",
    `!ll. always P ll ==> ¬ LFINITE ll`,
    HO_MATCH_MP_TAC always_ind >> rw[]);

val LDROP_1 = Q.store_thm("LDROP_1",
  `LDROP (1: num) (h:::t) = SOME t`,
  `LDROP (SUC 0) (h:::t) = SOME t` by fs[LDROP] >>
  metis_tac[ONE]);

val wfFS_LDROP = Q.store_thm("wfFS_LDROP",
 `wfFS fs ==> LDROP k fs.numchars = SOME numchars' ==>
    wfFS (fs with numchars := numchars')`,
 rw[wfFS_def] >> metis_tac[NOT_LFINITE_DROP_LFINITE]);

val Lnext_def = tDefine "Lnext" `
  Lnext P ll = if eventually P ll then
                        if P ll then 0
                        else SUC(Lnext P (THE (LTL ll)))
                     else ARB` 
 (qexists_tac`(\(P,ll') (P',ll). 
    P = P' /\ eventually P ll /\ eventually P ll' /\
    LTL ll = SOME ll' /\ ¬ P ll)` >>reverse(rw[WF_DEF,eventually_thm])
  >-(cases_on`ll` >> fs[])
  >-(cases_on`ll` >> fs[]) >>
  cases_on`w` >> rename[`B(P, ll)`] >> rename[`B(P, ll)`] >>
  reverse(cases_on`eventually P ll`)
  >-(qexists_tac`(P,ll)` >> rw[] >> pairarg_tac >> fs[] >> res_tac >> rfs[]) >>
  rpt(LAST_X_ASSUM MP_TAC) >> qid_spec_tac `ll` >> 
  HO_MATCH_MP_TAC eventually_ind >> rw[]
  >-(qexists_tac`(P,ll)` >> rw[] >> pairarg_tac >> fs[] >> res_tac >> rfs[]) >>
  cases_on`B(P,ll)` >-(metis_tac[]) >>
  qexists_tac`(P,h:::ll)` >> fs[] >> rw[] >> pairarg_tac >> fs[]);

val validFD_ALOOKUP = Q.store_thm("validFD_ALOOKUP",
  `validFD fd fs ==> ?v. ALOOKUP fs.infds fd = SOME v`,
  rw[validFD_def] >> cases_on`ALOOKUP fs.infds fd` >> fs[ALOOKUP_NONE]);

val Lnext_pos_def = Define`
  Lnext_pos (ll :num llist) = Lnext (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0) ll`

val fsupdate_LTL = Q.store_thm("fsupdate_LTL",
  `fs.numchars = h:::t ==>
   fsupdate fs fd (SUC k) p c =
   fsupdate (fs with numchars := t) fd k p c`,
   rw[] >> fs[fsupdate_def,LDROP]);

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

val fsupdate_o = Q.store_thm("fsupdate_o",
 `validFD fd fs ==> liveFS fs ==>
  fsupdate (fsupdate fs fd k1 pos1 c1) fd k2 pos2 c2 = 
  fsupdate fs fd (k1+k2) pos2 c2`,
  rw[fsupdate_def,validFD_def]
  >-(fs[ALIST_FUPDKEY_ALOOKUP] >>
     CASE_TAC >> fs[ALOOKUP_NONE,ALIST_FUPDKEY_o,ALIST_FUPDKEY_eq])
  >-(fs[ALIST_FUPDKEY_o] >> HO_MATCH_MP_TAC ALIST_FUPDKEY_eq >>
	 rw[] >> cases_on`v` >> fs[]) >>
  fs[LDROP_ADD,liveFS_def] >>
  imp_res_tac always_NOT_LFINITE >> imp_res_tac NOT_LFINITE_DROP >>
  FIRST_X_ASSUM(ASSUME_TAC o Q.SPEC`k1`) >> fs[]);

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

val LENGTH_extract_aux = Q.store_thm("LENGTH_extract_aux",
`!s x y. LENGTH (extract_aux s x y) = y`,
     Induct_on`y` >> fs[extract_aux_def,MIN_DEF]);

val strlen_extract_le = Q.store_thm("strlen_extract_le",
`!s x y. strlen (extract s x y) <= strlen s - x`,
  rw[extract_def] >> CASE_TAC >> fs[LENGTH_extract_aux]);

val extract_aux_DROP = Q.store_thm("extract_aux_DROP",
  `!s k. extract_aux (strlit s) k (LENGTH s - k) = DROP k s`,
  rw[] >> `?n. STRLEN s - k = n` by fs[] >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`s` >> qid_spec_tac`k` >>
  induct_on`n` >> fs[extract_aux_def,STRLEN_DEF,DROP_EL_CONS] >>
  rw[] >> fs[extract_aux_def,DROP_LENGTH_TOO_LONG] >>
  (* simplify *)
  FIRST_X_ASSUM MP_TAC >> PURE_REWRITE_TAC [Once (GSYM SUB_EQ_0)] >>
  strip_tac >> FIRST_X_ASSUM (fn x => PURE_REWRITE_TAC[x]) >>
  fs[extract_aux_def])

val extract_aux_eq = Q.store_thm("extract_aux_eq",
  `!n s. n = LENGTH s ==>
   extract_aux (strlit s) 0 n = s`,
  rw[] >> ASSUME_TAC(Q.SPECL[`s`,`0`] extract_aux_DROP) >> fs[]);

val extract_aux_add_r = Q.store_thm("extract_aux_add_r",
  `!n1 n2 s i. extract_aux s i (n1 + n2) = 
                extract_aux s i n1 ++ extract_aux s (i+n1) n2`,
  induct_on`n1` >- fs[extract_aux_def] >>
  rw[] >> fs[GSYM ADD_SUC,extract_aux_def] >> fs[ADD1]);

val extract_aux_eq = Q.store_thm("extract_aux_eq",
  `!s n. n = LENGTH s ==>
   extract_aux (strlit s) 0 n =s`,
  rw[] >> ASSUME_TAC(Q.SPECL[`s`,`0`] extract_aux_DROP) >> fs[]);

val extract_aux_TAKE = Q.store_thm("extract_aux_TAKE",
  `!s. n <= LENGTH s ==>
     extract_aux (strlit s) 0 n = TAKE n s`,
  rw[] >>
  sg`extract_aux (strlit s) 0 n ++ extract_aux (strlit s) n (LENGTH s - n)  = 
     TAKE n s ++ DROP n s`
  >-(fs[TAKE_DROP, GSYM extract_aux_add_r] >>
     ASSUME_TAC(Q.SPECL[`n`,`STRLEN s - n`,`strlit s`,`0`]extract_aux_add_r) >>
     rfs[] >> fs[extract_aux_eq]) >>
  FIRST_X_ASSUM MP_TAC >> PURE_REWRITE_TAC[extract_aux_DROP] >> rw[]);

val write_string_spec = Q.store_thm("write_string_spec",
  `!s (fd :word8) fdv sv fs content pos. 
    WORD fd fdv ⇒ validFD (w2n fd) fs ⇒ 
    STRING_TYPE s sv ⇒
    liveFS fs ⇒ w2n fd < 255 ⇒  wfFS fs ⇒
    (get_file_content fs (w2n fd) = SOME(content, pos)) ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "IO.write_string" (basis_st())) [fdv; sv]
    (IOFS fs * IOFS_iobuff)  
    (POSTv uv. &(UNIT_TYPE () uv) * IOFS_iobuff * 
       SEP_EXISTS k. IOFS (fsupdate fs (w2n fd) k (pos + (strlen s))
                                    (insert_atI (explode s) pos content)))`,
  strip_tac >>
  `?n. strlen s <= n` by (qexists_tac`strlen s` >> fs[]) >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`s` >>
  Induct_on`n` >>
  xcf "IO.write_string" (basis_st()) >> fs[IOFS_iobuff_def] >>
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
 
val _ = export_theory();

