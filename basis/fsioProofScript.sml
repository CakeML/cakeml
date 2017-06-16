open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory fsFFITheory fsFFIProofTheory fsioProgTheory 
     cfLetAutoLib optionMonadTheory

val _ = new_theory"fsioProof";

val _ = translation_extends "fsioProg";
val _ = monadsyntax.add_monadsyntax();
val IOFS_buff257_def = Define`
  IOFS_buff257 =
    SEP_EXISTS v. W8ARRAY buff257_loc v * cond (LENGTH v = 257)
`;

val IOFS_def = Define `
  IOFS fs = IOx fs_ffi_part fs * &(wfFS fs)`

val buff257_loc = EVAL``buff257_loc``

val BadFileName_exn_def = Define `
  BadFileName_exn v =
    (v = Conv (SOME ("BadFileName", TypeExn (Long "IO" (Short "BadFileName")))) [])`

val InvalidFD_exn_def = Define `
  InvalidFD_exn v =
    (v = Conv (SOME ("InvalidFD", TypeExn (Long "IO" (Short "InvalidFD")))) [])`

val EndOfFile_exn_def = Define `
  EndOfFile_exn v =
    (v = Conv (SOME ("EndOfFile", TypeExn (Long "IO" (Short "EndOfFile")))) [])`

val FILENAME_def = Define `
  FILENAME s sv =
    (STRING_TYPE s sv ∧
     ¬MEM (CHR 0) (explode s) ∧
     strlen s < 256)
`;

val basis_st = get_ml_prog_state;
(* TODO: move copy/str_to_w8array elsewhere? *)

val copyi_spec = Q.store_thm(
  "copyi_spec",
  `∀n nv cs csv a av.
     NUM n nv /\ n + LENGTH cs < LENGTH a /\ LIST_TYPE CHAR cs csv ==>
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
     insert_atI_NIL,insert_atI_CONS] >> instantiate);

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
  >-(xlet `POSTv zv. & WORD (0w:word8) zv * W8ARRAY av a`
     >- (xapp >> xsimpl) >>
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

val openIn_spec = Q.store_thm(
  "openIn_spec",
  `∀s sv fs.
     FILENAME s sv ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 255 ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "IO.open_in" (basis_st()))
       [sv]
       (IOFS fs * IOFS_buff257)
       (POST
          (\wv. &(WORD (n2w (nextFD fs) :word8) wv ∧
                  validFD (nextFD fs) (openFileFS s fs 0) ∧
                  inFS_fname fs s) *
                IOFS (openFileFS s fs 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s) * IOFS fs))`,
  xcf "IO.open_in" (basis_st()) >>
  fs[FILENAME_def, strlen_def, IOFS_def, IOFS_buff257_def] >> 
  xpull >>
  rename [`W8ARRAY buff257_loc fnm0`] >>
  qmatch_goalsub_abbrev_tac`catfs fs` >>
  xlet `POSTv u. &(UNIT_TYPE () u) * W8ARRAY buff257_loc
          (insert_atI (MAP (n2w o ORD) (explode s) ++ [0w]) 0 fnm0) *
                 catfs fs`
  >- (xapp >> xsimpl >> instantiate >>
      simp[fsioProgTheory.buff257_loc_def] >> xsimpl >>
      Cases_on`s` \\ fs[]) >>
  qabbrev_tac `fnm = insert_atI (MAP (n2w o ORD) (explode s) ++ [0w]) 0 fnm0` >>
  qmatch_goalsub_abbrev_tac`catfs fs' * _` >>
  Cases_on `inFS_fname fs s`
  >- (
    xlet `POSTv u2.
            &(UNIT_TYPE () u2 /\ nextFD fs < 255 /\
              validFD (nextFD fs) (openFileFS s fs 0)) *
            W8ARRAY buff257_loc (LUPDATE 0w 0 (LUPDATE (n2w (nextFD fs)) 1 fnm)) *
            catfs fs'`
    >- (simp[Abbr`catfs`,Abbr`fs'`] >>
        xffi >> simp[fsioProgTheory.buff257_loc_def] >>
        simp[fsFFITheory.fs_ffi_part_def,cfHeapsBaseTheory.IOx_def] >>
        qmatch_goalsub_abbrev_tac`IO st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`ns`,`f`,`encode (openFileFS s fs 0)`,`st`] 
        >> xsimpl >>
        simp[Abbr`f`,Abbr`st`,Abbr`ns`, cfHeapsBaseTheory.mk_ffi_next_def,
             ffi_open_in_def, decode_encode_FS, Abbr`fnm`,
             getNullTermStr_insert_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
             implode_explode, LENGTH_explode] >>
        `∃content. ALOOKUP fs.files s = SOME content`
          by (fs[inFS_fname_def, ALOOKUP_EXISTS_IFF, MEM_MAP, EXISTS_PROD] >>
              metis_tac[]) >>
        csimp[nextFD_ltX, openFileFS_def, openFile_def, validFD_def]) >>
    xlet `POSTv fdv. &WORD (0w : word8) fdv *
                     W8ARRAY buff257_loc (LUPDATE 0w 0 (LUPDATE (n2w (nextFD fs)) 1 fnm)) *
                     catfs fs'`
    >- (xapp >> xsimpl >> simp[fsioProgTheory.buff257_loc_def] >> xsimpl >>
        csimp[HD_LUPDATE] >>
        simp[Abbr`fnm`, LENGTH_insert_atI, LENGTH_explode]) >>
    xlet `POSTv eqn1v. &WORD (0w :word8) eqn1v *
                       W8ARRAY buff257_loc (LUPDATE 0w 0 (LUPDATE (n2w (nextFD fs)) 1 fnm)) *
                       catfs fs'`
    >- (xapp >> simp[fsioProgTheory.buff257_loc_def]>>  xsimpl >> 
        rw[Abbr`fnm`,LENGTH_insert_atI,LENGTH_explode,buff257_loc,HD_LUPDATE]) >>
    xlet `POSTv eqn1v. &BOOL T eqn1v *
                W8ARRAY buff257_loc (LUPDATE 0w 0 (LUPDATE (n2w (nextFD fs)) 1 fnm)) *
                catfs fs'`
    >- (xapp_spec eq_word8_v_thm >> instantiate >> xsimpl >> fs[FALSE_def]) >>
    xif >> instantiate >> xapp >> 
    simp[fsioProgTheory.buff257_loc_def] >> xsimpl >>
    fs[EL_LUPDATE,Abbr`fnm`,LENGTH_insert_atI,LENGTH_explode,wfFS_openFile,Abbr`fs'`])
    >- (xlet `POSTv u2.
            &UNIT_TYPE () u2 * catfs fs *
            W8ARRAY buff257_loc (LUPDATE 255w 0 fnm)`
    >- (simp[Abbr`catfs`,Abbr`fs'`] >> xffi >> simp[buff257_loc_def] >>
        simp[fsFFITheory.fs_ffi_part_def,cfHeapsBaseTheory.IOx_def] >>
        qmatch_goalsub_abbrev_tac`IO st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`ns`,`f`,`st`,`st`] >> xsimpl >>
        simp[Abbr`f`,Abbr`st`,Abbr`ns`, cfHeapsBaseTheory.mk_ffi_next_def,
             ffi_open_in_def, decode_encode_FS, Abbr`fnm`,
             getNullTermStr_insert_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
             implode_explode, LENGTH_explode] >>
        simp[not_inFS_fname_openFile]
        ) >>
    xlet `POSTv fdv. &WORD (0w: word8) fdv * catfs fs *
                     W8ARRAY buff257_loc (LUPDATE 255w 0 fnm)`
    >- (xapp >> xsimpl >> simp[buff257_loc_def] >> xsimpl >>
        csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insert_atI, LENGTH_explode]) >>
    xlet `POSTv fdv. &WORD (255w: word8) fdv * catfs fs *
                     W8ARRAY buff257_loc (LUPDATE 255w 0 fnm)`
    >- (xapp >> xsimpl >> simp[buff257_loc_def] >> xsimpl >>
        csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insert_atI, LENGTH_explode]) >>       
    xlet `POSTv eqn1v.  &BOOL F eqn1v *catfs fs *
            W8ARRAY buff257_loc (LUPDATE 255w 0 fnm)`
    >- (xapp_spec eq_word8_v_thm >> instantiate >> xsimpl >> fs[TRUE_def]) >>
    xif >> instantiate >> xlet_auto
    >- (xret >> xsimpl >> simp[BadFileName_exn_def]) >>
    xraise >> xsimpl >> 
    simp[Abbr`fnm`, LENGTH_insert_atI, LENGTH_explode,BadFileName_exn_def]));


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


val write_spec = Q.store_thm("write_spec",
 `liveFS fs ⇒ wfFS fs ⇒ validFD (w2n fd) fs ⇒
  0 < w2n n ⇒ w2n n <= 255 ⇒ w2n fd < 255 ⇒ LENGTH rest = 255 ⇒
  get_file_content fs (w2n fd) = SOME(content, pos) ⇒
  WORD (fd:word8) fdv ⇒ WORD (n:word8) nv ⇒ 
  app (p:'ffi ffi_proj) ^(fetch_v "write" (basis_st())) [fdv;nv]

  (IOFS fs * W8ARRAY buff257_loc (h1 :: h2 :: rest)) 

  (POST (\nwv. SEP_EXISTS nw. &(NUM nw nwv) * &(nw > 0) * &(nw <= w2n n) *
               W8ARRAY buff257_loc (0w :: n2w nw :: rest) *
                 IOFS(fsupdate fs (w2n fd) (1 + Lnext_pos fs.numchars) (pos + nw)
                        (TAKE pos content ++ 
                         TAKE nw (MAP (CHR o w2n) rest) ++ 
                         DROP (pos + nw) content)))
      (\e. &(InvalidFD_exn e) * W8ARRAY buff257_loc (1w::n::rest) *
           &(F) *
           IOFS (fs with numchars:= THE(LDROP (1 + Lnext_pos fs.numchars) fs.numchars))))`,
  strip_tac >> fs[liveFS_def] >> `?ll. fs.numchars = ll` by simp[]  >> fs[] >>
  `liveFS fs` by fs[liveFS_def] >> FIRST_X_ASSUM MP_TAC >> FIRST_X_ASSUM MP_TAC >> 
  qid_spec_tac `h2` >> qid_spec_tac `h1` >> qid_spec_tac `fs` >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac `ll` >> 
  HO_MATCH_MP_TAC always_eventually_ind >>
  xcf "write" (basis_st()) >> fs[buff257_loc_def]>>
  `ll = fs.numchars` by simp[] >> fs[]
(* next el is <> 0 *)
  >-(sg`Lnext_pos fs.numchars = 0`   
     >-(fs[Lnext_pos_def,Once Lnext_def,liveFS_def,always_thm] >>
        cases_on`fs.numchars` >> fs[]) >>
     xlet_auto >-(simp[LUPDATE_def] >> xsimpl) >>
     xlet_auto >-(simp[LUPDATE_def] >> xsimpl) >>
     xlet`POSTv uv. &(UNIT_TYPE () uv) *
            W8ARRAY buff257_loc (0w:: (n2w (MIN (w2n n) k)) ::rest) *
            IOFS (fsupdate fs (w2n fd) 1 (MIN (w2n n) k + pos)
                          (TAKE pos content ++ 
                           TAKE (MIN (w2n n) k) (MAP (CHR o w2n) rest) ++ 
                           DROP (MIN (w2n n) k + pos) content))`
     >-(qmatch_goalsub_abbrev_tac` _ * _ * IOFS fs'` >>
        xffi >> xsimpl >>
        fs[buff257_loc,IOFS_def,cfHeapsBaseTheory.IOx_def,fs_ffi_part_def,
               cfHeapsBaseTheory.mk_ffi_next_def] >>
        qmatch_goalsub_abbrev_tac`IO st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`ns`,`f`,`encode fs'`,`st`] >>
        xsimpl >>
        fs[Abbr`f`,Abbr`st`,Abbr`ns`,cfHeapsBaseTheory.mk_ffi_next_def,
           ffi_write_def,decode_encode_FS,MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
           dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
           HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,write_def,
           get_file_content_def] >>
        pairarg_tac >> xsimpl >>
        `MEM (w2n fd) (MAP FST fs.infds)` by (metis_tac[MEM_MAP]) >>
        rw[] >> TRY(metis_tac[wfFS_fsupdate]) >>
        EVAL_TAC >>
        (* TODO: automate? *)
        qexists_tac`(0w::n2w (MIN (w2n n) k)::rest,fs')` >> fs[] >>
        qexists_tac`(MIN (w2n n) k, fs')` >> fs[Abbr`fs'`,fsupdate_def] >>
        qexists_tac`(fnm, off)` >> fs[] >> rfs[] >>
        cases_on`fs.numchars` >> fs[]) >>
     qmatch_goalsub_abbrev_tac` _ * IOFS fs'` >>
     qmatch_goalsub_abbrev_tac`W8ARRAY _ (_::m::rest)` >>
     (* xlet_auto fails here *)
     xlet`POSTv g. &WORD (1w :word8) g * 
            W8ARRAY buff257_loc (0w::m::rest) * IOFS fs'` 
     >-(xapp >> xsimpl) >>
     xlet`POSTv g. &WORD (0w :word8) g * 
            W8ARRAY buff257_loc (0w::m::rest) * IOFS fs'` 
     >-(xapp >> simp[buff257_loc_def] >> xsimpl) >>
     xlet`POSTv comp. &BOOL FALSE comp * 
            W8ARRAY buff257_loc (0w::m::rest) * IOFS fs'` 
     >- (xapp_spec eq_word8_v_thm >>instantiate >> 
         fs[BOOL_def,FALSE_def,buff257_loc_def] >> xsimpl) >>
     xif >> fs[FALSE_def] >>
     xlet`POSTv g. &WORD (m :word8) g * 
            W8ARRAY buff257_loc (0w::m::rest) * IOFS fs'` 
     >-(xapp >> simp[buff257_loc_def] >> xsimpl) >>
     xlet`POSTv g. &NUM (MIN (w2n n) k) g * 
            W8ARRAY buff257_loc (0w::m::rest) * IOFS fs'` 
     >-(xapp >> instantiate >> fs[Abbr`m`] >>
        simp[buff257_loc_def] >> xsimpl) >>
     `w2n n <> 0` by (cases_on`w2n n` >> fs[]) >>
     xlet`POSTv comp. &BOOL FALSE comp * 
            W8ARRAY buff257_loc (0w::m::rest) * IOFS fs'`     
     >- (xapp_spec eq_num_v_thm >> xsimpl >> instantiate >> fs[FALSE_def]) >>
     xif >> fs[FALSE_def] >> xvar >> xsimpl
     >-(fs[Abbr`fs'`,MIN_DEF,buff257_loc_def] >> instantiate >> xsimpl) >>
     rw[InvalidFD_exn_def] >> fs[]) >>
 (* next element is 0 *)
  cases_on`fs.numchars` >- fs[liveFS_def] >> fs[] >>
  simp[buff257_loc_def] >> xlet_auto >- xsimpl >>
  simp[buff257_loc_def] >> xlet_auto 
  >- (xsimpl >> EVAL_TAC >> fs[]) >>
  xlet`POSTv uv. &(UNIT_TYPE () uv) *
        W8ARRAY buff257_loc (0w:: 0w ::rest) *
        IOFS (fsupdate fs (w2n fd) 1 pos
                          (TAKE pos content ++ 
                           TAKE 0 (MAP (CHR o w2n) rest) ++ 
                           DROP pos content))`
  >-(qmatch_goalsub_abbrev_tac` _ * _ * IOFS fs'` >>
    xffi >> xsimpl >>
    fs[buff257_loc,IOFS_def,cfHeapsBaseTheory.IOx_def,fs_ffi_part_def,
           cfHeapsBaseTheory.mk_ffi_next_def] >>
    qmatch_goalsub_abbrev_tac`IO st f ns` >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`ns`,`f`,`encode fs'`,`st`] >>
    xsimpl >>
    fs[Abbr`f`,Abbr`st`,Abbr`ns`,cfHeapsBaseTheory.mk_ffi_next_def,
       ffi_write_def,decode_encode_FS,MEM_MAP, ORD_BOUND,ORD_eq_0,wfFS_LDROP,
       dimword_8, MAP_MAP_o,o_DEF,char_BIJ,implode_explode,LENGTH_explode,
       HD_LUPDATE,LUPDATE_def,option_eq_some,validFD_def,write_def,
       get_file_content_def] >>
    pairarg_tac >> xsimpl >>
    `MEM (w2n fd) (MAP FST fs.infds)` by (metis_tac[MEM_MAP]) >>
    rw[] >> TRY(metis_tac[wfFS_fsupdate]) >>
    EVAL_TAC >>
    qexists_tac`(0w::0w::rest,fs')` >> fs[] >>
    qexists_tac`(0, fs')` >> fs[Abbr`fs'`,fsupdate_def] >>
    qexists_tac`(fnm, off)` >> fs[] >> rfs[] >>
    cases_on`fs.numchars` >> fs[liveFS_def]
    ) >>
  qmatch_goalsub_abbrev_tac` _ * IOFS fs'` >>
  xlet`POSTv g. &WORD (1w :word8) g * 
        W8ARRAY buff257_loc (0w:: 0w ::rest) * IOFS fs'` 
  >-(xapp >> simp[buff257_loc_def] >> xsimpl) >>
  xlet`POSTv g. &WORD (0w :word8) g * 
        W8ARRAY buff257_loc (0w::0w::rest) * IOFS fs'` 
  >-(xapp >> simp[buff257_loc_def] >> xsimpl) >>
  xlet`POSTv comp. &BOOL FALSE comp * 
        W8ARRAY buff257_loc (0w::0w::rest) * IOFS fs'` 
  >- (xapp_spec eq_word8_v_thm >>instantiate >> 
     fs[BOOL_def,FALSE_def,buff257_loc_def] >> xsimpl) >>
  xif >> fs[FALSE_def] >>
  xlet`POSTv g. &WORD (0w :word8) g * 
        W8ARRAY buff257_loc (0w::0w::rest) * IOFS fs'` 
  >-(xapp >> simp[buff257_loc_def] >> xsimpl) >>
  xlet`POSTv g. &NUM 0 g * 
        W8ARRAY buff257_loc (0w::0w::rest) * IOFS fs'` 
  >-(xapp >> instantiate >> simp[buff257_loc_def] >> xsimpl) >>
  xlet`POSTv comp. &BOOL TRUE comp * 
        IOFS fs' * W8ARRAY buff257_loc (0w::(n2w 0)::rest)`     
  >- (xapp_spec eq_num_v_thm >> xsimpl >> instantiate >> fs[TRUE_def]) >>
  xif >> fs[TRUE_def] >> fs[buff257_loc_def] >>
  sg`t = fs'.numchars` >-(fs[Abbr`fs'`,fsupdate_def,LDROP_1]) >>
  `wfFS fs'` by (fs[Abbr`fs'`,wfFS_fsupdate,validFD_def]) >>

  sg`fs' = fs with numchars := t`
  >-( imp_res_tac validFD_ALOOKUP >> fs[wfFS_def,Abbr`fs'`,fsupdate_def] >>
     fs[IO_fs_component_equality] >> fs[wfFS_def,get_file_content_def] >>
     pairarg_tac >> fs[ALIST_FUPDKEY_unchanged] >> rw[]) >>
  sg`fs  with numchars:= THE (LDROP (Lnext_pos (0:::t) + 1) (0:::t)) =
     fs' with numchars:= THE(LDROP (1 + Lnext_pos fs'.numchars) fs'.numchars)`
  >-(imp_res_tac validFD_ALOOKUP >>
     fs[wfFS_def,Abbr`fs'`,fsupdate_def] >>
     fs[IO_fs_component_equality] >>
     fs[wfFS_def,get_file_content_def] >>
     pairarg_tac >> fs[ALIST_FUPDKEY_unchanged] >> rw[] >> 
     fs[Lnext_pos_def,Once Lnext_def] >>
     cases_on`fs.numchars` >>
     fs[liveFS_def,always_thm,LDROP_1,ADD]) >>
  fs[buff257_loc_def] >>
  sg`get_file_content fs' (w2n fd) = SOME(content,pos)`
  >-(fs[get_file_content_def]) >>
  `liveFS fs'` by (fs[liveFS_def] >> fs[]) >>
  `validFD (w2n fd) fs'` by fs[validFD_def] >>
  sg`!pp cc. fsupdate fs (w2n fd) (Lnext_pos (0:::t) + 1) pp cc =
     fsupdate fs' (w2n fd) (1 + Lnext_pos fs'.numchars) pp cc`
  >-( fs[fsupdate_def]) >> 
  fs[] >>
  FIRST_X_ASSUM (MP_TAC o Q.SPECL [`fs'`, `0w`,`0w`]) >>
  rw[] >>
  rename[`cf_app p _ _ _ Precond Postcond`] >>
  fs[] >> 
  (* should work here *)
  TRY(LAST_X_ASSUM xapp_spec) >>
  cheat
);

val write_char_spec = Q.store_thm("write_char_spec",
  `!(fd :word8) fdv c cv bc content pos.
    w2n fd < 255 ⇒  wfFS fs ⇒
    CHAR c cv ⇒ WORD fd fdv ⇒ validFD (w2n fd) fs ⇒ liveFS fs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "IO.write_char" (basis_st())) [fdv; cv]
    (IOFS fs * &(get_file_content fs (w2n fd) = SOME(content, pos)) * IOFS_buff257) 
    (POST (\uv. &UNIT_TYPE () uv * IOFS_buff257 *
                IOFS (fsupdate fs (w2n fd) (1 + Lnext_pos fs.numchars) (pos + 1)
                     (TAKE pos content ++ [c] ++ DROP (pos + 1) content)))
          (\e. &(InvalidFD_exn e) * &F * IOFS_buff257 * 
               IOFS(fs with numchars :=
                      THE (LDROP (Lnext_pos fs.numchars + 1) fs.numchars))))`,
  xcf "IO.write_char" (basis_st()) >> fs[IOFS_buff257_def] >> 
  xpull >> rename [`W8ARRAY buff257_loc bdef`] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: t'` >>
  Cases_on `t'` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: h3 :: rest` >>
  fs[buff257_loc_def] >>
  xlet_auto >- xsimpl >>
  simp[EVAL ``LUPDATE rr 2 (zz :: tt)``,
       EVAL ``LUPDATE rr 1 (zz :: tt)``, LUPDATE_def] >>
  (* xletauto *)
  xlet `POSTv w. &WORD (1w :word8) w * IOFS fs * W8ARRAY (Loc 4) (h1::h2::n2w (ORD c)::rest)`
  >- (xapp >> xsimpl) >>
  (* xlet_auto *)
  `0 < w2n (1w:word8)` by fs[] >>
  `w2n (1w:word8) <= 255` by fs[] >>
  `LENGTH (n2w (ORD c) :: rest) = 255` by fs[]>>
  `[c] = TAKE 1 (MAP (CHR o w2n) (n2w (ORD c) :: rest))` 
    by (fs[CHR_ORD,LESS_MOD,ORD_BOUND]) >>
  imp_res_tac write_spec >> fs[buff257_loc_def] >>
  FIRST_X_ASSUM (MP_TAC o Q.SPECL [`p`, `h2`,`h1`]) >>
  qmatch_goalsub_abbrev_tac`app p _ _ _ Postcond` >> rw[] >>
  xlet `Postcond` >> fs[Abbr`Postcond`] >- xapp >-xsimpl >>
  xpull >> xcon	>> fs[CHR_ORD,LESS_MOD,ORD_BOUND] >>
  `nw = 1` by fs[] >> xsimpl);

(* TODO: use earlier *)
val fsupdate_unchanged = Q.store_thm("fsupdate_unchanged",
 `get_file_content fs fd = SOME(content, pos) ==> validFD fd fs ==>
    fsupdate fs fd 0 pos content = fs`,
    fs[fsupdate_def,get_file_content_def,validFD_def,IO_fs_component_equality]>>
    rw[] >> pairarg_tac >> fs[ALIST_FUPDKEY_unchanged] >> rw[]);

val write_w8array_spec = Q.store_thm("write_w8array_spec",
  `!(fd :word8) fdv a av bc content pos. 
    NUM i iv ⇒ NUM n nv ⇒ WORD fd fdv ⇒ validFD (w2n fd) fs ⇒ 
    liveFS fs ⇒ w2n fd < 255 ⇒  wfFS fs ⇒
    (get_file_content fs (w2n fd) = SOME(content, pos)) ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "IO.write_w8array" (basis_st())) [fdv; av; iv; nv]

    (IOFS fs *IOFS_buff257 * W8ARRAY av a)  

    (POSTv uv. &(UNIT_TYPE () uv) * IOFS_buff257 * W8ARRAY av a * SEP_EXISTS fs0. 
       SEP_EXISTS k. IOFS (fsupdate fs (w2n fd) k (pos + n)
                       (TAKE pos content ++ 
                        MAP (CHR o w2n) (TAKE n (DROP i a)) ++ 
                        DROP (pos + n) content)))`
  xcf "IO.write_w8array" (basis_st()) >> 
  fs[IOFS_buff257_def] >> xpull >>
  rename [`W8ARRAY buff257_loc bdef`] >>
  Induct_on`n` >> rw[] >> (xlet_auto >- xsimpl) >> xif >> instantiate
  >-(xcon >> xsimpl >> qexists_tac`0` >> fs[fsupdate_unchanged] >> xsimpl) >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  Cases_on `bdef` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: t` >>
  Cases_on `t` >> fs[] >> qmatch_goalsub_abbrev_tac`h1 :: h2 :: rest` >>
  xlet_auto
);
val _ = export_theory();


