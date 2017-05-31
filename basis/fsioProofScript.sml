open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory fsFFITheory fsFFIProofTheory fsioProgTheory 
     cfLetAutoLib

val _ = new_theory"fsioProof";

val _ = translation_extends "fsioProg";


val IOFS_buff257_def = Define`
  IOFS_buff257 =
    SEP_EXISTS v. W8ARRAY buff257_loc v * cond (LENGTH v = 257)
`;

val IOFS_def = Define `
  IOFS fs = IOx fs_ffi_part fs * &(wfFS fs) * IOFS_buff257`

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
                 W8ARRAY av (insertNTS_atI (MAP (n2w o ORD) cs) n a))`,
  Induct_on `cs` >> fs[LIST_TYPE_def, LENGTH_NIL]
  >- (xcf "IO.copyi" (basis_st()) >> xmatch >>
      xlet `POSTv zv. & WORD (0w:word8) zv * W8ARRAY av a`
      >- (xapp >> xsimpl) >>
      xapp >> xsimpl >> simp[insertNTS_atI_NIL] >> xsimpl >>
      metis_tac[DECIDE ``(x:num) + 1 < y ⇒ x < y``]) >>
  xcf "IO.copyi" (basis_st()) >> xmatch >>
  rename [`LIST_TYPE CHAR ctail ctailv`, `CHAR chd chdv`] >>
  xlet_auto >- (xsimpl) >>
  xlet_auto >- (xsimpl) >>
  xlet `POSTv u. &(UNIT_TYPE () u) * W8ARRAY av (LUPDATE (n2w (ORD chd)) n a)`
  >- (xapp >> simp[]) >>
  qabbrev_tac `a0 = LUPDATE (n2w (ORD chd)) n a` >>
  xlet_auto >- (xsimpl) >>
  xapp >> xsimpl >> qexists_tac `n + 1` >>
  simp[insertNTS_atI_CONS, Abbr`a0`, LUPDATE_insertNTS_commute,NUM_def]);

val str_to_w8array_spec = Q.store_thm(
  "str_to_w8array_spec",
  `∀s sv a av.
     LENGTH (explode s) < LENGTH a ∧ STRING_TYPE s sv ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "IO.str_to_w8array" (basis_st()))
       [av; sv]
       (W8ARRAY av a)
       (POSTv v.
          cond (UNIT_TYPE () v) *
          W8ARRAY av (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 a))`,
  rpt strip_tac >> xcf "IO.str_to_w8array" (basis_st()) >>
  xlet_auto >- xsimpl >> xapp >> simp[])

val openIn_spec = Q.store_thm(
  "openIn_spec",
  `∀s sv fs.
     FILENAME s sv ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 255 ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "IO.open_in" (basis_st()))
       [sv]
       (IOFS fs)
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
          (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0) *
                 catfs fs`
  >- (xapp >> xsimpl >> instantiate >>
      simp[fsioProgTheory.buff257_loc_def] >> xsimpl >>
      Cases_on`s` \\ fs[]) >>
  qabbrev_tac `fnm = insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0` >>
  qmatch_goalsub_abbrev_tac`catfs fs' * _ * _` >>
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
        map_every qexists_tac[`ns`,`f`,`encode (openFileFS s fs 0)`,`st`] >> xsimpl >>
        simp[Abbr`f`,Abbr`st`,Abbr`ns`, cfHeapsBaseTheory.mk_ffi_next_def,
             ffi_open_in_def, decode_encode_FS, Abbr`fnm`,
             getNullTermStr_insertNTS_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
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
        simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]) >>
    xlet `POSTv eqn1v. &WORD (0w :word8) eqn1v *
                       W8ARRAY buff257_loc (LUPDATE 0w 0 (LUPDATE (n2w (nextFD fs)) 1 fnm)) *
                       catfs fs'`
    >- (xapp >> simp[fsioProgTheory.buff257_loc_def]>>  xsimpl >> 
        rw[Abbr`fnm`,LENGTH_insertNTS_atI,LENGTH_explode,buff257_loc,HD_LUPDATE]) >>
    xlet `POSTv eqn1v. &BOOL T eqn1v *
                W8ARRAY buff257_loc (LUPDATE 0w 0 (LUPDATE (n2w (nextFD fs)) 1 fnm)) *
                catfs fs'`
    >- (xapp >> xsimpl >> fs[WORD_def, BOOL_def,EqualityType_NUM_BOOL] >> cheat) >>
    xif >> instantiate >> xapp >> 
    simp[fsioProgTheory.buff257_loc_def] >> xsimpl >>
    fs[EL_LUPDATE,Abbr`fnm`,LENGTH_insertNTS_atI,LENGTH_explode,wfFS_openFile,Abbr`fs'`])
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
             getNullTermStr_insertNTS_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
             implode_explode, LENGTH_explode] >>
        simp[not_inFS_fname_openFile]
        ) >>
    xlet `POSTv fdv. &WORD (0w: word8) fdv * catfs fs *
                     W8ARRAY buff257_loc (LUPDATE 255w 0 fnm)`
    >- (xapp >> xsimpl >> simp[buff257_loc_def] >> xsimpl >>
        csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]) >>
    xlet `POSTv fdv. &WORD (255w: word8) fdv * catfs fs *
                     W8ARRAY buff257_loc (LUPDATE 255w 0 fnm)`
    >- (xapp >> xsimpl >> simp[buff257_loc_def] >> xsimpl >>
        csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]) >>       
    xlet `POSTv eqn1v.  &BOOL F eqn1v *catfs fs *
            W8ARRAY buff257_loc (LUPDATE 255w 0 fnm)`
    >- ( xapp >> xsimpl >> fs[WORD_def, BOOL_def] >> cheat)>>
    xif >> instantiate >>
    xlet_auto

    >- (xret >> xsimpl >> simp[BadFileName_exn_def]) >>
    xraise >> xsimpl >> 
    simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode,BadFileName_exn_def]));

val option_eq_some = LIST_CONJ [
    OPTION_IGNORE_BIND_EQUALS_OPTION,
    OPTION_BIND_EQUALS_OPTION,
    OPTION_CHOICE_EQUALS_OPTION]


val FILE_CONTENT_def = Define`
  FILE_CONTENT fs fd c pos =
    IOFS fs * &(get_file_content fs fd = SOME (c, pos))`

val write_char_spec = Q.store_thm("write_char_spec",
  `!(fd :word8) fdv c cv bc content pos. CHAR c cv ⇒ WORD fd fdv ⇒ validFD (w2n fd) fs ⇒
                    app (p:'ffi ffi_proj) ^(fetch_v "IO.write_char" (basis_st())) [fdv; cv]
   (FILE_CONTENT fs (w2n fd) content pos)
   (POST (\uv. &(UNIT_TYPE () uv) * 
               IOFS (fsupdate fs (w2n fd) (LUPDATE c pos content) (pos + 1)))
         (\e. &(InvalidFD_exn e) * IOFS fs ))`,
  xcf "IO.write_char" (basis_st()) >> 
  fs[IOFS_def, IOFS_buff257_def,FILE_CONTENT_def] >> 
  xpull >>
  rename [`W8ARRAY buff257_loc bdef`] >>
  xlet `POSTv u. &(UNIT_TYPE () u) * IOx fs_ffi_part fs *
            W8ARRAY buff257_loc (LUPDATE fd 0 bdef)`
  >- (xapp >> simp[buff257_loc] >> xsimpl >> metis_tac[]) >>
  xlet `POSTv b. &WORD (1w :word8) b * IOx fs_ffi_part fs *
            W8ARRAY buff257_loc (LUPDATE fd 0 bdef)`
  >- (xapp >> xsimpl) >>
  xlet `POSTv u'. &(UNIT_TYPE () u') * IOx fs_ffi_part fs *
            W8ARRAY buff257_loc (LUPDATE (1w :word8) 1 (LUPDATE fd 0 bdef))`
  >- (xapp >> simp[buff257_loc] >> xsimpl >> metis_tac[]) >>
  xlet`POSTv d. &NUM (ORD c) d * IOx fs_ffi_part fs *
            W8ARRAY buff257_loc (LUPDATE 1w 1 (LUPDATE fd 0 bdef))`
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xlet_auto >- xsimpl >>
  xlet `POSTv u'. &(UNIT_TYPE () u') * IOx fs_ffi_part fs *
            W8ARRAY buff257_loc (LUPDATE (n2w (ORD c)) 2
                                (LUPDATE (1w :word8) 1 
                                (LUPDATE fd 0 bdef)))`
  >- (xapp >> simp[buff257_loc] >> xsimpl >> metis_tac[]) >>
  cases_on`write (w2n fd) 1 [c] fs`
  (* failed to write case *)
  >- (
    xlet `POSTv u''. &(UNIT_TYPE () u') * IOx fs_ffi_part fs *
            W8ARRAY buff257_loc (LUPDATE (n2w (ORD c)) 2
                                (LUPDATE (1w :word8) 1 
                                (LUPDATE 1w 0 bdef)))`  
    >- (xffi >>
        simp[buff257_loc,cfHeapsBaseTheory.IOx_def,fs_ffi_part_def,
             cfHeapsBaseTheory.mk_ffi_next_def] >>
        xsimpl >>
        qmatch_goalsub_abbrev_tac`IO st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`ns`,`f`, `encode fs`, `st`] >> xsimpl >>
        simp[Abbr`f`,Abbr`st`,Abbr`ns`, cfHeapsBaseTheory.mk_ffi_next_def,
             ffi_write_def, decode_encode_FS,
             MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ,
             implode_explode, LENGTH_explode] >>
        fs[write_def, HD_LUPDATE] >>
        (* TODO: clean this *)
        Cases_on `bdef` >> fs[] >>
        qmatch_goalsub_abbrev_tac`h :: t` >>
        Cases_on `t` >> fs[] >> 
        qmatch_goalsub_abbrev_tac`h :: h' :: t'` >>
        Cases_on`t'` >> fs[] >>
        rw[EVAL ``LUPDATE rr 2 (zz :: tt)``,
           EVAL ``LUPDATE rr 1 (zz :: tt)``, LUPDATE_def] >>
        pairarg_tac >>
        fs[option_eq_some]) >>
    simp[SEP_CLAUSES] >>
    xlet `POSTv g. &WORD (1w :word8) g *
            (IOx fs_ffi_part fs *
            W8ARRAY buff257_loc (LUPDATE (n2w (ORD c)) 2 
                                (LUPDATE 1w 1 
                                (LUPDATE 1w 0 bdef))))`
    >- (xapp >> xsimpl) >>
    xlet `POSTv g. &WORD (1w :word8) g *
            (IOx fs_ffi_part fs *
            W8ARRAY buff257_loc (LUPDATE (n2w (ORD c)) 2 
                                (LUPDATE 1w 1 
                                (LUPDATE 1w 0 bdef))))`
    >- (xapp >> xsimpl >>
        Cases_on `bdef` >> fs[] >>
        qmatch_goalsub_abbrev_tac`h :: t` >>
        Cases_on `t` >> fs[] >> 
        qmatch_goalsub_abbrev_tac`h :: h' :: t'` >>
        Cases_on`t'` >> fs[] >>
        rw[EVAL ``LUPDATE rr 2 (zz :: tt)``,
           EVAL ``LUPDATE rr 1 (zz :: tt)``, LUPDATE_def] >>
        simp[buff257_loc_def,LENGTH_LUPDATE] >> xsimpl) >>
    xlet `POSTv comp. &BOOL TRUE comp * IOx fs_ffi_part fs *
            SEP_EXISTS wl. (W8ARRAY buff257_loc wl * &(LENGTH wl = 257))`
    >- (xapp >> xsimpl >> cheat) >>
        xif >> fs[TRUE_def] >> xlet_auto >- (xcon >> xsimpl) >>
        xraise >> xsimpl >> fs[InvalidFD_exn_def,buff257_loc_def,wfFS_write]

        fs[write_def,get_file_content_def] >> fs[] >>
        pairarg_tac >> 
        `x = (fnm,off)` by (fs[]) >>
        fs[] >> fs[] >>
        >- cheat
        (* fs.numchars = [||] should not happen *)
        >- cheat

        >- cheat
        (* LHD fs.numchars = SOME 0 *)
        fs[]
        (* trivial: fnm = fnm' *)
        
            fs[option_eq_some] >>
            
        >-
        >-

        

        metis_tac[]
        prove_tac[]

        rw[fs_ffi_part_def,cfHeapsBaseTheory.IOx_def,cfHeapsBaseTheory.mk_ffi_next_def]
        rw[cfHeapsBaseTheory.POST_F_def]
        rw[cfHeapsBaseTheory.IO_def]
        rw[IOx]
        fs[write_def,get_file_content_def]
        pairarg_tac
        fs[ALOOKUP_NONE]
        imp_res_tac A_DELKEY_I
        res_tac
        fs[wfFS_def,fsupdate_def]
        imp_res_tac ALOOKUP_SOME_inFS_fname
        res_tac
        
        xif >> 

    >- (
    xret >> 
    xsimpl >> 
    simp[BadFileName_exn_def]) >>

        (* wfFS_write -> wfFS_fsupdate *)
        ) >>
    xcon >> fs[TRUE_def])

    (* success case *)
    cases_on`x` >> rename [`SOME(newb, fs')`]
    xlet`POSTv u'''. 
        &(UNIT_TYPE () u''') * 
        FILE_CONTENT fs' (w2n fd) (LUPDATEcontent ++ [c]) *
        W8ARRAY buff257_loc (LUPDATE (n2w (ORD c)) 2 
            (LUPDATE 1w 1 (LUPDATE 0w 0 bdef)))`
    >- (
    xffi >>
    fs[write_def] >>
    pairarg_tac >>
    simp[buff257_loc,cfHeapsBaseTheory.IOx_def,fs_ffi_part_def,
             cfHeapsBaseTheory.mk_ffi_next_def,FILE_CONTENT_def,
         get_file_content_def,ffi_write_def,MEM_MAP, IOFS_def] >>
    xsimpl >>
    Cases_on `bdef` >> fs[] >>
    qmatch_goalsub_abbrev_tac`h :: t` >>
    Cases_on `t` >> fs[] >> 
    qmatch_goalsub_abbrev_tac`h :: h' :: t'` >>
    Cases_on`t'` >> fs[] >>
    rw[EVAL ``LUPDATE rr 2 (zz :: tt)``,
       EVAL ``LUPDATE rr 1 (zz :: tt)``, LUPDATE_def] >>
    qmatch_goalsub_abbrev_tac`IO st f ns` >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    simp[write_def,MIN_DEF, write_file_def] >>
    qmatch_goalsub_abbrev_tac`wfFS fs'`
    map_every qexists_tac[`ns`,`f`, `encode fs'`, `st`] >> xsimpl >>
    fs[Abbr`f`,Abbr`st`,Abbr`ns`, cfHeapsBaseTheory.mk_ffi_next_def,
       ffi_write_def, decode_encode_FS, MEM_MAP, ORD_BOUND, ORD_eq_0,
       dimword_8, MAP_MAP_o, o_DEF, char_BIJ, implode_explode, 
       LENGTH_explode, IOFS_buff257_def, buff257_loc_def] >>
    xsimpl >>


    qexists_tac `(fnm,off + 1)` >>
    qexists_tac`(0w::1w::n2w (ORD c)::t, fs')` >>
    fs[option_eq_some] >> 
    (* TODO: as lemma *)
    `! fs fd fnm c. wfFS fs ==> wfFS (write_file fs fd fnm c)` by cheat >>
    res_tac >>
    rw[] >>
    >- (fs[LUPDATE_def,write_def,EVAL ``LUPDATE rr 1 (zz :: tt)``,MIN_DEF, 
           write_file_def,Abbr`fs'`,get_file_content_def] >>
        every_case_tac >> fs[] >>
        `strm = 1` by (fs[]) >> simp[]) >>
    >-(fs[Abbr`fs'`,write_file_def,STRLEN_CAT] >> cheat) (* ok *)
    >-(
       simp[ALIST_FUPDKEY_ALOOKUP]         
        
        

    )
val _ = export_theory();


