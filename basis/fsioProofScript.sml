open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory fsFFITheory fsFFIProofTheory fsioProgTheory

val _ = new_theory"fsioProof";

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
  xlet `POSTv oc. &(NUM (ORD chd)) oc * W8ARRAY av a`
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xlet `POSTv cw. &(WORD (n2w (ORD chd) : word8) cw) * W8ARRAY av a`
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xlet `POSTv u. &(UNIT_TYPE () u) * W8ARRAY av (LUPDATE (n2w (ORD chd)) n a)`
  >- (xapp >> simp[]) >>
  qabbrev_tac `a0 = LUPDATE (n2w (ORD chd)) n a` >>
  xlet `POSTv si. &(NUM (n + 1) si) * W8ARRAY av a0`
  >- (xapp >> xsimpl >> qexists_tac `&n` >>
      fs[ml_translatorTheory.NUM_def, integerTheory.INT_ADD]) >>
  xapp >> xsimpl >> qexists_tac `n + 1` >>
  simp[insertNTS_atI_CONS, Abbr`a0`, LUPDATE_insertNTS_commute]);

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
  xlet `POSTv csv. &(LIST_TYPE CHAR (explode s) csv) * W8ARRAY av a`
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xapp >> simp[])

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
  xlet `IOFS fs *
        (POSTv u2. &(UNIT_TYPE () u2) *
            W8ARRAY buff257_loc (LUPDATE (n2w fd) 0 bdef))`
  >- (
    xlet `POSTv u2.
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
    xlet `POSTv ev.
            &BadFileName_exn ev *catfs fs *
            W8ARRAY buff257_loc (LUPDATE 255w 0 fnm)`
    >- (xret >> xsimpl >> simp[BadFileName_exn_def]) >>
    xraise >> xsimpl >> simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]
  )
);

(*
  process_topdecs` fun write_char fd c = 
    let val a = Word8Array.update buff257 0 fd
        val a = Word8Array.update buff257 1 (Word8.fromInt 1) 
        val a = Word8Array.update buff257 2 (Word8.fromInt(ord c))
        val a = #(write) buff257
    in 
      if Word8Array.sub buff257 0 = Word8.fromInt 1 
      then raise InvalidFD (* inaccurate *)
      else ()
    end *)
(*
*     app (p:'ffi ffi_proj) ^(fetch_v "IO.open_in" (basis_st()))
       [sv]
       (IOFS fs)

* POST
          (\wv. &(WORD (n2w (nextFD fs) :word8) wv ∧
                  validFD (nextFD fs) (openFileFS s fs 0) ∧
                  inFS_fname fs s) *
                IOFS (openFileFS s fs 0))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s) * IOFS fs)*)

val write_char_spec = Q.store_thm("write_char_spec",
  `!fd fdv c cv bc. CHAR c cv ⇒ WORD fd fdv ⇒ validFD (w2n fd) fs ⇒
                    app (p:'ffi ffi_proj) ^(fetch_v "IO.write_char" (basis_st())) [fdv; cv]
   (IOFS fs)
   (POST (\uv. &(UNIT_TYPE () uv) ) (\e. &(InvalidFD_exn e) * IOFS fs ))`,

  xcf "IO.write_char" (basis_st()) >> 
  fs[IOFS_def, IOFS_buff257_def] >> xpull >>
  rename [`W8ARRAY buff257_loc bdef`] >>
  xlet `POSTv u. &(UNIT_TYPE () u) * 
            W8ARRAY buff257_loc (LUPDATE (n2w fd) 0 bdef)`


  fs[FILENAME_def, strlen_def, IOFS_def, IOFS_buff257_def] >> xpull >>
  qmatch_goalsub_abbrev_tac`catfs fs` >>
  xlet `POSTv u. &(UNIT_TYPE () u) * W8ARRAY buff257_loc
          (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0) *
                 catfs fs`
  >- (xapp >> xsimpl >> instantiate >>
      simp[fsioProgTheory.buff257_loc_def] >> xsimpl >>
      Cases_on`s` \\ fs[]) >>
  qabbrev_tac `fnm = insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0` >>
  qmatch_goalsub_abbrev_tac`catfs fs' * _ * _` >>

  xlet `POSTv u. &(UNIT_TYPE () u) * W8ARRAY buff257_loc
          (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0) *
                 catfs fs`
val _ = export_theory();
