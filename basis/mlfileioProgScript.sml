open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory mlcharioProgTheory rofsFFITheory
     cfLetAutoTheory cfLetAutoLib

val _ = new_theory"mlfileioProg";
val _ = translation_extends "mlcharioProg";

(* ----------------------------------------------------------------------

    Our operations require memory to be allocated in the heap for the
    passing of parameters:

    1. write requires write_loc for the storage of the character to be
       written
    2. open-file requires filenamae_loc for the storage of the name of the
       (probably zero-terminated) file
    3. read-char needs storage for a single byte for identifying the
       file-descripter to read through. This assumes that there can't
       be more than 256 file-descriptors.  Perhaps we can share write_loc.
    4. close-file also needs a file-descriptor.

    Memory of this sort can be pre-allocated by making calls to AST
    expressions like

      App Aw8alloc [Lit (IntLit sz); Lit (Word8 0w)]

    where sz is the number of bytes needed.

   ---------------------------------------------------------------------- *)

fun basis_st () = get_ml_prog_state ()

val _ = ml_prog_update (open_module "FileIO");

val onechar_e = ``(App Aw8alloc [Lit (IntLit 1); Lit (Word8 0w)])``
val filename_e = ``(App Aw8alloc [Lit (IntLit 256); Lit (Word8 0w)])``

(*
   - onechar_loc is the name of the HOL constant
   - onechar is the name of the binding in the module
*)
val _ = ml_prog_update
          (add_Dlet (derive_eval_thm "onechar_loc" onechar_e) "onechar" [])
val onechar_loc_def = definition "onechar_loc_def"

(* similarly
   - filename_loc is the name of the HOL constant
   - filename_array is the name of the binding in the module
*)
val _ = ml_prog_update
          (add_Dlet
             (derive_eval_thm "filename_loc" filename_e)
             "filename_array"
             [])


val word_eq1_d =
  ``Dletrec unknown_loc [("word_eq1", "w",
              Mat (Var (Short "w"))
                  [(Plit (Word8 1w), Con (SOME (Short "true")) []);
                   (Pvar "_", Con (SOME (Short "false")) [])])]``
val _ = append_dec word_eq1_d

val word_eq1_spec = Q.store_thm(
  "word_eq1_spec",
  `∀w:word8 wv.
     WORD w wv ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "word_eq1" (basis_st())) [wv]
       emp
       (POSTv bv. &BOOL (w = 1w) bv)`,
  rpt strip_tac >> xcf "word_eq1" (basis_st()) >> xmatch >> xsimpl >>
  rw[]
  >- (xret >> xsimpl >> fs[WORD_def])
  >- (xret >> xsimpl >> fs[WORD_def] >> rfs[wordsTheory.w2w_def])
  >- simp[validate_pat_def, pat_typechecks_def, astTheory.pat_bindings_def,
          pat_without_Pref_def, terminationTheory.pmatch_def]
  >- (simp[validate_pat_def, pat_typechecks_def, astTheory.pat_bindings_def,
           pat_without_Pref_def] >>
      fs[WORD_def] >> simp[terminationTheory.pmatch_def] >>
      rw[semanticPrimitivesTheory.lit_same_type_def]))

val word_eqneg1_d =
  ``Dletrec unknown_loc [("word_eqneg1", "w",
              Mat (Var (Short "w"))
                  [(Plit (Word8 255w), Con (SOME (Short "true")) []);
                   (Pvar "_", Con (SOME (Short "false")) [])])]``
val _ = append_dec word_eqneg1_d

val word_eqneg1_spec = Q.store_thm(
  "word_eqneg1_spec",
  `∀w:word8 wv.
     WORD w wv ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "word_eqneg1" (basis_st())) [wv]
       emp
       (POSTv bv. &BOOL (w = 255w) bv)`,
  rpt strip_tac >> xcf "word_eqneg1" (basis_st()) >> xmatch >> xsimpl >>
  rw[]
  >- (xret >> xsimpl >> fs[WORD_def])
  >- (xret >> xsimpl >> fs[WORD_def] >> rfs[wordsTheory.w2w_def])
  >- simp[validate_pat_def, pat_typechecks_def, astTheory.pat_bindings_def,
          pat_without_Pref_def, terminationTheory.pmatch_def]
  >- (simp[validate_pat_def, pat_typechecks_def, astTheory.pat_bindings_def,
           pat_without_Pref_def] >>
      fs[WORD_def] >> simp[terminationTheory.pmatch_def] >>
      rw[semanticPrimitivesTheory.lit_same_type_def]));

val copyi_q =
  `fun copyi a i clist =
      case clist of
          [] => let val z = Word8.fromInt 0 in Word8Array.update a i z end
        | c::cs => let
            val ordc = Char.ord c
            val cw = Word8.fromInt ordc
            val unit = Word8Array.update a i cw
            val suci = i + 1
          in
            copyi a suci cs
          end`
val copyi_d = process_topdecs copyi_q
val _ = append_prog copyi_d

val copyi_spec = Q.store_thm(
  "copyi_spec",
  `∀n nv cs csv a av.
     NUM n nv /\ n + LENGTH cs < LENGTH a /\ LIST_TYPE CHAR cs csv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "copyi" (basis_st()))
       [av; nv; csv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) *
                 W8ARRAY av (insertNTS_atI (MAP (n2w o ORD) cs) n a))`,
  Induct_on `cs` >> fs[LIST_TYPE_def, LENGTH_NIL]
  >- (xcf "copyi" (basis_st()) >> xmatch >>
      xlet `POSTv zv. & WORD (0w:word8) zv * W8ARRAY av a`
      >- (xapp >> xsimpl) >>
      xapp >> xsimpl >> simp[insertNTS_atI_NIL] >> xsimpl >>
      metis_tac[DECIDE ``(x:num) + 1 < y ⇒ x < y``]) >>
  xcf "copyi" (basis_st()) >> xmatch >>
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

val str_to_w8array_q =
  `fun str_to_w8array a s = let
     val clist = String.explode s
   in
      copyi a 0 clist
   end`
val str_to_w8array_d = process_topdecs str_to_w8array_q
val _ = append_prog str_to_w8array_d

val str_to_w8array_spec = Q.store_thm(
  "str_to_w8array_spec",
  `∀s sv a av.
     LENGTH (explode s) < LENGTH a ∧ STRING_TYPE s sv ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "str_to_w8array" (basis_st()))
       [av; sv]
       (W8ARRAY av a)
       (POSTv v.
          cond (UNIT_TYPE () v) *
          W8ARRAY av (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 a))`,
  rpt strip_tac >> xcf "str_to_w8array" (basis_st()) >>
  xlet `POSTv csv. &(LIST_TYPE CHAR (explode s) csv) * W8ARRAY av a`
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xapp >> simp[])

val _ = process_topdecs `
  exception BadFileName;
  exception InvalidFD
` |> append_prog

(* Predicates for exceptions BadFileName and InvalidFD *)
val BadFileName_exn_def = Define `
  BadFileName_exn v =
    (v = Conv (SOME ("BadFileName", TypeExn (Long "FileIO" (Short "BadFileName")))) [])`

val InvalidFD_exn_def = Define `
  InvalidFD_exn v =
    (v = Conv (SOME ("InvalidFD", TypeExn (Long "FileIO" (Short "InvalidFD")))) [])`

(* ML implementation of open function, with parameter name "fname" *)
val openIn_e =
  ``Let (SOME "_")
        (Apps [Var (Short "str_to_w8array");
               Var (Short "filename_array");
               Var (Short "fname")]) (
    Let (SOME "_")
        (App (FFI "open") [Var (Short "filename_array")]) (
    Let (SOME "fd")
        (Apps [Var (Long "Word8Array" (Short "sub")); Var (Short "filename_array");
               Lit (IntLit 0)]) (
    Let (SOME "eqneg1p") (Apps [Var (Short "word_eqneg1"); Var (Short "fd")]) (
    If (Var (Short "eqneg1p"))
       (Let (SOME "e") (Con (SOME (Short "BadFileName")) [])
            (Raise (Var (Short "e"))))
       (Var (Short "fd"))))))``
    |> EVAL |> concl |> rand
val _ = ml_prog_update
          (add_Dlet_Fun ``"openIn"`` ``"fname"`` openIn_e "openIn_v")
val openIn_v_def = definition "openIn_v_def"

(* ML implementation of eof function, with parameter w8 (a fd) *)
val eof_e =
  ``Let (SOME "_") (Apps [Var (Long "Word8Array" (Short "update"));
                          Var (Short "onechar"); Lit (IntLit 0);
                          Var (Short "w8")]) (
    Let (SOME "_") (App (FFI "isEof") [Var (Short "onechar")]) (
    Let (SOME "bw") (Apps [Var (Long "Word8Array" (Short "sub"));
                           Var (Short "onechar"); Lit (IntLit 0)]) (
      Mat (Var (Short "bw")) [
        (Plit (Word8 255w), Raise (Con (SOME (Short "InvalidFD")) []));
        (Pvar "_", Apps [Var (Short "word_eq1"); Var (Short "bw")])
      ]))) ``
  |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"eof"`` ``"w8"`` eof_e "eof_v")

(* ML implementation of fgetc function, with parameter name "fd" *)
val fgetc_e =
  ``Let (SOME "eofp")
        (Apps [Var (Short "eof"); Var (Short "fd")]) (
    If (Var (Short "eofp"))
       (Con (SOME (Short "NONE")) [])
       (Let (SOME "u1")
            (Apps [Var (Long "Word8Array" (Short "update"));
                   Var (Short "onechar");
                   Lit (IntLit 0);
                   Var (Short "fd")]) (
        Let (SOME "u2") (App (FFI "fgetc") [Var (Short "onechar")]) (
        Let (SOME "cw") (Apps [Var (Long "Word8Array" (Short "sub"));
                               Var (Short "onechar"); Lit (IntLit 0)]) (
        Let (SOME "ci") (Apps [Var (Long "Word8" (Short "toInt")); Var (Short "cw")]) (
        Let (SOME "cc") (Apps [Var (Long "Char" (Short"chr")); Var (Short "ci")]) (
          Con (SOME (Short "SOME")) [Var (Short "cc")])))))))``
   |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"fgetc"`` ``"fd"`` fgetc_e "fgetc_v")
val fgetc_v_def = definition "fgetc_v_def"

(* ML implementation of close function, with parameter "w8" *)
val close_e =
  ``Let (SOME "_") (Apps [Var (Long "Word8Array" (Short "update"));
                          Var (Short "onechar");
                          Lit (IntLit 0);
                          Var (Short "w8")]) (
    Let (SOME "u2") (App (FFI "close") [Var (Short "onechar")]) (
    Let (SOME "okw") (Apps [Var (Long "Word8Array" (Short "sub"));
                            Var (Short "onechar");
                            Lit (IntLit 0)]) (
    Let (SOME "ok") (Apps [Var (Short "word_eq1"); Var (Short "okw")]) (
      If (Var (Short "ok"))
         (Con NONE [])
         (Raise (Con (SOME (Short "InvalidFD")) []))))))``
    |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"close"`` ``"w8"`` close_e "close_v")

val ROFS_char1_def = Define `
  ROFS_char1 = SEP_EXISTS w. W8ARRAY onechar_loc [w]`;

val ROFS_fname_def = Define`
  ROFS_fname =
    SEP_EXISTS v. W8ARRAY filename_loc v * cond (LENGTH v = 256)
`;

val ROFS_def = Define `
  ROFS fs = IOx rofs_ffi_part fs * &(wfFS fs) * ROFS_char1 * ROFS_fname`

val onechar_loc = EVAL``onechar_loc``
val filename_loc = EVAL``filename_loc``

val ROFS_precond = Q.prove(
  `wfFS fs ∧ LENGTH v = 256 ⇒
   ROFS fs
    {FFI_part (encode fs) (mk_ffi_next rofs_ffi_part) (MAP FST (SND(SND rofs_ffi_part))) events;
     Mem ^(rand(rand(concl(onechar_loc)))) (W8array [w]);
     Mem ^(rand(rand(concl(filename_loc)))) (W8array v)}`,
  rw[ROFS_def,cfHeapsBaseTheory.IOx_def,rofs_ffi_part_def,cfHeapsBaseTheory.IO_def,ROFS_char1_def,ROFS_fname_def]
  \\ rw[set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,set_sepTheory.SEP_CLAUSES]
  \\ qexists_tac`v`
  \\ rw[cfHeapsBaseTheory.W8ARRAY_def,set_sepTheory.SEP_CLAUSES,
        cfHeapsBaseTheory.cell_def,onechar_loc,filename_loc,
        set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR]
  \\ rw[GSYM STAR_ASSOC]
  \\ rw[set_sepTheory.one_STAR,set_sepTheory.cond_STAR]
  \\ rw[set_sepTheory.one_def]
  \\ rw[DELETE_INSERT]) |> UNDISCH_ALL |> curry save_thm "ROFS_precond";

val FILENAME_def = Define `
  FILENAME s sv =
    (STRING_TYPE s sv ∧
     ¬MEM (CHR 0) (explode s) ∧
     strlen s < 256)
`;

val openIn_spec = Q.store_thm(
  "openIn_spec",
  `∀s sv fs.
     FILENAME s sv ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 255 ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "openIn" (basis_st()))
       [sv]
       (ROFS fs)
       (POST
          (\wv. &(WORD (n2w (nextFD fs) :word8) wv ∧
                  validFD (nextFD fs) (openFileFS s fs) ∧
                  inFS_fname fs s) *
                ROFS (openFileFS s fs))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname fs s) * ROFS fs))`,
  xcf "openIn" (basis_st()) >>
  fs[FILENAME_def, strlen_def, ROFS_def, ROFS_fname_def] >> xpull >>
  rename [`W8ARRAY filename_loc fnm0`] >>
  qmatch_goalsub_abbrev_tac`catfs fs` >>
  xlet `POSTv u. &(UNIT_TYPE () u) * ROFS_char1 *
                 W8ARRAY filename_loc
                         (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0) *
                 catfs fs`
  >- (xapp >> xsimpl >> instantiate >>
      simp[definition "filename_loc_def"] >> xsimpl >>
      Cases_on`s` \\ fs[]) >>
  qabbrev_tac `fnm = insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0` >>
  qmatch_goalsub_abbrev_tac`catfs fs' * _ * _ * _` >>
  Cases_on `inFS_fname fs s`
  >- (
    xlet `POSTv u2.
            &(UNIT_TYPE () u2 /\ nextFD fs < 255 /\
              validFD (nextFD fs) (openFileFS s fs)) *
            ROFS_char1 *
            W8ARRAY filename_loc (LUPDATE (n2w (nextFD fs)) 0 fnm) *
            catfs fs'`
    >- (simp[Abbr`catfs`,Abbr`fs'`] >>
        xffi >> simp[definition "filename_loc_def"] >>
        simp[rofsFFITheory.rofs_ffi_part_def,cfHeapsBaseTheory.IOx_def] >>
        qmatch_goalsub_abbrev_tac`IO st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`ns`,`f`,`encode (openFileFS s fs)`,`st`] >> xsimpl >>
        simp[Abbr`f`,Abbr`st`,Abbr`ns`, cfHeapsBaseTheory.mk_ffi_next_def,
             ffi_open_def, decode_encode_FS, Abbr`fnm`,
             getNullTermStr_insertNTS_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
             implode_explode, LENGTH_explode] >>
        `∃content. ALOOKUP fs.files s = SOME content`
          by (fs[inFS_fname_def, ALOOKUP_EXISTS_IFF, MEM_MAP, EXISTS_PROD] >>
              metis_tac[]) >>
        csimp[nextFD_ltX, openFile_def, openFileFS_def, validFD_def]) >>
    xlet `POSTv fdv. &WORD (n2w (nextFD fs) : word8) fdv *
                     ROFS_char1 *
                     W8ARRAY filename_loc (LUPDATE (n2w (nextFD fs)) 0 fnm) *
                     catfs fs'`
    >- (xapp >> xsimpl >> simp[definition "filename_loc_def"] >> xsimpl >>
        csimp[HD_LUPDATE] >>
        simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]) >>
    xlet `POSTv eqn1v. &BOOL F eqn1v * ROFS_char1 *
                       W8ARRAY filename_loc (LUPDATE (n2w (nextFD fs)) 0 fnm) *
                       catfs fs'`
    >- (xapp >> xsimpl >> qexists_tac `n2w (nextFD fs)` >>
        simp[WORD_def, BOOL_def]) >>
    xif >> instantiate >> xret >> simp[Abbr`catfs`,Abbr`fs'`] >> xsimpl >>
    simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode, wfFS_openFile]
  )
  >- (
    xlet `POSTv u2.
            &UNIT_TYPE () u2 * ROFS_char1 * catfs fs *
            W8ARRAY filename_loc (LUPDATE 255w 0 fnm)`
    >- (simp[Abbr`catfs`,Abbr`fs'`] >> xffi >> simp[definition "filename_loc_def"] >>
        simp[rofsFFITheory.rofs_ffi_part_def,cfHeapsBaseTheory.IOx_def] >>
        qmatch_goalsub_abbrev_tac`IO st f ns` >>
        CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`ns`,`f`,`st`,`st`] >> xsimpl >>
        simp[Abbr`f`,Abbr`st`,Abbr`ns`, cfHeapsBaseTheory.mk_ffi_next_def,
             ffi_open_def, decode_encode_FS, Abbr`fnm`,
             getNullTermStr_insertNTS_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
             implode_explode, LENGTH_explode] >>
        simp[not_inFS_fname_openFile]) >>
    xlet `POSTv fdv. &WORD (255w: word8) fdv *
                     ROFS_char1 * catfs fs *
                     W8ARRAY filename_loc (LUPDATE 255w 0 fnm)`
    >- (xapp >> xsimpl >> simp[definition "filename_loc_def"] >> xsimpl >>
        csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]) >>
    xlet `POSTv eqn1v.
            &BOOL T eqn1v *
            ROFS_char1 * catfs fs *
            W8ARRAY filename_loc (LUPDATE 255w 0 fnm)`
    >- (xapp >> xsimpl >> fs[WORD_def, BOOL_def]) >>
    xif >> instantiate >>
    xlet `POSTv ev.
            &BadFileName_exn ev *
            ROFS_char1 * catfs fs *
            W8ARRAY filename_loc (LUPDATE 255w 0 fnm)`
    >- (xret >> xsimpl >> simp[BadFileName_exn_def]) >>
    xraise >> xsimpl >> simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]
  )
);

val eof_spec = Q.store_thm(
  "eof_spec",
  `∀(w:word8) wv fs.
     WORD w wv ∧ validFD (w2n w) fs  ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "eof" (basis_st()))
       [wv]
       (ROFS fs)
       (POSTv bv.
          &(BOOL (THE (eof (w2n w) fs)) bv) * ROFS fs)`,
  xcf "eof" (basis_st()) >>
  simp[ROFS_def, ROFS_char1_def] >> xpull >>
  rename [`W8ARRAY onechar_loc [byte]`] >>
  qmatch_goalsub_abbrev_tac`CATIO * _ * ROFS_fname` >>
  xlet `POSTv u. &(UNIT_TYPE () u) * ROFS_fname * CATIO *
                 W8ARRAY onechar_loc [w]`
  >- (xapp >> xsimpl >> simp[onechar_loc_def] >> xsimpl >>
      simp[LUPDATE_def]) >>
  xlet `POSTv u. &(UNIT_TYPE () u) * ROFS_fname * CATIO *
                 W8ARRAY onechar_loc [if THE (eof (w2n w) fs) then 1w else 0w]`
  >- (simp[Abbr`CATIO`] >> xffi >> simp[onechar_loc_def] >>
      simp[cfHeapsBaseTheory.IOx_def,rofsFFITheory.rofs_ffi_part_def] >>
      qmatch_goalsub_abbrev_tac`IO st f ns` >>
      CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`ns`,`f`,`st`,`st`] >> xsimpl >>
      map_every qunabbrev_tac[`f`,`ns`,`st`] >>
      csimp[cfHeapsBaseTheory.mk_ffi_next_def, ffi_isEof_def, LUPDATE_def] >>
      simp[eof_def, EXISTS_PROD, PULL_EXISTS] >>
      `∃fnm pos. ALOOKUP fs.infds (w2n w) = SOME (fnm,pos)`
        by (fs[validFD_def, MEM_MAP, EXISTS_PROD] >>
            metis_tac[ALOOKUP_EXISTS_IFF, PAIR, EXISTS_PROD]) >>
      simp[] >>
      `∃conts. ALOOKUP fs.files fnm = SOME conts`
        by (fs[wfFS_def, validFD_def] >> res_tac >> fs[MEM_MAP, EXISTS_PROD] >>
            rw[] >> metis_tac[ALOOKUP_EXISTS_IFF]) >> simp[]) >>
  xlet `POSTv bw. &(WORD (if THE (eof (w2n w) fs) then 1w else 0w:word8) bw) *
                  CATIO * ROFS_fname *
                  W8ARRAY onechar_loc [if THE (eof (w2n w) fs) then 1w else 0w]`
  >- (xapp >> simp[onechar_loc_def] >> xsimpl) >>
  xmatch >>
  `bw ≠ Litv (Word8 255w)`
     by (strip_tac >> fs[WORD_def, w2w_def, bool_case_eq]) >> simp[] >>
  simp[validate_pat_def, pat_typechecks_def, pat_without_Pref_def,
       terminationTheory.pmatch_def, astTheory.pat_bindings_def] >>
  reverse conj_tac
  >- (fs[WORD_def] >>
      simp[terminationTheory.pmatch_def, w2w_def, bool_case_eq,
           semanticPrimitivesTheory.lit_same_type_def]) >>
  xapp >> xsimpl >>
  qexists_tac `if THE (eof (w2n w) fs) then 1w else 0w` >> rw[]);

val fgetc_spec = Q.store_thm(
  "fgetc_spec",
  `∀(fdw:word8) fdv fs.
     WORD fdw fdv ∧ validFD (w2n fdw) fs ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "fgetc" (basis_st())) [fdv]
       (ROFS fs)
       (POSTv coptv.
          &(OPTION_TYPE CHAR (FDchar (w2n fdw) fs) coptv) *
          ROFS (bumpFD (w2n fdw) fs))`,
  rpt strip_tac >> xcf "fgetc" (basis_st()) >>
  simp[ROFS_def] >> xpull >>
  qabbrev_tac `catfs = λfs. IOx rofs_ffi_part fs` >> simp[] >>
  `∃eofb. eof (w2n fdw) fs = SOME eofb` by metis_tac[wfFS_eof_EQ_SOME] >>
  xlet `POSTv bv. &(BOOL eofb bv) * catfs fs * ROFS_char1 * ROFS_fname`
  >- (xapp >> simp[onechar_loc_def, ROFS_def] >> xsimpl >> instantiate >>
      xsimpl) >>
  xif >- (xret >> fs[eof_FDchar, eof_bumpFD, OPTION_TYPE_def] >> xsimpl) >>
  fs[] >>
  simp[ROFS_char1_def] >> xpull >>
  xlet `POSTv u1. W8ARRAY onechar_loc [fdw] * catfs fs * ROFS_fname`
  >- (xapp >> simp[onechar_loc_def] >> xsimpl >>
      simp[LUPDATE_def]) >>
  `∃c. FDchar (w2n fdw) fs = SOME c` by metis_tac[neof_FDchar] >> simp[] >>
  xlet `POSTv u2. &UNIT_TYPE () u2 * catfs (bumpFD (w2n fdw) fs) *
                  ROFS_fname * W8ARRAY onechar_loc [n2w (ORD c)]`
  >- (xffi >> simp[onechar_loc_def, Abbr`catfs`] >> xsimpl >>
      (* TODO: this should be automatable without expanding IOx *)
      simp[cfHeapsBaseTheory.IOx_def,rofs_ffi_part_def] >>
      qmatch_goalsub_abbrev_tac`IO s u ns` >>
      CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`ns`,`u`,`encode (bumpFD (w2n fdw) fs)`,`s`] >>
      xsimpl >>
      simp[Abbr`s`,Abbr`u`,Abbr`ns`,
           cfHeapsBaseTheory.mk_ffi_next_def, EXISTS_PROD, ffi_fgetc_def,fgetc_def]) >>
  xlet `POSTv x. &WORD ((n2w (ORD c)):word8) x * catfs (bumpFD (w2n fdw) fs) *
                 ROFS_fname * W8ARRAY onechar_loc [n2w (ORD c)]`
  >- (xapp >> simp[onechar_loc_def,Abbr`catfs`] >> xsimpl ) >>
  xlet `POSTv x. &NUM (ORD c) x * catfs (bumpFD (w2n fdw) fs) *
                 ROFS_fname * W8ARRAY onechar_loc [n2w (ORD c)]`
  >- (xapp >> simp[onechar_loc_def,Abbr`catfs`] >> xsimpl >>
      instantiate >> simp[ORD_BOUND]) >>
  xlet `POSTv cwv.
         &(CHAR c cwv) * ROFS_fname *
         W8ARRAY onechar_loc [n2w (ORD c)] * catfs (bumpFD (w2n fdw) fs)`
  >- (xapp >> simp[onechar_loc_def] >> xsimpl >>
      instantiate >> simp[ORD_BOUND,CHR_ORD]) >>
  xret >> xsimpl >> simp[OPTION_TYPE_def])

val close_spec = Q.store_thm(
  "close_spec",
  `∀(fdw:word8) fdv fs.
     WORD fdw fdv ∧ validFD (w2n fdw) fs ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "close" (basis_st())) [fdv]
       (ROFS fs)
       (POSTv u. &UNIT_TYPE () u *
                 ROFS (fs with infds updated_by A_DELKEY (w2n fdw)))`,
  rpt strip_tac >>
  xcf "close" (basis_st()) >> simp[ROFS_def, ROFS_char1_def] >>
  xpull >>
  qabbrev_tac `catfs = IOx rofs_ffi_part` >> simp[] >>
  xlet `POSTv u.
         &UNIT_TYPE () u * W8ARRAY onechar_loc [fdw] * ROFS_fname * catfs fs`
  >- (xapp >> simp[onechar_loc_def] >> xsimpl >> simp[LUPDATE_def]) >>
  xlet `POSTv u2.
          &UNIT_TYPE () u2 * W8ARRAY onechar_loc [1w] * ROFS_fname *
          catfs (fs with infds updated_by A_DELKEY (w2n fdw))`
  >- (simp[Abbr`catfs`] >> xffi >> simp[onechar_loc_def] >> xsimpl >>
      simp[cfHeapsBaseTheory.IOx_def,rofs_ffi_part_def] >>
      qmatch_goalsub_abbrev_tac`IO s f ns` >>
      CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
      qmatch_goalsub_abbrev_tac`_ ==>> _ * IO s' _ _` >>
      map_every qexists_tac[`ns`,`f`,`s'`,`s`] >>
      xsimpl >>
      simp[Abbr`f`,Abbr`ns`,Abbr`s'`,Abbr`s`,cfHeapsBaseTheory.mk_ffi_next_def] >>
      simp[ffi_close_def, wfFS_DELKEY, closeFD_def, EXISTS_PROD] >>
      `∃p. ALOOKUP fs.infds (w2n fdw) = SOME p`
        by (fs[validFD_def, MEM_MAP, EXISTS_PROD] >>
            metis_tac[PAIR,EXISTS_PROD, ALOOKUP_EXISTS_IFF]) >>
      simp[LUPDATE_def, RO_fs_component_equality]) >>
  qabbrev_tac `fs' = fs with infds updated_by A_DELKEY (w2n fdw)` >>
  xlet `POSTv okwv. &WORD (1w:word8) okwv * ROFS fs'`
  >- (simp[ROFS_def,Abbr`catfs`,ROFS_char1_def] >> xapp >> simp[onechar_loc_def] >>
      xsimpl >> simp[Abbr`fs'`]) >>
  simp[GSYM ROFS_char1_def] >>
  xlet `POSTv okbv. &BOOL T okbv * ROFS fs'`
  >- (xapp >> xsimpl >> qexists_tac `1w` >> simp[]) >>
  xif >> qexists_tac `T` >> simp[Abbr`catfs`,ROFS_def] >>
  xpull >> xret >> xsimpl);

val eq_char_v_thm =
  mlbasicsProgTheory.eq_v_thm
  |> DISCH_ALL
  |> C MATCH_MP (ml_translatorTheory.EqualityType_NUM_BOOL
                 |> CONJUNCTS |> el 5)

val inputLine = process_topdecs`
  fun inputLine fd =
    let
      fun loop acc =
        case fgetc fd of
          NONE => #"\n"::acc
        | SOME c => if c = #"\n" then c::acc else loop (c::acc)
    in
      case fgetc fd of NONE => NONE
      | SOME c => if c = #"\n" then SOME (String.str c)
                  else SOME (String.implode (List.rev (loop [c])))
    end`;
val _ = append_prog inputLine;

val inputLine_spec = Q.store_thm("inputLine_spec",
  `∀fd fdv.
    WORD (fd:word8) fdv ∧ validFD (w2n fd) fs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "inputLine" (get_ml_prog_state())) [fdv]
      (ROFS fs)
      (POSTv sov. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs)) sov *
                  ROFS (bumpLineFD (w2n fd) fs))`,
  rw[]
  \\ xcf"inputLine"(get_ml_prog_state())
  \\ xfun_spec `loop`
    `!ls acc accv fs.
       LIST_TYPE CHAR acc accv ∧ validFD (w2n fd) fs ∧
       (ls = case FDline (w2n fd) fs of NONE => "\n" | SOME ls => ls)
       ⇒
       app p loop [accv]
         (ROFS fs)
         (POSTv lv. &LIST_TYPE CHAR (REVERSE ls ++ acc) lv *
            ROFS (bumpLineFD (w2n fd) fs))`
  >- (
    ho_match_mp_tac list_INDUCT
    \\ qpat_x_assum`_ fs`kall_tac
    \\ conj_tac
    >- (
      ntac 2 gen_tac \\ qx_gen_tac`fs`
      \\ CASE_TAC
      \\ strip_tac \\ rveq
      \\ fs[FDline_def]
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[] )
    \\ gen_tac \\ strip_tac
    \\ qx_gen_tac`h`
    \\ ntac 2 gen_tac \\ qx_gen_tac`fs`
    \\ CASE_TAC \\ strip_tac \\ rveq
    >- (
      first_x_assum match_mp_tac
      \\ xlet`POSTv x. &OPTION_TYPE CHAR (FDchar (w2n fd) fs) x *
                       ROFS (bumpFD (w2n fd) fs)`
      >- (xapp \\ rw[])
      \\ xmatch
      \\ rfs[GSYM FDchar_FDline_NONE]
      \\ fs[ml_translatorTheory.OPTION_TYPE_def]
      \\ reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
      \\ xcon
      \\ fs[ml_translatorTheory.LIST_TYPE_def]
      \\ fs[bumpFD_def,bumpLineFD_def]
      \\ fs[FDchar_FDline_NONE]
      \\ xsimpl )
    \\ last_x_assum match_mp_tac
    \\ xlet`POSTv x. &OPTION_TYPE CHAR (FDchar (w2n fd) fs) x *
                     ROFS (bumpFD (w2n fd) fs)`
    >- (xapp \\ rw[])
    \\ xmatch
    \\ Cases_on`FDchar (w2n fd) fs` \\ fs[ml_translatorTheory.OPTION_TYPE_def]
    >- fs[FDchar_FDline_NONE]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
    \\ rename1`CHAR c cv`
    \\ xlet`POSTv bv. &BOOL(c = #"\n") bv * ROFS (bumpFD (w2n fd)fs)`
    >- ( xapp_spec eq_char_v_thm \\ instantiate \\ xsimpl )
    \\ imp_res_tac FDchar_SOME_IMP_FDline
    \\ fs[] \\ rveq
    \\ xif
    >- (
      xcon
      \\ fs[bumpFD_def,bumpLineFD_def,FDchar_def,FDline_def]
      \\ fs[] \\ rveq
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[]
      \\ rveq
      \\ simp[ALIST_FUPDKEY_ALOOKUP]
      \\ Cases_on`l` \\ rveq
      >- (
        qpat_x_assum`_ = #"\n" :: _`mp_tac
        \\ simp[] \\ strip_tac \\ rveq
        \\ full_simp_tac std_ss [] \\ rfs[] \\ rveq
        \\ simp[ml_translatorTheory.LIST_TYPE_def]
        \\ qmatch_goalsub_abbrev_tac`_ o xx`
        \\ `xx = I`
        by (
          rw[Abbr`xx`,FUN_EQ_THM]
          \\ match_mp_tac ALIST_FUPDKEY_unchanged
          \\ simp[FORALL_PROD] )
        \\ xsimpl)
      \\ fs[] \\ rveq
      \\ imp_res_tac SPLITP_IMP
      \\ fs[])
    \\ xlet`POSTv x. &LIST_TYPE CHAR (c::acc) x * ROFS (bumpFD (w2n fd) fs)`
    >- ( xcon \\ simp[ml_translatorTheory.LIST_TYPE_def] \\ xsimpl )
    \\ xapp \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ imp_res_tac validFD_bumpFD
    \\ instantiate
    \\ imp_res_tac FDline_bumpFD
    \\ CASE_TAC \\ fs[] \\ rveq
    \\ xsimpl
    \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] )
  \\ xlet`POSTv x. &OPTION_TYPE CHAR (FDchar (w2n fd) fs) x *
                   ROFS (bumpFD (w2n fd) fs)`
  >- (xapp \\ rw[])
  \\ xmatch
  \\ Cases_on`FDchar (w2n fd) fs` \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  >- (
    reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
    \\ xcon
    \\ fs[FDchar_FDline_NONE,ml_translatorTheory.OPTION_TYPE_def]
    \\ simp[bumpFD_def,bumpLineFD_def]
    \\ fs[GSYM FDchar_FDline_NONE]
    \\ xsimpl )
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ rename1`CHAR c cv`
  \\ xlet`POSTv bv. &BOOL(c = #"\n") bv * ROFS (bumpFD (w2n fd)fs)`
  >- ( xapp_spec eq_char_v_thm \\ instantiate \\ xsimpl )
  \\ xif
  >- (
    xlet`POSTv sv. &STRING_TYPE (str c) sv * ROFS (bumpFD (w2n fd) fs)`
    >- ( xapp \\ instantiate \\ xsimpl )
    \\ xcon
    \\ fs[FDchar_def,FDline_def]
    \\ pairarg_tac \\ fs[]
    \\ Cases_on`DROP off content` \\ fs[DROP_NIL]
    \\ simp[SPLITP] \\ rfs[DROP_CONS_EL]
    \\ simp[ml_translatorTheory.OPTION_TYPE_def]
    \\ fs[mlstringTheory.str_def]
    \\ fs[bumpFD_def,bumpLineFD_def,FDchar_def,FDline_def,DROP_CONS_EL,SPLITP]
    \\ simp[ALIST_FUPDKEY_ALOOKUP]
    \\ qmatch_goalsub_abbrev_tac`_ o xx`
    \\ `xx = I`
    by (
      rw[Abbr`xx`,FUN_EQ_THM]
      \\ match_mp_tac ALIST_FUPDKEY_unchanged
      \\ simp[FORALL_PROD] )
    \\ xsimpl)
  \\ xlet`POSTv x. &LIST_TYPE CHAR [] x * ROFS (bumpFD (w2n fd) fs)`
  >- (xcon \\ simp[ml_translatorTheory.LIST_TYPE_def] \\ xsimpl)
  \\ xlet`POSTv accv. &LIST_TYPE CHAR [c] accv * ROFS (bumpFD (w2n fd) fs)`
  >- (xcon \\ fs[ml_translatorTheory.LIST_TYPE_def] \\ xsimpl)
  \\ first_x_assum drule
  \\ imp_res_tac validFD_bumpFD
  \\ disch_then drule
  \\ imp_res_tac FDchar_SOME_IMP_FDline
  \\ imp_res_tac FDline_bumpFD
  \\ qmatch_goalsub_abbrev_tac`REVERSE l`
  \\ `l = ls`
  by ( unabbrev_all_tac \\ CASE_TAC \\ fs[] )
  \\ fs[] \\ ntac 2 (pop_assum kall_tac)
  \\ simp[GSYM SNOC_APPEND]
  \\ once_rewrite_tac[GSYM (CONJUNCT2 REVERSE)]
  \\ strip_tac
  \\ xlet`POSTv v. &LIST_TYPE CHAR (REVERSE (c::ls)) v *
                   ROFS (bumpLineFD (w2n fd) fs)`
  >- (xapp \\ xsimpl)
  \\ xlet`POSTv lv. &LIST_TYPE CHAR (c::ls) lv * ROFS (bumpLineFD (w2n fd) fs)`
  >- ( xapp_spec (INST_TYPE[alpha|->``:char``]mllistProgTheory.reverse_v_thm)
       \\ instantiate \\ xsimpl \\ simp[REVERSE_APPEND] )
  \\ xlet`POSTv sv. &STRING_TYPE (implode (c::ls)) sv * ROFS (bumpLineFD (w2n fd) fs)`
  >- (xapp \\ instantiate \\ xsimpl )
  \\ xcon \\ simp[ml_translatorTheory.OPTION_TYPE_def] \\ xsimpl);

val _ = (append_prog o process_topdecs) `
  fun inputLines fd =
    case inputLine fd of
        NONE => []
      | SOME l => l::inputLines fd`

val inputLines_spec = Q.store_thm("input_lines_spec",
  `∀fnm fnv fs.
   WORD (fd:word8) fdv ∧ validFD (w2n fd) fs ⇒
   app (p:'ffi ffi_proj)
     ^(fetch_v "inputLines"(get_ml_prog_state())) [fdv]
     (ROFS fs)
     (POSTv fcv.
       &LIST_TYPE STRING_TYPE (MAP (\x. strcat (implode x) (implode "\n")) (linesFD (w2n fd) fs)) fcv *
       ROFS (bumpAllFD (w2n fd) fs))`,
  Induct_on`linesFD (w2n fd) fs` \\ rw[]
  >- (qpat_x_assum`[] = _`(assume_tac o SYM) \\ fs[]
      \\ xcf"inputLines"(get_ml_prog_state())
      \\ xlet`POSTv x. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs))  x *
                     ROFS (bumpLineFD (w2n fd) fs)`
      >- (xapp \\ fs[])
      \\ rfs[GSYM FDline_NONE_linesFD,ml_translatorTheory.OPTION_TYPE_def]
      \\ xmatch
      \\ xcon
      \\ imp_res_tac FDline_NONE_bumpAll_bumpLine
      \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def])
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM) \\ fs[]
  \\ xcf"inputLines"(get_ml_prog_state())
  \\ xlet`POSTv x. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs))  x *
                   ROFS (bumpLineFD (w2n fd) fs)`
  >- ( xapp \\ fs[] )
  \\ Cases_on`FDline (w2n fd) fs` \\ fs[FDline_NONE_linesFD]
  \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ drule linesFD_eq_cons_imp \\ strip_tac \\ fs[] \\ rveq
  \\ rename1`FDline _ _ = SOME ln`
  \\ rveq
  \\ xlet `POSTv fcv.
     &LIST_TYPE STRING_TYPE
        (MAP (λx. implode x ^ implode "\n") (linesFD (w2n fd) (bumpLineFD (w2n fd) fs)))
        fcv * ROFS (bumpAllFD (w2n fd) (bumpLineFD (w2n fd) fs))`
  >- (xapp  \\ xsimpl \\ simp[validFD_bumpLineFD])
  \\ xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def]
  \\ fs[mlstringTheory.implode_def,ml_translatorTheory.STRING_TYPE_def,mlstringTheory.strcat_def]
  \\ drule linesFD_eq_cons_imp \\ fs[]);

val _ = (append_prog o process_topdecs) `
  fun inputLinesFrom fname =
    let
      val fd = openIn fname
      val lines = inputLines fd
    in
      close fd; SOME lines
    end handle BadFileName => NONE`

val all_lines_def = Define
  `all_lines fs fname = MAP (\x. strcat (implode x) (implode "\n"))
                            (splitlines (THE (ALOOKUP fs.files fname)))`

val concat_all_lines = Q.store_thm("concat_all_lines",
  `concat (all_lines fs fname) = implode (THE (ALOOKUP fs.files fname)) ∨
   concat (all_lines fs fname) = implode (THE (ALOOKUP fs.files fname)) ^ str #"\n"`,
  rw[all_lines_def] \\
  qspec_tac(`THE (ALOOKUP fs.files fname)`,`ls`) \\
  Induct_on`splitlines ls` \\ rw[] \\
  pop_assum(assume_tac o SYM) \\
  fs[splitlines_eq_nil,concat_def] \\
  imp_res_tac splitlines_next \\ rw[] \\
  first_x_assum(qspec_then`DROP (SUC (LENGTH h)) ls`mp_tac) \\
  rw[] \\ rw[]
  >- (
    Cases_on`LENGTH h < LENGTH ls` \\ fs[] >- (
      disj1_tac \\
      rw[strcat_def] \\ AP_TERM_TAC \\
      fs[IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG,ADD1] ) \\
    fs[DROP_LENGTH_TOO_LONG] \\
    fs[IS_PREFIX_APPEND,strcat_def] \\ rw[] \\ fs[] \\
    EVAL_TAC )
  >- (
    disj2_tac \\
    rw[strcat_def] \\
    AP_TERM_TAC \\ rw[] \\
    Cases_on`LENGTH h < LENGTH ls` \\
    fs[IS_PREFIX_APPEND,DROP_APPEND,ADD1,DROP_LENGTH_TOO_LONG]  \\
    qpat_x_assum`concat [] = _`mp_tac \\ EVAL_TAC ));

val inputLinesFrom_spec = Q.store_thm("inputLinesFrom_spec",
  `FILENAME f fv /\
   CARD (FDOM (alist_to_fmap fs.infds)) < 255
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"inputLinesFrom"(get_ml_prog_state()))
     [fv]
     (ROFS fs)
     (POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
            (if inFS_fname fs f then
               SOME(all_lines fs f)
             else NONE) sv
             * ROFS fs)`,
  PURE_REWRITE_TAC [all_lines_def]
  \\ xcf"inputLinesFrom"(get_ml_prog_state())
  \\ reverse(xhandle`POST
       (λv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
         (if inFS_fname fs f then SOME(MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files f)))) else NONE) v * ROFS fs)
       (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs f) * ROFS fs)`)
  >- (xcases \\ fs[BadFileName_exn_def]
      \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
      \\ xcon \\ xsimpl \\ fs[ml_translatorTheory.OPTION_TYPE_def])
  >- xsimpl
  \\ xlet`POST (λv. &(WORD ((n2w (nextFD fs)):word8) v ∧ validFD (nextFD fs) (openFileFS f fs) ∧
                      inFS_fname fs f) * ROFS (openFileFS f fs))
               (λe. &(BadFileName_exn e ∧ ¬inFS_fname fs f) * ROFS fs)`
  >- (xapp \\ fs[])
  >- xsimpl
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE (MAP (\x. strcat (implode x) (implode "\n")) (splitlines (THE (ALOOKUP fs.files f)))) v * ROFS (bumpAllFD (nextFD fs) (openFileFS f fs))`
  >- (xapp \\ instantiate \\ qexists_tac `emp` \\ qexists_tac `openFileFS f fs`
      \\ fs[FDOM_alist_to_fmap] \\ drule (GEN_ALL nextFD_ltX) \\ strip_tac
      \\ fs[] \\ xsimpl
      \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS \\ fs[]
      \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD \\ simp[linesFD_def]
      \\ Cases_on`0 < LENGTH content` \\ fs[libTheory.the_def,LENGTH_NIL])
  \\ xlet`POSTv v. &UNIT_TYPE () v * ROFS fs`
  >- (fs[FDOM_alist_to_fmap] \\ imp_res_tac nextFD_ltX
      \\ xapp \\ qexists_tac `emp` \\ qexists_tac `bumpAllFD (nextFD fs) (openFileFS f fs)`
      \\ instantiate \\ xsimpl
      \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
      \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD \\ simp[linesFD_def]
      \\ fs[bumpAllFD_def,libTheory.the_def]
      \\ fs[openFileFS_def,openFile_def,A_DELKEY_def]
      \\ rpt (pop_assum kall_tac)
      \\ `FILTER (λp. FST p ≠ nextFD fs) fs.infds = fs.infds`
          suffices_by(fs[] \\ Cases_on `fs` \\ fs[RO_fs_fn_updates] \\ xsimpl)
      \\ assume_tac nextFD_NOT_MEM
      \\ fs[FILTER_EQ_ID,EVERY_MEM] \\ rpt strip_tac
      \\ Cases_on `p` \\ Cases_on `r` \\ fs[] \\ rfs[])
  \\ xcon \\ xsimpl \\ fs[ml_translatorTheory.OPTION_TYPE_def]);

val _ = ml_prog_update (close_module NONE);

(* xlet_auto *)
val UNIQUE_ROFS = Q.store_thm("UNIQUE_ROFS[hprop_inj]",
`!s fs1 fs2 H1 H2. VALID_HEAP s ==> (ROFS fs1 * H1) s /\ (ROFS fs2 * H2) s ==> fs2 = fs1`,
rw[ROFS_def, cfHeapsBaseTheory.IOx_def, rofs_ffi_part_def, GSYM STAR_ASSOC] >>
IMP_RES_TAC FRAME_UNIQUE_IO >>
fs[]);

(* TODO: make the rewriting/equality type instantiation/... more flexible so that we only need to add a theorem of the form: `FILENAME f fv ==> STRING_TYPE f fv` *)
val filename_tac = metis_tac[FILENAME_def, EqualityType_NUM_BOOL, EqualityType_def];

val FILENAME_UNICITY_R = Q.store_thm("FILENAME_UNICITY_R[xlet_auto_match]",
`!f fv fv'. FILENAME f fv ==> (FILENAME f fv' <=> fv' = fv)`,
filename_tac);

val FILENAME_UNICITY_L = Q.store_thm("FILENAME_UNICITY_L[xlet_auto_match]",
`!f f' fv. FILENAME f fv ==> (FILENAME f' fv <=> f' = f)`,
filename_tac);

val FILENAME_STRING_UNICITY_R = Q.store_thm("FILENAME_STRING_UNICITY_R[xlet_auto_match]",
`!f fv fv'. FILENAME f fv ==> STRING_TYPE f fv ==> (STRING_TYPE f fv' <=> fv' = fv)`,
filename_tac);

val FILENAME_STRING_UNICITY_L = Q.store_thm("FILENAME_STRING_UNICITY_L[xlet_auto_match]",
`!f f' fv. FILENAME f fv ==> STRING_TYPE f fv ==> (STRING_TYPE f' fv <=> f' = f)`,
filename_tac);

val STRING_FILENAME_UNICITY_R = Q.store_thm("STRING_FILENAME_UNICITY_R[xlet_auto_match]",
`!f fv fv'. STRING_TYPE f fv ==> FILENAME f fv ==> (FILENAME f fv' <=> fv' = fv)`,
filename_tac);

val STRING_FILENAME_UNICITY_L = Q.store_thm("STRING_FILENAME_UNICITY_L[xlet_auto_match]",
`!f f' fv. STRING_TYPE f fv ==> FILENAME f fv ==> (FILENAME f' fv <=> f' = f)`,
filename_tac);

val _ = export_theory();
