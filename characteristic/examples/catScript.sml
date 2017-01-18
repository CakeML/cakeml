open preamble
     semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     catfileSystemTheory mlcharioProgTheory basisFunctionsLib

val _ = new_theory "cat"

(* TODO: move *)
val ORD_eq_0 = Q.store_thm(
  "ORD_eq_0",
  `(ORD c = 0 ⇔ c = CHR 0) ∧ (0 = ORD c ⇔ c = CHR 0)`,
  metis_tac[char_BIJ, ORD_CHR, EVAL ``0n < 256``]);

val HD_LUPDATE = Q.store_thm(
  "HD_LUPDATE",
  `0 < LENGTH l ⇒ HD (LUPDATE x p l) = if p = 0 then x else HD l`,
  Cases_on `l` >> rw[LUPDATE_def] >> Cases_on `p` >> fs[LUPDATE_def]);

val ALIST_FUPDKEY_unchanged = Q.store_thm(
  "ALIST_FUPDKEY_unchanged",
  `ALOOKUP alist k = SOME v ∧ f v = v ⇒ ALIST_FUPDKEY k f alist = alist`,
  Induct_on `alist`>> simp[FORALL_PROD, ALIST_FUPDKEY_def] >> rw[]);

val ALIST_FUPDKEY_o = Q.store_thm(
  "ALIST_FUPDKEY_o",
  `ALIST_FUPDKEY k f1 (ALIST_FUPDKEY k f2 al) = ALIST_FUPDKEY k (f1 o f2) al`,
  Induct_on `al` >> simp[ALIST_FUPDKEY_def, FORALL_PROD] >>
  rw[ALIST_FUPDKEY_def]);
(* -- *)

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

val _ = translation_extends"mlcharioProg";

fun basis_st () = get_ml_prog_state ()

(* TODO: move? *)
val LENGTH_explode = Q.store_thm("LENGTH_explode",
  `LENGTH (explode s) = strlen s`,
  Cases_on`s` \\ simp[]);

val parse_t =
  ``λs. case peg_exec cmlPEG (nt (mkNT nDecl) I) (lexer_fun s) [] done failed of
          Result (SOME(_,[x])) => ptree_Decl x``
fun ParseDecl [QUOTE s] =
  EVAL (mk_comb(parse_t, stringSyntax.fromMLstring s))
       |> concl |> rhs |> rand
(* -- *)

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
  ``Dletrec [("word_eq1", "w",
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
  ``Dletrec [("word_eqneg1", "w",
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
val copyi_d = ParseDecl copyi_q
val _ = append_dec copyi_d

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
val str_to_w8array_d = ParseDecl str_to_w8array_q
val _ = append_dec str_to_w8array_d

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

(* not used - using CharIO.write directly (which takes a byte)
(* ML implementation of write function, with parameter "c" (type char) *)
val write_e =
  ``LetApps "ci" (Long "Char" "ord") [Var (Short "c")] (
    LetApps "cw" (Long "Word8" "fromInt") [Var(Short "ci")] (
    LetApps "u1" (Long "Word8Array" "update")
                 [Var (Short "onechar"); Lit (IntLit 0); Var (Short "cw")] (
    Let (SOME "_") (App (FFI "write") [Var (Short "onechar")])
        (Con NONE []))))``
  |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"write"`` ``"c"`` write_e "write_v")
*)

val _ = process_topdecs `
  exception BadFileName;
  exception InvalidFD
` |> append_prog

(* Predicates for exceptions BadFileName and InvalidFD *)
val BadFileName_exn_def = Define `
  BadFileName_exn v =
    (v = Conv (SOME ("BadFileName", TypeExn (Long "FileIO" "BadFileName"))) [])`

val InvalidFD_exn_def = Define `
  InvalidFD_exn v =
    (v = Conv (SOME ("InvalidFD", TypeExn (Long "FileIO" "InvalidFD"))) [])`

(* ML implementation of open function, with parameter name "fname" *)
val openIn_e =
  ``Let (SOME "_")
        (Apps [Var (Short "str_to_w8array");
               Var (Short "filename_array");
               Var (Short "fname")]) (
    Let (SOME "_")
        (App (FFI "open") [Var (Short "filename_array")]) (
    Let (SOME "fd")
        (Apps [Var (Long "Word8Array" "sub"); Var (Short "filename_array");
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
  ``Let (SOME "_") (Apps [Var (Long "Word8Array" "update");
                          Var (Short "onechar"); Lit (IntLit 0);
                          Var (Short "w8")]) (
    Let (SOME "_") (App (FFI "isEof") [Var (Short "onechar")]) (
    Let (SOME "bw") (Apps [Var (Long "Word8Array" "sub");
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
            (Apps [Var (Long "Word8Array" "update");
                   Var (Short "onechar");
                   Lit (IntLit 0);
                   Var (Short "fd")]) (
        Let (SOME "u2") (App (FFI "fgetc") [Var (Short "onechar")]) (
        Let (SOME "cw") (Apps [Var (Long "Word8Array" "sub");
                               Var (Short "onechar"); Lit (IntLit 0)]) (
          Con (SOME (Short "SOME")) [Var (Short "cw")])))))``
   |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"fgetc"`` ``"fd"`` fgetc_e "fgetc_v")
val fgetc_v_def = definition "fgetc_v_def"

(* ML implementation of close function, with parameter "w8" *)
val close_e =
  ``Let (SOME "_") (Apps [Var (Long "Word8Array" "update");
                          Var (Short "onechar");
                          Lit (IntLit 0);
                          Var (Short "w8")]) (
    Let (SOME "u2") (App (FFI "close") [Var (Short "onechar")]) (
    Let (SOME "okw") (Apps [Var (Long "Word8Array" "sub");
                            Var (Short "onechar");
                            Lit (IntLit 0)]) (
    Let (SOME "ok") (Apps [Var (Short "word_eq1"); Var (Short "okw")]) (
      If (Var (Short "ok"))
         (Con NONE [])
         (Raise (Con (SOME (Short "InvalidFD")) []))))))``
    |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"close"`` ``"w8"`` close_e "close_v")

val CHAR_IO_char1_def = Define `
  CHAR_IO_char1 = SEP_EXISTS w. W8ARRAY onechar_loc [w]`;

val CHAR_IO_fname_def = Define`
  CHAR_IO_fname =
    SEP_EXISTS v. W8ARRAY filename_loc v * cond (LENGTH v = 256)
`;

val CATFS_def = Define `
  CATFS fs =
    IO (encode fs) fs_ffi_next ["open";"fgetc";"close";"isEof"] * &(wfFS fs) *
    CHAR_IO_char1 * CHAR_IO_fname`

val FILENAME_def = Define `
  FILENAME s sv =
    (STRING_TYPE s sv ∧
     ¬MEM (CHR 0) (explode s) ∧
     strlen s < 256)
`;

val nextFD_ltX = Q.store_thm(
  "nextFD_ltX",
  `CARD (set (MAP FST fs.infds)) < x ⇒ nextFD fs < x`,
  simp[nextFD_def] >> strip_tac >> numLib.LEAST_ELIM_TAC >> simp[] >>
  qabbrev_tac `ns = MAP FST fs.infds` >> RM_ALL_ABBREVS_TAC >> conj_tac
  >- (qexists_tac `MAX_SET (set ns) + 1` >>
      pop_assum kall_tac >> DEEP_INTRO_TAC MAX_SET_ELIM >> simp[] >>
      rpt strip_tac >> res_tac >> fs[]) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `count x ⊆ set ns` by simp[SUBSET_DEF] >>
  `x ≤ CARD (set ns)`
     by metis_tac[CARD_COUNT, CARD_SUBSET, FINITE_LIST_TO_SET] >>
  fs[]);

val openIn_spec = Q.store_thm(
  "openIn_spec",
  `∀s sv fs.
     FILENAME s sv ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 255 ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "openIn" (basis_st()))
       [sv]
       (CATFS fs)
       (POST
          (\wv. &(WORD (n2w (nextFD fs) :word8) wv ∧
                  validFD (nextFD fs) (openFileFS s fs) ∧
                  inFS_fname s fs) *
                CATFS (openFileFS s fs))
          (\e. &(BadFileName_exn e ∧ ~inFS_fname s fs) * CATFS fs))`,
  xcf "openIn" (basis_st()) >>
  fs[FILENAME_def, mlstringTheory.strlen_def, CATFS_def, CHAR_IO_fname_def] >> xpull >>
  rename [`W8ARRAY filename_loc fnm0`] >>
  qmatch_goalsub_abbrev_tac`CATIO * _ * _` >>
  xlet `POSTv u. &(UNIT_TYPE () u) * CHAR_IO_char1 *
                 W8ARRAY filename_loc
                         (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0) *
                 CATIO`
  >- (xapp >> xsimpl >> instantiate >>
      simp[definition "filename_loc_def"] >> xsimpl >>
      Cases_on`s` \\ fs[]) >>
  qabbrev_tac `fnm = insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0` >>
  qmatch_goalsub_abbrev_tac`CATIOO * _ * _ * _` >>
  Cases_on `inFS_fname s fs`
  >- (
    xlet `POSTv u2.
            &(UNIT_TYPE () u2 /\ nextFD fs < 255 /\
              validFD (nextFD fs) (openFileFS s fs)) *
            CHAR_IO_char1 *
            W8ARRAY filename_loc (LUPDATE (n2w (nextFD fs)) 0 fnm) *
            CATIOO`
    >- (simp[Abbr`CATIO`,Abbr`CATIOO`] >>
        xffi >> simp[definition "filename_loc_def"] >>
        `MEM "open" ["open";"fgetc";"close";"isEof"]` by simp[] >> instantiate >> xsimpl >>
        simp[fs_ffi_next_def, decode_encode_FS, Abbr`fnm`,
             getNullTermStr_insertNTS_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
             mlstringTheory.implode_explode, LENGTH_explode] >>
        `∃content. ALOOKUP fs.files s = SOME content`
          by (fs[inFS_fname_def, ALOOKUP_EXISTS_IFF, MEM_MAP, EXISTS_PROD] >>
              metis_tac[]) >>
        csimp[nextFD_ltX, openFile_def, openFileFS_def, validFD_def]) >>
    xlet `POSTv fdv. &WORD (n2w (nextFD fs) : word8) fdv *
                     CHAR_IO_char1 *
                     W8ARRAY filename_loc (LUPDATE (n2w (nextFD fs)) 0 fnm) *
                     CATIOO`
    >- (xapp >> xsimpl >> simp[definition "filename_loc_def"] >> xsimpl >>
        csimp[HD_LUPDATE] >>
        simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]) >>
    xlet `POSTv eqn1v. &BOOL F eqn1v * CHAR_IO_char1 *
                       W8ARRAY filename_loc (LUPDATE (n2w (nextFD fs)) 0 fnm) *
                       CATIOO`
    >- (xapp >> xsimpl >> qexists_tac `n2w (nextFD fs)` >>
        simp[WORD_def, BOOL_def]) >>
    xif >> instantiate >> xret >> simp[Abbr`CATIOO`] >> xsimpl >>
    simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode, wfFS_openFile]
  )
  >- (
    xlet `POSTv u2.
            &UNIT_TYPE () u2 * CHAR_IO_char1 * CATIO *
            W8ARRAY filename_loc (LUPDATE 255w 0 fnm)`
    >- (simp[Abbr`CATIO`,Abbr`CATIOO`] >> xffi >> simp[definition "filename_loc_def"] >>
        `MEM "open" ["open";"fgetc";"close";"isEof"]` by simp[] >> instantiate >> xsimpl >>
        simp[fs_ffi_next_def, decode_encode_FS, Abbr`fnm`,
             getNullTermStr_insertNTS_atI, MEM_MAP, ORD_BOUND, ORD_eq_0,
             dimword_8, MAP_MAP_o, o_DEF, char_BIJ, wfFS_openFile,
             mlstringTheory.implode_explode, LENGTH_explode] >>
        simp[not_inFS_fname_openFile]) >>
    xlet `POSTv fdv. &WORD (255w: word8) fdv *
                     CHAR_IO_char1 * CATIO *
                     W8ARRAY filename_loc (LUPDATE 255w 0 fnm)`
    >- (xapp >> xsimpl >> simp[definition "filename_loc_def"] >> xsimpl >>
        csimp[HD_LUPDATE] >> simp[Abbr`fnm`, LENGTH_insertNTS_atI, LENGTH_explode]) >>
    xlet `POSTv eqn1v.
            &BOOL T eqn1v *
            CHAR_IO_char1 * CATIO *
            W8ARRAY filename_loc (LUPDATE 255w 0 fnm)`
    >- (xapp >> xsimpl >> fs[WORD_def, BOOL_def]) >>
    xif >> instantiate >>
    xlet `POSTv ev.
            &BadFileName_exn ev *
            CHAR_IO_char1 * CATIO *
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
       (CATFS fs)
       (POSTv bv.
          &(BOOL (THE (eof (w2n w) fs)) bv) * CATFS fs)`,
  xcf "eof" (basis_st()) >>
  simp[CATFS_def, CHAR_IO_char1_def] >> xpull >>
  rename [`W8ARRAY onechar_loc [byte]`] >>
  qmatch_goalsub_abbrev_tac`CATIO * _ * _` >>
  xlet `POSTv u. &(UNIT_TYPE () u) * CHAR_IO_fname * CATIO *
                 W8ARRAY onechar_loc [w]`
  >- (xapp >> xsimpl >> simp[onechar_loc_def] >> xsimpl >>
      simp[LUPDATE_def]) >>
  xlet `POSTv u. &(UNIT_TYPE () u) * CHAR_IO_fname * CATIO *
                 W8ARRAY onechar_loc [if THE (eof (w2n w) fs) then 1w else 0w]`
  >- (simp[Abbr`CATIO`] >> xffi >> simp[onechar_loc_def] >>
      `MEM "isEof" ["open";"fgetc";"close";"isEof"]` by simp[] >> instantiate >> xsimpl >>
      csimp[fs_ffi_next_def, LUPDATE_def] >>
      simp[eof_def, EXISTS_PROD, PULL_EXISTS] >>
      `∃fnm pos. ALOOKUP fs.infds (w2n w) = SOME (fnm,pos)`
        by (fs[validFD_def, MEM_MAP, EXISTS_PROD] >>
            metis_tac[ALOOKUP_EXISTS_IFF, PAIR, EXISTS_PROD]) >>
      simp[] >>
      `∃conts. ALOOKUP fs.files fnm = SOME conts`
        by (fs[wfFS_def, validFD_def] >> res_tac >> fs[MEM_MAP, EXISTS_PROD] >>
            rw[] >> metis_tac[ALOOKUP_EXISTS_IFF]) >> simp[]) >>
  xlet `POSTv bw. &(WORD (if THE (eof (w2n w) fs) then 1w else 0w:word8) bw) *
                  CATIO * CHAR_IO_fname *
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
       (CATFS fs)
       (POSTv coptv.
          &(OPTION_TYPE WORD (FDchar (w2n fdw) fs) coptv) *
          CATFS (bumpFD (w2n fdw) fs))`,
  rpt strip_tac >> xcf "fgetc" (basis_st()) >>
  simp[CATFS_def] >> xpull >>
  qabbrev_tac `catfs = λfs. IO (encode fs) fs_ffi_next ["open";"fgetc";"close";"isEof"]` >> simp[] >>
  `∃eofb. eof (w2n fdw) fs = SOME eofb` by metis_tac[wfFS_eof_EQ_SOME] >>
  xlet `POSTv bv. &(BOOL eofb bv) * catfs fs * CHAR_IO_char1 * CHAR_IO_fname`
  >- (xapp >> simp[onechar_loc_def, CATFS_def] >> xsimpl >> instantiate >>
      xsimpl) >>
  xif >- (xret >> fs[eof_FDchar, eof_bumpFD, OPTION_TYPE_def] >> xsimpl) >>
  fs[] >>
  simp[CHAR_IO_char1_def] >> xpull >>
  xlet `POSTv u1. W8ARRAY onechar_loc [fdw] * catfs fs * CHAR_IO_fname`
  >- (xapp >> simp[onechar_loc_def] >> xsimpl >>
      simp[LUPDATE_def]) >>
  `∃c. FDchar (w2n fdw) fs = SOME c` by metis_tac[neof_FDchar] >> simp[] >>
  xlet `POSTv u2. &UNIT_TYPE () u2 * catfs (bumpFD (w2n fdw) fs) *
                  CHAR_IO_fname * W8ARRAY onechar_loc [c]`
  >- (xffi >> simp[onechar_loc_def, Abbr`catfs`] >> xsimpl >>
      `MEM "fgetc" ["open";"fgetc";"close";"isEof"]` by simp[] >> instantiate >> xsimpl >>
      simp[fs_ffi_next_def, EXISTS_PROD, fgetc_def]) >>
  xlet `POSTv cwv.
         &(WORD c cwv) * CHAR_IO_fname *
         W8ARRAY onechar_loc [c] * catfs (bumpFD (w2n fdw) fs)`
  >- (xapp >> simp[onechar_loc_def] >> xsimpl) >>
  xret >> xsimpl >> simp[OPTION_TYPE_def])

val close_spec = Q.store_thm(
  "close_spec",
  `∀(fdw:word8) fdv fs.
     WORD fdw fdv ∧ validFD (w2n fdw) fs ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "close" (basis_st())) [fdv]
       (CATFS fs)
       (POSTv u. &UNIT_TYPE () u *
                 CATFS (fs with infds updated_by A_DELKEY (w2n fdw)))`,
  rpt strip_tac >>
  xcf "close" (basis_st()) >> simp[CATFS_def, CHAR_IO_char1_def] >>
  xpull >>
  qabbrev_tac `catfs = λfs. IO (encode fs) fs_ffi_next ["open";"fgetc";"close";"isEof"]` >> simp[] >>
  xlet `POSTv u.
         &UNIT_TYPE () u * W8ARRAY onechar_loc [fdw] * CHAR_IO_fname * catfs fs`
  >- (xapp >> simp[onechar_loc_def] >> xsimpl >> simp[LUPDATE_def]) >>
  xlet `POSTv u2.
          &UNIT_TYPE () u2 * W8ARRAY onechar_loc [1w] * CHAR_IO_fname *
          catfs (fs with infds updated_by A_DELKEY (w2n fdw))`
  >- (simp[Abbr`catfs`] >> xffi >> simp[onechar_loc_def] >> xsimpl >>
      `MEM "close" ["open";"fgetc";"close";"isEof"]` by simp[] >> instantiate >> xsimpl >>
      simp[fs_ffi_next_def, wfFS_DELKEY, closeFD_def, EXISTS_PROD] >>
      `∃p. ALOOKUP fs.infds (w2n fdw) = SOME p`
        by (fs[validFD_def, MEM_MAP, EXISTS_PROD] >>
            metis_tac[PAIR,EXISTS_PROD, ALOOKUP_EXISTS_IFF]) >>
      simp[LUPDATE_def, RO_fs_component_equality]) >>
  qabbrev_tac `fs' = fs with infds updated_by A_DELKEY (w2n fdw)` >>
  xlet `POSTv okwv. &WORD (1w:word8) okwv * CATFS fs'`
  >- (simp[CATFS_def,Abbr`catfs`,CHAR_IO_char1_def] >> xapp >> simp[onechar_loc_def] >>
      xsimpl >> simp[Abbr`fs'`]) >>
  simp[GSYM CHAR_IO_char1_def] >>
  xlet `POSTv okbv. &BOOL T okbv * CATFS fs'`
  >- (xapp >> xsimpl >> qexists_tac `1w` >> simp[]) >>
  xif >> qexists_tac `T` >> simp[Abbr`catfs`,CATFS_def] >>
  xpull >> xret >> xsimpl);

val _ = ml_prog_update (close_module NONE);

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

val nextFD_NOT_MEM = Q.store_thm(
  "nextFD_NOT_MEM",
  `∀f n fs. ¬MEM (nextFD fs,f,n) fs.infds`,
  rpt gen_tac >> simp[nextFD_def] >> numLib.LEAST_ELIM_TAC >> conj_tac
  >- (qexists_tac `MAX_SET (set (MAP FST fs.infds)) + 1` >>
      DEEP_INTRO_TAC MAX_SET_ELIM >>
      simp[MEM_MAP, EXISTS_PROD, FORALL_PROD] >> rw[] >> strip_tac >>
      res_tac >> fs[]) >>
  simp[EXISTS_PROD, FORALL_PROD, MEM_MAP]);

val do_onefile_spec = Q.store_thm(
  "do_onefile_spec",
  `∀fnm fnv fs out.
      FILENAME fnm fnv ∧
      CARD (FDOM (alist_to_fmap fs.infds)) < 255
    ⇒
      app (p:'ffi ffi_proj) ^(fetch_v "do_onefile" (basis_st())) [fnv]
       (CATFS fs * STDOUT out)
       (POST
         (\u. SEP_EXISTS content.
              &UNIT_TYPE () u *
              &(ALOOKUP fs.files fnm = SOME content) *
              CATFS fs * STDOUT (out ++ content))
         (\e. &BadFileName_exn e *
              &(~inFS_fname fnm fs) *
              CATFS fs * STDOUT out))`,
  rpt strip_tac >> xcf "do_onefile" (basis_st()) >>
  xlet `POST
          (\fdv.
            &(WORD (n2w (nextFD fs) : word8) fdv ∧
              validFD (nextFD fs) (openFileFS fnm fs) ∧
              inFS_fname fnm fs) *
            CATFS (openFileFS fnm fs) * STDOUT out)
          (\e.
            &(BadFileName_exn e ∧ ~inFS_fname fnm fs) *
            CATFS fs * STDOUT out)`
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
         (CATFS fs00 * STDOUT out00)
         (POSTv u.
            &UNIT_TYPE () u *
            CATFS (fs00 with <|
                     infds updated_by
                           ALIST_FUPDKEY fd (I ## K (LENGTH content))
                   |>) * STDOUT (out00 ++ DROP n content))`
  >- (Induct
      >- ((* base case *)
          rpt strip_tac >> `n = LENGTH content` by simp[] >> fs[] >> rveq >>
          xapp >> fs[UNIT_TYPE_def] >> xmatch >>
          xlet `POSTv av.
                  &OPTION_TYPE (WORD:word8->v->bool) NONE av * CATFS fs00 * STDOUT out00`
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
      xlet `POSTv av. &OPTION_TYPE (WORD:word8->v->bool) (FDchar fd fs00) av *
                      CATFS (bumpFD fd fs00) * STDOUT out00`
      >- (xapp >> xsimpl >> instantiate >>
          `fd < 256` by simp[Abbr`fd`, nextFD_ltX] >> simp[] >>
          xsimpl >> map_every qexists_tac [`STDOUT out00`, `fs00`] >> xsimpl >>
          simp[validFD_def, MEM_MAP, EXISTS_PROD] >>
          metis_tac[EXISTS_PROD, PAIR, ALOOKUP_EXISTS_IFF]) >>
      `∃c. FDchar fd fs00 = SOME c` by (irule neof_FDchar >> simp[eof_def] >> NO_TAC) >>
      fs[OPTION_TYPE_def] >> rveq >> xmatch >>
      qabbrev_tac `fs01 = bumpFD fd fs00` >>
      xlet `POSTv u. &UNIT_TYPE () u * CATFS fs01 * STDOUT (out00 ++ [c])`
      >- (xapp >> xsimpl >> instantiate >> xsimpl >>
          map_every qexists_tac [`CATFS fs01`,`out00`] >> xsimpl) >>
      xlet `POSTv bv. &UNIT_TYPE () bv * CATFS fs01 * STDOUT (out00 ++ [c])`
      >- (xret >> xsimpl) >>
      first_x_assum xapp_spec >>
      map_every qexists_tac [`emp`, `out00 ++ [c]`, `n + 1`, `fs01`] >> simp[] >> xsimpl >>
      simp[UNIT_TYPE_def] >> reverse conj_tac
      >- (qmatch_abbrev_tac `CATFS fs1 * STDOUT s1 ==>> CATFS fs2 * STDOUT s2 * GC` >>
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
  xlet `POSTv u2. &UNIT_TYPE () u2 * CATFS fs0 * STDOUT out`
  >- (xret >> xsimpl) >>
  (* calling recurse *)
  xlet `POSTv u3. &UNIT_TYPE () u3 *
                  CATFS (fs0 with <|
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
  qmatch_abbrev_tac `CATFS fs1 ==>> CATFS fs2 * GC` >>
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
     EVERY (\fnm. inFS_fname fnm fs) fns ∧
     CARD (FDOM (alist_to_fmap fs.infds)) < 255
    ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "cat" (basis_st())) [fnsv]
       (CATFS fs * STDOUT out)
       (POSTv u.
          &UNIT_TYPE () u *
          CATFS fs *
          STDOUT (out ++ catfiles_string fs fns))`,
  Induct >>
  rpt strip_tac >> xcf "cat" (basis_st()) >>
  fs[LIST_TYPE_def]
  >- (xmatch >> xret >> simp[catfiles_string_def, file_contents_def] >> xsimpl >>
      qmatch_abbrev_tac `CATFS fs1 ==>> CATFS fs2 * GC` >>
      `fs1 = fs2` suffices_by xsimpl >>
      UNABBREV_ALL_TAC >> simp[RO_fs_component_equality]) >>
  xmatch >>
  progress inFS_fname_ALOOKUP_EXISTS >>
  rename1 `ALOOKUP fs.files _ = SOME cnts` >>
  xlet `POSTv uv.
         &UNIT_TYPE () uv * CATFS fs *
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
    if inFS_fname fnm fs then file_contents fnm fs
    else []`

val cat1_spec = Q.store_thm (
  "cat1_spec",
  `!fnm fnmv.
     FILENAME fnm fnmv /\
     CARD (FDOM (alist_to_fmap fs.infds)) < 255 ==>
     app (p:'ffi ffi_proj) ^(fetch_v "cat1" (basis_st())) [fnmv]
       (CATFS fs * STDOUT out)
       (POSTv u.
          &UNIT_TYPE () u * CATFS fs *
          STDOUT (out ++ catfile_string fs fnm))`,
  xcf "cat1" (basis_st()) >>
  xhandle `POST
             (\u. SEP_EXISTS content. &UNIT_TYPE () u *
               &(ALOOKUP fs.files fnm = SOME content) *
               CATFS fs *
               STDOUT (out ++ content))
             (\e. &BadFileName_exn e * &(~inFS_fname fnm fs) *
                  CATFS fs * STDOUT out)` >> fs[]
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

val _ = overload_on ("noNullBytes", ``λs. ¬MEM (CHR 0) (explode s)``)

val _ = export_theory();
