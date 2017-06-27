open preamble mlstringTheory cfHeapsBaseTheory fsFFITheory optionMonadTheory

val _ = new_theory"fsFFIProof"

(* -- read -- *)
(*
* "The value returned is the number of bytes read (zero indicates end of file)
* and the file position is advanced by this number. It is not an error if this
* number is smaller than the number of bytes requested; this may happen for
* example because fewer bytes are actually available right now (maybe because we
* were close to end-of-file, or because we are reading from a pipe, or from a
* terminal), or because the system call was interrupted by a signal.
*
* Alternatively, -1 is returned when an error occurs, in such a case errno is
* set appropriately and further it is left unspecified whether the file position
* (if any) changes." *)

val _ = monadsyntax.add_monadsyntax();

(* nextFD *)
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

val nextFD_NOT_MEM = Q.store_thm(
  "nextFD_NOT_MEM",
  `∀f n fs. ¬MEM (nextFD fs,f,n) fs.infds`,
  rpt gen_tac >> simp[nextFD_def] >> numLib.LEAST_ELIM_TAC >> conj_tac
  >- (qexists_tac `MAX_SET (set (MAP FST fs.infds)) + 1` >>
      DEEP_INTRO_TAC MAX_SET_ELIM >>
      simp[MEM_MAP, EXISTS_PROD, FORALL_PROD] >> rw[] >> strip_tac >>
      res_tac >> fs[]) >>
  simp[EXISTS_PROD, FORALL_PROD, MEM_MAP]);

(* well formed file descriptor: all descriptors are < 255 
*  and correspond to file names in files *)
val wfFS_def = Define`
  wfFS fs =
    ((∀fd. fd ∈ FDOM (alist_to_fmap fs.infds) ⇒
         fd < 255 ∧
         ∃fnm off. ALOOKUP fs.infds fd = SOME (fnm,off) ∧
                   fnm ∈ FDOM (alist_to_fmap fs.files))∧
    ¬LFINITE fs.numchars)
`;

val wfFS_openFile = Q.store_thm(
  "wfFS_openFile",
  `wfFS fs ⇒ wfFS (openFileFS fnm fs off)`,
  simp[openFileFS_def, openFile_def] >>
  Cases_on `nextFD fs < 255` >> simp[] >>
  Cases_on `ALOOKUP fs.files fnm` >> simp[] >>
  dsimp[wfFS_def, MEM_MAP, EXISTS_PROD, FORALL_PROD] >> rw[] >>
  metis_tac[ALOOKUP_EXISTS_IFF]
  );

(* end of file is reached when the position index is the length of the file *)
val eof_def = Define`
  eof fd fsys =
    do
      (fnm,pos) <- ALOOKUP fsys.infds fd ;
      contents <- ALOOKUP fsys.files fnm ;
      return (LENGTH contents <= pos)
    od
`;

val wfFS_eof_EQ_SOME = Q.store_thm(
  "wfFS_eof_EQ_SOME",
  `wfFS fs ∧ validFD fd fs ⇒
   ∃b. eof fd fs = SOME b`,
  simp[eof_def, EXISTS_PROD, PULL_EXISTS, MEM_MAP, wfFS_def, validFD_def] >>
  rpt strip_tac >> res_tac >> metis_tac[ALOOKUP_EXISTS_IFF]);

val bumpFD_files = Q.store_thm("bumpFD_files[simp]",
  `(bumpFD fd fs n).files = fs.files`,
  EVAL_TAC \\ CASE_TAC \\ rw[]);

val wfFS_DELKEY = Q.store_thm(
  "wfFS_DELKEY[simp]",
  `wfFS fs ⇒ wfFS (fs with infds updated_by A_DELKEY k)`,
  simp[wfFS_def, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD,
       ALOOKUP_ADELKEY] >> 
       metis_tac[]);

val eof_read = Q.store_thm("eof_read",
 `!fd fs n. wfFS fs ⇒
            0 < n ⇒ (eof fd fs = SOME T) ⇒
            read fd fs n = SOME ([], fs with numchars := THE(LTL fs.numchars))`,
 rw[eof_def,read_def,MIN_DEF]  >>
 qexists_tac `x` >> rw[] >>
 cases_on `x` >> 
 fs[DROP_LENGTH_TOO_LONG] >>
 fs[bumpFD_def,wfFS_def] >>
 `ALIST_FUPDKEY fd (I ## $+ (STRLEN contents − r)) fs.infds = fs.infds` by 
   (`(∀v. ALOOKUP fs.infds fd = SOME v ⇒ (I ## $+ (STRLEN contents − r)) v = v)`
      by (cases_on`v` >> rw[]) >>
    imp_res_tac ALIST_FUPDKEY_unchanged) >>
  cases_on`fs.numchars` >> fs[] >>
  cases_on`fs` >>
  fs[IO_fs_fn_updates,IO_fs_11]);

val read_eof = Q.store_thm("eof_read",
 `!fd fs n fs'. 0 < n ⇒ read fd fs n = SOME ([], fs') ⇒ eof fd fs = SOME T`,
 rw[eof_def,read_def] >>
 qexists_tac `x` >> rw[] >>
 cases_on `x` >> 
 fs[DROP_NIL]);

val neof_read = Q.store_thm(
  "neof_read",
  `eof fd fs = SOME F ⇒ 0 < n ⇒ 
     wfFS fs ⇒ 
     ∃l fs'. l <> "" /\ read fd fs n = SOME (l,fs')`,
  mp_tac (Q.SPECL [`fd`, `fs`, `n`] read_def) >>
  rw[wfFS_def] >> 
  cases_on `ALOOKUP fs.infds fd` >> fs[eof_def] >>
  cases_on `x` >> fs[] >>
  cases_on `ALOOKUP fs.files q` >> fs[eof_def] >>
  cases_on `fs.numchars` >> fs[] >>
  cases_on `DROP r contents` >> fs[] >>
  `r ≥ LENGTH contents` by fs[DROP_EMPTY] >>
  fs[]);

val option_case_eq =
    prove_case_eq_thm  { nchotomy = option_nchotomy, case_def = option_case_def}

val wfFS_bumpFD = Q.store_thm(
  "wfFS_bumpFD[simp]",
  `wfFS fs ⇒ wfFS (bumpFD fd fs n)`,
  simp[bumpFD_def] >> 
  dsimp[wfFS_def, ALIST_FUPDKEY_ALOOKUP, option_case_eq, bool_case_eq,
        EXISTS_PROD] >> 
  `¬LFINITE fs.numchars ==>¬ LFINITE (THE (LTL fs.numchars)) `
    by (cases_on`fs.numchars` >> fs[]) >>
  metis_tac[]);

val validFD_bumpFD = Q.store_thm("validFD_bumpFD",
  `validFD fd fs ⇒ validFD fd (bumpFD fd fs n)`,
  rw[bumpFD_def,validFD_def]);

val inFS_fname_def = Define `
  inFS_fname fs s = (s ∈ FDOM (alist_to_fmap fs.files))`

val not_inFS_fname_openFile = Q.store_thm(
  "not_inFS_fname_openFile",
  `~inFS_fname fs fname ⇒ openFile fname fs off = NONE`,
  fs [inFS_fname_def, openFile_def, ALOOKUP_NONE]
  );

val inFS_fname_ALOOKUP_EXISTS = Q.store_thm(
  "inFS_fname_ALOOKUP_EXISTS",
  `inFS_fname fs fname ⇒ ∃content. ALOOKUP fs.files fname = SOME content`,
  fs [inFS_fname_def, MEM_MAP] >> rpt strip_tac >> fs[] >>
  rename1 `fname = FST p` >> Cases_on `p` >>
  fs[ALOOKUP_EXISTS_IFF] >> metis_tac[]);

val ALOOKUP_SOME_inFS_fname = Q.store_thm(
  "ALOOKUP_SOME_inFS_fname",
  `ALOOKUP fs.files fnm = SOME contents ==> inFS_fname fs fnm`,
  Induct_on `fs.files` >> rpt strip_tac >>
  qpat_x_assum `_ = fs.files` (assume_tac o GSYM) >> rw[] >>
  fs [inFS_fname_def] >> rename1 `fs.files = p::ps` >>
  Cases_on `p` >> fs [ALOOKUP_def] >> every_case_tac >> fs[] >> rw[] >>
  first_assum (qspec_then `fs with files := ps` assume_tac) >> fs []
);

val ALOOKUP_inFS_fname_openFileFS_nextFD = Q.store_thm("ALOOKUP_inFS_fname_openFileFS_nextFD",
  `inFS_fname fs f ∧ nextFD fs < 255
   ⇒
   ALOOKUP (openFileFS f fs off).infds (nextFD fs) = SOME (f,off)`,
  rw[openFileFS_def,openFile_def]
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ rw[]);

val A_DELKEY_nextFD_openFileFS = Q.store_thm("A_DELKEY_nextFD_openFileFS[simp]",
  `nextFD fs < 255 ⇒
   A_DELKEY (nextFD fs) (openFileFS f fs off).infds = fs.infds`,
  rw[openFileFS_def]
  \\ CASE_TAC
  \\ TRY CASE_TAC
  \\ simp[A_DELKEY_I,nextFD_NOT_MEM,MEM_MAP,EXISTS_PROD]
  \\ fs[openFile_def] \\ rw[]
  \\ rw[A_DELKEY_def,FILTER_EQ_ID,EVERY_MEM,FORALL_PROD,nextFD_NOT_MEM]);

(* encode/ decode *)
val decode_encode_files = Q.store_thm(
  "decode_encode_files",
  `∀l. decode_files (encode_files l) = return l`,
  rw[encode_files_def, decode_files_def] >>
  match_mp_tac decode_encode_list >>
  match_mp_tac decode_encode_pair >>
  rw[implode_explode,MAP_MAP_o,ORD_CHR,MAP_EQ_ID] >>
  Q.ISPEC_THEN`x`mp_tac w2n_lt \\ rw[]);

val decode_encode_fds = Q.store_thm(
  "decode_encode_fds",
  `decode_fds (encode_fds fds) = return fds`,
  simp[decode_fds_def, encode_fds_def] >>
  simp[decode_encode_list, decode_encode_pair, implode_explode]);

val decode_encode_FS = Q.store_thm(
  "decode_encode_FS[simp]",
  `decode (encode fs) = return fs`,
  simp[decode_def, encode_def, decode_encode_files, decode_encode_fds] >>
  simp[IO_fs_component_equality]);

val encode_11 = Q.store_thm(
  "encode_11[simp]",
  `encode fs1 = encode fs2 ⇔ fs1 = fs2`,
  metis_tac[decode_encode_FS, SOME_11]);

(* ffi lengths *)

val ffi_open_in_length = Q.store_thm("ffi_open_in_length",
  `ffi_open_in bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  rw[ffi_open_in_def] \\ fs[option_eq_some]
  \\ TRY(pairarg_tac) \\ fs[] \\ metis_tac[LENGTH_LUPDATE]);

val ffi_open_out_length = Q.store_thm("ffi_open_out_length",
  `ffi_open_out bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  rw[ffi_open_out_def] \\ fs[option_eq_some]
  \\ TRY(pairarg_tac) \\ fs[] \\ metis_tac[LENGTH_LUPDATE]);

val read_length = Q.store_thm("read_length", 
    `read fd fs k = SOME (l, fs') ==> LENGTH l <= k`,
    rw[read_def] >> pairarg_tac >> fs[option_eq_some,LENGTH_TAKE] >>
    ` l  = TAKE (MIN k (MIN (STRLEN content − off) (SUC strm)))
        (DROP off content)` by (fs[]) >>
    fs[MIN_DEF,LENGTH_DROP]);


val ffi_read_length = Q.store_thm("ffi_read_length",
  `ffi_read bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  rw[ffi_read_def] 
  \\ every_case_tac
  \\ fs[option_eq_some]
  \\ TRY(pairarg_tac) 
  \\ fs[] \\ TRY(metis_tac[LENGTH_LUPDATE])
  \\ fs[LENGTH_MAP,LENGTH_DROP,LENGTH_LUPDATE,LENGTH]
  \\ imp_res_tac read_length
  >- (`bytes' = 0w::n2w (STRLEN l)::(MAP (n2w ∘ ORD) l ++ DROP (STRLEN l) t')`
        by (fs[]) \\ fs[])
  >- (`bytes' = LUPDATE 1w 0 (h::h'::t')` by (fs[]) \\ fs[])
  >- (`bytes' = LUPDATE 1w 0 (h::h'::t')` by (fs[]) \\ fs[])); 

val ffi_write_length = Q.store_thm("ffi_write_length",
  `ffi_write bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ rw[] 
  \\ fs[option_eq_some] \\ every_case_tac \\ fs[] \\ rw[]
  \\ pairarg_tac \\ fs[] \\ pairarg_tac \\ fs[]
  \\ metis_tac[LENGTH_LUPDATE]);

val ffi_close_length = Q.store_thm("ffi_close_length",
  `ffi_close bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  rw[ffi_close_def]
  \\ Cases_on`closeFD (w2n (HD bytes)) fs` \\ fs[] \\ rw[]
  \\ pairarg_tac \\ fs[] \\ rw[]);

(* insert a string (l1) at specified index (n) in a list (l2) *)
val insert_atI_def = Define`
  insert_atI l1 n l2 =
    TAKE n l2 ++ l1 ++ DROP (n + LENGTH l1) l2
`;

val insert_atI_NIL = Q.store_thm(
  "insert_atI_NIL",
  `∀n l. n <= LENGTH l ==> insert_atI [] n l = l`,
  simp[insert_atI_def]);

val insert_atI_CONS = Q.store_thm(
  "insert_atI_CONS",
  `∀n l h t.
     n + LENGTH t < LENGTH l ==>
     insert_atI (h::t) n l = LUPDATE h n (insert_atI t (n + 1) l)`,
  simp[insert_atI_def] >> Induct_on `n`
  >- (Cases_on `l` >> simp[ADD1, LUPDATE_def]) >>
  Cases_on `l` >> simp[ADD1] >> fs[ADD1] >>
  simp[GSYM ADD1, LUPDATE_def]);

val LENGTH_insert_atI = Q.store_thm(
  "LENGTH_insert_atI",
  `p + LENGTH l1 <= LENGTH l2 ⇒ LENGTH (insert_atI l1 p l2) = LENGTH l2`,
  simp[insert_atI_def]);

val bumpAllFD_def = Define`
  bumpAllFD fd fs =
    the fs (do
      (fnm,off) <- ALOOKUP fs.infds fd;
      content <- ALOOKUP fs.files fnm;
      SOME (fs with infds updated_by ALIST_FUPDKEY fd (I ## (MAX (LENGTH content))))
    od)`;
val insert_atI_app = Q.store_thm("insert_atI_app",
  `∀n l c1 c2.  n + LENGTH c1 + LENGTH c2 <= LENGTH l ==>
     insert_atI (c1 ++ c2) n l = 
     insert_atI c1 n (insert_atI c2 (n + LENGTH c1) l)`,
  induct_on`c1` >> fs[insert_atI_NIL,insert_atI_CONS,LENGTH_insert_atI,ADD1]);

val LUPDATE_insert_commute = Q.store_thm(
  "LUPDATE_insert_commute",
  `∀ws pos1 pos2 a w.
     pos2 < pos1 ∧ pos1 + LENGTH ws <= LENGTH a ⇒
     insert_atI ws pos1 (LUPDATE w pos2 a) =
       LUPDATE w pos2 (insert_atI ws pos1 a)`,
  Induct >> simp[insert_atI_NIL,insert_atI_CONS, LUPDATE_commutes]);

val getNullTermStr_insert_atI = Q.store_thm(
  "getNullTermStr_insert_atI",
  `∀cs l. LENGTH cs < LENGTH l ∧ ¬MEM 0w cs ⇒
          getNullTermStr (insert_atI (cs++[0w]) 0 l) = SOME (MAP (CHR o w2n) cs)`,
  simp[getNullTermStr_def, insert_atI_def, findi_APPEND, NOT_MEM_findi,
       findi_def, TAKE_APPEND])

val validFD_bumpAllFD = Q.store_thm("validFD_bumpAllFD[simp]",
  `validFD fd (bumpAllFD fd fs) = validFD fd fs`,
  rw[validFD_def,bumpAllFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]);

val bumpAllFD_files = Q.store_thm("bumpAllFD_files[simp]",
  `(bumpAllFD fd fs).files = fs.files`,
  EVAL_TAC
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]);

val A_DELKEY_bumpAllFD_elim = Q.store_thm("A_DELKEY_bumpAllFD_elim[simp]",
  `A_DELKEY fd (bumpAllFD fd fs).infds = A_DELKEY fd fs.infds`,
  rw[bumpAllFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]);

val wfFS_fsupdate = Q.store_thm("wfFS_fsupdate",
    `! fs fd content pos k. wfFS fs ==> MEM fd (MAP FST fs.infds) ==> 
                            wfFS (fsupdate fs fd k pos content)`,
    rw[wfFS_def,ALIST_FUPDKEY_ALOOKUP,fsupdate_def,
       NOT_LFINITE_DROP_LFINITE]
    >-(every_case_tac >> fs[ALOOKUP_NONE] >>
       cases_on`x` >> fs[] >> res_tac >>
       fs[ALOOKUP_MEM,A_DELKEY_def,MEM_MAP, MEM_FILTER] >>
       metis_tac[])
    >-(`∃y. LDROP k fs.numchars = SOME y` by(fs[NOT_LFINITE_DROP]) >>
    fs[] >> metis_tac[NOT_LFINITE_DROP_LFINITE]));

val _ = export_theory();
