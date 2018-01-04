open preamble mlstringTheory cfHeapsBaseTheory fsFFITheory

val _ = new_theory"fsFFIProps"

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val option_case_eq =
    prove_case_eq_thm  { nchotomy = option_nchotomy, case_def = option_case_def}

val numchars_self = Q.store_thm("numchars_self",
  `!fs. fs = fs with numchars := fs.numchars`,
  cases_on`fs` >> fs[fsFFITheory.IO_fs_numchars_fupd]);

val _ = overload_on("hasFreeFD",``λfs. CARD (set (MAP FST fs.infds)) ≤ 255``);

(* nextFD lemmas *)

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

val nextFD_leX = Q.store_thm(
  "nextFD_leX",
  `CARD (set (MAP FST fs.infds)) ≤ x ⇒ nextFD fs ≤ x`,
  simp[nextFD_def] >> strip_tac >> numLib.LEAST_ELIM_TAC >> simp[] >>
  qabbrev_tac `ns = MAP FST fs.infds` >> RM_ALL_ABBREVS_TAC >> conj_tac
  >- (qexists_tac `MAX_SET (set ns) + 1` >>
      pop_assum kall_tac >> DEEP_INTRO_TAC MAX_SET_ELIM >> simp[] >>
      rpt strip_tac >> res_tac >> fs[]) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `count x PSUBSET set ns` by (
    simp[PSUBSET_DEF,SUBSET_DEF] >>
    simp[EXTENSION] \\
    qexists_tac`x` \\ simp[] ) \\
  `x < CARD (set ns)`
     by metis_tac[CARD_COUNT, CARD_PSUBSET, FINITE_LIST_TO_SET] >>
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

val nextFD_numchars = Q.store_thm("nextFD_numchars",
 `!fs ll. nextFD (fs with numchars := ll) = nextFD fs`,
  rw[nextFD_def]);

(* bumpFD lemmas *)

val bumpFD_numchars = Q.store_thm("bumpFD_numchars",
 `!fs fd n ll. bumpFD fd (fs with numchars := ll) n =
        (bumpFD fd fs n) with numchars := THE (LTL ll)`,
    fs[bumpFD_def]);

val bumpFD_files = Q.store_thm("bumpFD_files[simp]",
  `(bumpFD fd fs n).files = fs.files`,
  EVAL_TAC \\ CASE_TAC \\ rw[]);

val bumpFD_o = Q.store_thm("bumpFD_o",
 `!fs fd n1 n2.
    bumpFD fd (bumpFD fd fs n1) n2 =
    bumpFD fd fs (n1 + n2) with numchars := THE (LTL (THE (LTL fs.numchars)))`,
 rw[bumpFD_def] >> cases_on`fs` >> fs[IO_fs_component_equality] >>
 fs[ALIST_FUPDKEY_o] >> irule ALIST_FUPDKEY_eq >> rw[] >> cases_on `v` >> fs[])

val bumpFD_0 = Q.store_thm("bumpFD_0",
  `bumpFD fd fs 0 = fs with numchars := THE (LTL fs.numchars)`,
  rw[bumpFD_def,IO_fs_component_equality] \\
  match_mp_tac ALIST_FUPDKEY_unchanged \\
  simp[FORALL_PROD]);

(* validFD lemmas *)

val validFD_numchars = Q.store_thm("validFD_numchars",
  `!fd fs ll. validFD fd fs <=> validFD fd (fs with numchars := ll)`,
  rw[validFD_def])

val validFD_bumpFD = Q.store_thm("validFD_bumpFD",
  `validFD fd' fs ⇒ validFD fd' (bumpFD fd fs n)`,
  rw[bumpFD_def,validFD_def]);

val validFD_ALOOKUP = Q.store_thm("validFD_ALOOKUP",
  `validFD fd fs ==> ?v. ALOOKUP fs.infds fd = SOME v`,
  rw[validFD_def] >> cases_on`ALOOKUP fs.infds fd` >> fs[ALOOKUP_NONE]);

val ALOOKUP_validFD = Q.store_thm("ALOOKUP_validFD",
  `ALOOKUP fs.infds fd = SOME (fname, pos) ⇒ validFD fd fs`,
  rw[validFD_def] >> imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,EXISTS_PROD] >> metis_tac[]);

(* getNullTermStr lemmas *)

val getNullTermStr_add_null = Q.store_thm(
  "getNullTermStr_add_null",
  `∀cs. ¬MEM 0w cs ⇒ getNullTermStr (cs++(0w::ls)) = SOME (MAP (CHR o w2n) cs)`,
  simp[getNullTermStr_def,  findi_APPEND, NOT_MEM_findi, findi_def, TAKE_APPEND])

val getNullTermStr_insert_atI = Q.store_thm(
  "getNullTermStr_insert_atI",
  `∀cs l. LENGTH cs < LENGTH l ∧ ¬MEM 0w cs ⇒
          getNullTermStr (insert_atI (cs++[0w]) 0 l) = SOME (MAP (CHR o w2n) cs)`,
  simp[getNullTermStr_def, insert_atI_def, findi_APPEND, NOT_MEM_findi,
       findi_def, TAKE_APPEND])

(* the filesystem will always eventually allow to write something *)

val live_numchars_def = Define`
  live_numchars ns ⇔
    ¬LFINITE ns ∧
    always (eventually (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0n)) ns`;

val liveFS_def = Define`
  liveFS fs ⇔ live_numchars fs.numchars`;

(* well formed file descriptor: all descriptors are <= 255
*  and correspond to file names in files *)

val wfFS_def = Define`
  wfFS fs =
    ((∀fd. fd ∈ FDOM (alist_to_fmap fs.infds) ⇒
         fd <= 255 ∧
         ∃fnm off. ALOOKUP fs.infds fd = SOME (fnm,off) ∧
                   fnm ∈ FDOM (alist_to_fmap fs.files))∧
    liveFS fs)
`;

val wfFS_numchars = Q.store_thm("wfFS_numchars",
 `!fs ll. wfFS fs ==> ¬LFINITE ll ==>
          always (eventually (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0)) ll ==>
          wfFS (fs with numchars := ll)`,
 fs[wfFS_def,liveFS_def,live_numchars_def]);

val wfFS_LTL = Q.store_thm("wfFS_LTL",
 `!fs ll. wfFS (fs with numchars := ll) ==>
          wfFS (fs with numchars := THE (LTL ll))`,
 rw[wfFS_def,liveFS_def,live_numchars_def] >> cases_on `ll` >> fs[LDROP_1] >>
 imp_res_tac always_thm);

val wfFS_openFile = Q.store_thm(
  "wfFS_openFile",
  `wfFS fs ⇒ wfFS (openFileFS fnm fs off)`,
  simp[openFileFS_def, openFile_def] >>
  Cases_on `nextFD fs <= 255` >> simp[] >>
  Cases_on `ALOOKUP fs.files (File fnm)` >> simp[] >>
  dsimp[wfFS_def, MEM_MAP, EXISTS_PROD, FORALL_PROD] >> rw[] >>
  fs[liveFS_def] >> metis_tac[ALOOKUP_EXISTS_IFF]);

val wfFS_DELKEY = Q.store_thm(
  "wfFS_DELKEY[simp]",
  `wfFS fs ⇒ wfFS (fs with infds updated_by A_DELKEY k)`,
  simp[wfFS_def, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD,
       ALOOKUP_ADELKEY,liveFS_def] >>
       metis_tac[]);

val wfFS_LDROP = Q.store_thm("wfFS_LDROP",
  `wfFS fs ==> wfFS (fs with numchars := (THE (LDROP k fs.numchars)))`,
  rw[wfFS_def,liveFS_def,live_numchars_def,always_DROP] >>
  imp_res_tac NOT_LFINITE_DROP >>
  first_x_assum (assume_tac o Q.SPEC `k`) >> fs[] >>
  metis_tac[NOT_LFINITE_DROP_LFINITE]);

val wfFS_bumpFD = Q.store_thm(
  "wfFS_bumpFD[simp]",
  `wfFS fs ⇒ wfFS (bumpFD fd fs n)`,
  simp[bumpFD_def] >>
  dsimp[wfFS_def, ALIST_FUPDKEY_ALOOKUP, option_case_eq, bool_case_eq,
        EXISTS_PROD] >>
  rw[] >- metis_tac[] >>
  cases_on`fs.numchars` >> fs[liveFS_def,live_numchars_def] >> imp_res_tac always_thm);

(* end of file is reached when the position index is the length of the file *)

val eof_def = Define`
  eof fd fsys =
    do
      (fnm,pos) <- ALOOKUP fsys.infds fd ;
      contents <- ALOOKUP fsys.files fnm ;
      return (LENGTH contents <= pos)
    od
`;

val eof_numchars = Q.store_thm("eof_numchars[simp]",
  `eof fd (fs with numchars := ll) = eof fd fs`,
  rw[eof_def]);

val wfFS_eof_EQ_SOME = Q.store_thm(
  "wfFS_eof_EQ_SOME",
  `wfFS fs ∧ validFD fd fs ⇒
   ∃b. eof fd fs = SOME b`,
  simp[eof_def, EXISTS_PROD, PULL_EXISTS, MEM_MAP, wfFS_def, validFD_def] >>
  rpt strip_tac >> res_tac >> metis_tac[ALOOKUP_EXISTS_IFF]);

val eof_read = Q.store_thm("eof_read",
 `!fd fs n. wfFS fs ⇒
            0 < n ⇒ (eof fd fs = SOME T) ⇒
            read fd fs n = SOME ([], fs with numchars := THE(LTL fs.numchars))`,
 rw[eof_def,read_def,MIN_DEF]  >>
 qexists_tac `x` >> rw[] >>
 pairarg_tac >> fs[bumpFD_def,wfFS_def] >>
 cases_on`fs.numchars` >> fs[IO_fs_component_equality,liveFS_def,live_numchars_def] >>
 irule ALIST_FUPDKEY_unchanged >> cases_on`v` >> rw[]);

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
  rw[wfFS_def,liveFS_def,live_numchars_def] >>
  cases_on `ALOOKUP fs.infds fd` >> fs[eof_def] >>
  cases_on `x` >> fs[] >>
  cases_on `ALOOKUP fs.files q` >> fs[eof_def] >>
  cases_on `fs.numchars` >> fs[] >>
  cases_on `DROP r contents` >> fs[] >>
  `r ≥ LENGTH contents` by fs[DROP_EMPTY] >>
  fs[]);

val get_file_content_eof = Q.store_thm("get_file_content_eof",
  `get_file_content fs fd = SOME (content,pos) ⇒ eof fd fs = SOME (¬(pos < LENGTH content))`,
  rw[get_file_content_def,eof_def]
  \\ pairarg_tac \\ fs[]);

(* inFS_fname *)

val inFS_fname_def = Define `
  inFS_fname fs s = (s ∈ FDOM (alist_to_fmap fs.files))`

val not_inFS_fname_openFile = Q.store_thm(
  "not_inFS_fname_openFile",
  `~inFS_fname fs (File fname) ⇒ openFile fname fs off = NONE`,
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
  `inFS_fname fs (File f) ∧ nextFD fs <= 255
   ⇒
   ALOOKUP (openFileFS f fs off).infds (nextFD fs) = SOME (File f,off)`,
  rw[openFileFS_def,openFile_def]
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ rw[]);

val inFS_fname_numchars = Q.store_thm("inFS_fname_numchars",
 `!s fs ll. inFS_fname (fs with numchars := ll) s = inFS_fname fs s`,
  rw[] >> EVAL_TAC >> rpt(CASE_TAC >> fs[]));

(* ffi lengths *)

val ffi_open_in_length = Q.store_thm("ffi_open_in_length",
  `ffi_open_in conf bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  rw[ffi_open_in_def] \\ fs[option_eq_some]
  \\ TRY(pairarg_tac) \\ fs[] \\ metis_tac[LENGTH_LUPDATE]);

val ffi_open_out_length = Q.store_thm("ffi_open_out_length",
  `ffi_open_out conf bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  rw[ffi_open_out_def] \\ fs[option_eq_some]
  \\ TRY(pairarg_tac) \\ fs[] \\ metis_tac[LENGTH_LUPDATE]);

val read_length = Q.store_thm("read_length",
    `read fd fs k = SOME (l, fs') ==> LENGTH l <= k`,
    rw[read_def] >> pairarg_tac >> fs[option_eq_some,LENGTH_TAKE] >>
    ` l  = TAKE (MIN k (MIN (STRLEN content − off) (SUC strm)))
        (DROP off content)` by (fs[]) >>
    fs[MIN_DEF,LENGTH_DROP]);

val ffi_read_length = Q.store_thm("ffi_read_length",
  `ffi_read conf bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  rw[ffi_read_def]
  \\ fs[option_case_eq,prove_case_eq_thm{nchotomy=list_nchotomy,case_def=list_case_def}]
  \\ fs[option_eq_some]
  \\ TRY(pairarg_tac) \\ rveq \\ fs[] \\ rveq \\ fs[]
  \\ imp_res_tac read_length \\ fs[]);

val ffi_write_length = Q.store_thm("ffi_write_length",
  `ffi_write conf bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ rw[]
  \\ fs[option_eq_some] \\ every_case_tac \\ fs[] \\ rw[]
  \\ pairarg_tac \\ fs[] \\ pairarg_tac \\ fs[]
  \\ metis_tac[LENGTH_LUPDATE]);

val ffi_close_length = Q.store_thm("ffi_close_length",
  `ffi_close conf bytes fs = SOME (bytes',fs') ==> LENGTH bytes' = LENGTH bytes`,
  rw[ffi_close_def]
  \\ Cases_on`closeFD (w2n (HD bytes)) fs` \\ fs[] \\ rw[]
  \\ pairarg_tac \\ fs[] \\ rw[]);

(* fastForwardFD *)

val fastForwardFD_def = Define`
  fastForwardFD fs fd =
    the fs (do
      (fnm,off) <- ALOOKUP fs.infds fd;
      content <- ALOOKUP fs.files fnm;
      SOME (fs with infds updated_by ALIST_FUPDKEY fd (I ## MAX (LENGTH content)))
    od)`;

val validFD_fastForwardFD = Q.store_thm("validFD_fastForwardFD[simp]",
  `validFD fd (fastForwardFD fs fd) = validFD fd fs`,
  rw[validFD_def,fastForwardFD_def,bumpFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]
  \\ rw[OPTION_GUARD_COND,libTheory.the_def]);

val fastForwardFD_files = Q.store_thm("fastForwardFD_files[simp]",
  `(fastForwardFD fs fd).files = fs.files`,
  EVAL_TAC
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]
  \\ rw[OPTION_GUARD_COND,libTheory.the_def]);

val A_DELKEY_fastForwardFD_elim = Q.store_thm("A_DELKEY_fastForwardFD_elim[simp]",
  `A_DELKEY fd (fastForwardFD fs fd).infds = A_DELKEY fd fs.infds`,
  rw[fastForwardFD_def,bumpFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]
  \\ rw[OPTION_GUARD_COND,libTheory.the_def]);

val fastForwardFD_A_DELKEY_same = Q.store_thm("fastForwardFD_A_DELKEY_same[simp]",
  `fastForwardFD fs fd with infds updated_by A_DELKEY fd =
   fs with infds updated_by A_DELKEY fd`,
  rw[fastForwardFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[libTheory.the_def]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]
  \\ fs[IO_fs_component_equality,A_DELKEY_I])

val fastForwardFD_0 = Q.store_thm("fastForwardFD_0",
  `(∀content pos. get_file_content fs fd = SOME (content,pos) ⇒ LENGTH content ≤ pos) ⇒
   fastForwardFD fs fd = fs`,
  rw[fastForwardFD_def,get_file_content_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]
  \\ fs[IO_fs_component_equality]
  \\ match_mp_tac ALIST_FUPDKEY_unchanged
  \\ rw[] \\ rw[PAIR_MAP_THM]
  \\ rw[MAX_DEF]);

val fastForwardFD_with_numchars = Q.store_thm("fastForwardFD_with_numchars",
  `fastForwardFD (fs with numchars := ns) fd = fastForwardFD fs fd with numchars := ns`,
  rw[fastForwardFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ simp[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ simp[libTheory.the_def]);

val fastForwardFD_numchars = Q.store_thm("fastForwardFD_numchars[simp]",
  `(fastForwardFD fs fd).numchars = fs.numchars`,
  rw[fastForwardFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ simp[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ simp[libTheory.the_def]);

(* fsupdate *)

val wfFS_fsupdate = Q.store_thm("wfFS_fsupdate",
    `! fs fd content pos k. wfFS fs ==> MEM fd (MAP FST fs.infds) ==>
                            wfFS (fsupdate fs fd k pos content)`,
  rw[wfFS_def,fsupdate_def]
  >- (res_tac \\ fs[])
  >- (
    CASE_TAC \\ fs[] \\
    CASE_TAC \\ fs[ALIST_FUPDKEY_ALOOKUP] \\
    res_tac \\ fs[] \\ rw[] )
  >-( CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] \\
      fs[liveFS_def,live_numchars_def,always_DROP] >>
     `∃y. LDROP k fs.numchars = SOME y` by(fs[NOT_LFINITE_DROP]) >>
       fs[] >> metis_tac[NOT_LFINITE_DROP_LFINITE]));

val fsupdate_unchanged = Q.store_thm("fsupdate_unchanged",
 `get_file_content fs fd = SOME(content, pos) ==>
    fsupdate fs fd 0 pos content = fs`,
    fs[fsupdate_def,get_file_content_def,validFD_def,IO_fs_component_equality]>>
    rw[] >> pairarg_tac >> fs[ALIST_FUPDKEY_unchanged] >> rw[]);

val fsupdate_o = Q.store_thm("fsupdate_o",
  `liveFS fs ==>
   fsupdate (fsupdate fs fd k1 pos1 c1) fd k2 pos2 c2 =
   fsupdate fs fd (k1+k2) pos2 c2`,
  rw[fsupdate_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ fs[ALIST_FUPDKEY_ALOOKUP,ALIST_FUPDKEY_o,ALIST_FUPDKEY_eq] \\
  fs[LDROP_ADD,liveFS_def,live_numchars_def] >> imp_res_tac NOT_LFINITE_DROP >>
  FIRST_X_ASSUM(ASSUME_TAC o Q.SPEC`k1`) >> fs[]);

val fsupdate_o_0 = Q.store_thm("fsupdate_o_0[simp]",
  `fsupdate (fsupdate fs fd 0 pos1 c1) fd 0 pos2 c2 =
   fsupdate fs fd 0 pos2 c2`,
  rw[fsupdate_def] \\ CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] \\
  rw[ALIST_FUPDKEY_ALOOKUP,ALIST_FUPDKEY_o]
  \\ match_mp_tac ALIST_FUPDKEY_eq
  \\ simp[FORALL_PROD]);

val fsupdate_comm = Q.store_thm("fsupdate_comm",
  `!fs fd1 fd2 k1 p1 c1 fnm1 pos1 k2 p2 c2 fnm2 pos2.
     ALOOKUP fs.infds fd1 = SOME(fnm1, pos1) /\
     ALOOKUP fs.infds fd2 = SOME(fnm2, pos2) /\
  fnm1 <> fnm2 /\ fd1 <> fd2 /\ ¬ LFINITE fs.numchars ==>
  fsupdate (fsupdate fs fd1 k1 p1 c1) fd2 k2 p2 c2 =
  fsupdate (fsupdate fs fd2 k2 p2 c2) fd1 k1 p1 c1`,
  fs[fsupdate_def] >> rw[] >> fs[ALIST_FUPDKEY_ALOOKUP] >>
  rpt CASE_TAC >> fs[ALIST_FUPDKEY_comm,LDROP_LDROP]);

val fsupdate_MAP_FST_infds = Q.store_thm("fsupdate_MAP_FST_infds[simp]",
  `MAP FST (fsupdate fs fd k pos c).infds = MAP FST fs.infds`,
  rw[fsupdate_def] \\ every_case_tac \\ rw[]);

val fsupdate_MAP_FST_files = Q.store_thm("fsupdate_MAP_FST_files[simp]",
  `MAP FST (fsupdate fs fd k pos c).files = MAP FST fs.files`,
  rw[fsupdate_def] \\ every_case_tac \\ rw[]);

val validFD_fsupdate = Q.store_thm("validFD_fsupdate[simp]",
  `validFD fd (fsupdate fs fd' x y z) ⇔ validFD fd fs`,
  rw[fsupdate_def,validFD_def]);

val fsupdate_numchars = Q.store_thm("fsupdate_numchars",
  `!fs fd k p c ll. fsupdate fs fd k p c with numchars := ll =
                    fsupdate (fs with numchars := ll) fd 0 p c`,
  rw[fsupdate_def] \\ CASE_TAC \\ CASE_TAC \\ rw[]);

val fsupdate_A_DELKEY = Q.store_thm("fsupdate_A_DELKEY",
  `fd ≠ fd' ⇒
   fsupdate (fs with infds updated_by A_DELKEY fd') fd k pos content =
   fsupdate fs fd k pos content with infds updated_by A_DELKEY fd'`,
  rw[fsupdate_def,ALOOKUP_ADELKEY]
  \\ CASE_TAC \\ CASE_TAC
  \\ rw[A_DELKEY_ALIST_FUPDKEY_comm]);

val fsupdate_0_numchars = Q.store_thm("fsupdate_0_numchars",
  `IS_SOME (ALOOKUP fs.infds fd) ⇒
   fsupdate fs fd n pos content =
   fsupdate (fs with numchars := THE (LDROP n fs.numchars)) fd 0 pos content`,
  rw[fsupdate_def] \\ TOP_CASE_TAC \\ fs[]);

(* get_file_content *)

val get_file_content_numchars = Q.store_thm("get_file_content_numchars",
 `!fs fd c p. get_file_content fs fd =
              get_file_content (fs with numchars := ll) fd`,
 fs[get_file_content_def]);

val get_file_content_validFD = Q.store_thm("get_file_content_validFD",
  `get_file_content fs fd = SOME(c,p) ⇒ validFD fd fs`,
  fs[get_file_content_def,validFD_def] >> rw[] >> pairarg_tac >>
  imp_res_tac ALOOKUP_MEM >> fs[ALOOKUP_MEM,MEM_MAP] >>
  qexists_tac`(fd,x)` >> fs[]);

val get_file_content_fsupdate = Q.store_thm("get_file_content_fsupdate",
  `!fs fd x i c u. get_file_content fs fd = SOME u ⇒
  get_file_content (fsupdate fs fd x i c) fd = SOME(c,i)`,
  rw[get_file_content_def, fsupdate_def] >>
  pairarg_tac >> fs[ALIST_FUPDKEY_ALOOKUP]);

val get_file_content_fsupdate_unchanged = Q.store_thm(
  "get_file_content_fsupdate_unchanged",
  `!fs fd u fnm pos fd' fnm' pos' x i c.
   get_file_content fs fd = SOME u ⇒
   ALOOKUP fs.infds fd = SOME (fnm,pos) ⇒
   ALOOKUP fs.infds fd' = SOME (fnm',pos') ⇒ fnm ≠ fnm' ⇒
  get_file_content (fsupdate fs fd' x i c) fd = SOME u`,
  rw[get_file_content_def, fsupdate_def] >>
  pairarg_tac >> fs[ALIST_FUPDKEY_ALOOKUP] >>
  rpt(CASE_TAC >> fs[]));

val get_file_content_bumpFD = Q.store_thm("get_file_content_bumpFD[simp]",
 `!fs fd c pos n.
   get_file_content (bumpFD fd fs n) fd =
   OPTION_MAP (I ## (+) n) (get_file_content fs fd)`,
 rw[get_file_content_def,bumpFD_def,ALIST_FUPDKEY_ALOOKUP]
 \\ CASE_TAC \\ fs[]
 \\ pairarg_tac \\ fs[]
 \\ pairarg_tac \\ fs[] \\ rw[]
 \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[]);

(* liveFS *)

val liveFS_openFileFS = Q.store_thm("liveFS_openFileFS",
 `liveFS fs ⇒ liveFS (openFileFS s fs n)`,
  rw[liveFS_def,openFileFS_def, openFile_def] >>
  CASE_TAC >> fs[] >> CASE_TAC >> fs[] >>
  `r.numchars = fs.numchars` by
    (cases_on`fs` >> cases_on`r` >> fs[IO_fs_infds_fupd]) >>
  fs[]);

val liveFS_fsupdate = Q.store_thm("liveFS_fsupdate",
 `liveFS fs ⇒ liveFS (fsupdate fs fd n k c)`,
 rw[liveFS_def,live_numchars_def,fsupdate_def] >>
 every_case_tac \\ fs[always_DROP] \\
 metis_tac[NOT_LFINITE_DROP,NOT_LFINITE_DROP_LFINITE,THE_DEF]);

val liveFS_bumpFD = Q.store_thm("liveFS_bumpFD",
 `liveFS fs ⇒ liveFS (bumpFD fd fs k)`,
  rw[liveFS_def,live_numchars_def,bumpFD_def] >> cases_on`fs.numchars` >> fs[] >>
  imp_res_tac always_thm);

(* openFile, openFileFS *)

val openFile_fupd_numchars = Q.store_thm("openFile_fupd_numchars",
 `!s fs k ll fd fs'. openFile s (fs with numchars := ll) k =
      case openFile s fs k of
        SOME (fd, fs') => SOME (fd, fs' with numchars := ll)
      | NONE => NONE`,
  rw[openFile_def,nextFD_def] >> rpt(CASE_TAC >> fs[]) >>
  rfs[IO_fs_component_equality]);

val openFileFS_numchars = Q.store_thm("openFileFS_numchars",
  `!s fs k. (openFileFS s fs k).numchars = fs.numchars`,
   rw[openFileFS_def] \\ CASE_TAC \\ CASE_TAC
   \\ fs[openFile_def] \\ rw[]);

val wfFS_openFileFS = Q.store_thm("wfFS_openFileFS",
  `!f fs k.CARD (FDOM (alist_to_fmap fs.infds)) <= 255 /\ wfFS fs ==>
                   wfFS (openFileFS f fs k)`,
  rw[wfFS_def,openFileFS_def,liveFS_def] >> full_case_tac >> fs[openFile_def] >>
  cases_on`x` >> rw[] >> fs[MEM_MAP] >> res_tac >> fs[]
  >-(imp_res_tac ALOOKUP_MEM >-(qexists_tac`(File f,x')` >> fs[])) >>
  CASE_TAC
  >-(cases_on`y` >> fs[] >> cases_on`r` >> fs[] >> metis_tac[nextFD_NOT_MEM])
  >> metis_tac[])

val openFileFS_files = Q.store_thm("openFileFS_files[simp]",
 `!f fs pos. (openFileFS f fs pos).files = fs.files`,
  rw[openFileFS_def] >> CASE_TAC >> cases_on`x` >>
  fs[IO_fs_component_equality,openFile_def]);

val openFileFS_fupd_numchars = Q.store_thm("openFileFS_fupd_numchars",
 `!s fs k ll. openFileFS s (fs with numchars := ll) k =
              (openFileFS s fs k with numchars := ll)`,
  rw[openFileFS_def,openFile_fupd_numchars] >> rpt CASE_TAC);

val IS_SOME_get_file_content_openFileFS_nextFD = Q.store_thm("IS_SOME_get_file_content_openFileFS_nextFD",
  `inFS_fname fs (File f) ∧ nextFD fs ≤ 255
   ⇒ IS_SOME (get_file_content (openFileFS f fs off) (nextFD fs)) `,
  rw[get_file_content_def]
  \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD \\ simp[]
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS \\ fs[]);

val A_DELKEY_nextFD_openFileFS = Q.store_thm("A_DELKEY_nextFD_openFileFS[simp]",
  `nextFD fs <= 255 ⇒
   A_DELKEY (nextFD fs) (openFileFS f fs off).infds = fs.infds`,
  rw[openFileFS_def]
  \\ CASE_TAC
  \\ TRY CASE_TAC
  \\ simp[A_DELKEY_I,nextFD_NOT_MEM,MEM_MAP,EXISTS_PROD]
  \\ fs[openFile_def] \\ rw[]
  \\ rw[A_DELKEY_def,FILTER_EQ_ID,EVERY_MEM,FORALL_PROD,nextFD_NOT_MEM]);

val openFileFS_A_DELKEY_nextFD = Q.store_thm("openFileFS_A_DELKEY_nextFD",
  `nextFD fs ≤ 255 ⇒
   openFileFS f fs off with infds updated_by A_DELKEY (nextFD fs) = fs`,
  rw[IO_fs_component_equality,openFileFS_numchars,A_DELKEY_nextFD_openFileFS]);

(* forwardFD: like bumpFD but leave numchars *)

val forwardFD_def = Define`
  forwardFD fs fd n =
    fs with infds updated_by ALIST_FUPDKEY fd (I ## (+) n)`;

val forwardFD_const = Q.store_thm("forwardFD_const[simp]",
  `(forwardFD fs fd n).files = fs.files ∧
   (forwardFD fs fd n).numchars = fs.numchars`,
  rw[forwardFD_def]);

val forwardFD_o = Q.store_thm("forwardFD_o",
  `forwardFD (forwardFD fs fd n) fd m = forwardFD fs fd (n+m)`,
  rw[forwardFD_def,IO_fs_component_equality,ALIST_FUPDKEY_o]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM,FORALL_PROD]);

val forwardFD_0 = Q.store_thm("forwardFD_0[simp]",
  `forwardFD fs fd 0 = fs`,
  rw[forwardFD_def,IO_fs_component_equality]
  \\ match_mp_tac ALIST_FUPDKEY_unchanged
  \\ simp[FORALL_PROD]);

val forwardFD_numchars = Q.store_thm("forwardFD_numchars",
  `forwardFD (fs with numchars := ll) fd n = forwardFD fs fd n with numchars := ll`,
  rw[forwardFD_def]);

val liveFS_forwardFD = Q.store_thm("liveFS_forwardFD[simp]",
  `liveFS (forwardFD fs fd n) = liveFS fs`,
  rw[liveFS_def]);

val MAP_FST_forwardFD_infds = Q.store_thm("MAP_FST_forwardFD_infds[simp]",
  `MAP FST (forwardFD fs fd n).infds = MAP FST fs.infds`,
  rw[forwardFD_def]);

val validFD_forwardFD = Q.store_thm("validFD_forwardFD[simp]",
  `validFD fd (forwardFD fs fd n)= validFD fd fs`,
  rw[validFD_def]);

val wfFS_forwardFD = Q.store_thm("wfFS_forwardFD[simp]",
  `wfFS (forwardFD fs fd n) = wfFS fs`,
  rw[wfFS_def]
  \\ rw[forwardFD_def,ALIST_FUPDKEY_ALOOKUP]
  \\ rw[EQ_IMP_THM]
  \\ res_tac \\ fs[]
  \\ FULL_CASE_TAC \\ fs[]
  \\ FULL_CASE_TAC \\ fs[]
  \\ Cases_on`x` \\ fs[]);

val get_file_content_forwardFD = Q.store_thm("get_file_content_forwardFD[simp]",
  `!fs fd c pos n.
    get_file_content (forwardFD fs fd n) fd =
    OPTION_MAP (I ## (+) n) (get_file_content fs fd)`,
  rw[get_file_content_def,forwardFD_def,ALIST_FUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[] \\ rw[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[]);

val bumpFD_forwardFD = Q.store_thm("bumpFD_forwardFD",
  `bumpFD fd fs n = forwardFD fs fd n with numchars := THE (LTL fs.numchars)`,
  rw[bumpFD_def,forwardFD_def]);

val fastForwardFD_forwardFD = Q.store_thm("fastForwardFD_forwardFD",
  `get_file_content fs fd = SOME (content,pos) ∧ pos + n ≤ LENGTH content ⇒
   fastForwardFD (forwardFD fs fd n) fd = fastForwardFD fs fd`,
  rw[fastForwardFD_def,get_file_content_def,forwardFD_def,ALIST_FUPDKEY_ALOOKUP]
  \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[libTheory.the_def]
  \\ fs[IO_fs_component_equality,ALIST_FUPDKEY_o]
  \\ match_mp_tac ALIST_FUPDKEY_eq
  \\ simp[MAX_DEF]);

(* lineFD: the next line *)

val lineFD_def = Define`
  lineFD fs fd = do
    (content, pos) <- get_file_content fs fd;
    assert (pos < LENGTH content);
    let (l,r) = SPLITP ((=)#"\n") (DROP pos content) in
      SOME(l++"\n") od`;

(* linesFD: get all the lines *)

val linesFD_def = Define`
 linesFD fs fd =
   case get_file_content fs fd of
   | NONE => []
   | SOME (content,pos) =>
       MAP (λx. x ++ "\n")
         (splitlines (DROP pos content))`;

val linesFD_nil_lineFD_NONE = Q.store_thm("linesFD_nil_lineFD_NONE",
  `linesFD fs fd = [] ⇔ lineFD fs fd = NONE`,
  rw[lineFD_def,linesFD_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ pairarg_tac \\ fs[DROP_NIL]);

(* all_lines: get all the lines based on filename *)

val lines_of_def = Define `
  lines_of str =
    MAP (\x. strcat (implode x) (implode "\n"))
          (splitlines (explode str))`

val all_lines_def = Define `
  all_lines fs fname = lines_of (implode (THE (ALOOKUP fs.files fname)))`

val concat_lines_of = store_thm("concat_lines_of",
  ``!s. concat (lines_of s) = s ∨
        concat (lines_of s) = s ^ str #"\n"``,
  rw[lines_of_def] \\
  `s = implode (explode s)` by fs [explode_implode] \\
  qabbrev_tac `ls = explode s` \\ pop_assum kall_tac \\ rveq \\
  Induct_on`splitlines ls` \\ rw[] \\
  pop_assum(assume_tac o SYM) \\
  fs[splitlines_eq_nil,concat_cons]
  >- EVAL_TAC \\
  imp_res_tac splitlines_next \\ rw[] \\
  first_x_assum(qspec_then`DROP (SUC (LENGTH h)) ls`mp_tac) \\
  rw[] \\ rw[]
  >- (
    Cases_on`LENGTH h < LENGTH ls` \\ fs[] >- (
      disj1_tac \\
      rw[strcat_thm] \\ AP_TERM_TAC \\
      fs[IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG,ADD1] ) \\
    fs[DROP_LENGTH_TOO_LONG] \\
    fs[IS_PREFIX_APPEND,strcat_thm] \\ rw[] \\ fs[] \\
    EVAL_TAC )
  >- (
    disj2_tac \\
    rw[strcat_thm] \\
    AP_TERM_TAC \\ rw[] \\
    Cases_on`LENGTH h < LENGTH ls` \\
    fs[IS_PREFIX_APPEND,DROP_APPEND,ADD1,DROP_LENGTH_TOO_LONG]  \\
    qpat_x_assum`strlit [] = _`mp_tac \\ EVAL_TAC ));

val concat_all_lines = Q.store_thm("concat_all_lines",
  `concat (all_lines fs fname) = implode (THE (ALOOKUP fs.files fname)) ∨
   concat (all_lines fs fname) = implode (THE (ALOOKUP fs.files fname)) ^ str #"\n"`,
  fs [all_lines_def,concat_lines_of]);

val all_lines_with_numchars = Q.store_thm("all_lines_with_numchars",
  `all_lines (fs with numchars := ns) = all_lines fs`,
  rw[FUN_EQ_THM,all_lines_def]);

val linesFD_openFileFS_nextFD = Q.store_thm("linesFD_openFileFS_nextFD",
  `inFS_fname fs (File f) ∧ nextFD fs ≤ 255 ⇒
   linesFD (openFileFS f fs 0) (nextFD fs) = MAP explode (all_lines fs (File f))`,
  rw[linesFD_def,get_file_content_def,ALOOKUP_inFS_fname_openFileFS_nextFD]
  \\ rw[all_lines_def,lines_of_def]
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ fs[MAP_MAP_o,o_DEF,GSYM mlstringTheory.implode_STRCAT]);

(* lineForwardFD: seek past the next line *)

val lineForwardFD_def = Define`
  lineForwardFD fs fd =
    case get_file_content fs fd of
    | NONE => fs
    | SOME (content, pos) =>
      if pos < LENGTH content
      then let (l,r) = SPLITP ((=)#"\n") (DROP pos content) in
        forwardFD fs fd (LENGTH l + if NULL r then 0 else 1)
      else fs`;

val fastForwardFD_lineForwardFD = Q.store_thm("fastForwardFD_lineForwardFD[simp]",
  `fastForwardFD (lineForwardFD fs fd) fd = fastForwardFD fs fd`,
  rw[fastForwardFD_def,lineForwardFD_def]
  \\ TOP_CASE_TAC \\ fs[libTheory.the_def]
  \\ TOP_CASE_TAC \\ fs[libTheory.the_def]
  \\ TOP_CASE_TAC \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[forwardFD_def,ALIST_FUPDKEY_ALOOKUP,get_file_content_def]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[libTheory.the_def]
  \\ fs[IO_fs_component_equality,ALIST_FUPDKEY_o]
  \\ match_mp_tac ALIST_FUPDKEY_eq
  \\ simp[] \\ rveq
  \\ imp_res_tac SPLITP_JOIN
  \\ pop_assum(mp_tac o Q.AP_TERM`LENGTH`)
  \\ simp[SUB_RIGHT_EQ]
  \\ rw[MAX_DEF,NULL_EQ] \\ fs[]);

val IS_SOME_get_file_content_lineForwardFD = Q.store_thm("IS_SOME_get_file_content_lineForwardFD[simp]",
  `IS_SOME (get_file_content (lineForwardFD fs fd) fd) =
   IS_SOME (get_file_content fs fd)`,
  rw[lineForwardFD_def]
  \\ CASE_TAC \\ simp[]
  \\ CASE_TAC \\ simp[]
  \\ CASE_TAC \\ simp[]
  \\ pairarg_tac \\ simp[]);

val lineFD_NONE_lineForwardFD_fastForwardFD = Q.store_thm("lineFD_NONE_lineForwardFD_fastForwardFD",
  `lineFD fs fd = NONE ⇒
   lineForwardFD fs fd = fastForwardFD fs fd`,
  rw[lineFD_def,lineForwardFD_def,fastForwardFD_def,get_file_content_def]
  \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[libTheory.the_def]
  \\ rveq \\ fs[libTheory.the_def]
  \\ rw[] \\ TRY (
    simp[IO_fs_component_equality]
    \\ match_mp_tac (GSYM ALIST_FUPDKEY_unchanged)
    \\ simp[MAX_DEF] )
  \\ rw[] \\ fs[forwardFD_def,libTheory.the_def]
  \\ pairarg_tac \\ fs[]);

val linesFD_cons_imp = Q.store_thm("linesFD_cons_imp",
  `linesFD fs fd = ln::ls ⇒
   lineFD fs fd = SOME ln ∧
   linesFD (lineForwardFD fs fd) fd = ls`,
  simp[linesFD_def,lineForwardFD_def]
  \\ CASE_TAC \\ CASE_TAC
  \\ strip_tac
  \\ rename1`_ = SOME (content,off)`
  \\ conj_asm1_tac
  >- (
    simp[lineFD_def]
    \\ Cases_on`DROP off content` \\ rfs[DROP_NIL]
    \\ conj_asm1_tac
    >- ( CCONTR_TAC \\ fs[DROP_LENGTH_TOO_LONG] )
    \\ fs[splitlines_def,FIELDS_def]
    \\ pairarg_tac \\ fs[]
    \\ every_case_tac \\ fs[] \\ rw[]
    \\ fs[NULL_EQ]
    \\ imp_res_tac SPLITP_NIL_IMP \\ fs[] \\ rw[]
    >- ( Cases_on`FIELDS ($= #"\n") t` \\ fs[] )
    >- ( Cases_on`FIELDS ($= #"\n") (TL r)` \\ fs[] ))
  \\ reverse IF_CASES_TAC \\ fs[DROP_LENGTH_TOO_LONG]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`splitlines (DROP off content)` \\ fs[] \\ rveq
  \\ AP_TERM_TAC
  \\ imp_res_tac splitlines_next
  \\ fs[DROP_DROP_T,ADD1,NULL_EQ]
  \\ imp_res_tac splitlines_CONS_FST_SPLITP \\ rfs[]
  \\ IF_CASES_TAC \\ fs[] \\ rw[]
  \\ fs[SPLITP_NIL_SND_EVERY]
  \\ rveq \\ fs[DROP_LENGTH_TOO_LONG]);

val linesFD_lineForwardFD = Q.store_thm("linesFD_lineForwardFD",
  `linesFD (lineForwardFD fs fd) fd' =
   if fd = fd' then
     DROP 1 (linesFD fs fd)
   else linesFD fs fd'`,
  rw[linesFD_def,lineForwardFD_def]
  >- (
    CASE_TAC \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ CASE_TAC \\ fs[DROP_LENGTH_TOO_LONG]
    \\ pairarg_tac \\ fs[]
    \\ qmatch_asmsub_rename_tac`DROP x pos`
    \\ Cases_on`splitlines (DROP x pos)` \\ fs[DROP_NIL]
    \\ imp_res_tac splitlines_CONS_FST_SPLITP
    \\ imp_res_tac splitlines_next
    \\ rveq
    \\ rw[NULL_EQ,DROP_DROP_T,ADD1]
    \\ fs[SPLITP_NIL_SND_EVERY] \\ rw[]
    \\ fs[o_DEF]
    \\ drule SPLITP_EVERY
    \\ strip_tac \\ fs[DROP_LENGTH_TOO_LONG])
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ simp[get_file_content_def]
  \\ simp[forwardFD_def,ALIST_FUPDKEY_ALOOKUP]
  \\ CASE_TAC \\ fs[]);

val lineForwardFD_forwardFD = Q.store_thm("lineForwardFD_forwardFD",
  `∀fs fd. ∃n. lineForwardFD fs fd = forwardFD fs fd n`,
  rw[forwardFD_def,lineForwardFD_def]
  \\ CASE_TAC
  >- (
    qexists_tac`0`
    \\ simp[IO_fs_component_equality]
    \\ match_mp_tac (GSYM ALIST_FUPDKEY_unchanged)
    \\ simp[FORALL_PROD] )
  \\ CASE_TAC
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    qexists_tac`0`
    \\ simp[IO_fs_component_equality]
    \\ match_mp_tac (GSYM ALIST_FUPDKEY_unchanged)
    \\ simp[FORALL_PROD] ));

val get_file_content_lineForwardFD_forwardFD = Q.store_thm("get_file_content_lineForwardFD_forwardFD",
  `∀fs fd. get_file_content fs fd = SOME (x,pos) ⇒
     lineForwardFD fs fd = forwardFD fs fd (LENGTH(FST(SPLITP((=)#"\n")(DROP pos x))) +
                                            if NULL(SND(SPLITP((=)#"\n")(DROP pos x))) then 0 else 1)`,
  simp[forwardFD_def,lineForwardFD_def]
  \\ ntac 3 strip_tac
  \\ pairarg_tac \\ fs[]
  \\ reverse IF_CASES_TAC \\ fs[DROP_LENGTH_TOO_LONG,SPLITP]
  \\ rw[IO_fs_component_equality]
  \\ match_mp_tac (GSYM ALIST_FUPDKEY_unchanged)
  \\ simp[FORALL_PROD] );

(* Property ensuring that standard streams are correctly opened *)
val STD_streams_def = Define
  `STD_streams fs = ?inp out err.
    (ALOOKUP fs.files (IOStream(strlit "stdout")) = SOME out) ∧
    (ALOOKUP fs.files (IOStream(strlit "stderr")) = SOME err) ∧
    (∀fd off. ALOOKUP fs.infds fd = SOME (IOStream(strlit "stdin"),off) ⇔ fd = 0 ∧ off = inp) ∧
    (∀fd off. ALOOKUP fs.infds fd = SOME (IOStream(strlit "stdout"),off) ⇔ fd = 1 ∧ off = LENGTH out) ∧
    (∀fd off. ALOOKUP fs.infds fd = SOME (IOStream(strlit "stderr"),off) ⇔ fd = 2 ∧ off = LENGTH err)`;

val STD_streams_fsupdate = Q.store_thm("STD_streams_fsupdate",
  `! fs fd k pos c.
   ((fd = 1 \/ fd = 2) ==> LENGTH c = pos) /\
   (*
   (fd >= 3 ==> (FST(THE (ALOOKUP fs.infds fd)) <> IOStream(strlit "stdout") /\
                 FST(THE (ALOOKUP fs.infds fd)) <> IOStream(strlit "stderr"))) /\
   *)
    STD_streams fs ==>
    STD_streams (fsupdate fs fd k pos c)`,
  rw[STD_streams_def,fsupdate_def]
  \\ CASE_TAC \\ fs[] >- metis_tac[]
  \\ CASE_TAC \\ fs[ALIST_FUPDKEY_ALOOKUP]
  \\ qmatch_goalsub_abbrev_tac`out' = SOME _ ∧ (err' = SOME _ ∧ _)`
  \\ qmatch_assum_rename_tac`_ = SOME (fnm,_)`
  \\ map_every qexists_tac[`if fnm = IOStream(strlit"stdin") then pos else inp`,`THE out'`,`THE err'`]
  \\ conj_tac >- rw[Abbr`out'`]
  \\ conj_tac >- rw[Abbr`err'`]
  \\ unabbrev_all_tac
  \\ rw[] \\ fs[] \\ rw[] \\ TOP_CASE_TAC \\ fs[] \\ rw[] \\ rfs[]
  \\ rw[] \\ rfs[PAIR_MAP]
  \\ metis_tac[NOT_SOME_NONE,SOME_11,PAIR,FST]);

val STD_streams_openFileFS = Q.store_thm("STD_streams_openFileFS",
  `!fs s k. STD_streams fs ==> STD_streams (openFileFS s fs k)`,
   rw[STD_streams_def,openFileFS_files] >>
   map_every qexists_tac[`inp`,`out`,`err`] >>
   fs[openFileFS_def] >> rpt(CASE_TAC >> fs[]) >>
   fs[openFile_def,IO_fs_component_equality] >>
   qpat_x_assum`_::_ = _`(assume_tac o SYM) \\ fs[] \\
   rw[] \\ metis_tac[ALOOKUP_MEM,nextFD_NOT_MEM,PAIR]);

val STD_streams_numchars = Q.store_thm("STD_streams_numchars",
 `!fs ll. STD_streams fs = STD_streams (fs with numchars := ll)`,
 fs[STD_streams_def]);

val lemma = Q.prove(
  `IOStream (strlit "stdin") ≠ IOStream (strlit "stdout") ∧
   IOStream (strlit "stdin") ≠ IOStream (strlit "stderr") ∧
   IOStream (strlit "stdout") ≠ IOStream (strlit "stderr")`,rw[]);

val STD_streams_forwardFD = Q.store_thm("STD_streams_forwardFD",
  `fd ≠ 1 ∧ fd ≠ 2 ⇒
   (STD_streams (forwardFD fs fd n) = STD_streams fs)`,
  rw[STD_streams_def,forwardFD_def,ALIST_FUPDKEY_ALOOKUP]
  \\ Cases_on`fd = 0`
  >- (
    EQ_TAC \\ rw[]
    \\ fsrw_tac[ETA_ss][option_case_eq,PULL_EXISTS,PAIR_MAP]
    >- (
      qexists_tac`inp-n` \\ rw[]
      >- (
        Cases_on`fd = 0` \\ fs[]
        >- (
          last_x_assum(qspecl_then[`fd`,`inp`]mp_tac)
          \\ rw[] \\ rw[] \\ Cases_on`v` \\ fs[] )
        \\ last_x_assum(qspecl_then[`fd`,`off`]mp_tac)
        \\ rw[] )
      \\ metis_tac[PAIR,SOME_11,FST,SND,lemma] )
    \\ qexists_tac`inp+n` \\ rw[]
    \\ metis_tac[PAIR,SOME_11,FST,SND,lemma,ADD_COMM] )
  \\ EQ_TAC \\ rw[]
  \\ fsrw_tac[ETA_ss][option_case_eq,PULL_EXISTS,PAIR_MAP]
  \\ qexists_tac`inp` \\ rw[]
  \\ metis_tac[PAIR,SOME_11,FST,SND,lemma]);

val STD_streams_bumpFD = Q.store_thm("STD_streams_bumpFD",
  `fd ≠ 1 ∧ fd ≠ 2 ⇒
   (STD_streams (bumpFD fd fs n) = STD_streams fs)`,
  rw[bumpFD_forwardFD,GSYM STD_streams_numchars,STD_streams_forwardFD]);

val STD_streams_nextFD = Q.store_thm("STD_streams_nextFD",
  `STD_streams fs ⇒ 3 ≤ nextFD fs`,
  rw[STD_streams_def,nextFD_def,MEM_MAP,EXISTS_PROD]
  \\ numLib.LEAST_ELIM_TAC \\ rw[]
  >- (
    CCONTR_TAC \\ fs[]
    \\ `CARD (count (LENGTH fs.infds + 1)) ≤ CARD (set (MAP FST fs.infds))`
    by (
      match_mp_tac (MP_CANON CARD_SUBSET)
      \\ simp[SUBSET_DEF,MEM_MAP,EXISTS_PROD] )
    \\ `CARD (set (MAP FST fs.infds)) ≤ LENGTH fs.infds` by metis_tac[CARD_LIST_TO_SET,LENGTH_MAP]
    \\ fs[] )
  \\ Cases_on`n=0` >- metis_tac[ALOOKUP_MEM]
  \\ Cases_on`n=1` >- metis_tac[ALOOKUP_MEM]
  \\ Cases_on`n=2` >- metis_tac[ALOOKUP_MEM]
  \\ decide_tac);

val STD_streams_lineForwardFD = Q.store_thm("STD_streams_lineForwardFD",
  `fd ≠ 1 ∧ fd ≠ 2 ⇒
   (STD_streams (lineForwardFD fs fd) ⇔ STD_streams fs)`,
  rw[lineForwardFD_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ simp[STD_streams_forwardFD]);

val STD_streams_fastForwardFD = Q.store_thm("STD_streams_fastForwardFD",
  `fd ≠ 1 ∧ fd ≠ 2 ⇒
   (STD_streams (fastForwardFD fs fd) ⇔ STD_streams fs)`,
  rw[fastForwardFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]
  \\ EQ_TAC \\ rw[STD_streams_def,option_case_eq,ALIST_FUPDKEY_ALOOKUP,PAIR_MAP] \\ rw[]
  >- (
    qmatch_assum_rename_tac`ALOOKUP _ fnm = SOME r` \\
    qexists_tac`if fd = 0 then off else inp` \\ rw[] \\
    metis_tac[SOME_11,PAIR,FST,SND,lemma] ) \\
  qmatch_assum_rename_tac`ALOOKUP _ fnm = SOME r` \\
  qexists_tac`if fd = 0 then MAX (LENGTH r) off else inp` \\ rw[] \\
  metis_tac[SOME_11,PAIR,FST,SND,lemma] );

val _ = export_theory();
