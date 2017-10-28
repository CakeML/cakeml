open preamble mlstringTheory cfHeapsBaseTheory fsFFITheory

val _ = new_theory"fsFFIProps"

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val numchars_self = Q.store_thm("numchars_self",
  `!fs. fs = fs with numchars := fs.numchars`,
  cases_on`fs` >> fs[fsFFITheory.IO_fs_numchars_fupd]);

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

val bumpFD_files = Q.store_thm("bumpFD_files[simp]",
  `(bumpFD fd fs n).files = fs.files`,
  EVAL_TAC \\ CASE_TAC \\ rw[]);

(* validFD lemmas *)

val validFD_bumpFD = Q.store_thm("validFD_bumpFD",
  `validFD fd' fs ⇒ validFD fd' (bumpFD fd fs n)`,
  rw[bumpFD_def,validFD_def]);

val validFD_ALOOKUP = Q.store_thm("validFD_ALOOKUP",
  `validFD fd fs ==> ?v. ALOOKUP fs.infds fd = SOME v`,
  rw[validFD_def] >> cases_on`ALOOKUP fs.infds fd` >> fs[ALOOKUP_NONE]);

(* getNullTermStr lemmas *)

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

val option_case_eq =
    prove_case_eq_thm  { nchotomy = option_nchotomy, case_def = option_case_def}

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

(* encode/ decode *)

val decode_encode_inode = Q.store_thm(
  "decode_encode_inode",
  `∀f. decode_inode (encode_inode f) = return f`,
  strip_tac >> cases_on`f` >>
  rw[encode_inode_def, decode_inode_def] >>
  rpt CASE_TAC >> fs[decode_pair_def]);

val decode_encode_files = Q.store_thm(
  "decode_encode_files",
  `∀l. decode_files (encode_files l) = return l`,
  rw[encode_files_def, decode_files_def] >>
  match_mp_tac decode_encode_list >>
  match_mp_tac decode_encode_pair >>
  simp[implode_explode,decode_encode_inode]);

val encode_files_11 = Q.store_thm("encode_files_11",
  `encode_files l1 = encode_files l2 ⇒ l1 = l2`,
  rw[] >>
  `decode_files (encode_files l1) = decode_files(encode_files l2)` by fs[] >>
  fs[decode_encode_files]);

val decode_encode_fds = Q.store_thm(
  "decode_encode_fds",
  `decode_fds (encode_fds fds) = return fds`,
  simp[decode_fds_def, encode_fds_def] >>
  simp[decode_encode_list, decode_encode_pair,decode_encode_inode]);

val encode_fds_11 = Q.store_thm("encode_fds_11",
  `encode_fds l1 = encode_fds l2 ⇒ l1 = l2`,
  rw[] >> `decode_fds (encode_fds l1) = decode_fds(encode_fds l2)` by fs[] >>
  fs[decode_encode_fds]);

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
  \\ every_case_tac
  \\ fs[option_eq_some]
  \\ TRY(pairarg_tac)
  \\ fs[] \\ TRY(metis_tac[LENGTH_LUPDATE])
  \\ fs[LENGTH_MAP,LENGTH_DROP,LENGTH_LUPDATE,LENGTH]
  \\ imp_res_tac read_length
  \\ imp_res_tac LENGTH_EQ \\ fs[]);

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

val validFD_numchars = Q.store_thm("validFD_numchars",
  `!fd fs ll. validFD fd fs <=> validFD fd (fs with numchars := ll)`,
  rw[validFD_def])

val fsupdate_numchars = Q.store_thm("fsupdate_numchars",
  `!fs fd k p c ll. fsupdate fs fd k p c with numchars := ll =
                    fsupdate (fs with numchars := ll) fd 0 p c`,
  rw[fsupdate_def] \\ CASE_TAC \\ CASE_TAC \\ rw[]);

(* get_file_content *)

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

val _ = export_theory();
