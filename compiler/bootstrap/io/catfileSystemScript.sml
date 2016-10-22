open preamble

open monadsyntax

val _ = new_theory "catfileSystem";

val _ = overload_on ("return", ``SOME``)
val _ = overload_on ("fail", ``NONE``)
val _ = overload_on ("SOME", ``SOME``)
val _ = overload_on ("NONE", ``NONE``)
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unit_bind", ``OPTION_IGNORE_BIND``)
val _ = overload_on ("++", ``OPTION_CHOICE``)

(* TODO: move candidates follow *)
val ALOOKUP_EXISTS_IFF = Q.store_thm(
  "ALOOKUP_EXISTS_IFF",
  `(∃v. ALOOKUP alist k = SOME v) ⇔ (∃v. MEM (k,v) alist)`,
  Induct_on `alist` >> simp[FORALL_PROD] >> rw[] >> metis_tac[]);

val ALIST_FUPDKEY_def = Define`
  (ALIST_FUPDKEY k f [] = []) ∧
  (ALIST_FUPDKEY k f ((k',v)::rest) =
     if k = k' then (k,f v)::rest
     else (k',v) :: ALIST_FUPDKEY k f rest)
`;

val ALIST_FUPDKEY_ALOOKUP = Q.store_thm(
  "ALIST_FUPDKEY_ALOOKUP",
  `ALOOKUP (ALIST_FUPDKEY k2 f al) k1 =
     case ALOOKUP al k1 of
         NONE => NONE
       | SOME v => if k1 = k2 then SOME (f v) else SOME v`,
  Induct_on `al` >> simp[ALIST_FUPDKEY_def, FORALL_PROD] >> rw[]
  >- (Cases_on `ALOOKUP al k1` >> simp[]) >>
  simp[]);

val MAP_FST_ALIST_FUPDKEY = Q.store_thm(
  "MAP_FST_ALIST_FUPDKEY[simp]",
  `MAP FST (ALIST_FUPDKEY f k alist) = MAP FST alist`,
  Induct_on `alist` >> simp[ALIST_FUPDKEY_def, FORALL_PROD] >> rw[]);

val A_DELKEY_def = Define`
  A_DELKEY k alist = FILTER (λp. FST p <> k) alist
`;

val LUPDATE_commutes = Q.store_thm(
  "LUPDATE_commutes",
  `∀m n e1 e2 l.
    m ≠ n ⇒
    LUPDATE e1 m (LUPDATE e2 n l) = LUPDATE e2 n (LUPDATE e1 m l)`,
  Induct_on `l` >> simp[LUPDATE_def] >>
  Cases_on `m` >> simp[LUPDATE_def] >> rpt strip_tac >>
  rename[`LUPDATE _ nn (_ :: _)`] >>
  Cases_on `nn` >> fs[LUPDATE_def]);

val MEM_DELKEY = Q.store_thm(
  "MEM_DELKEY[simp]",
  `∀al. MEM (k1,v) (A_DELKEY k2 al) ⇔ k1 ≠ k2 ∧ MEM (k1,v) al`,
  Induct >> simp[A_DELKEY_def, FORALL_PROD] >> rw[MEM_FILTER] >>
  metis_tac[]);

val ALOOKUP_ADELKEY = Q.store_thm(
  "ALOOKUP_ADELKEY",
  `∀al. ALOOKUP (A_DELKEY k1 al) k2 = if k1 = k2 then NONE else ALOOKUP al k2`,
  simp[A_DELKEY_def] >> Induct >> simp[FORALL_PROD] >> rw[] >> simp[]);

val findi_APPEND = Q.store_thm(
  "findi_APPEND",
  `∀l1 l2 x.
      findi x (l1 ++ l2) =
        let n0 = findi x l1
        in
          if n0 = LENGTH l1 then n0 + findi x l2
          else n0`,
  Induct >> simp[findi_def] >> rw[] >> fs[]);

val NOT_MEM_findi_IFF = Q.store_thm(
  "NOT_MEM_findi_IFF",
  `¬MEM e l ⇔ findi e l = LENGTH l`,
  Induct_on `l` >> simp[findi_def, bool_case_eq, ADD1] >> metis_tac[]);

val NOT_MEM_findi = save_thm( (* more useful as conditional rewrite *)
  "NOT_MEM_findi",
  NOT_MEM_findi_IFF |> EQ_IMP_RULE |> #1);

val _ = Datatype`
  RO_fs = <| files : (mlstring # string) list ;
             infds : (num # (mlstring # num)) list ;
             stdout : string
  |>
`

val wfFS_def = Define`
  wfFS fs =
    ∀fd. fd ∈ FDOM (alist_to_fmap fs.infds) ⇒
         fd < 255 ∧
         ∃fnm off. ALOOKUP fs.infds fd = SOME (fnm,off) ∧
                   fnm ∈ FDOM (alist_to_fmap fs.files)
`;

val nextFD_def = Define`
  nextFD fsys = LEAST n. ~ MEM n (MAP FST fsys.infds)
`;

val writeStdOut_def = Define`
  writeStdOut c fsys =
    SOME (fsys with stdout := fsys.stdout ++ [c])
`;

val openFile_def = Define`
  openFile fnm fsys =
     let fd = nextFD fsys
     in
       do
          assert (fd < 255) ;
          ALOOKUP fsys.files fnm ;
          return (fd, fsys with infds := (nextFD fsys, (fnm, 0)) :: fsys.infds)
       od
`;

val openFileFS_def = Define`
  openFileFS fnm fs =
    case openFile fnm fs of
      NONE => fs
    | SOME (_, fs') => fs'
`;

val wfFS_openFile = Q.store_thm(
  "wfFS_openFile",
  `wfFS fs ⇒ wfFS (openFileFS fnm fs)`,
  simp[openFileFS_def, openFile_def] >>
  Cases_on `nextFD fs < 255` >> simp[] >>
  Cases_on `ALOOKUP fs.files fnm` >> simp[] >>
  dsimp[wfFS_def, MEM_MAP, EXISTS_PROD, FORALL_PROD] >> rw[] >>
  metis_tac[ALOOKUP_EXISTS_IFF]);

val eof_def = Define`
  eof fd fsys =
    do
      (fnm,pos) <- ALOOKUP fsys.infds fd ;
      contents <- ALOOKUP fsys.files fnm ;
      return (LENGTH contents <= pos)
    od
`;

val validFD_def = Define`
  validFD fd fs ⇔ fd ∈ FDOM (alist_to_fmap fs.infds)
`;

val wfFS_eof_EQ_SOME = Q.store_thm(
  "wfFS_eof_EQ_SOME",
  `wfFS fs ∧ validFD fd fs ⇒
   ∃b. eof fd fs = SOME b`,
  simp[eof_def, EXISTS_PROD, PULL_EXISTS, MEM_MAP, wfFS_def, validFD_def] >>
  rpt strip_tac >> res_tac >> metis_tac[ALOOKUP_EXISTS_IFF]);

val FDchar_def = Define`
  FDchar fd fs =
    do
      (fnm, off) <- ALOOKUP fs.infds fd ;
      content <- ALOOKUP fs.files fnm ;
      if off < LENGTH content then SOME (EL off content)
      else NONE
    od
`;

val eof_FDchar = Q.store_thm(
  "eof_FDchar",
  `eof fd fs = SOME T ⇒ FDchar fd fs = NONE`,
  simp[eof_def, EXISTS_PROD, FDchar_def, PULL_EXISTS]);

val bumpFD_def = Define`
  bumpFD fd fs =
    case FDchar fd fs of
        NONE => fs
      | SOME _ =>
          fs with infds updated_by (ALIST_FUPDKEY fd (I ## SUC))
`;

val eof_bumpFD = Q.store_thm(
  "eof_bumpFD",
  `eof fd fs = SOME T ⇒ bumpFD fd fs = fs`,
  simp[bumpFD_def, eof_FDchar]);

val neof_FDchar = Q.store_thm(
  "neof_FDchar",
  `eof fd fs = SOME F ⇒ ∃c. FDchar fd fs = SOME c`,
  simp[eof_def, FDchar_def, EXISTS_PROD, PULL_EXISTS, FORALL_PROD]);

val option_case_eq =
    prove_case_eq_thm  { nchotomy = option_nchotomy, case_def = option_case_def}

val wfFS_bumpFD = Q.store_thm(
  "wfFS_bumpFD[simp]",
  `wfFS (bumpFD fd fs) ⇔ wfFS fs`,
  simp[bumpFD_def] >> Cases_on `FDchar fd fs` >> simp[] >>
  dsimp[wfFS_def, ALIST_FUPDKEY_ALOOKUP, option_case_eq, bool_case_eq,
        EXISTS_PROD] >> metis_tac[]);

val fgetc_def = Define`
  fgetc fd fsys =
    if validFD fd fsys then SOME (FDchar fd fsys, bumpFD fd fsys)
    else NONE
`;

val closeFD_def = Define`
  closeFD fd fsys =
    do
       ALOOKUP fsys.infds fd ;
       return ((), fsys with infds := A_DELKEY fd fsys.infds)
    od
`;

val inFS_fname_def = Define `
  inFS_fname s fs = (s ∈ FDOM (alist_to_fmap fs.files))`

(* ----------------------------------------------------------------------
    Coding RO_fs values as ffi values
   ---------------------------------------------------------------------- *)

val destStr_def = Define`
  (destStr (Str s) = SOME s) ∧
  (destStr _ = NONE)
`
val _ = export_rewrites ["destStr_def"]

val destNum_def = Define`
  (destNum (Num n) = SOME n) ∧
  (destNum _ = NONE)
`;
val _ = export_rewrites ["destNum_def"]

val encode_pair_def = Define`
  encode_pair e1 e2 (x,y) = Cons (e1 x) (e2 y)
`;

val decode_pair_def = Define`
  (decode_pair d1 d2 (Cons f1 f2) =
      do
        x <- d1 f1;
        y <- d2 f2;
        return (x,y)
      od) ∧
  (decode_pair _ _ _ = fail)
`;

val decode_encode_pair = Q.store_thm(
  "decode_encode_pair",
  `(∀x. d1 (e1 x) = return x) ∧ (∀y. d2 (e2 y) = return y) ⇒
   ∀p. decode_pair d1 d2 (encode_pair e1 e2 p) = return p`,
  strip_tac >> Cases >> simp[encode_pair_def, decode_pair_def])

val encode_list_def = Define`
  encode_list e l = List (MAP e l)
`;

val OPT_MMAP_def = Define`
  (OPT_MMAP f [] = return []) ∧
  (OPT_MMAP f (h0::t0) = do h <- f h0 ; t <- OPT_MMAP f t0 ; return (h::t) od)
`;

val decode_list_def = Define`
  (decode_list d (List fs) = OPT_MMAP d fs) ∧
  (decode_list d _ = fail)
`;

val decode_encode_list = Q.store_thm(
  "decode_encode_list[simp]",
  `(∀x. d (e x) = return x) ⇒
   ∀l. decode_list d (encode_list e l) = return l`,
  strip_tac >> simp[decode_list_def, encode_list_def] >> Induct >>
  simp[OPT_MMAP_def]);

val encode_files_def = Define`
  encode_files fs = encode_list (encode_pair (Str o explode) Str) fs
`;

val encode_fds_def = Define`
  encode_fds fds =
     encode_list (encode_pair Num (encode_pair (Str o explode) Num)) fds
`;

val encode_def = Define`
  encode fs = cfHeapsBase$Cons
                         (encode_files fs.files)
                         (Cons (encode_fds fs.infds) (Str fs.stdout))
`


val decode_files_def = Define`
  decode_files f = decode_list (decode_pair (lift implode o destStr) destStr) f
`

val decode_encode_files = store_thm(
  "decode_encode_files",
  ``∀l. decode_files (encode_files l) = return l``,
  simp[encode_files_def, decode_files_def] >>
  simp[decode_encode_list, decode_encode_pair, implode_explode]);

val decode_fds_def = Define`
  decode_fds =
    decode_list (decode_pair destNum
                             (decode_pair (lift implode o destStr) destNum))
`;

val decode_encode_fds = Q.store_thm(
  "decode_encode_fds",
  `decode_fds (encode_fds fds) = return fds`,
  simp[decode_fds_def, encode_fds_def] >>
  simp[decode_encode_list, decode_encode_pair, implode_explode]);

val decode_def = Define`
  (decode (Cons files0 (Cons fds0 stdout0)) =
     do
        files <- decode_files files0 ;
        fds <- decode_fds fds0 ;
        stdout <- destStr stdout0 ;
        return <| files := files ; infds := fds ; stdout := stdout |>
     od) ∧
  (decode _ = fail)
`;

val decode_encode_FS = Q.store_thm(
  "decode_encode_FS[simp]",
  `decode (encode fs) = return fs`,
  simp[decode_def, encode_def, decode_encode_files, decode_encode_fds] >>
  simp[theorem "RO_fs_component_equality"]);

val encode_11 = Q.store_thm(
  "encode_11[simp]",
  `encode fs1 = encode fs2 ⇔ fs1 = fs2`,
  metis_tac[decode_encode_FS, SOME_11]);

(* ----------------------------------------------------------------------
    Making the above available in the ffi_next view of the world
   ----------------------------------------------------------------------

    There are four operations to be used in the example:

    1. write char to stdout
    2. open file
    3. read char from file descriptor
    4. close file

    The existing example that handles stdout and the write operation
    labels that operation with 0; we might as well keep that, and then
    number the others above 1, 2 and 3. There should probably be a
    better way of developing this numbering methodically (and
    compositionally?).

   ---------------------------------------------------------------------- *)

val getNullTermStr_def = Define`
  getNullTermStr (bytes : word8 list) =
     let sz = findi 0w bytes
     in
       if sz = LENGTH bytes then NONE
       else SOME(MAP (CHR o w2n) (TAKE sz bytes))
`


val fs_ffi_next_def = Define`
  fs_ffi_next (n:num) bytes fs_ffi =
    do
      fs <- decode fs_ffi ;
      case n of
        0 => do (* write *)
               assert(LENGTH bytes = 1);
               fs' <- writeStdOut (CHR (w2n (HD bytes))) fs;
               return (bytes, encode fs')
             od
      | 1 => do (* open file *)
               fname <- getNullTermStr bytes;
               (fd, fs') <- openFile (implode fname) fs;
               assert(fd < 255);
               return (LUPDATE (n2w fd) 0 bytes, encode fs')
             od ++ return (LUPDATE 255w 0 bytes, encode fs)
      | 2 => do (* fgetc *)
               assert(LENGTH bytes = 1);
               (copt, fs') <- fgetc (w2n (HD bytes)) fs;
               case copt of
                   NONE => return ([255w], encode fs')
                 | SOME c => return ([n2w (ORD c)], encode fs')
             od
      | 3 => do (* close *)
               assert(LENGTH bytes = 1);
               do
                 (_, fs') <- closeFD (w2n (HD bytes)) fs;
                 return (LUPDATE 1w 0 bytes, encode fs')
               od ++ return (LUPDATE 0w 0 bytes, encode fs)
             od
      | 4 => do (* eof check *)
               assert(LENGTH bytes = 1);
               do
                 b <- eof (w2n (HD bytes)) fs ;
                 return (LUPDATE (if b then 1w else 0w) 0 bytes, encode fs)
               od ++ return (LUPDATE 255w 0 bytes, encode fs)
             od
      | _ => fail
    od
`;

val closeFD_lemma = Q.store_thm(
  "closeFD_lemma",
  `validFD fd fs ∧ wfFS fs
     ⇒
   fs_ffi_next 3 [n2w fd] (encode fs) =
     SOME ([1w], encode (fs with infds updated_by A_DELKEY fd))`,
  simp[fs_ffi_next_def, decode_encode_FS, closeFD_def, PULL_EXISTS,
       MEM_MAP, FORALL_PROD, ALOOKUP_EXISTS_IFF, validFD_def, wfFS_def,
       EXISTS_PROD] >>
  rpt strip_tac >> res_tac >> simp[LUPDATE_def] >>
  simp[theorem "RO_fs_component_equality"]);

val write_lemma = Q.store_thm(
  "write_lemma",
  `fs_ffi_next 0 [c] (encode fs) =
     SOME ([c], encode (fs with stdout := fs.stdout ++ [CHR (w2n c)]))`,
  simp[fs_ffi_next_def, decode_encode_FS, writeStdOut_def]);

(* insert null-terminated-string (l1) at specified index (n) in a list (l2) *)
val insertNTS_atI_def = Define`
  insertNTS_atI (l1:word8 list) n l2 =
    TAKE n l2 ++ l1 ++ [0w] ++ DROP (n + LENGTH l1 + 1) l2
`;

val insertNTS_atI_NIL = Q.store_thm(
  "insertNTS_atI_NIL",
  `∀n l. n < LENGTH l ==> insertNTS_atI [] n l = LUPDATE 0w n l`,
  simp[insertNTS_atI_def] >> Induct_on `n`
  >- (Cases_on `l` >> simp[LUPDATE_def]) >>
  Cases_on `l` >> simp[LUPDATE_def, ADD1]);

val insertNTS_atI_CONS = Q.store_thm(
  "insertNTS_atI_CONS",
  `∀n l h t.
     n + LENGTH t + 1 < LENGTH l ==>
     insertNTS_atI (h::t) n l = LUPDATE h n (insertNTS_atI t (n + 1) l)`,
  simp[insertNTS_atI_def] >> Induct_on `n`
  >- (Cases_on `l` >> simp[ADD1, LUPDATE_def]) >>
  Cases_on `l` >> simp[ADD1] >> fs[ADD1] >>
  simp[GSYM ADD1, LUPDATE_def]);

val LUPDATE_insertNTS_commute = Q.store_thm(
  "LUPDATE_insertNTS_commute",
  `∀ws pos1 pos2 a w.
     pos2 < pos1 ∧ pos1 + LENGTH ws < LENGTH a
       ⇒
     insertNTS_atI ws pos1 (LUPDATE w pos2 a) =
       LUPDATE w pos2 (insertNTS_atI ws pos1 a)`,
  Induct >> simp[insertNTS_atI_NIL, insertNTS_atI_CONS, LUPDATE_commutes]);

val getNullTermStr_insertNTS_atI = Q.store_thm(
  "getNullTermStr_insertNTS_atI",
  `∀cs l. LENGTH cs < LENGTH l ∧ ¬MEM 0w cs ⇒
          getNullTermStr (insertNTS_atI cs 0 l) = SOME (MAP (CHR o w2n) cs)`,
  simp[getNullTermStr_def, insertNTS_atI_def, findi_APPEND, NOT_MEM_findi,
       findi_def, TAKE_APPEND])

val LENGTH_insertNTS_atI = Q.store_thm(
  "LENGTH_insertNTS_atI",
  `p + LENGTH l1 < LENGTH l2 ⇒ LENGTH (insertNTS_atI l1 p l2) = LENGTH l2`,
  simp[insertNTS_atI_def]);

val wfFS_DELKEY = Q.store_thm(
  "wfFS_DELKEY[simp]",
  `wfFS fs ⇒ wfFS (fs with infds updated_by A_DELKEY k)`,
  simp[wfFS_def, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD,
       ALOOKUP_ADELKEY] >> metis_tac[]);

val not_inFS_fname_openFile = Q.store_thm(
  "not_inFS_fname_openFile",
  `~inFS_fname fname fs ⇒ openFile fname fs = NONE`,
  fs [inFS_fname_def, openFile_def, ALOOKUP_NONE]);

val inFS_fname_ALOOKUP_EXISTS = Q.store_thm(
  "inFS_fname_ALOOKUP_EXISTS",
  `inFS_fname fname fs ⇒ ∃content. ALOOKUP fs.files fname = SOME content`,
  fs [inFS_fname_def, MEM_MAP] >> rpt strip_tac >> fs[] >>
  rename1 `fname = FST p` >> Cases_on `p` >>
  fs[ALOOKUP_EXISTS_IFF] >> metis_tac[]);

val _ = export_theory()
