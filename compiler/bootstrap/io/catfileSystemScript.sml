open preamble

open monadsyntax

val _ = new_theory "catfileSystem";

val _ = overload_on ("return", ``SOME``)
val _ = overload_on ("fail", ``NONE``)
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unit_bind", ``OPTION_IGNORE_BIND``)

val _ = Datatype`
  RO_fs = <| files : (string # string) list ;
             infds : (num # (string # num)) list
  |>
`

val nextFD_def = Define`
  nextFD fsys = LEAST n. ~ MEM n (MAP FST fsys.infds)
`;

val openFile_def = Define`
  openFile fnm fsys =
     do
        ALOOKUP fsys.files fnm ;
        return <|
          files := fsys.files ;
          infds := (nextFD fsys, (fnm, 0)) :: fsys.infds
        |>
     od
`;

val A_DELKEY_def = Define`
  A_DELKEY k alist = FILTER (λp. FST p <> k) alist
`;

val fgetc_def = Define`
  fgetc fd fsys =
    do
       (fnm, off) <- ALOOKUP fsys.infds fd ;
       content <- ALOOKUP fsys.files fnm ;
       if off < LENGTH content then
         return
           (SOME (EL off content),
            fsys with infds := (fd,(fnm,off+1)) :: A_DELKEY fd fsys.infds)
       else
         return (NONE, fsys)
    od
`;

val closeFD_def = Define`
  closeFD fd fsys =
    do
       ALOOKUP fsys.infds fd ;
       return ((), fsys with infds := A_DELKEY fd fsys.infds)
    od
`;

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
  encode_files fs = encode_list (encode_pair Str Str) fs
`;

val encode_fds_def = Define`
  encode_fds fds =
     encode_list (encode_pair Num (encode_pair Str Num)) fds
`;

val encode_def = Define`
  encode fs = cfHeapsBase$Cons (encode_files fs.files) (encode_fds fs.infds)
`


val decode_files_def = Define`
  decode_files f = decode_list (decode_pair destStr destStr) f
`

val decode_encode_files = store_thm(
  "decode_encode_files",
  “∀l. decode_files (encode_files l) = return l”,
  simp[encode_files_def, decode_files_def] >>
  simp[decode_encode_list, decode_encode_pair]);

val decode_fds_def = Define`
  decode_fds = decode_list (decode_pair destNum (decode_pair destStr destNum))
`;

val decode_encode_fds = Q.store_thm(
  "decode_encode_fds",
  `decode_fds (encode_fds fds) = return fds`,
  simp[decode_fds_def, encode_fds_def] >>
  simp[decode_encode_list, decode_encode_pair]);

val decode_def = Define`
  (decode (Cons files0 fds0) =
     do
        files <- decode_files files0 ;
        fds <- decode_fds fds0 ;
        return <| files := files ; infds := fds |>
     od) ∧
  (decode _ = fail)
`;

val decode_encode_FS = Q.store_thm(
  "decode_encode_FS",
  `decode (encode fs) = return fs`,
  simp[decode_def, encode_def, decode_encode_files, decode_encode_fds] >>
  simp[theorem "RO_fs_component_equality"]);

val _ = export_theory();
