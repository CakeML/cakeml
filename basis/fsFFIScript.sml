open preamble mlstringTheory cfHeapsBaseTheory

val _ = new_theory"fsFFI"

val _ = option_monadsyntax.temp_add_option_monadsyntax();

(* Logical model of filesystem and I/O streams *)

val _ = Datatype` inode = IOStream mlstring | File mlstring`

val _ = overload_on("isFile",``λinode. ∃fnm. inode = File fnm``);

(* files: a list of file names and their content.
*  infds: descriptor * (filename * position)
*  numchars: stream of num modeling the nondeterministic output of read and
*    write *)

val _ = Datatype`
  IO_fs = <| files : (inode # char list) list ;
             infds : (num # (inode # num)) list;
             numchars : num llist |>`

val IO_fs_component_equality = theorem"IO_fs_component_equality";

val with_same_numchars = Q.store_thm("with_same_numchars",
  `fs with numchars := fs.numchars = fs`,
  rw[IO_fs_component_equality]);

val get_file_content_def = Define`
    get_file_content fs fd =
      do
        (fnm, off) <- ALOOKUP fs.infds fd ;
        c <- ALOOKUP fs.files fnm;
        return (c, off)
      od`

(* find smallest unused descriptor index *)
val nextFD_def = Define`
  nextFD fsys = LEAST n. ~ MEM n (MAP FST fsys.infds)
`;

(* file descriptors are encoded on 8 bytes but there might be OS limits
*  so we define this limit as maxFD
*  ulimit -n has a usual value of 1024 *)

val _ = new_constant("maxFD", ``:num``)

(* adds a new file in infds *)
val openFile_def = Define`
  openFile fnm fsys pos =
     let fd = nextFD fsys
     in
       do
          assert (fd <= maxFD) ;
          ALOOKUP fsys.files (File fnm);
          return (fd, fsys with infds := (nextFD fsys, (File fnm, pos)) :: fsys.infds)
       od
`;

val openFileFS_def = Define`
  openFileFS fnm fs pos =
    case openFile fnm fs pos of
      NONE => fs
    | SOME (_, fs') => fs'
`;

(* adds a new file in infds and truncate it *)
val openFile_truncate_def = Define`
  openFile_truncate fnm fsys =
    let fd = nextFD fsys in
      do
        assert (fd <= maxFD) ;
        ALOOKUP fsys.files (File fnm);
        return (fd, (fsys with infds := (nextFD fsys, (File fnm, 0)) :: fsys.infds)
                          with files updated_by (ALIST_FUPDKEY (File fnm) (\x."")))
      od `;

(* checks if a descriptor index is in infds *)
val validFD_def = Define`
  validFD fd fs ⇔ fd ∈ FDOM (alist_to_fmap fs.infds)
`;

(* increase by n the position in file descriptor and dump numchar's head *)
val bumpFD_def = Define`
  bumpFD fd fs n = (fs with infds updated_by (ALIST_FUPDKEY fd (I ## ((+) n))))
                       with numchars := THE(LTL fs.numchars)`

(* reads several chars and update position *)
val read_def = Define`
  read fd fs n =
    do
      (fnm, off) <- ALOOKUP fs.infds fd ;
      content <- ALOOKUP fs.files fnm ;
      strm <- LHD fs.numchars;
      let k = MIN n (MIN (LENGTH content - off) (SUC strm)) in
      return (TAKE k (DROP off content), bumpFD fd fs k)
    od `;

(* replaces the content of the file in fs with filename fnm,
* set the position in the file and skip k fsnumchars elements*)
val fsupdate_def = Define`
  fsupdate fs fd k pos content =
    case ALOOKUP fs.infds fd of NONE => fs | SOME (fnm,_) =>
    (fs with <| files := ALIST_FUPDKEY fnm (K content) fs.files;
                numchars := THE (LDROP k fs.numchars);
                infds := (ALIST_FUPDKEY fd (I ## (K pos))) fs.infds|>)`;

(* "The write function returns the number of bytes successfully written into the
*  array, which may at times be less than the specified nbytes. It returns -1 if
*  an exceptional condition is encountered." *)
(* can it be 0? *)

val write_def = Define`
  write fd n chars fs =
    do
      (fnm, off) <- ALOOKUP fs.infds fd ;
      content <- ALOOKUP fs.files fnm ;
      assert(n <= LENGTH chars);
      assert(fs.numchars <> [||]);
      strm <- LHD fs.numchars;
      let k = MIN n strm in
        (* an unspecified error occurred *)
        return (k, fsupdate fs fd 1 (off + k)
                            (TAKE off content ++
                             TAKE k chars ++
                             DROP (off + k) content))
    od `;


(* remove file from infds *)
val closeFD_def = Define`
  closeFD fd fsys =
    do
       ALOOKUP fsys.infds fd ;
       return ((), fsys with infds := A_DELKEY fd fsys.infds)
    od
`;


(* Specification of the FFI functions operating on the above model:
    - open_in
    - open_out
    - read
    - write
    - close
*)

(* truncate byte list after null byte and convert into char list *)
val getNullTermStr_def = Define`
  getNullTermStr (bytes : word8 list) =
     let sz = findi 0w bytes
     in
       if sz = LENGTH bytes then NONE
       else SOME(MAP (CHR o w2n) (TAKE sz bytes))
`;

(* encode/decode nums as 2 or 8 bytes *)
(* similar to n2l & l2n but with padding *)
val n2w2_def = Define`
  n2w2 (i : num) : word8 list = [n2w (i DIV 256); n2w i]`

val n2w8_def = Define`
  n2w8 (i : num) : word8 list =
   [n2w (i DIV 256**7); n2w (i DIV 256**6);
    n2w (i DIV 256**5); n2w (i DIV 256**4);
    n2w (i DIV 256**3); n2w (i DIV 256**2);
    n2w (i DIV 256); n2w i]`

val w22n_def = Define`
  w22n ([b1; b0] : word8 list) = w2n b1 * 256 + w2n b0`

val w82n_def = Define`
  w82n ([b7; b6; b5; b4; b3; b2; b1; b0] : word8 list) =
  256 * ( 256 * ( 256 * ( 256 * ( 256 * ( 256 * ( 256 *
  w2n b7 + w2n b6) + w2n b5) + w2n b4) + w2n b3) + w2n b2) + w2n b1) + w2n b0`

val w2n_nw2 = Q.store_thm("w2n_nw2",
  `!i. i < 2**(2*8) ==> w22n (n2w2 i) = i`,
  rw[w22n_def,n2w2_def] >>
  `0 < (256 : num)` by fs[] >> imp_res_tac DIVISION >> fs[] >>
  first_x_assum (assume_tac o Q.SPEC`i`) >> fs[]);

val n2w2_w22n = Q.store_thm("n2w2_w22n",
  `!b. LENGTH b = 2 ==> n2w2 (w22n b) = b`,
  Cases_on`b` >> fs[] >> Cases_on`t` >> rw[w22n_def,n2w2_def]
  >-(PURE_REWRITE_TAC[Once MULT_COMM] >> fs[ADD_DIV_ADD_DIV] >>
     fs[LESS_DIV_EQ_ZERO,w2n_lt_256]) >>
  fs[GSYM word_add_n2w,GSYM word_mul_n2w] >>
  `256w : word8 = 0w` by fs[GSYM n2w_dimword] >>
  first_x_assum (fn x => PURE_REWRITE_TAC[x]) >> fs[]);

val w82n_n2w8 = Q.store_thm("w82n_n2w8",
  `!i. i <= 256**8 - 1 ==> w82n (n2w8 i) = i`,
  rw[w82n_def,n2w8_def] >>
  `0 < (256 : num)` by fs[] >> imp_res_tac DIVISION >> fs[] >> rw[] >>
  NTAC 6(qmatch_abbrev_tac`256* i0 + x MOD 256 = x` >>
      `i0 = x DIV 256` suffices_by fs[] >>
      unabbrev_all_tac >> fs[DIV_DIV_DIV_MULT]) >>
  PURE_REWRITE_TAC[Once ADD_COMM] >>
  qmatch_abbrev_tac`256* i0 + x MOD 256 = x` >>
  `i0 = x DIV 256` suffices_by fs[] >>
  unabbrev_all_tac >> fs[DIV_DIV_DIV_MULT] >>
  `i DIV 256**7 <= 255` suffices_by fs[] >>
  fs[DIV_LE_X]);


val nw8_w8n = Q.store_thm("nw8_nw8",
  `!b. LENGTH b = 8 ==> n2w8 (w82n b) = b`,
  Cases_on`b` >> fs[] >>
  NTAC 4 (Cases_on`t` >> fs[] >> Cases_on`t'` >> fs[]) >>
  fs[w82n_def,n2w8_def] >> rpt (TRY strip_tac
  >-(rpt(qmatch_goalsub_abbrev_tac`(a + 256 * b) DIV m` >>
         `m = 256 * (m DIV 256)` by fs[Abbr`m`] >>
         first_x_assum (fn x => PURE_REWRITE_TAC[Once x]) >>
         `0 < m DIV 256` by fs[Abbr`m`] >>
         fs[GSYM DIV_DIV_DIV_MULT] >>
         `0 < 256 : num` by fs[] >> imp_res_tac ADD_DIV_ADD_DIV >>
         fs[] >>
         unabbrev_all_tac >> rw[LESS_DIV_EQ_ZERO,w2n_lt_256]) >>
     PURE_REWRITE_TAC[Once ADD_COMM] >>
     TRY (first_x_assum(fn x => PURE_REWRITE_TAC[x])) >>
     rw[LESS_DIV_EQ_ZERO,w2n_lt_256] >>
     fs[GSYM word_add_n2w,GSYM word_mul_n2w] >>
     `256w : word8 = 0w` by fs[GSYM n2w_dimword] >>
     first_x_assum (fn x => PURE_REWRITE_TAC[x]) >> fs[])));

val LENGTH_n2w2 = Q.store_thm("LENGTH_n2w2",
  `!n. LENGTH(n2w2 n) = 2`,
  fs[n2w2_def]);

val LENGTH_n2w8 = Q.store_thm("LENGTH_n2w8",
  `!n. LENGTH(n2w8 n) = 8`,
  fs[n2w8_def])

(* read file name from the first non null bytes
*  open the file with read access
*  return result code in first byte
*  write its file descriptor index in the second byte *)
val ffi_open_in_def = Define`
  ffi_open_in (conf: word8 list) bytes fs =
    do
      assert(9 <= LENGTH bytes);
      fname <- getNullTermStr bytes;
      (fd, fs') <- openFile (implode fname) fs 0;
      return (0w :: n2w8 fd ++ DROP 9 bytes, fs')
    od ++
    return (LUPDATE 1w 0 bytes, fs)`;

(* open append:
      contents <- ALOOKUP fs.files (implode fname);
      (fd, fs') <- openFile (implode fname) fs (LENGTH contents);
*)

(* open for writing
* position: the beginning of the file.
* The file is truncated to zero length if it already exists.
* TODO: It is created if it does not already exists.*)
val ffi_open_out_def = Define`
  ffi_open_out (conf: word8 list) bytes fs =
    do
      assert(9 <= LENGTH bytes);
      fname <- getNullTermStr bytes;
      (fd, fs') <- openFile_truncate (implode fname) fs;
      assert(fd <= 255);
      return (0w :: n2w8 fd ++ DROP 9 bytes, fs')
    od ++
    return (LUPDATE 255w 0 bytes, fs)`;

(*
* [descriptor index (8 bytes); number of char to read (2 bytes); buffer]
*   -> [return code; number of read chars (2 bytes); read chars]
* corresponding system call:
*  ssize_t read(int fd, void *buf, size_t count) *)
val ffi_read_def = Define`
  ffi_read (conf: word8 list) bytes fs =
    (* the buffer contains at least the number of requested bytes *)
    case bytes of
       | (n1 :: n0 :: pad1 :: pad2 :: tll) =>
           do
             assert(LENGTH conf = 8);
             assert(LENGTH tll >= w22n [n1; n0]);
             (l, fs') <- read (w82n conf) fs (w22n [n1; n0]);
      (* return ok code and list of chars
      *  the end of the array may remain unchanged *)
             return (0w :: n2w2 (LENGTH l) ++ [pad2] ++
                    MAP (n2w o ORD) l ++
                    DROP (LENGTH l) tll, fs')
           od ++ return (LUPDATE 1w 0 bytes, fs)
      (* inaccurate: "when an error occurs, [...]
      * it is left unspecified whether the file position (if any) changes. *)
       | _ => NONE`

(* [descriptor index; number of chars to write; chars to write]
*    -> [return code; number of written chars]
* corresponding system call:
* ssize_t write(int fildes, const void *buf, size_t nbytes) *)
val ffi_write_def = Define`
  ffi_write (conf:word8 list) bytes fs =
    case bytes of
       | (n1 :: n0 :: off1 :: off0 :: tll) =>
          do
          (* the buffer contains at least the number of requested bytes *)
            assert(LENGTH conf = 8);
            assert(LENGTH tll >= w22n [off1; off0]);
            (nw, fs') <- write (w82n conf) (w22n [n1; n0])
                               (MAP (CHR o w2n) (DROP (w22n [off1; off0]) tll)) fs;
            (* return ok code and number of bytes written *)
            return (0w :: n2w2 nw ++ (off0 :: tll), fs')
          (* return error code *)
          od ++ return (LUPDATE 1w 0 bytes, fs)
        | _ => NONE`;

(* closes a file given its descriptor index *)
val ffi_close_def = Define`
  ffi_close (conf:word8 list) (bytes: word8 list) fs =
    do
      assert(LENGTH bytes >= 1);
      assert(LENGTH conf = 8);
      do
        (_, fs') <- closeFD (w82n conf) fs;
        return (LUPDATE 0w 0 bytes, fs')
      od ++
      return (LUPDATE 1w 0 bytes, fs)
    od`;

(* given a file descriptor and an offset, returns 0 and update fs or returns 1
* if an error is met val ffi_seek = Define`
  ffi_seek bytes fs =
    do
      assert(LENGTH bytes = 2);
      do
        fs' <- seek (w2n (HD bytes)) fs (w2n (HD (TL bytes)));
        return(LUPDATE 0w 0 bytes, fs')
      od ++
      return (LUPDATE 1w 0 bytes, fs)
    od`; *)
(* -- *)

(* Packaging up the model as an ffi_part *)

val encode_inode_def = Define`
  (encode_inode (IOStream s) = Cons (Num 0) ((Str o explode) s)) /\
  encode_inode (File s) = Cons (Num 1) ((Str o explode) s)`;

val encode_files_def = Define`
  encode_files fs = encode_list (encode_pair encode_inode Str) fs`;

val encode_fds_def = Define`
  encode_fds fds =
     encode_list (encode_pair Num (encode_pair encode_inode Num)) fds`;

val encode_def = zDefine`
  encode fs = cfFFIType$Cons
                (cfFFIType$Cons
                  (encode_files fs.files)
                  (encode_fds fs.infds))
                (Stream fs.numchars)`

val encode_inode_11 = store_thm("encode_inode_11[simp]",
  ``!x y. encode_inode x = encode_inode y <=> x = y``,
  Cases \\ Cases_on `y` \\ fs [encode_inode_def,explode_11]);

val encode_files_11 = store_thm("encode_files_11[simp]",
  ``!xs ys. encode_files xs = encode_files ys <=> xs = ys``,
  rw [] \\ eq_tac \\ rw [encode_files_def]
  \\ drule encode_list_11
  \\ fs [encode_pair_def,FORALL_PROD,encode_inode_def]);

val encode_fds_11 = store_thm("encode_fds_11[simp]",
  ``!xs ys. encode_fds xs = encode_fds ys <=> xs = ys``,
  rw [] \\ eq_tac \\ rw [encode_fds_def]
  \\ drule encode_list_11
  \\ fs [encode_pair_def,FORALL_PROD,encode_inode_def]);

val encode_11 = store_thm("encode_11[simp]",
  ``!x y. encode x = encode y <=> x = y``,
  fs [encode_def] \\ rw [] \\ eq_tac \\ rw []
  \\ fs [IO_fs_component_equality]);

val decode_encode = new_specification("decode_encode",["decode"],
  prove(``?decode. !cls. decode (encode cls) = SOME cls``,
        qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]));
val _ = export_rewrites ["decode_encode"];

val fs_ffi_part_def = Define`
  fs_ffi_part =
    (encode,decode,
      [("open_in",ffi_open_in);
       ("open_out",ffi_open_out);
       ("read",ffi_read);
       ("write",ffi_write);
       ("close",ffi_close)])`;

val _ = export_theory();
