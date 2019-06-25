(*
  Logical model of filesystem and I/O streams
*)
open preamble mlstringTheory cfHeapsBaseTheory MarshallingTheory

val _ = new_theory"fsFFI"

val _ = option_monadsyntax.temp_add_option_monadsyntax();


(* Logical model of filesystem and I/O streams *)

(* regular files and unnamed streams *)
val _ = Datatype` inode = UStream mlstring | File mlstring`

val _ = overload_on("isFile",``λinode. ∃fnm. inode = File fnm``);

val _ = Datatype` mode = ReadMode | WriteMode`;

(* files: a list of file names and their content.
*  infds: descriptor * (filename * mode * position)
*  numchars: stream of num modeling the nondeterministic output of read and
*    write
* maxFD:
* file descriptors are encoded on 8 bytes but there might be OS limits
*  so we define this limit as maxFD
*  ulimit -n has a usual value of 1024
*)

val _ = Datatype`
  IO_fs = <| inode_tbl : (inode # char list) list ;
             files : (mlstring # mlstring) list;
             infds : (num # (inode # mode # num)) list;
             numchars : num llist;
             maxFD : num
           |>`

val IO_fs_component_equality = theorem"IO_fs_component_equality";

Theorem with_same_numchars:
   fs with numchars := fs.numchars = fs
Proof
  rw[IO_fs_component_equality]
QED

val get_file_content_def = Define`
    get_file_content fs fd =
      do
        (ino, md, off) <- ALOOKUP fs.infds fd ;
        c <- ALOOKUP fs.inode_tbl ino;
        return (c, off)
      od`

(* find smallest unused descriptor index *)
val nextFD_def = Define`
  nextFD fsys = LEAST n. ~ MEM n (MAP FST fsys.infds)
`;

(* adds a new file in infds *)
val openFile_def = Define`
  openFile fnm fsys md pos =
     let fd = nextFD fsys
     in
       do
          assert (fd <= fsys.maxFD) ;
          iname <- ALOOKUP fsys.files fnm;
          ALOOKUP fsys.inode_tbl (File iname);
          return (fd, fsys with infds := (nextFD fsys, (File iname, md, pos)) :: fsys.infds)
       od
`;

val openFileFS_def = Define`
  openFileFS fnm fs md pos =
    case openFile fnm fs md pos of
      NONE => fs
    | SOME (_, fs') => fs'
`;

(* adds a new file in infds and truncate it *)
val openFile_truncate_def = Define`
  openFile_truncate fnm fsys md =
    let fd = nextFD fsys in
      do
        assert (fd <= fsys.maxFD) ;
        iname <- ALOOKUP fsys.files fnm;
        ALOOKUP fsys.inode_tbl (File iname);
        return (fd, (fsys with infds := (nextFD fsys, (File iname, md, 0)) :: fsys.infds)
                          with inode_tbl updated_by (AFUPDKEY (File iname) (\x."")))
      od `;

(* checks if a descriptor index is in infds *)
val validFD_def = Define`
  validFD fd fs ⇔ fd ∈ FDOM (alist_to_fmap fs.infds)
`;

(* increase by n the position in file descriptor and dump numchar's head *)
val bumpFD_def = Define`
  bumpFD fd fs n = (fs with infds updated_by (AFUPDKEY fd (I ## I ## ((+) n))))
                       with numchars := THE(LTL fs.numchars)`

(* reads several chars and update position *)
val read_def = Define`
  read fd fs n =
    do
      (ino, md, off) <- ALOOKUP fs.infds fd ;
      assert (md = ReadMode) ;
      content <- ALOOKUP fs.inode_tbl ino ;
      strm <- LHD fs.numchars;
      let k = MIN n (MIN (LENGTH content - off) (SUC strm)) in
      return (TAKE k (DROP off content), bumpFD fd fs k)
    od `;

(* replaces the content of the file in fs with filename fnm,
* set the position in the file and skip k fsnumchars elements*)
val fsupdate_def = Define`
  fsupdate fs fd k pos content =
    case ALOOKUP fs.infds fd of NONE => fs | SOME (fnm,_) =>
    (fs with <| inode_tbl := AFUPDKEY fnm (K content) fs.inode_tbl;
                numchars := THE (LDROP k fs.numchars);
                infds := (AFUPDKEY fd (I ## I ## (K pos))) fs.infds|>)`;

(* "The write function returns the number of bytes successfully written into the
*  array, which may at times be less than the specified nbytes. It returns -1 if
*  an exceptional condition is encountered." *)
(* can it be 0? *)

val write_def = Define`
  write fd n chars fs =
    do
      (ino, md, off) <- ALOOKUP fs.infds fd ;
      assert(md = WriteMode) ;
      content <- ALOOKUP fs.inode_tbl ino ;
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
       (fnm, md, off) <- ALOOKUP fsys.infds fd ;
       assert (isFile fnm) ;
       return ((), fsys with infds := ADELKEY fd fsys.infds)
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

(* read file name from the first non null bytes
*  open the file with read access
*  return result code in first byte
*  write its file descriptor index in the second byte *)
val ffi_open_in_def = Define`
  ffi_open_in (conf: word8 list) bytes fs =
    do
      assert(9 <= LENGTH bytes);
      fname <- getNullTermStr conf;
      (fd, fs') <- openFile (implode fname) fs ReadMode 0;
      return (FFIreturn (0w :: n2w8 fd ++ DROP 9 bytes) fs')
    od ++
    do
      assert(0 < LENGTH bytes);
      return (FFIreturn (LUPDATE 1w 0 bytes) fs)
    od`;

(* open append:
      contents <- ALOOKUP fs.inode_tbl (implode fname);
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
      fname <- getNullTermStr conf;
      (fd, fs') <- openFile_truncate (implode fname) fs WriteMode;
      assert(fd <= 255);
      return (FFIreturn (0w :: n2w8 fd ++ DROP 9 bytes) fs')
    od ++
    do
      assert(0 < LENGTH bytes);
      return (FFIreturn (LUPDATE 1w 0 bytes) fs)
    od`;

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
             return (FFIreturn
                       (0w :: n2w2 (LENGTH l) ++ [pad2] ++
                        MAP (n2w o ORD) l ++
                        DROP (LENGTH l) tll)
                       fs')
           od ++ return (FFIreturn (LUPDATE 1w 0 bytes) fs)
      (* inaccurate: "when an error occurs, [...]
      * it is left unspecified whether the file position (if any) changes. *)
  | _  => NONE`

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
            return (FFIreturn (0w :: n2w2 nw ++ (off0 :: tll)) fs')
          (* return error code *)
          od ++ return (FFIreturn (LUPDATE 1w 0 bytes) fs)
        | _ => NONE`;

(* closes a file given its descriptor index *)
val ffi_close_def = Define`
  ffi_close (conf:word8 list) (bytes: word8 list) fs =
    do
      assert(LENGTH bytes >= 1);
      assert(LENGTH conf = 8);
      do
        (_, fs') <- closeFD (w82n conf) fs;
        return (FFIreturn (LUPDATE 0w 0 bytes) fs')
      od ++
      return (FFIreturn (LUPDATE 1w 0 bytes) fs)
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
  (encode_inode (UStream s) = Cons (Num 0) ((Str o explode) s)) /\
  encode_inode (File s) = Cons (Num 1) ((Str o explode) s)`;

val encode_inode_tbl_def = Define`
  encode_inode_tbl tbl = encode_list (encode_pair encode_inode Str) tbl`;

val encode_mode_def = Define`
  (encode_mode ReadMode = Num 0) ∧
  (encode_mode WriteMode = Num 1)`;

val encode_fds_def = Define`
  encode_fds fds =
     encode_list (encode_pair Num (encode_pair encode_inode (encode_pair encode_mode Num))) fds`;

val encode_files_def = Define`
  encode_files fs = encode_list (encode_pair (Str o explode) (Str o explode)) fs`;

val encode_def = zDefine`
  encode fs = Cons
               (Cons
                 (cfFFIType$Cons
                  (cfFFIType$Cons
                    (encode_inode_tbl fs.inode_tbl)
                    (encode_fds fs.infds))
                  (Stream fs.numchars))
                 (encode_files fs.files))
               (Num fs.maxFD)`

Theorem encode_inode_11[simp]:
   !x y. encode_inode x = encode_inode y <=> x = y
Proof
  Cases \\ Cases_on `y` \\ fs [encode_inode_def,explode_11]
QED

Theorem encode_inode_tbl_11[simp]:
   !xs ys. encode_inode_tbl xs = encode_inode_tbl ys <=> xs = ys
Proof
  rw [] \\ eq_tac \\ rw [encode_inode_tbl_def]
  \\ drule encode_list_11
  \\ fs [encode_pair_def,FORALL_PROD,encode_inode_def]
QED

Theorem encode_mode_11[simp]:
   ∀x y. encode_mode x = encode_mode y ⇔ x = y
Proof
  Cases \\ Cases \\ rw[encode_mode_def]
QED

Theorem encode_fds_11[simp]:
   !xs ys. encode_fds xs = encode_fds ys <=> xs = ys
Proof
  rw [] \\ eq_tac \\ rw [encode_fds_def]
  \\ drule encode_list_11
  \\ fs [encode_pair_def,FORALL_PROD,encode_inode_def]
QED

Theorem encode_files_11[simp]:
   !xs ys. encode_files xs = encode_files ys <=> xs = ys
Proof
 rw [] \\ eq_tac \\ rw [encode_files_def]
  \\ drule encode_list_11
  \\ fs [encode_pair_def,FORALL_PROD]
QED

Theorem encode_11[simp]:
   !x y. encode x = encode y <=> x = y
Proof
  fs [encode_def] \\ rw [] \\ eq_tac \\ rw []
  \\ fs [IO_fs_component_equality]
QED

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
