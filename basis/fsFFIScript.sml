open preamble mlstringTheory cfHeapsBaseTheory

val _ = new_theory"fsFFI"

(* TODO: put these calls in a re-usable option syntax Lib *)
val _ = monadsyntax.temp_add_monadsyntax();
val _ = temp_overload_on ("return", ``SOME``)
val _ = temp_overload_on ("fail", ``NONE``)
val _ = temp_overload_on ("SOME", ``SOME``)
val _ = temp_overload_on ("NONE", ``NONE``)
val _ = temp_overload_on ("monad_bind", ``OPTION_BIND``)
val _ = temp_overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
(* -- *)

(* files: a list of file names and their content.
*  infds: descriptor * (filename * position)
*  numchars: stream of num modeling the nondeterministic output of read and
*    write *)
val _ = Datatype`
  RO_fs = <| files : (mlstring # char list) list ;
             infds : (num # (mlstring # num)) list;
             numchars : num llist |>`

val RO_fs_component_equality = theorem"RO_fs_component_equality";


(* find smallest unused descriptor index *)
val nextFD_def = Define`
  nextFD fsys = LEAST n. ~ MEM n (MAP FST fsys.infds)
`;

(* adds a new file in infds *)
val openFile_def = Define`
  openFile fnm fsys pos =
     let fd = nextFD fsys
     in
       do
          assert (fd < 255) ;
          ALOOKUP fsys.files fnm ;
          return (fd, fsys with infds := (nextFD fsys, (fnm, pos)) :: fsys.infds)
       od
`;

(* adds a new file in infds and truncate it *)
val openFile_truncate_def = Define`
  openFile_truncate fnm fsys pos =
    let fd = nextFD fsys in
      do
        assert (fd < 255) ;
        ALOOKUP fsys.files fnm ;
        return (fd, (fsys with infds := (nextFD fsys, (fnm, 0)) :: fsys.infds)
                          with files updated_by (ALIST_FUPDKEY fnm (\x."")))
      od `;

(* update filesystem with newly opened file *)
val openFileFS_def = Define`
  openFileFS fnm fs off =
    case openFile fnm fs off of
      NONE => fs
    | SOME (_, fs') => fs'
`;

(* end of file is reached when the position index is the length of the file *)
val eof_def = Define`
  eof fd fsys =
    do
      (fnm,pos) <- ALOOKUP fsys.infds fd ;
      contents <- ALOOKUP fsys.files fnm ;
      return (LENGTH contents <= pos)
    od
`;

(* checks if a descriptor index is in the file descriptor *)
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
      let k = MIN n (MIN (LENGTH content - off) (SUC (THE (LHD fs.numchars)))) in
      return (TAKE n (DROP off content), bumpFD fd fs k)
    od `;

(* changes the offset of a file *)
val seek_def = Define`
  seek fd fs off =
    do
      (fnm, _) <- ALOOKUP fs.infds fd ;
      return(fs with infds updated_by (ALIST_FUPDKEY fd (I ## (\_. off))))
    od `;



(* replaces the content of the file in fs with filename fnm *)
val write_file_def = Define`
  write_file fs fnm content = 
    (fs with files := ((fnm, content) :: (A_DELKEY fnm fs.files)))
        with numchars := THE (LTL fs.numchars)`

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
      let k = MIN n (THE (LHD fs.numchars)) in
      return (k, write_file fs fnm (content ++ TAKE k chars))
    od `;


(* remove file from file descriptor *)
val closeFD_def = Define`
  closeFD fd fsys =
    do
       ALOOKUP fsys.infds fd ;
       return ((), fsys with infds := A_DELKEY fd fsys.infds)
    od
`;


(* ----------------------------------------------------------------------
    Making the above available as FFI functions
   ----------------------------------------------------------------------

    There are four operations to be used in the example:

    1. write char to stdout
    2. open file
    3. read char from file descriptor
    4. close file

   ---------------------------------------------------------------------- *)
(* truncate byte list after null byte and convert into char list *)
val getNullTermStr_def = Define`
  getNullTermStr (bytes : word8 list) =
     let sz = findi 0w bytes
     in
       if sz = LENGTH bytes then NONE
       else SOME(MAP (CHR o w2n) (TAKE sz bytes))
`

(* read file name from the first non null bytes
*  open the file with read access
*  write its file descriptor index in the first byte *)
val ffi_open_in_def = Define`
  ffi_open_in bytes fs =
    do
      fname <- getNullTermStr bytes;
      (fd, fs') <- openFile (implode fname) fs 0;
      assert(fd < 255);
      return (LUPDATE (n2w fd) 0 bytes, fs')
    od ++
    return (LUPDATE 255w 0 bytes, fs)`;

(* open append: 
      contents <- ALOOKUP fs.files (implode fname);
      (fd, fs') <- openFile (implode fname) fs (LENGTH contents);
      *)

(* open for writing
* position: the beginning of the file. 
* The file is truncated to zero length if it already exists. 
* TODO: It is created if it does not already exists.*)
val ffi_open_out_def = Define`
  ffi_open_out bytes fs =
    do
      fname <- getNullTermStr bytes;
      contents <- ALOOKUP fs.files (implode fname);
      (fd, fs') <- openFile_truncate (implode fname) fs 0;
      assert(fd < 255);
      return (LUPDATE (n2w fd) 0 bytes, fs')
    od ++
    return (LUPDATE 255w 0 bytes, fs)`;

(* 
* [descriptor index; number of char to read; buffer]
*   -> [return code; number of read chars; read chars]
* corresponding system call:
*  ssize_t read(int fd, void *buf, size_t count) *)
val ffi_read_def = Define`
  ffi_read bytes fs =
    do
    (* the buffer contains at least the number of requested bytes *)
      assert(LENGTH bytes >= w2n (HD (TL bytes)) + 2);
      (l, fs') <- read (w2n (HD bytes)) fs (w2n (HD (TL bytes)));
      (* return ok code and list of chars
      *  the end of the array may remain unchanged *)
      return (0w :: n2w (LENGTH l) ::
              MAP (n2w o ORD) l ++
              DROP (LENGTH l +2) bytes, fs')
      od ++ return ([1w], fs)`;
      (* inaccurate: "when an error occurs, [...] 
      * it is left unspecified whether the file position (if any) changes. *)

(* [descriptor index; number of chars to write; chars to write]
*    -> [return code; number of written chars]
* corresponding system call:
* ssize_t write(int fildes, const void *buf, size_t nbytes) *)
val ffi_write_def = Define`
  ffi_write bytes fs =
    do
    (* the buffer contains at least the number of requested bytes *)
      assert(LENGTH bytes >= 2);
      (nw, fs') <- write (w2n (HD bytes)) (w2n (HD (TL bytes))) 
                         (MAP (CHR o w2n) (TL (TL bytes))) fs;
      (* return ok code and list of chars *)
      return ([0w; n2w nw], fs')
    (* return error code *)
    od ++ return ([1w], fs)`;

(* closes a file given its descriptor index *)
val ffi_close_def = Define`
  ffi_close bytes fs =
    do
      assert(LENGTH bytes = 1);
      do
        (_, fs') <- closeFD (w2n (HD bytes)) fs;
        return (LUPDATE 1w 0 bytes, fs')
      od ++
      return (LUPDATE 0w 0 bytes, fs)
    od`;

(* given a file descriptor, returns 0, 1 if EOF is met. 255 is an error *)
val ffi_isEof_def = Define`
  ffi_isEof bytes fs =
    do
      assert(LENGTH bytes = 1);
      do
        b <- eof (w2n (HD bytes)) fs ;
        return (LUPDATE (if b then 1w else 0w) 0 bytes, fs)
      od ++
      return (LUPDATE 255w 0 bytes, fs)
    od`;

(* given a file descriptor and an offset, returns 0 and update fs or returns 1
* if an error is met *)
val ffi_seek = Define`
  ffi_seek bytes fs =
    do
      assert(LENGTH bytes = 2);
      do
        fs' <- seek (w2n (HD bytes)) fs (w2n (HD (TL bytes)));
        return(LUPDATE 0w 0 bytes, fs')
      od ++ 
      return (LUPDATE 1w 0 bytes, fs)
    od`;

(* -- *)

val encode_files_def = Define`
  encode_files fs = encode_list (encode_pair (Str o explode) Str) fs
`;

val encode_fds_def = Define`
  encode_fds fds =
     encode_list (encode_pair Num (encode_pair (Str o explode) Num)) fds
`;

val encode_def = zDefine`
  encode fs = cfHeapsBase$Cons
                (cfHeapsBase$Cons
                  (encode_files fs.files)
                  (encode_fds fs.infds))
                (Stream fs.numchars)
`

val decode_files_def = Define`
  decode_files f = decode_list (decode_pair (lift implode o destStr) destStr) f
`

val decode_fds_def = Define`
  decode_fds =
    decode_list (decode_pair destNum
                             (decode_pair (lift implode o destStr) destNum))
`;

val decode_def = zDefine`
  (decode (Cons (Cons files0 fds0) (Stream numchars0)) =
     do
        files <- decode_files files0 ;
        fds <- decode_fds fds0 ;
        return <| files := files ; infds := fds; numchars := numchars0 |>
     od) ∧
  (decode _ = fail)
`;

val fs_ffi_part_def = Define`
  fs_ffi_part =
    (encode,decode,
      [("open_in",ffi_open_in);
       ("open_out",ffi_open_out);
       ("read",ffi_read);
       ("write",ffi_write);
       ("close",ffi_close);
       ("seek",ffi_seek);
       ("isEof",ffi_isEof)])`;

val _ = export_theory();

(* TODO: 
* val flush : out_channel -> unit
*
* Flush the buffer associated with the given output channel, performing all
* pending writes on that channel. Interactive programs must be careful about
* flushing standard output and standard error at the right time.
*
* val pos_out : out_channel -> int
* given by seek 0, but can be larger than a char
*)
