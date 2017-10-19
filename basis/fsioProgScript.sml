open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory mlcommandLineProgTheory fsFFITheory fsioConstantsProgTheory

val _ = new_theory"fsioProg";
val _ = translation_extends "fsioConstantsProg";

(* stdin, stdout, stderr *)
(* these are functions as append_prog rejects constants *)
val _ = process_topdecs`
    fun stdin () = Word8.fromInt 0;
    fun stdout () = Word8.fromInt 1;
    fun stderr () = Word8.fromInt 2
    ` |> append_prog

(* writei: higher-lever write function which calls #write until something is written or
* a filesystem error is raised and outputs the number of bytes written.
* It assumes that iobuff is initialised
* write: idem, but keeps writing until the whole (specified part of the) buffer
* is written *)

val _ =
  process_topdecs`fun writei fd n i =
    let val a = Word8Array.update iobuff 0 fd
        val a = Word8Array.update iobuff 1 n
        val a = Word8Array.update iobuff 2 i
        val a = #(write) "" iobuff in
        if Word8Array.sub iobuff 0 = Word8.fromInt 1
        then raise InvalidFD
        else
          let val nw = Word8.toInt(Word8Array.sub iobuff 1) in
            if nw = 0 then writei fd n i
            else nw
          end
    end
    fun write fd n i =
      if n = 0 then () else
        let val nw = writei fd (Word8.fromInt n) (Word8.fromInt i) in
          if nw < n then write fd (n-nw) (i+nw) else () end` |> append_prog

(* Output functions on given file descriptor *)
val _ =
  process_topdecs` fun write_char fd c =
    (Word8Array.update iobuff 3 (Word8.fromInt(Char.ord c)); write fd 1 0; ())

    fun print_char c = write_char (stdout()) c
    fun prerr_char c = write_char (stderr()) c
    ` |> append_prog

(* copies the content of a list after position i of an array a
* and terminates it with null byte *)
val _ = process_topdecs
  `fun copyi_nts a i clist =
      case clist of
          [] => Word8Array.update a i (Word8.fromInt 0)
        | c::cs => let
            val ordc = Char.ord c
            val cw = Word8.fromInt ordc
            val unit = Word8Array.update a i cw
            val suci = i + 1
          in
            copyi_nts a suci cs
          end` |> append_prog

(* writes a string into a file *)
val _ =
  process_topdecs` fun output fd s =
  if s = "" then () else
  let val z = String.size s
      val n = if z <= 255 then z else 255
      val fl = Word8Array.copyVec s 0 n iobuff 3
      val a = write fd n 0 in
         output fd (String.substring s n (z-n))
  end;
  fun print_string s = output (stdout()) s;
  fun prerr_string s = output (stderr()) s;

    ` |> append_prog

(* val print_newline : unit -> unit *)
val _ = process_topdecs`
    fun write_newline fd = write_char fd #"\n"
    fun print_newline () = write_char (stdout()) #"\n"
    fun prerr_newline () = write_char (stderr()) #"\n"
    ` |> append_prog


val _ = process_topdecs
  `fun str_to_w8array a s = let
     val clist = String.explode s
   in
      copyi_nts a 0 clist
   end` |> append_prog

val _ = process_topdecs`
fun openIn fname =
  let val a = str_to_w8array iobuff fname
      val a = #(open_in) "" iobuff in
        if Word8Array.sub iobuff 0 = Word8.fromInt 0
        then Word8Array.sub iobuff 1
        else raise BadFileName
  end
fun openOut fname =
  let val a = str_to_w8array iobuff fname
      val a = #(open_out) "" iobuff in
        if Word8Array.sub iobuff 0 = Word8.fromInt 0
        then Word8Array.sub iobuff 1
        else raise BadFileName
  end` |> append_prog
val _ = process_topdecs`

fun close fd =
  let val a = Word8Array.update iobuff 0 fd
      val a = #(close) "" iobuff in
        if Word8Array.sub iobuff 0 = Word8.fromInt 1
        then () else raise InvalidFD
  end` |> append_prog

(* wrapper for ffi call *)
val _ = process_topdecs`
  fun read fd n =
    let val a = Word8Array.update iobuff 0 fd
        val a = Word8Array.update iobuff 1 n in
          (#(read) "" iobuff;
          if Word8.toInt (Word8Array.sub iobuff 0) <> 1
          then Word8.toInt(Word8Array.sub iobuff 1)
          else raise InvalidFD)
    end` |> append_prog

(* reads 1 char *)
val _ = process_topdecs`
fun read_char fd =
    if read fd (Word8.fromInt 1) = 0 then raise EndOfFile
    else Word8Array.sub iobuff 3
` |> append_prog

(* val input : in_channel -> bytes -> int -> int -> int
* input ic buf pos len reads up to len characters from the given channel ic,
* storing them in byte sequence buf, starting at character number pos. *)
(* TODO: input0 as local fun *)
val _ =
  process_topdecs`
fun input fd buff off len =
let fun input0 off len count =
    let val nread = read fd (Word8.fromInt(min len 255)) in
        if nread = 0 then count else
          (Word8Array.copy iobuff 3 nread buff off;
           input0 (off + nread) (len - nread) (count + nread))
    end
in input0 off len 0 end
` |> append_prog

(* generalisable to splitl *)
val _ = process_topdecs`
fun find_newline s i l =
  if i >= l then l else
  if String.sub s i = #"\n" then i
  else find_newline s (i+1) l
fun split_newline s =
  let val l = String.size s
      val i = find_newline s 0 l in
        (String.substring s 0 i, String.substring s i (l-i))
  end
` |> append_prog

(* using lets/ifs as case take a while in xlet *)
(* if/if take a while in xcf *)
val _ = process_topdecs`
fun inputLine fd lbuf =
  let fun inputLine_aux lacc =
    let val nr = read fd (Word8.fromInt 255) in
      if nr = 0 then (String.concat (List.rev lacc), "") else
        let val lread = Word8Array.substring iobuff 3 nr
            val split = split_newline lread
            val line = fst split
            val lrest = snd split in
              if lrest = "" then inputLine_aux (line :: lacc)
              else (String.concat (List.rev("\n" :: line :: lacc)),
                    String.extract lrest 1 NONE)
        end
    end
  val split = split_newline lbuf
  val line = fst split
  val lrest = snd split in
    if lrest = "" then
      let val split' = inputLine_aux [] in
        (String.concat (line :: fst split' :: []), snd split') end
    else (String.concat (line :: "\n" :: []), String.extract lrest 1 NONE)
  end` |> append_prog

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
