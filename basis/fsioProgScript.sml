open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory mlcharioProgTheory fsFFITheory


val _ = new_theory"fsioProg";
val _ = translation_extends "mlcharioProg";

fun basis_st () = get_ml_prog_state ();

val _ = ml_prog_update (open_module "IO");
(* " *)

val _ = process_topdecs `
  exception BadFileName;
  exception InvalidFD;
  exception EndOfFile
` |> append_prog

(* 257 w8 array *)
val buff257_e = ``(App Aw8alloc [Lit (IntLit 257); Lit (Word8 0w)])``
val _ = ml_prog_update
          (add_Dlet (derive_eval_thm "buff257_loc" buff257_e) "buff257" [])
val buff257_loc_def = definition "buff257_loc_def"

(* stdin, stdout, stderr *)
(* these are functions as append_prog rejects constants *)
val _ = process_topdecs`
    val stdin () = Word8.fromInt 0;
    fun stdout () = Word8.fromInt 1;
    fun stderr () = Word8.fromInt  2
    ` |> append_prog
 (* 
    process_topdecs` val stdtest = Word8.fromInt 0 ` |> append_dec
*)

(* higher-lever write function which calls #write until something is written or
* an filesystem error is raised and outputs the number of bytes written.
* It assumes that buff257 is initialised *)

val _ =
  process_topdecs`fun write fd n =
    let val a = Word8Array.update buff257 0 fd
        val a = Word8Array.update buff257 1 n
        val a = #(write) buff257 in
        if Word8Array.sub buff257 0 = Word8.fromInt 1 
        then raise InvalidFD
        else 
          let val n = Word8.toInt(Word8Array.sub buff257 1) in
            if n = 0 then write fd n
            else n
          end
    end` |> append_prog

(* Output functions on given file descriptor *)
val _ = 
  process_topdecs` fun write_char fd c = 
    let val a = Word8Array.update buff257 2 (Word8.fromInt(Char.ord c))
        val i = Word8.fromInt 1
        val r = write fd i
    in () end

    fun print_char c = write_char (stdout()) c
    fun prerr_char c = write_char (stderr()) c
    ` |> append_prog

(* copies the content of a list after position i of an array a *)
val _ = process_topdecs
  `fun copyi a i clist =
      case clist of
          [] => ()
        | c::cs => let
            val ordc = Char.ord c
            val cw = Word8.fromInt ordc
            val unit = Word8Array.update a i cw
            val suci = i + 1
          in
            copyi a suci cs
          end` |> append_prog

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
(* writes n chars of a w8array starting on index i  *)
val _ = 
  process_topdecs` fun write_w8array fd w i n =
  if n <= 0 then ()
  else
    let val m = Word8.fromInt(min n 255)
        val a = copyi buff257 2 (TODO) 
        val nw = write fd m
    in
          write_w8array fd w (i + nw) (n - nw)
    end` |> append_prog

(* val print_newline : unit -> unit *)
val _ = process_topdecs`
    fun write_newline fd = write_char fd #"\n"
    fun print_newline () = write_newline (stdin())
    fun prerr_newline () = write_newline (stdout())
    ` |> append_prog


val _ = process_topdecs
  `fun str_to_w8array a s = let
     val clist = String.explode s
   in
      copyi_nts a 0 clist
   end` |> append_prog

val _ = process_topdecs`
fun open_in fname =
  let val a = str_to_w8array buff257 fname
      val a = #(open_in) buff257 in
        if Word8Array.sub buff257 0 = Word8.fromInt 0 
        then Word8Array.sub buff257 1
        else raise BadFileName
  end
fun open_out fname =
  let val a = str_to_w8array buff257 fname
      val a = #(open_out) buff257 in
        if Word8Array.sub buff257 0 = Word8.fromInt 0 
        then Word8Array.sub buff257 1
        else raise BadFileName
  end` |> append_prog

(* val input : in_channel -> bytes -> int -> int -> int
* input ic buf pos len reads up to len characters from the given channel ic,
* storing them in byte sequence buf, starting at character number pos. *)
val _ = 
  process_topdecs`
fun input fd buf pos len =
  let val a = Word8Array.update buff257 0 fd
      fun input_aux pos len count =
      let val a = Word8Array.update buff257 1 (min len 255)
        val a = #(read) buff257
        val res = Word8.toInt (Word8Array.sub buff257 0)
        val nread = Word8.toInt (Word8Array.sub buff257 1)
      in           
        if res = 1 then raise InvalidFD
        else if nread = 0 then count
        else 
          let val a = Word8Array.copy_aux buff257 buf pos nread 2 in
            if nread < len then input_aux (pos + nread) (len - nread) count
            else (count + nread)
          end
      end 
        in input_aux pos len count
  end` |> append_prog

(* reads 1 char *)
val _ = process_topdecs`
fun read_char fd =
let val a = Word8Array.update buff257 0 fd
  val a = Word8Array.update buff257 1 1
  val a = #(read) buff257
  val res = Word8.toInt (Word8Array.sub buff257 0)
  val nread = Word8.toInt (Word8Array.sub buff257 1) 
  in
    if res = 1 then raise InvalidFD
    else if nread = 0 then raise EndOfFile
    else Word8Array.sub buff257 1
  end` |> append_prog


val _ = ml_prog_update (close_module NONE);
val _ = export_theory();
