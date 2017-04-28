open preamble
     ml_translatorTheory ml_translatorLib ml_progLib
     cfTacticsBaseLib cfTacticsLib basisFunctionsLib
     mlstringTheory mlcharioProgTheory fsFFITheory


val _ = new_theory"ioProg";
val _ = translation_extends "mlcharioProg";

fun basis_st () = get_ml_prog_state ();

val _ = ml_prog_update (open_module "IO");
(* " *)

val _ = process_topdecs `
  exception BadFileName;
  exception InvalidFD
` |> append_prog

(* 255 w8 array *)
val buff255_e = ``(App Aw8alloc [Lit (IntLit 255); Lit (Word8 0w)])``
val _ = ml_prog_update
          (add_Dlet (derive_eval_thm "buff255_loc" buff255_e) "buff255" [])
val buff255_loc_def = definition "buff255_loc_def"
(* from Ocaml Pervasives lib *)
val tm = ``Dlet
        (<|row := 1; col := 16; offset := 0|>,
         <|row := 1; col := 28; offset := 0|>) (Pvar "stdin")
        (Lit (IntLit 0))``
(* stdin, stdout, stderr *)
(* these are functions as append_prog rejects constants *)
val _ = process_topdecs`
    fun stdin () = Word8.fromInt 0
    fun stdout () = Word8.fromInt 1;
    fun stderr () = Word8.fromInt  2
    ` |> append_prog
(*
* Output functions on given file descriptor
* TODO: convert to word8 *)
val _ = 
  process_topdecs` fun write_char fd c = 
    let val a = Word8Array.update buff255 0 fd
        val a = Word8Array.update buff255 1 1 
        val a = Word8Array.update buff255 2 (ord c)
        val a = #(write) buff255
    in 
      if Word8Array.sub buff255 0 = Word8.fromInt 1 
      then raise InvalidFD (* inaccurate *)
      else ()
    end

    fun print_char c = write_char 1 c
    fun prerr_char c = write_char 2 c
    ` |> append_prog

(* writes a w8array between indices i and j *)
val _ = 
  process_topdecs` fun write_w8array fd w i n =
  if n <= 0 then ()
  else
    let val m = min n 253
        val a = Word8Array.update buff255 0 fd
        val a = Word8Array.update buff255 1 m
        val a = Word8Array.copy_aux w buff255 2 m i
        (* array_copy_aux_spec should be more complete *)
        val a = #(write) buff255
        (* TODO: handle errors *)
    in
      write_w8array w (i + 253) (n-253)
    end ` |> append_prog



(* Print a string on standard output.
*
* val print_bytes : bytes -> unit
* val print_int : int -> unit
* val print_float : float -> unit
* val print_string : string -> unit 
*)

(*
* val print_endline : string -> unit
*
* Print a string, followed by a newline character, on standard output and flush
* standard output.
*
* val print_newline : unit -> unit *)
val _ = process_topdecs` fun write_newline fd =
    let val a = Word8Array.update buff255 0 fd
        val a = Word8Array.update buff255 1 1
        val a = Word8Array.update buff255 2 (ord #"\n")
    in
      #(write) buff255
    end
    fun print_newline () = write_newline 1 
    fun prerr_newline () = write_newline 2 
    ` |> append_prog
(*
* Print a newline character on standard output, and flush standard output. This
* can be used to simulate line buffering of standard output.
*)
