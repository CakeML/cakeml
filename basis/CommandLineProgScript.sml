(*
  A module about command-line arguments for the CakeML standard basis
  library.
*)
open preamble
     ml_translatorLib ml_progLib ml_translatorTheory
     HashtableProgTheory basisFunctionsLib

val _ = new_theory "CommandLineProg";

val _ = translation_extends "HashtableProg";

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val _ = ml_prog_update (open_module "CommandLine")

val _ = ml_prog_update open_local_block;

val e = (append_prog o process_topdecs) `
  fun read16bit a =
    let
      val w0 = Word8Array.sub a 0
      val w1 = Word8Array.sub a 1
    in Word8.toInt w0 + (Word8.toInt w1 * 256) end`

val e = (append_prog o process_topdecs) `
  fun write16bit a i =
    (Word8Array.update a 0 (Word8.fromInt i);
     Word8Array.update a 1 (Word8.fromInt (i div 256)))`

val e = (append_prog o process_topdecs) `
  fun cloop a n acc =
    if n = 0 then acc else
      let
        val n = n - 1
        val u = write16bit a n
        val u = #(get_arg_length) "" a
        val l = read16bit a
        val tmp = Word8Array.array (max 2 l) (Word8.fromInt 0)
        val u = write16bit tmp n
        val u = #(get_arg) "" tmp
        val arg = Word8Array.substring tmp 0 l
      in cloop a n (arg :: acc) end`

val _ = ml_prog_update open_local_in_block;

val e = (append_prog o process_topdecs) `
  fun cline u =
    case u of () => (* in order to make type unit -> ... *)
    let
      val a = Word8Array.array 2 (Word8.fromInt 0)
      val u = #(get_arg_count) "" a
      val n = read16bit a
    in cloop a n [] end`;

val _ = (append_prog o process_topdecs) `fun name u = List.hd (cline u)`

val _ = (append_prog o process_topdecs) `fun arguments u = List.tl (cline u)`

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
