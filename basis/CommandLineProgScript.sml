(*
  A module about command-line arguments for the CakeML standard basis
  library.
*)
Theory CommandLineProg
Ancestors
  ml_translator HashtableProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "HashtableProg";

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val cakeml = append_prog o process_topdecs;

val _ = ml_prog_update (open_module "CommandLine")

val _ = ml_prog_update open_local_block;

Quote cakeml:
  fun read16bit a =
    let
      val w0 = Word8Array.sub a 0
      val w1 = Word8Array.sub a 1
    in Word8.toInt w0 + (Word8.toInt w1 * 256) end
End

Quote cakeml:
  fun write16bit a i =
    (Word8Array.update a 0 (Word8.fromInt i);
     Word8Array.update a 1 (Word8.fromInt (i div 256)))
End

Quote cakeml:
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
      in cloop a n (arg :: acc) end
End

val _ = ml_prog_update open_local_in_block;

Quote cakeml:
  fun cline u =
    case u of () => (* in order to make type unit -> ... *)
    let
      val a = Word8Array.array 2 (Word8.fromInt 0)
      val u = #(get_arg_count) "" a
      val n = read16bit a
    in cloop a n [] end
End

Quote cakeml:
  fun name u = List.hd (cline u)
End

Quote cakeml:
  fun arguments u = List.tl (cline u)
End

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

