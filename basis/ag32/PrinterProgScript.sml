open preamble ml_translatorLib ml_progLib basisFunctionsLib
     Word8ArrayProgTheory printFFITheory

val _ = new_theory"PrinterProg"

val _ = translation_extends"Word8ArrayProg"

val () = generate_sigs := true;

val _ = ml_prog_update (open_module "Printer");

val print = process_topdecs`
  fun print s =
    if String.size s < 64 then
      #(print) s (Word8Array.array 0 (Word8.fromInt 0))
    else
      (#(print) (String.substring s 0 63) (Word8Array.array 0 (Word8.fromInt 0));
       print (String.extract s 63 None))`;

val () = append_prog print;

val sigs = module_signatures ["print"];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory();
