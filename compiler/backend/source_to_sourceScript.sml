(*
  This phase collects all source-to-source transformations.
 *)
Theory source_to_source
Ancestors
  source_let source_weakenlet misc[qualified]
Libs
  preamble


Definition compile_def:
  compile prog =
       let prog = source_let$compile_decs prog in
       let prog = source_weakenlet$compile_decs prog in
           prog
End

