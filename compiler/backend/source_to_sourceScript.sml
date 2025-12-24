(*
  This phase collects all source-to-source transformations.
 *)
Theory source_to_source
Ancestors
  source_let misc[qualified]
Libs
  preamble


Definition compile_def:
  compile = source_let$compile_decs
End

