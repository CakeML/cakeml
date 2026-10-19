(*
  This phase collects all source-to-source transformations.
 *)
Theory source_to_source
Ancestors
  source_dce source_let source_lift_consts
Libs
  preamble


Definition compile_def:
  compile p =
    let p = source_dce$compile_decs p in
    let p = source_let$compile_decs p in
    let p = source_lift_consts$compile_decs p in
      p
End

Definition inc_compile_def:
  inc_compile p =
    let p = source_let$compile_decs p in
    let p = source_lift_consts$compile_decs p in
      p
End
