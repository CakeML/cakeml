open preamble ml_translatorLib

val _ = new_theory "Test";

(* Tests *)
val _ = Hol_datatype `exn_type = Fail of string | Subscript`
val _ = register_type ``:string``

val ty = ``:exn_type``
val is_exn_type = true

val _ = register_exn_type ``:exn_type``

val _ = export_theory ()
