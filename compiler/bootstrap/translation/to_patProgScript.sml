(*
  Translate the backend phase from flatLang to patLang.
*)
open preamble

val _ = new_theory "to_patProg";

(* FIXME: retire entirely *)

val _ = export_theory ();
