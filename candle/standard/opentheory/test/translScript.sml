open preamble
     ml_monad_translatorLib
     testTheory
open ml_monadBaseLib

val _ = new_theory "testTwo";

val _ = translation_extends "test"

val _ = (use_full_type_names := false);
(*val _ = hide "state"*)

(*
  Try to translate something using the foo function in
  testTheory.
*)

(* --- Monad syntax --- *)

val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax();
val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val baz_def = Define `
  baz (n: num) =
    do
      y <- foo_fun ();
      res <- get_foo;
      return (n > res)
    od`;

val r = m_translate baz_def


(*
  type_of ``get_foo``
  type_of ``baz``
  type_of ``set_foo``
  type_of ``st_ex_bind``
  type_of ``st_ex_return``
  type_of ``foo_fun``
*)

(*
  Parse.overload_info_for "st_ex_bind"
  Parse.overload_info_for "monad_bind"
*)
(*type_of ``*)

val _ = export_theory ();

