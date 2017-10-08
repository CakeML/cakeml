open preamble
     ml_monad_translatorLib
     test1_monTheory
     (*ml_monadBaseLib*)

val _ = new_theory "test1_transl";

val _ = m_translation_extends "test1_mon";

(* Cannot translate st_ex_bind. *)
val r = m_translate bar_def;

(* Cannot type-instantiate input theorem *)
val r = m_translate simple_def;

(* Other notes:

   When translating bar_def, the translation starts translating
   STATE_REFS_TYPE_def. Why? This should be done when translating
   the functions in test1_monTheory.
*)

val _ = export_theory ();

