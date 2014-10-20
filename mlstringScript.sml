open HolKernel boolLib bossLib lcsymtacs stringTheory
val _ = ParseExtras.temp_tight_equality()
val _ = new_theory"mlstring"

(* Defines strings as a separate type from char list. This theory should be
   moved into HOL, either as its own theory, or as an addendum to stringTheory *)

val _ = Datatype`mlstring = strlit string`

val implode_def = Define`
  implode = strlit`

val explode_def = Define`
  explode (strlit ls) = ls`
val _ = export_rewrites["explode_def"]

val explode_implode = store_thm("explode_implode",
  ``∀x. explode (implode x) = x``,
  rw[implode_def])

val implode_explode = store_thm("implode_explode",
  ``∀x. implode (explode x) = x``,
  Cases >> rw[implode_def])

val explode_11 = store_thm("explode_11",
  ``∀s1 s2. explode s1 = explode s2 ⇔ s1 = s2``,
  Cases >> Cases >> simp[])

val _ = export_theory()
