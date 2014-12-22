open HolKernel boolLib bossLib lcsymtacs stringTheory relationTheory totoTheory pred_setTheory
val _ = ParseExtras.temp_tight_equality()
val _ = new_theory"mlstring"

(* TODO: move *)
val irreflexive_inv_image = store_thm("irreflexive_inv_image",
  ``!R f. irreflexive R ==> irreflexive (inv_image R f)``,
  SIMP_TAC std_ss [irreflexive_def,inv_image_def])

val trichotomous_inv_image = store_thm("trichotomous_inv_image",
  ``!R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous (inv_image R f)``,
  SIMP_TAC std_ss [trichotomous,inv_image_def,INJ_DEF,IN_UNIV] THEN
  METIS_TAC[])

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

val implode_BIJ = store_thm("implode_BIJ",
  ``BIJ implode UNIV UNIV``,
  rw[BIJ_IFF_INV] >>
  qexists_tac`explode` >>
  rw[implode_explode,
     explode_implode])

val explode_BIJ = store_thm("explode_BIJ",
  ``BIJ explode UNIV UNIV``,
  rw[BIJ_IFF_INV] >>
  qexists_tac`implode` >>
  rw[implode_explode,
     explode_implode])

(* TODO: don't explode/implode once CakeML supports string append *)
val strcat_def = Define`
  strcat s1 s2 = implode(explode s1 ++ explode s2)`
val _ = Parse.add_infix("^",480,Parse.LEFT)
val _ = Parse.overload_on("^",``λx y. strcat x y``)

val strlen_def = Define`
  strlen s = LENGTH (explode s)`

val mlstring_lt_def = Define`
  mlstring_lt (strlit s1) (strlit s2) ⇔
    string_lt s1 s2`

val mlstring_lt_inv_image = store_thm("mlstring_lt_inv_image",
  ``mlstring_lt = inv_image string_lt explode``,
  simp[inv_image_def,FUN_EQ_THM] >>
  Cases >> Cases >> simp[mlstring_lt_def])

val transitive_mlstring_lt = prove(
  ``transitive mlstring_lt``,
  simp[mlstring_lt_inv_image] >>
  match_mp_tac transitive_inv_image >>
  metis_tac[transitive_def,string_lt_trans])

val irreflexive_mlstring_lt = prove(
  ``irreflexive mlstring_lt``,
  simp[mlstring_lt_inv_image] >>
  match_mp_tac irreflexive_inv_image >>
  simp[irreflexive_def,string_lt_nonrefl])

val trichotomous_mlstring_lt = prove(
  ``trichotomous mlstring_lt``,
  simp[mlstring_lt_inv_image] >>
  match_mp_tac trichotomous_inv_image >>
  reverse conj_tac >- metis_tac[explode_BIJ,BIJ_DEF] >>
  metis_tac[trichotomous,string_lt_cases])

val StrongLinearOrder_mlstring_lt = store_thm("StrongLinearOrder_mlstring_lt",
  ``StrongLinearOrder mlstring_lt``,
  rw[StrongLinearOrder,trichotomous_mlstring_lt,
     StrongOrder,irreflexive_mlstring_lt,transitive_mlstring_lt])

val mlstring_cmp_def = Define`
  mlstring_cmp = TO_of_LinearOrder mlstring_lt`

val TotOrd_mlstring_cmp = store_thm("TotOrd_mlstring_cmp",
  ``TotOrd mlstring_cmp``,
  simp[mlstring_cmp_def] >>
  match_mp_tac TotOrd_TO_of_Strong >>
  simp[StrongLinearOrder_mlstring_lt])

val _ = export_theory()
