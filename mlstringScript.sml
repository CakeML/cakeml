(*
   Small theory of wrapped strings, so the translator can distinguish
   them from char lists and can target CakeML strings directly.
*)
open HolKernel boolLib bossLib lcsymtacs stringTheory relationTheory totoTheory pred_setTheory listTheory
val _ = ParseExtras.temp_tight_equality()
val _ = new_theory"mlstring"

(* TODO: move *)
val irreflexive_inv_image = Q.store_thm("irreflexive_inv_image",
  `!R f. irreflexive R ==> irreflexive (inv_image R f)`,
  SIMP_TAC std_ss [irreflexive_def,inv_image_def])

val trichotomous_inv_image = Q.store_thm("trichotomous_inv_image",
  `!R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous (inv_image R f)`,
  SIMP_TAC std_ss [trichotomous,inv_image_def,INJ_DEF,IN_UNIV] THEN
  METIS_TAC[])

(* Defines strings as a separate type from char list. This theory should be
   moved into HOL, either as its own theory, or as an addendum to stringTheory *)

val _ = Datatype`mlstring = strlit string`

val implode_def = Define`
  implode = strlit`

val strlen_def = Define`
  strlen (strlit s) = LENGTH s`

val strsub_def = Define`
  strsub (strlit s) n = EL n s`;

val _ = export_rewrites["strlen_def","strsub_def"];

val explode_aux_def = Define`
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) =
    strsub s n :: (explode_aux s (n+1) len))`;
val _ = export_rewrites["explode_aux_def"];

val explode_aux_thm = Q.store_thm("explode_aux_thm",
  `∀max n ls.
    n + max = LENGTH ls ⇒
    explode_aux (strlit ls) n max = DROP n ls`,
  Induct \\ rw[] \\ fs[LENGTH_NIL_SYM,DROP_LENGTH_TOO_LONG]
  \\ match_mp_tac (GSYM rich_listTheory.DROP_EL_CONS)
  \\ simp[]);

val explode_def = Define`
  explode s = explode_aux s 0 (strlen s)`;

val explode_thm = Q.store_thm("explode_thm[simp]",
  `explode (strlit ls) = ls`,
  rw[explode_def,SIMP_RULE std_ss [] explode_aux_thm]);

val explode_implode = Q.store_thm("explode_implode",
  `∀x. explode (implode x) = x`,
  rw[implode_def])

val implode_explode = Q.store_thm("implode_explode",
  `∀x. implode (explode x) = x`,
  Cases >> rw[implode_def])

val explode_11 = Q.store_thm("explode_11",
  `∀s1 s2. explode s1 = explode s2 ⇔ s1 = s2`,
  Cases >> Cases >> simp[])

val implode_BIJ = Q.store_thm("implode_BIJ",
  `BIJ implode UNIV UNIV`,
  rw[BIJ_IFF_INV] >>
  qexists_tac`explode` >>
  rw[implode_explode,
     explode_implode])

val explode_BIJ = Q.store_thm("explode_BIJ",
  `BIJ explode UNIV UNIV`,
  rw[BIJ_IFF_INV] >>
  qexists_tac`implode` >>
  rw[implode_explode,
     explode_implode])

(* TODO: don't explode/implode once CakeML supports string append *)
val strcat_def = Define`
  strcat s1 s2 = implode(explode s1 ++ explode s2)`
val _ = Parse.add_infix("^",480,Parse.LEFT)
val _ = Parse.overload_on("^",``λx y. strcat x y``)

val mlstring_lt_def = Define`
  mlstring_lt (strlit s1) (strlit s2) ⇔
    string_lt s1 s2`

val mlstring_lt_inv_image = Q.store_thm("mlstring_lt_inv_image",
  `mlstring_lt = inv_image string_lt explode`,
  simp[inv_image_def,FUN_EQ_THM] >>
  Cases >> Cases >> simp[mlstring_lt_def])

val transitive_mlstring_lt = Q.prove(
  `transitive mlstring_lt`,
  simp[mlstring_lt_inv_image] >>
  match_mp_tac transitive_inv_image >>
  metis_tac[transitive_def,string_lt_trans])

val irreflexive_mlstring_lt = Q.prove(
  `irreflexive mlstring_lt`,
  simp[mlstring_lt_inv_image] >>
  match_mp_tac irreflexive_inv_image >>
  simp[irreflexive_def,string_lt_nonrefl])

val trichotomous_mlstring_lt = Q.prove(
  `trichotomous mlstring_lt`,
  simp[mlstring_lt_inv_image] >>
  match_mp_tac trichotomous_inv_image >>
  reverse conj_tac >- metis_tac[explode_BIJ,BIJ_DEF] >>
  metis_tac[trichotomous,string_lt_cases])

val StrongLinearOrder_mlstring_lt = Q.store_thm("StrongLinearOrder_mlstring_lt",
  `StrongLinearOrder mlstring_lt`,
  rw[StrongLinearOrder,trichotomous_mlstring_lt,
     StrongOrder,irreflexive_mlstring_lt,transitive_mlstring_lt])

val mlstring_cmp_def = Define`
  mlstring_cmp = TO_of_LinearOrder mlstring_lt`

val TotOrd_mlstring_cmp = Q.store_thm("TotOrd_mlstring_cmp",
  `TotOrd mlstring_cmp`,
  simp[mlstring_cmp_def] >>
  match_mp_tac TotOrd_TO_of_Strong >>
  simp[StrongLinearOrder_mlstring_lt])

val ALL_DISTINCT_MAP_implode = Q.store_thm("ALL_DISTINCT_MAP_implode",
  `ALL_DISTINCT ls ⇒ ALL_DISTINCT (MAP implode ls)`,
  strip_tac >>
  match_mp_tac ALL_DISTINCT_MAP_INJ >>
  rw[implode_def])
val _ = export_rewrites["ALL_DISTINCT_MAP_implode"]

val ALL_DISTINCT_MAP_explode = Q.store_thm("ALL_DISTINCT_MAP_explode",
  `∀ls. ALL_DISTINCT (MAP explode ls) ⇔ ALL_DISTINCT ls`,
  gen_tac >> EQ_TAC >- MATCH_ACCEPT_TAC ALL_DISTINCT_MAP >>
  STRIP_TAC >> MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >>
  simp[explode_11])
val _ = export_rewrites["ALL_DISTINCT_MAP_explode"]

val _ = export_theory()
