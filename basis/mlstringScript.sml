(*
   Small theory of wrapped strings, so the translator can distinguish
   them from char lists and can target CakeML strings directly.
*)
open preamble

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

(*
It should be like this when the primitives change in CakeML:

(* assume these are primitive... *)
val length_def = Define`
  length (strlit s) = LENGTH s`;
val sub_def = Define`
  sub (strlit s) n = EL n s`;
val implode_def = Define`
  implode = strlit`

val explode_aux_def = Define`
  explode_aux s n = if n < length s then sub s n :: (explode_aux s (n+1)) else []`;
val explode_def = Define`
  explode s = explode_aux s 0`;
val explode_aux_thm = Q.prove(
  `explode_aux (strlit s) n = DROP n s`,

val explode_thm = Q.store_thm("explode_thm",
  `explode (strlit s) = s`,
  ...);
*)

val implode_def = Define`
  implode = strlit`

val explode_def = Define`
  explode (strlit ls) = ls`
val _ = export_rewrites["explode_def"]

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

val strlen_def = Define`
  strlen s = LENGTH (explode s)`;

val sub_def = Define`
  sub s n =  EL n (explode s)`;

(* TODO: write a bunch of string functions in terms of strlen and sub *)
(* TODO: strlen should be called size ? or length ? *)


val extract_aux_def = tDefine "extract_aux"`
    extract_aux s n max =
    if max <= n
      then []
    else (sub s n)::(extract_aux s (n + 1) max)`
(wf_rel_tac `measure (\(s, n, max). max - n)`)


val extract_def = Define`
  extract s i opt = case opt of
    (SOME x) => implode (extract_aux s i (THE opt))
    | NONE => implode (extract_aux s i (strlen s))`;

val substring_def = Define`
  substring s i j = implode (extract_aux s i j)`;


(* TODO: don't explode/implode once CakeML supports string append *)
val strcat_def = Define`
  strcat s1 s2 = implode(explode s1 ++ explode s2)`
val _ = Parse.add_infix("^",480,Parse.LEFT)
val _ = Parse.overload_on("^",``λx y. strcat x y``)

val stringListToChars_def = Define`
  stringListToChars l = case l of 
    [] => []
    | ([]::t) => stringListToChars t
    | ((hh::ht)::t) => hh::stringListToChars(ht::t)`;

val concat_def = Define`
  concat l = implode (stringListToChars l)`;

(*NEED TO PROVE TERMINATION*)
(*may be a bit complex to attempt to save memory (passing around a lot)*)
val concatWith_aux_def = Define`
  concatWith_aux l s ss bool =
  if bool then
    case l of
      [] => []
      | []::[] => []
      | ([]::t) => concatWith_aux t s s F
      | ((hh::ht)::t) => hh::(concatWith_aux (ht::t) s ss T)
  else
    case ss of
      [] => concatWith_aux l s ss T
      | (h::t) => h::(concatWith_aux l s t F) `;

val concatWith_def = Define`
    concatWith s l = implode (concatWith_aux l s s T)`;

val str_def = Define`
  str (c: char) = [c]`;

val explode_aux_def = tDefine "explode_aux"`
  explode_aux s max n =
    if max <= n then []
    else (sub s n)::(explode_aux s max (n + 1))`
(wf_rel_tac `measure (\(s, max, n). max - n)`);

val explode_def = Define`
  explode s = explode_aux s (strlen s) 0`;

val translate_aux_def = tDefine "translate_aux"`
  translate_aux f s max n = 
    if max <= n then []
    else f (sub s n)::(translate_aux f s max (n + 1))`
(wf_rel_tac `measure (\(f, s, max, n). max - n)`);


val translate_def = Define`
  translate f s = implode (translate_aux f s (strlen s) 0)`;
(*TODO: Check the functionality *)
val tokens_aux_def = tDefine "tokens_aux"`
  tokens_aux f s ss max n =
  if max <= n
    then []
  else if (f (sub s n) /\ ~(ss = []))
    then ss::(tokens_aux f s [] max (n + 1))
  else if f (sub s n)
    then tokens_aux f s ss max (n + 1)
  else tokens_aux f s ((sub s n)::ss) max (n + 1)`
(wf_rel_tac `measure (\(f, s, ss, max, n). max - n)`);



val tokens_def = Define `
  tokens f s = tokens_aux f s [] (strlen s) 0`;

fun tokens_aux (f : char -> bool) s ss max n =
  if max <= n
    then []
  else if (f (String.sub s n)) andalso not(ss = [])
    then ss::(tokens_aux f s [] max (n + 1))
  else if f (String.sub s n)
    then tokens_aux f s ss max (n + 1)
  else tokens_aux f s ((String.sub s n)::ss) max (n + 1)


(*TODO: Check the functionality *)
val fields_aux_def = tDefine "fields_aux"`
  fields_aux f s ss max n =
  if max <= n
    then []
  else if f (sub s n)
    then ss::(fields_aux f s [] max (n + 1))
  else fields_aux f s ((sub s n)::ss) max (n + 1)`
(wf_rel_tac `measure (\(f, s, ss, max, n). max - n)`);

val fields_def = Define`
  fields f s = fields_aux f s [] (strlen s) 0`;



(*this could be one less iteration if the check is for n + 1 *)
val isStringThere_aux_def = tDefine "isPrefix_aux"`
  isStringThere_aux s1 s2 max n =
  if max <= n
    then T
  else if (sub s1 n) = (sub s2 n)
    then isStringThere_aux s1 s2 max (n + 1)
  else F`
(wf_rel_tac `measure (\(s1, s2, max, n). max - n)`);

val isPrefix_def = Define`
  isPrefix s1 s2 = isStringThere_aux s1 s2 (strlen s1) 0`;

val isSuffix_def = Define`
  isSuffix s1 s2 = isStringThere_aux s1 s2 (strlen s2) ((strlen s2) - (strlen s1))`;

val isSubstring_aux_def = tDefine "isSubstring_aux"`
  isSubstring_aux s1 s2 len1 max n =
    if max <= n
      then F
    else if isStringThere_aux s1 s2 (n + len1) n
      then T
    else isSubstring_aux s1 s2 len1 max (n + 1)`
(wf_rel_tac `measure (\(s1, s2, len1, max, n). max - n)`);

val isSubstring_def = Define`
  isSubstring s1 s2 = isSubstring_aux s1 s2 (strlen s1) ((strlen s2) - (strlen s1)) 0`;



val compare_aux_def = tDefine "compare_aux"`
  compare_aux (s1 : mlstring) s2 max ord n =
    if max <= n
      then ord
    else if (sub s1 n) > (sub s2 n)
      then GREATER
    else if (sub s1 n) < (sub s2 n)
      then LESS
    else compare_aux s1 s2 max ord (n + 1)`
(wf_rel_tac `measure (\(s1, s2, max, ord, n). max - n)`);

val compare_def = Define`
  compare_def s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 (strlen s1) GREATER 0
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 (strlen s2) LESS 0
  else compare_aux s1 s2 (strlen s2) EQUAL 0`;



val collate_aux_def = tDefine "collate_aux"`
  collate_aux f (s1 : mlstring) s2 max ord n =
    if max <= n
      then ord
    else if f (sub s1 n) (sub s2 n) = EQUAL
      then collate_aux f s1 s2 max ord (n + 1)
    else
      f (sub s1 n) (sub s2 n)`
(wf_rel_tac `measure (\(f, s1, s2, max, ord, n). max - n)`);

val collate_def = Define`
  collate f s1 s2 =
  if (strlen s1) < (strlen s2)
    then collate_aux f s1 s2 (strlen s1) GREATER 0
  else if (strlen s2) < (strlen s1)
    then collate_aux f s1 s2 (strlen s2) LESS 0
  else collate_aux f s1 s2 (strlen s2) EQUAL 0`;






























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
