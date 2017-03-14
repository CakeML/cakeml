open preamble
    mllistTheory miscTheory totoTheory

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

val concat_def = Define`
  concat l = strlit (FLAT (MAP (λs. case s of strlit x => x) l))`;

val concat_nil = Q.store_thm("concat_nil[simp]",
  `concat [] = strlit ""`, EVAL_TAC);

val _ = export_rewrites["strlen_def","strsub_def"];


val explode_aux_def = Define`
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) =
    strsub s n :: (explode_aux s (n + 1) len))`;
val _ = export_rewrites["explode_aux_def"];

val explode_aux_thm = Q.store_thm("explode_aux_thm",
  `∀max n ls.
    (n + max = LENGTH ls) ⇒
    (explode_aux (strlit ls) n max = DROP n ls)`,
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
  `∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2)`,
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

val LENGTH_explode = Q.store_thm("LENGTH_explode",
  `LENGTH (explode s) = strlen s`,
  Cases_on`s` \\ simp[]);

val concat_thm = Q.store_thm("concat_thm",
  `concat l = implode (FLAT (MAP explode l))`,
  rw[concat_def,implode_def] \\
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\
  rw[FUN_EQ_THM] \\ CASE_TAC \\ simp[]);

val extract_aux_def = Define`
  (extract_aux s n 0 = []) /\
  (extract_aux s n (SUC len) = strsub s n:: extract_aux s (n + 1) len)`;

val extract_def = Define`
  extract s i opt =
    if strlen s <= i
      then implode []
    else case opt of
      (SOME x) => implode (extract_aux s i (MIN (strlen s - i) x))
      | NONE => implode (extract_aux s i ((strlen s) - i))`;

val substring_def = Define`
  substring s i j =
    if strlen s <= i
      then implode []
    else implode (extract_aux s i (MIN (strlen s - i) j))`;

val extract_aux_thm = Q.prove (
  `!s n len. (n + len <= strlen s) ==> (extract_aux s n len = SEG len n (explode s))`,
  Cases_on `s` \\ Induct_on `len` >-
  rw[extract_aux_def, SEG] \\
  fs [extract_aux_def, strsub_def, strlen_def, explode_def] \\
  rw [EL_SEG, SEG_TAKE_BUTFISTN] \\
  rw [TAKE_SUM, take1_drop, DROP_DROP, DROP_EL_CONS]
);

(*This proves that the functions are the same for values where SEG is defined*)
val extract_thm = Q.store_thm (
  "extract_thm",
  `!s i opt. (i < strlen s) ==> (extract s i opt = (case opt of
    (SOME x) => implode (SEG (MIN (strlen s - i) x) i (explode s))
    | NONE => implode (SEG ((strlen s) - i) i (explode s))))`,
    Cases_on `opt` >- rw [extract_def, extract_aux_thm, implode_def, strlen_def, MIN_DEF] \\
    rw [extract_def] \\ AP_TERM_TAC ORELSE AP_THM_TAC \\ rw[MIN_DEF, extract_aux_thm]
);

val substring_thm = Q.store_thm (
  "substring_thm",
  `!s i j. (i < strlen s) ==> (substring s i j = implode (SEG (MIN (strlen s - i) j) i (explode s)))`,
  rw [substring_def] \\ AP_TERM_TAC \\ rw [MIN_DEF, extract_aux_thm]
);



val strcat_def = Define`strcat s1 s2 = concat [s1; s2]`
val _ = Parse.add_infix("^",480,Parse.LEFT)
val _ = Parse.overload_on("^",``λx y. strcat x y``)

val concat_cons = Q.store_thm("concat_cons",
  `concat (h::t) = strcat h (concat t)`,
  rw[strcat_def,concat_def]);

val strcat_thm = Q.store_thm("strcat_thm",
  `strcat s1 s2 = implode (explode s1 ++ explode s2)`,
  rw[strcat_def,concat_def]
  \\ CASE_TAC \\ rw[] \\ CASE_TAC \\ rw[implode_def]);

val strcat_assoc = Q.store_thm("strcat_assoc",
  `!s1 s2 s3.
    s1 ^ s2 ^ s3 = s1 ^ (s2 ^ s3)`,
    rw[strcat_def,concat_def]);

val strcat_nil = Q.store_thm("strcat_nil[simp]",
  `(strcat (strlit "") s = s) ∧
   (strcat s (strlit "") = s)`,
  rw[strcat_def,concat_def] \\ CASE_TAC \\ rw[]);

val implode_STRCAT = Q.store_thm("implode_STRCAT",
  `!l1 l2.
    implode(STRCAT l1 l2) = implode l1 ^ implode l2`,
    rw[implode_def, strcat_def, concat_def]
);


val concatWith_aux_def = tDefine "concatWith_aux"`
  (concatWith_aux s [] bool = implode []) /\
  (concatWith_aux s (h::t) T = strcat h (concatWith_aux s t F)) /\
  (concatWith_aux s (h::t) F = strcat s (concatWith_aux s (h::t) T))`
  (wf_rel_tac `inv_image ($< LEX $<) (\(s,l,b). (LENGTH l, if b then 0n else 1))` \\
  rw[]);

val concatWith_def = Define`
  concatWith s l = concatWith_aux s l T`;

val concatWith_CONCAT_WITH_aux = Q.prove (
  `!s l fl. (CONCAT_WITH_aux s l fl = REVERSE fl ++ explode (concatWith (implode s) (MAP implode l)))`,
  ho_match_mp_tac CONCAT_WITH_aux_ind
  \\ rw[CONCAT_WITH_aux_def, concatWith_def, implode_def, concatWith_aux_def, strcat_thm]
  >-(Induct_on `l` \\ rw[MAP, implode_def, concatWith_aux_def, strcat_thm]
  \\ Cases_on `l` \\ rw[concatWith_aux_def, explode_implode, strcat_thm, implode_def])
);

val concatWith_CONCAT_WITH = Q.store_thm ("concatWith_CONCAT_WITH",
  `!s l. CONCAT_WITH s l = explode (concatWith (implode s) (MAP implode l))`,
    rw[concatWith_def, CONCAT_WITH_def, concatWith_CONCAT_WITH_aux]
);

val str_def = Define`
  str (c: char) = implode [c]`;

val translate_aux_def = Define`
  (translate_aux f s n 0 = []) /\
  (translate_aux f s n (SUC len) = f (strsub s n)::translate_aux f s (n + 1) len)`;

val translate_def = Define`
  translate f s = implode (translate_aux f s 0 (strlen s))`;

val translate_aux_thm = Q.prove (
  `!f s n len. (n + len = strlen s) ==> (translate_aux f s n len = MAP f (DROP n (explode s)))`,
  Cases_on `s` \\ Induct_on `len` \\ rw [translate_aux_def, strlen_def, explode_def] >-
  rw [DROP_LENGTH_NIL] \\
  rw [strsub_def, DROP_EL_CONS]
);

val translate_thm = Q.store_thm (
  "translate_thm",
  `!f s. translate f s = implode (MAP f (explode s))`,
  rw [translate_def, translate_aux_thm]
);

val tokens_aux_def = Define`
  (tokens_aux f s [] n 0 = []) /\
  (tokens_aux f s (h::t) n 0 = [implode (REVERSE (h::t))]) /\
  (tokens_aux f s [] n (SUC len) =
    if f (strsub s n)
      then tokens_aux f s [] (n + 1) len
    else tokens_aux f s [strsub s n] (n + 1) len) /\
  (tokens_aux f s (h::t) n (SUC len) =
    if f (strsub s n)
      then (implode (REVERSE (h::t)))::(tokens_aux f s [] (n + 1) len)
    else tokens_aux f s (strsub s n::(h::t)) (n + 1) len)`;

val tokens_aux_ind = theorem"tokens_aux_ind";

val tokens_def = Define `
 tokens f s = tokens_aux f s [] 0 (strlen s)`;


val tokens_aux_filter = Q.prove (
  `!f s ss n len. (n + len = strlen s) ==> (concat (tokens_aux f s ss n len) =
      implode (REVERSE ss++FILTER ($~ o f) (DROP n (explode s))))`,
  Cases_on `s` \\ Induct_on `len` \\
  rw [strlen_def, tokens_aux_def, concat_cons, DROP_LENGTH_NIL, strcat_thm, implode_def] \\
  Cases_on `ss` \\ rw [tokens_aux_def, DROP_EL_CONS, concat_cons, strcat_thm, implode_def]
);

val tokens_filter = Q.store_thm (
  "tokens_filter",
  `!f s. concat (tokens f s) = implode (FILTER ($~ o f) (explode s))`,
  rw [tokens_def, tokens_aux_filter]
);

val TOKENS_eq_tokens_aux = Q.store_thm("TOKENS_eq_tokens_aux",
  `!P ls ss n len. (n + len = LENGTH (explode ls)) ==>
      (MAP explode (tokens_aux P ls ss n len) = case ss of
        | (h::t) => if (len <> 0) /\ ($~ (P (EL n (explode ls)))) then
          (REVERSE (h::t) ++ HD (TOKENS P (DROP n (explode ls))))::TL (TOKENS P (DROP n (explode ls)))
           else if (len <> 0) then
              REVERSE (h::t)::(TOKENS P (DROP n (explode ls)))
           else [REVERSE(h::t)]
        | [] => (TOKENS P (DROP n (explode ls))))`,
    ho_match_mp_tac tokens_aux_ind \\ rw[] \\ Cases_on `s`
    \\ rw[explode_thm, tokens_aux_def, TOKENS_def, implode_def, strlen_def, strsub_def]
    \\ fs[strsub_def, DROP_LENGTH_TOO_LONG, TOKENS_def]
    >-(rw[EQ_SYM_EQ, Once DROP_EL_CONS] \\ rw[TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[]
      \\ imp_res_tac SPLITP_NIL_IMP \\ fs[SPLITP] \\ rfs[])
     >-(rw[EQ_SYM_EQ, Once DROP_EL_CONS]
      \\ rw[TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[]
      >-(fs[SPLITP] \\ rfs[] \\ Cases_on `DROP (n + 1) s'`)
      >-(fs[SPLITP] \\ rfs[] \\ Cases_on `DROP (n + 1) s'`
        >-(imp_res_tac DROP_EMPTY \\ fs[ADD1])
        \\ Cases_on `f h` \\ rw[]
        >-(`n + 1 < LENGTH s'` by fs[]
          \\ `h = EL (n + 1) s'` by metis_tac[miscTheory.hd_drop, HD] \\ fs[])
        \\ rw[TOKENS_def, SPLITP]
      ) (*this is a copy*)
      >-(fs[SPLITP] \\ rfs[] \\ Cases_on `DROP (n + 1) s'`
        >-(imp_res_tac DROP_EMPTY \\ fs[ADD1])
        \\ Cases_on `f h` \\ rw[]
        >-(`n + 1 < LENGTH s'` by fs[]
          \\ `h = EL (n + 1) s'` by metis_tac[miscTheory.hd_drop, HD] \\ fs[])
        \\ rw[TOKENS_def, SPLITP]))
    >-(rw[DROP_EL_CONS, TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[]
      \\ rw[TOKENS_def]
      \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[] \\ metis_tac[TL])
    (*This is a copy *)
    >-(rw[DROP_EL_CONS, TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[]
      \\ rw[TOKENS_def]
      \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[] \\ metis_tac[TL])
    >-(`n = LENGTH s' - 1` by DECIDE_TAC
      \\ rw[DROP_EL_CONS, DROP_LENGTH_TOO_LONG, TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[]
      \\ `LENGTH r = 1` by EVAL_TAC >-(rw[])
      \\ Cases_on `TL r` >-(rw[TOKENS_def])
      \\ `LENGTH (TL r) = 0` by fs[LENGTH_TL] \\ rfs[])
    >-(fs[ADD1]
      \\ `x0 = implode [EL n s']` by fs[implode_explode] \\ rw[explode_implode]
      \\ rw[DROP_EL_CONS, DROP_LENGTH_TOO_LONG, TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[] \\ rw[TOKENS_def])
    \\(rw[DROP_EL_CONS, DROP_LENGTH_TOO_LONG, TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[] \\ rw[TOKENS_def]
      \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[] \\ metis_tac[TL]));
(*
  >> TRY (
  recogniser (e.g., rename1_tac or qmatch_goalsub_rename_tac ...) >>
  ... >> NO_TAC)
  >> TRY (
  ... >> NO_TAC)
  >> TRY (
  ... >> NO_TAC)
*)


val TOKENS_eq_tokens = Q.store_thm("TOKENS_eq_tokens",
  `!P ls.(MAP explode (tokens P ls) = TOKENS P (explode ls))`,
  Cases_on `ls` \\ rw[tokens_def, TOKENS_eq_tokens_aux]
);

(*
val TOKENS_eq_tokens_sym = Q.store_thm("TOKENS_eq_tokens_sym",
  `!P ls. tokens P ls = MAP implode (TOKENS P (explode ls))`,
  rw[]
  \\ Q.ISPEC_THEN`explode`match_mp_tac INJ_MAP_EQ
  \\ simp[MAP_MAP_o,INJ_DEF,explode_11,o_DEF,explode_implode,TOKENS_eq_tokens]
*)

val TOKENS_eq_tokens_sym = save_thm("TOKENS_eq_tokens_sym",
        TOKENS_eq_tokens
        |> SPEC_ALL
        |> Q.AP_TERM`MAP implode`
        |> SIMP_RULE(srw_ss())[MAP_MAP_o,implode_explode,o_DEF]);


val tokens_append = Q.store_thm("tokens_append",
  `!P s1 x s2.
    P x ==>
      (tokens P (strcat s1 (strcat (str x) s2)) = tokens P s1 ++ tokens P s2)`,
    rw[TOKENS_eq_tokens_sym] \\ Cases_on `s1` \\ Cases_on `s2`  \\ rw[implode_def, explode_thm, strcat_thm, str_def, TOKENS_APPEND]
)



val fields_aux_def = Define `
  (fields_aux f s ss n 0 = [implode (REVERSE ss)]) /\
  (fields_aux f s ss n (SUC len) =
    if f (strsub s n)
      then implode (REVERSE ss)::(fields_aux f s [] (n + 1) len)
    else fields_aux f s (strsub s n::ss) (n + 1) len)`;



val fields_def = Define`
  fields f s = fields_aux f s [] 0 (strlen s)`;



val fields_aux_filter = Q.prove (
  `!f s ss n len. (n + len = strlen s) ==> (concat (fields_aux f s ss n len) =
      implode (REVERSE ss++FILTER ($~ o f) (DROP n (explode s))))`,
  Cases_on `s` \\ Induct_on `len` \\ rw [strlen_def, fields_aux_def, concat_cons,
    implode_def, explode_thm, DROP_LENGTH_NIL, strcat_thm] \\
  rw [DROP_EL_CONS]
);

val fields_filter = Q.store_thm (
  "fields_filter",
  `!f s. concat (fields f s) = implode (FILTER ($~ o f) (explode s))`,
  rw [fields_def, fields_aux_filter]
);

val fields_aux_length = Q.prove (
  `!f s ss n len. (n + len = strlen s) ==>
    (LENGTH (fields_aux f s ss n len) = LENGTH (FILTER f (DROP n (explode s))) + 1)`,
  Cases_on `s` \\ Induct_on `len` \\
  rw [strlen_def, fields_aux_def, explode_thm, DROP_LENGTH_NIL, ADD1, DROP_EL_CONS]
);


val fields_length = Q.store_thm (
  "fields_length",
  `!f s. LENGTH (fields f s) = (LENGTH (FILTER f (explode s)) + 1)`,
  rw [fields_def, fields_aux_length]
)

val isStringThere_aux_def = Define`
  (isStringThere_aux s1 s2 s1i s2i 0 = T) /\
  (isStringThere_aux s1 s2 s1i s2i (SUC len) =
    if strsub s1 s1i = strsub s2 s2i
      then isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len
    else F)`;


(*

val isStringThere_thm = Q.prove (
  `!s1 s2 s1i s2i len. (s2i + len <= strlen s2) /\ (s1i + len = strlen s1) /\
  (strlen s1 <= strlen s2) /\ (s1i <= s2i) /\ (isStringThere_aux s1 s2 0 s2i (strlen s1)) ==>
  (SEG len s2i (explode s2) = TAKE len (explode s1))`
  Cases_on `s1` \\ Cases_on `s2` \\
  rw [strlen_def, explode_thm, SEG, SEG_TAKE_BUTFISTN] \\
  Cases_on `len` \\ rw [SEG] \\ `s2i < STRLEN s'` by DECIDE_TAC \\
);
*)

val isPrefix_def = Define`
  isPrefix s1 s2 =
    if strlen s1 <= strlen s2
      then isStringThere_aux s1 s2 0 0 (strlen s1)
    else F`;

val isSuffix_def = Define`
  isSuffix s1 s2 =
    if strlen s1 <= strlen s2
      then isStringThere_aux s1 s2 0 (strlen s2 - strlen s1) (strlen s1)
    else F`;

val isSubstring_aux_def = Define`
  (isSubstring_aux s1 s2 lens1 n 0 = F) /\
  (isSubstring_aux s1 s2 lens1 n (SUC len) =
    if (isStringThere_aux s1 s2 0 n lens1)
      then T
    else isSubstring_aux s1 s2 lens1 (n + 1) len)`;

val isSubstring_def = Define`
  isSubstring s1 s2 =
  if strlen s1 <= strlen s2
    then isSubstring_aux s1 s2 (strlen s1) 0 ((strlen s2) - (strlen s1))
  else F`;


val compare_aux_def = Define`
  (compare_aux (s1: mlstring) s2 ord n 0 = ord) /\
  (compare_aux s1 s2 ord n (SUC len) =
    if strsub s2 n < strsub s1 n
      then GREATER
    else if strsub s1 n < strsub s2 n
      then LESS
    else compare_aux s1 s2 ord (n + 1) len)`;

val compare_def = Define`
  compare s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)`;


val collate_aux_def = Define`
  (collate_aux f (s1: mlstring) s2 ord n 0 = ord) /\
  (collate_aux f s1 s2 ord n (SUC len) =
    if f (strsub s1 n) (strsub s2 n) = EQUAL
      then collate_aux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n))`;

val collate_def = Define`
  collate f s1 s2 =
  if (strlen s1) < (strlen s2)
    then collate_aux f s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then collate_aux f s1 s2 GREATER 0 (strlen s2)
  else collate_aux f s1 s2 EQUAL 0 (strlen s2)`;


val collate_aux_less_thm = Q.prove (
  `!f s1 s2 n len. (n + len = strlen s1) /\ (strlen s1 < strlen s2) ==>
    (collate_aux f s1 s2 Less n len = mllist$collate f (DROP n (explode s1)) (DROP n (explode s2)))`,
      Cases_on `s1` \\ Cases_on `s2` \\ Induct_on `len` \\
      rw [collate_aux_def, mllistTheory.collate_def, strlen_def, explode_thm, strsub_def, DROP_EL_CONS]
      >- rw [DROP_LENGTH_TOO_LONG, mllistTheory.collate_def]
);

val collate_aux_equal_thm = Q.prove (
  `!f s1 s2 n len. (n + len = strlen s2) /\ (strlen s1 = strlen s2) ==>
    (collate_aux f s1 s2 Equal n len =
      mllist$collate f (DROP n (explode s1)) (DROP n (explode s2)))`,
  Cases_on `s1` \\ Cases_on `s2` \\ Induct_on `len` \\
  rw [collate_aux_def, mllistTheory.collate_def, strlen_def, explode_thm, strsub_def]
  >- rw [DROP_LENGTH_TOO_LONG, mllistTheory.collate_def] \\
  fs [DROP_EL_CONS, mllistTheory.collate_def]
);

val collate_aux_greater_thm = Q.prove (
  `!f s1 s2 n len. (n + len = strlen s2) /\ (strlen s2 < strlen s1) ==>
    (collate_aux f s1 s2 Greater n len =
      mllist$collate f (DROP n (explode s1)) (DROP n (explode s2)))`,
  Cases_on `s1` \\ Cases_on `s2` \\ Induct_on `len` \\
  rw [collate_aux_def, mllistTheory.collate_def, strlen_def, explode_thm, strsub_def, DROP_EL_CONS]
  >- rw [DROP_LENGTH_TOO_LONG, mllistTheory.collate_def]
);

val collate_thm = Q.store_thm (
  "collate_thm",
  `!f s1 s2. collate f s1 s2 = mllist$collate f (explode s1) (explode s2)`,
  rw [collate_def, collate_aux_greater_thm, collate_aux_equal_thm, collate_aux_less_thm]
);




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
