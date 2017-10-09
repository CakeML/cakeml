open preamble
    mllistTheory miscTheory totoTheory

val _ = new_theory"mlstring"

val cpn_distinct = TypeBase.distinct_of ``:ordering``
val cpn_nchotomy = TypeBase.nchotomy_of ``:ordering``

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

val explode_implode = Q.store_thm("explode_implode[simp]",
  `∀x. explode (implode x) = x`,
  rw[implode_def])

val implode_explode = Q.store_thm("implode_explode[simp]",
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

val strlen_implode = Q.store_thm("strlen_implode[simp]",
  `strlen (implode s) = LENGTH s`, EVAL_TAC);

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

val LENGTH_extract_aux = Q.store_thm("LENGTH_extract_aux",
`!s x y. LENGTH (extract_aux s x y) = y`,
     Induct_on`y` >> fs[extract_aux_def,MIN_DEF]);

val strlen_extract_le = Q.store_thm("strlen_extract_le",
`!s x y. strlen (extract s x y) <= strlen s - x`,
  rw[extract_def] >> CASE_TAC >> fs[LENGTH_extract_aux]);

val extract_aux_DROP = Q.store_thm("extract_aux_DROP",
  `!s k. extract_aux (strlit s) k (LENGTH s - k) = DROP k s`,
  rw[] >> `?n. STRLEN s - k = n` by fs[] >>
  FIRST_X_ASSUM MP_TAC >> qid_spec_tac`s` >> qid_spec_tac`k` >>
  induct_on`n` >> fs[extract_aux_def,STRLEN_DEF,DROP_EL_CONS] >>
  rw[] >> fs[extract_aux_def,DROP_LENGTH_TOO_LONG] >>
  (* simplify *)
  FIRST_X_ASSUM MP_TAC >> PURE_REWRITE_TAC [Once (GSYM SUB_EQ_0)] >>
  strip_tac >> FIRST_X_ASSUM (fn x => PURE_REWRITE_TAC[x]) >>
  fs[extract_aux_def])

val extract_aux_eq = Q.store_thm("extract_aux_eq",
  `!n s. n = LENGTH s ==>
   extract_aux (strlit s) 0 n = s`,
  rw[] >> ASSUME_TAC(Q.SPECL[`s`,`0`] extract_aux_DROP) >> fs[]);

val extract_aux_add_r = Q.store_thm("extract_aux_add_r",
  `!n1 n2 s i. extract_aux s i (n1 + n2) = 
                extract_aux s i n1 ++ extract_aux s (i+n1) n2`,
  induct_on`n1` >- fs[extract_aux_def] >>
  rw[] >> fs[GSYM ADD_SUC,extract_aux_def] >> fs[ADD1]);

val extract_aux_eq = Q.store_thm("extract_aux_eq",
  `!s n. n = LENGTH s ==>
   extract_aux (strlit s) 0 n =s`,
  rw[] >> ASSUME_TAC(Q.SPECL[`s`,`0`] extract_aux_DROP) >> fs[]);

val extract_aux_TAKE = Q.store_thm("extract_aux_TAKE",
  `!s. n <= LENGTH s ==>
     extract_aux (strlit s) 0 n = TAKE n s`,
  rw[] >>
  sg`extract_aux (strlit s) 0 n ++ extract_aux (strlit s) n (LENGTH s - n)  = 
     TAKE n s ++ DROP n s`
  >-(fs[TAKE_DROP, GSYM extract_aux_add_r] >>
     ASSUME_TAC(Q.SPECL[`n`,`STRLEN s - n`,`strlit s`,`0`]extract_aux_add_r) >>
     rfs[] >> fs[extract_aux_eq]) >>
  FIRST_X_ASSUM MP_TAC >> PURE_REWRITE_TAC[extract_aux_DROP] >> rw[]);

val strsub_substring_0_thm = Q.store_thm("strsub_substring_0_thm",
  `∀m n l. m < n ⇒ strsub (substring l 0 n) m = strsub l m`,
  Cases_on `l` \\ Cases_on `s = ""`
      >- rw [strsub_def
            , substring_thm
            , substring_def
            , implode_def
            , explode_aux_def]
      >- (rw [strsub_def]
          \\ `0 < strlen (strlit s)`
             by (Cases_on `s` \\ rw [strlen_def,STRLEN_DEF])
          \\ rw [substring_thm]
          \\ Cases_on `n ≤ STRLEN s`
          \\ fs [MIN_DEF
                , strsub_def
                , implode_def
                , GSYM TAKE_SEG
                , EL_TAKE
                ,SEG_LENGTH_ID]));

val substring_DROP = Q.store_thm("substring_DROP",
`∀s. substring (strlit s) 1 (STRLEN s) = strlit (DROP 1 s)`,
rw []
\\ Cases_on `1 < strlen (strlit s)`
\\ Cases_on `s`
\\ rw [substring_thm, MIN_DEF, implode_def
      , GSYM DROP_SEG, GSYM TAKE_SEG
      , SEG_SUC_CONS
        |> CONV_RULE PairRules.SWAP_PFORALL_CONV
        |> SPEC ``0n``|> EVAL_RULE ]
\\ fs [substring_def, implode_def, NOT_LESS,GSYM LESS_EQ]);

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
      \\ `LENGTH r = 1` by rw[]
      \\ Cases_on `TL r` >-(rw[TOKENS_def])
      \\ rw[] \\ fs[])
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


(* String orderings *)
val compare_aux_def = Define`
  compare_aux (s1: mlstring) s2 ord start len =
    if len = 0n then
      ord
    else if strsub s2 start < strsub s1 start
      then GREATER
    else if strsub s1 start < strsub s2 start
      then LESS
    else compare_aux s1 s2 ord (start + 1) (len - 1)`;

val compare_def = Define`
  compare s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)`;

val mlstring_lt_def = Define `
  mlstring_lt s1 s2 ⇔ (compare s1 s2 = LESS)`;
val _ = Parse.overload_on("<",``λx y. mlstring_lt x y``);

val mlstring_le_def = Define `
  mlstring_le s1 s2 ⇔ (compare s1 s2 ≠ GREATER)`;
val _ = Parse.overload_on("<=",``λx y. mlstring_le x y``);

val mlstring_gt_def = Define `
  mlstring_gt s1 s2 ⇔ (compare s1 s2 = GREATER)`;
val _ = Parse.overload_on(">",``λx y. mlstring_gt x y``);

val mlstring_ge_def = Define `
  mlstring_ge s1 s2 ⇔ (compare s1 s2 <> LESS)`;
val _ = Parse.overload_on(">=",``λx y. mlstring_ge x y``);

(* Properties of string orderings *)

val flip_ord_def = ternaryComparisonsTheory.invert_comparison_def
val _ = overload_on ("flip_ord", ``invert_comparison``);

val compare_aux_spec = Q.prove (
  `!s1 s2 ord_in start len.
    len + start ≤ strlen s1 ∧ len + start ≤ strlen s2 ⇒
    (compare_aux s1 s2 ord_in start len =
      if TAKE len (DROP start (explode s1)) = TAKE len (DROP start (explode s2)) then
        ord_in
      else if string_lt (TAKE len (DROP start (explode s1))) (TAKE len (DROP start (explode s2))) then
        LESS
      else
        GREATER)`,
  Induct_on `len` >>
  rw [] >>
  ONCE_REWRITE_TAC [compare_aux_def] >>
  simp [] >>
  Cases_on `s1` >>
  Cases_on `s2` >>
  fs [] >>
  full_simp_tac (srw_ss()) [TAKE_SUM, DECIDE ``!n. SUC n = 1 + n``] >>
  fs [take1_drop, DROP_DROP_T, char_lt_def] >>
  fs [string_lt_def] >>
  simp [] >>
  rw [] >>
  fs [char_lt_def, CHAR_EQ_THM]);

val compare_aux_refl = Q.prove (
  `!s1 s2 start len.
    start + len ≤ strlen s1 ∧ start + len ≤ strlen s2
    ⇒
    ((compare_aux s1 s2 EQUAL start len = EQUAL)
     ⇔
     (TAKE len (DROP start (explode s1)) = TAKE len (DROP start (explode s2))))`,
  rw [compare_aux_spec]);

val compare_aux_equal = Q.prove (
  `!s1 s2 ord_in start len.
    (compare_aux s1 s2 ord_in start len = EQUAL) ⇒ (ord_in = EQUAL)`,
  Induct_on `len` >>
  rw []
  >- fs [Once compare_aux_def] >>
  pop_assum mp_tac >>
  ONCE_REWRITE_TAC [compare_aux_def] >>
  simp_tac (std_ss++ARITH_ss) [] >>
  rw [] >>
  metis_tac []);

val compare_aux_sym = Q.prove (
  `!s1 s2 ord_in start len ord_out.
    (compare_aux s1 s2 ord_in start len = ord_out)
    ⇔
    (compare_aux s2 s1 (flip_ord ord_in) start len = flip_ord ord_out)`,
  Induct_on `len` >>
  rw [] >>
  ONCE_REWRITE_TAC [compare_aux_def] >>
  simp []
  >- (
    Cases_on `ord_in` >>
    Cases_on `ord_out` >>
    simp [flip_ord_def]) >>
  simp [char_lt_def, CHAR_EQ_THM] >>
  `ORD (strsub s2 start) < ORD (strsub s1 start) ∨
   ORD (strsub s1 start) < ORD (strsub s2 start) ∨
   (ORD (strsub s1 start) = ORD (strsub s2 start))`
  by decide_tac
  >- (
    Cases_on `ord_out` >>
    simp [flip_ord_def])
  >- (
    simp [] >>
    Cases_on `ord_out` >>
    simp [flip_ord_def]) >>
  ASM_REWRITE_TAC [] >>
  simp_tac (std_ss++ARITH_ss) [] >>
  metis_tac []);

val string_lt_take_mono = Q.prove (
  `!s1 s2 x.
    s1 < s2 ⇒ TAKE x s1 < TAKE x s2 ∨ (TAKE x s1 = TAKE x s2)`,
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def] >>
  Cases_on `x` >>
  fs [string_lt_def] >>
  metis_tac []);

val string_lt_remove_take = Q.prove (
  `!s1 s2 x. TAKE x s1 < TAKE x s2 ⇒ s1 < s2`,
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def] >>
  Cases_on `x` >>
  fs [string_lt_def] >>
  metis_tac []);

val string_prefix_le = Q.prove (
  `!s1 s2. s1 ≼ s2 ⇒ s1 ≤ s2`,
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def, string_le_def, isPREFIX_STRCAT] >>
  Cases_on `s3` >>
  fs []);

val take_prefix = Q.prove (
  `!l s. TAKE l s ≼ s`,
  Induct_on `s` >>
  rw [] >>
  Cases_on `l` >>
  fs []);

val mlstring_lt_inv_image = Q.store_thm("mlstring_lt_inv_image",
  `mlstring_lt = inv_image string_lt explode`,
  simp [inv_image_def, FUN_EQ_THM] >>
  Cases >>
  Cases >>
  simp [mlstring_lt_def, compare_def, compare_aux_spec] >>
  rpt (qpat_abbrev_tac `x = STRLEN _`) >>
  rw []
  >- (
    `TAKE x s' ≤ s'` by metis_tac [take_prefix, string_prefix_le] >>
    fs [string_le_def] >>
    `x ≠ x'` by decide_tac >>
    metis_tac [LENGTH_TAKE, LESS_OR_EQ])
  >- metis_tac [string_lt_remove_take, TAKE_LENGTH_ID]
  >- metis_tac [string_lt_take_mono, TAKE_LENGTH_ID]
  >- metis_tac [take_prefix, string_prefix_le, LENGTH_TAKE, LESS_OR_EQ, string_lt_antisym, string_le_def]
  >- metis_tac [string_lt_remove_take, TAKE_LENGTH_ID]
  >- metis_tac [string_lt_take_mono, TAKE_LENGTH_ID]
  >- metis_tac [take_prefix, string_prefix_le, string_lt_antisym, string_le_def]
  >- metis_tac [string_lt_remove_take, TAKE_LENGTH_ID]
  >- metis_tac [string_lt_take_mono, TAKE_LENGTH_ID]);

val TotOrd_compare = Q.store_thm ("TotOrd_compare",
  `TotOrd compare`,
  rw [TotOrd]
  >- (
    rw [compare_def, compare_aux_refl] >>
    Cases_on `x` >>
    Cases_on `y` >>
    fs [strlen_def]
    >- metis_tac [compare_aux_equal, cpn_distinct, prim_recTheory.LESS_NOT_EQ]
    >- metis_tac [compare_aux_equal, cpn_distinct, prim_recTheory.LESS_NOT_EQ]
    >- (
      `STRLEN s' = STRLEN s` by decide_tac >>
      simp []))
  >- (
    rw [compare_def] >>
    fs []
    >- metis_tac [compare_aux_sym, flip_ord_def]
    >- metis_tac [compare_aux_sym, flip_ord_def] >>
    `strlen x = strlen y` by decide_tac >>
    metis_tac [compare_aux_sym, flip_ord_def])
  >- (
    fs [GSYM mlstring_lt_def, mlstring_lt_inv_image] >>
    metis_tac [string_lt_trans]));

val good_cmp_compare = Q.store_thm("good_cmp_compare",
  `good_cmp compare`,
  match_mp_tac comparisonTheory.TotOrder_imp_good_cmp \\
  MATCH_ACCEPT_TAC TotOrd_compare);

val mlstring_lt_antisym = Q.store_thm ("mlstring_lt_antisym",
  `∀s t. ¬(s < t ∧ t < s)`,
  rw [mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd, cpn_distinct]);

val mlstring_lt_cases = Q.store_thm ("mlstring_lt_cases",
  `∀s t. (s = t) ∨ s < t ∨ t < s`,
  rw [mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd, cpn_nchotomy]);

val mlstring_lt_nonrefl = Q.store_thm ("mlstring_lt_nonrefl",
  `∀s. ¬(s < s)`,
  rw [mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd, cpn_distinct]);

val mlstring_lt_trans = Q.store_thm ("mlstring_lt_trans",
  `∀s1 s2 s3. s1 < s2 ∧ s2 < s3 ⇒ s1 < s3`,
  rw [mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd]);

val mlstring_le_thm = Q.store_thm ("mlstring_le_thm",
  `!s1 s2. s1 ≤ s2 ⇔ (s1 = s2) ∨ s1 < s2`,
  rw [mlstring_le_def, mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd, cpn_distinct, cpn_nchotomy]);

val mlstring_gt_thm = Q.store_thm ("mlstring_gt_thm",
  `!s1 s2. s1 > s2 ⇔ s2 < s1`,
  rw [mlstring_gt_def, mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd]);

val mlstring_ge_thm = Q.store_thm ("mlstring_ge_thm",
  `!s1 s2. s1 ≥ s2 ⇔ s2 ≤ s1`,
  rw [mlstring_ge_def, mlstring_le_def] >>
  metis_tac [TotOrd_compare, TotOrd]);

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
