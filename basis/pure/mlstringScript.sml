(*
  Pure functions for the String module.

  Defines mlstring as a separate type from string in HOL's standard library (a
  synonym for char list).
*)
Theory mlstring
Ancestors
  misc toto mllist
Libs
  preamble

val cpn_distinct = TypeBase.distinct_of ``:ordering``
val cpn_nchotomy = TypeBase.nchotomy_of ``:ordering``

(* Defines strings as a separate type from char list. This theory should be
   moved into HOL, either as its own theory, or as an addendum to stringTheory *)

Datatype:
  mlstring = strlit string
End
val _ = add_strliteral_form{inj=``strlit``, ldelim = "«"};

Definition implode_def:
  implode = strlit
End

Definition strlen_def[simp]:
  strlen (strlit s) = LENGTH s
End

Definition strsub_def[simp]:
  strsub (strlit s) n = EL n s
End

(* the test here is because underspecification is annoying (and SEG is underspecified) *)
(* the underlying primitive (CopyStrStr) raises an exception if the test is false *)
Definition substring_def:
  substring (strlit s) off len = strlit (if off + len ≤ LENGTH s then SEG len off s
                                         else if off <= LENGTH s then DROP off s
                                         else "")
End

Definition concat_def:
  concat l = strlit (FLAT (MAP (λs. case s of strlit x => x) l))
End

Theorem concat_nil[simp]:
   concat [] = strlit ""
Proof
EVAL_TAC
QED

Definition explode_aux_def[simp]:
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) =
    strsub s n :: (explode_aux s (n + 1) len))
End

Theorem explode_aux_thm:
   ∀max n ls.
    (n + max = LENGTH ls) ⇒
    (explode_aux (strlit ls) n max = DROP n ls)
Proof
  Induct \\ rw[] \\ fs[LENGTH_NIL_SYM,DROP_LENGTH_TOO_LONG]
  \\ match_mp_tac (GSYM rich_listTheory.DROP_EL_CONS)
  \\ simp[]
QED

Definition explode_def:
  explode s = explode_aux s 0 (strlen s)
End

Theorem explode_thm[simp]:
   explode (strlit ls) = ls
Proof
  rw[explode_def,SIMP_RULE std_ss [] explode_aux_thm]
QED

Theorem explode_implode[simp]:
   ∀x. explode (implode x) = x
Proof
  rw[implode_def]
QED

Theorem implode_explode[simp]:
   ∀x. implode (explode x) = x
Proof
  Cases >> rw[implode_def]
QED

Theorem explode_11[simp]:
   ∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2)
Proof
  Cases >> Cases >> simp[]
QED

Theorem implode_BIJ:
   BIJ implode UNIV UNIV
Proof
  rw[BIJ_IFF_INV] >>
  qexists_tac`explode` >>
  rw[implode_explode,
     explode_implode]
QED

Theorem explode_BIJ:
   BIJ explode UNIV UNIV
Proof
  rw[BIJ_IFF_INV] >>
  qexists_tac`implode` >>
  rw[implode_explode,
     explode_implode]
QED

Theorem LENGTH_explode[simp]:
   LENGTH (explode s) = strlen s
Proof
  Cases_on`s` \\ simp[]
QED

Theorem concat_thm:
   concat l = implode (FLAT (MAP explode l))
Proof
  rw[concat_def,implode_def] \\
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\
  rw[FUN_EQ_THM] \\ CASE_TAC \\ simp[]
QED

Theorem strlen_implode[simp]:
   strlen (implode s) = LENGTH s
Proof
EVAL_TAC
QED

Theorem strlen_substring:
   strlen (substring s i j) = if i + j <= strlen s then j
                              else if i <= strlen s then strlen s - i
                              else 0
Proof
  Cases_on`s` \\ rw[substring_def,LENGTH_SEG]
QED

Definition extract_def:
  extract s i opt =
    if strlen s <= i
      then implode []
    else case opt of
        SOME x => substring s i (MIN (strlen s - i) x)
      | NONE => substring s i (strlen s - i)
End

Theorem strlen_extract_le:
 !s x y. strlen (extract s x y) <= strlen s - x
Proof
  rw[extract_def] >> CASE_TAC >> fs[strlen_substring]
QED

Theorem strsub_substring_0_thm:
   ∀m n l. m < n ⇒ strsub (substring l 0 n) m = strsub l m
Proof
  Cases_on`l` \\ rw[strsub_def,substring_def]
  \\ rw[SEG_TAKE_DROP,EL_TAKE]
QED

Theorem substring_full[simp]:
   substring s 0 (strlen s) = s
Proof
  Cases_on`s` \\ rw[substring_def,SEG_LENGTH_ID]
QED

Theorem substring_too_long:
   strlen s <= i ==> substring s i j = strlit ""
Proof
  Cases_on`s` \\ rw[substring_def,DROP_NIL] \\
  `j = 0` by decide_tac \\ fs[SEG]
QED

Definition strcat_def:
  strcat s1 s2 = concat [s1; s2]
End
val _ = Parse.add_infix("^",480,Parse.LEFT)
Overload "^" = ``λx y. strcat x y``

Theorem concat_cons:
   concat (h::t) = strcat h (concat t)
Proof
  rw[strcat_def,concat_def]
QED

Theorem strcat_thm:
   strcat s1 s2 = implode (explode s1 ++ explode s2)
Proof
  rw[strcat_def,concat_def]
  \\ CASE_TAC \\ rw[] \\ CASE_TAC \\ rw[implode_def]
QED

Theorem strcat_assoc[simp]:
   !s1 s2 s3.
    s1 ^ (s2 ^ s3) = s1 ^ s2 ^ s3
Proof
    rw[strcat_def,concat_def]
QED

Theorem strcat_o:
  strcat x ∘ strcat y = strcat (x ^ y)
Proof
  simp [FUN_EQ_THM]
QED

Theorem strcat_nil[simp]:
   (strcat (strlit "") s = s) ∧
   (strcat s (strlit "") = s)
Proof
  rw[strcat_def,concat_def] \\ CASE_TAC \\ rw[]
QED

Theorem mlstring_common_prefix[simp]:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2
Proof
  rpt Cases \\ gvs [strcat_thm,implode_def]
QED

Theorem mlstring_common_char_prefix[simp]:
  ∀c1 s1 s2 t2 t2. (strlit (c1 :: s1) ^ t1) = (strlit (c2 :: s2) ^ t2) ⇔
    c1 = c2 ∧ strlit s1 ^ t1 = strlit s2 ^ t2
Proof
  rw [strcat_thm, implode_def]
QED

Theorem mlstring_common_suffix[simp]:
  ∀s t1 t2. t1 ^ s = t2 ^ s ⇔ t1 = t2
Proof
  rpt Cases \\ gvs [strcat_thm,implode_def]
QED

Theorem concat_append:
  concat (xs ++ ys) = concat xs ^ concat ys
Proof
  Induct_on `xs` \\ simp [concat_cons]
QED

Theorem implode_STRCAT:
   !l1 l2.
    implode(STRCAT l1 l2) = implode l1 ^ implode l2
Proof
    rw[implode_def, strcat_def, concat_def]
QED

Theorem explode_strcat[simp]:
   explode (strcat s1 s2) = explode s1 ++ explode s2
Proof
  rw[strcat_thm]
QED

Theorem strlen_strcat[simp]:
   strlen (strcat s1 s2) = strlen s1 + strlen s2
Proof
  rw[strcat_thm]
QED

Definition concatWith_aux_def:
  (concatWith_aux s [] bool = implode []) /\
  (concatWith_aux s (h::t) T = strcat h (concatWith_aux s t F)) /\
  (concatWith_aux s (h::t) F = strcat s (concatWith_aux s (h::t) T))
Termination
  wf_rel_tac `inv_image ($< LEX $<) (\(s,l,b). (LENGTH l, if b then 0n else 1))` \\
  rw[]
End

Definition concatWith_def:
  concatWith s l = concatWith_aux s l T
End

Theorem concatWith_CONCAT_WITH_aux[local]:
  !s l fl. (CONCAT_WITH_aux s l fl = REVERSE fl ++ explode (concatWith (implode s) (MAP implode l)))
Proof
  ho_match_mp_tac CONCAT_WITH_aux_ind
  \\ rw[CONCAT_WITH_aux_def, concatWith_def, implode_def, concatWith_aux_def, strcat_thm]
  >-(Induct_on `l` \\ rw[MAP, implode_def, concatWith_aux_def, strcat_thm]
  \\ Cases_on `l` \\ rw[concatWith_aux_def, explode_implode, strcat_thm, implode_def])
QED

Theorem concatWith_CONCAT_WITH:
   !s l. CONCAT_WITH s l = explode (concatWith (implode s) (MAP implode l))
Proof
    rw[concatWith_def, CONCAT_WITH_def, concatWith_CONCAT_WITH_aux]
QED

Definition str_def:
  str (c: char) = implode [c]
End

Theorem explode_str[simp]:
   explode (str c) = [c]
Proof
  rw[str_def]
QED

Theorem strlen_str[simp]:
   strlen (str c) = 1
Proof
rw[str_def]
QED

Definition translate_aux_def:
  (translate_aux f s n 0 = []) /\
  (translate_aux f s n (SUC len) = f (strsub s n)::translate_aux f s (n + 1) len)
End

Definition translate_def:
  translate f s = implode (translate_aux f s 0 (strlen s))
End

Theorem translate_aux_thm[local]:
  !f s n len. (n + len = strlen s) ==> (translate_aux f s n len = MAP f (DROP n (explode s)))
Proof
  Cases_on `s` \\ Induct_on `len` \\ rw [translate_aux_def, strlen_def, explode_def] \\
  rw [DROP_LENGTH_NIL] \\
  rw [strsub_def, DROP_EL_CONS]
QED

Theorem translate_thm:
   !f s. translate f s = implode (MAP f (explode s))
Proof
  rw [translate_def, translate_aux_thm]
QED

Definition splitl_aux_def:
  splitl_aux P s i =
    if i < strlen s ∧ P (strsub s i) then
        splitl_aux P s (i+1)
    else (extract s 0 (SOME i), extract s i NONE)
Termination
  WF_REL_TAC`inv_image $< (λ(x,s,i). strlen s - i)`
End

val splitl_aux_ind = theorem"splitl_aux_ind";

Definition splitl_def:
  splitl P s = splitl_aux P s 0
End

Theorem splitl_aux_SPLITP:
   ∀P s i.
    splitl_aux P s i =
    (implode o ((++)(TAKE i (explode s))) ## implode)
      (SPLITP ((~) o P) (DROP i (explode s)))
Proof
  recInduct splitl_aux_ind
  \\ rw[]
  \\ Cases_on`SPLITP P (DROP i (explode s))` \\ fs[]
  \\ simp[Once splitl_aux_def]
  \\ Cases_on`strlen s ≤ i` \\ fs[DROP_LENGTH_TOO_LONG,LENGTH_explode]
  >- (
    fs[SPLITP] \\ rveq
    \\ simp[TAKE_LENGTH_TOO_LONG,LENGTH_explode]
    \\ simp[extract_def]
    \\ Cases_on`s` \\ fs[substring_def]
    \\ rw[implode_def]
    \\ qmatch_goalsub_rename_tac`MIN (LENGTH s) i`
    \\ `MIN (LENGTH s) i = LENGTH s` by rw[MIN_DEF]
    \\ rw[SEG_LENGTH_ID] )
  \\ Cases_on`DROP i (explode s)` \\ fs[DROP_NIL,LENGTH_explode]
  \\ fs[SPLITP]
  \\ `strsub s i = h` by ( Cases_on`s` \\ rfs[strsub_def,DROP_EL_CONS] )
  \\ rveq \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  >- (
    rveq \\ fs[]
    \\ rfs[DROP_EL_CONS,LENGTH_explode]
    \\ rveq
    \\ Cases_on`SPLITP ($~ o P) (DROP (i+1) (explode s))` \\ fs[]
    \\ AP_TERM_TAC
    \\ simp[LIST_EQ_REWRITE,LENGTH_TAKE,LENGTH_explode]
    \\ rw[]
    \\ Cases_on`x < i` \\ simp[EL_APPEND1,EL_APPEND2,LENGTH_explode,EL_TAKE]
    \\ Cases_on`x < i+1` \\ simp[EL_APPEND1,EL_APPEND2,LENGTH_explode,EL_TAKE,EL_CONS,PRE_SUB1]
    \\ `x = i` by DECIDE_TAC
    \\ rw[] )
  \\ Cases_on`s`
  \\ rw[extract_def,substring_def,implode_def] \\ fs[MIN_DEF]
  \\ simp[TAKE_SEG] \\ rfs[]
  \\ rfs[DROP_SEG]
QED

Theorem splitl_SPLITL:
   splitl P s = (implode ## implode) (SPLITL P (explode s))
Proof
  rw[splitl_def,splitl_aux_SPLITP,SPLITL_def]
  \\ Cases_on`SPLITP((~)o P)(explode s)` \\ fs[]
QED

Definition tokens_aux_def:
  (tokens_aux f s [] n 0 = []) /\
  (tokens_aux f s (h::t) n 0 = [implode (REVERSE (h::t))]) /\
  (tokens_aux f s [] n (SUC len) =
    if f (strsub s n)
      then tokens_aux f s [] (n + 1) len
    else tokens_aux f s [strsub s n] (n + 1) len) /\
  (tokens_aux f s (h::t) n (SUC len) =
    if f (strsub s n)
      then (implode (REVERSE (h::t)))::(tokens_aux f s [] (n + 1) len)
    else tokens_aux f s (strsub s n::(h::t)) (n + 1) len)
End

val tokens_aux_ind = theorem"tokens_aux_ind";

Definition tokens_def:
 tokens f s = tokens_aux f s [] 0 (strlen s)
End


Theorem tokens_aux_filter[local]:
  !f s ss n len. (n + len = strlen s) ==> (concat (tokens_aux f s ss n len) =
      implode (REVERSE ss++FILTER ($~ o f) (DROP n (explode s))))
Proof
  Cases_on `s` \\ Induct_on `len` \\
  rw [strlen_def, tokens_aux_def, concat_cons, DROP_LENGTH_NIL, strcat_thm, implode_def] \\
  Cases_on `ss` \\ rw [tokens_aux_def, DROP_EL_CONS, concat_cons, strcat_thm, implode_def]
QED

Theorem tokens_filter:
   !f s. concat (tokens f s) = implode (FILTER ($~ o f) (explode s))
Proof
  rw [tokens_def, tokens_aux_filter]
QED

Theorem TOKENS_eq_tokens_aux:
   !P ls ss n len. (n + len = LENGTH (explode ls)) ==>
      (MAP explode (tokens_aux P ls ss n len) = case ss of
        | (h::t) => if (len <> 0) /\ ($~ (P (EL n (explode ls)))) then
          (REVERSE (h::t) ++ HD (TOKENS P (DROP n (explode ls))))::TL (TOKENS P (DROP n (explode ls)))
           else if (len <> 0) then
              REVERSE (h::t)::(TOKENS P (DROP n (explode ls)))
           else [REVERSE(h::t)]
        | [] => (TOKENS P (DROP n (explode ls))))
Proof
    ho_match_mp_tac tokens_aux_ind \\ rw[] \\ Cases_on `s`
    \\ rw[explode_thm, tokens_aux_def, TOKENS_def, implode_def, strlen_def, strsub_def]
    \\ fs[strsub_def, DROP_LENGTH_TOO_LONG, TOKENS_def]
    >-(rw[EQ_SYM_EQ, Once DROP_EL_CONS] \\ rw[TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[]
      \\ imp_res_tac SPLITP_NIL_FST_IMP \\ fs[SPLITP] \\ rfs[])
     >-(rw[EQ_SYM_EQ, Once DROP_EL_CONS]
      \\ rw[TOKENS_def]
      \\ pairarg_tac  \\ fs[NULL_EQ] \\ rw[]
      >-(fs[SPLITP] \\ rfs[] \\ Cases_on `DROP (n + 1) s'`)
      >-(fs[SPLITP] \\ rfs[] \\ Cases_on `DROP (n + 1) s'`
        >-(imp_res_tac DROP_EMPTY \\ fs[ADD1])
        \\ Cases_on `f h` \\ rw[]
        >-(`n + 1 < LENGTH s'` by fs[]
          \\ `h = EL (n + 1) s'` by metis_tac[HD_DROP, HD] \\ fs[])
        \\ rw[TOKENS_def, SPLITP]
      ) (*this is a copy*)
      >-(fs[SPLITP] \\ rfs[] \\ Cases_on `DROP (n + 1) s'`
        >-(imp_res_tac DROP_EMPTY \\ fs[ADD1])
        \\ Cases_on `f h` \\ rw[]
        >-(`n + 1 < LENGTH s'` by fs[]
          \\ `h = EL (n + 1) s'` by metis_tac[HD_DROP, HD] \\ fs[])
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
      \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP] \\ rfs[] \\ metis_tac[TL])
QED
(*
  >> TRY (
  recogniser (e.g., rename1_tac or qmatch_goalsub_rename_tac ...) >>
  ... >> NO_TAC)
  >> TRY (
  ... >> NO_TAC)
  >> TRY (
  ... >> NO_TAC)
*)


Theorem TOKENS_eq_tokens:
   !P ls.(MAP explode (tokens P ls) = TOKENS P (explode ls))
Proof
  Cases_on `ls` \\ rw[tokens_def, TOKENS_eq_tokens_aux]
QED

(*
Theorem TOKENS_eq_tokens_sym
  `!P ls. tokens P ls = MAP implode (TOKENS P (explode ls))`
  (rw[]
  \\ Q.ISPEC_THEN`explode`match_mp_tac INJ_MAP_EQ
  \\ simp[MAP_MAP_o,INJ_DEF,explode_11,o_DEF,explode_implode,TOKENS_eq_tokens]
*)

Theorem TOKENS_eq_tokens_sym =
  TOKENS_eq_tokens
        |> SPEC_ALL
        |> Q.AP_TERM`MAP implode`
        |> SIMP_RULE(srw_ss())[MAP_MAP_o,implode_explode,o_DEF]


Theorem tokens_append:
   !P s1 x s2.
    P x ==>
      (tokens P (strcat (strcat s1 (str x)) s2) = tokens P s1 ++ tokens P s2)
Proof
    rw[TOKENS_eq_tokens_sym] \\ Cases_on `s1` \\ Cases_on `s2`
    \\ rewrite_tac[GSYM MAP_APPEND] \\ AP_TERM_TAC
    \\ rw[explode_thm]
    \\ rewrite_tac[GSYM APPEND_ASSOC,APPEND]
    \\ match_mp_tac TOKENS_APPEND \\ rw[]
QED

Definition tokens_alt_aux_def:
  (tokens_alt_aux f s i j n =
  if j < n then
    (if f (strsub s j)
    then
      (if i = j then tokens_alt_aux f s (i+1) (j+1) n
      else
        substring s i (j-i)::
        (tokens_alt_aux f s (j+1) (j+1) n))
    else
      tokens_alt_aux f s i (j+1) n)
  else
    if i = j then []
    else [substring s i (j-i)])
Termination
  WF_REL_TAC`measure (λf,s,i,j,n. n - j)`>>rw[]
End

Theorem substring_1_strsub:
  i < strlen s ⇒
  substring s i 1 = str (strsub s i)
Proof
  Cases_on`s`>>rw[substring_def]>>
  DEP_REWRITE_TAC[SEG1]>>
  gvs[str_def,implode_def]
QED

Theorem substring_0[simp]:
  substring s i 0 = strlit ""
Proof
  Cases_on`s`>>rw[substring_def]>>
  EVAL_TAC
QED

Theorem substring_add:
  i + x + y ≤ strlen s ⇒
  substring s i (x + y) =
  substring s i x ^ substring s (i + x) y
Proof
  Cases_on`s`>>rw[substring_def]>>
  simp[TAKE_SUM]>>
  DEP_REWRITE_TAC[SEG_TAKE_DROP]>>
  rw[TAKE_SUM,DROP_DROP]>>
  simp[strcat_def]>>
  EVAL_TAC
QED

Theorem tokens_alt_tokens_alt_aux:
  ∀f s acc j l i.
  i ≤ j ∧ j ≤ strlen s ∧
  strlen s - j = l ∧
  acc = REVERSE (explode (substring s i (j - i))) ⇒
  tokens_aux f s acc j l =
  tokens_alt_aux f s i j (strlen s)
Proof
  ho_match_mp_tac tokens_aux_ind>>rw[]
  >- (
    simp[Once tokens_alt_aux_def]>>
    rw[tokens_aux_def]>>
    qpat_x_assum`_ _ = ""`
      (mp_tac o  Q.AP_TERM `LENGTH`)>>
    simp[strlen_substring]>>rw[])
  >- (
    qpat_assum`STRING _ _ = _` (SUBST1_TAC o SYM)>>
    simp[Once tokens_alt_aux_def,tokens_aux_def]>>
    rw[]>>gvs[]>>
    qpat_x_assum`STRING _ _ = REVERSE _`
      (mp_tac o Q.AP_TERM `implode o REVERSE`)>>
    simp[])
  >- (
    simp[Once tokens_alt_aux_def]>>
    rw[tokens_aux_def]>>gvs[]
    >- (
      qpat_x_assum`_ _ = ""`
        (mp_tac o  Q.AP_TERM `LENGTH`)>>
      simp[strlen_substring]>>rw[])
    >- (
      first_x_assum(qspec_then`i` mp_tac)>> simp[]>>
      impl_keep_tac >-
        simp[substring_1_strsub]>>
      rw[])>>
    first_x_assum(qspec_then`i` mp_tac)>> simp[]>>
    impl_keep_tac >- (
      qpat_x_assum`_ _ = ""`
        (mp_tac o  Q.AP_TERM `LENGTH`)>>
      simp[strlen_substring]>>rw[])>>
    rw[])>>
  gvs[]>>
  pop_assum (assume_tac o SYM)>>
  simp[Once tokens_alt_aux_def]>>
  rw[tokens_aux_def]>>gvs[]
  >- (
    qpat_x_assum`REVERSE _ = STRING _ _`
      (mp_tac o Q.AP_TERM `implode o REVERSE`)>>
    simp[])
  >- (
    first_x_assum(qspec_then`i` mp_tac)>> simp[]>>
    impl_keep_tac >- (
      `j + 1 - i = (j - i) + 1` by simp[]>>
      pop_assum SUBST1_TAC>>
      DEP_REWRITE_TAC[substring_add]>>
      simp[]>>
      DEP_REWRITE_TAC[substring_1_strsub]>>rw[])>>
    rw[])
QED

Theorem tokens_alt:
  tokens f s =
  tokens_alt_aux f s 0 0 (strlen s)
Proof
  rw[tokens_def]>>
  match_mp_tac tokens_alt_tokens_alt_aux>>
  simp[]
QED

Definition fields_aux_def:
  (fields_aux f s ss n 0 = [implode (REVERSE ss)]) /\
  (fields_aux f s ss n (SUC len) =
    if f (strsub s n)
      then implode (REVERSE ss)::(fields_aux f s [] (n + 1) len)
    else fields_aux f s (strsub s n::ss) (n + 1) len)
End



Definition fields_def:
  fields f s = fields_aux f s [] 0 (strlen s)
End



Theorem fields_aux_filter[local]:
  !f s ss n len. (n + len = strlen s) ==> (concat (fields_aux f s ss n len) =
      implode (REVERSE ss++FILTER ($~ o f) (DROP n (explode s))))
Proof
  Cases_on `s` \\ Induct_on `len` \\ rw [strlen_def, fields_aux_def, concat_cons,
    implode_def, explode_thm, DROP_LENGTH_NIL, strcat_thm] \\
  rw [DROP_EL_CONS]
QED

Theorem fields_filter:
   !f s. concat (fields f s) = implode (FILTER ($~ o f) (explode s))
Proof
  rw [fields_def, fields_aux_filter]
QED

Theorem fields_aux_length[local]:
  !f s ss n len. (n + len = strlen s) ==>
    (LENGTH (fields_aux f s ss n len) = LENGTH (FILTER f (DROP n (explode s))) + 1)
Proof
  Cases_on `s` \\ Induct_on `len` \\
  rw [strlen_def, fields_aux_def, explode_thm, DROP_LENGTH_NIL, ADD1, DROP_EL_CONS]
QED


Theorem fields_length:
   !f s. LENGTH (fields f s) = (LENGTH (FILTER f (explode s)) + 1)
Proof
  rw [fields_def, fields_aux_length]
QED

Definition fields_alt_aux_def:
  (fields_alt_aux f s i j n =
  if j < n then
    (if f (strsub s j)
    then
        substring s i (j-i)::
        (fields_alt_aux f s (j+1) (j+1) n)
    else
      fields_alt_aux f s i (j+1) n)
  else
    [substring s i (j-i)])
Termination
  WF_REL_TAC`measure (λf,s,i,j,n. n - j)`>>rw[]
End

Theorem fields_alt_fields_alt_aux:
  ∀l acc j i.
  i ≤ j ∧ j ≤ strlen s ∧
  strlen s - j = l ∧
  acc = REVERSE (explode (substring s i (j - i))) ⇒
  fields_aux f s acc j l =
  fields_alt_aux f s i j (strlen s)
Proof
  Induct>>rw[]
  >- (
    simp[Once fields_alt_aux_def]>>
    rw[fields_aux_def])
  >- (
    simp[Once fields_alt_aux_def]>>
    rw[fields_aux_def]>>gvs[]>>
    first_x_assum(qspecl_then [`j+1`,`i`] mp_tac)>> simp[]>>
    `j + 1 - i = (j - i) + 1` by simp[]>>
    pop_assum SUBST1_TAC>>
    DEP_REWRITE_TAC[substring_add]>>
    simp[]>>
    DEP_REWRITE_TAC[substring_1_strsub]>>rw[])
QED

Theorem fields_alt:
  fields f s =
  fields_alt_aux f s 0 0 (strlen s)
Proof
  rw[fields_def]>>
  match_mp_tac fields_alt_fields_alt_aux>>
  simp[]
QED


Definition str_findi_def:
  str_findi P i s = if i < strlen s
    then if P (strsub s i) then SOME i else str_findi P (i + 1) s
    else NONE
Termination
  WF_REL_TAC `measure (\(P, i, s). strlen s - i)`
End

Theorem str_findi_range:
  !P i s. str_findi P i s = SOME j ==> i <= j /\ j < strlen s
Proof
  recInduct str_findi_ind
  \\ rpt gen_tac
  \\ disch_tac
  \\ simp [Once str_findi_def]
  \\ rw []
  \\ fs []
QED

Theorem OLEAST_LE_STEP:
  (OLEAST j. i <= j /\ P j) = (if P i then SOME i
    else (OLEAST j. i + 1 <= j /\ P j))
Proof
  rw []
  \\ simp [WhileTheory.OLEAST_EQ_SOME]
  \\ qmatch_goalsub_abbrev_tac `opt1 = $OLEAST _`
  \\ Cases_on `opt1`
  \\ fs [WhileTheory.OLEAST_EQ_SOME]
  \\ rw []
  \\ fs [LESS_EQ |> REWRITE_RULE [ADD1] |> GSYM, arithmeticTheory.LT_LE]
  \\ CCONTR_TAC
  \\ fs []
  \\ metis_tac []
QED

Theorem str_findi_OLEAST:
  !P i s. str_findi P i s = (OLEAST j. i <= j /\ j < strlen s /\ P (strsub s j))
Proof
  recInduct str_findi_ind
  \\ rw []
  \\ simp [Once OLEAST_LE_STEP]
  \\ simp [Once str_findi_def]
  \\ rw []
  \\ fs []
  \\ CCONTR_TAC
  \\ fs []
QED

Definition isStringThere_aux_def:
  (isStringThere_aux s1 s2 s1i s2i 0 = T) /\
  (isStringThere_aux s1 s2 s1i s2i (SUC len) =
    if strsub s1 s1i = strsub s2 s2i
      then isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len
    else F)
End


(*

val isStringThere_thm = Q.prove (
  `!s1 s2 s1i s2i len. (s2i + len <= strlen s2) /\ (s1i + len = strlen s1) /\
  (strlen s1 <= strlen s2) /\ (s1i <= s2i) /\ (isStringThere_aux s1 s2 0 s2i (strlen s1)) ==>
  (SEG len s2i (explode s2) = TAKE len (explode s1))`
  Cases_on `s1` \\ Cases_on `s2` \\
  rw [strlen_def, explode_thm, SEG, SEG_TAKE_DROP] \\
  Cases_on `len` \\ rw [SEG] \\ `s2i < STRLEN s'` by DECIDE_TAC \\
);
*)

Definition isPrefix_def:
  isPrefix s1 s2 =
    if strlen s1 <= strlen s2
      then isStringThere_aux s1 s2 0 0 (strlen s1)
    else F
End

Theorem exists_mlstring:
  (∃x:mlstring. P x) ⇔ (∃s. P (strlit s))
Proof
  eq_tac \\ rw []
  >- (Cases_on ‘x’ \\ gvs [] \\ pop_assum $ irule_at Any)
  \\ pop_assum $ irule_at Any
QED

Theorem isprefix_thm_aux[local]:
  ∀ys xs zs.
    LENGTH ys ≤ LENGTH zs ⇒
    (isStringThere_aux (strlit (xs ++ ys)) (strlit (xs ++ zs))
       (LENGTH xs) (LENGTH xs) (LENGTH ys) ⇔
       ys ≼ zs)
Proof
  Induct \\ gvs [isStringThere_aux_def]
  \\ rpt strip_tac
  \\ Cases_on ‘zs’ \\ gvs []
  \\ rename [‘_ = h' ∧ _ ≼ zs’]
  \\ gvs [EL_APPEND]
  \\ last_x_assum $ qspecl_then [‘xs ++ [h]’, ‘zs’] mp_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
  \\ gvs [] \\ metis_tac []
QED

Theorem isprefix_thm:
  isPrefix s₁ s₂ ⇔ explode s₁ ≼ explode s₂
Proof
  namedCases_on ‘s₁’ ["s"]
  \\ namedCases_on ‘s₂’ ["t"]
  \\ gvs [isPrefix_def]
  \\ Cases_on ‘LENGTH s ≤ LENGTH t’ \\ gvs []
  >- (qspecl_then [‘s’, ‘[]’, ‘t’] mp_tac isprefix_thm_aux \\ gvs [])
  \\ strip_tac \\ imp_res_tac IS_PREFIX_LENGTH
QED

Theorem isprefix_strcat:
  ∀s₁ s₂. isPrefix s₁ s₂ = ∃s₃. s₂ = s₁ ^ s₃
Proof
  rpt gen_tac
  \\ gvs [isprefix_thm, strcat_thm, isPREFIX_STRCAT, exists_mlstring,
          implode_def]
  \\ Cases_on ‘s₂’ \\ simp []
QED

Definition isSuffix_def:
  isSuffix s1 s2 =
    if strlen s1 <= strlen s2
      then isStringThere_aux s1 s2 0 (strlen s2 - strlen s1) (strlen s1)
    else F
End

Definition isSubstring_aux_def:
  (isSubstring_aux s1 s2 lens1 n 0 = F) /\
  (isSubstring_aux s1 s2 lens1 n (SUC len) =
    if (isStringThere_aux s1 s2 0 n lens1)
      then T
    else isSubstring_aux s1 s2 lens1 (n + 1) len)
End

Definition isSubstring_def:
  isSubstring s1 s2 =
  if strlen s1 <= strlen s2
    then isSubstring_aux s1 s2 (strlen s1) 0 ((strlen s2) - (strlen s1) + 1)
  else F
End

(* proof that isSubstring has the right sort of properties *)
Theorem isStringThere_SEG:
   ∀i1 i2.
     i1 + n ≤ LENGTH s1 ∧ i2 + n ≤ LENGTH s2 ⇒
     (isStringThere_aux (strlit s1) (strlit s2) i1 i2 n <=>
       (SEG n i1 s1 = SEG n i2 s2))
Proof
  Induct_on `n`
  >- simp[SEG, isStringThere_aux_def]
  >- simp[isStringThere_aux_def, SEG_SUC_EL]
QED

Theorem isSubstring_aux_lemma:
   ∀i len.
     i + len ≤ strlen s2 ==>
     (isSubstring_aux s1 s2 lens1 i len ⇔
      ∃n. n < len ∧ isStringThere_aux s1 s2 0 (n+i) lens1)
Proof
  Induct_on `len`
  >- simp[isSubstring_aux_def] >>
  fs[isSubstring_aux_def] >> rw[EQ_IMP_THM]
  >- (qexists_tac ‘0’ >> simp[])
  >- (rename [‘n < len’, ‘i + (n + 1)’] >> qexists_tac ‘n + 1’ >> simp[]) >>
  rename [‘isStringThere_aux _ _ 0 (i + n)’] >>
  Cases_on ‘n’ >> fs[] >> metis_tac[ADD1]
QED

Theorem isSubstring_SEG:
   isSubstring (strlit s1) (strlit s2) <=>
   ∃i. i + LENGTH s1 ≤ LENGTH s2 ∧ SEG (LENGTH s1) i s2 = s1
Proof
  rw[isSubstring_def] >> Cases_on `s1` >> simp[]
  >- (fs[isSubstring_aux_def, isStringThere_aux_def, GSYM ADD1] >>
      qexists_tac `0` >> simp[SEG])
  >- (simp[] >>
      rename [‘SUC (STRLEN s0) ≤ STRLEN s2’, ‘STRING h s0’] >>
      Cases_on ‘SUC(STRLEN s0) ≤ STRLEN s2’ >> fs[] >>
      csimp[isSubstring_aux_lemma, isStringThere_SEG, SUB_LEFT_LESS,
            DECIDE “x < y + 1n ⇔ x ≤ y”] >>
      ‘STRLEN (STRING h s0) = SUC (STRLEN s0)’ by simp[] >>
      metis_tac[SEG_LENGTH_ID])
QED

Theorem strlit_STRCAT:
   strlit a ^ strlit b = strlit (a ++ b)
Proof
  fs[strcat_def, concat_def]
QED

Theorem isSubString_spec:
   isSubstring s1 s2 ⇔ ∃p s. s2 = p ^ s1 ^ s
Proof
  map_every Cases_on [`s1`,`s2`] >> rw[isSubstring_SEG, EQ_IMP_THM]
  >- (rename [‘SEG (STRLEN s1) i s2 = s1’] >>
      map_every qexists_tac [
        ‘strlit (TAKE i s2)’, ‘strlit (DROP (i + STRLEN s1) s2)’
      ] >> simp[strlit_STRCAT] >> metis_tac[TAKE_SEG_DROP, ADD_COMM]) >>
  rename [‘strlit s2 = px ^ strlit s1 ^ sx’] >>
  qexists_tac `strlen px` >> Cases_on `px` >> simp[strlit_STRCAT] >>
  Cases_on `sx` >> fs[strlit_STRCAT] >>
  simp[SEG_APPEND1, SEG_APPEND2, SEG_LENGTH_ID]
QED

(* String orderings *)
Definition compare_aux_def:
  compare_aux (s1: mlstring) s2 ord start len =
    if len = 0n then
      ord
    else if strsub s2 start < strsub s1 start
      then GREATER
    else if strsub s1 start < strsub s2 start
      then LESS
    else compare_aux s1 s2 ord (start + 1) (len - 1)
End

Definition compare_def:
  compare s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)
End

Definition mlstring_lt_def:
  mlstring_lt s1 s2 ⇔ (compare s1 s2 = LESS)
End

Definition mlstring_le_def:
  mlstring_le s1 s2 ⇔ (compare s1 s2 ≠ GREATER)
End

Definition mlstring_gt_def:
  mlstring_gt s1 s2 ⇔ (compare s1 s2 = GREATER)
End

Definition mlstring_ge_def:
  mlstring_ge s1 s2 ⇔ (compare s1 s2 <> LESS)
End

Overload "<" = ``λx y. mlstring_lt x y``
Overload "<=" = ``λx y. mlstring_le x y``
Overload ">" = ``λx y. mlstring_gt x y``
Overload ">=" = ``λx y. mlstring_ge x y``

(* Properties of string orderings *)

val flip_ord_def = ternaryComparisonsTheory.invert_comparison_def
Overload flip_ord = ``invert_comparison``

Theorem compare_aux_spec[local]:
  !s1 s2 ord_in start len.
    len + start ≤ strlen s1 ∧ len + start ≤ strlen s2 ⇒
    (compare_aux s1 s2 ord_in start len =
      if TAKE len (DROP start (explode s1)) = TAKE len (DROP start (explode s2)) then
        ord_in
      else if string_lt (TAKE len (DROP start (explode s1))) (TAKE len (DROP start (explode s2))) then
        LESS
      else
        GREATER)
Proof
  Induct_on `len` >>
  rw [] >>
  ONCE_REWRITE_TAC [compare_aux_def] >>
  simp [] >>
  Cases_on `s1` >>
  Cases_on `s2` >>
  fs [] >>
  full_simp_tac (srw_ss()) [TAKE_SUM, DECIDE ``!n. SUC n = 1 + n``] >>
  fs [TAKE1_DROP, DROP_DROP_T, char_lt_def] >>
  fs [string_lt_def] >>
  simp [] >>
  rw [] >>
  fs [char_lt_def, CHAR_EQ_THM]
QED

Theorem compare_aux_refl[local]:
  !s1 s2 start len.
    start + len ≤ strlen s1 ∧ start + len ≤ strlen s2
    ⇒
    ((compare_aux s1 s2 EQUAL start len = EQUAL)
     ⇔
     (TAKE len (DROP start (explode s1)) = TAKE len (DROP start (explode s2))))
Proof
  rw [compare_aux_spec]
QED

Theorem compare_aux_equal[local]:
  !s1 s2 ord_in start len.
    (compare_aux s1 s2 ord_in start len = EQUAL) ⇒ (ord_in = EQUAL)
Proof
  Induct_on `len` >>
  rw []
  >- fs [Once compare_aux_def] >>
  pop_assum mp_tac >>
  ONCE_REWRITE_TAC [compare_aux_def] >>
  simp_tac (std_ss++ARITH_ss) [] >>
  rw [] >>
  metis_tac []
QED

Theorem compare_aux_sym[local]:
  !s1 s2 ord_in start len ord_out.
    (compare_aux s1 s2 ord_in start len = ord_out)
    ⇔
    (compare_aux s2 s1 (flip_ord ord_in) start len = flip_ord ord_out)
Proof
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
  metis_tac []
QED

Theorem string_lt_take_mono[local]:
  !s1 s2 x.
    s1 < s2 ⇒ TAKE x s1 < TAKE x s2 ∨ (TAKE x s1 = TAKE x s2)
Proof
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def] >>
  Cases_on `x` >>
  fs [string_lt_def] >>
  metis_tac []
QED

Theorem string_lt_remove_take[local]:
  !s1 s2 x. TAKE x s1 < TAKE x s2 ⇒ s1 < s2
Proof
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def] >>
  Cases_on `x` >>
  fs [string_lt_def] >>
  metis_tac []
QED

Theorem string_prefix_le[local]:
  !s1 s2. s1 ≼ s2 ⇒ s1 ≤ s2
Proof
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def, string_le_def, isPREFIX_STRCAT] >>
  Cases_on `s3` >>
  fs []
QED

Theorem take_prefix[local]:
  !l s. TAKE l s ≼ s
Proof
  Induct_on `s` >>
  rw [] >>
  Cases_on `l` >>
  fs []
QED

Theorem mlstring_lt_inv_image:
   mlstring_lt = inv_image string_lt explode
Proof
  simp [inv_image_def, FUN_EQ_THM] >>
  Cases >>
  Cases >>
  simp [mlstring_lt_def, compare_def, compare_aux_spec] >>
  qmatch_goalsub_abbrev_tac ‘if x < x' then _ else _’ >>
  rw []
  >- (
    `TAKE x s' ≤ s'` by metis_tac [take_prefix, string_prefix_le] >>
    fs [string_le_def] >>
    `x ≠ x'` by decide_tac >>
    unabbrev_all_tac >> fs [])
  >- metis_tac [string_lt_remove_take, TAKE_LENGTH_ID]
  >- metis_tac [string_lt_take_mono, TAKE_LENGTH_ID]
  >- metis_tac [take_prefix, string_prefix_le, LENGTH_TAKE, LESS_OR_EQ, string_lt_antisym, string_le_def]
  >- metis_tac [string_lt_remove_take, TAKE_LENGTH_ID]
  >- metis_tac [string_lt_take_mono, TAKE_LENGTH_ID]
  >- metis_tac [take_prefix, string_prefix_le, string_lt_antisym, string_le_def]
  >- metis_tac [string_lt_remove_take, TAKE_LENGTH_ID]
  >- metis_tac [string_lt_take_mono, TAKE_LENGTH_ID]
QED

Theorem TotOrd_compare:
   TotOrd compare
Proof
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
    metis_tac [string_lt_trans])
QED

Theorem good_cmp_compare:
   good_cmp compare
Proof
  match_mp_tac comparisonTheory.TotOrder_imp_good_cmp \\
  MATCH_ACCEPT_TAC TotOrd_compare
QED

Theorem mlstring_lt_antisym:
   ∀s t. ¬(s < t ∧ t < s)
Proof
  rw [mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd, cpn_distinct]
QED

Theorem mlstring_lt_cases:
   ∀s t. (s = t) ∨ s < t ∨ t < s
Proof
  rw [mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd, cpn_nchotomy]
QED

Theorem mlstring_lt_nonrefl:
   ∀s. ¬(s < s)
Proof
  rw [mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd, cpn_distinct]
QED

Theorem mlstring_lt_trans:
   ∀s1 s2 s3. s1 < s2 ∧ s2 < s3 ⇒ s1 < s3
Proof
  rw [mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd]
QED

Theorem mlstring_le_thm:
   !s1 s2. s1 ≤ s2 ⇔ (s1 = s2) ∨ s1 < s2
Proof
  rw [mlstring_le_def, mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd, cpn_distinct, cpn_nchotomy]
QED

Theorem mlstring_gt_thm:
   !s1 s2. s1 > s2 ⇔ s2 < s1
Proof
  rw [mlstring_gt_def, mlstring_lt_def] >>
  metis_tac [TotOrd_compare, TotOrd]
QED

Theorem mlstring_ge_thm:
   !s1 s2. s1 ≥ s2 ⇔ s2 ≤ s1
Proof
  rw [mlstring_ge_def, mlstring_le_def] >>
  metis_tac [TotOrd_compare, TotOrd]
QED

Theorem transitive_mlstring_le:
   transitive mlstring_le
Proof
  fs [transitive_def,mlstring_le_thm]
  \\ rw [] \\ fs [mlstring_lt_inv_image]
  \\ imp_res_tac string_lt_trans \\ fs []
QED

Theorem antisymmetric_mlstring_le:
   antisymmetric mlstring_le
Proof
  fs [antisymmetric_def,mlstring_le_thm]
  \\ rw [] \\ fs [mlstring_lt_inv_image]
  \\ imp_res_tac string_lt_antisym
QED

Theorem char_lt_total:
   !(c1:char) c2. ¬(c1 < c2) ∧ ¬(c2 < c1) ⇒ c1 = c2
Proof
  rw [char_lt_def, CHAR_EQ_THM]
QED

Theorem string_lt_total:
   !(s1:string) s2. ¬(s1 < s2) ∧ ¬(s2 < s1) ⇒ s1 = s2
Proof
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def, char_lt_total]
  >- (
    Cases_on `s1` >>
    fs [string_lt_def]) >>
  metis_tac [char_lt_total]
QED

Theorem total_mlstring_le:
   total mlstring_le
Proof
  fs [total_def,mlstring_le_thm] \\ CCONTR_TAC \\ fs []
  \\ rw [] \\ fs [mlstring_lt_inv_image]
  \\ imp_res_tac string_lt_total \\ fs []
QED

Theorem transitive_mlstring_lt[local]:
  transitive mlstring_lt
Proof
  simp[mlstring_lt_inv_image] >>
  match_mp_tac transitive_inv_image >>
  metis_tac[transitive_def,string_lt_trans]
QED

Theorem strlit_le_strlit:
   strlit s1 ≤ strlit s2 <=> s1 <= s2
Proof
  fs [mlstring_le_thm] \\ Cases_on `s1 = s2`
  \\ fs [string_le_def,mlstring_lt_inv_image]
QED

Theorem irreflexive_mlstring_lt[local]:
  irreflexive mlstring_lt
Proof
  simp[mlstring_lt_inv_image] >>
  match_mp_tac irreflexive_inv_image >>
  simp[irreflexive_def,string_lt_nonrefl]
QED

Theorem trichotomous_mlstring_lt[local]:
  trichotomous mlstring_lt
Proof
  simp[mlstring_lt_inv_image] >>
  match_mp_tac trichotomous_inv_image >>
  reverse conj_tac >- metis_tac[explode_BIJ,BIJ_DEF] >>
  metis_tac[trichotomous,string_lt_cases]
QED

Theorem StrongLinearOrder_mlstring_lt:
   StrongLinearOrder mlstring_lt
Proof
  rw[StrongLinearOrder,trichotomous_mlstring_lt,
     StrongOrder,irreflexive_mlstring_lt,transitive_mlstring_lt]
QED

Definition collate_aux_def:
  (collate_aux f (s1: mlstring) s2 ord n 0 = ord) /\
  (collate_aux f s1 s2 ord n (SUC len) =
    if f (strsub s1 n) (strsub s2 n) = EQUAL
      then collate_aux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n))
End

Definition collate_def:
  collate f s1 s2 =
  if (strlen s1) < (strlen s2)
    then collate_aux f s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then collate_aux f s1 s2 GREATER 0 (strlen s2)
  else collate_aux f s1 s2 EQUAL 0 (strlen s2)
End


Theorem collate_aux_less_thm[local]:
  !f s1 s2 n len.
    n + len = strlen s1 /\ strlen s1 < strlen s2 ==>
    collate_aux f s1 s2 Less n len =
    mllist$collate f (DROP n (explode s1)) (DROP n (explode s2))
Proof
  Cases_on `s1` \\ Cases_on `s2` \\ Induct_on `len` \\
  rw [collate_aux_def, mllistTheory.collate_def, strlen_def, explode_thm,
      strsub_def, DROP_EL_CONS]
QED

Theorem collate_aux_equal_thm[local]:
  !f s1 s2 n len.
    n + len = strlen s2 /\ strlen s1 = strlen s2 ==>
    collate_aux f s1 s2 Equal n len =
    mllist$collate f (DROP n (explode s1)) (DROP n (explode s2))
Proof
  Cases_on `s1` \\ Cases_on `s2` \\ Induct_on `len` \\
  rw [collate_aux_def, mllistTheory.collate_def, strlen_def, explode_thm, strsub_def]
  >- rw [DROP_LENGTH_TOO_LONG, mllistTheory.collate_def] \\
  fs [DROP_EL_CONS, mllistTheory.collate_def]
QED

Theorem collate_aux_greater_thm[local]:
  !f s1 s2 n len.
    n + len = strlen s2 /\ strlen s2 < strlen s1 ==>
    collate_aux f s1 s2 Greater n len =
    mllist$collate f (DROP n (explode s1)) (DROP n (explode s2))
Proof
  Cases_on `s1` \\ Cases_on `s2` \\ Induct_on `len` \\
  rw [collate_aux_def, mllistTheory.collate_def, strlen_def, explode_thm,
      strsub_def, DROP_EL_CONS]
QED

Theorem collate_thm:
   !f s1 s2. collate f s1 s2 = mllist$collate f (explode s1) (explode s2)
Proof
  rw [collate_def, collate_aux_greater_thm, collate_aux_equal_thm, collate_aux_less_thm]
QED

Definition char_escape_seq_def:
  char_escape_seq c =
    if c = #"\t"
    then SOME (strlit "\\t")
    else if c = #"\n"
    then SOME (strlit "\\n")
    else if c = #"\\"
    then SOME (strlit "\\\\")
    else if c = #"\""
    then SOME (strlit "\\\"")
    else NONE
End

Definition char_escaped_def:
  char_escaped c = case char_escape_seq c of
    NONE => [c]
  | SOME s => explode s
End

Definition escape_str_def:
  escape_str s = implode ("\"" ++ FLAT (MAP char_escaped (explode s)) ++ "\"")
End

Definition escape_char_def:
  escape_char c = implode ("#\"" ++ char_escaped c ++ "\"")
End

Theorem ALL_DISTINCT_MAP_implode[simp]:
   ALL_DISTINCT ls ⇒ ALL_DISTINCT (MAP implode ls)
Proof
  strip_tac >>
  match_mp_tac ALL_DISTINCT_MAP_INJ >>
  rw[implode_def]
QED

Theorem ALL_DISTINCT_MAP_explode[simp]:
   ∀ls. ALL_DISTINCT (MAP explode ls) ⇔ ALL_DISTINCT ls
Proof
  gen_tac >> EQ_TAC >- MATCH_ACCEPT_TAC ALL_DISTINCT_MAP >>
  STRIP_TAC >> MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >>
  simp[explode_11]
QED

(* optimising mlstring app_list *)

Datatype:
  app_list_ann = BigList ('a list)
               | BigAppend app_list_ann app_list_ann
               | Small ('a app_list)
End

Definition sum_sizes_def:
  sum_sizes [] k = k ∧
  sum_sizes (l::ls) k = sum_sizes ls (strlen l + k)
End

Overload size_limit[local] = “2048:num”

Definition make_app_list_ann_def:
  make_app_list_ann input =
    case input of
    | Nil => (Small input, 0)
    | Append l1 l2 =>
        (let (x1,n1) = make_app_list_ann l1 in
         let (x2,n2) = make_app_list_ann l2 in
         let n = n1+n2 in
           if n < size_limit then
             (Small input,n)
           else
             (BigAppend x1 x2,n))
    | List ls =>
        (let n = sum_sizes ls 0 in
           if n < size_limit then
             (Small input,n)
           else (BigList ls,n))
End

Definition shrink_def:
  shrink (Small t) = List [concat (append t)] ∧
  shrink (BigList ls) = List ls ∧
  shrink (BigAppend l1 l2) = Append (shrink l1) (shrink l2)
End

Definition str_app_list_opt_def:
  str_app_list_opt l =
    let (t,n) = make_app_list_ann l in
      shrink t
End

Theorem str_app_list_opt_test[local]:
  str_app_list_opt (Append (List [strlit "Hello"; strlit " there"])
                           (List [strlit "!"])) =
  List [strlit "Hello there!"]
Proof
  EVAL_TAC
QED

Theorem str_app_list_opt_thm:
  concat (append (str_app_list_opt l)) = concat (append l)
Proof
  ‘str_app_list_opt l = shrink $ FST $ make_app_list_ann l’
       by fs [str_app_list_opt_def,UNCURRY]
  \\ fs [] \\ pop_assum kall_tac
  \\ Induct_on ‘l’
  >~ [‘Nil’] >- EVAL_TAC
  >~ [‘Append’] >-
   (simp [Once make_app_list_ann_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ IF_CASES_TAC
    \\ gvs [shrink_def,concat_cons,concat_nil,concat_append])
  \\ simp [Once make_app_list_ann_def] \\ rw []
  \\ gvs [shrink_def,concat_cons,concat_nil,concat_append]
QED

Theorem concat_sing[simp]:
  concat [x] = x
Proof
  Cases_on ‘x’ \\ gvs [concat_def]
QED

(* The translator turns each `empty_ffi s` into a call to the FFI with
   an empty name and passing `s` as the argument. The empty FFI is
   used for logging/timing purposes. *)
Definition empty_ffi_def:
  empty_ffi (s:mlstring) = ()
End
