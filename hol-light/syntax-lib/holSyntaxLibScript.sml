open HolKernel boolLib bossLib lcsymtacs pairTheory listTheory alistTheory pred_setTheory stringTheory sortingTheory arithmeticTheory
val _ = temp_tight_equality()
val _ = new_theory"holSyntaxLib"
infix \\ val op \\ = op THEN;

(* TOOD: move? *)
val SORTED_FILTER = store_thm("SORTED_FILTER",
  ``∀R ls P. transitive R ∧ SORTED R ls ⇒ SORTED R (FILTER P ls)``,
  ho_match_mp_tac SORTED_IND >>
  rw[] >> rw[] >> rfs[SORTED_EQ] >> fs[SORTED_EQ] >>
  first_x_assum(qspec_then`P`mp_tac) >> rw[] >>
  rfs[SORTED_EQ] >> fs[MEM_FILTER])

val LENGTH_EQ_FILTER_FILTER = store_thm("LENGTH_EQ_FILTER_FILTER",
  ``!xs. EVERY (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs ==>
         (LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q xs))``,
  Induct \\ SIMP_TAC std_ss [LENGTH,FILTER,EVERY_DEF] \\ STRIP_TAC
  \\ Cases_on `P h` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD_CLAUSES]);

val LIST_REL_MAP_FILTER_NEQ = store_thm("LIST_REL_MAP_FILTER_NEQ",
  ``∀P f1 f2 z1 z2 l1 l2.
      LIST_REL P (MAP f1 l1) (MAP f2 l2) ∧
      (∀y1 y2. MEM (y1,y2) (ZIP(l1,l2)) ⇒ (SND y1 ≠ z1 ⇔ SND y2 ≠ z2) ∧ (P (f1 y1) (f2 y2)))
      ⇒
      LIST_REL P (MAP f1 (FILTER (λ(x,y). y ≠ z1) l1)) (MAP f2 (FILTER (λ(x,y). y ≠ z2) l2))``,
  ntac 5 gen_tac >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  strip_tac >>
  Cases_on`h`>>fs[] >> rw[] >>
  METIS_TAC[SND])

val MAP_EQ_MAP_IMP = store_thm("MAP_EQ_MAP_IMP",
  ``!xs ys f.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      (MAP f xs = MAP f ys) ==> (xs = ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [MAP] \\ METIS_TAC []);
(* *)

val ALPHAVARS_def = Define`
  (ALPHAVARS [] tmp ⇔ (FST tmp = SND tmp)) ∧
  (ALPHAVARS (tp::oenv) tmp ⇔
    (tmp = tp) ∨
    (FST tp ≠ FST tmp) ∧ (SND tp ≠ SND tmp) ∧ ALPHAVARS oenv tmp)`

val ALPHAVARS_REFL = store_thm("ALPHAVARS_REFL",
  ``∀env t. EVERY (UNCURRY $=) env ==> ALPHAVARS env (t,t)``,
  Induct >> simp[ALPHAVARS_def,FORALL_PROD])

val ALPHAVARS_MEM = store_thm("ALPHAVARS_MEM",
  ``∀env tp. ALPHAVARS env tp ⇒ MEM tp env ∨ (FST tp = SND tp)``,
   Induct >> simp[ALPHAVARS_def] >> rw[] >> res_tac >> simp[])

val REV_ASSOCD_def = Define`
  (REV_ASSOCD a [] d = d) ∧
  (REV_ASSOCD a (p::t) d = if SND p = a then FST p else REV_ASSOCD a t d)`

val REV_ASSOCD = store_thm("REV_ASSOCD",
  ``(∀a d. REV_ASSOCD a [] d = d) ∧
    (∀a x y t d. REV_ASSOCD a ((x,y)::t) d =
                 if y = a then x else REV_ASSOCD a t d)``,
  rw[REV_ASSOCD_def])

val REV_ASSOCD_ALOOKUP = store_thm("REV_ASSOCD_ALOOKUP",
  ``∀ls x d. REV_ASSOCD x ls d = case ALOOKUP (MAP (λ(x,y). (y,x)) ls) x of NONE => d | SOME y => y``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> rw[])

val PRIMED_INFINITE = store_thm("PRIMED_INFINITE",
  ``INFINITE (IMAGE (λn. APPEND x (GENLIST (K #"'") n)) UNIV)``,
  match_mp_tac (MP_CANON IMAGE_11_INFINITE) >>
  simp[] >> Induct >- metis_tac[NULL_EQ,NULL_GENLIST] >>
  simp[GENLIST_CONS] >> qx_gen_tac`y` >>
  Cases_on`GENLIST (K #"'") y`>>simp[]>>rw[]>>
  Cases_on`y`>>fs[GENLIST_CONS])

val REV_ASSOCD_FILTER = store_thm("REV_ASSOCD_FILTER",
  ``∀l a b d.
      REV_ASSOCD a (FILTER (λ(y,x). P x) l) b =
        if P a then REV_ASSOCD a l b else b``,
  Induct >> simp[REV_ASSOCD,FORALL_PROD] >>
  rw[] >> fs[FORALL_PROD,REV_ASSOCD] >> rw[] >> fs[])

val REV_ASSOCD_MEM = store_thm("REV_ASSOCD_MEM",
  ``∀l x d. MEM (REV_ASSOCD x l d,x) l ∨ (REV_ASSOCD x l d = d)``,
  Induct >> simp[REV_ASSOCD,FORALL_PROD] >>rw[]>>fs[])

val _ = Hol_datatype`result = Clash of 'a | Result of 'a`

val IS_RESULT_def = Define`
  IS_RESULT(Clash _) = F ∧
  IS_RESULT(Result _) = T`

val IS_CLASH_def = Define`
  IS_CLASH(Clash _) = T ∧
  IS_CLASH(Result _) = F`

val RESULT_def = Define`
  RESULT(Result t) = t`

val CLASH_def = Define`
  CLASH(Clash t) = t`

val _ = export_rewrites["IS_RESULT_def","IS_CLASH_def","RESULT_def","CLASH_def"]

val NOT_IS_CLASH_IS_RESULT = store_thm("NOT_IS_CLASH_IS_RESULT",
  ``∀x. IS_CLASH x ⇔ ¬IS_RESULT x``,
  Cases >> simp[])

val RESULT_eq_suff = store_thm("RESULT_eq_suff",
  ``x = Result y ⇒ RESULT x = y``,
  Cases_on`x`>>simp[])

val IS_CLASH_IMP = store_thm("IS_CLASH_IMP",
  ``!x. IS_CLASH x ==> !tm. ~(x = Result tm)``,
  Cases \\ simp[])

val NOT_IS_CLASH_IMP = store_thm("NOT_IS_CLASH_IMP",
  ``!x. ~IS_CLASH x ==> !tm. ~(x = Clash tm)``,
  Cases \\ simp[])

val IS_RESULT_IMP = store_thm("IS_RESULT_IMP",
  ``!x. IS_RESULT x ==> (!tm. ~(x = Clash tm))``,
  Cases \\ simp[])

val NOT_IS_RESULT_IMP_Clash = store_thm("NOT_IS_RESULT_IMP_Clash",
  ``!x. ~IS_RESULT x ==> ?var. x = Clash var``,
  Cases \\ simp[])

val IS_RESULT_IMP_Result = store_thm("IS_RESULT_IMP_Result",
  ``!x. IS_RESULT x ==> ?res. x = Result res``,
  Cases \\ simp[])

val NOT_IS_CLASH_IMP_Result = store_thm("NOT_IS_CLASH_IMP_Result",
  ``!x. ~IS_CLASH x ==> ?res. x = Result res``,
  Cases \\ simp[])

val LIST_INSERT_def = Define`
  LIST_INSERT x xs = if MEM x xs then xs else x::xs`

val MEM_LIST_INSERT = store_thm("MEM_LIST_INSERT",
  ``∀l x. set (LIST_INSERT x l) = x INSERT set l``,
  Induct >> simp[LIST_INSERT_def] >> rw[] >>
  rw[EXTENSION] >> metis_tac[])

val LIST_UNION_def = Define`
  LIST_UNION xs ys = FOLDR LIST_INSERT ys xs`

val MEM_LIST_UNION = store_thm("MEM_LIST_UNION",
  ``∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2``,
  Induct >> fs[LIST_UNION_def,MEM_LIST_INSERT] >>
  rw[EXTENSION] >> metis_tac[])

val MEM_FOLDR_LIST_UNION = store_thm("MEM_FOLDR_LIST_UNION",
  ``∀ls x f b. MEM x (FOLDR (λx y. LIST_UNION (f x) y) b ls) ⇔ MEM x b ∨ ∃y. MEM y ls ∧ MEM x (f y)``,
  Induct >> simp[MEM_LIST_UNION] >> metis_tac[])

val ALL_DISTINCT_LIST_UNION = store_thm("ALL_DISTINCT_LIST_UNION",
  ``∀l1 l2. ALL_DISTINCT l2 ⇒ ALL_DISTINCT (LIST_UNION l1 l2)``,
  Induct >> fs[LIST_UNION_def,LIST_INSERT_def] >> rw[])

val LIST_UNION_NIL = store_thm("LIST_UNION_NIL",
  ``∀l2. (LIST_UNION [] l2 = l2)``,
  simp[LIST_UNION_def] )
val _ = export_rewrites["LIST_UNION_NIL"]

val set_LIST_UNION = store_thm("set_LIST_UNION",
  ``∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2``,
  rw[EXTENSION,MEM_LIST_UNION])
val _ = export_rewrites["set_LIST_UNION"]

val LIST_UNION_NIL_2 = store_thm("LIST_UNION_NIL_2",
  ``∀ls. ALL_DISTINCT ls ⇒ LIST_UNION ls [] = ls``,
  Induct >> simp[LIST_UNION_def,LIST_INSERT_def] >>
  rw[] >> fs[] >> rfs[LIST_UNION_def])

val LIST_UNION_same = store_thm("LIST_UNION_same",
  ``∀l1 l2. set l1 ⊆ set l2 ⇒ LIST_UNION l1 l2 = l2``,
  Induct >> simp[LIST_UNION_def] >>
  fs[pred_setTheory.SUBSET_DEF] >>
  fs[LIST_UNION_def,LIST_INSERT_def])

val INORDER_INSERT_def = Define`
  INORDER_INSERT x xs =
    APPEND (FILTER (λy. string_lt y x) xs)
   (APPEND [x] (FILTER (λy. string_lt x y) xs))`

val LENGTH_INORDER_INSERT = prove(
  ``!xs. ALL_DISTINCT (x::xs) ==> (LENGTH (INORDER_INSERT x xs) = SUC (LENGTH xs))``,
  FULL_SIMP_TAC std_ss [INORDER_INSERT_def,LENGTH_APPEND,LENGTH]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [DECIDE ``1 + n = SUC n``]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,ADD_CLAUSES]
  \\ MATCH_MP_TAC (GSYM LENGTH_EQ_FILTER_FILTER)
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `MEM y xs` []
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x = y` \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [stringTheory.string_lt_cases,stringTheory.string_lt_antisym]);

val ALL_DISTINCT_INORDER_INSERT = prove(
  ``!xs h. ALL_DISTINCT xs ==> ALL_DISTINCT (INORDER_INSERT h xs)``,
  FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT,INORDER_INSERT_def,
    ALL_DISTINCT_APPEND,MEM_FILTER] \\ REPEAT STRIP_TAC
  \\ TRY (MATCH_MP_TAC FILTER_ALL_DISTINCT)
  \\ FULL_SIMP_TAC (srw_ss()) [stringTheory.string_lt_nonrefl]
  \\ METIS_TAC [stringTheory.string_lt_antisym]);

val ALL_DISTINCT_FOLDR_INORDER_INSERT = prove(
  ``!xs. ALL_DISTINCT (FOLDR INORDER_INSERT [] xs)``,
  Induct \\ SIMP_TAC std_ss [ALL_DISTINCT,FOLDR] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC ALL_DISTINCT_INORDER_INSERT \\ FULL_SIMP_TAC std_ss []);

val MEM_FOLDR_INORDER_INSERT = store_thm("MEM_FOLDR_INORDER_INSERT",
  ``!xs x. MEM x (FOLDR INORDER_INSERT [] xs) = MEM x xs``,
  Induct \\ FULL_SIMP_TAC std_ss [FOLDR,INORDER_INSERT_def,MEM,MEM_APPEND,
    MEM_FILTER] \\ METIS_TAC [stringTheory.string_lt_cases]);
val _ = export_rewrites["MEM_FOLDR_INORDER_INSERT"]

val STRING_SORT_def = Define`
  STRING_SORT xs = FOLDR INORDER_INSERT [] xs`

val PERM_STRING_SORT = store_thm("PERM_STRING_SORT",
  ``∀ls. ALL_DISTINCT ls ⇒ PERM ls (STRING_SORT ls)``,
  Induct >>
  simp[STRING_SORT_def] >>
  simp[INORDER_INSERT_def] >>
  fs[STRING_SORT_def] >>
  simp[PERM_CONS_EQ_APPEND] >>
  gen_tac >> strip_tac >> fs[] >>
  qho_match_abbrev_tac`∃M N. A ++ [h] ++ B = M ++ [h] ++ N ∧ (Z M N)` >>
  map_every qexists_tac[`A`,`B`] >>
  simp[Abbr`Z`] >>
  match_mp_tac PERM_ALL_DISTINCT >>
  simp[ALL_DISTINCT_APPEND] >>
  simp[Abbr`A`,Abbr`B`,MEM_FILTER] >>
  metis_tac[FILTER_ALL_DISTINCT,ALL_DISTINCT_PERM,string_lt_antisym,string_lt_cases,MEM_PERM] )

val LENGTH_STRING_SORT = store_thm("LENGTH_STRING_SORT",
  ``∀ls. ALL_DISTINCT ls ⇒ (LENGTH (STRING_SORT ls) = LENGTH ls)``,
  metis_tac[PERM_STRING_SORT,PERM_LENGTH])
val _ = export_rewrites["LENGTH_STRING_SORT"]

val MEM_STRING_SORT = store_thm("MEM_STRING_SORT",
  ``∀ls. set (STRING_SORT ls) = set ls``,
  Induct >>
  simp[STRING_SORT_def,INORDER_INSERT_def,EXTENSION,MEM_FILTER] >>
  rw[] >> metis_tac[string_lt_cases])
val _ = export_rewrites["MEM_STRING_SORT"]

val ALL_DISTINCT_STRING_SORT = store_thm("ALL_DISTINCT_STRING_SORT",
  ``∀ls. ALL_DISTINCT ls ⇒ ALL_DISTINCT (STRING_SORT ls)``,
  metis_tac[PERM_STRING_SORT,ALL_DISTINCT_PERM])
val _ = export_rewrites["ALL_DISTINCT_STRING_SORT"]

val STRING_SORT_SORTED = store_thm("STRING_SORT_SORTED",
  ``∀ls. SORTED $< (STRING_SORT ls)``,
  Induct >> simp[STRING_SORT_def,INORDER_INSERT_def] >>
  rw[] >> match_mp_tac SORTED_APPEND >>
  conj_asm1_tac >- METIS_TAC [string_lt_trans,relationTheory.transitive_def] >>
  simp[MEM_FILTER] >> fs[GSYM STRING_SORT_def] >>
  simp[SORTED_FILTER] >>
  conj_tac >- (
    match_mp_tac SORTED_APPEND >>
    simp[SORTED_FILTER,MEM_FILTER] ) >>
  rw[] >> fs[relationTheory.transitive_def] >>
  METIS_TAC[])

(*
val STRING_SORT_EQ = store_thm("STRING_SORT_EQ",
  ``∀l1 l2. STRING_SORT l1 = STRING_SORT l2 ⇔ PERM l1 l2``,
  rw[EQ_IMP_THM] >>
  `transitive $< ∧ antisymmetric $<`
 SORTED_PERM_EQ
  Induct >> simp[STRING_SORT_def] >- (
    Cases >> simp[INORDER_INSERT_def] ) >>
  simp[INORDER_INSERT_def]
  print_apropos``QSORT R l1 = QSORT R l2``
  SORTED_EQ
*)

val ALL_DISTINCT_LIST_UNION = store_thm("ALL_DISTINCT_LIST_UNION",
  ``∀l1 l2. ALL_DISTINCT l2 ⇒ ALL_DISTINCT (LIST_UNION l1 l2)``,
  Induct >> fs[LIST_UNION_def,LIST_INSERT_def] >> rw[])

val _ = export_theory()
