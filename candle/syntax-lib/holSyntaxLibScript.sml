(*
  Definitions for manipulating (deeply embedded) HOL syntax.
*)
open preamble mlstringTheory

val _ = new_theory"holSyntaxLib"

val ALPHAVARS_def = Define`
  (ALPHAVARS [] tmp ⇔ (FST tmp = SND tmp)) ∧
  (ALPHAVARS (tp::oenv) tmp ⇔
    (tmp = tp) ∨
    (FST tp ≠ FST tmp) ∧ (SND tp ≠ SND tmp) ∧ ALPHAVARS oenv tmp)`

Theorem ALPHAVARS_REFL:
   ∀env t. EVERY (UNCURRY $=) env ==> ALPHAVARS env (t,t)
Proof
  Induct >> simp[ALPHAVARS_def,FORALL_PROD]
QED

Theorem ALPHAVARS_MEM:
   ∀env tp. ALPHAVARS env tp ⇒ MEM tp env ∨ (FST tp = SND tp)
Proof
   Induct >> simp[ALPHAVARS_def] >> rw[] >> res_tac >> simp[]
QED

val REV_ASSOCD_def = Define`
  (REV_ASSOCD a [] d = d) ∧
  (REV_ASSOCD a (p::t) d = if SND p = a then FST p else REV_ASSOCD a t d)`

Theorem REV_ASSOCD:
   (∀a d. REV_ASSOCD a [] d = d) ∧
    (∀a x y t d. REV_ASSOCD a ((x,y)::t) d =
                 if y = a then x else REV_ASSOCD a t d)
Proof
  rw[REV_ASSOCD_def]
QED

Theorem REV_ASSOCD_ALOOKUP:
   ∀ls x d. REV_ASSOCD x ls d = case ALOOKUP (MAP (λ(x,y). (y,x)) ls) x of NONE => d | SOME y => y
Proof
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> rw[]
QED

Theorem PRIMED_INFINITE:
   INFINITE (IMAGE (λn. APPEND x (GENLIST (K #"'") n)) UNIV)
Proof
  match_mp_tac (MP_CANON IMAGE_11_INFINITE) >>
  simp[] >> Induct >- metis_tac[NULL_EQ,NULL_GENLIST] >>
  simp[GENLIST_CONS] >> qx_gen_tac`y` >>
  Cases_on`GENLIST (K #"'") y`>>simp[]>>rw[]>>
  Cases_on`y`>>fs[GENLIST_CONS]
QED

Theorem REV_ASSOCD_FILTER:
   ∀l a b d.
      REV_ASSOCD a (FILTER (λ(y,x). P x) l) b =
        if P a then REV_ASSOCD a l b else b
Proof
  Induct >> simp[REV_ASSOCD,FORALL_PROD] >>
  rw[] >> fs[FORALL_PROD,REV_ASSOCD] >> rw[] >> fs[]
QED

Theorem REV_ASSOCD_MEM:
   ∀l x d. MEM (REV_ASSOCD x l d,x) l ∨ (REV_ASSOCD x l d = d)
Proof
  Induct >> simp[REV_ASSOCD,FORALL_PROD] >>rw[]>>fs[]
QED

Theorem tyvar_inst_exists:
   ∃i. ty = REV_ASSOCD tyvar i b
Proof
  qexists_tac`[(ty,tyvar)]` >> rw[REV_ASSOCD]
QED

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

Theorem NOT_IS_CLASH_IS_RESULT:
   ∀x. IS_CLASH x ⇔ ¬IS_RESULT x
Proof
  Cases >> simp[]
QED

Theorem RESULT_eq_suff:
   x = Result y ⇒ RESULT x = y
Proof
  Cases_on`x`>>simp[]
QED

Theorem IS_CLASH_IMP:
   !x. IS_CLASH x ==> !tm. ~(x = Result tm)
Proof
  Cases \\ simp[]
QED

Theorem NOT_IS_CLASH_IMP:
   !x. ~IS_CLASH x ==> !tm. ~(x = Clash tm)
Proof
  Cases \\ simp[]
QED

Theorem IS_RESULT_IMP:
   !x. IS_RESULT x ==> (!tm. ~(x = Clash tm))
Proof
  Cases \\ simp[]
QED

Theorem NOT_IS_RESULT_IMP_Clash:
   !x. ~IS_RESULT x ==> ?var. x = Clash var
Proof
  Cases \\ simp[]
QED

Theorem IS_RESULT_IMP_Result:
   !x. IS_RESULT x ==> ?res. x = Result res
Proof
  Cases \\ simp[]
QED

Theorem NOT_IS_CLASH_IMP_Result:
   !x. ~IS_CLASH x ==> ?res. x = Result res
Proof
  Cases \\ simp[]
QED

val LIST_INSERT_def = Define`
  LIST_INSERT x xs = if MEM x xs then xs else x::xs`

Theorem MEM_LIST_INSERT:
   ∀l x. set (LIST_INSERT x l) = x INSERT set l
Proof
  Induct >> simp[LIST_INSERT_def] >> rw[] >>
  rw[EXTENSION] >> metis_tac[]
QED

val LIST_UNION_def = Define`
  LIST_UNION xs ys = FOLDR LIST_INSERT ys xs`

Theorem MEM_LIST_UNION:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
Proof
  Induct >> fs[LIST_UNION_def,MEM_LIST_INSERT] >>
  rw[EXTENSION] >> metis_tac[]
QED

Theorem MEM_FOLDR_LIST_UNION:
   ∀ls x f b. MEM x (FOLDR (λx y. LIST_UNION (f x) y) b ls) ⇔ MEM x b ∨ ∃y. MEM y ls ∧ MEM x (f y)
Proof
  Induct >> simp[MEM_LIST_UNION] >> metis_tac[]
QED

Theorem ALL_DISTINCT_LIST_UNION:
   ∀l1 l2. ALL_DISTINCT l2 ⇒ ALL_DISTINCT (LIST_UNION l1 l2)
Proof
  Induct >> fs[LIST_UNION_def,LIST_INSERT_def] >> rw[]
QED

Theorem LIST_UNION_NIL:
   ∀l2. (LIST_UNION [] l2 = l2)
Proof
  simp[LIST_UNION_def]
QED
val _ = export_rewrites["LIST_UNION_NIL"]

Theorem set_LIST_UNION:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
Proof
  rw[EXTENSION,MEM_LIST_UNION]
QED
val _ = export_rewrites["set_LIST_UNION"]

Theorem LIST_UNION_NIL_2:
   ∀ls. ALL_DISTINCT ls ⇒ LIST_UNION ls [] = ls
Proof
  Induct >> simp[LIST_UNION_def,LIST_INSERT_def] >>
  rw[] >> fs[] >> rfs[LIST_UNION_def]
QED

Theorem LIST_UNION_same:
   ∀l1 l2. set l1 ⊆ set l2 ⇒ LIST_UNION l1 l2 = l2
Proof
  Induct >> simp[LIST_UNION_def] >>
  fs[pred_setTheory.SUBSET_DEF] >>
  fs[LIST_UNION_def,LIST_INSERT_def]
QED

val INORDER_INSERT_def = Define`
  INORDER_INSERT x xs =
    APPEND (FILTER (λy. string_lt y x) xs)
   (APPEND [x] (FILTER (λy. string_lt x y) xs))`

val LENGTH_INORDER_INSERT = Q.prove(
  `!xs. ALL_DISTINCT (x::xs) ==> (LENGTH (INORDER_INSERT x xs) = SUC (LENGTH xs))`,
  FULL_SIMP_TAC std_ss [INORDER_INSERT_def,LENGTH_APPEND,LENGTH]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [DECIDE ``1 + n = SUC n``]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,ADD_CLAUSES]
  \\ MATCH_MP_TAC (GSYM LENGTH_EQ_FILTER_FILTER)
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `MEM y xs`
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x = y` \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [stringTheory.string_lt_cases,stringTheory.string_lt_antisym]);

val ALL_DISTINCT_INORDER_INSERT = Q.prove(
  `!xs h. ALL_DISTINCT xs ==> ALL_DISTINCT (INORDER_INSERT h xs)`,
  FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT,INORDER_INSERT_def,
    ALL_DISTINCT_APPEND,MEM_FILTER] \\ REPEAT STRIP_TAC
  \\ TRY (MATCH_MP_TAC FILTER_ALL_DISTINCT)
  \\ FULL_SIMP_TAC (srw_ss()) [stringTheory.string_lt_nonrefl]
  \\ METIS_TAC [stringTheory.string_lt_antisym]);

val ALL_DISTINCT_FOLDR_INORDER_INSERT = Q.prove(
  `!xs. ALL_DISTINCT (FOLDR INORDER_INSERT [] xs)`,
  Induct \\ SIMP_TAC std_ss [ALL_DISTINCT,FOLDR] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC ALL_DISTINCT_INORDER_INSERT \\ FULL_SIMP_TAC std_ss []);

Theorem MEM_FOLDR_INORDER_INSERT:
   !xs x. MEM x (FOLDR INORDER_INSERT [] xs) = MEM x xs
Proof
  Induct \\ FULL_SIMP_TAC std_ss [FOLDR,INORDER_INSERT_def,MEM,MEM_APPEND,
    MEM_FILTER] \\ METIS_TAC [stringTheory.string_lt_cases]
QED
val _ = export_rewrites["MEM_FOLDR_INORDER_INSERT"]

val STRING_SORT_def = Define`
  STRING_SORT xs = FOLDR INORDER_INSERT [] xs`

Theorem PERM_STRING_SORT:
   ∀ls. ALL_DISTINCT ls ⇒ PERM ls (STRING_SORT ls)
Proof
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
  metis_tac[FILTER_ALL_DISTINCT,ALL_DISTINCT_PERM,string_lt_antisym,string_lt_cases,MEM_PERM]
QED

Theorem LENGTH_STRING_SORT:
   ∀ls. ALL_DISTINCT ls ⇒ (LENGTH (STRING_SORT ls) = LENGTH ls)
Proof
  metis_tac[PERM_STRING_SORT,PERM_LENGTH]
QED
val _ = export_rewrites["LENGTH_STRING_SORT"]

Theorem MEM_STRING_SORT:
   ∀ls. set (STRING_SORT ls) = set ls
Proof
  Induct >>
  simp[STRING_SORT_def,INORDER_INSERT_def,EXTENSION,MEM_FILTER] >>
  rw[] >> metis_tac[string_lt_cases]
QED
val _ = export_rewrites["MEM_STRING_SORT"]

Theorem ALL_DISTINCT_STRING_SORT:
   !xs. ALL_DISTINCT (STRING_SORT xs)
Proof
  Induct
  >> FULL_SIMP_TAC std_ss [STRING_SORT_def,FOLDR,ALL_DISTINCT,INORDER_INSERT_def]
  >> FULL_SIMP_TAC std_ss [ALL_DISTINCT_APPEND,MEM_FILTER,MEM,MEM_APPEND,
       ALL_DISTINCT,stringTheory.string_lt_nonrefl]
  >> REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  >> TRY (MATCH_MP_TAC FILTER_ALL_DISTINCT)
  >> FULL_SIMP_TAC std_ss []
  >> METIS_TAC [stringTheory.string_lt_antisym,stringTheory.string_lt_trans,
        stringTheory.string_lt_cases]
QED
val _ = export_rewrites["ALL_DISTINCT_STRING_SORT"]

Theorem STRING_SORT_SORTED:
   ∀ls. SORTED $< (STRING_SORT ls)
Proof
  Induct >> simp[STRING_SORT_def,INORDER_INSERT_def] >>
  rw[] >> match_mp_tac SORTED_APPEND >>
  conj_asm1_tac >- METIS_TAC [string_lt_trans,relationTheory.transitive_def] >>
  simp[MEM_FILTER] >> fs[GSYM STRING_SORT_def] >>
  simp[SORTED_FILTER] >>
  conj_tac >- (
    match_mp_tac SORTED_APPEND >>
    simp[SORTED_FILTER,MEM_FILTER] ) >>
  rw[] >> fs[relationTheory.transitive_def] >>
  METIS_TAC[]
QED

Theorem STRING_SORT_EQ:
   ∀l1 l2. ALL_DISTINCT l1 ∧ ALL_DISTINCT l2 ⇒
      (STRING_SORT l1 = STRING_SORT l2 ⇔ PERM l1 l2)
Proof
  rw[] >>
  imp_res_tac PERM_STRING_SORT >>
  `transitive string_lt ∧ antisymmetric string_lt` by (
    simp[relationTheory.transitive_def,relationTheory.antisymmetric_def] >>
    METIS_TAC[string_lt_trans,string_lt_antisym] ) >>
  `SORTED $< (STRING_SORT l1) ∧ SORTED $< (STRING_SORT l2)`
    by METIS_TAC[STRING_SORT_SORTED] >>
  METIS_TAC[SORTED_PERM_EQ,PERM_REFL,PERM_SYM,PERM_TRANS]
QED

Theorem ALL_DISTINCT_LIST_UNION:
   ∀l1 l2. ALL_DISTINCT l2 ⇒ ALL_DISTINCT (LIST_UNION l1 l2)
Proof
  Induct >> fs[LIST_UNION_def,LIST_INSERT_def] >> rw[]
QED

Theorem set_MAP_implode_STRING_SORT_MAP_explode:
   set (MAP implode (STRING_SORT (MAP explode ls))) = set ls
Proof
  rw[EXTENSION,MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode]
QED

val mlstring_sort_def = Define`
  mlstring_sort ls = MAP implode (STRING_SORT (MAP explode ls))`

Theorem mlstring_sort_eq:
   ∀l1 l2. ALL_DISTINCT l1 ∧ ALL_DISTINCT l2 ⇒
    ((mlstring_sort l1 = mlstring_sort l2) ⇔ PERM l1 l2)
Proof
  rw[mlstring_sort_def] >>
  qspecl_then[`l1`,`l2`]mp_tac(MATCH_MP PERM_MAP_BIJ mlstringTheory.explode_BIJ) >>
  disch_then SUBST1_TAC >>
  imp_res_tac ALL_DISTINCT_MAP_explode >>
  imp_res_tac STRING_SORT_EQ >>
  first_x_assum(CHANGED_TAC o (SUBST1_TAC o SYM)) >>
  match_mp_tac INJ_MAP_EQ_IFF >>
  mp_tac mlstringTheory.implode_BIJ >>
  simp[BIJ_DEF,INJ_DEF,MEM_MAP,PULL_EXISTS]
QED

val _ = export_theory()
