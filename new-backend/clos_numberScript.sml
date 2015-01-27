open HolKernel boolLib bossLib miscLib lcsymtacs
open arithmeticTheory listTheory pairTheory sortingTheory rich_listTheory finite_mapTheory
open closLangTheory
val _ = new_theory"clos_number"

(* TODO: move *)
val SORTED_ALL_DISTINCT = store_thm("SORTED_ALL_DISTINCT",
  ``irreflexive R /\ transitive R ==> !ls. SORTED R ls ==> ALL_DISTINCT ls``,
  STRIP_TAC THEN Induct THEN SRW_TAC[][] THEN
  IMP_RES_TAC SORTED_EQ THEN
  FULL_SIMP_TAC (srw_ss()) [SORTED_DEF] THEN
  METIS_TAC[relationTheory.irreflexive_def])

val EXISTS_ZIP = Q.prove (
`!l f. EXISTS (\(x,y). f x) l = EXISTS f (MAP FST l)`,
 Induct_on `l` >>
 rw [] >>
 Cases_on `h` >>
 fs [] >>
 metis_tac []);

val EVERY_ZIP = Q.prove (
`!l f. EVERY (\(x,y). f x) l = EVERY f (MAP FST l)`,
 Induct_on `l` >>
 rw [] >>
 Cases_on `h` >>
 fs [] >>
 metis_tac []);


val list_rel_lastn = Q.prove (
`!f l1 l2 n.
  n ≤ LENGTH l1 ∧
  LIST_REL f l1 l2 ⇒ 
  LIST_REL f (LASTN n l1) (LASTN n l2)`, 
 Induct_on `l1` >>
 rw [LASTN] >>
 imp_res_tac EVERY2_LENGTH >>
 Cases_on `n = LENGTH l1 + 1`
 >- metis_tac [LASTN_LENGTH_ID, ADD1, LENGTH, LIST_REL_def] >>
 `n ≤ LENGTH l1` by decide_tac >>
 `n ≤ LENGTH ys` by decide_tac >>
 res_tac >>
 fs [LASTN_CONS]);

val list_rel_butlastn = Q.prove (
`!f l1 l2 n.
  n ≤ LENGTH l1 ∧
  LIST_REL f l1 l2 ⇒ 
  LIST_REL f (BUTLASTN n l1) (BUTLASTN n l2)`, 
 Induct_on `l1` >>
 rw [BUTLASTN] >>
 imp_res_tac EVERY2_LENGTH >>
 Cases_on `n = LENGTH l1 + 1`
 >- metis_tac [BUTLASTN_LENGTH_NIL, ADD1, LENGTH, LIST_REL_def] >>
 `n ≤ LENGTH l1` by decide_tac >>
 `n ≤ LENGTH ys` by decide_tac >>
 res_tac >>
 fs [BUTLASTN_CONS]);


(* -- *)

(* add locations after translation from patLang *)

val lookup_vars_NONE = prove(
  ``!vs. (lookup_vars vs env = NONE) <=> ?v. MEM v vs /\ LENGTH env <= v``,
  Induct \\ fs [lookup_vars_def]
  \\ REPEAT STRIP_TAC \\ fs []
  \\ Cases_on `h < LENGTH env` \\ fs [NOT_LESS]
  \\ Cases_on `lookup_vars vs env` \\ fs []
  THEN1 METIS_TAC []
  \\ CCONTR_TAC \\ fs [] \\ METIS_TAC [NOT_LESS])

val lookup_vars_SOME = prove(
  ``!vs env xs.
      (lookup_vars vs env = SOME xs) ==>
      (LENGTH vs = LENGTH xs)``,
  Induct \\ fs [lookup_vars_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ fs [] \\ SRW_TAC [] [] \\ RES_TAC);

val lookup_vars_MEM = prove(
  ``!ys n x (env2:clos_val list).
      (lookup_vars ys env2 = SOME x) /\ n < LENGTH ys ==>
      (EL n ys) < LENGTH env2 /\
      (EL n x = EL (EL n ys) env2)``,
  Induct \\ fs [lookup_vars_def] \\ NTAC 5 STRIP_TAC
  \\ Cases_on `lookup_vars ys env2` \\ fs []
  \\ Cases_on `n` \\ fs [] \\ SRW_TAC [] [] \\ fs []) |> SPEC_ALL;

val code_locs_def = tDefine "code_locs" `
  (code_locs [] = []) /\
  (code_locs (x::y::xs) =
     let c1 = code_locs [x] in
     let c2 = code_locs (y::xs) in
       c1 ++ c2) /\
  (code_locs [Var v] = []) /\
  (code_locs [If x1 x2 x3] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
     let c3 = code_locs [x3] in
       c1 ++ c2 ++ c3) /\
  (code_locs [Let xs x2] =
     let c1 = code_locs xs in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Raise x1] =
     code_locs [x1]) /\
  (code_locs [Tick x1] =
     code_locs [x1]) /\
  (code_locs [Op op xs] =
     code_locs xs) /\
  (code_locs [App loc_opt x1 xs] =
     let c1 = code_locs [x1] in
     let c2 = code_locs xs in
         c1++c2) /\
  (code_locs [Fn loc vs num_args x1] =
     let c1 = code_locs [x1] in
       c1 ++ [loc]) /\
  (code_locs [Letrec loc vs fns x1] =
     let c1 = code_locs (MAP SND fns) in
     let c2 = code_locs [x1] in
     c1 ++ GENLIST ($+ loc) (LENGTH fns) ++ c2) /\
  (code_locs [Handle x1 x2] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Call dest xs] =
     code_locs xs)`
 (WF_REL_TAC `measure (clos_exp3_size)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
  Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  Cases_on `h` >>
  fs [clos_exp_size_def] >>
  decide_tac);

val code_locs_cons = store_thm("code_locs_cons",
  ``∀x xs. code_locs (x::xs) = code_locs [x] ++ code_locs xs``,
  gen_tac >> Cases >> simp[code_locs_def])

val renumber_code_locs_def = tDefine "renumber_code_locs" `
  (renumber_code_locs_list n [] = (n,[])) /\
  (renumber_code_locs_list n (x::xs) =
     let (n,x) = renumber_code_locs n x in
     let (n,xs) = renumber_code_locs_list n xs in
     (n, x::xs)) /\
  (renumber_code_locs n (Var v) = (n,(Var v))) /\
  (renumber_code_locs n (If x1 x2 x3) =
     let (n,x1) = renumber_code_locs n x1 in
     let (n,x2) = renumber_code_locs n x2 in
     let (n,x3) = renumber_code_locs n x3 in
       (n,If x1 x2 x3)) /\
  (renumber_code_locs n (Let xs x2) =
     let (n,xs) = renumber_code_locs_list n xs in
     let (n,x2) = renumber_code_locs n x2 in
       (n,Let xs x2)) /\
  (renumber_code_locs n (Raise x1) =
     let (n,x1) = renumber_code_locs n x1 in
       (n,Raise x1)) /\
  (renumber_code_locs n (Tick x1) =
     let (n,x1) = renumber_code_locs n x1 in
       (n,Tick x1)) /\
  (renumber_code_locs n (Op op xs) =
     let (n,xs) = renumber_code_locs_list n xs in
       (n,Op op xs)) /\
  (renumber_code_locs n (App loc_opt x1 x2) =
     let (n,x1) = renumber_code_locs n x1 in
     let (n,x2) = renumber_code_locs_list n x2 in
       (n,App loc_opt x1 x2)) /\
  (renumber_code_locs n (Fn loc vs num_args x1) =
     let (n,x1) = renumber_code_locs n x1 in
       (n+1,Fn n vs num_args x1)) /\
  (renumber_code_locs n (Letrec loc vs fns x1) =
     let (m,fns') = renumber_code_locs_list n (MAP SND fns) in
     let (n,x1) = renumber_code_locs (m+LENGTH fns') x1 in
     (n,Letrec m vs (ZIP (MAP FST fns, fns')) x1)) /\
  (renumber_code_locs n (Handle x1 x2) =
     let (n,x1) = renumber_code_locs n x1 in
     let (n,x2) = renumber_code_locs n x2 in
     (n,Handle x1 x2)) /\
  (renumber_code_locs n (Call dest xs) =
     let (n,xs) = renumber_code_locs_list n xs in
     (n,Call dest xs))`
 (WF_REL_TAC `inv_image $< (λx. case x of INL p => clos_exp3_size (SND p) | INR p => clos_exp_size (SND p))` >>
 rw [] >>
 TRY decide_tac >>
 Induct_on `fns` >>
 srw_tac [ARITH_ss] [clos_exp_size_def] >>
 Cases_on `h` >>
 rw [clos_exp_size_def] >>
 decide_tac);

val renumber_code_locs_ind = theorem"renumber_code_locs_ind"

fun tac (g as (asl,w)) =
  let
    fun finder tm =
      let
        val (f,args) = strip_comb tm
      in
        (same_const``renumber_code_locs`` f orelse
         same_const``renumber_code_locs_list`` f)
        andalso
         all is_var args
        andalso
         length args = 2
      end
    val tms = find_terms finder w
  in
    map_every (fn tm => Cases_on [ANTIQUOTE tm]) tms g
  end

val renumber_code_locs_inc = store_thm("renumber_code_locs_inc",
  ``(∀n es. n ≤ FST (renumber_code_locs_list n es)) ∧
    (∀n e. n ≤ FST (renumber_code_locs n e))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def] >> rw[] >>
  tac >> fs[] >>
  tac >> fs[] >>
  tac >> fs[] >> simp[] >>
  Cases_on `renumber_code_locs_list n (MAP SND fns)` >> rw [] >>
  Cases_on`renumber_code_locs (q+LENGTH r) e`>>fs[]>>simp[])

val renumber_code_locs_imp_inc = store_thm("renumber_code_locs_imp_inc",
  ``(renumber_code_locs_list n es = (m,vs) ⇒ n ≤ m) ∧
    (renumber_code_locs n e = (z,v) ⇒ n ≤ z)``,
  metis_tac[pairTheory.pair_CASES,pairTheory.FST,renumber_code_locs_inc])

val sorted_append = MATCH_MP SORTED_transitive_APPEND_IFF transitive_LESS
val sorted_eq = MATCH_MP SORTED_EQ transitive_LESS

val SORTED_GENLIST_PLUS = prove(
  ``∀n k. SORTED $< (GENLIST ($+ k) n)``,
  Induct >> simp[GENLIST_CONS,sorted_eq,MEM_GENLIST] >> gen_tac >>
  `$+ k o SUC = $+ (k+1)` by (
    simp[FUN_EQ_THM] ) >>
  metis_tac[])

val renumber_code_locs_list_length = prove(
  ``∀ls n x y. renumber_code_locs_list n ls = (x,y) ⇒ LENGTH y = LENGTH ls``,
  Induct >> simp[renumber_code_locs_def,LENGTH_NIL] >> rw[] >>
  Cases_on`renumber_code_locs n h`>>fs[]>>
  Cases_on`renumber_code_locs_list q ls`>>fs[]>>rw[]>>
  res_tac)

val renumber_code_locs_distinct_lemma = prove(
  ``(∀n es. SORTED $< (code_locs (SND (renumber_code_locs_list n es))) ∧
            EVERY ($<= n) (code_locs (SND (renumber_code_locs_list n es))) ∧
            EVERY ($> (FST (renumber_code_locs_list n es))) (code_locs (SND (renumber_code_locs_list n es)))) ∧
    (∀n e. SORTED $< (code_locs [SND (renumber_code_locs n e)]) ∧
            EVERY ($<= n) (code_locs [SND (renumber_code_locs n e)]) ∧
            EVERY ($> (FST (renumber_code_locs n e))) (code_locs [SND (renumber_code_locs n e)]))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def,code_locs_def,pairTheory.UNCURRY] >>
  rw[] >> rpt (CHANGED_TAC tac >> fs[]) >> rw[] >>
  imp_res_tac renumber_code_locs_imp_inc >> simp[] >>
  simp[EVERY_GENLIST] >>
  TRY (
    CHANGED_TAC(simp[EVERY_MEM]) >>
    fs[EVERY_MEM] >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC ) >>
  TRY (
    CHANGED_TAC(simp[EVERY_MEM]) >>
    fs[EVERY_MEM] >>
    simp[Once code_locs_cons] >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC ) >>
  rpt(match_mp_tac sortingTheory.SORTED_APPEND >> simp[] >> TRY conj_tac) >>
  TRY (
    rw[] >> fs[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC) >>
  TRY (
    simp[Once code_locs_cons] >>
    match_mp_tac sortingTheory.SORTED_APPEND >> simp[] >>
    rw[] >> fs[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC ) >>
  TRY (
    Cases_on`renumber_code_locs (n+1) e`>>fs[] >>
    simp[sorted_eq] >>
    imp_res_tac renumber_code_locs_imp_inc >>
    rw[] >> fs[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC) >>
  Cases_on `renumber_code_locs_list n (MAP SND fns)` >>
  fs [] >>
  Cases_on`renumber_code_locs (q+LENGTH fns) e`>>fs[] >>
  rpt(CHANGED_TAC tac >> fs[])>>
  simp[SORTED_GENLIST_PLUS] >>
  simp[MEM_GENLIST] >>
  imp_res_tac renumber_code_locs_imp_inc >>
  imp_res_tac renumber_code_locs_list_length >>
  rw[] >> fs[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] >>
  rw[] >> fs[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][MAP_ZIP] >>
  rfs [MAP_ZIP] >>
  rw[] >> fs[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][MAP_ZIP]);

val renumber_code_locs_distinct = store_thm("renumber_code_locs_distinct",
  ``∀n e. ALL_DISTINCT (code_locs [SND (renumber_code_locs n e)]) ∧
          EVERY ($<= n) (code_locs [SND (renumber_code_locs n e)]) ∧
          EVERY ($> (FST (renumber_code_locs n e))) (code_locs [SND (renumber_code_locs n e)])``,
  rw[] >>
  qspecl_then[`n`,`e`]strip_assume_tac (CONJUNCT2 renumber_code_locs_distinct_lemma) >> simp[] >>
  match_mp_tac (MP_CANON (GEN_ALL SORTED_ALL_DISTINCT)) >>
  qexists_tac`$<` >> simp[] >>
  simp[relationTheory.irreflexive_def])

val contains_App_SOME_def = tDefine "contains_App_SOME" `
  (contains_App_SOME [] ⇔ F) /\
  (contains_App_SOME (x::y::xs) ⇔
     contains_App_SOME [x] ∨
     contains_App_SOME (y::xs)) /\
  (contains_App_SOME [Var v] ⇔ F) /\
  (contains_App_SOME [If x1 x2 x3] ⇔
     contains_App_SOME [x1] ∨
     contains_App_SOME [x2] ∨
     contains_App_SOME [x3]) /\
  (contains_App_SOME [Let xs x2] ⇔
     contains_App_SOME [x2] ∨
     contains_App_SOME xs) /\
  (contains_App_SOME [Raise x1] ⇔
     contains_App_SOME [x1]) /\
  (contains_App_SOME [Tick x1] ⇔
     contains_App_SOME [x1]) /\
  (contains_App_SOME [Op op xs] ⇔
     contains_App_SOME xs) /\
  (contains_App_SOME [App loc_opt x1 x2] ⇔
     IS_SOME loc_opt ∨
     contains_App_SOME [x1] ∨
     contains_App_SOME x2) /\
  (contains_App_SOME [Fn loc vs num_args x1] ⇔
     contains_App_SOME [x1]) /\
  (contains_App_SOME [Letrec loc vs fns x1] ⇔
     contains_App_SOME (MAP SND fns) ∨
     contains_App_SOME [x1]) /\
  (contains_App_SOME [Handle x1 x2] ⇔
     contains_App_SOME [x1] ∨
     contains_App_SOME [x2]) /\
  (contains_App_SOME [Call dest xs] ⇔
     contains_App_SOME xs)`
 (WF_REL_TAC `measure (clos_exp3_size)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
  Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  Cases_on `h` >>
  fs [clos_exp_size_def] >>
  decide_tac);

val (val_rel_rules,val_rel_ind,val_rel_cases) = Hol_reln `
  (val_rel (Number j) (Number j))
  /\
  (EVERY2 val_rel (xs:clos_val list) (ys:clos_val list) ==>
   val_rel (Block t xs) (Block t ys))
  /\
  (val_rel (RefPtr r1) (RefPtr r1))
  /\
  (LIST_REL val_rel env env' ∧
   LIST_REL val_rel argenv argenv' ∧
   ¬contains_App_SOME [c] ∧
   c' = SND (renumber_code_locs n c) ==>
   val_rel (Closure p argenv env num_args c) (Closure p' argenv' env' num_args c'))
  /\
  (LIST_REL val_rel env env' ∧
   LIST_REL val_rel argenv argenv' ∧
   ¬contains_App_SOME (MAP SND es) ∧
   es' = ZIP (MAP FST es, SND (renumber_code_locs_list n (MAP SND es)))
   ⇒
   val_rel (Recclosure p argenv env es k) (Recclosure p' argenv' env' es' k))`

val (ref_rel_rules,ref_rel_ind,ref_rel_cases) = Hol_reln `
  (EVERY2 val_rel xs ys ==>
   ref_rel (ValueArray xs) (ValueArray ys)) /\
  (ref_rel (ByteArray b) (ByteArray b))`

val code_rel_def = Define`
  code_rel (a1,e1) (a2,e2) ⇔
    (a1 = a2) ∧ ¬contains_App_SOME [e1] ∧
    ∃n. e2 = SND (renumber_code_locs n e1)`

val state_rel_def = Define `
  state_rel (s:clos_state) (t:clos_state) <=>
    (s.clock = t.clock) /\ (s.output = t.output) /\
    (s.restrict_envs = t.restrict_envs) ∧
    fmap_rel ref_rel s.refs t.refs ∧
    EVERY2 (OPTREL val_rel) s.globals t.globals /\
    fmap_rel code_rel s.code t.code`

val (res_rel_rules,res_rel_ind,res_rel_cases) = Hol_reln `
  (EVERY2 val_rel xs ys ==>
   res_rel (Result xs) (Result ys)) /\
  (val_rel x y ==>
   res_rel (Exception x) (Exception y)) /\
  (res_rel TimeOut TimeOut) /\
  (res_rel Error Error)`

val res_rel_simp = let
  val f = SIMP_CONV (srw_ss()) [res_rel_cases]
  in map f [``res_rel (Result x) y``,
            ``res_rel (Exception x) y``,
            ``res_rel Error y``,
            ``res_rel TimeOut y``] |> LIST_CONJ end
val _ = save_thm("res_rel_simp",res_rel_simp)

val val_rel_simp = let
  val f = SIMP_CONV (srw_ss()) [Once val_rel_cases]
  in map f [``val_rel (Number x) y``,
            ``val_rel (Block n l) y``,
            ``val_rel (RefPtr x) y``,
            ``val_rel (Closure n a l narg x) y``,
            ``val_rel (Recclosure x1 x2 x3 x4 x5) y``,
            ``val_rel y (Number x)``,
            ``val_rel y (Block n l)``,
            ``val_rel y (RefPtr x)``,
            ``val_rel y (Closure n a l narg x)``,
            ``val_rel y (Recclosure x1 x2 x3 x4 x5)``] |> LIST_CONJ end
  |> curry save_thm"val_rel_simp"

val renumber_code_locs_list_els = prove(
  ``∀ls ls' n n'. renumber_code_locs_list n ls = (n',ls') ⇒
      ∀x. x < LENGTH ls ⇒
        ∃m. EL x ls' = SND (renumber_code_locs m (EL x ls))``,
  Induct >> simp[renumber_code_locs_def] >>
  simp[UNCURRY] >> rw[] >>
  Cases_on`x`>>fs[] >- METIS_TAC[] >>
  first_x_assum (MATCH_MP_TAC o MP_CANON) >>
  simp[] >>
  METIS_TAC[pair_CASES,SND])

val contains_App_SOME_EXISTS = store_thm("contains_App_SOME_EXISTS",
  ``∀ls. contains_App_SOME ls ⇔ EXISTS (λx. contains_App_SOME [x]) ls``,
  Induct >> simp[contains_App_SOME_def] >>
  Cases_on`ls`>>fs[contains_App_SOME_def])

val state_rel_clock = Q.prove (
`!s t. state_rel s t ⇒ state_rel (s with clock := x) (t with clock := x)`,
 rw [state_rel_def]);

val dest_closure_val_rel_none = Q.prove (
`!f args f' args'.
  val_rel f f' ∧
  LIST_REL val_rel args args' ∧
  dest_closure NONE f args = NONE
  ⇒ 
  dest_closure NONE f' args' = NONE`,
 rw [] >>
 imp_res_tac EVERY2_LENGTH >>
 fs [dest_closure_def, val_rel_cases] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [LET_THM, check_loc_def] >>
 rw [] >>
 imp_res_tac EVERY2_LENGTH >>
 rw [] >>
 TRY decide_tac >>
 Cases_on `EL k es` >>
 fs [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 Cases_on `renumber_code_locs_list n (MAP SND es)` >>
 imp_res_tac renumber_code_locs_list_length >>
 rw [] >>
 Cases_on `EL k (ZIP (MAP FST es,r'))` >>
 rw [] >>
 CCONTR_TAC >>
 fs [] >>
 `k < LENGTH es` by decide_tac >>
 `LENGTH (MAP FST es) = LENGTH r'` by metis_tac [LENGTH_MAP] >>
 fs [EL_ZIP, EL_MAP] >>
 rw [] >>
 rfs []);

val dest_closure_val_rel_partial = Q.prove (
`!c f args f' args'.
  val_rel f f' ∧
  LIST_REL val_rel args args' ∧
  dest_closure NONE f args = SOME (Partial_app c)
  ⇒ 
  ?c'.
    dest_closure NONE f' args' = SOME (Partial_app c') ∧
    val_rel c c'`,
 rw [] >>
 imp_res_tac EVERY2_LENGTH >>
 fs [dest_closure_def, val_rel_cases] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [LET_THM, check_loc_def] >>
 rw [] >>
 imp_res_tac EVERY2_LENGTH >>
 rw [] >>
 TRY decide_tac
 >- metis_tac [EVERY2_APPEND] >>
 Cases_on `EL k es` >>
 fs [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 Cases_on `renumber_code_locs_list n (MAP SND es)` >>
 imp_res_tac renumber_code_locs_list_length >>
 rw [] >>
 Cases_on `EL k (ZIP (MAP FST es,r'))` >>
 rw [] >>
 CCONTR_TAC >>
 fs [] >>
 `k < LENGTH es` by decide_tac >>
 `LENGTH (MAP FST es) = LENGTH r'` by metis_tac [LENGTH_MAP] >>
 fs [EL_ZIP, EL_MAP] >>
 rw [] >>
 rfs [] >>
 metis_tac [SND, EVERY2_APPEND]);

val dest_closure_val_rel_full = Q.prove (
`!c f args f' args' args1 args2.
  val_rel f f' ∧
  LIST_REL val_rel args args' ∧
  dest_closure NONE f args = SOME (Full_app exp args1 args2)
  ⇒ 
  ?args1' args2' n.
    dest_closure NONE f' args' = SOME (Full_app (SND (renumber_code_locs n exp)) args1' args2') ∧
    LIST_REL val_rel args1 args1' ∧
    LIST_REL val_rel args2 args2' ∧
    ~contains_App_SOME [exp]`,
 rw [] >>
 imp_res_tac EVERY2_LENGTH >>
 fs [dest_closure_def, val_rel_cases] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [LET_THM, check_loc_def] >>
 rw [] >>
 imp_res_tac EVERY2_LENGTH >>
 rw [] >>
 TRY (qexists_tac `n`) >>
 TRY decide_tac >>
 rw [] >>
 TRY decide_tac >>
 TRY (`n' - LENGTH argenv' ≤ LENGTH args'` by decide_tac) >>
 fs [] >>
 rw [DROP_REVERSE, TAKE_REVERSE] >>
 TRY (`n' - LENGTH argenv' ≤ LENGTH args'` by decide_tac)
 >- metis_tac [list_rel_butlastn, list_rel_lastn, EVERY2_APPEND]
 >- metis_tac [list_rel_butlastn, list_rel_lastn, EVERY2_APPEND] >>
 Cases_on `renumber_code_locs_list n (MAP SND es)` >>
 fs [] >>
 Cases_on `EL k es` >>
 fs [] >>
 Cases_on `LENGTH args' + LENGTH argenv' < q'` >>
 fs [] >>
 rw [] >>
 imp_res_tac renumber_code_locs_list_length >>
 rw [] >>
 `k < LENGTH es` by decide_tac >>
 fs [EL_ZIP, EL_MAP] >>
 cheat);

val helper = Q.prove (
`SND ((λ(n',x'). (n',[x'])) x) = [SND x]`,
 Cases_on `x` >>
 fs []);

val renumber_code_locs_correct = store_thm("renumber_code_locs_correct",
  ``(!tmp xs env s1 env' t1 res s2 n.
      tmp = (xs,env,s1) ∧
      (cEval (xs,env,s1) = (res,s2)) ⇒
      ¬contains_App_SOME xs ∧
      LIST_REL val_rel env env' ∧
      state_rel s1 t1 ==>
      ?res' t2.
         (cEval (SND(renumber_code_locs_list n xs),env',t1) = (res',t2)) /\
         res_rel res res' /\
         state_rel s2 t2) ∧
    (!loc f args s res s2 f' args' s1 t1.
        cEvalApp loc f args s = (res,s2) ⇒
        val_rel f f' ∧
        loc = NONE ∧
        LIST_REL val_rel args args' ∧
        state_rel s t1
        ⇒
        ?res' t2.
           (cEvalApp loc f' args' t1 = (res',t2)) /\
           res_rel res res' /\
           state_rel s2 t2)``,
  ho_match_mp_tac cEval_ind \\ rw []
  THEN1 (* NIL *)
   (fs [renumber_code_locs_def,cEval_def]
    \\ SRW_TAC [] [res_rel_cases])
  THEN1 (* CONS *)
   (simp [renumber_code_locs_def,cEval_def,UNCURRY] >>
    tac >> fs[] >> rw[] >>
    tac >> fs[] >> rw[] >>
    tac >> fs[] >> rw[] >>
    fs[cEval_def]
    \\ `?r1 s1. cEval ([x],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs []
    \\ fs[renumber_code_locs_def,LET_THM,contains_App_SOME_def] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [res_rel_simp] >> rw[res_rel_simp] >>
    `?r2 s2. cEval (y::xs,env,s1) = (r2,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r2` \\ fs [res_rel_simp] >> rw[res_rel_simp] >>
    imp_res_tac cEval_SING >> fs[])
  THEN1 (* Var *)
   (rw[renumber_code_locs_def] >>
    fs[LIST_REL_EL_EQN] >>
    fs[cEval_def] >> rw[] >> fs[] >> rw[res_rel_simp])
  THEN1 (* If *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY] >>
    tac >> fs[] >> rw[] >>
    tac >> fs[] >> rw[] >>
    tac >> fs[] >> rw[] >>
    fs[cEval_def,contains_App_SOME_def] >>
    `?r1 s1. cEval ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [res_rel_simp] >> rw[res_rel_simp] >> fs[] >>
    imp_res_tac cEval_SING >> fs[] >> rw[] >> fs[val_rel_simp] >> rw[] >>
    TRY (
      first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
      disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
      NO_TAC) >>
    TRY (
      first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
      disch_then(fn th => first_x_assum(qspec_then`q'`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
      NO_TAC) >>
    qpat_assum`X = (res,Y)`mp_tac >>
    rw[res_rel_simp] >> fs[val_rel_simp,res_rel_simp])
  THEN1 (* Let *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY] >>
    tac >> fs[] >> rw[] >>
    fs[cEval_def,contains_App_SOME_def] >>
    `?r1 s1. cEval (xs,env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [res_rel_simp] >> rw[res_rel_simp] >> fs[] >>
    first_x_assum MATCH_MP_TAC >> rw[] >>
    MATCH_MP_TAC EVERY2_APPEND_suff >> rw[] )
  THEN1 (* Raise *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s1. cEval ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[cEval_def,contains_App_SOME_def] >>
    tac >> fs[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [res_rel_simp] >> rw[res_rel_simp] >> fs[] >>
    imp_res_tac cEval_SING >> fs[])
  THEN1 (* Handle *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s2. cEval ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[cEval_def,contains_App_SOME_def] >>
    tac >> fs[] >> rw[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [res_rel_simp] >> rw[res_rel_simp] >> fs[] )
  THEN1 (* Op *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s2. cEval (xs,env,s) = (r1,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[cEval_def,contains_App_SOME_def] >>
    tac >> fs[] >> rw[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [res_rel_simp] >> rw[res_rel_simp] >> fs[] >>
    cheat)
  THEN1 (* Fn *)
   (fs [renumber_code_locs_def,cEval_def,LET_THM,UNCURRY] >>
    `t1.restrict_envs = s.restrict_envs` by fs[state_rel_def] >>
    fs[clos_env_def] >> rw[] >> fs[contains_App_SOME_def] >> rw[res_rel_simp,val_rel_simp] >>
    TRY (fs [res_rel_cases] >> PROVE_TAC[]) >>
    last_x_assum mp_tac >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac lookup_vars_NONE >>
      BasicProvers.CASE_TAC >> rw[] >> rw[res_rel_simp] >>
      imp_res_tac lookup_vars_SOME >>
      imp_res_tac lookup_vars_MEM >>
      fs[LIST_REL_EL_EQN,MEM_EL] >> rw[] >> rfs[] >>
      res_tac >> DECIDE_TAC ) >>
    rw[] >>
    imp_res_tac lookup_vars_SOME >>
    imp_res_tac lookup_vars_MEM >>
    BasicProvers.CASE_TAC >> rw[] >> rw[res_rel_simp,val_rel_simp] >- (
      imp_res_tac lookup_vars_NONE >> fs[MEM_EL] >>
      res_tac >>
      imp_res_tac LIST_REL_LENGTH >>
      DECIDE_TAC ) >>
    fs[LIST_REL_EL_EQN] >>
    qexists_tac`n`>>simp[] >>
    imp_res_tac lookup_vars_SOME >>
    imp_res_tac lookup_vars_MEM >>
    simp[] )
  THEN1 (* Letrec *)
   (fs[renumber_code_locs_def,cEval_def,LET_THM,UNCURRY] >>
    `t1.restrict_envs = s.restrict_envs` by fs[state_rel_def] >>
    Cases_on`renumber_code_locs_list n (MAP SND fns)`>>fs[]>>
    imp_res_tac renumber_code_locs_list_length >>
    fs [EVERY_ZIP, MAP_ZIP] >>
    reverse (rw []) >>
    full_simp_tac (bool_ss) []
    >- (rw [] >> rw [])
    >- rw [res_rel_cases] >>
    fs [combinTheory.o_DEF, EVERY_MAP, LAMBDA_PROD] >>
    fs[build_recc_def,clos_env_def] >> reverse(rw[]) >> fs[contains_App_SOME_def] >> rw[] >- (
      first_x_assum MATCH_MP_TAC >> rw[] >>
      MATCH_MP_TAC EVERY2_APPEND_suff >> rw[] >>
      imp_res_tac renumber_code_locs_list_length >>
      rw[LIST_REL_EL_EQN,EL_GENLIST] >>
      rw[val_rel_simp] >>
      METIS_TAC[SND] ) >>
    last_x_assum mp_tac >>
    BasicProvers.CASE_TAC >> fs[] >> rw[] >- (
      imp_res_tac lookup_vars_NONE >>
      BasicProvers.CASE_TAC >> rw[] >> rw[res_rel_simp] >>
      imp_res_tac lookup_vars_SOME >>
      imp_res_tac lookup_vars_MEM >>
      fs[LIST_REL_EL_EQN,MEM_EL] >> rw[] >> rfs[] >>
      res_tac >> `F` suffices_by rw[] >> DECIDE_TAC ) >>
    imp_res_tac lookup_vars_SOME >>
    imp_res_tac lookup_vars_MEM >>
    reverse BasicProvers.CASE_TAC >- (
      first_x_assum MATCH_MP_TAC >> rw[] >>
      MATCH_MP_TAC EVERY2_APPEND_suff >> rw[] >>
      imp_res_tac renumber_code_locs_list_length >>
      rw[LIST_REL_EL_EQN,EL_GENLIST] >>
      rw[val_rel_simp,LIST_REL_EL_EQN] >>
      imp_res_tac lookup_vars_SOME >>
      imp_res_tac lookup_vars_MEM >>
      qexists_tac`n`>>simp[] >>
      fs[LIST_REL_EL_EQN]) >>
    imp_res_tac lookup_vars_NONE >>
    imp_res_tac lookup_vars_SOME >>
    imp_res_tac lookup_vars_MEM >>
    imp_res_tac LIST_REL_EL_EQN >>
    fs[MEM_EL] >> res_tac >>
    `F` suffices_by rw[] >>
    DECIDE_TAC )
  THEN1 (* App *)
   (fs [renumber_code_locs_def,cEval_def,LET_THM,UNCURRY] >>
    `LENGTH (SND (renumber_code_locs_list (FST (renumber_code_locs n x1)) args)) = LENGTH args`
            by (Cases_on `renumber_code_locs n x1` >>
                fs [] >>
                Cases_on `renumber_code_locs_list q args` >>
                fs [] >>
                metis_tac [renumber_code_locs_list_length]) >>
    rw [] >>
    fs [] >>
    rw [res_rel_simp] >>
    tac >> fs[] >> rw[]
    \\ `?r1 s1. cEval (args,env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[contains_App_SOME_def] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [res_rel_simp] >> rw[res_rel_simp] >> fs[] >>
    `?r2 s2. cEval ([x1],env,s1) = (r2,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r2` \\ fs [res_rel_simp] >> rw[res_rel_simp] >> fs[] >>
    first_x_assum match_mp_tac >>
    rw [] >>
    imp_res_tac cEval_SING >> fs[] >> rw[] >>
    metis_tac [])
  THEN1 (* Tick *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s1. cEval ([x],env,dec_clock 1 s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[cEval_def,contains_App_SOME_def] >>
    tac >> fs[] >>
    `t1.clock = s.clock` by fs[state_rel_def] >>
    rw[] >> fs[res_rel_simp] >> rw[res_rel_simp] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(qspecl_then[`dec_clock 1 t1`,`n`]mp_tac) >>
    discharge_hyps >- fs[state_rel_def,dec_clock_def] >> rw[])
  THEN1 (* Call *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY] >>
    fs[cEval_def,contains_App_SOME_def] >>
    `?r1 s2. cEval (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [res_rel_simp] >> rw[res_rel_simp] >> fs[] >>
    fs[find_code_def] >>
    `FDOM s2'.code = FDOM t2.code` by fs[state_rel_def,fmap_rel_def] >>
    BasicProvers.CASE_TAC >> fs[] >- (
      fs[FLOOKUP_DEF] >>
      rw[res_rel_simp] ) >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac LIST_REL_LENGTH >>
    `s2'.clock = t2.clock` by fs[state_rel_def] >>
    `∃x. FLOOKUP s2'.code dest = SOME x ∧ code_rel x (q,r)` by (
      fs[state_rel_def,fmap_rel_def,FLOOKUP_DEF] >>
      METIS_TAC[] ) >>
    Cases_on`x`>>fs[code_rel_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    BasicProvers.CASE_TAC >> fs[] >- (
      rw[] >> fs[] >> rw[res_rel_simp] >> rfs[] >>
      first_x_assum MATCH_MP_TAC >>
      simp[] >>
      fs[state_rel_def,dec_clock_def] ) >>
    rw[res_rel_simp])
  THEN1 (* App empty *)
   (fs [cEval_def] >>
    rw [res_rel_cases])
  THEN1 (* Real App *)
   (fs [cEval_def] >>
    Cases_on `dest_closure NONE f (v41::v42)` >>
    fs [] >>
    rw []
    >- (imp_res_tac dest_closure_val_rel_none >>
        rw [res_rel_cases]) >>
    `s.clock = t1.clock` by fs[state_rel_def] >>
    imp_res_tac EVERY2_LENGTH >>
    Cases_on `x` >>
    fs []
    >- (`?c'. val_rel c c' ∧ dest_closure NONE f' (y::ys) = SOME (Partial_app c')`
                 by metis_tac [LIST_REL_def, dest_closure_val_rel_partial] >>
        rw [] >>
        fs [] >>
        rw [res_rel_cases, dec_clock_def] >>
        metis_tac [state_rel_clock])
    >- (`∃args1' args2' n.
           dest_closure NONE f' (y::ys) =
           SOME (Full_app (SND (renumber_code_locs n c)) args1' args2') ∧
           ~contains_App_SOME [c] ∧
           LIST_REL val_rel l args1' ∧ LIST_REL val_rel l0 args2'`
                     by prove_tac [dest_closure_val_rel_full, LIST_REL_def] >>
        simp [] >>
        imp_res_tac EVERY2_LENGTH >>
        fs [] >>
        rw [] >>
        fs []
        >- rw [res_rel_cases]
        >- metis_tac [state_rel_clock] >>
        Cases_on `cEval ([c],l,dec_clock (SUC (LENGTH ys) − LENGTH args2') s)` >>
        rw [] >>
        fs [] >>
        Cases_on `q` >>
        fs [] >>
        rw [] >>
        first_x_assum (qspecl_then [`args1'`, `dec_clock (SUC (LENGTH ys) - LENGTH (args2')) t1`, 
                                    `n`] mp_tac) >>
        rw [] >>
        fs [dec_clock_def] >>
        rfs [state_rel_clock] >>
        fs [renumber_code_locs_def, LET_THM, helper] >>
        BasicProvers.EVERY_CASE_TAC >>
        fs [res_rel_cases] >>
        metis_tac [])));
            
open pat_to_closTheory boolSimps

val pComp_contains_App_SOME = store_thm("pComp_contains_App_SOME",
  ``∀e. ¬contains_App_SOME[pComp e]``,
  ho_match_mp_tac pComp_ind >>
  simp[pComp_def,contains_App_SOME_def] >>
  rw[] >> srw_tac[ETA_ss][] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  rw[contains_App_SOME_def] >> rw[EVERY_MEM] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  rw[contains_App_SOME_def] >> rw[EVERY_MEM] >>
  fs[REPLICATE_GENLIST,MEM_GENLIST, MEM_MAP] >>
  rw[contains_App_SOME_def])

val _ = export_theory()
