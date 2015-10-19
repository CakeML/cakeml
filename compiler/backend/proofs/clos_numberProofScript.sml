open preamble closLangTheory clos_numberTheory closSemTheory closPropsTheory;

val _ = new_theory"clos_numberProof";

(* properties of renumber_code_locs *)

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
    simp[less_sorted_eq] >>
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

(* value relation *)

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln `
  (v_rel (Number j) (Number j))
  /\
  (EVERY2 v_rel (xs:closSem$v list) (ys:closSem$v list) ==>
   v_rel (Block t xs) (Block t ys))
  /\
  (v_rel (RefPtr r1) (RefPtr r1))
  /\
  (LIST_REL v_rel env env' ∧
   LIST_REL v_rel argenv argenv' ∧
   ¬contains_App_SOME [c] ∧
   c' = SND (renumber_code_locs n c) ==>
   v_rel (Closure p argenv env num_args c) (Closure p' argenv' env' num_args c'))
  /\
  (LIST_REL v_rel env env' ∧
   LIST_REL v_rel argenv argenv' ∧
   ¬contains_App_SOME (MAP SND es) ∧
   es' = ZIP (MAP FST es, SND (renumber_code_locs_list n (MAP SND es)))
   ⇒
   v_rel (Recclosure p argenv env es k) (Recclosure p' argenv' env' es' k))`

val code_rel_def = Define`
  code_rel (a1,e1) (a2,e2) ⇔
    (a1 = a2) ∧ ¬contains_App_SOME [e1] ∧
    ∃n. e2 = SND (renumber_code_locs n e1)`

val state_rel_def = Define `
  state_rel (s:'ffi closSem$state) (t:'ffi closSem$state) <=>
    (s.clock = t.clock) /\ (s.ffi = t.ffi) /\
    (s.restrict_envs = t.restrict_envs) ∧
    fmap_rel (ref_rel v_rel) s.refs t.refs ∧
    EVERY2 (OPTREL v_rel) s.globals t.globals /\
    fmap_rel code_rel s.code t.code`

val state_rel_clock = Q.prove (
  `!s t. state_rel s t ⇒ state_rel (s with clock := x) (t with clock := x)`,
   rw [state_rel_def]);

val state_rel_globals = prove(
  ``state_rel s t ⇒
    LIST_REL (OPTREL v_rel) s.globals t.globals``,
  rw[state_rel_def])

val state_rel_refs = prove(
  ``state_rel s t ⇒
    fmap_rel (ref_rel v_rel) s.refs t.refs``,
  rw[state_rel_def])

val v_rel_simp = let
  val f = SIMP_CONV (srw_ss()) [Once v_rel_cases]
  in map f [``v_rel (Number x) y``,
            ``v_rel (Block n l) y``,
            ``v_rel (RefPtr x) y``,
            ``v_rel (Closure n a l narg x) y``,
            ``v_rel (Recclosure x1 x2 x3 x4 x5) y``,
            ``v_rel y (Number x)``,
            ``v_rel y (Block n l)``,
            ``v_rel y (RefPtr x)``,
            ``v_rel y (Closure n a l narg x)``,
            ``v_rel y (Recclosure x1 x2 x3 x4 x5)``] |> LIST_CONJ end
  |> curry save_thm"v_rel_simp"

val v_rel_Boolv = store_thm("v_rel_Boolv[simp]",
  ``(v_rel x (Boolv b) ⇔ (x = Boolv b)) ∧
    (v_rel (Boolv b) x ⇔ (x = Boolv b))``,
  Cases_on`b`>>rw[Boolv_def,Once v_rel_cases] >>
  rw[Once v_rel_cases])

val v_rel_Unit = store_thm("v_rel_Unit[simp]",
  ``(v_rel x Unit ⇔ (x = Unit)) ∧
    (v_rel Unit x ⇔ (x = Unit))``,
  EVAL_TAC >> simp[v_rel_simp])

(* semantic functions respect relation *)

val dest_closure_v_rel_none = Q.prove (
  `!f args f' args'.
    v_rel f f' ∧
    LIST_REL v_rel args args' ∧
    dest_closure NONE f args = NONE
    ⇒
    dest_closure NONE f' args' = NONE`,
  rw [] >>
  imp_res_tac EVERY2_LENGTH >>
  fs [dest_closure_def, v_rel_cases] >>
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

val dest_closure_v_rel_partial = Q.prove (
  `!c f args f' args'.
    v_rel f f' ∧
    LIST_REL v_rel args args' ∧
    dest_closure NONE f args = SOME (Partial_app c)
    ⇒
    ?c'.
      dest_closure NONE f' args' = SOME (Partial_app c') ∧
      v_rel c c'`,
  rw [] >>
  imp_res_tac EVERY2_LENGTH >>
  fs [dest_closure_def, v_rel_cases] >>
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

val dest_closure_v_rel_full = Q.prove (
  `!c f args f' args' args1 args2.
    v_rel f f' ∧
    LIST_REL v_rel args args' ∧
    dest_closure NONE f args = SOME (Full_app exp args1 args2)
    ⇒
    ?args1' args2' n.
      dest_closure NONE f' args' = SOME (Full_app (SND (renumber_code_locs n exp)) args1' args2') ∧
      LIST_REL v_rel args1 args1' ∧
      LIST_REL v_rel args2 args2' ∧
      ~contains_App_SOME [exp]`,
  rw [] >>
  imp_res_tac EVERY2_LENGTH >>
  fs [dest_closure_def, v_rel_cases] >>
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
  `LIST_REL v_rel (GENLIST (Recclosure o' [] env es) (LENGTH es))
                    (GENLIST (Recclosure p' [] env' (ZIP (MAP FST es,r))) (LENGTH es))`
                 by (rw [LIST_REL_EL_EQN] >>
                     rw [v_rel_cases] >>
                     qexists_tac `n` >>
                     rw []) >>
  fs [Once contains_App_SOME_EXISTS] >>
  fs [EVERY_MAP, EVERY_EL] >>
  first_x_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  rw [] >>
  imp_res_tac renumber_code_locs_list_els >>
  fs [] >>
  pop_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  rw [EL_MAP] >>
  qexists_tac `m` >>
  simp [DROP_REVERSE, TAKE_REVERSE] >>
  `q' - LENGTH argenv' ≤ LENGTH args` by decide_tac >>
  rw [] >>
  metis_tac [EVERY2_APPEND, list_rel_lastn, LENGTH_LASTN, LENGTH_GENLIST, EVERY2_LENGTH, list_rel_butlastn]);

val helper = Q.prove (
  `SND ((λ(n',x'). (n',[x'])) x) = [SND x]`,
  Cases_on `x` >> fs []);

val list_to_v = prove(
  ``∀l1 l2. LIST_REL v_rel l1 l2 ⇒
    v_rel (list_to_v l1) (list_to_v l2)``,
  Induct >> simp[list_to_v_def,v_rel_simp] >>
  rw[PULL_EXISTS,list_to_v_def])

val v_rel_Boolv_mono = prove(
  ``(x ⇔ y) ⇒ (v_rel (Boolv x) (Boolv y))``,
  Cases_on`x`>>simp[Boolv_def,v_rel_simp])

val v_to_list = prove(
  ``∀x y. v_rel x y ⇒
          OPTREL (LIST_REL v_rel) (v_to_list x) (v_to_list y)``,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_rel_simp,v_to_list_def,PULL_EXISTS] >>
  rw[] >> TRY(rw[optionTheory.OPTREL_def]>>NO_TAC) >>
  first_x_assum(fn th => first_x_assum(STRIP_ASSUME_TAC o MATCH_MP th)) >>
  fs[optionTheory.OPTREL_def])

val do_eq = prove(
  ``∀x1 y1. v_rel x1 y1 ⇒
      ∀x2 y2. v_rel x2 y2 ⇒ (do_eq x1 x2 = do_eq y1 y2)``,
  ho_match_mp_tac v_rel_ind >> rw[] >>
  Cases_on`x2`>>fs[v_rel_simp]>>TRY(fs[do_eq_def]>>NO_TAC)>> rw[] >>
  simp[do_eq_def] >>
  imp_res_tac LIST_REL_LENGTH >> rw[] >>
  match_mp_tac do_eq_list_rel >> rw[] >>
  fs[LIST_REL_EL_EQN,EL_ZIP])

val do_app = prove(
  ``state_rel s1 s2 ∧
    LIST_REL v_rel x1 x2 ⇒
    (∀err.
      do_app op x1 s1 = (Rerr err) ⇒
      do_app op x2 s2 = (Rerr err)) ∧
    (∀v1 w1. do_app op x1 s1 = Rval(v1,w1) ⇒
             ∃v2 w2. do_app op x2 s2 = Rval(v2,w2) ∧
                     v_rel v1 v2 ∧ state_rel w1 w2)``,
  strip_tac >>
  simp[do_app_def] >>
  Cases_on`op`>>simp[v_rel_simp]>>
  Cases_on`x1`>>fs[v_rel_simp] >>
  rpt BasicProvers.VAR_EQ_TAC
  >- (
    simp[get_global_def] >>
    imp_res_tac state_rel_globals >>
    every_case_tac >> fs[LIST_REL_EL_EQN,OPTREL_def] >>
    res_tac >> fs[] >> rw[] >> rfs[] )
  >- (
    simp[get_global_def] >>
    imp_res_tac state_rel_globals >>
    every_case_tac >> fs[LIST_REL_EL_EQN,OPTREL_def] >>
    res_tac >> fs[] >> rw[] >> rfs[] >>
    fs[state_rel_def] >>
    match_mp_tac EVERY2_LUPDATE_same >>
    simp[OPTREL_def])
  >- ( fs[state_rel_def] >> simp[OPTREL_def])
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t'` >> fs[v_rel_simp]>>
    rpt var_eq_tac >>
    rw[] >> simp[] >> fs[LIST_REL_EL_EQN] >> rfs[] )
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    fs[LIST_REL_EL_EQN] )
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    fs[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    every_case_tac >> fs[] >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[v_rel_simp]>>
    simp[LIST_REL_EL_EQN] )
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    fs[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    every_case_tac >> fs[] >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[v_rel_simp])
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t'` >> fs[v_rel_simp]>>
    rw[] >> simp[v_rel_simp] >>
    imp_res_tac state_rel_refs >- fs[fmap_rel_def] >>
    `FDOM s1.refs = FDOM s2.refs` by fs[fmap_rel_def] >>
    fs[state_rel_def,fmap_rel_OPTREL_FLOOKUP] >>
    fs[OPTREL_def,FLOOKUP_UPDATE] >>
    rw[] >> fs[] )
  >- (
    Cases_on`t` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t'` >> fs[v_rel_simp]>>
    rw[] >> simp[v_rel_simp] >>
    imp_res_tac state_rel_refs >- fs[fmap_rel_def] >>
    `FDOM s1.refs = FDOM s2.refs` by fs[fmap_rel_def] >>
    fs[state_rel_def,fmap_rel_OPTREL_FLOOKUP] >>
    fs[OPTREL_def,FLOOKUP_UPDATE] >>
    rw[] >> fs[] >>
    simp[LIST_REL_REPLICATE_same])
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t'` >> fs[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    rpt var_eq_tac >>
    fs[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    every_case_tac >> fs[] >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[v_rel_simp]>>
    metis_tac[])
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t'` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    rpt var_eq_tac >>
    imp_res_tac state_rel_refs >>
    fs[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    first_x_assum(qspec_then`n`mp_tac)>>rw[v_rel_simp]>>
    every_case_tac >> fs[] >> rw[] >> fs[] >> rw[] >> fs[] >>
    fs[state_rel_def,fmap_rel_OPTREL_FLOOKUP] >>
    simp[FLOOKUP_UPDATE] >> rw[] >>
    simp[OPTREL_def] )
  >- (
    Cases_on`t` >> fs[v_rel_simp]>>
    imp_res_tac v_to_list >>
    every_case_tac >> fs[OPTREL_def] >>
    simp[v_rel_simp] )
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    imp_res_tac list_to_v )
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    fs[LIST_REL_EL_EQN] )
  >- (
    Cases_on`t` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp])
  >- (
    fs[state_rel_def,fmap_rel_def,FAPPLY_FUPDATE_THM] >> rw[] )
  >- (
    fs[state_rel_def,fmap_rel_def,FAPPLY_FUPDATE_THM] >> rw[] )
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t'` >> fs[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    fs[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    first_x_assum(qspec_then`n`mp_tac)>>rw[v_rel_simp]>>
    every_case_tac >> fs[] >> rw[] >> fs[LIST_REL_EL_EQN] >> rfs[] >>
    first_x_assum match_mp_tac >> intLib.COOPER_TAC)
  >- (
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    Cases_on`h` >> fs[v_rel_simp]>>
    Cases_on`t'` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    fs[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    first_x_assum(qspec_then`n`mp_tac)>>rw[v_rel_simp]>>
    every_case_tac >> fs[] >> rw[] >> fs[LIST_REL_EL_EQN] >> rfs[] >>
    fs[state_rel_def,fmap_rel_OPTREL_FLOOKUP,OPTREL_def,FLOOKUP_UPDATE] >>
    rw[] >> match_mp_tac EVERY2_LUPDATE_same >>
    fs[] >> last_x_assum(qspec_then`k`mp_tac) >> simp[] )
  >- (
    Cases_on`y` >> fs[v_rel_simp]>>
    Cases_on`t` >> fs[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    fs[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    first_x_assum(qspec_then`n'`mp_tac)>>rw[v_rel_simp]>>
    every_case_tac >> fs[] >> rw[] >> fs[LIST_REL_EL_EQN] >> rfs[] >>
    rfs[state_rel_def] >>
    fs[fmap_rel_OPTREL_FLOOKUP,OPTREL_def,FLOOKUP_UPDATE] >>
    rw[] )
  >- (
    Cases_on`t`>>fs[v_rel_simp]>>
    Cases_on`t'`>>fs[v_rel_simp]>>
    imp_res_tac do_eq >> simp[] >>
    every_case_tac >> simp[v_rel_simp] )
  >> (
    Cases_on`h`>>fs[v_rel_simp]>>
    Cases_on`t`>>fs[v_rel_simp]>>
    Cases_on`h`>>fs[v_rel_simp]>>
    Cases_on`t'`>>fs[v_rel_simp] >>
    every_case_tac >> fs[v_rel_simp]));

(* compiler correctness *)

val lookup_vars_NONE_related_env = Q.store_thm(
  "lookup_vars_NONE_related_env",
  `LIST_REL v_rel e1 e2 ⇒
   (lookup_vars vs e1 = NONE ⇔ lookup_vars vs e2 = NONE)`,
  strip_tac >> `LENGTH e1 = LENGTH e2` by metis_tac[LIST_REL_LENGTH] >>
  metis_tac[lookup_vars_NONE]);

val renumber_code_locs_correct = Q.store_thm("renumber_code_locs_correct",
  `(!tmp xs env (s1:'ffi closSem$state) env' t1 res s2 n.
     tmp = (xs,env,s1) ∧
     (evaluate (xs,env,s1) = (res,s2)) ⇒
     ¬contains_App_SOME xs ∧
     LIST_REL v_rel env env' ∧
     state_rel s1 t1 ==>
     ?res' t2.
        (evaluate (SND(renumber_code_locs_list n xs),env',t1) = (res',t2)) /\
        result_rel (LIST_REL v_rel) v_rel res res' /\
        state_rel s2 t2) ∧
   (!loc f args (s:'ffi closSem$state) res s2 f' args' t1.
       evaluate_app loc f args s = (res,s2) ⇒
       v_rel f f' ∧
       loc = NONE ∧
       LIST_REL v_rel args args' ∧
       state_rel s t1
       ⇒
       ?res' t2.
          (evaluate_app loc f' args' t1 = (res',t2)) /\
          result_rel (LIST_REL v_rel) v_rel res res' /\
          state_rel s2 t2)`,
  ho_match_mp_tac evaluate_ind \\ rw []
  THEN1 (* NIL *)
   (fs [renumber_code_locs_def,evaluate_def]
    \\ SRW_TAC [] [])
  THEN1 (* CONS *)
   (simp [renumber_code_locs_def,evaluate_def,UNCURRY] >>
    tac >> fs[] >> rw[] >>
    tac >> fs[] >> rw[] >>
    tac >> fs[] >> rw[] >>
    fs[evaluate_def]
    \\ `?r1 s1. evaluate ([x],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs []
    \\ fs[renumber_code_locs_def,LET_THM,contains_App_SOME_def] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [] >> rw[] >>
    `?r2 s2. evaluate (y::xs,env,s1) = (r2,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r2` \\ fs [] >> rw[] >>
    imp_res_tac evaluate_SING >> fs[])
  THEN1 (* Var *)
   (rw[renumber_code_locs_def] >>
    fs[LIST_REL_EL_EQN] >>
    fs[evaluate_def] >> rw[] >> fs[] >> rw[])
  THEN1 (* If *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY] >>
    tac >> fs[] >> rw[] >>
    tac >> fs[] >> rw[] >>
    tac >> fs[] >> rw[] >>
    fs[evaluate_def,contains_App_SOME_def] >>
    `?r1 s1. evaluate ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [] >> rw[] >> fs[] >>
    imp_res_tac evaluate_SING >> fs[] >> rw[] >> fs[v_rel_simp] >> rw[] >>
    TRY (
      first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
      disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
      NO_TAC) >>
    TRY (
      first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
      disch_then(fn th => first_x_assum(qspec_then`q'`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
      NO_TAC) >>
    qpat_assum`X = (res,Y)`mp_tac >>
    rw[] >> fs[v_rel_simp])
  THEN1 (* Let *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY] >>
    tac >> fs[] >> rw[] >>
    fs[evaluate_def,contains_App_SOME_def] >>
    `?r1 s1. evaluate (xs,env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [] >> rw[] >> fs[] >>
    first_x_assum MATCH_MP_TAC >> rw[] >>
    MATCH_MP_TAC EVERY2_APPEND_suff >> rw[] )
  THEN1 (* Raise *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s1. evaluate ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[evaluate_def,contains_App_SOME_def] >>
    tac >> fs[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [] >> rw[] >> fs[] >>
    imp_res_tac evaluate_SING >> fs[])
  THEN1 (* Handle *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[evaluate_def,contains_App_SOME_def] >>
    tac >> fs[] >> rw[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [] >> rw[] >> fs[] >>
    Cases_on`e`>>fs[] >> rw[])
  THEN1 (* Op *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s2. evaluate (xs,env,s) = (r1,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[evaluate_def,contains_App_SOME_def] >>
    tac >> fs[] >> rw[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [] >> rw[] >> fs[] >>
    imp_res_tac EVERY2_REVERSE >> pop_assum kall_tac >>
    first_assum(fn th1 => first_assum(fn th2 => mp_tac (MATCH_MP do_app (CONJ th1 th2)))) >>
    strip_tac >>
    last_x_assum mp_tac >>
    BasicProvers.CASE_TAC >> TRY(Cases_on`a'`) >> rw[] >> simp[] >>
    imp_res_tac do_app_err >>
    reverse(Cases_on`op=Equal`) >> fs[] >>
    fs[do_app_def] >>
    every_case_tac >> fs[] >> rw[v_rel_simp])
  THEN1 (* Fn *)
   (fs [renumber_code_locs_def,evaluate_def,LET_THM,UNCURRY] >>
    `t1.restrict_envs = s.restrict_envs` by fs[state_rel_def] >>
    fs[clos_env_def] >> rw[] >> fs[contains_App_SOME_def] >> rw[v_rel_simp] >>
    TRY (fs [] >> PROVE_TAC[]) >>
    last_x_assum mp_tac >>
    BasicProvers.CASE_TAC >- (
      rw[] >> simp[v_rel_simp] >> METIS_TAC[] ) >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac lookup_vars_NONE >>
      BasicProvers.CASE_TAC >> rw[] >> rw[] >>
      imp_res_tac lookup_vars_SOME >>
      imp_res_tac lookup_vars_MEM >>
      fs[LIST_REL_EL_EQN,MEM_EL] >> rw[] >> rfs[] >>
      res_tac >> DECIDE_TAC ) >>
    rw[] >>
    imp_res_tac lookup_vars_SOME >>
    imp_res_tac lookup_vars_MEM >>
    BasicProvers.CASE_TAC >> rw[] >> rw[v_rel_simp] >- (
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
   (cheat (* fs[renumber_code_locs_def,evaluate_def,LET_THM,UNCURRY] >>
    `t1.restrict_envs = s.restrict_envs` by fs[state_rel_def] >>
    Cases_on`renumber_code_locs_list n (MAP SND fns)`>>fs[]>>
    imp_res_tac renumber_code_locs_list_length >>
    fs [EVERY_ZIP, MAP_ZIP] >>
    reverse (rw []) >>
    full_simp_tac (bool_ss) []
    >- (rw [] >> rw [])
    >- rw [] >>
    fs [combinTheory.o_DEF, EVERY_MAP, LAMBDA_PROD] >>
    fs[build_recc_def,clos_env_def] >> reverse(rw[]) >> fs[contains_App_SOME_def] >> rw[] >- (
      Cases_on `namesopt` >> fs[]
      >- (first_x_assum MATCH_MP_TAC >> rw[] >>
          MATCH_MP_TAC EVERY2_APPEND_suff >> rw[] >>
          imp_res_tac renumber_code_locs_list_length >>
          rw[LIST_REL_EL_EQN,EL_GENLIST] >>
          rw[v_rel_simp] >>
          METIS_TAC[SND])
      >- (qcase_tac `lookup_vars vv env` >> Cases_on `lookup_vars vv env` >>
          fs[]
          >- (qcase_tac `LIST_REL v_rel env1 env2` >>
              `lookup_vars vv env2 = NONE`
                by metis_tac[lookup_vars_NONE_related_env] >>
              simp[] >> rw[])

     ) >>
    last_x_assum mp_tac >>
    BasicProvers.CASE_TAC >> fs[] >> rw[] >- (
      imp_res_tac lookup_vars_NONE >>
      BasicProvers.CASE_TAC >> rw[] >> rw[] >>
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
      rw[v_rel_simp,LIST_REL_EL_EQN] >>
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
    DECIDE_TAC*) )
  THEN1 (* App *)
   (fs [renumber_code_locs_def,evaluate_def,LET_THM,UNCURRY] >>
    `LENGTH (SND (renumber_code_locs_list (FST (renumber_code_locs n x1)) args)) = LENGTH args`
            by (Cases_on `renumber_code_locs n x1` >>
                fs [] >>
                Cases_on `renumber_code_locs_list q args` >>
                fs [] >>
                metis_tac [renumber_code_locs_list_length]) >>
    rw [] >> fs [] >> rw [] >>
    tac >> fs[] >> rw[] >>
    first_assum(split_pair_case_tac o lhs o concl) >>
    fs[contains_App_SOME_def] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `v2` \\ fs [] >> rw[] >> fs[] >>
    first_assum(split_pair_case_tac o lhs o concl) >> fs[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `v2'` \\ fs [] >> rw[] >> fs[] >>
    first_x_assum match_mp_tac >>
    rw [] >>
    imp_res_tac evaluate_SING >> fs[] >> rw[])
  THEN1 (* Tick *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s1. evaluate ([x],env,dec_clock 1 s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs [] >>
    fs[evaluate_def,contains_App_SOME_def] >>
    tac >> fs[] >>
    `t1.clock = s.clock` by fs[state_rel_def] >>
    rw[] >> fs[] >> rw[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(qspecl_then[`dec_clock 1 t1`,`n`]mp_tac) >>
    discharge_hyps >- fs[state_rel_def,dec_clock_def] >> rw[])
  THEN1 (* Call *)
   (fs [renumber_code_locs_def,LET_THM,UNCURRY] >>
    fs[evaluate_def,contains_App_SOME_def] >>
    `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rfs[] >>
    Cases_on `r1` \\ fs [] >> rw[] >> fs[] >>
    fs[find_code_def] >>
    `FDOM s2'.code = FDOM t2.code` by fs[state_rel_def,fmap_rel_def] >>
    BasicProvers.CASE_TAC >> fs[] >- (
      fs[FLOOKUP_DEF] >>
      rw[] ) >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac LIST_REL_LENGTH >>
    `s2'.clock = t2.clock` by fs[state_rel_def] >>
    `∃x. FLOOKUP s2'.code dest = SOME x ∧ code_rel x (q,r)` by (
      fs[state_rel_def,fmap_rel_def,FLOOKUP_DEF] >>
      METIS_TAC[] ) >>
    Cases_on`x`>>fs[code_rel_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    BasicProvers.CASE_TAC >> fs[] >- (
      rw[] >> fs[] >> rw[] >> rfs[] >>
      first_x_assum MATCH_MP_TAC >>
      simp[] >>
      fs[state_rel_def,dec_clock_def] ) >>
    rw[])
  THEN1 (* App empty *)
   (fs [evaluate_def] >> rw [])
  THEN1 (* Real App *)
   (fs [evaluate_def] >>
    Cases_on `dest_closure NONE f (v41::v42)` >>
    fs [] >>
    rw []
    >- (imp_res_tac dest_closure_v_rel_none >>
        rw []) >>
    `s.clock = t1.clock` by fs[state_rel_def] >>
    imp_res_tac EVERY2_LENGTH >>
    Cases_on `x` >>
    fs []
    >- (`?c'. v_rel v c' ∧ dest_closure NONE f' (y::ys) = SOME (Partial_app c')`
                 by metis_tac [LIST_REL_def, dest_closure_v_rel_partial] >>
        rw [] >>
        fs [] >>
        rw [ dec_clock_def] >>
        metis_tac [state_rel_clock])
    >- (`∃args1' args2' n.
           dest_closure NONE f' (y::ys) =
           SOME (Full_app (SND (renumber_code_locs n e)) args1' args2') ∧
           ~contains_App_SOME [e] ∧
           LIST_REL v_rel l args1' ∧ LIST_REL v_rel l0 args2'`
                     by (
               imp_res_tac dest_closure_v_rel_full >>
               fs[PULL_EXISTS] >> prove_tac[]) >>
        simp [] >>
        imp_res_tac EVERY2_LENGTH >>
        fs [] >>
        rw [] >>
        fs []
        >- metis_tac [state_rel_clock] >>
        Cases_on `evaluate ([e],l,dec_clock (SUC (LENGTH ys) − LENGTH args2') s)` >>
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
        fs [] >> rw[])));

val renumber_code_locs_every_Fn_SOME = Q.store_thm("renumber_code_locs_every_Fn_SOME",
  `(∀n es. every_Fn_SOME (SND (renumber_code_locs_list n es))) ∧
   (∀n e. every_Fn_SOME [SND (renumber_code_locs n e)])`,
  ho_match_mp_tac renumber_code_locs_ind >>
  rw[renumber_code_locs_def] >> rw[every_Fn_SOME_def] >> fs[] >>
  fs[Once every_Fn_SOME_EVERY] >>
  imp_res_tac renumber_code_locs_list_length >>
  fs[EVERY_MAP,ZIP_MAP] >>
  fs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,MEM_EL]);

val _ = export_theory()
