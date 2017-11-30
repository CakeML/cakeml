open preamble closLangTheory clos_numberTheory closSemTheory closPropsTheory;

val _ = new_theory"clos_numberProof";

(* properties of renumber_code_locs *)
val option_case_eq = Q.prove(
  `(option_CASE opt n s = v) ⇔
      (opt = NONE ∧ v = n) ∨ (∃x. opt = SOME x ∧ v = s x)`,
  Cases_on `opt` >> simp[EQ_SYM_EQ]);


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

val renumber_code_locs_inc = Q.store_thm("renumber_code_locs_inc",
  `(∀n es. n ≤ FST (renumber_code_locs_list n es)) ∧
    (∀n e. n ≤ FST (renumber_code_locs n e))`,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def] >> srw_tac[][] >>
  tac >> full_simp_tac(srw_ss())[] >>
  tac >> full_simp_tac(srw_ss())[] >>
  tac >> full_simp_tac(srw_ss())[] >> simp[] >>
  pairarg_tac \\ fs[] \\ pairarg_tac \\ fs[]);

val renumber_code_locs_imp_inc = Q.store_thm("renumber_code_locs_imp_inc",
  `(renumber_code_locs_list n es = (m,vs) ⇒ n ≤ m) ∧
    (renumber_code_locs n e = (z,v) ⇒ n ≤ z)`,
  metis_tac[pairTheory.pair_CASES,pairTheory.FST,renumber_code_locs_inc])

val renumber_code_locs_list_length = Q.prove(
  `∀ls n x y. renumber_code_locs_list n ls = (x,y) ⇒ LENGTH y = LENGTH ls`,
  Induct >> simp[renumber_code_locs_def,LENGTH_NIL] >> srw_tac[][] >>
  Cases_on`renumber_code_locs n h`>>full_simp_tac(srw_ss())[]>>
  Cases_on`renumber_code_locs_list q ls`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
  res_tac)

val renumber_code_locs_distinct_lemma = Q.prove(
  `(∀n es. SORTED $< (code_locs (SND (renumber_code_locs_list n es))) ∧
            EVERY ($<= n) (code_locs (SND (renumber_code_locs_list n es))) ∧
            EVERY ($> (FST (renumber_code_locs_list n es))) (code_locs (SND (renumber_code_locs_list n es)))) ∧
    (∀n e. SORTED $< (code_locs [SND (renumber_code_locs n e)]) ∧
            EVERY ($<= n) (code_locs [SND (renumber_code_locs n e)]) ∧
            EVERY ($> (FST (renumber_code_locs n e))) (code_locs [SND (renumber_code_locs n e)]))`,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def,code_locs_def,pairTheory.UNCURRY] >>
  srw_tac[][] >> rpt (CHANGED_TAC tac >> full_simp_tac(srw_ss())[]) >> srw_tac[][] >>
  imp_res_tac renumber_code_locs_imp_inc >> simp[] >>
  simp[EVERY_GENLIST] >>
  TRY (
    CHANGED_TAC(simp[EVERY_MEM]) >>
    full_simp_tac(srw_ss())[EVERY_MEM] >>
    srw_tac[][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC ) >>
  TRY (
    CHANGED_TAC(simp[EVERY_MEM]) >>
    full_simp_tac(srw_ss())[EVERY_MEM] >>
    simp[Once code_locs_cons] >>
    srw_tac[][] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC ) >>
  rpt(match_mp_tac sortingTheory.SORTED_APPEND >> simp[] >> TRY conj_tac) >>
  TRY (
    srw_tac[][] >> full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC) >>
  TRY (
    simp[Once code_locs_cons] >>
    match_mp_tac sortingTheory.SORTED_APPEND >> simp[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC ) >>
  TRY (
    Cases_on`renumber_code_locs (n+2) e`>>full_simp_tac(srw_ss())[] >>
    simp[less_sorted_eq] >>
    imp_res_tac renumber_code_locs_imp_inc >>
    srw_tac[][] >> full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    NO_TAC) >>
  fs[times_add_o,GSYM MAP_GENLIST,
     MATCH_MP sorted_map transitive_LESS,
     SORTED_inv_image_LESS_PLUS,
     SORTED_GENLIST_TIMES] >>
  Cases_on `renumber_code_locs_list n (MAP SND fns)` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on`renumber_code_locs (q+2 * LENGTH fns) e`>>full_simp_tac(srw_ss())[] >>
  rpt(CHANGED_TAC tac >> full_simp_tac(srw_ss())[])>>
  simp[MEM_GENLIST,MEM_MAP,PULL_EXISTS] >>
  imp_res_tac renumber_code_locs_imp_inc >>
  imp_res_tac renumber_code_locs_list_length >>
  srw_tac[][] >> full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][MAP_ZIP] >>
  rev_full_simp_tac(srw_ss())[MAP_ZIP] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> fsrw_tac[ARITH_ss][MAP_ZIP]);

val renumber_code_locs_distinct = Q.store_thm("renumber_code_locs_distinct",
  `∀n e. ALL_DISTINCT (code_locs [SND (renumber_code_locs n e)]) ∧
          EVERY ($<= n) (code_locs [SND (renumber_code_locs n e)]) ∧
          EVERY ($> (FST (renumber_code_locs n e))) (code_locs [SND (renumber_code_locs n e)])`,
  srw_tac[][] >>
  qspecl_then[`n`,`e`]strip_assume_tac (CONJUNCT2 renumber_code_locs_distinct_lemma) >> simp[] >>
  match_mp_tac (MP_CANON (GEN_ALL SORTED_ALL_DISTINCT)) >>
  qexists_tac`$<` >> simp[] >>
  simp[relationTheory.irreflexive_def])

val renumber_code_locs_list_els = Q.prove(
  `∀ls ls' n n'. renumber_code_locs_list n ls = (n',ls') ⇒
      ∀x. x < LENGTH ls ⇒
        ∃m. EL x ls' = SND (renumber_code_locs m (EL x ls))`,
  Induct >> simp[renumber_code_locs_def] >>
  simp[UNCURRY] >> srw_tac[][] >>
  Cases_on`x`>>full_simp_tac(srw_ss())[] >- METIS_TAC[] >>
  first_x_assum (MATCH_MP_TAC o MP_CANON) >>
  simp[] >>
  METIS_TAC[pair_CASES,SND])

(* value relation *)

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln `
  (v_rel max_app (Number j) (Number j))
  /\
  (v_rel max_app (Word64 w) (Word64 w))
  /\
  (EVERY2 (v_rel max_app) (xs:closSem$v list) (ys:closSem$v list) ==>
   v_rel max_app (Block t xs) (Block t ys))
  /\
  (v_rel max_app (ByteVector ws) (ByteVector ws))
  /\
  (v_rel max_app (RefPtr r1) (RefPtr r1))
  /\
  (LIST_REL (v_rel max_app) env env' ∧
   LIST_REL (v_rel max_app) argenv argenv' ∧
   ¬contains_App_SOME max_app [c] ∧
   c' = SND (renumber_code_locs n c) ==>
   v_rel max_app (Closure p argenv env num_args c) (Closure p' argenv' env' num_args c'))
  /\
  (LIST_REL (v_rel max_app) env env' ∧
   LIST_REL (v_rel max_app) argenv argenv' ∧
   ¬contains_App_SOME max_app (MAP SND es) ∧
   es' = ZIP (MAP FST es, SND (renumber_code_locs_list n (MAP SND es)))
   ⇒
   v_rel max_app (Recclosure p argenv env es k) (Recclosure p' argenv' env' es' k))`

val code_rel_def = Define`
  code_rel max_app (a1,e1) (a2,e2) ⇔
    (a1 = a2) ∧ ¬contains_App_SOME max_app [e1] ∧
    ∃n. e2 = SND (renumber_code_locs n e1)`

val state_rel_def = Define `
  state_rel (s:'ffi closSem$state) (t:'ffi closSem$state) <=>
    (s.clock = t.clock) /\ (s.ffi = t.ffi) /\ (t.max_app = s.max_app) /\
    fmap_rel (ref_rel (v_rel s.max_app)) s.refs t.refs ∧
    EVERY2 (OPTREL (v_rel s.max_app)) s.globals t.globals /\
    fmap_rel (code_rel s.max_app) s.code t.code`

val state_rel_max_app = Q.prove (
  `!s t. state_rel s t ⇒ s.max_app = t.max_app`,
   srw_tac[][state_rel_def]);

val state_rel_clock = Q.prove (
  `!s t. state_rel s t ⇒ state_rel (s with clock := x) (t with clock := x)`,
   srw_tac[][state_rel_def] \\ rfs[]);

val state_rel_globals = Q.prove(
  `state_rel s t ⇒
    LIST_REL (OPTREL (v_rel s.max_app)) s.globals t.globals`,
  srw_tac[][state_rel_def])

val state_rel_refs = Q.prove(
  `state_rel s t ⇒
    fmap_rel (ref_rel (v_rel t.max_app)) s.refs t.refs`,
  srw_tac[][state_rel_def])

val v_rel_simp = let
  val f = SIMP_CONV (srw_ss()) [Once v_rel_cases]
  in map f [``v_rel max_app (Number x) y``,
            ``v_rel max_app (Word64 n) y``,
            ``v_rel max_app (Block n l) y``,
            ``v_rel max_app (ByteVector ws) y``,
            ``v_rel max_app (RefPtr x) y``,
            ``v_rel max_app (Closure n a l narg x) y``,
            ``v_rel max_app (Recclosure x1 x2 x3 x4 x5) y``,
            ``v_rel max_app y (Number x)``,
            ``v_rel max_app y (Block n l)``,
            ``v_rel max_app y (ByteVector ws)``,
            ``v_rel max_app y (RefPtr x)``,
            ``v_rel max_app y (Closure n a l narg x)``,
            ``v_rel max_app y (Recclosure x1 x2 x3 x4 x5)``] |> LIST_CONJ end
  |> curry save_thm"v_rel_simp"

val v_rel_Boolv = Q.store_thm("v_rel_Boolv[simp]",
  `(v_rel max_app x (Boolv b) ⇔ (x = Boolv b)) ∧
    (v_rel max_app (Boolv b) x ⇔ (x = Boolv b))`,
  Cases_on`b`>>srw_tac[][Boolv_def,Once v_rel_cases] >>
  srw_tac[][Once v_rel_cases])

val v_rel_Unit = Q.store_thm("v_rel_Unit[simp]",
  `(v_rel max_app x Unit ⇔ (x = Unit)) ∧
    (v_rel max_app Unit x ⇔ (x = Unit))`,
  EVAL_TAC >> simp[v_rel_simp])

(* semantic functions respect relation *)

val dest_closure_v_rel_none = Q.prove (
  `!f args f' args'.
    v_rel max_app f f' ∧
    LIST_REL (v_rel max_app) args args' ∧
    dest_closure max_app NONE f args = NONE
    ⇒
    dest_closure max_app NONE f' args' = NONE`,
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[dest_closure_def, v_rel_cases] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[LET_THM, check_loc_def] >>
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  srw_tac[][] >>
  TRY decide_tac >>
  Cases_on `EL k es` >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `renumber_code_locs_list n (MAP SND es)` >>
  imp_res_tac renumber_code_locs_list_length >>
  srw_tac[][] >>
  Cases_on `EL k (ZIP (MAP FST es,r'))` >>
  srw_tac[][] >>
  CCONTR_TAC >>
  full_simp_tac(srw_ss())[] >>
  `k < LENGTH es` by decide_tac >>
  `LENGTH (MAP FST es) = LENGTH r'` by metis_tac [LENGTH_MAP] >>
  full_simp_tac(srw_ss())[EL_ZIP, EL_MAP] >>
  srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[]);

val dest_closure_v_rel_partial = Q.prove (
  `!c f args f' args'.
    v_rel max_app f f' ∧
    LIST_REL (v_rel max_app) args args' ∧
    dest_closure max_app NONE f args = SOME (Partial_app c)
    ⇒
    ?c'.
      dest_closure max_app NONE f' args' = SOME (Partial_app c') ∧
      v_rel max_app c c'`,
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[dest_closure_def, v_rel_cases] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[LET_THM, check_loc_def] >>
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  srw_tac[][] >>
  TRY decide_tac
  >- metis_tac [EVERY2_APPEND] >>
  Cases_on `EL k es` >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `renumber_code_locs_list n (MAP SND es)` >>
  imp_res_tac renumber_code_locs_list_length >>
  srw_tac[][] >>
  Cases_on `EL k (ZIP (MAP FST es,r'))` >>
  srw_tac[][] >>
  CCONTR_TAC >>
  full_simp_tac(srw_ss())[] >>
  `k < LENGTH es` by decide_tac >>
  `LENGTH (MAP FST es) = LENGTH r'` by metis_tac [LENGTH_MAP] >>
  full_simp_tac(srw_ss())[EL_ZIP, EL_MAP] >>
  srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[] >>
  metis_tac [SND, EVERY2_APPEND]);

val dest_closure_v_rel_full = Q.prove (
  `!c f args f' args' args1 args2.
    v_rel max_app f f' ∧
    LIST_REL (v_rel max_app) args args' ∧
    dest_closure max_app NONE f args = SOME (Full_app exp args1 args2)
    ⇒
    ?args1' args2' n.
      dest_closure max_app NONE f' args' = SOME (Full_app (SND (renumber_code_locs n exp)) args1' args2') ∧
      LIST_REL (v_rel max_app) args1 args1' ∧
      LIST_REL (v_rel max_app) args2 args2' ∧
      ~contains_App_SOME max_app [exp]`,
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[dest_closure_def, v_rel_cases] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[LET_THM, check_loc_def] >>
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  srw_tac[][] >>
  TRY (qexists_tac `n`) >>
  TRY decide_tac >>
  srw_tac[][] >>
  TRY decide_tac >>
  TRY (`n' - LENGTH argenv' ≤ LENGTH args'` by decide_tac) >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][DROP_REVERSE, TAKE_REVERSE] >>
  TRY (`n' - LENGTH argenv' ≤ LENGTH args'` by decide_tac)
  >- metis_tac [list_rel_butlastn, list_rel_lastn, EVERY2_APPEND]
  >- metis_tac [list_rel_butlastn, list_rel_lastn, EVERY2_APPEND] >>
  Cases_on `renumber_code_locs_list n (MAP SND es)` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `EL k es` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `LENGTH args' + LENGTH argenv' < q'` >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  imp_res_tac renumber_code_locs_list_length >>
  srw_tac[][] >>
  `k < LENGTH es` by decide_tac >>
  full_simp_tac(srw_ss())[EL_ZIP, EL_MAP] >>
  `LIST_REL (v_rel max_app) (GENLIST (Recclosure o' [] env es) (LENGTH es))
                    (GENLIST (Recclosure p' [] env' (ZIP (MAP FST es,r))) (LENGTH es))`
                 by (srw_tac[][LIST_REL_EL_EQN] >>
                     srw_tac[][v_rel_cases] >>
                     qexists_tac `n` >>
                     srw_tac[][]) >>
  full_simp_tac(srw_ss())[Once contains_App_SOME_EXISTS] >>
  full_simp_tac(srw_ss())[EVERY_MAP, EVERY_EL] >>
  first_x_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  srw_tac[][] >>
  imp_res_tac renumber_code_locs_list_els >>
  full_simp_tac(srw_ss())[] >>
  pop_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  srw_tac[][EL_MAP] >>
  qexists_tac `m` >>
  simp [DROP_REVERSE, TAKE_REVERSE] >>
  `q' - LENGTH argenv' ≤ LENGTH args` by decide_tac >>
  srw_tac[][] >>
  metis_tac [EVERY2_APPEND, list_rel_lastn, LENGTH_LASTN, LENGTH_GENLIST, EVERY2_LENGTH, list_rel_butlastn]);

val helper = Q.prove (
  `SND ((λ(n',x'). (n',[x'])) x) = [SND x]`,
  Cases_on `x` >> full_simp_tac(srw_ss())[]);

val v_rel_Boolv_mono = Q.prove(
  `(x ⇔ y) ⇒ (v_rel max_app (Boolv x) (Boolv y))`,
  Cases_on`x`>>simp[Boolv_def,v_rel_simp])

val v_to_list = Q.prove(
  `∀x y. v_rel max_app x y ⇒
          OPTREL (LIST_REL (v_rel max_app)) (v_to_list x) (v_to_list y)`,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_rel_simp,v_to_list_def,PULL_EXISTS] >>
  srw_tac[][] >> TRY(srw_tac[][optionTheory.OPTREL_def]>>NO_TAC) >>
  first_x_assum(fn th => first_x_assum(STRIP_ASSUME_TAC o MATCH_MP th)) >>
  full_simp_tac(srw_ss())[optionTheory.OPTREL_def])

val do_eq = Q.prove(
  `∀x1 y1. v_rel max_app x1 y1 ⇒
      ∀x2 y2. v_rel max_app x2 y2 ⇒ (do_eq x1 x2 = do_eq y1 y2)`,
  ho_match_mp_tac v_rel_ind >> srw_tac[][] >>
  Cases_on`x2`>>full_simp_tac(srw_ss())[v_rel_simp]>>TRY(full_simp_tac(srw_ss())[do_eq_def]>>NO_TAC)>> srw_tac[][] >>
  simp[do_eq_def] >>
  imp_res_tac LIST_REL_LENGTH >> srw_tac[][] >>
  match_mp_tac do_eq_list_rel >> srw_tac[][] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN,EL_ZIP])

val do_app = Q.prove(
  `state_rel s1 s2 ∧
    LIST_REL (v_rel s1.max_app) x1 x2 ⇒
    (∀err.
      do_app op x1 s1 = (Rerr err) ⇒
      do_app op x2 s2 = (Rerr err)) ∧
    (∀v1 w1. do_app op x1 s1 = Rval(v1,w1) ⇒
             ∃v2 w2. do_app op x2 s2 = Rval(v2,w2) ∧
                     v_rel s1.max_app v1 v2 ∧ state_rel w1 w2)`,
  strip_tac >>
  Cases_on `?tag. op = ConsExtend tag`
  >- (
    rw [do_app_cases_val]
    >- (
      Cases_on `err` >>
      fs [do_app_cases_err] >>
      fs [] >>
      Cases_on `a` >>
      fs [do_app_cases_timeout] >>
      fs [] >>
      pop_assum mp_tac >>
      simp [Once do_app_cases_type_error] >>
      rw [] >>
      rw [do_app_def] >>
      fs [v_rel_cases] >>
      rw [] >>
      fs [] >>
      rw [] >>
      imp_res_tac LIST_REL_LENGTH >>
      intLib.ARITH_TAC)
    >- (
      fs [] >>
      rw [] >>
      fs [v_rel_cases] >>
      rw [PULL_EXISTS] >>
      imp_res_tac LIST_REL_LENGTH >>
      metis_tac [EVERY2_APPEND_suff, EVERY2_TAKE, EVERY2_DROP])) >>
  simp[do_app_def] >>
  Cases_on`op`>>simp[v_rel_simp]>>
  Cases_on`x1`>>full_simp_tac(srw_ss())[v_rel_simp] >>
  rpt BasicProvers.VAR_EQ_TAC
  (* GetGlobal *)
  >- (
    simp[get_global_def] >>
    imp_res_tac state_rel_globals >>
    every_case_tac >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN,OPTREL_def] >>
    res_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] )
  (* SetGlobal *)
  >- (
    simp[get_global_def] >>
    imp_res_tac state_rel_globals >>
    every_case_tac >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN,OPTREL_def] >>
    res_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    match_mp_tac EVERY2_LUPDATE_same >>
    simp[OPTREL_def])
  (* AllocGlobal *)
  >- ( full_simp_tac(srw_ss())[state_rel_def] >> simp[OPTREL_def])
  (* El *)
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t'` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    rpt var_eq_tac >>
    srw_tac[][] >> simp[] >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> rev_full_simp_tac(srw_ss())[] )
  (* LengthBlock *)
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] )
  (* LengthArray *)
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[v_rel_simp]>>
    simp[LIST_REL_EL_EQN] )
  (* LengthByteArray *)
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[v_rel_simp])
  (* AllocByteArray *)
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t'` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    srw_tac[][] >> simp[v_rel_simp] >>
    imp_res_tac state_rel_refs >- full_simp_tac(srw_ss())[fmap_rel_def] >>
    `FDOM s1.refs = FDOM s2.refs` by full_simp_tac(srw_ss())[fmap_rel_def] >>
    full_simp_tac(srw_ss())[state_rel_def,fmap_rel_OPTREL_FLOOKUP] >>
    full_simp_tac(srw_ss())[OPTREL_def,FLOOKUP_UPDATE] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] )
  (* AllocArray *)
  >- (
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t'` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    srw_tac[][] >> simp[v_rel_simp] >>
    imp_res_tac state_rel_refs >- full_simp_tac(srw_ss())[fmap_rel_def] >>
    `FDOM s1.refs = FDOM s2.refs` by full_simp_tac(srw_ss())[fmap_rel_def] >>
    full_simp_tac(srw_ss())[state_rel_def,fmap_rel_OPTREL_FLOOKUP] >>
    full_simp_tac(srw_ss())[OPTREL_def,FLOOKUP_UPDATE] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    simp[LIST_REL_REPLICATE_same])
  (* SubByteArray *)
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t'` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    rpt var_eq_tac >>
    full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[v_rel_simp]>>
    metis_tac[])
  (* UpdateByteArray *)
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t'` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    rpt var_eq_tac >>
    imp_res_tac state_rel_refs >>
    full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    first_x_assum(qspec_then`n`mp_tac)>>srw_tac[][v_rel_simp]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[state_rel_def,fmap_rel_OPTREL_FLOOKUP] >>
    simp[FLOOKUP_UPDATE] >> srw_tac[][] >>
    simp[OPTREL_def] )
  (* ConcatByteVec *)
  >- (
    Cases_on`t` \\ fs[]
    \\ rename1`v_rel _ v1 v2`
    \\ DEEP_INTRO_TAC some_intro \\ fs[PULL_EXISTS]
    \\ DEEP_INTRO_TAC some_intro \\ fs[PULL_EXISTS,v_rel_simp]
    \\ Cases_on`v_to_list v1` \\ fs[] \\ Cases_on`v_to_list v2` \\ fs[]
    \\ imp_res_tac v_to_list \\ fs[OPTREL_def] \\ fs[] \\ rveq
    \\ rename1`LIST_REL _ l1 l2`
    \\ reverse(Cases_on`∃ws. l1 = MAP ByteVector ws` \\ fs[])
    >- (
      spose_not_then strip_assume_tac
      \\ fs[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP,v_rel_simp]
      \\ metis_tac[EL_MAP,v_rel_simp] )
    \\ `l2 = MAP ByteVector ws`
    by (
      fs[LIST_REL_EL_EQN,LIST_EQ_REWRITE] \\
      metis_tac[EL_MAP,v_rel_simp] )
    \\ fs[]
    \\ rw[]
    \\ qexists_tac`ws` \\ rw[]
    \\ imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF])
  (* CopyByte *)
  >- (
    rw[] \\ fs[case_eq_thms,bool_case_eq] \\ rw[] \\ fs[v_rel_simp] \\
    imp_res_tac state_rel_refs \\
    imp_res_tac fmap_rel_FLOOKUP_imp \\ fs[] \\
    fs[state_rel_def,fmap_rel_FUPDATE_same])
  >- (
    Cases_on`t` >> fsrw_tac[][v_rel_simp]>>
    imp_res_tac v_to_list >>
    every_case_tac >> full_simp_tac(srw_ss())[OPTREL_def] >>
    simp[v_rel_simp] )
  (* FromListByte *)
  >- (
    every_case_tac \\ fs[v_rel_simp]
    \\ rpt(qpat_x_assum`$some _ = _`mp_tac)
    \\ rpt(DEEP_INTRO_TAC some_intro) \\ fs[] \\ rw[]
    \\ imp_res_tac v_to_list \\ rfs[OPTREL_def]
    \\ fs[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP] \\ rfs[EL_MAP,v_rel_simp]
    \\ fs[EVERY_MEM,EXISTS_MEM]
    \\ metis_tac[EL_MAP,o_THM,v_11,integerTheory.INT_INJ,v_rel_simp])
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] )
  >- ( every_case_tac \\ fs[v_rel_simp] \\ rw[] \\ fs[] )
  >- (
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_simp]>>
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_simp] >>
    imp_res_tac LIST_REL_LENGTH >> fs [] >>
    imp_res_tac state_rel_refs >>
    full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[v_rel_simp])
  >- ( every_case_tac \\ fs[v_rel_simp] \\ rw[] \\ fs[LIST_REL_EL_EQN] )
  >- (
    full_simp_tac(srw_ss())[state_rel_def,fmap_rel_def,FAPPLY_FUPDATE_THM] >> srw_tac[][] )
  >- (
    full_simp_tac(srw_ss())[state_rel_def,fmap_rel_def,FAPPLY_FUPDATE_THM] >> srw_tac[][] )
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t'` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    first_x_assum(qspec_then`n`mp_tac)>>srw_tac[][v_rel_simp]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac state_rel_max_app >> fs[] >>
    first_x_assum match_mp_tac >> intLib.COOPER_TAC)
  >- (
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`h` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t'` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t` >> full_simp_tac(srw_ss())[v_rel_simp]>>
    imp_res_tac state_rel_refs >>
    full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    first_x_assum(qspec_then`n`mp_tac)>>srw_tac[][v_rel_simp]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> rev_full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[state_rel_def,fmap_rel_OPTREL_FLOOKUP,OPTREL_def,FLOOKUP_UPDATE] >>
    srw_tac[][] >> match_mp_tac EVERY2_LUPDATE_same >>
    full_simp_tac(srw_ss())[] >> last_x_assum(qspec_then`k`mp_tac) >> simp[] )
  >- (
    Cases_on`y`\\fs[v_rel_simp]
    \\ Cases_on`t`\\fs[v_rel_simp]
    \\ Cases_on`h`\\fs[v_rel_simp]
    \\ rveq
    \\ imp_res_tac state_rel_refs
    \\ fs[fmap_rel_OPTREL_FLOOKUP]
    \\ first_x_assum(qspec_then`n`mp_tac)>>srw_tac[][v_rel_simp]
    \\ every_case_tac \\ fs[OPTREL_def]
    \\ rveq\\ fs[state_rel_def,fmap_rel_OPTREL_FLOOKUP,OPTREL_def,FLOOKUP_UPDATE]
    \\ rw[] \\ rfs[] \\ fs[v_rel_simp] \\ rename [`FLOOKUP _ k = _`]
    \\ rpt(first_x_assum(qspec_then `k` assume_tac))
    \\ rfs[] >> fs[] )
  >- (
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[v_rel_simp]>>
    imp_res_tac do_eq >> simp[] >>
    every_case_tac >> simp[v_rel_simp] )
  >> (
    TRY(Cases_on`w`)\\fs[]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_simp]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_simp]>>
    TRY(Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_simp])>>
    TRY(Cases_on`t'`>>full_simp_tac(srw_ss())[v_rel_simp]) >>
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_simp] >>
    imp_res_tac LIST_REL_LENGTH >> fs [] >>
    imp_res_tac state_rel_refs >>
    full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP,OPTREL_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`n`mp_tac)>>simp[v_rel_simp]>>
    simp[LIST_REL_EL_EQN] ));

(* compiler correctness *)

val lookup_vars_NONE_related_env = Q.store_thm(
  "lookup_vars_NONE_related_env",
  `LIST_REL (v_rel max_app) e1 e2 ⇒
   (lookup_vars vs e1 = NONE ⇔ lookup_vars vs e2 = NONE)`,
  strip_tac >> `LENGTH e1 = LENGTH e2` by metis_tac[LIST_REL_LENGTH] >>
  metis_tac[lookup_vars_NONE]);

val lookup_vars_SOME_related_env = Q.store_thm(
  "lookup_vars_SOME_related_env",
  `LIST_REL (v_rel max_app) e1 e2 ∧ lookup_vars vs e1 = SOME e1' ∧
   lookup_vars vs e2 = SOME e2' ⇒ LIST_REL (v_rel max_app) e1' e2'`,
  map_every qid_spec_tac [`e2'`, `e1'`, `e2`, `e1`, `vs`] >> Induct >>
  simp[lookup_vars_def] >>
  dsimp[option_case_eq] >> reverse conj_tac >- metis_tac[] >>
  simp[LIST_REL_EL_EQN]);

val renumber_code_locs_correct = Q.store_thm("renumber_code_locs_correct",
  `(!tmp xs env (s1:'ffi closSem$state) env' t1 res s2 n.
     tmp = (xs,env,s1) ∧
     (evaluate (xs,env,s1) = (res,s2)) ⇒
     ¬contains_App_SOME s1.max_app xs ∧
     LIST_REL (v_rel s1.max_app) env env' ∧
     state_rel s1 t1 ==>
     ?res' t2.
        (evaluate (SND(renumber_code_locs_list n xs),env',t1) = (res',t2)) /\
        result_rel (LIST_REL (v_rel s1.max_app)) (v_rel s1.max_app) res res' /\
        state_rel s2 t2) ∧
   (!loc f args (s:'ffi closSem$state) res s2 f' args' t1.
       evaluate_app loc f args s = (res,s2) ⇒
       v_rel s.max_app f f' ∧
       loc = NONE ∧
       LIST_REL (v_rel s.max_app) args args' ∧
       state_rel s t1
       ⇒
       ?res' t2.
          (evaluate_app loc f' args' t1 = (res',t2)) /\
          result_rel (LIST_REL (v_rel s.max_app)) (v_rel s.max_app) res res' /\
          state_rel s2 t2)`,
  ho_match_mp_tac evaluate_ind \\ srw_tac[][]
  THEN1 (* NIL *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,evaluate_def]
    \\ SRW_TAC [] [])
  THEN1 (* CONS *)
   (simp [renumber_code_locs_def,evaluate_def,UNCURRY] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[evaluate_def]
    \\ `?r1 s1. evaluate ([x],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,contains_App_SOME_def] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    `?r2 s2. evaluate (y::xs,env,s1) = (r2,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_const >> fs[] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    Cases_on `r2` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_SING >> full_simp_tac(srw_ss())[])
  THEN1 (* Var *)
   (srw_tac[][renumber_code_locs_def] >>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
    full_simp_tac(srw_ss())[evaluate_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][])
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    `?r1 s1. evaluate ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_const >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_SING >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[v_rel_simp] >> srw_tac[][] >>
    TRY (
      first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
      disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
      NO_TAC) >>
    TRY (
      first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
      disch_then(fn th => first_x_assum(qspec_then`q'`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
      NO_TAC) >>
    qpat_x_assum`X = (res,Y)`mp_tac >>
    srw_tac[][] >> full_simp_tac(srw_ss())[v_rel_simp])
  THEN1 (* Let *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    rename1`evaluate(xs,env,s)` \\
    `?r1 s1. evaluate (xs,env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_const >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    first_x_assum MATCH_MP_TAC >> srw_tac[][] >>
    MATCH_MP_TAC EVERY2_APPEND_suff >> srw_tac[][] )
  THEN1 (* Raise *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s1. evaluate ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    tac >> full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_SING >> full_simp_tac(srw_ss())[])
  THEN1 (* Handle *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_const >> fs[] >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    Cases_on`e`>>full_simp_tac(srw_ss())[] >> srw_tac[][])
  THEN1 (* Op *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s2. evaluate (xs,env,s) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    `s.max_app = s2'.max_app` by (
      imp_res_tac state_rel_max_app >>
      imp_res_tac evaluate_const >>
      fs[]) >> fs[] >>
    imp_res_tac EVERY2_REVERSE >> pop_assum kall_tac >>
    first_assum(fn th1 => first_assum(fn th2 => mp_tac (MATCH_MP do_app (CONJ th1 th2)))) >>
    strip_tac >>
    last_x_assum mp_tac >>
    BasicProvers.CASE_TAC >> TRY(Cases_on`a'`) >> srw_tac[][] >> simp[] >>
    imp_res_tac do_app_err >>
    reverse(Cases_on`op=Equal`) >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[do_app_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][v_rel_simp])
  THEN1 (* Fn *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,evaluate_def,LET_THM,UNCURRY] >>
    imp_res_tac state_rel_max_app >>
    full_simp_tac(srw_ss())[clos_env_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[contains_App_SOME_def] >> srw_tac[][v_rel_simp] >>
    TRY (full_simp_tac(srw_ss())[] >> PROVE_TAC[]) >>
    last_x_assum mp_tac >>
    BasicProvers.CASE_TAC >- (
      srw_tac[][] >> simp[v_rel_simp] >> METIS_TAC[] ) >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac lookup_vars_NONE >>
      BasicProvers.CASE_TAC >> srw_tac[][] >> srw_tac[][] >>
      imp_res_tac lookup_vars_SOME >>
      imp_res_tac lookup_vars_MEM >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN,MEM_EL] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
      res_tac >> DECIDE_TAC ) >>
    srw_tac[][] >>
    imp_res_tac lookup_vars_SOME >>
    imp_res_tac lookup_vars_MEM >>
    BasicProvers.CASE_TAC >> srw_tac[][] >> srw_tac[][v_rel_simp] >- (
      imp_res_tac lookup_vars_NONE >> full_simp_tac(srw_ss())[MEM_EL] >>
      res_tac >>
      imp_res_tac LIST_REL_LENGTH >>
      DECIDE_TAC ) >>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
    qexists_tac`n`>>simp[] >>
    imp_res_tac lookup_vars_SOME >>
    imp_res_tac lookup_vars_MEM >>
    simp[] )
  THEN1 (* Letrec *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,evaluate_def,LET_THM,UNCURRY] >>
    Cases_on`renumber_code_locs_list n (MAP SND fns)`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac state_rel_max_app >>
    imp_res_tac renumber_code_locs_list_length >>
    full_simp_tac(srw_ss())[EVERY_ZIP, MAP_ZIP] >>
    reverse (srw_tac[][]) >>
    full_simp_tac (bool_ss) []
    >- (srw_tac[][] >> srw_tac[][])
    >- srw_tac[][] >>
    full_simp_tac(srw_ss())[combinTheory.o_DEF, EVERY_MAP, LAMBDA_PROD] >>
    full_simp_tac(srw_ss())[build_recc_def,clos_env_def] >> reverse(srw_tac[][]) >>
    full_simp_tac(srw_ss())[contains_App_SOME_def] >> srw_tac[][] >>
    Cases_on `namesopt` >> full_simp_tac(srw_ss())[]
    >- (first_x_assum MATCH_MP_TAC >> srw_tac[][] >>
        MATCH_MP_TAC EVERY2_APPEND_suff >> srw_tac[][] >>
        imp_res_tac renumber_code_locs_list_length >>
        srw_tac[][LIST_REL_EL_EQN,EL_GENLIST] >>
        srw_tac[][v_rel_simp] >> METIS_TAC[SND])
    >- (rename1 `lookup_vars vv EE` >> Cases_on `lookup_vars vv EE` >> full_simp_tac(srw_ss())[]
        >- (rename1 `LIST_REL (v_rel _) env1 EE` >>
            `lookup_vars vv env1 = NONE`
                by metis_tac[lookup_vars_NONE_related_env] >>
            full_simp_tac(srw_ss())[] >> srw_tac[][]) >>
        rename1 `LIST_REL (v_rel _) env1 EE` >>
        full_simp_tac (srw_ss() ++ DNF_ss) [AND_IMP_INTRO] >>
        first_x_assum match_mp_tac >> simp[] >>
        `∃ee. lookup_vars vv env1 = SOME ee`
           by (Cases_on `lookup_vars vv env1` >> simp[] >>
               metis_tac[lookup_vars_NONE_related_env, NOT_NONE_SOME]) >>
        full_simp_tac(srw_ss())[] >> MATCH_MP_TAC EVERY2_APPEND_suff >> simp[] >>
        srw_tac[][LIST_REL_EL_EQN] >> simp[v_rel_simp] >>
        metis_tac[lookup_vars_SOME_related_env, SND]))
  THEN1 (* App *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,evaluate_def,LET_THM,UNCURRY] >>
    `LENGTH (SND (renumber_code_locs_list (FST (renumber_code_locs n x1)) args)) = LENGTH args`
            by (Cases_on `renumber_code_locs n x1` >>
                full_simp_tac(srw_ss())[] >>
                Cases_on `renumber_code_locs_list q args` >>
                full_simp_tac(srw_ss())[] >>
                metis_tac [renumber_code_locs_list_length]) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    first_assum(split_pair_case0_tac o lhs o concl) >>
    full_simp_tac(srw_ss())[contains_App_SOME_def] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`evaluate (args,env,s) = (v2,_)` >>
    Cases_on `v2` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
    imp_res_tac state_rel_max_app >> fs[] >>
    imp_res_tac evaluate_const >> fs[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`evaluate (_,env,_) = (v2',_)` >>
    Cases_on `v2'` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    first_x_assum match_mp_tac >>
    srw_tac[][] >>
    imp_res_tac evaluate_SING >> full_simp_tac(srw_ss())[] >> srw_tac[][])
  THEN1 (* Tick *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s1. evaluate ([x],env,dec_clock 1 s) = (r1,s1)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    tac >> full_simp_tac(srw_ss())[] >>
    `t1.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    fs[dec_clock_def] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(qspecl_then[`dec_clock 1 t1`,`n`]mp_tac) >>
    impl_tac >- full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] >> srw_tac[][] >>
    fs[dec_clock_def] >> rfs[])
  THEN1 (* Call *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[find_code_def] >>
    `FDOM s2'.code = FDOM t2.code` by full_simp_tac(srw_ss())[state_rel_def,fmap_rel_def] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
      srw_tac[][] ) >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    imp_res_tac LIST_REL_LENGTH >>
    `s2'.clock = t2.clock` by full_simp_tac(srw_ss())[state_rel_def] >>
    `∃x. FLOOKUP s2'.code dest = SOME x ∧ code_rel s2'.max_app x (q,r)` by (
      full_simp_tac(srw_ss())[state_rel_def,fmap_rel_def,FLOOKUP_DEF] >>
      METIS_TAC[] ) >>
    Cases_on`x`>>full_simp_tac(srw_ss())[code_rel_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[]
      >- ( match_mp_tac state_rel_clock \\ rw[] ) >>
      fs[dec_clock_def] >>
      imp_res_tac state_rel_max_app >> fs[] >>
      imp_res_tac evaluate_const >> fs[] >>
      first_x_assum MATCH_MP_TAC >>
      simp[] >>
      full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] ) >>
    srw_tac[][])
  THEN1 (* App empty *)
   (full_simp_tac(srw_ss())[evaluate_def] >> srw_tac[][])
  THEN1 (* Real App *)
   (full_simp_tac(srw_ss())[evaluate_def] >>
    rename1 `dest_closure s.max_app NONE f (z::zs)` >>
    Cases_on `dest_closure s.max_app NONE f (z::zs)` >>
    imp_res_tac state_rel_max_app >>
    full_simp_tac(srw_ss())[] >>
    srw_tac[][]
    >- (imp_res_tac dest_closure_v_rel_none >>
        srw_tac[][]) >>
    `s.clock = t1.clock` by full_simp_tac(srw_ss())[state_rel_def] >>
    imp_res_tac EVERY2_LENGTH >>
    Cases_on `x` >>
    full_simp_tac(srw_ss())[]
    >- (`?c'. v_rel t1.max_app v c' ∧ dest_closure t1.max_app NONE f' (y::ys) = SOME (Partial_app c')`
                 by metis_tac [LIST_REL_def, dest_closure_v_rel_partial] >>
        srw_tac[][] >>
        full_simp_tac(srw_ss())[] >>
        srw_tac[][ dec_clock_def] >>
        metis_tac [state_rel_clock])
    >- (`∃args1' args2' n.
           dest_closure t1.max_app NONE f' (y::ys) =
           SOME (Full_app (SND (renumber_code_locs n e)) args1' args2') ∧
           ~contains_App_SOME t1.max_app [e] ∧
           LIST_REL (v_rel t1.max_app) l args1' ∧ LIST_REL (v_rel t1.max_app) l0 args2'`
                     by (
               imp_res_tac dest_closure_v_rel_full >>
               full_simp_tac(srw_ss())[PULL_EXISTS] >> prove_tac[]) >>
        simp [] >>
        imp_res_tac EVERY2_LENGTH >>
        full_simp_tac(srw_ss())[] >>
        srw_tac[][] >>
        full_simp_tac(srw_ss())[]
        >- metis_tac [state_rel_clock] >>
        Cases_on `evaluate ([e],l,dec_clock (SUC (LENGTH ys) − LENGTH args2') s)` >>
        srw_tac[][] >>
        full_simp_tac(srw_ss())[] >>
        Cases_on `q` >>
        full_simp_tac(srw_ss())[] >>
        srw_tac[][] >>
        first_x_assum (qspecl_then [`args1'`, `dec_clock (SUC (LENGTH ys) - LENGTH (args2')) t1`,
                                    `n`] mp_tac) >>
        srw_tac[][] >>
        full_simp_tac(srw_ss())[dec_clock_def] >>
        rev_full_simp_tac(srw_ss())[state_rel_clock] >>
        full_simp_tac(srw_ss())[renumber_code_locs_def, LET_THM, helper] >>
        BasicProvers.EVERY_CASE_TAC >>
        full_simp_tac(srw_ss())[] >> srw_tac[][] >>
        imp_res_tac state_rel_max_app >>
        imp_res_tac evaluate_const >> fs[])));

val renumber_code_locs_every_Fn_SOME = Q.store_thm("renumber_code_locs_every_Fn_SOME",
  `(∀n es. every_Fn_SOME (SND (renumber_code_locs_list n es))) ∧
   (∀n e. every_Fn_SOME [SND (renumber_code_locs n e)])`,
  ho_match_mp_tac renumber_code_locs_ind >>
  srw_tac[][renumber_code_locs_def] >> srw_tac[][every_Fn_SOME_def] >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[Once every_Fn_SOME_EVERY] >>
  imp_res_tac renumber_code_locs_list_length >>
  full_simp_tac(srw_ss())[EVERY_MAP,ZIP_MAP] >>
  full_simp_tac(srw_ss())[EVERY_MEM,MEM_ZIP,PULL_EXISTS,MEM_EL]);

val renumber_code_locs_every_Fn_vs_NONE = Q.store_thm("renumber_code_locs_every_Fn_vs_NONE",
  `(∀n es. every_Fn_vs_NONE (SND (renumber_code_locs_list n es)) ⇔
           every_Fn_vs_NONE es) ∧
   (∀n e. every_Fn_vs_NONE [SND (renumber_code_locs n e)] ⇔
          every_Fn_vs_NONE [e])`,
  ho_match_mp_tac renumber_code_locs_ind >>
  srw_tac[][renumber_code_locs_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >- (
    simp[Once every_Fn_vs_NONE_EVERY] >>
    simp[Once every_Fn_vs_NONE_EVERY,SimpRHS] >>
    metis_tac[every_Fn_vs_NONE_EVERY] ) >>
  imp_res_tac renumber_code_locs_list_length >>
  full_simp_tac(srw_ss())[Once every_Fn_vs_NONE_EVERY] >>
  full_simp_tac(srw_ss())[Once every_Fn_vs_NONE_EVERY,SimpRHS] >>
  full_simp_tac(srw_ss())[EVERY_MAP,ZIP_MAP] >>
  full_simp_tac(srw_ss())[EVERY_MEM,MEM_ZIP,PULL_EXISTS,MEM_EL]);

val renumber_code_locs_EVEN = Q.store_thm("renumber_code_locs_EVEN",
  `(∀n es. EVEN n ⇒ EVEN (FST (renumber_code_locs_list n es)) ∧ EVERY EVEN (code_locs (SND (renumber_code_locs_list n es)))) ∧
   (∀n e. EVEN n ⇒ EVEN (FST (renumber_code_locs n e)) ∧ EVERY EVEN (code_locs [SND (renumber_code_locs n e)]))`,
  ho_match_mp_tac renumber_code_locs_ind
  \\ rw[renumber_code_locs_def,code_locs_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ fs[code_locs_def]
  >- ( rw[Once code_locs_cons] )
  \\ fs[EVEN_MOD2,ADD_MODULUS]
  \\ fs[SIMP_RULE(srw_ss()++ARITH_ss)[]MOD_TIMES]
  \\ imp_res_tac renumber_code_locs_list_length
  \\ fs[MAP_ZIP,EVERY_GENLIST] \\ rw[]
  \\ simp[EVEN_MOD2,SIMP_RULE(srw_ss()++ARITH_ss)[]MOD_TIMES]);

val renumber_code_locs_elist_globals = Q.store_thm(
  "renumber_code_locs_elist_globals",
  `(∀loc es n es'.
      renumber_code_locs_list loc es = (n,es') ⇒
      elist_globals es' = elist_globals es) ∧
   (∀loc e n e'.
      renumber_code_locs loc e = (n, e') ⇒
      set_globals e' = set_globals e)`,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
  rename1`renumber_code_locs_list locn1 (MAP SND functions)` >>
  qspecl_then [`locn1`, `MAP SND functions`] mp_tac
    (CONJUNCT1 renumber_code_locs_length) >>
  simp[] >> simp[MAP_ZIP]);

val renumber_code_locs_esgc_free = Q.store_thm(
  "renumber_code_locs_esgc_free",
  `(∀loc es n es'.
      renumber_code_locs_list loc es = (n,es') ∧ EVERY esgc_free es ⇒
      EVERY esgc_free es') ∧
   (∀loc e n e'.
      renumber_code_locs loc e = (n,e') ∧ esgc_free e ⇒ esgc_free e')`,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[]
  >- (imp_res_tac renumber_code_locs_elist_globals >> simp[])
  >- (rename1`renumber_code_locs_list locn1 (MAP SND functions)` >>
      qspecl_then [`locn1`, `MAP SND functions`] mp_tac
        (CONJUNCT1 renumber_code_locs_length) >>
      simp[] >> simp[MAP_ZIP] >> imp_res_tac renumber_code_locs_elist_globals >>
      simp[]));

val _ = export_theory();
