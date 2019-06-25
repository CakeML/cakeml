(*
  Correctness proof for clos_number
*)
open preamble backendPropsTheory closLangTheory clos_numberTheory closSemTheory closPropsTheory;

val _ = new_theory"clos_numberProof";

val _ = temp_bring_to_front_overload"lookup"{Name="lookup",Thy="sptree"};
val _ = temp_bring_to_front_overload"insert"{Name="insert",Thy="sptree"};
val _ = temp_bring_to_front_overload"delete"{Name="delete",Thy="sptree"};
val _ = temp_bring_to_front_overload"map"{Name="map",Thy="sptree"};
val _ = temp_bring_to_front_overload"wf"{Name="wf",Thy="sptree"};

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

Theorem renumber_code_locs_list_IMP_LENGTH:
   renumber_code_locs_list loc es = (l1,es2) ==> LENGTH es2 = LENGTH es
Proof
  metis_tac [SND,renumber_code_locs_length]
QED

Theorem renumber_code_locs_inc:
   (∀n es. n ≤ FST (renumber_code_locs_list n es)) ∧
    (∀n e. n ≤ FST (renumber_code_locs n e))
Proof
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def] >> srw_tac[][] >>
  tac >> full_simp_tac(srw_ss())[] >>
  tac >> full_simp_tac(srw_ss())[] >>
  tac >> full_simp_tac(srw_ss())[] >> simp[] >>
  pairarg_tac \\ fs[] \\ pairarg_tac \\ fs[]
QED

Theorem renumber_code_locs_imp_inc:
   (renumber_code_locs_list n es = (m,vs) ⇒ n ≤ m) ∧
    (renumber_code_locs n e = (z,v) ⇒ n ≤ z)
Proof
  metis_tac[pairTheory.pair_CASES,pairTheory.FST,renumber_code_locs_inc]
QED

Theorem renumber_code_locs_list_length:
   ∀ls n x y. renumber_code_locs_list n ls = (x,y) ⇒ LENGTH y = LENGTH ls
Proof
  Induct >> simp[renumber_code_locs_def,LENGTH_NIL] >> srw_tac[][] >>
  Cases_on`renumber_code_locs n h`>>full_simp_tac(srw_ss())[]>>
  Cases_on`renumber_code_locs_list q ls`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
  res_tac
QED

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

Theorem renumber_code_locs_distinct:
   ∀n e. ALL_DISTINCT (code_locs [SND (renumber_code_locs n e)]) ∧
          EVERY ($<= n) (code_locs [SND (renumber_code_locs n e)]) ∧
          EVERY ($> (FST (renumber_code_locs n e))) (code_locs [SND (renumber_code_locs n e)])
Proof
  srw_tac[][] >>
  qspecl_then[`n`,`e`]strip_assume_tac (CONJUNCT2 renumber_code_locs_distinct_lemma) >> simp[] >>
  match_mp_tac (MP_CANON (GEN_ALL SORTED_ALL_DISTINCT)) >>
  qexists_tac`$<` >> simp[] >>
  simp[relationTheory.irreflexive_def]
QED

Theorem renumber_code_locs_list_distinct:
   !n es.
     ALL_DISTINCT (code_locs (SND (renumber_code_locs_list n es))) /\
     EVERY ($<= n) (code_locs (SND (renumber_code_locs_list n es))) /\
     EVERY ($> (FST (renumber_code_locs_list n es)))
           (code_locs (SND (renumber_code_locs_list n es)))
Proof
  rw []
  \\ qspecl_then [`n`,`es`] strip_assume_tac
         (CONJUNCT1 renumber_code_locs_distinct_lemma) \\ fs []
  \\ match_mp_tac (MP_CANON (GEN_ALL SORTED_ALL_DISTINCT))
  \\ qexists_tac `$<` \\ simp [relationTheory.irreflexive_def]
QED

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

val compile_inc_def = Define `
  compile_inc n xs =
    (* leave space in the naming for the daisy chaining of clos_to_bvl *)
    let n1 = make_even (n + MAX (LENGTH xs) 1) in
    let (m,ys) = renumber_code_locs_list n1 xs in
      (* embed the name of the first free slot (n) in the code *)
      (* no code will be generated for this pure Const expression *)
      (m, Op None (Const (&n)) [] :: ys)`;

val state_rel_def = Define `
  state_rel (s:(num#'c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (s.clock = t.clock) /\ (s.ffi = t.ffi) /\ (t.max_app = s.max_app) /\
    s.compile = state_cc (ignore_table compile_inc) t.compile /\
    t.compile_oracle = state_co (ignore_table compile_inc) s.compile_oracle /\
    fmap_rel (ref_rel (v_rel s.max_app)) s.refs t.refs ∧
    EVERY2 (OPTREL (v_rel s.max_app)) s.globals t.globals /\
    (*
    (∀n. SND (SND (s.compile_oracle n )) = [] ∧
         ¬contains_App_SOME s.max_app (FST(SND(s.compile_oracle n)))) /\
    *)
    s.code = FEMPTY ∧ t.code = FEMPTY`

val state_rel_max_app = Q.prove (
  `!s t. state_rel s t ⇒ s.max_app = t.max_app`,
   srw_tac[][state_rel_def]);

val state_rel_with_clock = Q.prove (
  `!s t. state_rel s t ⇒ state_rel (s with clock := x) (t with clock := x)`,
   srw_tac[][state_rel_def] \\ rfs[]);

val state_rel_clock = Q.prove(
  `state_rel s t ⇒ s.clock = t.clock`,
  rw[state_rel_def]);

val state_rel_globals = Q.prove(
  `state_rel s t ⇒
    LIST_REL (OPTREL (v_rel s.max_app)) s.globals t.globals`,
  srw_tac[][state_rel_def])

val state_rel_refs = Q.prove(
  `state_rel s t ⇒
    fmap_rel (ref_rel (v_rel t.max_app)) s.refs t.refs`,
  srw_tac[][state_rel_def])

val state_rel_code = Q.prove(
  `state_rel s t ⇒ s.code = FEMPTY ∧ t.code = FEMPTY`,
  rw[state_rel_def]);

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
            ``v_rel max_app y (Word64 n)``,
            ``v_rel max_app y (Block n l)``,
            ``v_rel max_app y (ByteVector ws)``,
            ``v_rel max_app y (RefPtr x)``,
            ``v_rel max_app y (Closure n a l narg x)``,
            ``v_rel max_app y (Recclosure x1 x2 x3 x4 x5)``] |> LIST_CONJ end
  |> curry save_thm"v_rel_simp"

Theorem v_rel_Boolv[simp]:
   (v_rel max_app x (Boolv b) ⇔ (x = Boolv b)) ∧
    (v_rel max_app (Boolv b) x ⇔ (x = Boolv b))
Proof
  Cases_on`b`>>srw_tac[][Boolv_def,Once v_rel_cases] >>
  srw_tac[][Once v_rel_cases]
QED

Theorem v_rel_Unit[simp]:
   (v_rel max_app x Unit ⇔ (x = Unit)) ∧
    (v_rel max_app Unit x ⇔ (x = Unit))
Proof
  EVAL_TAC >> simp[v_rel_simp]
QED

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

val do_app_inst =
  simple_val_rel_do_app
  |> Q.INST [`vr`|->`v_rel s.max_app`]
  |> INST_TYPE [``:'a``|->``:num # 'a``,``:'c``|->``:'a``]
  |> Q.INST [`sr`|->`\r t. (r.max_app = s.max_app) /\ state_rel r t`]
  |> SIMP_RULE std_ss []

Theorem do_app_lemma:
   state_rel s t ∧ LIST_REL (v_rel s.max_app) xs ys ⇒
    case do_app opp xs s of
      Rval (x,s1) =>
        ∃y t1.
          v_rel s.max_app x y ∧
          (s1.max_app = s.max_app ∧ state_rel s1 t1) ∧
          do_app opp ys t = Rval (y,t1)
    | Rerr err1 =>
        ∃err2.
          do_app opp ys t = Rerr err2 ∧
          exc_rel (v_rel s.max_app) err1 err2
Proof
  match_mp_tac do_app_inst
  \\ conj_tac THEN1
   (fs [simple_val_rel_def]
    \\ once_rewrite_tac [v_rel_cases] \\ fs []
    \\ rw [] \\ fs [])
  \\ fs [simple_state_rel_def,state_rel_def] \\ rw []
  \\ fs [FLOOKUP_DEF,fmap_rel_def] \\ TRY (rfs [] \\ NO_TAC)
  THEN1
   (`ref_rel (v_rel r.max_app) (r.refs ' ptr) (t.refs ' ptr)` by fs[]
    \\ rpt (qpat_x_assum `!x._` kall_tac)
    \\ rfs [] \\ Cases_on `r.refs ' ptr` \\ fs [ref_rel_def])
  THEN1
   (`ref_rel (v_rel r.max_app) (r.refs ' ptr) (t.refs ' ptr)` by fs[]
    \\ rpt (qpat_x_assum `!x._` kall_tac)
    \\ rfs [] \\ Cases_on `r.refs ' ptr` \\ fs [ref_rel_def])
  \\ rpt gen_tac \\ fs [] \\ Cases_on `x = p` \\ fs [FAPPLY_FUPDATE_THM]
  \\ metis_tac []
QED

Theorem list_to_v_v_rel:
   !xs ys.
     LIST_REL (v_rel ap) xs ys ==> v_rel ap (list_to_v xs) (list_to_v ys)
Proof
  Induct
  >- rw [LIST_REL_EL_EQN, v_rel_simp, list_to_v_def]
  \\ rw [] \\ fs [v_rel_simp, list_to_v_def]
QED

val do_app = Q.prove(
  `state_rel s1 s2 ∧
    LIST_REL (v_rel s1.max_app) x1 x2 ⇒
    (∀err.
      do_app op x1 s1 = (Rerr err) ⇒
      do_app op x2 s2 = (Rerr err)) ∧
    (∀v1 w1. do_app op x1 s1 = Rval(v1,w1) ⇒
             ∃v2 w2. do_app op x2 s2 = Rval(v2,w2) ∧
                     v_rel s1.max_app v1 v2 ∧ state_rel w1 w2)`,
  rpt strip_tac
  \\ drule (GEN_ALL do_app_lemma)
  \\ disch_then drule
  \\ disch_then (qspec_then `op` mp_tac) \\ fs []
  \\ rw [] \\ fs []
  \\ Cases_on `err` \\ fs []
  \\ qpat_x_assum `_ = Rerr (Rraise _)` mp_tac
  \\ simp [do_app_cases_err]
  \\ strip_tac \\ fs []
  \\ every_case_tac \\ fs[]);

val v_to_bytes = Q.prove(
  `v_rel m v w ⇒ v_to_bytes v = v_to_bytes w`,
  rw[v_to_bytes_def]
  \\ imp_res_tac v_to_list
  \\ fs[OPTREL_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro
  \\ rw[] \\ fs[]
  \\ fs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP,v_rel_simp]
  \\ rfs[EL_MAP,v_rel_simp,PULL_FORALL,METIS_PROVE[]``¬P ∨ Q ⇔ P ⇒ Q``]
  \\ rw[]
  >- ( qexists_tac`x` \\ simp[EL_MAP] )
  \\ first_x_assum(qspec_then`x`mp_tac) \\ rw[]
  \\ asm_exists_tac \\ rw[EL_MAP] \\ fs[]
  \\ res_tac \\ strip_tac \\ fs[v_rel_simp] \\ rfs[EL_MAP]);

val v_to_words = Q.prove(
  `v_rel m v w ⇒ v_to_words v = v_to_words w`,
  rw[v_to_words_def]
  \\ imp_res_tac v_to_list
  \\ fs[OPTREL_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ DEEP_INTRO_TAC some_intro
  \\ rw[] \\ fs[]
  \\ fs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP,v_rel_simp]
  \\ rfs[EL_MAP,v_rel_simp,PULL_FORALL,METIS_PROVE[]``¬P ∨ Q ⇔ P ⇒ Q``]
  \\ rw[]
  >- ( qexists_tac`x` \\ simp[EL_MAP] )
  \\ first_x_assum(qspec_then`x`mp_tac) \\ rw[]
  \\ asm_exists_tac \\ rw[EL_MAP] \\ fs[]
  \\ res_tac \\ strip_tac \\ fs[v_rel_simp] \\ rfs[EL_MAP]);

(*
val do_install = Q.prove(
  `state_rel s1 s2 ∧
   LIST_REL (v_rel s1.max_app) x1 x2 ⇒
   (∀err t. do_install x1 s1 = (Rerr (Rabort Rtimeout_error),t) ⇒
            ?t'. do_install x2 s2 = (Rerr (Rabort Rtimeout_error),t') /\
                 state_rel t t') ∧
   (∀e1 t1. do_install x1 s1 = (Rval e1,t1) ⇒
     ∃e2 t2. do_install x2 s2 = (Rval e2,t2) ∧
             ¬contains_App_SOME t1.max_app (e1) ∧ t1.max_app = s1.max_app ∧
             e2 = SND (compile_inc (FST(FST(s1.compile_oracle 0))) e1) ∧
             state_rel t1 t2)`,
  strip_tac
  \\ `∃res. do_install x1 s1 = res` by fs[]
  \\ fs[do_install_def,case_eq_thms] \\ rveq \\ fs[]
  \\ imp_res_tac v_to_bytes \\ fs[]
  \\ imp_res_tac v_to_words \\ fs[]
  \\ pairarg_tac \\ fs[] \\ pairarg_tac \\ fs[]
  \\ imp_res_tac state_rel_code \\ fs[]
  \\ imp_res_tac state_rel_max_app \\ fs[]
  \\ imp_res_tac state_rel_clock \\ fs[]
  \\ fs[shift_seq_def]
  \\ `s2.compile_oracle = state_co (ignore_table compile_inc) s1.compile_oracle` by fs[state_rel_def]
  \\ `s1.compile = state_cc (ignore_table compile_inc) s2.compile` by fs[state_rel_def]
  \\ fs[]
  \\ qpat_x_assum`state_co _ _ _ = _`mp_tac
  \\ simp[Once state_co_def]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac \\ rveq
  \\ imp_res_tac ignore_table_imp \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ simp[state_cc_def]
  \\ CASE_TAC \\ fs[]
  \\ split_pair_case_tac \\ fs[] \\ rveq
  \\ simp[FST_state_co]
  \\ split_pair_case_tac \\ fs[] \\ rveq
  \\ split_pair_case_tac \\ fs[] \\ rveq
  \\ IF_CASES_TAC \\ fs[]
  \\ fs[CaseEq"bool"]
  \\ fs[ignore_table_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ rename [`_ = (st1,code1)`]
  \\ `code1 <> []` by
    (fs [compile_inc_def] \\ pairarg_tac \\ fs [] \\ rveq \\ fs [])
  \\ fs[state_rel_def,state_co_def,ignore_table_def]
  \\ metis_tac[FUPDATE_LIST_THM,FST,SND,DECIDE``(n+1n)+1 = n+2``,LENGTH_NIL] );
*)

(* compiler correctness *)

Theorem lookup_vars_NONE_related_env:
   LIST_REL (v_rel max_app) e1 e2 ⇒
   (lookup_vars vs e1 = NONE ⇔ lookup_vars vs e2 = NONE)
Proof
  strip_tac >> `LENGTH e1 = LENGTH e2` by metis_tac[LIST_REL_LENGTH] >>
  metis_tac[lookup_vars_NONE]
QED

Theorem lookup_vars_SOME_related_env:
   LIST_REL (v_rel max_app) e1 e2 ∧ lookup_vars vs e1 = SOME e1' ∧
   lookup_vars vs e2 = SOME e2' ⇒ LIST_REL (v_rel max_app) e1' e2'
Proof
  map_every qid_spec_tac [`e2'`, `e1'`, `e2`, `e1`, `vs`] >> Induct >>
  simp[lookup_vars_def] >>
  dsimp[CaseEq"option"] >> reverse conj_tac >- metis_tac[] >>
  simp[LIST_REL_EL_EQN]
QED

(*
val do_install_Rabort = prove(
  ``closSem$do_install xs s2 = (Rerr (Rabort a),s3) ==>
    a = Rtype_error \/ a = Rtimeout_error``,
  rw [do_install_def]
  \\ fs[case_eq_thms,pair_case_eq] \\ rveq \\ fs[]
  \\ pairarg_tac \\ fs []
  \\ fs [do_install_def,case_eq_thms,pair_case_eq,bool_case_eq]);
*)

Theorem renumber_code_locs_correct:
   (!tmp xs env (s1:(num#'c,'ffi) closSem$state) env' t1 res s2 n.
     tmp = (xs,env,s1) ∧
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr (Rabort Rtype_error) ⇒
     ¬contains_App_SOME s1.max_app xs ∧
     LIST_REL (v_rel s1.max_app) env env' ∧
     state_rel s1 t1 ==>
     ?res' t2.
        (evaluate (SND(renumber_code_locs_list n xs),env',t1) = (res',t2)) /\
        result_rel (LIST_REL (v_rel s1.max_app)) (v_rel s1.max_app) res res' /\
        state_rel s2 t2) ∧
   (!loc f args (s:(num#'c,'ffi) closSem$state) res s2 f' args' t1.
       evaluate_app loc f args s = (res,s2) /\ res <> Rerr (Rabort Rtype_error) ⇒
       v_rel s.max_app f f' ∧
       loc = NONE ∧
       LIST_REL (v_rel s.max_app) args args' ∧
       state_rel s t1
       ⇒
       ?res' t2.
          (evaluate_app loc f' args' t1 = (res',t2)) /\
          result_rel (LIST_REL (v_rel s.max_app)) (v_rel s.max_app) res res' /\
          state_rel s2 t2)
Proof
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
    \\ `?r1 s1. evaluate ([x],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs[]
    \\ fs[renumber_code_locs_def,LET_THM,contains_App_SOME_def]
    \\ reverse (fs [case_eq_thms]) \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then `n` mp_tac) \\ rw [] \\ fs []
    \\ Cases_on `evaluate (y::xs,env,s1)` \\ fs []
    \\ rename1 `_ = (res4,t5)`
    \\ `res4 ≠ Rerr (Rabort Rtype_error)` by (strip_tac \\ fs [])
    \\ imp_res_tac evaluate_const \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then `q` mp_tac) \\ rw [] \\ fs []
    \\ reverse (Cases_on `res4`) \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [])
  THEN1 (* Var *)
   (srw_tac[][renumber_code_locs_def] >>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
    full_simp_tac(srw_ss())[evaluate_def] >> srw_tac[][] >> fs [] \\ rw [])
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    `?r1 s1. evaluate ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs[]
    \\ `r1 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) \\ fs[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >>
    rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_const >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_SING >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[v_rel_simp] >> srw_tac[][] >>
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
    `r1 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) \\ fs[] >>
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
    `r1 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) \\ fs[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_SING >> full_simp_tac(srw_ss())[])
  THEN1 (* Handle *)
   (full_simp_tac(srw_ss())[renumber_code_locs_def,LET_THM,UNCURRY]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[evaluate_def,contains_App_SOME_def] >>
    `r1 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) \\ fs[] >>
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
    `r1 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) \\ fs[] >>
    tac >> full_simp_tac(srw_ss())[] >>
    Cases_on`op = Install` >- (
      fs[]
      \\ first_x_assum drule
      \\ disch_then drule
      \\ disch_then(qspec_then`n`mp_tac)
      \\ rw[] \\ rw[]
      \\ fs[case_eq_thms]
      \\ rw[] \\ simp[PULL_EXISTS] \\ fs[] )
    (*
      fs[]
      \\ first_x_assum drule
      \\ disch_then drule
      \\ disch_then(qspec_then`n`strip_assume_tac) \\ rfs[]
      \\ Cases_on`r1` \\ fs[] \\ rveq \\ fs[]
      \\ imp_res_tac state_rel_max_app
      \\ imp_res_tac evaluate_const
      \\ drule (GEN_ALL do_install) \\ fs[]
      \\ imp_res_tac EVERY2_REVERSE \\ pop_assum kall_tac
      \\ disch_then drule
      \\ reverse (strip_tac
        \\ fsrw_tac[DNF_ss][case_eq_thms,pair_case_eq]
        \\ rfs[] \\ fs[] \\ rveq \\ fs[])
      THEN1
       (Cases_on `err` \\ fs []
        \\ imp_res_tac do_install_not_Rraise \\ fs []
        \\ rename1 `aa = Rtimeout_error ==> _`
        \\ Cases_on `aa` \\ fs []
        \\ imp_res_tac do_install_not_Rffi_error \\ fs[])
      \\ first_x_assum drule
      \\ fs [compile_inc_def]
      \\ qmatch_goalsub_abbrev_tac`renumber_code_locs_list nn`
      \\ disch_then(qspec_then`nn`strip_assume_tac)
      \\ rveq \\ fs[]
      THEN1
       (rename [`LIST_REL (v_rel t1.max_app) a vss`]
        \\ Q.ISPEC_THEN`vss`FULL_STRUCT_CASES_TAC SNOC_CASES
        >- (
          imp_res_tac evaluate_IMP_LENGTH
          \\ fs[do_install_def,CaseEq"list",CaseEq"option",CaseEq"prod"]
          \\ pairarg_tac \\ fs[CaseEq"bool",CaseEq"option",CaseEq"prod"] )
        \\ fs[LIST_REL_SNOC]
        \\ pairarg_tac \\ fs []
        \\ once_rewrite_tac [evaluate_CONS]
        \\ fs [EVAL ``evaluate ([Op None (Const n) []],[],t)``])
      \\ Q.ISPEC_THEN`v'`FULL_STRUCT_CASES_TAC SNOC_CASES
      >- (
        imp_res_tac evaluate_IMP_LENGTH
        \\ fs[do_install_def,CaseEq"list",CaseEq"option",CaseEq"prod"]
        \\ pairarg_tac \\ fs[CaseEq"bool",CaseEq"option",CaseEq"prod"] )
      \\ fs[LIST_REL_SNOC]
      \\ pairarg_tac \\ fs []
      \\ once_rewrite_tac [evaluate_CONS]
      \\ fs [EVAL ``evaluate ([Op None (Const n) []],[],t)``]
      \\ rename [`LIST_REL _ a vss`]
      \\ reverse (Q.ISPEC_THEN`vss`FULL_STRUCT_CASES_TAC SNOC_CASES)
      THEN1 (rewrite_tac [GSYM SNOC,LAST_SNOC] \\ fs [LIST_REL_SNOC])
      \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ fs [do_install_def,case_eq_thms]
      \\ rpt (pairarg_tac \\ fs [])
      \\ fs [do_install_def,case_eq_thms,bool_case_eq,pair_case_eq]*) >>
    srw_tac[][] >>
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
    >- (srw_tac[][] >> srw_tac[][]) >>
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
    `v3 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) >> fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`q`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    qmatch_assum_rename_tac`evaluate (args,env,s) = (v2,_)` >>
    Cases_on `v2` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
    imp_res_tac state_rel_max_app >> fs[] >>
    imp_res_tac evaluate_const >> fs[] >>
    `v2 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) >> fs [] >>
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
    `r1 <> Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) >> fs [] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(qspec_then`n`STRIP_ASSUME_TAC o MATCH_MP th)) >> rev_full_simp_tac(srw_ss())[] >>
    Cases_on `r1` \\ full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[find_code_def] >>
    `FDOM s2'.code = FDOM t2.code` by full_simp_tac(srw_ss())[state_rel_def,fmap_rel_def] >>
    fs [FLOOKUP_DEF,state_rel_def])
  THEN1 (* App empty *)
   (full_simp_tac(srw_ss())[evaluate_def] >> srw_tac[][])
  THEN1 (* Real App *)
   (full_simp_tac(srw_ss())[evaluate_def] >>
    rename1 `dest_closure s.max_app NONE f (z::zs)` >>
    Cases_on `dest_closure s.max_app NONE f (z::zs)` >>
    imp_res_tac state_rel_max_app >>
    full_simp_tac(srw_ss())[] >>
    srw_tac[][] >>
    `s.clock = t1.clock` by full_simp_tac(srw_ss())[state_rel_def] >>
    imp_res_tac EVERY2_LENGTH >>
    Cases_on `x` >>
    full_simp_tac(srw_ss())[]
    >- (`?c'. v_rel t1.max_app v c' ∧ dest_closure t1.max_app NONE f' (y::ys) = SOME (Partial_app c')`
                 by metis_tac [LIST_REL_def, dest_closure_v_rel_partial] >>
        srw_tac[][] >>
        full_simp_tac(srw_ss())[] >>
        srw_tac[][ dec_clock_def] >>
        metis_tac [state_rel_with_clock]) >>
    `∃args1' args2' n.
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
    >- metis_tac [state_rel_with_clock] >>
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
    rev_full_simp_tac(srw_ss())[state_rel_with_clock] >>
    full_simp_tac(srw_ss())[renumber_code_locs_def, LET_THM, helper] >>
    BasicProvers.EVERY_CASE_TAC >>
    full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac state_rel_max_app >>
    imp_res_tac evaluate_const >> fs[])
QED

Theorem renumber_code_locs_every_Fn_SOME:
   (∀n es. every_Fn_SOME (SND (renumber_code_locs_list n es))) ∧
   (∀n e. every_Fn_SOME [SND (renumber_code_locs n e)])
Proof
  ho_match_mp_tac renumber_code_locs_ind >>
  srw_tac[][renumber_code_locs_def] >> srw_tac[][every_Fn_SOME_def] >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[Once every_Fn_SOME_EVERY] >>
  imp_res_tac renumber_code_locs_list_length >>
  full_simp_tac(srw_ss())[EVERY_MAP,ZIP_MAP] >>
  full_simp_tac(srw_ss())[EVERY_MEM,MEM_ZIP,PULL_EXISTS,MEM_EL]
QED

Theorem renumber_code_locs_every_Fn_vs_NONE:
   (∀n es. every_Fn_vs_NONE (SND (renumber_code_locs_list n es)) ⇔
           every_Fn_vs_NONE es) ∧
   (∀n e. every_Fn_vs_NONE [SND (renumber_code_locs n e)] ⇔
          every_Fn_vs_NONE [e])
Proof
  ho_match_mp_tac renumber_code_locs_ind >>
  srw_tac[][renumber_code_locs_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >- (
    simp[Once every_Fn_vs_NONE_EVERY] >>
    simp[Once every_Fn_vs_NONE_EVERY,SimpRHS] >>
    metis_tac[every_Fn_vs_NONE_EVERY] ) >>
  imp_res_tac renumber_code_locs_list_length >>
  full_simp_tac(srw_ss())[Once every_Fn_vs_NONE_EVERY] >>
  full_simp_tac(srw_ss())[Once every_Fn_vs_NONE_EVERY,SimpRHS] >>
  full_simp_tac(srw_ss())[EVERY_MAP,ZIP_MAP] >>
  full_simp_tac(srw_ss())[EVERY_MEM,MEM_ZIP,PULL_EXISTS,MEM_EL]
QED

Theorem renumber_code_locs_EVEN:
   (∀n es. EVEN n ⇒ EVEN (FST (renumber_code_locs_list n es)) ∧ EVERY EVEN (code_locs (SND (renumber_code_locs_list n es)))) ∧
   (∀n e. EVEN n ⇒ EVEN (FST (renumber_code_locs n e)) ∧ EVERY EVEN (code_locs [SND (renumber_code_locs n e)]))
Proof
  ho_match_mp_tac renumber_code_locs_ind
  \\ rw[renumber_code_locs_def,code_locs_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ fs[code_locs_def]
  >- ( rw[Once code_locs_cons] )
  \\ fs[EVEN_MOD2,ADD_MODULUS]
  \\ fs[SIMP_RULE(srw_ss()++ARITH_ss)[]MOD_TIMES]
  \\ imp_res_tac renumber_code_locs_list_length
  \\ fs[MAP_ZIP,EVERY_GENLIST] \\ rw[]
  \\ simp[EVEN_MOD2,SIMP_RULE(srw_ss()++ARITH_ss)[]MOD_TIMES]
QED

Theorem renumber_code_locs_elist_globals:
   (∀loc es n es'.
      renumber_code_locs_list loc es = (n,es') ⇒
      elist_globals es' = elist_globals es) ∧
   (∀loc e n e'.
      renumber_code_locs loc e = (n, e') ⇒
      set_globals e' = set_globals e)
Proof
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[EVAL ``op_gbag Add``] >>
  rename1`renumber_code_locs_list locn1 (MAP SND functions)` >>
  qspecl_then [`locn1`, `MAP SND functions`] mp_tac
    (CONJUNCT1 renumber_code_locs_length) >>
  simp[] >> simp[MAP_ZIP]
QED

Theorem renumber_code_locs_esgc_free:
   (∀loc es n es'.
      renumber_code_locs_list loc es = (n,es') ∧ EVERY esgc_free es ⇒
      EVERY esgc_free es') ∧
   (∀loc e n e'.
      renumber_code_locs loc e = (n,e') ∧ esgc_free e ⇒ esgc_free e')
Proof
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[renumber_code_locs_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[]
  >- (imp_res_tac renumber_code_locs_elist_globals >> simp[])
  >- (rename1`renumber_code_locs_list locn1 (MAP SND functions)` >>
      qspecl_then [`locn1`, `MAP SND functions`] mp_tac
        (CONJUNCT1 renumber_code_locs_length) >>
      simp[] >> simp[MAP_ZIP] >> imp_res_tac renumber_code_locs_elist_globals >>
      simp[])
QED

Theorem renumber_code_locs_obeys_max_app:
   (∀loc es n es'.
      renumber_code_locs_list loc es = (n,es') ∧ EVERY (obeys_max_app m) es ⇒
      EVERY (obeys_max_app m) es') ∧
   (∀loc e n e'.
      renumber_code_locs loc e = (n,e') ∧ obeys_max_app m e ⇒ obeys_max_app m e')
Proof
  ho_match_mp_tac renumber_code_locs_ind
  \\ rw [renumber_code_locs_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ imp_res_tac renumber_code_locs_list_IMP_LENGTH \\ fs []
  \\ fs [] \\ rw [] \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
  \\ fs [MEM_ZIP] \\ fs [PULL_EXISTS,MEM_EL]
QED

Theorem renumber_code_locs_no_Labels:
   (∀loc es n es'.
      renumber_code_locs_list loc es = (n,es') ∧ EVERY no_Labels es ⇒
      EVERY no_Labels es') ∧
   (∀loc e n e'.
      renumber_code_locs loc e = (n,e') ∧ no_Labels e ⇒ no_Labels e')
Proof
  ho_match_mp_tac renumber_code_locs_ind
  \\ rw [renumber_code_locs_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ imp_res_tac renumber_code_locs_list_IMP_LENGTH \\ fs []
  \\ fs [] \\ rw [] \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
  \\ fs [MEM_ZIP] \\ fs [PULL_EXISTS,MEM_EL]
QED

Theorem renumber_code_locs_imp_EVEN:
   (renumber_code_locs_list n es = (n',es') ∧ EVEN n ⇒ EVEN n') ∧
   (renumber_code_locs n e = (n',e') ∧ EVEN n ⇒ EVEN n')
Proof
  rw[]
  \\ strip_assume_tac(SPEC_ALL (CONJUNCT1 renumber_code_locs_EVEN)) \\ rfs[]
  \\ strip_assume_tac(SPEC_ALL (CONJUNCT2 renumber_code_locs_EVEN)) \\ rfs[]
QED

Theorem renumber_code_locs_get_code_labels:
   (∀n es n' es'. renumber_code_locs_list n es = (n',es') ∧ EVERY ((=){}) (MAP get_code_labels es) ∧ EVEN n ⇒
      BIGUNION (set (MAP get_code_labels es')) = { n + 2 * k | k | n + 2 * k < n' }) ∧
   (∀n e n' e'. renumber_code_locs n e = (n',e') ∧ get_code_labels e = {} ∧ EVEN n ⇒
     get_code_labels e' = { n + 2 * k | k | n + 2 * k < n' })
Proof
  ho_match_mp_tac clos_numberTheory.renumber_code_locs_ind
  \\ rw[clos_numberTheory.renumber_code_locs_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ imp_res_tac renumber_code_locs_imp_inc
  \\ imp_res_tac renumber_code_locs_imp_EVEN \\ fs[]
  >- (
    rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ qpat_x_assum`EVEN _`mp_tac
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[]
      \\ qpat_x_assum`EVEN n`mp_tac
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ))
  >- (
    rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      `EVEN (n'''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[] \\ rw[] \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ Cases_on`p' + p'' ≤ k` \\ fs[]
      >- ( qexists_tac`k - p' - p''` \\ simp[] )
      \\ qexists_tac`k - p''`
      \\ simp[] ) )
  >- (
    rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rw[] \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ) )
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- fs[EVERY_MEM]
    \\ rw[]
    \\ rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rw[] \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ) )
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- fs[EVERY_MEM]
    \\ rw[] )
  >- fs[clos_numberTheory.renumber_code_locs_def]
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- fs[EVERY_MEM]
    \\ rw[]
    \\ rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rw[] \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ) )
  >- (
    reverse(rw[EXTENSION, EQ_IMP_THM])
    >- (
      Cases_on`2 * k + n = n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ rw[EVEN_EXISTS] \\ fs[]
      \\ fs[GSYM LEFT_ADD_DISTRIB] )
    >- ( qexists_tac`k` \\ fs[] )
    >- (
      rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ rw[EVEN_EXISTS] \\ fs[]
      \\ fs[GSYM LEFT_ADD_DISTRIB]
      \\ qexists_tac`m'-m`
      \\ simp[] ) )
  >- (
    imp_res_tac renumber_code_locs_list_IMP_LENGTH
    \\ fs[] \\ rveq \\ rfs[]
    \\ qpat_x_assum`{} = _`(assume_tac o SYM) \\ fs[]
    \\ rpt(qpat_x_assum`EVEN _`mp_tac)
    \\ rw[EVEN_EXISTS] \\ fs[]
    \\ rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k + m'' - m'` \\ simp[] )
    \\ fs[EXTENSION]
    \\ fs[LESS_EQ_EXISTS] \\ rveq
    \\ qexists_tac`k-p`
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB]
    \\ fs[clos_numberTheory.renumber_code_locs_def] )
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- (
      fs[EVERY_MEM]
      \\ fs[EVEN_ADD]
      \\ fs[EVEN_EXISTS] )
    \\ rw[]
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- (
      fs[EVERY_MEM]
      \\ fs[EXTENSION, MEM_MAP, PULL_EXISTS] )
    \\ rw[]
    \\ imp_res_tac renumber_code_locs_list_IMP_LENGTH \\ fs[]
    \\ simp[MAP_ZIP]
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- (
      fs[EVERY_MEM]
      \\ fs[EVEN_ADD]
      \\ fs[EVEN_EXISTS] )
    \\ rw[]
    \\ rpt(qpat_x_assum`EVEN _`mp_tac)
    \\ rw[EVEN_EXISTS] \\ fs[]
    \\ fs[LESS_EQ_EXISTS] \\ rveq
    \\ rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k+p` \\ simp[LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB] )
    >- ( qexists_tac`k + LENGTH fns + p` \\ simp[LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB] )
    >- ( qexists_tac`k` \\ simp[LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB] )
    \\ fs[]
    \\ Cases_on`k < p` \\ fs[]
    \\ fs[LEFT_ADD_DISTRIB]
    \\ Cases_on`k - p < LENGTH fns` \\ fs[]
    >- ( qexists_tac`k-p` \\ simp[] )
    >- ( qexists_tac`k - p - LENGTH fns` \\ fs[] )
    >- ( qexists_tac`k - p` \\ fs[] ) )
  >- (
    rw[EQ_IMP_THM, EXTENSION]
    >- ( qexists_tac`k` \\ fs[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ qpat_x_assum`EVEN _`mp_tac
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[]
      \\ qpat_x_assum`EVEN n`mp_tac
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ))
QED

Theorem renumber_code_locs_any_dests:
   (!k xs n ys. renumber_code_locs_list k xs = (n,ys) ==> any_dests ys = ∅) /\
    (!k x n y. renumber_code_locs k x = (n,y) ==> any_dests [y] = ∅)
Proof
  ho_match_mp_tac clos_numberTheory.renumber_code_locs_ind \\ rpt strip_tac
  \\ fs [clos_numberTheory.renumber_code_locs_def] \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ once_rewrite_tac [closPropsTheory.app_call_dests_cons] \\ fs []
  \\ `LENGTH fns = LENGTH fns'` by
       metis_tac [clos_numberTheory.renumber_code_locs_length,LENGTH_MAP,SND]
  \\ fs [MAP_ZIP]
QED

(* preservation of observable semantics *)

Theorem semantics_number:
   semantics (ffi:'ffi ffi_state) max_app FEMPTY co
     (state_cc (ignore_table compile_inc) cc) xs <> Fail ==>
   ¬contains_App_SOME max_app xs (* /\
   (∀n.
      SND (SND (co n)) = [] ∧
      ¬contains_App_SOME max_app (FST (SND (co n)))) *) ==>
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     (state_co (ignore_table compile_inc) co) cc
        (SND (renumber_code_locs_list n xs)) =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (state_cc (ignore_table compile_inc) cc) xs
Proof
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ drule (renumber_code_locs_correct
       |> CONJUNCT1 |> SIMP_RULE std_ss [])
  \\ simp []
  \\ qabbrev_tac `ff = initial_state ffi max_app FEMPTY
       (state_co (ignore_table compile_inc) co) cc`
  \\ disch_then (qspec_then `ff k` mp_tac)
  \\ qunabbrev_tac `ff`
  \\ disch_then (qspec_then `n` mp_tac)
  \\ impl_tac THEN1 (fs [state_rel_def,initial_state_def])
  \\ strip_tac
  \\ qexists_tac `0` \\ fs []
  \\ fs [state_rel_def]
  \\ Cases_on `res1` \\ fs []
  \\ Cases_on `e` \\ fs []
QED

val _ = export_theory();
