(* Various basic properties of the big and small step semantics, and their
 * semantic primitives. *)

open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory;
open terminationTheory;
open miscLib boolSimps;

val _ = new_theory "evalProps";

val pmatch_append = Q.store_thm ("pmatch_append",
`(!(cenv : envC) (st : v store) p v env env' env''.
    (pmatch cenv st p v env = Match env') ⇒
    (pmatch cenv st p v (env++env'') = Match (env'++env''))) ∧
 (!(cenv : envC) (st : v store) ps v env env' env''.
    (pmatch_list cenv st ps v env = Match env') ⇒
    (pmatch_list cenv st ps v (env++env'') = Match (env'++env'')))`,
ho_match_mp_tac pmatch_ind >>
rw [pmatch_def, bind_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val do_app_cases = Q.store_thm ("do_app_cases",
`!st op st' vs v.
  (do_app st op vs = SOME (st',v))
  =
  ((?op' n1 n2.
    (op = Opn op') ∧ (vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∧
    (((((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧
     (st' = st) ∧ (v = Rerr (Rraise (prim_exn "Div")))) ∨
     ~(((op' = Divide) ∨ (op' = Modulo)) ∧ (n2 = 0)) ∧
     (st' = st) ∧ (v = Rval (Litv (IntLit (opn_lookup op' n1 n2)))))) ∨
  (?op' n1 n2.
    (op = Opb op') ∧ (vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∧
    (st = st') ∧ (v = Rval (Litv (Bool (opb_lookup op' n1 n2))))) ∨
  ((op = Equality) ∧ (st = st') ∧
    ((?v1 v2. 
      (vs = [v1;v2]) ∧ 
      ((?b. (do_eq v1 v2 = Eq_val b) ∧ (v = Rval (Litv (Bool b)))) ∨
       ((do_eq v1 v2 = Eq_closure) ∧ (v = Rerr (Rraise (prim_exn "Eq")))))))) ∨
  (?lnum v2.
    (op = Opassign) ∧ (vs = [Loc lnum; v2]) ∧ (store_assign lnum (Refv v2) st = SOME st') ∧
     (v = Rval (Litv Unit))) ∨
  (?lnum v2.
    (op = Opref) ∧ (vs = [v2]) ∧ (store_alloc (Refv v2) st = (st',lnum)) ∧
     (v = Rval (Loc lnum))) ∨
  (?lnum v2.
    (st = st') ∧
    (op = Opderef) ∧ (vs = [Loc lnum]) ∧ (store_lookup lnum st = SOME (Refv v2)) ∧
    (v = Rval v2)) ∨
  (?i w.
      (op = Aalloc) ∧ (vs = [Litv (IntLit i); Litv (Word8 w)]) ∧
      (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript")) ∧ (st = st')) ∨
       (?lnum. ~(i < 0) ∧
        (st',lnum) = store_alloc (W8array (REPLICATE (Num (ABS i)) w)) st ∧
        v = Rval (Loc lnum)))) ∨
  (?ws lnum i.
    (op = Asub) ∧ (vs = [Loc lnum; Litv (IntLit i)]) ∧ (st = st') ∧
    store_lookup lnum st = SOME (W8array ws) ∧ 
    (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript"))) ∨
     ((~(i < 0) ∧ Num (ABS i) ≥ LENGTH ws ∧
       v = Rerr (Rraise (prim_exn "Subscript")))) ∨
     (~(i < 0) ∧
      Num (ABS i) < LENGTH ws ∧
      (v = Rval (Litv (Word8 (EL (Num(ABS i)) ws))))))) ∨
  (?lnum ws.
    (op = Alength) ∧ (vs = [Loc lnum]) ∧ st = st' ∧
    store_lookup lnum st = SOME (W8array ws) ∧ 
    v = Rval (Litv (IntLit (&(LENGTH ws))))) ∨
  (?ws lnum i w.
    (op = Aupdate) ∧ (vs = [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) ∧ 
    store_lookup lnum st = SOME (W8array ws) ∧ 
    (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript")) ∧ st = st') ∨
     ((~(i < 0) ∧ Num (ABS i) ≥ LENGTH ws ∧ st = st' ∧
       v = Rerr (Rraise (prim_exn "Subscript")))) ∨
     (~(i < 0) ∧
      Num (ABS i) < LENGTH ws ∧
      store_assign lnum (W8array (LUPDATE w (Num (ABS i)) ws)) st = SOME st' ∧
      v = Rval (Litv Unit)))) ∨
  (?vs' v'.
    (op = VfromList) ∧ (vs = [v']) ∧ (SOME vs' = v_to_list v') ∧
    st = st' ∧
    v = Rval (Vectorv vs')) ∨
  (?vs' lnum i.
    (op = Vsub) ∧ (vs = [Vectorv vs'; Litv (IntLit i)]) ∧ (st = st') ∧
    (((i < 0) ∧ v = Rerr (Rraise (prim_exn "Subscript"))) ∨
     ((~(i < 0) ∧ Num (ABS i) ≥ LENGTH vs' ∧
       v = Rerr (Rraise (prim_exn "Subscript")))) ∨
     (~(i < 0) ∧
      Num (ABS i) < LENGTH vs' ∧
      (v = Rval (EL (Num(ABS i)) vs'))))))`,
 SIMP_TAC (srw_ss()) [do_app_def] >>
 cases_on `op` >>
 rw [] >>
 cases_on `vs` >>
 rw [] >>
 every_case_tac >>
 rw [] >>
 TRY (cases_on `do_eq v1 v2`) >>
 rw [] >>
 UNABBREV_ALL_TAC >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 every_case_tac >>
 rw [] >>
 metis_tac []);

val do_opapp_cases = store_thm("do_opapp_cases",
  ``∀env' vs v.
    (do_opapp vs = SOME (env',v))
    =
  ((∃v2 menv'' cenv'' env'' n e.
    (vs = [Closure (menv'',cenv'',env'') n e; v2]) ∧
    (env' = (menv'',cenv'',bind n v2 env'')) ∧ (v = e)) ∨
  (?v2 menv'' cenv'' env'' funs n' n'' e.
    (vs = [Recclosure (menv'',cenv'',env'') funs n'; v2]) ∧
    (find_recfun n' funs = SOME (n'',e)) ∧
    (ALL_DISTINCT (MAP (\(f,x,e). f) funs)) ∧
    (env' = (menv'',cenv'', bind n'' v2 (build_rec_env funs (menv'',cenv'',env'') env''))) ∧ (v = e)))``,
  rw[do_opapp_def] >>
  cases_on `vs` >> rw [] >>
  every_case_tac >> metis_tac []);

val build_rec_env_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. bind f (Recclosure env funs' f) env') env' funs =
merge (MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs) env'`,
Induct >>
rw [merge_def, bind_def] >>
PairCases_on `h` >>
rw []);

(* Alternate definition for build_rec_env *)
val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
`∀funs funs' env env'.
  build_rec_env funs env env' =
  merge (MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs) env'`,
rw [build_rec_env_def, build_rec_env_help_lem]);

val do_con_check_build_conv = Q.store_thm ("do_con_check_build_conv",
`!tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v`,
rw [do_con_check_def, build_conv_def] >>
every_case_tac >>
fs []);

val merge_envC_empty_assoc = Q.store_thm ("merge_envC_empty_assoc",
`!envC1 envC2 envC3.
  merge_envC ([],envC1) (merge_envC ([],envC2) envC3)
  =
  merge_envC ([],envC1++envC2) envC3`,
 rw [] >>
 PairCases_on `envC3` >>
 rw [merge_envC_def, merge_def]);

val same_ctor_and_same_tid = Q.store_thm ("same_ctor_and_same_tid",
`!cn1 tn1 cn2 tn2.
  same_tid tn1 tn2 ∧
  same_ctor (cn1,tn1) (cn2,tn2)
  ⇒
  tn1 = tn2 ∧ cn1 = cn2`,
 cases_on `tn1` >>
 cases_on `tn2` >>
 fs [same_tid_def, same_ctor_def]);

val same_tid_sym = Q.store_thm ("same_tid_sym",
`!tn1 tn2. same_tid tn1 tn2 = same_tid tn2 tn1`,
 cases_on `tn1` >>
 cases_on `tn2` >>
 rw [same_tid_def] >>
 metis_tac []);

val build_tdefs_cons = Q.store_thm ("build_tdefs_cons",
`(!tvs tn ctors tds mn.
  build_tdefs mn ((tvs,tn,ctors)::tds) =
    build_tdefs mn tds ++ REVERSE (MAP (\(conN,ts). (conN, LENGTH ts, TypeId (mk_id mn tn))) ctors)) ∧
 (!mn. build_tdefs mn [] = [])`,
rw [build_tdefs_def]);

val check_ctor_foldr_flat_map = Q.prove (
`!c. (FOLDR
         (λ(tvs,tn,condefs) x2.
            FOLDR (λ(n,ts) x2. n::x2) x2 condefs) [] c)
    =
    FLAT (MAP (\(tvs,tn,condefs). (MAP (λ(n,ts). n)) condefs) c)`,
induct_on `c` >>
rw [LET_THM] >>
PairCases_on `h` >>
fs [LET_THM] >>
pop_assum (fn _ => all_tac) >>
induct_on `h2` >>
rw [] >>
PairCases_on `h` >>
rw []);

val check_dup_ctors_thm = Q.store_thm ("check_dup_ctors_thm",
`!tds.
  check_dup_ctors tds =
    ALL_DISTINCT (FLAT (MAP (\(tvs,tn,condefs). (MAP (λ(n,ts). n)) condefs) tds))`,
metis_tac [check_dup_ctors_def,check_ctor_foldr_flat_map]);

val check_dup_ctors_cons = Q.store_thm ("check_dup_ctors_cons",
`!tvs ts ctors tds.
  check_dup_ctors ((tvs,ts,ctors)::tds)
  ⇒
  check_dup_ctors tds`,
induct_on `tds` >>
rw [check_dup_ctors_def, LET_THM, RES_FORALL] >>
PairCases_on `h` >>
fs [] >>
pop_assum MP_TAC >>
pop_assum (fn _ => all_tac) >>
induct_on `ctors` >>
rw [] >>
PairCases_on `h` >>
fs []);

val map_error_result_def = Define`
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f Rtype_error = Rtype_error) ∧
  (map_error_result f Rtimeout_error = Rtimeout_error)`
val _ = export_rewrites["map_error_result_def"]

val map_error_result_Rtype_error = store_thm("map_error_result_Rtype_error",
  ``map_error_result f e = Rtype_error ⇔ e = Rtype_error``,
  Cases_on`e`>>simp[])
val map_error_result_Rtimeout_error = store_thm("map_error_result_Rtimeout_error",
  ``map_error_result f e = Rtimeout_error ⇔ e = Rtimeout_error``,
  Cases_on`e`>>simp[])
val _ = export_rewrites["map_error_result_Rtimeout_error","map_error_result_Rtype_error"]

val map_result_def = Define`
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))`
val _ = export_rewrites["map_result_def"]

val map_result_Rerr = store_thm("map_result_Rerr",
  ``map_result f1 f2 e = Rerr e' ⇔ ∃a. e = Rerr a ∧ map_error_result f2 a = e'``,
  Cases_on`e`>>simp[EQ_IMP_THM])
val _ = export_rewrites["map_result_Rerr"]

val evaluate_decs_evaluate_prog_MAP_Tdec = store_thm("evaluate_decs_evaluate_prog_MAP_Tdec",
  ``∀ck env cs tids ds res.
      evaluate_decs ck NONE env (cs,tids) ds res
      ⇔
      case res of ((s,tids'),envC,r) =>
      evaluate_prog ck env (cs,tids,{}) (MAP Tdec ds) ((s,tids',{}),([],envC),map_result(λenvE. (emp,envE))(I)r)``,
  Induct_on`ds`>>simp[Once evaluate_decs_cases,Once evaluate_prog_cases] >- (
    rpt gen_tac >> BasicProvers.EVERY_CASE_TAC >> simp[emp_def] >>
    Cases_on`r'`>>simp[] ) >>
  srw_tac[DNF_ss][] >>
  PairCases_on`res`>>srw_tac[DNF_ss][]>>
  PairCases_on`env`>>srw_tac[DNF_ss][]>>
  simp[evaluate_top_cases] >> srw_tac[DNF_ss][emp_def] >>
  srw_tac[DNF_ss][EQ_IMP_THM] >- (
    Cases_on`e`>>simp[] )
  >- (
    disj1_tac >>
    CONV_TAC(STRIP_BINDER_CONV(SOME existential)(lift_conjunct_conv(equal``evaluate_dec`` o fst o strip_comb))) >>
    first_assum(split_pair_match o concl) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fsrw_tac[DNF_ss][EQ_IMP_THM] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[] >> strip_tac >>
    fs[merge_def] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    Cases_on`r`>> simp[combine_dec_result_def,combine_mod_result_def,merge_def,emp_def,merge_envC_def] )
  >- (
    disj2_tac >>
    CONV_TAC(STRIP_BINDER_CONV(SOME existential)(lift_conjunct_conv(equal``evaluate_dec`` o fst o strip_comb))) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fsrw_tac[DNF_ss][EQ_IMP_THM,FORALL_PROD,merge_def,merge_envC_def] >>
    `∃z. r' = map_result (λenvE. (emp,envE)) I z` by (
      Cases_on`r'`>>fs[combine_mod_result_def,merge_def] >>
      TRY(METIS_TAC[]) >>
      Cases_on`a`>>fs[]>>
      Cases_on`res4`>>fs[]>>rw[]>>
      qexists_tac`Rval r` >> simp[emp_def] ) >>
    PairCases_on`new_tds'`>>fs[merge_envC_def,merge_def]>>rw[]>>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[combine_dec_result_def,combine_mod_result_def] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    TRY (Cases_on`res4`>>fs[]) >>
    Cases_on`a`>>Cases_on`e`>>fs[]>>rw[])
  >- (
    Cases_on`a`>>fs[]))

val pat_bindings_accum = Q.store_thm ("pat_bindings_accum",
`(!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
 (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)`,
 Induct >>
 rw []
 >- rw [pat_bindings_def]
 >- rw [pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- rw [pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]);

val _ = export_theory ();
