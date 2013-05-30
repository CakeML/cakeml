open preamble;
open LibTheory TypeSystemTheory AstTheory SemanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open typeSysPropsTheory;

val o_f_id = Q.prove (
`!m. (\x.x) o_f m = m`,
rw [fmap_EXT]);

val _ = new_theory "inferSound";

val infer_deBruijn_inc_def = tDefine "infer_deBruijn_inc" `
(infer_deBruijn_inc n (Infer_Tvar_db m) = 
  Infer_Tvar_db (m + n)) ∧
(infer_deBruijn_inc n (Infer_Tapp ts tn) =
  Infer_Tapp (MAP (infer_deBruijn_inc n) ts) tn) ∧
(infer_deBruijn_inc n (Infer_Tuvar m) = 
  Infer_Tuvar m)`
(WF_REL_TAC `measure (infer_t_size o SND)` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val t_unify_apply = Q.prove (
`!s1 s2 t1 t2.
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
cheat);

val t_unify_apply2 = Q.prove (
`!s1 s2 t1' t2' t1 t2.
  (t_unify s1 t1' t2' = SOME s2) ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
cheat);

val t_unify_wfs = Q.prove (
`!s1 t1 t2 s2.
  t_wfs s1 ∧
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  t_wfs s2`,
cheat);

val inc_wfs = Q.prove (
`!tvs s. t_wfs s ⇒ t_wfs (infer_deBruijn_inc tvs o_f s)`,
cheat);

val walkstar_inc = Q.prove (
`!tvs s n.
  t_wfs s ⇒
  (t_walkstar (infer_deBruijn_inc tvs o_f s) (Infer_Tuvar n) =
   infer_deBruijn_inc tvs (t_walkstar s (Infer_Tuvar n)))`,
cheat);

val flookup_thm = Q.prove (
`!f x v. ((FLOOKUP f x = NONE) = (x ∉ FDOM f)) ∧
         ((FLOOKUP f x = SOME v) = (x ∈ FDOM f ∧ (f ' x = v)))`,
rw [FLOOKUP_DEF]);

val lookup_map = Q.prove (
`!n env v f. 
  (lookup n env = SOME v) ⇒ (lookup n (MAP (\(x,y). (x, f y)) env) = SOME (f v))`,
ho_match_mp_tac lookup_ind >>
rw []);

val count_add1 = Q.prove (
`!n. count (n + 1) = n INSERT count n`,
metis_tac [COUNT_SUC, arithmeticTheory.ADD1]);

val st_ex_return_success = Q.prove (
`!v st v' st'.
  (st_ex_return v st = (Success v', st')) =
  ((v = v') ∧ (st = st'))`,
rw [st_ex_return_def]);

val st_ex_bind_success = Q.prove (
`!f g st st' v. 
 (st_ex_bind f g st = (Success v, st')) =
 ?v' st''. (f st = (Success v', st'')) /\ (g v' st'' = (Success v, st'))`,
rw [st_ex_bind_def] >>
cases_on `f st` >>
rw [] >>
cases_on `q` >>
rw []);

val fresh_uvar_success = Q.prove (
`!st t st'. 
  (fresh_uvar st = (Success t, st')) =
  ((t = Infer_Tuvar st.next_uvar) ∧
   (st' = st with next_uvar := st.next_uvar + 1))`,
rw [fresh_uvar_def] >>
metis_tac []);

val stupid_record_thing = Q.prove (
`(!st. (st with next_uvar := st.next_uvar) = st) ∧
 (!st. (st with subst := st.subst) = st) ∧
 (!st s. (st with subst := s).subst = s) ∧
 (!st s. (st with subst := s).next_uvar = st.next_uvar) ∧
 (!st uv. (st with next_uvar := uv).subst = st.subst)`,
cheat);

val count_list_sub1 = Q.prove (
`!n. (n ≠ 0) ⇒ (COUNT_LIST n = 0::MAP SUC (COUNT_LIST (n - 1)))`,
induct_on `n` >>
ONCE_REWRITE_TAC [rich_listTheory.COUNT_LIST_def] >>
fs []);

val el_map_count = Q.prove (
`!n f m. n < m ⇒ EL n (MAP f (COUNT_LIST m)) = f n`,
induct_on `n` >>
rw [] >>
cases_on `m` >>
fs [rich_listTheory.COUNT_LIST_def] >>
`n < SUC n'` by decide_tac >>
res_tac >>
fs [rich_listTheory.COUNT_LIST_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (mp_tac o GSYM o Q.SPEC `f o SUC`) >>
rw [MAP_MAP_o]);

val n_fresh_uvar_success = Q.prove (
`!n st ts st'. 
  (n_fresh_uvar n st = (Success ts, st')) =
  ((ts = MAP (\n. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST n)) ∧
   (st' = st with next_uvar := st.next_uvar + n))`,
ho_match_mp_tac n_fresh_uvar_ind >>
rw [] >>
rw [st_ex_return_success, Once n_fresh_uvar_def, rich_listTheory.COUNT_LIST_SNOC,
    st_ex_bind_success, fresh_uvar_success, stupid_record_thing] >-
metis_tac [] >>
fs [] >>
srw_tac [ARITH_ss] [] >>
rw [count_list_sub1, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF] >>
eq_tac >>
srw_tac [ARITH_ss] [arithmeticTheory.ADD1]);

val apply_subst_success = Q.prove (
`!t1 st1 t2 st2.
  (apply_subst t1 st1 = (Success t2, st2))
  =
  ((st2 = st1) ∧
   (t2 = t_walkstar st1.subst t1))`,
rw [st_ex_return_def, st_ex_bind_def, LET_THM, apply_subst_def, read_def] >>
eq_tac >>
rw []);

val add_constraint_success = Q.prove (
`!t1 t2 st st' x.
  (add_constraint t1 t2 st = (Success x, st'))
  =
  ((x = ()) ∧ (?s. (t_unify st.subst t1 t2 = SOME s) ∧ (st' = st with subst := s)))`,
rw [add_constraint_def] >>
full_case_tac >>
metis_tac []);

val pure_add_constraints_def = Define `
(pure_add_constraints s [] s' = (s = s')) ∧
(pure_add_constraints s1 ((t1,t2)::rest) s' = 
  ?s2. (t_unify s1 t1 t2 = SOME s2) ∧
       pure_add_constraints s2 rest s')`;

val pure_add_constraints_ind = fetch "-" "pure_add_constraints_ind";

val pure_add_constraints_append2 = Q.prove (
`!s1 ts s2 t1 t2.
  pure_add_constraints s1 ts s2 ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
induct_on `ts` >>
rw [pure_add_constraints_def] >>
rw [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_apply2]);

val pure_add_constraints_apply = Q.prove (
`!s1 ts s2.
  pure_add_constraints s1 ts s2
  ⇒
  MAP (t_walkstar s2 o FST) ts = MAP (t_walkstar s2 o SND) ts`,
induct_on `ts` >>
rw [pure_add_constraints_def] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_apply, pure_add_constraints_append2]);

val pure_add_constraints_append = Q.prove (
`!s1 ts1 s3 ts2. 
  pure_add_constraints s1 (ts1 ++ ts2) s3
  =
  (?s2. pure_add_constraints s1 ts1 s2 ∧ pure_add_constraints s2 ts2 s3)`,
ho_match_mp_tac pure_add_constraints_ind >>
rw [pure_add_constraints_def] >>
metis_tac []);

val add_constraints_success = Q.prove (
`!ts1 ts2 st st' x.
  (add_constraints ts1 ts2 st = (Success x, st'))
  =
  ((LENGTH ts1 = LENGTH ts2) ∧ 
   ((x = ()) ∧ 
   (st.next_uvar = st'.next_uvar) ∧
   pure_add_constraints st.subst (ZIP (ts1,ts2)) st'.subst))`,
ho_match_mp_tac add_constraints_ind >>
rw [add_constraints_def, pure_add_constraints_def, st_ex_return_success,
    failwith_def, st_ex_bind_success, add_constraint_success] >>
TRY (cases_on `x`) >>
rw [pure_add_constraints_def] >-
metis_tac [infer_st_component_equality] >>
eq_tac >>
rw [] >>
fs [infer_st_subst] >>
cases_on `t_unify st.subst t1 t2` >>
fs []);

val failwith_success = Q.prove (
`!m st v st'. (failwith m st = (Success v, st')) = F`,
rw [failwith_def]);

val lookup_st_ex_success = Q.prove (
`!pr x l st v st'. 
  (lookup_st_ex pr x l st = (Success v, st'))
  =
  ((lookup x l = SOME v) ∧ (st = st'))`,
ho_match_mp_tac lookup_st_ex_ind >>
rw [lookup_st_ex_def, lookup_def, failwith_def, st_ex_return_success]);

val constrain_uop_success = Q.prove (
`!uop t st v st'.
  (constrain_uop uop t st = (Success v, st'))
  =
  (((uop = Opref) ∧ (st = st') ∧ (v = Infer_Tapp [t] TC_ref)) ∨
   ((uop = Opderef) ∧ 
    (?uvar st''. ((fresh_uvar : ((num |-> infer_t) infer_st, infer_t, string) M) st = (Success uvar, st'')) ∧
                 (v = uvar) ∧
                 (add_constraint t (Infer_Tapp [uvar] TC_ref) st'' = (Success (), st')))))`,
rw [constrain_uop_def] >>
full_case_tac >>
rw [st_ex_return_success, st_ex_bind_success, oneTheory.one] >>
metis_tac []);

val op_case_expand = Q.prove (
`!f1 f2 f3 f4 f5 op st v st'.
  ((case op of
       Opn opn => f1
     | Opb opb => f2
     | Equality => f3
     | Opapp => f4
     | Opassign => f5) st
   = (Success v, st'))
  =
  ((?opn. (op = Opn opn) ∧ (f1 st = (Success v, st'))) ∨
   (?opb. (op = Opb opb) ∧ (f2 st = (Success v, st'))) ∨
   ((op = Equality) ∧ (f3 st = (Success v, st'))) ∨
   ((op = Opapp) ∧ (f4 st = (Success v, st'))) ∨
   ((op = Opassign) ∧ (f5 st = (Success v, st'))))`,
rw [] >>
cases_on `op` >>
rw []);

val constrain_op_success = 
  SIMP_CONV (srw_ss()) [constrain_op_def, op_case_expand, st_ex_bind_success,
                        st_ex_return_success, add_constraint_success]
  ``(constrain_op op t1 t2 st = (Success v, st'))``

val get_next_uvar_success = Q.prove (
`!st v st'. 
  (get_next_uvar st = (Success v, st')) 
  =
  ((v = st.next_uvar) ∧ (st = st'))`,
rw [get_next_uvar_def] >>
metis_tac []);

val apply_subst_list_success =
  SIMP_CONV (srw_ss()) [apply_subst_list_def, LET_THM]
  ``(apply_subst_list ts st = (Success v, st'))``

val guard_success = Q.prove (
`∀P m st v st'.
  (guard P m st = (Success v, st'))
  =
  (P ∧ (v = ()) ∧ (st = st'))`,
rw [guard_def, st_ex_return_def, failwith_def] >>
metis_tac []);

val success_eqns = 
  LIST_CONJ [st_ex_return_success, st_ex_bind_success, fresh_uvar_success,
             apply_subst_success, add_constraint_success, lookup_st_ex_success,
             n_fresh_uvar_success, failwith_success, add_constraints_success,
             constrain_uop_success, constrain_op_success, oneTheory.one,
             get_next_uvar_success, apply_subst_list_success, guard_success,
             read_def];

val check_t_def = tDefine "check_t" `
(check_t n uvars (Infer_Tuvar v) = (v ∈ uvars)) ∧
(check_t n uvars (Infer_Tvar_db n') = 
  (n' < n)) ∧
(check_t n uvars (Infer_Tapp ts tc) = EVERY (check_t n uvars) ts)`
(WF_REL_TAC `measure (infer_t_size o SND o SND)` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val check_env_def = Define `
check_env uvars env =
  EVERY (\(x, (tvs,t)). check_t tvs uvars t)  env`;

val check_menv_def = Define `
check_menv menv =
  EVERY (\(mn,env). EVERY (\(x, (tvs,t)). check_t tvs {} t) env) menv`;

val check_cenv_def = Define `
check_cenv (cenv : tenvC) = 
  EVERY (\(cn,(tvs,ts,t)). EVERY (check_freevars 0 tvs) ts) cenv`;

val convert_t_def = tDefine "convert_t" `
(convert_t (Infer_Tvar_db n) = Tvar_db n) ∧
(convert_t (Infer_Tapp ts tc) = Tapp (MAP convert_t ts) tc)`
(WF_REL_TAC `measure infer_t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val convert_menv_def = Define `
convert_menv menv = 
  MAP (\(mn,env). (mn, MAP (\(x,(tvs,t)). (x,(tvs,convert_t t))) env)) menv`;

val remove_pair_lem = Q.prove (
`(!f v. (\(x,y). f x y) v = f (FST v) (SND v)) ∧
 (!f v. (\(x,y,z). f x y z) v = f (FST v) (FST (SND v)) (SND (SND v)))`,
rw [] >>
PairCases_on `v` >>
rw []);

val check_convert_freevars = Q.prove (
`(!tvs uvs t. check_t tvs uvs t ⇒ (uvs = {}) ⇒ check_freevars tvs [] (convert_t t))`,
ho_match_mp_tac (fetch "-" "check_t_ind") >>
rw [check_freevars_def, check_t_def, convert_t_def] >>
fs [EVERY_MEM, MEM_MAP] >>
metis_tac []);

val check_t_more = Q.prove (
`(!t tvs. check_t tvs {} t ⇒ !uvs. check_t tvs uvs t) ∧
 (!ts tvs. EVERY (check_t tvs {}) ts ⇒ !uvs. EVERY (check_t tvs uvs) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >>
metis_tac []);

val infer_p_next_uvar_mono = Q.prove (
`(!cenv p st t env st'.
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!cenv ps st ts env st'.
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar)`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
metis_tac [DECIDE ``!(x:num) y z. x ≤ y ⇒ x ≤ y + z``,
           arithmeticTheory.LESS_EQ_TRANS]);

val infer_e_next_uvar_mono = Q.prove (
`(!menv cenv env e st st' t.
    (infer_e menv cenv env e st = (Success t, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!menv cenv env es st st' ts.
    (infer_es menv cenv env es st = (Success ts, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!menv cenv env pes t1 t2 st st'.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar) ∧
 (!menv cenv env funs st st' ts.
    (infer_funs menv cenv env funs st = (Success ts, st'))
    ⇒
    st.next_uvar ≤ st'.next_uvar)`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
metis_tac [infer_p_next_uvar_mono, arithmeticTheory.LESS_EQ_TRANS,
           pair_CASES,
           DECIDE ``!(x:num) y. x ≤ x + y``,
           DECIDE ``!(x:num) y. x + 1 ≤ y ⇒ x ≤ y``,
           DECIDE ``!(x:num) y z. x ≤ y ⇒ x ≤ y + z``]);

val infer_p_constraints = Q.prove (
`(!cenv p st t env st'.
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!cenv ps st ts env st'.
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
    (?ts'. pure_add_constraints st.subst ts' st'.subst))`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def]);

val infer_e_constraints = Q.prove (
`(!menv cenv env e st st' t.
    (infer_e menv cenv env e st = (Success t, st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!menv cenv env es st st' ts.
    (infer_es menv cenv env es st = (Success ts, st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!menv cenv env pes t1 t2 st st'.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst)) ∧
 (!menv cenv env funs st st' ts'.
    (infer_funs menv cenv env funs st = (Success ts', st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst))`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
TRY (cases_on `v'`) >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def, infer_p_constraints]);

val pure_add_constraints_wfs = Q.prove (
`!s1 ts s2.
  t_wfs s1 ∧
  pure_add_constraints s1 ts s2
  ⇒
  t_wfs s2`,
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_wfs]);

val infer_p_wfs = Q.prove (
`(!cenv p st t env st'.
    t_wfs st.subst ∧
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    t_wfs st'.subst) ∧
 (!cenv ps st ts env st'.
    t_wfs st.subst ∧
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
   t_wfs st'.subst)`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
prove_tac [pure_add_constraints_wfs]);

val infer_e_wfs = Q.prove (
`(!menv cenv env e st st' t.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!menv cenv env es st st' ts.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!menv cenv env pes t1 t2 st st'.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst) ∧
 (!menv cenv env funs st st' ts'.
    (infer_funs menv cenv env funs st = (Success ts', st')) ∧
    t_wfs st.subst
    ⇒
    t_wfs st'.subst)`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
fs [] >>
res_tac >>
imp_res_tac t_unify_wfs >>
fs [] >>
imp_res_tac pure_add_constraints_wfs >>
fs [] >>
cases_on `v'` >>
imp_res_tac infer_p_wfs >>
fs []);

val sub_completion_def = Define `
sub_completion tvs next_uvar s1 extra_constraints s2 =
  (pure_add_constraints s1 extra_constraints s2 ∧
   (count next_uvar SUBSET FDOM s2) ∧
   (!uv. uv ∈ FDOM s2 ⇒ check_t tvs {} (t_walkstar s2 (Infer_Tuvar uv))))`;

val sub_completion_unify = Q.prove (
`!st t1 t2 s1 n ts s2 n.
  (t_unify st.subst t1 t2 = SOME s1) ∧
  sub_completion n (st.next_uvar + 1) s1 ts s2
  ⇒
  sub_completion n st.next_uvar st.subst ((t1,t2)::ts) s2`,
rw [sub_completion_def, pure_add_constraints_def] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF, count_add1]);

val sub_completion_unify2 = Q.prove (
`!st t1 t2 s1 n ts s2 n s3 next_uvar.
  (t_unify s1 t1 t2 = SOME s2) ∧
  sub_completion n next_uvar s2 ts s3
  ⇒
  sub_completion n next_uvar s1 ((t1,t2)::ts) s3`,
rw [sub_completion_def, pure_add_constraints_def]);

val sub_completion_infer = Q.prove (
`!menv cenv env e st1 t st2 n ts2 s.
  (infer_e menv cenv env e st1 = (Success t, st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
rw [sub_completion_def, pure_add_constraints_append] >>
imp_res_tac infer_e_constraints >>
imp_res_tac infer_e_next_uvar_mono >>
qexists_tac `ts` >>
rw [] >|
[qexists_tac `st2.subst` >>
     rw [],
 full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF]]);

val sub_completion_add_constraints = Q.prove (
`!s1 ts1 s2 n next_uvar s2 s3 ts2.
  pure_add_constraints s1 ts1 s2 ∧
  sub_completion n next_uvar s2 ts2 s3
  ⇒
  sub_completion n next_uvar s1 (ts1++ts2) s3`,
induct_on `ts1` >>
rw [pure_add_constraints_def] >>
Cases_on `h` >>
fs [pure_add_constraints_def] >>
res_tac >>
fs [sub_completion_def] >>
rw [] >>
fs [pure_add_constraints_def, pure_add_constraints_append] >>
metis_tac []);

val sub_completion_more_vars = Q.prove (
`!m n1 n2 s1 ts s2.
  sub_completion m (n1 + n2) s1 ts s2 ⇒ sub_completion m n1 s1 ts s2`,
rw [sub_completion_def] >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF]);

val sub_completion_infer_es = Q.prove (
`!menv cenv env es st1 t st2 n ts2 s.
  (infer_es menv cenv env es st1 = (Success t, st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
induct_on `es` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
res_tac >>
imp_res_tac sub_completion_infer >>
metis_tac [APPEND_ASSOC]);

val sub_completion_apply = Q.prove (
`!n uvars s1 ts s2 t1 t2.
  (t_walkstar s1 t1 = t_walkstar s1 t2) ∧
  sub_completion n uvars s1 ts s2 
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
rw [sub_completion_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum mp_tac >>
Q.SPEC_TAC (`s1`, `s1`) >>
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
cases_on `h` >>
fs [pure_add_constraints_def] >>
fs [] >>
metis_tac [t_unify_apply2]);

val sub_completion_apply_list = Q.prove (
`!n uvars s1 ts s2 ts1 ts2.
  (MAP (t_walkstar s1) ts1 = MAP (t_walkstar s1) ts2) ∧
  sub_completion n uvars s1 ts s2 
  ⇒
  (MAP (t_walkstar s2) ts1 = MAP (t_walkstar s2) ts2)`,
induct_on `ts1` >>
rw [] >>
cases_on `ts2` >>
fs [] >>
metis_tac [sub_completion_apply]);

val sub_completion_wfs = Q.prove (
`!n uvars s1 ts s2.
  t_wfs s1 ∧
  sub_completion n uvars s1 ts s2 
  ⇒
  t_wfs s2`,
rw [sub_completion_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum mp_tac >>
Q.SPEC_TAC (`s1`, `s1`) >>
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
metis_tac [t_unify_wfs]);

val check_t_to_check_freevars = Q.prove (
`!tvs (n:num set) t. check_t tvs {} t ⇒ check_freevars tvs [] (convert_t t)`,
ho_match_mp_tac (fetch "-" "check_t_ind") >>
rw [check_t_def, check_freevars_def, convert_t_def, EVERY_MAP] >>
fs [EVERY_MEM]);

val sub_completion_check = Q.prove (
`!tvs m s uvar s' extra_constraints.
sub_completion m (uvar + tvs) s' extra_constraints s
⇒
EVERY (λn. check_freevars m [] (convert_t (t_walkstar s (Infer_Tuvar (uvar + n))))) (COUNT_LIST tvs)`,
induct_on `tvs` >>
rw [sub_completion_def, rich_listTheory.COUNT_LIST_SNOC, EVERY_SNOC] >>
fs [sub_completion_def] >|
[qpat_assum `!m' s. P m' s` match_mp_tac >>
     rw [] >>
     qexists_tac `s'` >>
     qexists_tac `extra_constraints` >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF],
 fs [SUBSET_DEF] >>
     `uvar+tvs < uvar + SUC tvs`
            by full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF] >>
     metis_tac [check_t_to_check_freevars]]);

val infer_deBruijn_inc0 = Q.prove (
`!(n:num) t. infer_deBruijn_inc 0 t = t`,
ho_match_mp_tac (fetch "-" "infer_deBruijn_inc_ind") >>
rw [infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []);

val infer_deBruijn_inc0_id = Q.prove (
`infer_deBruijn_inc 0 = (\x.x)`,
metis_tac [infer_deBruijn_inc0]);

val convert_inc = Q.prove (
`!t tvs tvs'. 
  check_t tvs' {} t
  ⇒
  (convert_t (infer_deBruijn_inc tvs t) = deBruijn_inc 0 tvs (convert_t t))`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
rw [check_t_def, convert_t_def, infer_deBruijn_inc_def, deBruijn_inc_def] >>
induct_on `ts` >>
fs [] >>
metis_tac []);

val t_walkstar_eqn1 = Q.prove (
`!s idx ts tc.
  t_wfs s ⇒ 
  (t_walkstar s (Infer_Tvar_db idx) = Infer_Tvar_db idx) ∧
  (t_walkstar s (Infer_Tapp ts tc) = Infer_Tapp (MAP (t_walkstar s) ts) tc)`,
rw [t_walkstar_eqn, t_walk_eqn]);

val check_t_subst = Q.prove (
`!t tvs s. 
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (convert_t t = convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t))`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
srw_tac [ARITH_ss] [check_t_def, convert_t_def, apply_subst_t_eqn] >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
fs [t_walkstar_eqn1, convert_t_def] >>
induct_on `ts` >>
rw []);

val db_subst_infer_subst_swap = Q.prove (
`(!t s tvs uvar n.
  t_wfs s ∧
  count (uvar + tvs) ⊆ FDOM s ∧
  (!uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  check_t tvs (FDOM s) t
  ⇒
  (convert_t
    (t_walkstar s
       (infer_deBruijn_subst
          (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))
          t)) =
   deBruijn_subst 0
    (MAP (convert_t o t_walkstar s)
       (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
    (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)))) ∧
 (!ts s tvs uvar n.
  t_wfs s ∧
  count (uvar + tvs) ⊆ FDOM s ∧
  (!uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  EVERY (\t. check_t tvs (FDOM s) t) ts ⇒
  (MAP (convert_t o
       t_walkstar s o
       infer_deBruijn_subst (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
      ts =
   MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))) o
       convert_t o 
       t_walkstar (infer_deBruijn_inc tvs o_f s))
      ts))`,
ho_match_mp_tac infer_t_induction >>
rw [convert_t_def, deBruijn_subst_def, EL_MAP, t_walkstar_eqn1,
    infer_deBruijn_subst_def, MAP_MAP_o, combinTheory.o_DEF, check_t_def,
    rich_listTheory.LENGTH_COUNT_LIST] >|
[`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     fs [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def,
         rich_listTheory.LENGTH_COUNT_LIST] >>
     fs [LENGTH_MAP, el_map_count, rich_listTheory.EL_COUNT_LIST],
 `t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     fs [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def, MAP_MAP_o, 
         combinTheory.o_DEF] >>
     metis_tac [],
 res_tac >>
     imp_res_tac convert_inc >>
     rw [walkstar_inc] >>
     metis_tac [subst_inc_cancel, arithmeticTheory.ADD,
                deBruijn_inc0,
                rich_listTheory.LENGTH_COUNT_LIST, LENGTH_MAP],
 metis_tac [],
 metis_tac []]);

val subst_infer_subst_swap = Q.prove (
`(!t tvs s uvar.
  t_wfs s ⇒
  (t_walkstar s (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs)))) t)
   =
   infer_type_subst (ZIP (tvs, MAP (λn. t_walkstar s (Infer_Tuvar (uvar + n))) (COUNT_LIST (LENGTH tvs)))) t)) ∧
 (!ts tvs s uvar.
  t_wfs s ⇒
  (MAP (t_walkstar s) (MAP (infer_type_subst (ZIP (tvs, MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST (LENGTH tvs))))) ts)
   =
   MAP (infer_type_subst (ZIP (tvs, MAP (λn. t_walkstar s (Infer_Tuvar (uvar + n))) (COUNT_LIST (LENGTH tvs))))) ts))`, 
ho_match_mp_tac t_induction >>
rw [type_subst_def, infer_type_subst_def, t_walkstar_eqn1] >|
[full_case_tac >>
     full_case_tac >>
     rw [t_walkstar_eqn1] >>
     fs [lookup_notin] >>
     imp_res_tac lookup_in2 >>
     fs [MAP_ZIP, rich_listTheory.LENGTH_COUNT_LIST] >>
     REPEAT (pop_assum mp_tac) >>
     Q.SPEC_TAC (`uvar`,`uvar`) >>
     induct_on `tvs` >>
     fs [lookup_def] >>
     rw [rich_listTheory.COUNT_LIST_def, MAP_MAP_o, combinTheory.o_DEF] >>
     qpat_assum `!uvar. P uvar` (mp_tac o Q.SPEC `SUC uvar`) >>
     rw [] >>
     fs [DECIDE ``!(x:num) y. (x + SUC y) = ((SUC x) + y)``],
 metis_tac []]);

val convert_t_subst = Q.prove (
`(!t tvs ts'. 
    (LENGTH tvs = LENGTH ts') ∧
    check_freevars 0 tvs t ⇒
    convert_t (infer_type_subst (ZIP (tvs,ts')) t) = 
    type_subst (ZIP (tvs, MAP convert_t ts')) t) ∧
 (!ts tvs ts'. 
    (LENGTH tvs = LENGTH ts') ∧
    EVERY (check_freevars 0 tvs) ts ⇒
    MAP convert_t (MAP (infer_type_subst (ZIP (tvs,ts'))) ts) = 
    MAP (type_subst (ZIP (tvs, MAP convert_t ts'))) ts)`,
ho_match_mp_tac t_induction >>
rw [check_freevars_def, convert_t_def, type_subst_def, infer_type_subst_def] >|
[full_case_tac >>
     full_case_tac >>
     fs [lookup_notin] >>
     imp_res_tac lookup_in2 >>
     REPEAT (pop_assum mp_tac) >>
     rw [MAP_ZIP] >>
     REPEAT (pop_assum mp_tac) >>
     Q.SPEC_TAC (`tvs`,`tvs`) >>
     induct_on `ts'` >>
     rw [] >>
     cases_on `tvs` >>
     fs [] >>
     metis_tac [optionTheory.SOME_11],
 metis_tac []]);

val binop_tac =
imp_res_tac infer_e_wfs >>
fs [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer >>
fs [] >>
res_tac >>
fs []  >>
imp_res_tac t_unify_apply >>
imp_res_tac sub_completion_apply >>
fs [] >>
imp_res_tac t_unify_wfs >>
imp_res_tac sub_completion_wfs >>
fs [t_walkstar_eqn, t_walk_eqn, convert_t_def] >>
rw [type_op_cases, 
    Tint_def, Tbool_def, Tref_def, Tfn_def, Tunit_def] >>
metis_tac [MAP];

val tenv_inv_def = Define `
tenv_inv s env tenv =
  (!x tvs t.
    (lookup x env = SOME (tvs,t)) ⇒
    check_t tvs (FDOM s) t ∧
    ((lookup_tenv x 0 tenv = 
      SOME (tvs, convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)))))`;

val check_menv_lookup = Q.prove (
`!menv mn n env tvs t.
  check_menv menv ∧
  (lookup mn menv = SOME env) ∧
  (lookup n env = SOME (tvs,t))
  ⇒
  check_t tvs {} t`,
induct_on `menv` >>
rw [lookup_def, check_t_def, check_menv_def] >>
PairCases_on `h` >>
fs [] >>
cases_on `h0 = mn` >>
fs [] >>
rw [] >|
[induct_on `env` >>
     fs [lookup_def] >>
     rw [] >>
     PairCases_on `h` >>
     fs [] >>
     cases_on `h0 = n` >>
     fs [],
 metis_tac [check_menv_def]]);

val check_cenv_lookup = Q.prove (
`!cenv cn tvs ts t.
  check_cenv cenv ∧
  (lookup cn cenv = SOME (tvs,ts,t))
  ⇒
  EVERY (check_freevars 0 tvs) ts`,
induct_on `cenv` >>
rw [] >>
PairCases_on `h` >>
fs [check_cenv_def] >>
every_case_tac >>
rw [] >>
metis_tac []);

(*
val infer_e_sound = Q.prove (
`(!menv cenv env e st st' ext tenv t extra_constraints s.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    type_e (convert_menv menv) cenv tenv e 
           (convert_t (t_walkstar s t))) ∧
 (!menv cenv env es st st' ext tenv ts extra_constraints s.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    type_es (convert_menv menv) cenv tenv es 
            (MAP (convert_t o t_walkstar s) ts)) ∧
 (!menv cenv env pes t1 t2 st st' tenv ext extra_constraints s.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    T) ∧
 (!menv cenv env funs st st' ext tenv extra_constraints s ts.
    (infer_funs menv cenv env funs st = (Success ts, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    ?env'. type_funs (convert_menv menv) cenv tenv funs env')`,

ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem] >>
rw [check_t_def] >>
fs [bind_def, check_env_def, check_t_def] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [Tbool_def, Tint_def, Tunit_def] >|
[(* Raise *)
     fs [sub_completion_def, flookup_thm, count_add1, SUBSET_DEF] >>
     `st.next_uvar < st.next_uvar + 1` by decide_tac >>
     metis_tac [IN_INSERT, check_convert_freevars, prim_recTheory.LESS_REFL],
 (* Handle *)
     binop_tac,
 (* Handle *)
     `tenv_inv s ((x,0,Infer_Tapp [] TC_int)::env) 
                 (Bind_name x 0 
                            (convert_t (t_walkstar s (Infer_Tapp [] TC_int))) 
                            tenv)`
             by (fs [tenv_inv_def, lookup_tenv_def] >>
                 rw [deBruijn_inc0, infer_deBruijn_inc0] >>
                 rw [infer_deBruijn_inc0_id, o_f_id] >>
                 fs [sub_completion_def, check_t_def] >>
                 metis_tac []) >>
     `num_tvs tenv = num_tvs (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tapp [] TC_int))) tenv)`
             by rw [num_tvs_def] >>
     rw [bind_tenv_def] >>
     binop_tac,
 (* Lit bool *)
     binop_tac,
 (* Lit int *)
     binop_tac,
 (* Lit unit *)
     binop_tac,
 (* Var short *)
     rw [t_lookup_var_id_def] >>
     `?tvs t. v' = (tvs, t)` 
                by (PairCases_on `v'` >>
                    rw []) >>
     rw [] >>
     qexists_tac `convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)` >>
     qexists_tac `MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST tvs))` >>
     rw [] >|
     [fs [sub_completion_def] >>
          rw [] >>
          `check_t tvs (FDOM s) t` by 
                     (fs [tenv_inv_def] >>
                      res_tac) >>
          metis_tac [db_subst_infer_subst_swap, pure_add_constraints_wfs],
      rw [EVERY_MAP] >>
          metis_tac [sub_completion_check, FST],
      rw [rich_listTheory.LENGTH_COUNT_LIST] >>
          fs [tenv_inv_def]],
 (* Var long *)
     rw [t_lookup_var_id_def] >>
     `?tvs t. v' = (tvs, t)` 
                by (PairCases_on `v'` >>
                    rw []) >>
     rw [] >>
     qexists_tac `convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)` >>
     qexists_tac `MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST tvs))` >>
     rw [] >|
     [fs [sub_completion_def] >>
          rw [] >>
          `check_t tvs (FDOM s) t` by 
                     (metis_tac [check_menv_lookup, check_t_more]) >>
          metis_tac [db_subst_infer_subst_swap, pure_add_constraints_wfs],
      rw [EVERY_MAP] >>
          metis_tac [sub_completion_check, FST],
      rw [rich_listTheory.LENGTH_COUNT_LIST] >>
          fs [convert_menv_def, check_menv_def] >>
          `lookup mn (MAP (λ(mn,env). (mn,MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env)) menv) =
           SOME (MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env')`
                    by metis_tac [lookup_map] >>
          rw [] >>
          `lookup n (MAP (λ(x,y). (x,(\z. FST z,convert_t (SND z)) y)) env') =
           SOME ((\y. FST y,convert_t (SND y)) (tvs,t))`
                    by (match_mp_tac lookup_map >>
                        rw[]) >>
          fs [LAMBDA_PROD] >>
          `check_t tvs {} t`
                    by (imp_res_tac lookup_in >>
                        fs [MEM_MAP, EVERY_MEM] >>
                        rw [] >>
                        PairCases_on `y'` >>
                        PairCases_on `y''''` >>
                        PairCases_on `y'''` >>
                        PairCases_on `y'''''` >>
                        fs [] >>
                        rw [] >>
                        res_tac >>
                        fs [] >>
                        res_tac >>
                        fs []) >>
          metis_tac [check_t_subst, sub_completion_wfs]],
 (* Con *)
     `?tvs ts t. v' = (tvs, ts, t)` by (PairCases_on `v'` >> rw []) >>
     rw [] >>
     fs [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs, pure_add_constraints_wfs] >>
     rw [convert_t_def, t_walkstar_eqn1, MAP_MAP_o, combinTheory.o_DEF,
         EVERY_MAP, rich_listTheory.LENGTH_COUNT_LIST] >-
     metis_tac [sub_completion_check] >>
     `type_es (convert_menv menv) cenv tenv es (MAP (convert_t o t_walkstar s) ts'')`
             by (imp_res_tac sub_completion_add_constraints >>
                 `sub_completion (num_tvs tenv) st'''.next_uvar st'''.subst
                        (ZIP
                           (ts'',
                            MAP
                              (infer_type_subst
                                 (ZIP
                                    (tvs,
                                     MAP (λn. Infer_Tuvar (st'''.next_uvar + n))
                                       (COUNT_LIST (LENGTH tvs))))) ts) ++
                         extra_constraints) s`
                                   by metis_tac [sub_completion_more_vars] >>
                 imp_res_tac sub_completion_infer_es >>
                 metis_tac []) >>
     imp_res_tac pure_add_constraints_apply >>
     pop_assum mp_tac >>
     rw [MAP_ZIP] >>
     imp_res_tac sub_completion_apply_list >>
     pop_assum mp_tac >>
     rw [subst_infer_subst_swap] >>
     `EVERY (check_freevars 0 tvs) ts` by metis_tac [check_cenv_lookup] >>
     metis_tac [convert_t_subst, rich_listTheory.LENGTH_COUNT_LIST, LENGTH_MAP,
                MAP_MAP_o, combinTheory.o_DEF],
 (* Fun *)

     `t_wfs s` by metis_tac [stupid_record_thing,sub_completion_wfs, infer_e_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tfn_def] >|


 (*
     `tenv_inv s ((x,0,Infer_Tuvar st.next_uvar)::env) 
                 (Bind_name x 0 
                            (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) 
                            tenv)`
             by (fs [tenv_inv_def, lookup_tenv_def] >>
                 rw [deBruijn_inc0, infer_deBruijn_inc0] >>
                 rw [infer_deBruijn_inc0_id, o_f_id] >>
                 fs [sub_completion_def, check_t_def] >>
                 metis_tac []) >>
     `num_tvs tenv = num_tvs (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tapp [] TC_int))) tenv)`
             by rw [num_tvs_def] >>
     rw [bind_tenv_def] >>
     binop_tac,
     *)
     all_tac,
 (* Opref *)
     rw [type_uop_cases, Tref_def] >>
     binop_tac,
 (* Opderef *)
     all_tac,
     (*
     rw [type_uop_cases, Tref_def] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_unify >>
     imp_res_tac sub_completion_apply >>
     fs [apply_subst_t_eqn] >>
     metis_tac [convert_t_def, MAP],
     *)
 (* Opn *)
     binop_tac,
 (* Opb *)
     binop_tac,
 (* Equality *)
     binop_tac, 
 (* Opapp *)
     all_tac,
 (* Opassign *) 
     all_tac, 
 (* Log *)
     binop_tac,
 (* Log *)
     binop_tac,
 (* If *)
     binop_tac,
 (* If *)
     binop_tac,
 (* If *)
     binop_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac]

 *)

 (*
(* Fn case *)
rw [Tfn_def]
 
(* Poly LET case (r 15;) *)
`?tvs t_gen. generalise n 0 t1' = (tvs,t_gen)` 
        by (cases_on `generalise n 0 t1'` >>
            rw []) >>
DISJ1_TAC >>
fs [apply_subst_thm, get_next_uvar_def] >>
rw [] >>
fs [st_ex_bind_success] >>
rw [] >>
qexists_tac `convert_t (apply_subst_t sub t1)` >>
qexists_tac `tvs` >>
rw [] >|
[qpat_assum `∀st''''' st'''''' sub' tenv' t'.
        (infer_e menv cenv env e st''''' = (Success t',st'''''')) ∧
        tenv_rel sub' env tenv' ∧ infer_invariant st'''''' sub' ⇒
        type_e (convert_menv menv) cenv tenv' e
          (convert_t (apply_subst_t sub' t'))`
            match_mp_tac >>
     qexists_tac `st` >>
     qexists_tac `st'''` >>
     rw [] >|
     [all_tac,
      fs [get_next_uvar_def] >>
          rw [] >>
          fs [st_ex_bind_success] >>
          imp_res_tac apply_subst_st >>
          rw []

 qpat_assum `∀num_gen t1'' st''''' st'''''' sub' tenv' t'.
        (infer_e menv cenv (bind x (num_gen,t1'') env) e' st''''' =
         (Success t',st'''''')) ∧
        tenv_rel sub' (bind x (num_gen,t1'') env) tenv' ∧
        infer_invariant st'''''' sub' ⇒
        type_e (convert_menv menv) cenv tenv' e'
          (convert_t (apply_subst_t sub' t'))` match_mp_tac >>
     qexists_tac `tvs` >>
     qexists_tac `t_gen` >>
     qexists_tac `st''''` >>
     qexists_tac `st'` >>
     rw [] >>
     fs [st_ex_bind_success] >>
     rw [Once tenv_rel_cases, bind_def, bind_tenv_def]
     *)

val _ = export_theory ();
