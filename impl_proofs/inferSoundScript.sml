open preamble;
open rich_listTheory;
open LibTheory TypeSystemTheory AstTheory SemanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open typeSysPropsTheory;

val o_f_id = Q.prove (
`!m. (\x.x) o_f m = m`,
rw [fmap_EXT]);

val lookup_tenv_inc = Q.prove (
`!x inc tenv tvs t inc2.
  (lookup_tenv x inc tenv = SOME (tvs,t))
  ⇒
  (lookup_tenv x (inc2 + inc) tenv = SOME (tvs, deBruijn_inc tvs inc2 t))`,
induct_on `tenv` >>
rw [lookup_tenv_def] >>
rw [deBruijn_inc_deBruijn_inc] >>
metis_tac [arithmeticTheory.ADD_ASSOC]);

val deBruijn_inc_inc = Q.prove (
`(!t inc1 inc2.
  deBruijn_inc inc2 inc1 (deBruijn_inc 0 inc2 t) = deBruijn_inc 0 (inc1 + inc2) t) ∧
 (!ts inc1 inc2.
  MAP (deBruijn_inc inc2 inc1 o deBruijn_inc 0 inc2) ts = MAP (deBruijn_inc 0 (inc1 + inc2)) ts)`,
Induct >>
rw [deBruijn_inc_def, MAP_MAP_o] >-
decide_tac >-
decide_tac >>
metis_tac []);

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

val infer_deBruijn_inc_inc = Q.prove (
`(!t inc1 inc2.
  (infer_deBruijn_inc inc1 o infer_deBruijn_inc inc2) t = infer_deBruijn_inc (inc1 + inc2) t) ∧
 (!ts inc1 inc2.
  MAP (infer_deBruijn_inc inc1 o infer_deBruijn_inc inc2) ts = MAP (infer_deBruijn_inc (inc1 + inc2)) ts)`,
Induct >>
rw [infer_deBruijn_inc_def, MAP_MAP_o] >-
decide_tac >>
metis_tac []);

val free_uvars_def = tDefine "free_uvars" `
(free_uvars (Infer_Tvar_db n) = {}) ∧
(free_uvars (Infer_Tuvar m) = {m}) ∧
(free_uvars (Infer_Tapp ts tc) =  BIGUNION (set (MAP free_uvars ts)))`
(WF_REL_TAC `measure infer_t_size` >>
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

val t_unify_wfs = Q.store_thm ("t_unify_wfs",
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
ONCE_REWRITE_TAC [COUNT_LIST_def] >>
fs []);

val el_map_count = Q.prove (
`!n f m. n < m ⇒ EL n (MAP f (COUNT_LIST m)) = f n`,
induct_on `n` >>
rw [] >>
cases_on `m` >>
fs [COUNT_LIST_def] >>
`n < SUC n'` by decide_tac >>
res_tac >>
fs [COUNT_LIST_def] >>
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
rw [st_ex_return_success, Once n_fresh_uvar_def, COUNT_LIST_SNOC,
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

val add_constraint_success = Q.store_thm ("add_constraint_success",
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

val _ = save_thm ("success_eqns", success_eqns);

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
  EVERY (\(x, (tvs,t)). check_t tvs uvars t) env`;

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

val check_t_more2 = Q.prove (
`(!t tvs uvs. check_t tvs uvs t ⇒ !tvs'. check_t (tvs' + tvs) uvs t) ∧
 (!ts tvs uvs. EVERY (check_t tvs uvs) ts ⇒ !tvs'. EVERY (check_t (tvs' + tvs) uvs) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >-
decide_tac >>
metis_tac []);

val check_t_more3 = Q.prove (
`(!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. check_t tvs (count (uvs + uvs')) t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. EVERY (check_t tvs (count (uvs + uvs'))) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def] >-
metis_tac [] >>
decide_tac);

val check_t_more4 = Q.prove (
`(!t uvs tvs. check_t tvs (count uvs) t ⇒ !uvs'. uvs ≤ uvs' ⇒ check_t tvs (count uvs') t) ∧
 (!ts uvs tvs. EVERY (check_t tvs (count uvs)) ts ⇒ !uvs'. uvs ≤ uvs' ⇒ EVERY (check_t tvs (count uvs')) ts)`,
ho_match_mp_tac infer_t_induction >>
srw_tac [ARITH_ss] [check_t_def] >>
metis_tac []);

val check_t_more5 = Q.prove (
`(!t uvs tvs. check_t tvs uvs t ⇒ !uvs'. uvs ⊆ uvs' ⇒ check_t tvs uvs' t) ∧
 (!ts uvs tvs. EVERY (check_t tvs uvs) ts ⇒ !uvs'. uvs ⊆ uvs' ⇒ EVERY (check_t tvs uvs') ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, SUBSET_DEF] >>
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

val pure_add_constraints_wfs = Q.store_thm ("pure_add_constraints_wfs",
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

val infer_p_wfs = Q.store_thm ("infer_p_wfs",
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

val infer_e_wfs = Q.store_thm ("infer_e_wfs",
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

val sub_completion_infer_p = Q.prove (
`(!cenv p st t env st' tvs extra_constraints s.
    (infer_p cenv p st = (Success (t,env), st')) ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    ?ts. sub_completion tvs st.next_uvar st.subst (ts++extra_constraints) s) ∧
 (!cenv ps st ts env st' tvs extra_constraints s.
    (infer_ps cenv ps st = (Success (ts,env), st')) ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    ?ts. sub_completion tvs st.next_uvar st.subst (ts++extra_constraints) s)`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem] >>
fs [] >|
[metis_tac [APPEND, sub_completion_more_vars],
 metis_tac [APPEND, sub_completion_more_vars],
 metis_tac [APPEND, sub_completion_more_vars],
 metis_tac [APPEND, sub_completion_more_vars],
 imp_res_tac sub_completion_add_constraints >>
     PairCases_on `v''` >>
     fs [] >>
     metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars],
 PairCases_on `v'` >>
     fs [] >>
     metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars],
 metis_tac [APPEND, sub_completion_more_vars],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [] >>
     metis_tac [APPEND_ASSOC]]);
 
val sub_completion_infer_pes = Q.prove (
`!menv cenv env pes t1 t2 st1 t st2 n ts2 s.
  (infer_pes menv cenv env pes t1 t2 st1 = (Success (), st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
induct_on `pes` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
PairCases_on `v'` >>
fs [infer_e_def, success_eqns] >>
rw [] >>
res_tac >>
fs [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer >>
fs [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer_p >>
fs [] >>
metis_tac [APPEND, APPEND_ASSOC]);

val sub_completion_infer_funs = Q.prove (
`!menv cenv env funs st1 t st2 n ts2 s.
  (infer_funs menv cenv env funs st1 = (Success t, st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
induct_on `funs` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
res_tac >>
imp_res_tac sub_completion_infer >>
fs [] >>
metis_tac [sub_completion_more_vars, APPEND_ASSOC]);

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
rw [sub_completion_def, COUNT_LIST_SNOC, EVERY_SNOC] >>
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
  (t = (t_walkstar (infer_deBruijn_inc tvs o_f s) t))`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
srw_tac [ARITH_ss] [check_t_def, apply_subst_t_eqn] >>
`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
fs [t_walkstar_eqn1] >>
induct_on `ts` >>
rw []);

val check_t_deBruijn_inc2 = Q.prove (
`!inc t. check_t tvs {} t ⇒ check_t (inc + tvs) {} (infer_deBruijn_inc inc t)`,
ho_match_mp_tac (fetch "-" "infer_deBruijn_inc_ind") >>
rw [check_t_def, infer_deBruijn_inc_def] >>
fs [EVERY_MAP, EVERY_MEM]);

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
    LENGTH_COUNT_LIST] >|
[`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     fs [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def,
         LENGTH_COUNT_LIST] >>
     fs [LENGTH_MAP, el_map_count, EL_COUNT_LIST],
 `t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     fs [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def, MAP_MAP_o, 
         combinTheory.o_DEF] >>
     metis_tac [],
 res_tac >>
     imp_res_tac convert_inc >>
     rw [walkstar_inc] >>
     metis_tac [subst_inc_cancel, arithmeticTheory.ADD,
                deBruijn_inc0,
                LENGTH_COUNT_LIST, LENGTH_MAP],
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
     fs [MAP_ZIP, LENGTH_COUNT_LIST] >>
     REPEAT (pop_assum mp_tac) >>
     Q.SPEC_TAC (`uvar`,`uvar`) >>
     induct_on `tvs` >>
     fs [lookup_def] >>
     rw [COUNT_LIST_def, MAP_MAP_o, combinTheory.o_DEF] >>
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

val tenv_inv_def = Define `
tenv_inv s env tenv =
  (!x tvs t.
   (lookup x env = SOME (tvs,t)) ⇒
   ((lookup_tenv x 0 tenv = 
     SOME (tvs, convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)))))`;

val check_t_deBruijn_inc = Q.prove (
`!inc t. check_t 0 UNIV t ⇒ (infer_deBruijn_inc inc t = t)`,
ho_match_mp_tac (fetch "-" "infer_deBruijn_inc_ind") >>
rw [check_t_def, infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []);

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

val infer_p_check_t = Q.prove (
`(!cenv p st t env st'.
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    EVERY (\(x,t). check_t 0 (count st'.next_uvar) t) env ∧
    check_t 0 (count st'.next_uvar) t) ∧
 (!cenv ps st ts env st'.
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
    EVERY (\(x,t). check_t 0 (count st'.next_uvar) t) env ∧
    EVERY (check_t 0 (count st'.next_uvar)) ts)`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem] >>
rw [check_t_def] >|
[PairCases_on `v''` >>
     fs [remove_pair_lem, EVERY_MEM] >>
     rw [] >>
     metis_tac [check_t_more3],
 PairCases_on `v''` >>
     fs [remove_pair_lem, EVERY_MAP, EVERY_MEM, MEM_COUNT_LIST] >>
     rw [check_t_def] >>
     decide_tac,
 PairCases_on `v'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `v'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [] >>
     metis_tac [],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [remove_pair_lem, EVERY_MEM] >>
     rw [] >>
     `?n. st'.next_uvar = st''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [] >>
     `?n. st'.next_uvar = st''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     fs [] >>
     `?n. st'.next_uvar = st''.next_uvar + n`
                 by (imp_res_tac infer_p_next_uvar_mono >>
                     qexists_tac `st'.next_uvar - st''.next_uvar` >>
                     srw_tac [ARITH_ss] []) >>
     metis_tac [check_t_more3]]);

val check_env_more = Q.prove (
`!uvs env. check_env (count uvs) env ⇒ !uvs'. uvs ≤ uvs' ⇒ check_env (count uvs') env`,
rw [check_env_def, EVERY_MEM] >>
PairCases_on `e` >>
rw [] >>
res_tac >>
fs [] >>
metis_tac [check_t_more4]);

val check_env_bind = Q.prove (
`!uvs x tvs t env.
  check_env uvs (bind x (tvs,t) env) = (check_t tvs uvs t ∧ check_env uvs env)`,
rw [check_env_def, bind_def]);

val check_env_merge = Q.prove (
`!uvs env1 env2. check_env uvs (merge env1 env2) = (check_env uvs env1 ∧ check_env uvs env2)`,
rw [check_env_def, merge_def]);

val check_env_letrec_lem = Q.prove (
`∀uvs funs uvs' n.
  check_env (count uvs) (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (uvs' + n)) (COUNT_LIST (LENGTH funs)))) =
  ((funs = []) ∨ (uvs' + LENGTH funs ≤ uvs))`,
induct_on `funs` >>
rw [COUNT_LIST_def, check_env_def] >>
cases_on `funs` >>
fs [COUNT_LIST_def, check_env_def] >>
PairCases_on `h` >>
rw [check_t_def] >-
decide_tac >>
rw [] >>
PairCases_on `h'` >>
fs [check_t_def] >>
eq_tac >>
srw_tac [ARITH_ss] [] >>
fs [MAP_MAP_o, combinTheory.o_DEF] >|
[qpat_assum `!x. P x` (mp_tac o Q.SPECL [`uvs`, `uvs' + 1`]) >>
     rw [] >>
     fs [DECIDE ``SUC (SUC x) + y = y + 1 + SUC x``] >>
     decide_tac,
 qpat_assum `!x. P x` (mp_tac o Q.SPECL [`uvs`, `uvs' + 1`]) >>
     rw [] >>
     fs [DECIDE ``SUC (SUC x) + y = y + 1 + SUC x``,
         DECIDE ``x + (SUC (SUC y)) = x + 1 + SUC y``] >>
     metis_tac []]);

val ckeck_t_infer_db_subst = Q.prove (
`(!t uvs tvs.
   check_t 0 (count (uvs + tvs)) (infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs)) t)
   =
   check_t tvs (count (uvs + tvs)) t) ∧
 (!ts uvs tvs.
   EVERY (check_t 0 (count (uvs + tvs)) o infer_deBruijn_subst (MAP (\n. Infer_Tuvar (uvs + n)) (COUNT_LIST tvs))) ts
   =
   EVERY (check_t tvs (count (uvs + tvs))) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, infer_deBruijn_subst_def, LENGTH_COUNT_LIST, 
    EL_MAP, EL_COUNT_LIST, EVERY_MAP] >>
metis_tac []);

val check_env_lookup = Q.prove (
`!uvs n env tvs t.
  check_env uvs env ∧
  (lookup n env = SOME (tvs,t))
  ⇒
  check_t tvs uvs t`,
induct_on `env` >>
rw [check_t_def, lookup_def] >>
PairCases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
rw [] >>
fs [check_env_bind, GSYM bind_def] >>
metis_tac []);

val infer_e_check_t = Q.prove (
`(!menv cenv env e st st' t.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    check_menv menv ∧
    check_env (count st.next_uvar) env
    ⇒
    check_t 0 (count st'.next_uvar) t) ∧
 (!menv cenv env es st st' ts.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    check_menv menv ∧
    check_env (count st.next_uvar) env
    ⇒
    EVERY (check_t 0 (count st'.next_uvar)) ts) ∧
 (!menv cenv env pes t1 t2 st st'.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    check_menv menv ∧
    check_env (count st.next_uvar) env
    ⇒
    T) ∧
 (!menv cenv env funs st st' ts'.
    (infer_funs menv cenv env funs st = (Success ts', st')) ∧
    check_menv menv ∧
    check_env (count st.next_uvar) env
    ⇒
    EVERY (check_t 0 (count st'.next_uvar)) ts')`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem] >>
fs [check_t_def] >>
imp_res_tac infer_e_next_uvar_mono >>
fs [EVERY_MAP, check_t_def, check_env_bind, check_env_merge, ckeck_t_infer_db_subst] >|
[metis_tac [check_t_more4],
 PairCases_on `v'` >>
     imp_res_tac check_env_lookup >>
     rw [] >>
     metis_tac [check_t_more3],
 PairCases_on `v'` >>
     imp_res_tac check_menv_lookup >>
     rw [] >>
     metis_tac [check_t_more],
 rw [EVERY_MEM, MEM_COUNT_LIST] >>
     decide_tac,
 srw_tac [ARITH_ss] [] >>
     res_tac >>
     fs [check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``],
 metis_tac [check_t_more4],
 res_tac >>
     fs [] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4],
 decide_tac,
 res_tac >>
     fs [check_t_def] >>
     metis_tac [check_env_more, DECIDE ``x:num ≤ x + 1``],
 res_tac >>
     fs [check_env_merge, check_env_letrec_lem] >>
     metis_tac [check_env_more, DECIDE ``x + y ≤ z ⇒ x ≤ z:num``],
 res_tac >>
     fs [] >>
     metis_tac [arithmeticTheory.LESS_EQ_TRANS, check_env_more, check_t_more4],
 srw_tac [ARITH_ss] [] >>
     res_tac >>
     fs [check_t_def] >>
     metis_tac [check_env_more, check_t_more4, DECIDE ``x ≤ x + 1:num``]]);

val tenv_inv_extend = Q.prove (
`!s x tvs t env t' tenv.
  tenv_inv s env tenv 
  ⇒
  tenv_inv s ((x,tvs,t)::env) (bind_tenv x tvs (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)) tenv)`,
rw [tenv_inv_def] >>
every_case_tac >>
rw [] >>
rw [lookup_tenv_def, bind_tenv_def, deBruijn_inc0] >>
metis_tac []);

val tenv_inv_extend0 = Q.prove (
`!s x t env tenv.
  tenv_inv s env tenv 
  ⇒
  tenv_inv s ((x,0,t)::env) (bind_tenv x 0 (convert_t (t_walkstar s t)) tenv)`,
rw [] >>
`infer_deBruijn_inc 0 o_f s = s` by rw [GSYM fmap_EQ_THM, infer_deBruijn_inc0] >>
metis_tac [tenv_inv_extend]);

val tenv_inv_letrec_merge = Q.prove (
`!funs tenv' env tenv st s.
  tenv_inv s env tenv 
  ⇒
  tenv_inv s (merge (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs)))) env)
             (bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)))) tenv)`,
induct_on `funs` >>
rw [COUNT_LIST_def, merge_def, bind_var_list_def] >>
PairCases_on `h` >>
rw [bind_var_list_def] >>
match_mp_tac tenv_inv_extend0 >>
fs [merge_def] >>
rw [check_t_def] >>
res_tac >>
pop_assum (mp_tac o Q.SPEC `st with next_uvar := st.next_uvar + 1`) >>
strip_tac >>
fs [] >>
metis_tac [MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = x + 1 + y``]);

val convert_env_def = Define `
convert_env s env = MAP (\(x,t). (x, convert_t (t_walkstar s t))) env`;

val tenv_inv_merge = Q.prove (
`!s x uv env env' tenv. 
  tenv_inv s env tenv
  ⇒
  tenv_inv s (merge (MAP (λ(n,t). (n,0,t)) env') env) (bind_var_list 0 (convert_env s env') tenv)`,
induct_on `env'` >>
rw [merge_def, convert_env_def, bind_var_list_def] >>
res_tac >>
fs [tenv_inv_def] >>
rw [] >>
PairCases_on `h` >>
fs [] >>
cases_on `h0 = x` >>
fs [] >>
rw [bind_var_list_def, bind_tenv_def, lookup_def, lookup_tenv_def,
    deBruijn_inc0, infer_deBruijn_inc0_id, o_f_id] >>
fs [merge_def] >>
res_tac >>
metis_tac [convert_env_def]);

val letrec_lemma = Q.prove (
`!funs funs_ts s st. 
  (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)) =
   MAP (\t. convert_t (t_walkstar s t)) funs_ts)
  ⇒
  (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs))) =
   MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts)`,
induct_on `funs` >>
rw [] >>
cases_on `funs_ts` >>
fs [COUNT_LIST_def] >>
rw [] >|
[PairCases_on `h` >>
     rw [],
 qpat_assum `!x. P x` match_mp_tac >>
     qexists_tac `st with next_uvar := st.next_uvar + 1` >>
     fs [MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = x + 1 + y``]]);

val check_t_walkstar = Q.prove (
`(!t tvs s.
    t_wfs s ∧
    check_t 0 (FDOM s) t ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t tvs ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    check_t tvs {} (t_walkstar s t)) ∧
 (!ts tvs s.
    t_wfs s ∧
    EVERY (check_t 0 (FDOM s)) ts ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t tvs ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    EVERY (check_t tvs {} o t_walkstar s) ts)`,
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, t_walkstar_eqn1, EVERY_MAP] >>
metis_tac []);

val infer_funs_length = Q.prove (
`!menv cenv env funs ts st1 st2.
  (infer_funs menv cenv env funs st1 = (Success ts, st2)) ⇒
  (LENGTH funs = LENGTH ts)`,
induct_on `funs` >>
rw [infer_e_def, success_eqns] >>
rw [] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
rw [] >>
metis_tac []);

val map_zip_lem = Q.prove (
`!funs ts. 
  (LENGTH funs = LENGTH ts)
  ⇒
  (MAP (λx. FST ((λ((x',y,z),t). (x',convert_t (t_walkstar s t))) x)) (ZIP (funs,ts))
   =
   MAP FST funs)`,
induct_on `funs` >>
rw [] >>
cases_on `ts` >>
fs [] >>
PairCases_on `h` >>
rw []);

val type_pes_def = Define `
type_pes menv cenv tenv pes t1 t2 =
  ∀x::set pes.
    (λ(p,e).
       ∃tenv'.
         ALL_DISTINCT (pat_bindings p []) ∧
         type_p (num_tvs tenv) cenv p t1 tenv' ∧
         type_e menv cenv (bind_var_list 0 tenv' tenv) e t2) x`;

val type_pes_cons = Q.prove (
`!menv cenv tenv p e pes t1 t2.
  type_pes menv cenv tenv ((p,e)::pes) t1 t2 =
  (ALL_DISTINCT (pat_bindings p []) ∧
   (?tenv'.
       type_p (num_tvs tenv) cenv p t1 tenv' ∧
       type_e menv cenv (bind_var_list 0 tenv' tenv) e t2) ∧
   type_pes menv cenv tenv pes t1 t2)`,
rw [type_pes_def, RES_FORALL] >>
eq_tac >>
rw [] >>
rw [] >|
[pop_assum (mp_tac o Q.SPEC `(p,e)`) >>
     rw [],
 pop_assum (mp_tac o Q.SPEC `(p,e)`) >>
     rw [] >>
     metis_tac [],
 metis_tac []]);

val infer_p_bindings = Q.prove (
`(!cenv p st t env st' x.
    (infer_p cenv p st = (Success (t,env), st'))
    ⇒
    (pat_bindings p x = MAP FST env ++ x)) ∧
 (!cenv ps st ts env st' x.
    (infer_ps cenv ps st = (Success (ts,env), st'))
    ⇒
    (pats_bindings ps x = MAP FST env ++ x))`,
ho_match_mp_tac infer_p_ind >>
rw [pat_bindings_def, infer_p_def, success_eqns, remove_pair_lem] >>
rw [] >|
[PairCases_on `v''` >>
     rw [] >>
     metis_tac [],
 PairCases_on `v'` >>
     rw [] >>
     metis_tac [],
 PairCases_on `v'` >>
     PairCases_on `v''` >>
     rw [] >>
     metis_tac [APPEND_ASSOC]]);

val infer_p_sound = Q.prove (
`(!cenv p st t env st' tvs extra_constraints s.
    (infer_p cenv p st = (Success (t,env), st')) ∧
    t_wfs st.subst ∧
    check_cenv cenv ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_p tvs cenv p (convert_t (t_walkstar s t)) (convert_env s env)) ∧
 (!cenv ps st ts env st' tvs extra_constraints s.
    (infer_ps cenv ps st = (Success (ts,env), st')) ∧
    t_wfs st.subst ∧
    check_cenv cenv ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_ps tvs cenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env))`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem] >>
rw [Once type_p_cases, convert_env_def] >>
imp_res_tac sub_completion_wfs >>
fs [] >>
rw [t_walkstar_eqn1, convert_t_def, Tbool_def, Tint_def, Tunit_def] >|
[match_mp_tac check_t_to_check_freevars >>
     rw [] >>
     fs [sub_completion_def] >>
     qpat_assum `!uv. uv ∈ FDOM s ⇒ P uv` match_mp_tac >>
     fs [count_def, SUBSET_DEF],
 `?ts env. v'' = (ts,env)` by (PairCases_on `v''` >> metis_tac []) >>
     `?tvs ts tn. v' = (tvs,ts,tn)` by (PairCases_on `v'` >> metis_tac []) >>
     rw [] >>
     `type_ps tvs cenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env)` 
               by metis_tac [sub_completion_add_constraints, sub_completion_more_vars] >>
     rw [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_p_wfs, pure_add_constraints_wfs] >>
     rw [convert_t_def, t_walkstar_eqn1, MAP_MAP_o, combinTheory.o_DEF,
         EVERY_MAP, LENGTH_COUNT_LIST] >>
     fs [] >-
     metis_tac [sub_completion_check] >>
     imp_res_tac pure_add_constraints_apply >>
     pop_assum mp_tac >>
     rw [MAP_ZIP] >>
     imp_res_tac sub_completion_apply_list >>
     pop_assum mp_tac >>
     rw [subst_infer_subst_swap] >>
     `EVERY (check_freevars 0 tvs') ts'` by metis_tac [check_cenv_lookup] >>
     rw [] >>
     fs [convert_env_def] >>
     metis_tac [convert_t_subst, LENGTH_COUNT_LIST, LENGTH_MAP,
                MAP_MAP_o, combinTheory.o_DEF],
 `?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
     `t_wfs s` by metis_tac [infer_p_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
     fs [convert_env_def] >>
     metis_tac [],
 `?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     `?ts' env'. v'' = (ts',env')` by (PairCases_on `v''` >> metis_tac []) >>
     rw [] >>
     `t_wfs st''.subst` by metis_tac [infer_p_wfs] >>
     `?ts. sub_completion tvs st''.next_uvar st''.subst ts s` by metis_tac [sub_completion_infer_p] >>
     fs [convert_env_def] >>
     metis_tac []]);

val wfs_thms = Q.prove (
`t_wfs s ⇒ t_wfs (s |+ (n,Infer_Tvar_db n'))`,
cheat);

val generalise_subst = Q.prove (
`(!t m n s tvs s' t'.
  t_wfs s ∧
  (generalise m n s t = (tvs, s', t'))
  ⇒
  t_wfs s' ∧
  (s SUBMAP s') ∧
  (FDOM s' = FDOM s ∪ { uv | uv ∈ free_uvars t ∧ m ≤ uv }) ∧
  (!uv. uv ∈ FDOM s' DIFF FDOM s ⇒ ∃tv. (FAPPLY s' uv = Infer_Tvar_db tv) ∧ n ≤ tv ∧ tv < tvs + n) ∧
  (t_walkstar s' t = t_walkstar s t')) ∧
 (!ts m n s tvs s' ts'.
  t_wfs s ∧
  (generalise_list m n s ts = (tvs, s', ts'))
  ⇒
  t_wfs s' ∧
  (s SUBMAP s') ∧
  (FDOM s' = FDOM s ∪ { uv | uv ∈ BIGUNION (set (MAP free_uvars ts)) ∧ m ≤ uv }) ∧
  (!uv. uv ∈ FDOM s' DIFF FDOM s ⇒ ∃tv. (FAPPLY s' uv = Infer_Tvar_db tv) ∧ n ≤ tv ∧ tv < tvs + n) ∧
  (MAP (t_walkstar s') ts = MAP (t_walkstar s) ts'))`,
Induct >>
SIMP_TAC (srw_ss()) [free_uvars_def, generalise_def] >|
[REPEAT GEN_TAC  >>
     STRIP_TAC >>
     `?tvs s' ts'. generalise_list m n s ts = (tvs, s', ts')`
               by (cases_on `generalise_list m n s ts` >>
                   rw [] >>
                   cases_on `r` >>
                   fs []) >>
     fs [LET_THM] >>
     rw [] >>
     res_tac >>
     rw [EXTENSION, t_walkstar_eqn1] >>
     metis_tac [],
 rw [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     `t_wfs (s |+ (n, Infer_Tvar_db n'))` by metis_tac [wfs_thms] >>
     rw [FLOOKUP_DEF, EXTENSION] >>
     TRY (EQ_TAC) >>
     rw [] >>
     fs [FLOOKUP_DEF] >|
     [rw [t_walkstar_eqn, t_walk_eqn, Once t_vwalk_eqn, FLOOKUP_DEF],
      rw [t_walkstar_eqn, t_walk_eqn, Once t_vwalk_eqn, FLOOKUP_DEF] >>
          cases_on `s ' n` >>
          rw [t_walk_eqn],
      rw [t_walkstar_eqn, t_walk_eqn, Once t_vwalk_eqn, FLOOKUP_DEF] >>
          cases_on `s ' n` >>
          rw [t_walk_eqn]],
 REPEAT GEN_TAC >>
     STRIP_TAC >>
     `?tvs s' t'. generalise m n s t = (tvs, s', t')`
               by (cases_on `generalise m n s t` >>
                   rw [] >>
                   cases_on `r` >>
                   fs []) >>
     fs [LET_THM] >>
     `?tvs s' ts'. generalise_list m (tvs'+n) s'' ts = (tvs, s', ts')`
               by (cases_on `generalise_list m (tvs'+n) s'' ts` >>
                   rw [] >>
                   cases_on `r` >>
                   fs []) >>
     fs [LET_THM] >>
     qpat_assum `!m'. P m'`
           (mp_tac o Q.SPECL [`m`, `tvs'+n`, `s''`, `tvs''`, `s'''`, `ts''`]) >>
     qpat_assum `!m'. P m'`
           (mp_tac o Q.SPECL [`m`, `n`, `s`, `tvs'`, `s''`, `t'`]) >>
     rw [INTER_UNION] >|
     [metis_tac [SUBMAP_TRANS],
      rw [EXTENSION] >>
          metis_tac [],
      `uv ∈ FDOM s''` by fs [] >>
          res_tac >>
          qexists_tac `tv` >>
          rw [INTER_UNION] >>
          fs [SUBMAP_DEF] >-
          metis_tac [] >>
          decide_tac,
      cases_on `uv ∈ {uv | uv ∈ free_uvars t ∧ m ≤ uv}` >>
          full_simp_tac (srw_ss()++ARITH_ss) [] >|
          [`uv ∈ FDOM s''` by fs [] >>
               res_tac >>
               qexists_tac `tv` >>
               fs [SUBMAP_DEF] >>
               rw [] >-
               metis_tac [] >>
               full_simp_tac (srw_ss()++ARITH_ss) [],
           `uv ∈ FDOM s'` by (fs [] >> metis_tac []) >>
               res_tac >>
               qexists_tac `tv'''` >>
               rw [] >>
               decide_tac,
           metis_tac []],
     cheat,
     cheat]]); 

val t_walkstar_FEMPTY = Q.prove (
`!t. t_walkstar FEMPTY t = t`,
cheat);

val generalise_subst_empty = Q.prove (
`(!ts m n s tvs s' ts'.
  (generalise_list m n FEMPTY ts = (tvs, s', ts'))
  ⇒
  t_wfs s' ∧
  (FDOM s' = { uv | uv ∈ BIGUNION (set (MAP free_uvars ts)) ∧ m ≤ uv }) ∧
  (!uv. uv ∈ FDOM s' ⇒ ∃tv. (FAPPLY s' uv = Infer_Tvar_db tv) ∧ n ≤ tv ∧ tv < tvs + n) ∧
  (MAP (t_walkstar s') ts = ts'))`,
rw [] >>
imp_res_tac generalise_subst >>
fs [EXTENSION] >>
`t_wfs FEMPTY` by fs [t_wfs_def] >>
rw [] >>
REPEAT (pop_assum (fn _ => all_tac)) >>
induct_on `ts'` >>
rw [] >>
metis_tac [t_walkstar_FEMPTY]);

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
fs [t_walkstar_eqn, t_walk_eqn, convert_t_def, deBruijn_inc_def, check_t_def] >>
rw [type_op_cases, 
    Tint_def, Tbool_def, Tref_def, Tfn_def, Tunit_def] >>
metis_tac [MAP, infer_e_next_uvar_mono, check_env_more];

val infer_e_sound = Q.prove (
`(!menv cenv env e st st' ext tenv t extra_constraints s.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
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
    check_env (count st.next_uvar) env ∧
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
    check_env (count st.next_uvar) env ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    type_pes (convert_menv menv) cenv tenv pes (convert_t (t_walkstar s t1)) (convert_t (t_walkstar s t2))) ∧
 (!menv cenv env funs st st' ext tenv extra_constraints s ts.
    (infer_funs menv cenv env funs st = (Success ts, st')) ∧
    t_wfs st.subst ∧
    check_menv menv ∧
    check_cenv cenv ∧
    check_env (count st.next_uvar) env ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv ∧
    ALL_DISTINCT (MAP FST funs)
    ⇒
    type_funs (convert_menv menv) cenv tenv funs (MAP2 (\(x,y,z) t. (x, (convert_t o t_walkstar s) t)) funs ts))`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem] >>
rw [check_t_def] >>
fs [bind_def, check_t_def, check_env_bind, check_env_merge] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [Tbool_def, Tint_def, Tunit_def] >|
[(* Raise *)
     fs [sub_completion_def, flookup_thm, count_add1, SUBSET_DEF] >>
     `st.next_uvar < st.next_uvar + 1` by decide_tac >>
     metis_tac [IN_INSERT, check_convert_freevars, prim_recTheory.LESS_REFL],
 (* Handle *)
     binop_tac,
 (* Handle *)
     `tenv_inv s
                 ((x,0,Infer_Tapp [] TC_int)::env) 
                 (bind_tenv x 0 
                            (convert_t (t_walkstar s (Infer_Tapp [] TC_int))) 
                            tenv)`
             by (match_mp_tac tenv_inv_extend0 >>
                 rw []) >>
     `num_tvs tenv = num_tvs (bind_tenv x 0 (convert_t (t_walkstar s (Infer_Tapp [] TC_int))) tenv)`
             by rw [bind_tenv_def, num_tvs_def] >>
     fs [bind_tenv_def] >>
     `check_env (count (st'' with subst := s').next_uvar) env`
                by (fs [] >>
                    metis_tac [check_env_more, infer_e_next_uvar_mono]) >>
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
          `count st.next_uvar ⊆ FDOM s`
                  by (fs [count_def, SUBSET_DEF] >>
                      rw [] >>
                      metis_tac [DECIDE ``x < y ⇒ x < y + z:num``]) >>
          `check_t tvs (FDOM s) t`
                     by metis_tac [check_env_lookup, check_t_more5] >>
          metis_tac [db_subst_infer_subst_swap, pure_add_constraints_wfs],
      rw [EVERY_MAP] >>
          metis_tac [sub_completion_check, FST],
      rw [LENGTH_COUNT_LIST] >>
          metis_tac [tenv_inv_def]],
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
      rw [LENGTH_COUNT_LIST] >>
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
         EVERY_MAP, LENGTH_COUNT_LIST] >-
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
     metis_tac [convert_t_subst, LENGTH_COUNT_LIST, LENGTH_MAP,
                MAP_MAP_o, combinTheory.o_DEF],
 (* Fun *)
     `t_wfs s ∧ t_wfs st'.subst` by metis_tac [stupid_record_thing,sub_completion_wfs, infer_e_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tfn_def] >>
     imp_res_tac infer_e_next_uvar_mono >>
     fs [] >>
     `st.next_uvar < st'.next_uvar` by decide_tac >|
     [fs [sub_completion_def, SUBSET_DEF] >>
          metis_tac [check_t_to_check_freevars],
      `tenv_inv s
                 ((x,0,Infer_Tuvar st.next_uvar)::env) 
                 (bind_tenv x 0 
                            (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) 
                            tenv)`
             by (match_mp_tac tenv_inv_extend0 >>
                 fs []) >>
          fs [bind_tenv_def] >>
          `check_t 0 (count (st with next_uvar := st.next_uvar + 1).next_uvar) (Infer_Tuvar st.next_uvar)`
                     by rw [check_t_def] >>
          `check_env (count (st with next_uvar := st.next_uvar + 1).next_uvar) env`
                     by (rw [] >>
                         metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]) >>
          metis_tac [num_tvs_def, stupid_record_thing, bind_tenv_def]],
 (* Opref *)
     rw [type_uop_cases, Tref_def] >>
     binop_tac,
 (* Opderef *)
     rw [type_uop_cases, Tref_def] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_unify >>
     imp_res_tac sub_completion_apply >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs] >>
     fs [t_walkstar_eqn1] >>
     `type_e (convert_menv menv) cenv tenv e (convert_t (t_walkstar s t'))`
                by metis_tac [] >>
     metis_tac [convert_t_def, MAP],
 (* Opn *)
     binop_tac,
 (* Opb *)
     binop_tac,
 (* Equality *)
     binop_tac, 
 (* Opapp *)
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac sub_completion_unify >>
     imp_res_tac sub_completion_infer >>
     fs [] >>
     res_tac >>
     fs [] >>
     rw [type_op_cases, Tint_def, Tbool_def, Tref_def, Tfn_def, Tunit_def] >>
     qexists_tac `convert_t (t_walkstar s t2)` >>
     rw [] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_apply >>
     fs [] >>
     imp_res_tac t_unify_wfs >>
     imp_res_tac sub_completion_wfs >>
     fs [t_walkstar_eqn, t_walk_eqn, convert_t_def] >>
     metis_tac [check_env_more, infer_e_next_uvar_mono],
 (* Opassign *) 
     binop_tac, 
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
 (* If *)
     `t_wfs (st'' with subst := s').subst` 
                by (rw [] >>
                    metis_tac [t_unify_wfs, infer_e_wfs]) >>
     `t_wfs st''''.subst` by metis_tac [infer_e_wfs] >>
     `st.next_uvar ≤ st''''.next_uvar` 
                by (imp_res_tac infer_e_next_uvar_mono >>
                    fs [] >>
                    decide_tac) >>
     `check_env (count st''''.next_uvar) env` by metis_tac [check_env_more] >>
     `?ts. sub_completion (num_tvs tenv) st'''''.next_uvar st'''''.subst ts s` 
               by metis_tac [sub_completion_unify2] >>
     `type_e (convert_menv menv) cenv tenv e'' (convert_t (t_walkstar s t3))` by metis_tac [] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_apply >>
     metis_tac [],
 (* Match *)
     `?ts. sub_completion (num_tvs tenv) st''.next_uvar st''.subst  ts s` 
              by (imp_res_tac sub_completion_infer_pes >>
                  fs [] >>
                  metis_tac [sub_completion_more_vars]) >>
     `type_e (convert_menv menv) cenv tenv e (convert_t (t_walkstar s t1))` by metis_tac [] >>
     qexists_tac `convert_t (t_walkstar s t1)` >>
     rw [RES_FORALL] >>
     `?p e. x = (p,e)` by (PairCases_on `x` >> metis_tac []) >>
     rw [] >>
     `t_wfs (st'' with next_uvar := st''.next_uvar + 1).subst`
              by (rw [] >>
                  metis_tac [infer_e_wfs]) >>
     `st.next_uvar ≤ (st'' with next_uvar := st''.next_uvar + 1).next_uvar`
              by (rw [] >>
                  imp_res_tac infer_e_next_uvar_mono >>
                  fs [] >>
                  decide_tac) >>
     `check_env (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) env` by metis_tac [check_env_more] >>
     `type_pes (convert_menv menv) cenv tenv pes (convert_t (t_walkstar s t1)) (convert_t (t_walkstar s (Infer_Tuvar st''.next_uvar)))`
              by metis_tac [] >>
     fs [type_pes_def, RES_FORALL] >>
     pop_assum (mp_tac o Q.SPEC `(p,e')`) >>
     rw [],
 (* Let *)
     disj2_tac >>
     imp_res_tac sub_completion_infer >>
     fs [] >>
     imp_res_tac sub_completion_unify >>
     qexists_tac `convert_t (t_walkstar s t1)` >>
     rw [] >-
     metis_tac [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_wfs >>
     `tenv_inv s ((x,0,t1)::env) 
                 (bind_tenv x 0 (convert_t (t_walkstar s t1)) tenv)` 
            by (match_mp_tac tenv_inv_extend0 >>
                rw [] >>
                fs []) >>
     `num_tvs (bind_tenv x 0 (convert_t (t_walkstar s t1)) tenv) = num_tvs tenv` 
            by (rw [num_tvs_def, bind_tenv_def]) >>
     `check_t 0 (count st''.next_uvar) t1` by metis_tac [infer_e_check_t] >>
     `check_env (count st''.next_uvar) env` by metis_tac [infer_e_next_uvar_mono, check_env_more] >>
     metis_tac [],
 (* Letrec *)
     `t_wfs (st with next_uvar := st.next_uvar + LENGTH funs).subst`
               by rw [] >>
     Q.ABBREV_TAC `env' = MAP2 (λ(f,x,e) uvar. (f,0:num,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs)))` >>
     Q.ABBREV_TAC `tenv' = MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)))` >>
     `sub_completion (num_tvs (bind_var_list 0 tenv' tenv)) st'.next_uvar st'.subst extra_constraints s`
                 by metis_tac [num_tvs_bind_var_list] >>
     `?constraints1. sub_completion (num_tvs (bind_var_list 0 tenv' tenv)) st''''.next_uvar st''''.subst constraints1 s`
                 by metis_tac [sub_completion_infer] >>
     `?constraints2. sub_completion (num_tvs (bind_var_list 0 tenv' tenv)) st'''.next_uvar st'''.subst constraints2 s`
                 by metis_tac [sub_completion_add_constraints] >>
     `tenv_inv s (merge env' env) (bind_var_list 0 tenv' tenv)` 
                 by (UNABBREV_ALL_TAC >>
                     match_mp_tac tenv_inv_letrec_merge >>
                     rw []) >>
     `check_env (count (st with next_uvar := st.next_uvar + LENGTH funs).next_uvar) (merge env' env)`
                 by (rw [check_env_merge] >|
                     [Q.UNABBREV_TAC `env'` >>
                          rw [check_env_letrec_lem],
                      metis_tac [check_env_more, DECIDE ``x ≤ x+y:num``]]) >>
     `type_funs (convert_menv menv) cenv (bind_var_list 0 tenv' tenv) funs 
                (MAP2 (\(x,y,z) t. (x, convert_t (t_walkstar s t))) funs funs_ts)`
                 by metis_tac [] >>
     `t_wfs st''''.subst` by metis_tac [infer_e_wfs, pure_add_constraints_wfs] >>
     `st.next_uvar + LENGTH funs ≤ st''''.next_uvar`
                 by (fs [] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     fs [] >>
                     metis_tac []) >>
     fs [] >>
     `type_e (convert_menv menv) cenv (bind_var_list 0 tenv' tenv) e (convert_t (t_walkstar s t))`
                 by metis_tac [check_env_more] >>
     qexists_tac `tenv'` >>
     qexists_tac `0` >>
     rw [bind_tvar_def] >>
     `tenv' = MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts`
                 by (Q.UNABBREV_TAC `tenv'` >>
                     match_mp_tac letrec_lemma >>
                     imp_res_tac pure_add_constraints_apply >>
                     `LENGTH funs = LENGTH funs_ts` by metis_tac [LENGTH_COUNT_LIST] >>
                     fs [GSYM MAP_MAP_o, MAP_ZIP, LENGTH_COUNT_LIST, LENGTH_MAP] >>
                     metis_tac [MAP_MAP_o, combinTheory.o_DEF, sub_completion_apply_list]) >>
     rw [],
 metis_tac [sub_completion_infer_es],
 metis_tac [infer_e_wfs, infer_e_next_uvar_mono, check_env_more],
 rw [type_pes_def, RES_FORALL],
 `?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     rw [] >>
     `∃ts. sub_completion (num_tvs tenv) (st'''' with subst:= s'').next_uvar (st'''' with subst:= s'').subst ts s` 
                   by metis_tac [sub_completion_infer_pes] >>
     fs [] >>
     `∃ts. sub_completion (num_tvs tenv) st''''.next_uvar st''''.subst ts s` 
              by metis_tac [sub_completion_unify2] >>
     `∃ts. sub_completion (num_tvs tenv) (st'' with subst := s').next_uvar (st'' with subst := s').subst ts s` 
              by metis_tac [sub_completion_infer] >>
     fs [] >>
     `∃ts. sub_completion (num_tvs tenv) st''.next_uvar st''.subst ts s` 
              by metis_tac [sub_completion_unify2] >>
     `type_p (num_tvs tenv) cenv p (convert_t (t_walkstar s t)) (convert_env s env')`
              by metis_tac [infer_p_sound] >>
     `t_wfs (st'' with subst := s').subst`
           by (rw [] >>
               metis_tac [infer_p_wfs, t_unify_wfs]) >>
     imp_res_tac infer_p_check_t >>
     `check_env (count (st'' with subst:=s').next_uvar) (merge (MAP (λ(n,t). (n,0,t)) (SND (t,env'))) env)`
           by (rw [check_env_merge] >|
               [rw [check_env_def, EVERY_MAP, remove_pair_lem] >>
                    fs [EVERY_MEM] >>
                    rw [] >>
                    PairCases_on `x` >>
                    fs [] >>
                    res_tac >>
                    fs [],
                metis_tac [infer_p_next_uvar_mono, check_env_more]]) >>
     `tenv_inv s (merge (MAP (λ(n,t). (n,0,t)) env') env) (bind_var_list 0 (convert_env s env') tenv)` 
              by (metis_tac [tenv_inv_merge]) >>
     `type_e (convert_menv menv) cenv (bind_var_list 0 (convert_env s env') tenv) e (convert_t (t_walkstar s t2'))`
               by metis_tac [check_env_merge, SND, num_tvs_bind_var_list] >>
     rw [type_pes_cons] >|
     [imp_res_tac infer_p_bindings >>
          metis_tac [APPEND_NIL],
      qexists_tac `(convert_env s env')` >>
           rw [] >>
           imp_res_tac t_unify_apply >>
           metis_tac [sub_completion_apply],
      `t_wfs (st'''' with subst := s'').subst`
           by (rw [] >>
               metis_tac [t_unify_wfs, infer_e_wfs]) >>
          `(st.next_uvar ≤ (st'''' with subst := s'').next_uvar)` 
                  by (fs [] >>
                      imp_res_tac infer_p_next_uvar_mono >>
                      imp_res_tac infer_e_next_uvar_mono >>
                      fs [] >>
                      decide_tac) >>
          `check_env (count (st'''' with subst := s'').next_uvar) env` by metis_tac [check_env_more] >>
          metis_tac []],
 `t_wfs st'''.subst ∧ t_wfs (st with next_uvar := st.next_uvar + 1).subst` by metis_tac [infer_e_wfs, stupid_record_thing] >>
     imp_res_tac sub_completion_infer_funs >>
     `tenv_inv s ((x,0,Infer_Tuvar st.next_uvar)::env) (bind_tenv x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv)`
              by (match_mp_tac tenv_inv_extend0 >>
                  rw []) >>
     `num_tvs (bind_tenv x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv) = num_tvs tenv`
              by fs [num_tvs_def, bind_tenv_def] >>
     `check_env (count (st with next_uvar := st.next_uvar + 1).next_uvar) env ∧
      check_t 0 (count (st with next_uvar := st.next_uvar + 1).next_uvar) (Infer_Tuvar st.next_uvar)`
                by (rw [check_t_def] >>
                    metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]) >>
     `type_e (convert_menv menv) cenv (bind_tenv x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv)
             e (convert_t (t_walkstar s t))`
                 by metis_tac [] >>
     `check_env (count st'''.next_uvar) env`
                 by (metis_tac [check_env_more, infer_e_next_uvar_mono]) >>
     `type_funs (convert_menv menv) cenv tenv funs (MAP2 (\(x,y,z) t. (x, convert_t (t_walkstar s t))) funs ts')`
               by metis_tac [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tfn_def] >|
     [rw [check_freevars_def] >>
          match_mp_tac check_t_to_check_freevars >>
          rw [] >>
          fs [sub_completion_def] >|
          [`st.next_uvar < st'''.next_uvar`
                    by (imp_res_tac infer_e_next_uvar_mono >>
                        fs [] >>
                        decide_tac) >>
               `st.next_uvar ∈ FDOM s`
                    by fs [count_def, SUBSET_DEF] >>
               metis_tac [],
           match_mp_tac (hd (CONJUNCTS check_t_walkstar)) >>
               rw [] >>
               `check_t 0 (count (st'''.next_uvar)) t`
                         by (imp_res_tac infer_e_check_t >>
                             fs [GSYM bind_def, check_env_bind]) >>
               metis_tac [check_t_more5]],
      imp_res_tac infer_funs_length >>
          rw [lookup_notin, MAP2_MAP, LENGTH_MAP2, MAP_MAP_o, combinTheory.o_DEF, map_zip_lem]]]);

          (*
val infer_d_sound = Q.prove (
`!mn menv cenv env d st1 st2 cenv' env' tenv.
  infer_d mn menv cenv env d st1 = (Success (cenv',env'), st2) ∧
  check_menv menv ∧
  check_cenv cenv ∧
  check_env (count (init_infer_state:(num |-> infer_t) infer_st).next_uvar) env ∧
  tenv_inv init_infer_state.subst env tenv
  ⇒
  type_d mn (convert_menv menv) cenv tenv d cenv' (MAP (\(x,tvs,t). (x,tvs,convert_t t)) env')`,

cases_on `d` >>
rw [infer_d_def, success_eqns, type_d_cases] >>
rw [emp_def] >|

[disj1_tac >>
     `?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     rw [] >>
     fs [success_eqns] >>
     `?tvs s ts. generalise_list st''.next_uvar 0 FEMPTY (MAP SND env'') = (tvs,s,ts)`
                 by (cases_on `generalise_list st''.next_uvar 0 FEMPTY (MAP SND env'')` >>
                     rw [] >>
                     cases_on `r` >>
                     metis_tac []) >>
     fs [success_eqns] >>
     rw []
     fs [init_state_def] >>
     rw [] >>
     `t_wfs init_infer_state.subst` by rw [init_infer_state_def, t_wfs_def] >>
     rw [] >>
     `check_t 0 (count st'''.next_uvar) t1` by metis_tac [infer_e_check_t] >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac generalise_subst_empty >>
     full_simp_tac (srw_ss()++ARITH_ss) []


     imp_res_tac sub_completion_unify2



 disj2_tac >>
     `?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
     rw [] >>
     fs [success_eqns] >>
     rw [] >>
     fs [init_state_def] >>
     `t_wfs init_infer_state.subst` by rw [init_infer_state_def, t_wfs_def] >>
     rw [] >>
     `check_t 0 (count st'''.next_uvar) t1` by metis_tac [infer_e_check_t] >>
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac sub_completion_unify2

     `sub_completion (num_tvs tenv) st''''.next_uvar st''''.subst 


     imp_res_tac infer_e_sound




     infer_p_sound
     infer_e_sound



   rw [] >>
   *)

val _ = export_theory ();
