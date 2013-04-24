open preamble;
open MiniMLTheory MiniMLTerminationTheory inferTheory unifyTheory;

val fmap2_id = Q.prove (
`!m. FMAP_MAP2 (\(x,y). y) m = m`,
rw [FMAP_MAP2_def] >>
cheat);

val _ = new_theory "inferSound";

val t_unify_apply = Q.prove (
`!s1 s2 t1 t2.
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  (apply_subst_t (t_collapse s2) t1 = apply_subst_t (t_collapse s2) t2)`,
cheat);

val t_unify_apply2 = Q.prove (
`!s1 s2 t1' t2' t1 t2.
  (t_unify s1 t1' t2' = SOME s2) ∧
  (apply_subst_t (t_collapse s1) t1 = apply_subst_t (t_collapse s1) t2)
  ⇒
  (apply_subst_t (t_collapse s2) t1 = apply_subst_t (t_collapse s2) t2)`,
cheat);

val t_collapse_idem = Q.prove (
`!s. t_collapse (t_collapse s) = t_collapse s`,
cheat);

val flookup_thm = Q.prove (
`!f x v. ((FLOOKUP f x = NONE) = x ∉ FDOM f) ∧
         ((FLOOKUP f x = SOME v) = x ∈ FDOM f ∧ (f ' x = v))`,
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
 (!st. (st with subst := st.subst) = st)`,
cheat);

val count_list_sub1 = Q.prove (
`!n. (n ≠ 0) ⇒ (COUNT_LIST n = 0::MAP SUC (COUNT_LIST (n - 1)))`,
induct_on `n` >>
ONCE_REWRITE_TAC [rich_listTheory.COUNT_LIST_def] >>
fs []);

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
  ((st2 = st1 with subst := t_collapse st1.subst) ∧
   (t2 = apply_subst_t (t_collapse st1.subst) t1))`,
rw [LET_THM, apply_subst_def] >>
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
(pure_add_constraints s1 (SOME (t1,t2)::rest) s' = 
  ?s2. (t_unify s1 t1 t2 = SOME s2) ∧
       pure_add_constraints s2 rest s') ∧
(pure_add_constraints s (NONE::rest) s' =
  pure_add_constraints (t_collapse s) rest s')`;

val pure_add_constraints_ind = fetch "-" "pure_add_constraints_ind";

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
  (LENGTH ts1 = LENGTH ts2) ∧ 
  ((x = ()) ∧ 
  (st.next_uvar = st'.next_uvar) ∧
  pure_add_constraints st.subst (MAP SOME (ZIP (ts1,ts2))) st'.subst)`,
ho_match_mp_tac add_constraints_ind >>
rw [add_constraints_def, pure_add_constraints_def, st_ex_return_success,
    failwith_def, st_ex_bind_success, add_constraint_success] >>
TRY (cases_on `x`) >>
rw [pure_add_constraints_def] >-
metis_tac [elab_st_component_equality] >>
eq_tac >>
rw [] >>
fs [elab_st_subst] >>
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
    (?uvar st''. ((fresh_uvar : ((num |-> infer_t) elab_st, infer_t, string) M) st = (Success uvar, st'')) ∧
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
             get_next_uvar_success, apply_subst_list_success, guard_success];

val check_t_def = tDefine "check_t" `
(check_t n uvars (Infer_Tuvar v) = v ∈ uvars) ∧
(check_t n uvars (Infer_Tvar_db n') = 
  n' < n) ∧
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

(*
val (tenv_rel_rules, tenv_rel_ind, tenv_rel_cases) = Hol_reln `
(!s. 
  tenv_rel s [] Empty) ∧
(!s x tvs t env tenv.
  tenv_rel s env tenv
  ⇒
  tenv_rel s ((x,(tvs,t))::env) 
             (Bind_name x tvs (convert_t (apply_subst_t (t_collapse s) t)) tenv)) ∧
(!s tvs env tenv.
  tenv_rel s env tenv 
  ⇒
  tenv_rel s env (Bind_tvar tvs tenv))`;

val tenv_rel_lookup = Q.prove (
`!s env tenv.
  tenv_rel s env tenv
  ⇒
  !x tvs t tvs'. (lookup x env = SOME (tvs,t)) ⇒
    (lookup_tenv x tvs' tenv = 
     SOME (tvs, (convert_t (apply_subst_t (t_collapse s) t))))`,

ho_match_mp_tac tenv_rel_ind >>
rw [lookup_tenv_def] >>
TRY full_case_tac >>
rw []

val infer_invariant_def = Define `
infer_invariant st = 
  (* Only substitute for existing uvars *)
  (FDOM st.subst ⊆ count st.next_uvar) ∧
  (* Only uvars that exist can occur in the types substituted in *)
  (!t. t ∈ FRANGE st.subst ⇒ check_t 0 (count st.next_uvar) t)`;
  *)

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
 (!menv cenv env funs st st'.
    (infer_funs menv cenv env funs st = (Success (), st'))
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
 (!menv cenv env funs st st'.
    (infer_funs menv cenv env funs st = (Success (), st'))
    ⇒
    (?ts. pure_add_constraints st.subst ts st'.subst))`,
ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem, GSYM FORALL_PROD] >>
rw [] >>
res_tac >>
fs [] >>
TRY (cases_on `v'`) >>
prove_tac [pure_add_constraints_append, pure_add_constraints_def, infer_p_constraints]);

val sub_completion_def = Define `
sub_completion tvs next_uvar s1 extra_constraints s3 =
  ?s2.
    pure_add_constraints s1 extra_constraints s2 ∧
    (s3 = t_collapse s2) ∧
    (count next_uvar SUBSET FDOM s3) ∧
    (!t. t ∈ FRANGE s3 ⇒ check_t tvs {} t)`;

val sub_completion_unify = Q.prove (
`!st t1 t2 s1 n ts s2 n.
  (t_unify st.subst t1 t2 = SOME s1) ∧
  sub_completion n (st.next_uvar + 1) s1 ts s2
  ⇒
  sub_completion n st.next_uvar st.subst (SOME (t1,t2)::ts) s2`,
rw [sub_completion_def, pure_add_constraints_def] >>
qexists_tac `s2'` >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF, count_add1]);

val sub_completion_unify2 = Q.prove (
`!st t1 t2 s1 n ts s2 n s3 next_uvar.
  (t_unify s1 t1 t2 = SOME s2) ∧
  sub_completion n next_uvar s2 ts s3
  ⇒
  sub_completion n next_uvar s1 (SOME (t1,t2)::ts) s3`,
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
qexists_tac `s2` >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF] >>
metis_tac []);

val sub_completion_apply = Q.prove (
`!n uvars s1 ts s2 t1 t2.
  (apply_subst_t (t_collapse s1) t1 = apply_subst_t (t_collapse s1) t2) ∧
  sub_completion n uvars s1 ts s2 
  ⇒
  (apply_subst_t s2 t1 = apply_subst_t s2 t2)`,
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
fs [pure_add_constraints_def] >-
metis_tac [t_collapse_idem] >>
PairCases_on `x` >>
fs [pure_add_constraints_def] >>
every_case_tac >>
fs [] >>
metis_tac [t_unify_apply2]);

val check_t_to_check_freevars = Q.prove (
`!tvs (n:num set) t. check_t tvs {} t ⇒ check_freevars tvs [] (convert_t t)`,
ho_match_mp_tac (fetch "-" "check_t_ind") >>
rw [check_t_def, check_freevars_def, convert_t_def, EVERY_MAP] >>
fs [EVERY_MEM]);

val sub_completion_check = Q.prove (
`!tvs m s uvar s' extra_constraints.
sub_completion m (uvar + tvs) s' extra_constraints s
⇒
EVERY (λn. check_freevars m [] (convert_t (apply_subst_t s (Infer_Tuvar (uvar + n))))) (COUNT_LIST tvs)`,
induct_on `tvs` >>
rw [sub_completion_def, rich_listTheory.COUNT_LIST_SNOC, EVERY_SNOC] >>
fs [sub_completion_def] >|
[qpat_assum `!m' s. P m' s` match_mp_tac >>
     rw [] >>
     qexists_tac `s'` >>
     qexists_tac `extra_constraints` >>
     qexists_tac `s2` >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF],
 rw [apply_subst_t_eqn] >>
     `uvar+tvs ∈ FDOM (t_collapse s2)`
            by full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF] >>
     fs [FLOOKUP_DEF] >>
     `t_collapse s2 ' (uvar + tvs) ∈ FRANGE (t_collapse s2)`
            by (fs [FRANGE_DEF] >>
                metis_tac []) >>
     metis_tac [check_t_to_check_freevars]]);

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

val infer_deBruijn_inc0 = Q.prove (
`!(n:num) t. infer_deBruijn_inc 0 t = t`,
ho_match_mp_tac (fetch "-" "infer_deBruijn_inc_ind") >>
rw [infer_deBruijn_inc_def] >>
induct_on `ts` >>
rw []);

val subst_infer_subst_swap_lem = Q.prove (
`!t. (LENGTH ts = tvs) ∧
     check_t n {} t
     ⇒
     (convert_t t = deBruijn_subst 0 ts (convert_t (infer_deBruijn_inc tvs t)))`,
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
srw_tac [ARITH_ss] [check_t_def, convert_t_def, infer_deBruijn_inc_def, deBruijn_subst_def] >>
induct_on `ts'` >>
rw []);

val subst_infer_subst_swap = Q.prove (
`(!t s tvs uvar n.
  count (uvar + tvs) ⊆ FDOM (t_collapse s) ∧
  (!t. t ∈ FRANGE (t_collapse s) ⇒ check_t n {} t) ∧
  check_t tvs (count uvar) t ⇒
  (convert_t
    (apply_subst_t (t_collapse s)
       (infer_deBruijn_subst
          (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))
          t)) =
   deBruijn_subst 0
    (MAP (convert_t o apply_subst_t (t_collapse s))
       (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
    (convert_t (apply_subst_t (FMAP_MAP2 (λ(x,t). infer_deBruijn_inc tvs t) (t_collapse s)) t)))) ∧
 (!ts s tvs uvar n.
  count (uvar + tvs) ⊆ FDOM (t_collapse s) ∧
  (!t. t ∈ FRANGE (t_collapse s) ⇒ check_t n {} t) ∧
  EVERY (\t. check_t tvs (count uvar) t) ts ⇒
  (MAP (convert_t o
       apply_subst_t (t_collapse s) o
       infer_deBruijn_subst (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
      ts =
   MAP (deBruijn_subst 0 (MAP (convert_t o apply_subst_t (t_collapse s)) (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))) o
       convert_t o 
       apply_subst_t (FMAP_MAP2 (λ(x,t). infer_deBruijn_inc tvs t) (t_collapse s)))
      ts))`,
ho_match_mp_tac infer_t_induction >>
rw [apply_subst_t_eqn, convert_t_def, deBruijn_subst_def, EL_MAP,
    infer_deBruijn_subst_def, MAP_MAP_o, combinTheory.o_DEF, check_t_def,
    rich_listTheory.LENGTH_COUNT_LIST] >|
[fs [SUBSET_DEF, FLOOKUP_DEF, FRANGE_FLOOKUP, FMAP_MAP2_THM] >>
     `n < uvar + tvs` by decide_tac >>
     `n ∈ FDOM (t_collapse s)` by res_tac >>
     fs [] >>
     `check_t n' {} (t_collapse s ' n)` by metis_tac [] >>
     fs [] >>
     metis_tac [LENGTH_MAP, rich_listTheory.LENGTH_COUNT_LIST, subst_infer_subst_swap_lem],
 metis_tac [],
 metis_tac []]);

val binop_tac =
rw [typeSystemTheory.type_op_cases, 
    Tint_def, Tbool_def, Tref_def, Tfn_def, Tunit_def] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer >>
res_tac >>
imp_res_tac t_unify_apply >>
imp_res_tac sub_completion_apply >>
fs [apply_subst_t_eqn] >>
metis_tac [convert_t_def, MAP];

val tenv_inv_def = Define `
tenv_inv s env tenv =
  (!x tvs t.
    (lookup x env = SOME (tvs,t)) ⇒
    (lookup_tenv x 0 tenv = 
     SOME (tvs, convert_t (apply_subst_t (FMAP_MAP2 (λ(x,t).  infer_deBruijn_inc tvs t) (t_collapse s)) t))))`;

     (*
val infer_e_sound = Q.prove (
`(!menv cenv env e st st' ext tenv t extra_constraints s.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    check_menv menv ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    type_e (convert_menv menv) cenv tenv e 
           (convert_t (apply_subst_t s t))) ∧
 (!menv cenv env es st st' ext tenv ts extra_constraints s.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    check_menv menv ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    type_es (convert_menv menv) cenv tenv es 
            (MAP (convert_t o apply_subst_t s) ts)) ∧
 (!menv cenv env pes t1 t2 st st' tenv ext extra_constraints s.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    check_menv menv ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    T) ∧
 (!menv cenv env funs st st' ext tenv extra_constraints s.
    (infer_funs menv cenv env funs st = (Success (), st')) ∧
    check_menv menv ∧
    sub_completion (num_tvs tenv) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s env tenv
    ⇒
    ?env'. type_funs (convert_menv menv) cenv tenv funs env')`,

ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem] >>
rw [check_t_def] >>
fs [bind_def, check_env_def, check_t_def] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [apply_subst_t_eqn, convert_t_def, Tbool_def, Tint_def, Tunit_def] >|
[(* Raise *)
     every_case_tac >>
     rw [] >>
     fs [sub_completion_def, flookup_thm, count_add1, FRANGE_DEF] >>
     metis_tac [IN_INSERT, check_convert_freevars, prim_recTheory.LESS_REFL],
 (* Handle *)
     binop_tac,
 (* Handle *)
     `tenv_inv s ((x,0,Infer_Tapp [] TC_int)::env) 
                 (Bind_name x 0 
                            (convert_t (apply_subst_t s (Infer_Tapp [] TC_int))) 
                            tenv)`
             by (fs [tenv_inv_def, lookup_tenv_def] >>
                 rw [typeSystemTheory.deBruijn_inc0, infer_deBruijn_inc0] >>
                 rw [infer_deBruijn_inc0, fmap2_id] >>
                 fs [sub_completion_def, t_collapse_idem]) >>
     `num_tvs tenv = num_tvs (Bind_name x 0 (convert_t (apply_subst_t s (Infer_Tapp [] TC_int))) tenv)`
             by rw [num_tvs_def] >>
     rw [bind_tenv_def] >>
     binop_tac,
 (* Var short *)
     rw [t_lookup_var_id_def] >>
     `?tvs t. v' = (tvs, t)` 
                by (PairCases_on `v'` >>
                    rw []) >>
     rw [] >>
     qexists_tac `convert_t (apply_subst_t (FMAP_MAP2 (λ(x,t). infer_deBruijn_inc tvs t) (t_collapse s)) t)` >>
     qexists_tac `MAP (convert_t o apply_subst_t s) (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST tvs))` >>
     rw [] >|
     [fs [sub_completion_def] >>
          rw [] >>
          `check_t tvs (count st.next_uvar) t` by cheat >>
          metis_tac [subst_infer_subst_swap, t_collapse_idem],
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
     qexists_tac `convert_t (apply_subst_t (FMAP_MAP2 (λ(x,t). infer_deBruijn_inc tvs t) (t_collapse s)) t)` >>
     qexists_tac `MAP (convert_t o apply_subst_t s) (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST tvs))` >>
     rw [] >|
     [fs [sub_completion_def] >>
          rw [] >>
          `check_t tvs (count st.next_uvar) t` by cheat >>
          metis_tac [subst_infer_subst_swap, t_collapse_idem],
      rw [EVERY_MAP] >>
          metis_tac [sub_completion_check, FST],
      rw [rich_listTheory.LENGTH_COUNT_LIST] >>
          fs [convert_menv_def, check_menv_def] >>
          `lookup mn (MAP (λ(mn,env). (mn,MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env)) menv) =
           SOME (MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env')`
                    by metis_tac [lookup_map] >>
          rw [] >>
          all_tac],
 (* Con *)
     all_tac,
 (* Fun *)
     all_tac,
 (* Opref *)
     rw [typeSystemTheory.type_uop_cases, Tref_def] >>
     metis_tac [],
 (* Opderef *)
     rw [typeSystemTheory.type_uop_cases, Tref_def] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_unify >>
     imp_res_tac sub_completion_apply >>
     fs [apply_subst_t_eqn] >>
     metis_tac [convert_t_def, MAP],
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
