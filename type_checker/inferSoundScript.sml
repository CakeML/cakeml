open preamble;
open MiniMLTheory MiniMLTerminationTheory inferTheory unifyTheory;

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

val flookup_thm = Q.prove (
`!f x v. ((FLOOKUP f x = NONE) = x ∉ FDOM f) ∧
         ((FLOOKUP f x = SOME v) = x ∈ FDOM f ∧ (f ' x = v))`,
rw [FLOOKUP_DEF]);

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
(pure_add_constraints s1 ((t1,t2)::rest) s' = 
  case t_unify s1 t1 t2 of
    | NONE => F
    | SOME s2 => pure_add_constraints s2 rest s')`;

val add_constraints_success = Q.prove (
`!ts1 ts2 st st' x.
  (add_constraints ts1 ts2 st = (Success x, st'))
  =
  (LENGTH ts1 = LENGTH ts2) ∧ 
  ((x = ()) ∧ 
  (st.next_uvar = st'.next_uvar) ∧
  pure_add_constraints st.subst (ZIP (ts1,ts2)) st'.subst)`,
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

val (tenv_rel_rules, tenv_rel_ind, tenv_rel_cases) = Hol_reln `
(!sub. 
  tenv_rel sub [] Empty) ∧
(!sub x tvs t env tenv.
  tenv_rel sub env tenv
  ⇒
  tenv_rel sub ((x,(tvs,t))::env) 
               (Bind_name x tvs (convert_t (apply_subst_t sub t)) tenv)) ∧
(!sub tvs env tenv.
  tenv_rel sub env tenv 
  ⇒
  tenv_rel sub env (Bind_tvar tvs tenv))`;

val infer_invariant_def = Define `
infer_invariant st = 
  (* Only substitute for existing uvars *)
  (FDOM st.subst ⊆ count st.next_uvar) ∧
  (* Only uvars that exist can occur in the types substituted in *)
  (!t. t ∈ FRANGE st.subst ⇒ check_t 0 (count st.next_uvar) t)`;

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

val sub_completion_def = Define `
sub_completion tvs st extra_constraints s2 =
  ?s1.
  pure_add_constraints st.subst extra_constraints s1 ∧
  (s2 = t_collapse s1) ∧
  (count st.next_uvar SUBSET FDOM s2) ∧
  (!t. t ∈ FRANGE s2 ⇒ check_t tvs {} t)`;

val sub_completion_unify = Q.prove (
`!st t1 t2 s1 n ts s2 n.
  (t_unify st.subst t1 t2 = SOME s1) ∧
  sub_completion n <| next_uvar := st.next_uvar + 1; subst := s1 |> ts s2
  ⇒
  sub_completion n st ((t1,t2)::ts) s2`,
rw [sub_completion_def, pure_add_constraints_def] >>
qexists_tac `s1'` >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF, count_add1]);

val sub_completion_apply = Q.prove (
`!n uvars s1 ts s2 t1 t2.
  (apply_subst_t (t_collapse s1) t1 = apply_subst_t (t_collapse s1) t2) ∧
  sub_completion n <| next_uvar := uvars; subst := s1 |> ts s2 
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
PairCases_on `h` >>
fs [pure_add_constraints_def] >>
every_case_tac >>
fs [] >>
metis_tac [t_unify_apply2]);

(*
val infer_e_sound = Q.prove (
`(!menv cenv env e st st' ext tenv t extra_constraints s.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    check_menv menv ∧
    sub_completion (num_tvs tenv) st' extra_constraints s
    ⇒
    type_e (convert_menv menv) cenv tenv e 
           (convert_t (apply_subst_t s t))) ∧
 (!menv cenv env es st st' ext tenv ts extra_constraints s.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    check_menv menv ∧
    sub_completion (num_tvs tenv) st' extra_constraints s
    ⇒
    type_es (convert_menv menv) cenv tenv es 
            (MAP (convert_t o apply_subst_t s) ts)) ∧
 (!menv cenv env pes t1 t2 st st' tenv ext extra_constraints s.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    check_menv menv ∧
    sub_completion (num_tvs tenv) st' extra_constraints s
    ⇒
    T) ∧
 (!menv cenv env funs st st' ext tenv extra_constraints s.
    (infer_funs menv cenv env funs st = (Success (), st')) ∧
    check_menv menv ∧
    sub_completion (num_tvs tenv) st' extra_constraints s
    ⇒
    ?env'. type_funs (convert_menv menv) cenv tenv funs env')`,

ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, success_eqns, remove_pair_lem] >>
rw [check_t_def] >>
fs [bind_def, check_env_def, check_t_def] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [apply_subst_t_eqn, convert_t_def, Tbool_def, Tint_def, Tunit_def] >|
[every_case_tac >>
     rw [] >>
     fs [sub_completion_def, flookup_thm, count_add1, FRANGE_DEF] >>
     metis_tac [IN_INSERT, check_convert_freevars, prim_recTheory.LESS_REFL],
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
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
     rw [typeSystemTheory.type_op_cases, Tint_def] >>
     
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
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
