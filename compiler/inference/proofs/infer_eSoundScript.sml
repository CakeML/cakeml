open preamble;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory infer_tTheory;
open astPropsTheory;
open inferPropsTheory;
open typeSysPropsTheory;

local open typeSoundInvariantsTheory in
end

val o_f_id = Q.prove (
`!m. (\x.x) o_f m = m`,
rw [fmap_EXT]);

val _ = new_theory "infer_eSound";



(* ---------- sub_completion ---------- *)

val sub_completion_unify = Q.prove (
`!st t1 t2 s1 n ts s2 n.
  (t_unify st.subst t1 t2 = SOME s1) ∧
  sub_completion n (st.next_uvar + 1) s1 ts s2
  ⇒
  sub_completion n st.next_uvar st.subst ((t1,t2)::ts) s2`,
rw [sub_completion_def, pure_add_constraints_def] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF, count_add1]);

val sub_completion_unify2 = Q.store_thm ("sub_completion_unify2",
`!st t1 t2 s1 n ts s2 n s3 next_uvar.
  (t_unify s1 t1 t2 = SOME s2) ∧
  sub_completion n next_uvar s2 ts s3
  ⇒
  sub_completion n next_uvar s1 ((t1,t2)::ts) s3`,
rw [sub_completion_def, pure_add_constraints_def]);

val sub_completion_infer = Q.prove (
`!ienv e st1 t st2 n ts2 s.
  (infer_e ienv e st1 = (Success t, st2)) ∧
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

val sub_completion_add_constraints = Q.store_thm ("sub_completion_add_constraints",
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
  (infer_es ienv es st1 = (Success t, st2)) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s`,
induct_on `es` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
res_tac >>
imp_res_tac sub_completion_infer >>
metis_tac [APPEND_ASSOC]);

val sub_completion_infer_p = Q.store_thm ("sub_completion_infer_p",
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
fs []
>- metis_tac [APPEND, sub_completion_more_vars]
>- metis_tac [APPEND, sub_completion_more_vars]
>- metis_tac [APPEND, sub_completion_more_vars]
>- metis_tac [APPEND, sub_completion_more_vars]
>- metis_tac [APPEND, sub_completion_more_vars]
>- metis_tac [APPEND, sub_completion_more_vars]
>- (PairCases_on `v'` >>
    fs [] >>
    metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars])
>- (imp_res_tac sub_completion_add_constraints >>
    PairCases_on `v''` >>
    fs [] >>
    metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars,ADD_COMM])
>- (PairCases_on `v'` >>
    fs [] >>
    metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars])
>- (imp_res_tac sub_completion_unify2 >>
    metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars])
>- metis_tac [APPEND, sub_completion_more_vars]
>- (PairCases_on `v'` >>
    PairCases_on `v''` >>
    fs [] >>
    metis_tac [APPEND_ASSOC]));

val sub_completion_infer_pes = Q.prove (
`!ienv pes t1 t2 st1 t st2 n ts2 s.
  (infer_pes ienv pes t1 t2 st1 = (Success (), st2)) ∧
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
`!ienv funs st1 t st2 n ts2 s.
  (infer_funs ienv funs st1 = (Success t, st2)) ∧
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

val sub_completion_apply = Q.store_thm ("sub_completion_apply",
`!n uvars s1 ts s2 t1 t2.
  t_wfs s1 ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2) ∧
  sub_completion n uvars s1 ts s2
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)`,
rw [sub_completion_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum mp_tac >>
pop_assum mp_tac >>
Q.SPEC_TAC (`s1`, `s1`) >>
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
cases_on `h` >>
fs [pure_add_constraints_def] >>
fs [] >>
metis_tac [t_unify_apply2, t_unify_wfs]);

val sub_completion_apply_list = Q.prove (
`!n uvars s1 ts s2 ts1 ts2.
  t_wfs s1 ∧
  (MAP (t_walkstar s1) ts1 = MAP (t_walkstar s1) ts2) ∧
  sub_completion n uvars s1 ts s2
  ⇒
  (MAP (t_walkstar s2) ts1 = MAP (t_walkstar s2) ts2)`,
induct_on `ts1` >>
rw [] >>
cases_on `ts2` >>
fs [] >>
metis_tac [sub_completion_apply]);

val sub_completion_check = Q.prove (
`!tvs m s uvar s' extra_constraints.
sub_completion m (uvar + tvs) s' extra_constraints s
⇒
EVERY (λn. check_freevars m [] (convert_t (t_walkstar s (Infer_Tuvar (uvar + n))))) (COUNT_LIST tvs)`,
induct_on `tvs` >>
rw [sub_completion_def, COUNT_LIST_SNOC, EVERY_SNOC] >>
fs [sub_completion_def] >|
[qpat_x_assum `!m' s. P m' s` match_mp_tac >>
     rw [] >>
     qexists_tac `s'` >>
     qexists_tac `extra_constraints` >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF],
 fs [SUBSET_DEF] >>
     `uvar+tvs < uvar + SUC tvs`
            by full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF] >>
     metis_tac [check_t_to_check_freevars,ADD_COMM]]);

(* ---------- Soundness ---------- *)

val type_pes_def = Define `
type_pes tenv pes t1 t2 =
  ∀x::set pes.
    (λ(p,e).
       ∃tenv'.
         ALL_DISTINCT (pat_bindings p []) ∧
         type_p (num_tvs tenv.v) tenv p t1 tenv' ∧
         type_e (tenv with v := bind_var_list 0 tenv' tenv.v) e t2) x`;

val type_pes_cons = Q.prove (
`!tenv p e pes t1 t2.
  type_pes tenv ((p,e)::pes) t1 t2 =
  (ALL_DISTINCT (pat_bindings p []) ∧
   (?tenv'.
       type_p (num_tvs tenv.v) tenv p t1 tenv' ∧
       type_e (tenv with v := bind_var_list 0 tenv' tenv.v) e t2) ∧
   type_pes tenv pes t1 t2)`,
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

val infer_p_sound = Q.store_thm ("infer_p_sound",
`(!ienv p st t tenv env st' tvs extra_constraints s.
    (infer_p ienv p st = (Success (t,env), st')) ∧
    t_wfs st.subst ∧
    check_cenv tenv.c ∧
    ienv.inf_c = tenv.c ∧
    ienv.inf_t = tenv.t ∧
    tenv_tabbrev_ok tenv.t ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_p tvs tenv p (convert_t (t_walkstar s t)) (convert_env s env)) ∧
 (!ienv ps st ts tenv env st' tvs extra_constraints s.
    (infer_ps ienv ps st = (Success (ts,env), st')) ∧
    t_wfs st.subst ∧
    check_cenv tenv.c ∧
    ienv.inf_c = tenv.c ∧
    ienv.inf_t = tenv.t ∧
    tenv_tabbrev_ok tenv.t ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_ps tvs tenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env))`,
ho_match_mp_tac infer_p_ind >>
rw [infer_p_def, success_eqns, remove_pair_lem] >>
rw [Once type_p_cases, convert_env_def] >>
imp_res_tac sub_completion_wfs >>
fs [] >>
rw [t_walkstar_eqn1, convert_t_def, Tint_def, Tstring_def, Tchar_def]
>- (match_mp_tac check_t_to_check_freevars >>
    rw [] >>
    fs [sub_completion_def] >>
    qpat_x_assum `!uv. uv ∈ FDOM s ⇒ P uv` match_mp_tac >>
    fs [count_def, SUBSET_DEF])
>- (`?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
    `t_wfs s` by metis_tac [infer_p_wfs] >>
    rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
    fs [convert_env_def] >>
    metis_tac [MAP_MAP_o])
>- (`?ts env. v'' = (ts,env)` by (PairCases_on `v''` >> metis_tac []) >>
    `?tvs ts tn. v' = (tvs,ts,tn)` by (PairCases_on `v'` >> metis_tac []) >>
    rw [] >>
    `type_ps tvs tenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env)`
              by metis_tac [sub_completion_add_constraints, sub_completion_more_vars,ADD_COMM] >>
    rw [] >>
    `t_wfs s` by metis_tac [sub_completion_wfs, infer_p_wfs, pure_add_constraints_wfs] >>
    rw [convert_t_def, t_walkstar_eqn1, MAP_MAP_o, combinTheory.o_DEF,
        EVERY_MAP, LENGTH_COUNT_LIST] >>
    fs [] >- (
      qpat_x_assum`_ + _ = (_:num)`(assume_tac o ONCE_REWRITE_RULE[ADD_COMM] o SYM)
      \\ fsrw_tac[][]
      \\ drule sub_completion_check
      \\ simp[] ) >>
    `t_wfs st'''.subst` by metis_tac [infer_p_wfs] >>
    imp_res_tac pure_add_constraints_apply >>
    pop_assum (fn _ => all_tac) >>
    pop_assum (fn _ => all_tac) >>
    pop_assum mp_tac >>
    rw [MAP_ZIP] >>
    `t_wfs st'.subst` by metis_tac [pure_add_constraints_wfs] >>
    imp_res_tac sub_completion_apply_list >>
    NTAC 6 (pop_assum (fn _ => all_tac)) >>
    pop_assum mp_tac >>
    rw [ONCE_REWRITE_RULE[ADD_COMM](CONJUNCT2 subst_infer_subst_swap)] >>
    `EVERY (check_freevars 0 tvs') ts'` by metis_tac [check_cenv_lookup] >>
    rw [] >>
    fs [convert_env_def] >>
    metis_tac [convert_t_subst, LENGTH_COUNT_LIST, LENGTH_MAP,
               MAP_MAP_o, combinTheory.o_DEF])
>- (`?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
    `t_wfs s` by metis_tac [infer_p_wfs] >>
    rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
    fs [convert_env_def] >>
    metis_tac [])
>- (drule (hd (CONJUNCTS infer_p_wfs)) >>
    disch_then drule >>
    rw [] >>
    drule t_unify_apply >>
    disch_then drule >>
    rw [] >>
    drule t_unify_wfs >>
    disch_then drule >>
    rw [] >>
    drule sub_completion_apply >>
    rpt (disch_then drule) >>
    rw [] >>
    drule check_freevars_type_name_subst >>
    rpt (disch_then drule) >>
    rw [] >>
    drule (hd (CONJUNCTS infer_type_subst_nil)) >>
    rw [] >> fs [] >>
    `check_t 0 {} (infer_type_subst [] (type_name_subst tenv.t t))`
      by metis_tac [infer_type_subst_empty_check] >>
    metis_tac [t_walkstar_no_vars, check_freevars_empty_convert_unconvert_id])
>- (`type_name_subst tenv.t t = convert_t (t_walkstar s t')`
       by (* This is the previous goal *)
          (drule (hd (CONJUNCTS infer_p_wfs)) >>
           disch_then drule >>
           rw [] >>
           drule t_unify_apply >>
           disch_then drule >>
           rw [] >>
           drule t_unify_wfs >>
           disch_then drule >>
           rw [] >>
           drule sub_completion_apply >>
           rpt (disch_then drule) >>
           rw [] >>
           drule check_freevars_type_name_subst >>
           rpt (disch_then drule) >>
           rw [] >>
           drule (hd (CONJUNCTS infer_type_subst_nil)) >>
           rw [] >> fs [] >>
           `check_t 0 {} (infer_type_subst [] (type_name_subst tenv.t t))`
             by metis_tac [infer_type_subst_empty_check] >>
           metis_tac [t_walkstar_no_vars, check_freevars_empty_convert_unconvert_id]) >>
    rw [GSYM convert_env_def] >>
    first_x_assum irule >> rw [] >>
    imp_res_tac sub_completion_unify2 >>
    metis_tac [APPEND_ASSOC, APPEND, sub_completion_add_constraints])
>- (`?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
    `?ts' env'. v'' = (ts',env')` by (PairCases_on `v''` >> metis_tac []) >>
    rw [] >>
    `t_wfs st''.subst` by metis_tac [infer_p_wfs] >>
    `?ts. sub_completion tvs st''.next_uvar st''.subst ts s` by metis_tac [sub_completion_infer_p] >>
    fs [convert_env_def] >>
    metis_tac []));

val letrec_lemma = Q.prove (
`!funs funs_ts s st.
  (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)) =
   MAP (\t. convert_t (t_walkstar s t)) funs_ts)
  ⇒
  (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs))) =
   MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts)`,
induct_on `funs` >>
srw_tac[] [] >>
cases_on `funs_ts` >>
fsrw_tac[] [COUNT_LIST_def] >>
srw_tac[] [] >|
[PairCases_on `h` >>
     rw [],
 qpat_x_assum `!x. P x` match_mp_tac >>
     qexists_tac `st with next_uvar := st.next_uvar + 1` >>
     fsrw_tac[] [MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = x + 1 + y``]]);

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

val binop_tac =
imp_res_tac infer_e_wfs >>
imp_res_tac t_unify_wfs >>
fsrw_tac[] [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer >>
fsrw_tac[] [] >>
res_tac >>
fsrw_tac[] [] >>
imp_res_tac t_unify_apply >>
imp_res_tac sub_completion_apply >>
imp_res_tac t_unify_wfs >>
imp_res_tac sub_completion_wfs >>
fsrw_tac[] [t_walkstar_eqn, t_walk_eqn, convert_t_def, deBruijn_inc_def, check_t_def] >>
srw_tac[] [type_op_cases, Tint_def, Tstring_def, Tref_def, Tfn_def, Texn_def, Tchar_def] >>
metis_tac [MAP, infer_e_next_uvar_mono, check_env_more];

val binop_tac2 =
imp_res_tac infer_e_wfs >>
imp_res_tac t_unify_wfs >>
fsrw_tac[] [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer >>
fsrw_tac[] [] >>
last_x_assum drule >> disch_then drule >> fsrw_tac[] [] >>
disch_then drule >> srw_tac[] [] >>
imp_res_tac t_unify_apply >>
`t_walkstar s t1 = t_walkstar s (Infer_Tapp [] (TC_name (Short "bool")))`
  by metis_tac[sub_completion_apply] >>
imp_res_tac t_unify_wfs >>
imp_res_tac sub_completion_wfs >>
fsrw_tac[] [t_walkstar_eqn, t_walk_eqn, convert_t_def, deBruijn_inc_def, check_t_def]

val constrain_op_sub_completion = Q.prove (
`sub_completion (num_tvs tenv) st.next_uvar st.subst extra_constraints s ∧
 constrain_op op ts st' = (Success t,st)
 ⇒
 ∃c. sub_completion (num_tvs tenv) st'.next_uvar st'.subst c s`,
 rw [] >>
 fs [constrain_op_success] >>
 every_case_tac >>
 fs [success_eqns] >>
 rw [] >>
 fs [infer_st_rewrs] >>
 metis_tac [sub_completion_unify2, sub_completion_unify]);

val constrain_op_sound = Q.prove (
`t_wfs st.subst ∧
 sub_completion (num_tvs tenv) st'.next_uvar st'.subst c s ∧
 constrain_op op ts st = (Success t,st')
 ⇒
 type_op op (MAP (convert_t o t_walkstar s) ts) (convert_t (t_walkstar s t))`,
 fs [constrain_op_def, type_op_cases] >>
 every_case_tac >>
 fs [success_eqns] >>
 rw [] >>
 fs [infer_st_rewrs,Tchar_def] >>
 binop_tac);

local val rw = srw_tac[] val fs = fsrw_tac[] val rfs = rev_full_simp_tac(srw_ss()) in
val infer_e_sound = Q.store_thm ("infer_e_sound",
`(!ienv e st st' tenv t extra_constraints s.
    infer_e ienv e st = (Success t, st') ∧
    check_menv ienv.inf_m ∧
    menv_alpha ienv.inf_m tenv.m ∧
    check_cenv ienv.inf_c ∧
    ienv.inf_c = tenv.c ∧
    ienv.inf_t = tenv.t ∧
    tenv_tabbrev_ok tenv.t ∧
    check_env (count st.next_uvar) ienv.inf_v ∧
    t_wfs st.subst ∧
    sub_completion (num_tvs tenv.v) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s ienv.inf_v tenv.v
    ⇒
    type_e tenv e (convert_t (t_walkstar s t))) ∧
 (!ienv es st st' tenv ts extra_constraints s.
    infer_es ienv es st = (Success ts, st') ∧
    check_menv ienv.inf_m ∧
    menv_alpha ienv.inf_m tenv.m ∧
    check_cenv ienv.inf_c ∧
    ienv.inf_c = tenv.c ∧
    ienv.inf_t = tenv.t ∧
    tenv_tabbrev_ok tenv.t ∧
    check_env (count st.next_uvar) ienv.inf_v ∧
    t_wfs st.subst ∧
    sub_completion (num_tvs tenv.v) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s ienv.inf_v tenv.v
    ⇒
    type_es tenv es (MAP (convert_t o t_walkstar s) ts)) ∧
 (!ienv pes t1 t2 st st' tenv extra_constraints s.
    infer_pes ienv pes t1 t2 st = (Success (), st') ∧
    check_menv ienv.inf_m ∧
    menv_alpha ienv.inf_m tenv.m ∧
    check_cenv ienv.inf_c ∧
    ienv.inf_c = tenv.c ∧
    ienv.inf_t = tenv.t ∧
    tenv_tabbrev_ok tenv.t ∧
    check_env (count st.next_uvar) ienv.inf_v ∧
    t_wfs st.subst ∧
    sub_completion (num_tvs tenv.v) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s ienv.inf_v tenv.v
    ⇒
    type_pes tenv pes (convert_t (t_walkstar s t1)) (convert_t (t_walkstar s t2))) ∧
 (!ienv funs st st' tenv extra_constraints s ts.
    infer_funs ienv funs st = (Success ts, st') ∧
    check_menv ienv.inf_m ∧
    menv_alpha ienv.inf_m tenv.m ∧
    check_cenv ienv.inf_c ∧
    ienv.inf_c = tenv.c ∧
    ienv.inf_t = tenv.t ∧
    tenv_tabbrev_ok tenv.t ∧
    check_env (count st.next_uvar) ienv.inf_v ∧
    t_wfs st.subst ∧
    sub_completion (num_tvs tenv.v) st'.next_uvar st'.subst extra_constraints s ∧
    tenv_inv s ienv.inf_v tenv.v ∧
    ALL_DISTINCT (MAP FST funs)
    ⇒
    type_funs tenv funs (MAP2 (\(x,y,z) t. (x, (convert_t o t_walkstar s) t)) funs ts))`,
  ho_match_mp_tac infer_e_ind >>
  rw [infer_e_def, success_eqns, remove_pair_lem] >>
  rw [check_t_def] >>
  fs [check_t_def, check_env_bind, check_env_merge] >>
  ONCE_REWRITE_TAC [type_e_cases] >>
  rw [Tint_def, Tchar_def]
  >-
  (* Raise *)
     (fs [sub_completion_def, flookup_thm, count_add1, SUBSET_DEF] >>
     `st''.next_uvar < st''.next_uvar + 1` by decide_tac >>
     metis_tac [IN_INSERT, check_convert_freevars, prim_recTheory.LESS_REFL])
  >-
 (* Raise *)
     (imp_res_tac sub_completion_unify >>
     `type_e tenv e (convert_t (t_walkstar s t2))` by metis_tac [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_apply >>
     imp_res_tac t_unify_wfs >>
     fs [] >>
     rw [] >>
     imp_res_tac sub_completion_wfs >>
     fs [t_walkstar_eqn1, convert_t_def, Texn_def])
  >- (
    Cases_on `pes` >>
    fs [failwith_def, success_eqns] >>
    first_x_assum match_mp_tac >>
    rw [] >>
    `?ts. sub_completion (num_tvs tenv.v) st''.next_uvar st''.subst  ts s`
              by (imp_res_tac sub_completion_infer_pes >>
                  fs [] >>
                  metis_tac [sub_completion_more_vars]) >>
     metis_tac [])
  >-
     (
     Cases_on `pes = []` >>
     fs [failwith_def, success_eqns] >>
     `?ts. sub_completion (num_tvs tenv.v) st''.next_uvar st''.subst  ts s`
              by (imp_res_tac sub_completion_infer_pes >>
                  fs [] >>
                  metis_tac [sub_completion_more_vars]) >>
     rw [RES_FORALL] >>
     `?p e. x = (p,e)` by (PairCases_on `x` >> metis_tac []) >>
     rw [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     `st.next_uvar ≤ st''.next_uvar` by metis_tac [infer_e_next_uvar_mono] >>
     `check_env (count st''.next_uvar) ienv.inf_v` by metis_tac [check_env_more] >>
     `type_pes tenv pes (convert_t (t_walkstar s (Infer_Tapp [] TC_exn))) (convert_t (t_walkstar s t))`
              by metis_tac [] >>
     fs [type_pes_def, RES_FORALL] >>
     pop_assum (mp_tac o Q.SPEC `(p,e')`) >>
     rw [Texn_def] >>
     imp_res_tac sub_completion_wfs >>
     fs [t_walkstar_eqn1, convert_t_def, Texn_def] >>
     metis_tac [])
  >-
 (* Lit int *)
     binop_tac
  >-
 (* Lit char *)
     binop_tac
  >-
 (* Lit string *)
     binop_tac
 (* Lit word8 *)
 >- binop_tac
 (* Lit word64 *)
 >- binop_tac
 (* Var short *)
 >-
     (rw [t_lookup_var_id_def] >>
     `?tvs t. v' = (tvs, t)`
                by (PairCases_on `v'` >>
                    rw []) >>
     rw [] >>
     fs[tenv_inv_def]>>res_tac>>
     fs[check_env_def]>>pop_assum mp_tac>> IF_CASES_TAC>>rw[]
     >-
       (fs[sub_completion_def]>>
        Q.ISPECL_THEN [`t`,`s`,`tvs`,`st.next_uvar`,`num_tvs tenv.v`] mp_tac (db_subst_infer_subst_swap|>CONJ_PAIR|>fst) >>
        impl_keep_tac>-
          (fs[]>>
          metis_tac[pure_add_constraints_wfs,check_t_more])
        >>
        rw[] >>
        imp_res_tac inc_wfs>>
        pop_assum kall_tac>>pop_assum (qspec_then`tvs` assume_tac)>>
        imp_res_tac t_walkstar_no_vars>>fs[]>>
        qpat_x_assum`A=convert_t t` (SUBST_ALL_TAC o SYM)>>
        fs[]>>
        qpat_abbrev_tac `ls:t list = MAP A (MAP B (COUNT_LIST tvs))`>>
        assume_tac (deBruijn_subst2|>CONJ_PAIR|>fst)>>
        pop_assum(qspecl_then[`t'`,`0`,`subst`,`ls`,`ARB`] mp_tac)>>
        impl_tac>-fs[]>>
        rw[]>>
        fs[deBruijn_inc0]>>
        qexists_tac`MAP (deBruijn_subst 0 ls) subst`>>
        fs[EVERY_MAP]>>
        (*
          Almost done:
          Need something like num_tvs tenv ≥ tvs
          i.e. that the type system's env is consistent
        *)
        fs[EVERY_MEM]>>rw[]>>
        match_mp_tac deBruijn_subst_check_freevars2>>
        fs[Abbr`ls`,LENGTH_COUNT_LIST]>>
        fs[EVERY_MAP,EVERY_MEM,MEM_COUNT_LIST]>>rw[]>>
        `st.next_uvar+ n' ∈ FDOM s` by
          fs[SUBSET_DEF]>>
        metis_tac[check_t_to_check_freevars])
     >>
       (qexists_tac`[]`>>fs[COUNT_LIST_def,infer_deBruijn_subst_id,deBruijn_subst_id]>>
       fs[COUNT_LIST_def,infer_deBruijn_subst_id,sub_completion_def]>>
       metis_tac[deBruijn_subst_nothing]))
 >-
 (* Var long *)
     (
     rw [t_lookup_var_id_def]>>
     fs[menv_alpha_def,fmap_rel_OPTREL_FLOOKUP]>>
     last_x_assum(qspec_then`mn` assume_tac)>>
     rfs[optionTheory.OPTREL_def]>>
     fs[tenv_alpha_def,tenv_inv_def]>>
      `?tvs t. v' = (tvs, t)`
                by (PairCases_on `v'` >>
                    rw []) >>
     fs[GSYM bvl2_lookup]>>
     res_tac>>
     fs[]>>
     pop_assum mp_tac>>IF_CASES_TAC>>rw[]
     >-
       (fs[sub_completion_def]>>
        Q.ISPECL_THEN [`t`,`s`,`tvs`,`st.next_uvar`,`num_tvs tenv.v`] mp_tac (db_subst_infer_subst_swap|>CONJ_PAIR|>fst) >>
        impl_keep_tac>-
          (fs[]>>
          metis_tac[pure_add_constraints_wfs,check_t_more])
        >>
        rw[] >>
        imp_res_tac inc_wfs>>
        pop_assum kall_tac>>pop_assum (qspec_then`tvs` assume_tac)>>
        imp_res_tac t_walkstar_no_vars>>fs[]>>
        qpat_x_assum`A=convert_t t` (SUBST_ALL_TAC o SYM)>>
        fs[]>>
        qpat_abbrev_tac `ls:t list = MAP A (MAP B (COUNT_LIST tvs))`>>
        assume_tac (deBruijn_subst2|>CONJ_PAIR|>fst)>>
        pop_assum(qspecl_then[`t''`,`0`,`subst`,`ls`,`ARB`] mp_tac)>>
        impl_tac>-
          fs[]>>
        rw[]>>
        fs[deBruijn_inc0]>>
        qexists_tac`MAP (deBruijn_subst 0 ls) subst`>>
        fs[EVERY_MAP]>>
        fs[EVERY_MEM]>>rw[]>>
        match_mp_tac deBruijn_subst_check_freevars2>>
        fs[Abbr`ls`,LENGTH_COUNT_LIST]>>
        fs[EVERY_MAP,EVERY_MEM,MEM_COUNT_LIST]>>rw[]>>
        `st.next_uvar+ n' ∈ FDOM s` by
          fs[SUBSET_DEF]>>
        metis_tac[check_t_to_check_freevars])
     >>
     (qexists_tac`[]`>>fs[COUNT_LIST_def,infer_deBruijn_subst_id,deBruijn_subst_id]>>
      fs[COUNT_LIST_def,infer_deBruijn_subst_id,sub_completion_def]>>
      fs[check_menv_def,FEVERY_ALL_FLOOKUP]>>
      res_tac>>
      imp_res_tac ALOOKUP_MEM>>
      fs[EVERY_MEM,FORALL_PROD]>>
      metis_tac[]))
 >-
 (* Tup *)
     (`?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs, pure_add_constraints_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
     metis_tac [MAP_MAP_o])
 >-
 (* Con *)
     (`?tvs ts t. v' = (tvs, ts, t)` by (PairCases_on `v'` >> rw []) >>
     rw [] >>
     fs [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs, pure_add_constraints_wfs] >>
     rw [convert_t_def, t_walkstar_eqn1, MAP_MAP_o, combinTheory.o_DEF,
         EVERY_MAP, LENGTH_COUNT_LIST] >-
     metis_tac [sub_completion_check] >>
     `type_es tenv es (MAP (convert_t o t_walkstar s) ts'')`
             by (imp_res_tac sub_completion_add_constraints >>
                 `sub_completion (num_tvs tenv.v) st'''.next_uvar st'''.subst
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
     `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac pure_add_constraints_apply >>
     pop_assum (fn _ => all_tac) >>
     pop_assum (fn _ => all_tac) >>
     pop_assum mp_tac >>
     rw [MAP_ZIP] >>
     `t_wfs st'.subst` by metis_tac [pure_add_constraints_wfs] >>
     `MAP (t_walkstar s) ts'' =
       MAP (t_walkstar s)
         (MAP
            (infer_type_subst
               (ZIP
                  (tvs,
                   MAP (λn. Infer_Tuvar (st'''.next_uvar + n))
                     (COUNT_LIST (LENGTH tvs))))) ts)`
                 by metis_tac [sub_completion_apply_list] >>
     pop_assum mp_tac >>
     rw [subst_infer_subst_swap] >>
     `EVERY (check_freevars 0 tvs) ts` by metis_tac [check_cenv_lookup] >>
     metis_tac [convert_t_subst, LENGTH_COUNT_LIST, LENGTH_MAP,
                MAP_MAP_o, combinTheory.o_DEF])
 >-
 (* Fun *)
     (`t_wfs s ∧ t_wfs st'.subst` by metis_tac [infer_st_rewrs,sub_completion_wfs, infer_e_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tfn_def] >>
     imp_res_tac infer_e_next_uvar_mono >>
     fs [] >>
     `st.next_uvar < st'.next_uvar` by decide_tac >|
     [fs [sub_completion_def, SUBSET_DEF] >>
          metis_tac [check_t_to_check_freevars],
      `tenv_inv s
                 ((x,0,Infer_Tuvar st.next_uvar)::ienv.inf_v)
                 (Bind_name x 0
                            (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar)))
                            tenv.v)`
             by (match_mp_tac tenv_inv_extend0 >>
                 fs []) >>
          fs [] >>
          `check_t 0 (count (st with next_uvar := st.next_uvar + 1).next_uvar) (Infer_Tuvar st.next_uvar)`
                     by rw [check_t_def] >>
          `check_env (count (st with next_uvar := st.next_uvar + 1).next_uvar) ienv.inf_v`
                     by (rw [] >>
                         metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]) >>
          first_x_assum match_mp_tac>>
          rw [] >>
          HINT_EXISTS_TAC>>
          qexists_tac`st with next_uvar := st.next_uvar +1`>>
          fs[num_tvs_def]>>
          metis_tac[]])
 >-
 (* App *)
     (`?c. sub_completion (num_tvs tenv.v) st''.next_uvar st''.subst c s`
           by metis_tac [constrain_op_sub_completion] >>
     res_tac >>
     metis_tac [constrain_op_sound, infer_e_wfs])
 >-
 (* Log *)
     binop_tac2
 >-
 (* Log *)
     binop_tac2
 >-
 (* If *)
 (
  imp_res_tac infer_e_wfs >>
  imp_res_tac t_unify_wfs >>
  fsrw_tac[] [] >>
  imp_res_tac sub_completion_unify2 >>
  imp_res_tac sub_completion_infer >>
  fsrw_tac[] [] >>
  first_x_assum(fn th => drule th >> disch_then drule) >>
  fsrw_tac[][] >>
  imp_res_tac infer_e_next_uvar_mono >>
  imp_res_tac check_env_more >> fsrw_tac[][] >>
  disch_then drule >> srw_tac[][] >>
  imp_res_tac t_unify_apply >>
  imp_res_tac t_unify_wfs >>
  fsrw_tac[][] >>
  `t_walkstar s t2 = t_walkstar s (Infer_Tapp [] (TC_name (Short "bool")))`
    by metis_tac[sub_completion_apply] >>
  imp_res_tac sub_completion_wfs >>
  fsrw_tac[] [t_walkstar_eqn, t_walk_eqn, convert_t_def, deBruijn_inc_def, check_t_def]
 )

 >-
 (* If *)
     (imp_res_tac sub_completion_unify2 >>
     imp_res_tac sub_completion_infer >>
     imp_res_tac sub_completion_infer >>
     fs [] >>
     imp_res_tac sub_completion_unify2 >>
     `type_e tenv e (convert_t (t_walkstar s t1))`
             by metis_tac [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_apply >>
     `t_wfs s'`  by metis_tac [t_unify_wfs] >>
     imp_res_tac sub_completion_apply >>
     `t_wfs s` by metis_tac [sub_completion_wfs] >>
     fs [t_walkstar_eqn, t_walk_eqn, convert_t_def])
 >-
 (* If *)
     (`t_wfs (st'' with subst := s').subst`
                by (rw [] >>
                    metis_tac [t_unify_wfs, infer_e_wfs]) >>
     `st.next_uvar ≤ (st'' with subst := s').next_uvar`
                by (imp_res_tac infer_e_next_uvar_mono >>
                    fs [] >>
                    decide_tac) >>
     `check_env (count (st'' with subst := s').next_uvar) ienv.inf_v`
                by (metis_tac [check_env_more]) >>
     `?ts. sub_completion (num_tvs tenv.v) st'''''.next_uvar st'''''.subst ts s`
               by metis_tac [sub_completion_unify2] >>
     imp_res_tac sub_completion_infer >>
     metis_tac [])
  >-
 (* If *)
     (`t_wfs (st'' with subst := s').subst`
                by (rw [] >>
                    metis_tac [t_unify_wfs, infer_e_wfs]) >>
     `t_wfs st''''.subst ∧ t_wfs st'''''.subst ∧ t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     `st.next_uvar ≤ st''''.next_uvar`
                by (imp_res_tac infer_e_next_uvar_mono >>
                    fs [] >>
                    decide_tac) >>
     `check_env (count st''''.next_uvar) ienv.inf_v` by metis_tac [check_env_more] >>
     `?ts. sub_completion (num_tvs tenv.v) st'''''.next_uvar st'''''.subst ts s`
               by metis_tac [sub_completion_unify2] >>
     `type_e tenv e'' (convert_t (t_walkstar s t3))` by metis_tac [] >>
     imp_res_tac t_unify_apply >>
     `t_wfs s''` by metis_tac [t_unify_wfs] >>
     imp_res_tac sub_completion_apply >>
     metis_tac [])
  >-
 (* Match *)
     (Cases_on `pes = []` >>
      fs [failwith_def, success_eqns] >>
      `?ts. sub_completion (num_tvs tenv.v) st''.next_uvar st''.subst  ts s`
              by (imp_res_tac sub_completion_infer_pes >>
                  fs [] >>
                  metis_tac [sub_completion_more_vars]) >>
     `type_e tenv e (convert_t (t_walkstar s t1))` by metis_tac [] >>
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
     `check_env (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) ienv.inf_v` by metis_tac [check_env_more] >>
     `type_pes tenv pes (convert_t (t_walkstar s t1)) (convert_t (t_walkstar s (Infer_Tuvar st''.next_uvar)))`
              by metis_tac [] >>
     fs [type_pes_def, RES_FORALL] >>
     pop_assum (mp_tac o Q.SPEC `(p,e')`) >>
     rw [])
 >-
 (* Let *)
     (* COMPLETENESS disj2_tac >>*)
     (imp_res_tac sub_completion_infer >>
     fs [] >>
     imp_res_tac sub_completion_unify >>
     qexists_tac `convert_t (t_walkstar s t1)` >>
     rw [] >-
     metis_tac [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_wfs >>
     `tenv_inv s (opt_bind x (0,t1) ienv.inf_v)
                 (opt_bind_name x 0 (convert_t (t_walkstar s t1)) tenv.v)`
            by (cases_on `x` >>
                fs [opt_bind_def, opt_bind_name_def] >>
                match_mp_tac tenv_inv_extend0 >>
                metis_tac[sub_completion_wfs])>>
     `num_tvs (opt_bind_name x 0 (convert_t (t_walkstar s t1)) tenv.v) = num_tvs tenv.v`
            by (cases_on `x` >>
                rw [opt_bind_name_def] >>
                rw [num_tvs_def]) >>
     `check_t 0 (count st''.next_uvar) t1` by metis_tac [infer_e_check_t] >>
     `check_env (count st''.next_uvar) ienv.inf_v` by metis_tac [infer_e_next_uvar_mono, check_env_more] >>
     `check_env (count st''.next_uvar) (opt_bind x (0,t1) ienv.inf_v)`
               by (cases_on `x` >>
                   fs [opt_bind_def, check_env_def]) >>
     first_x_assum match_mp_tac >>
     rw [] >>
     metis_tac [])
 >-
 (* Letrec *)
     (`t_wfs (st with next_uvar := st.next_uvar + LENGTH funs).subst`
               by rw [] >>
     Q.ABBREV_TAC `env' = MAP2 (λ(f,x,e) uvar. (f,0:num,uvar)) funs (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH funs)))` >>
     Q.ABBREV_TAC `tenv' = MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)))` >>
     `sub_completion (num_tvs (bind_var_list 0 tenv' tenv.v)) st'.next_uvar st'.subst extra_constraints s`
                 by metis_tac [num_tvs_bind_var_list] >>
     `?constraints1. sub_completion (num_tvs (bind_var_list 0 tenv' tenv.v)) st''''.next_uvar st''''.subst constraints1 s`
                 by metis_tac [sub_completion_infer] >>
     `?constraints2. sub_completion (num_tvs (bind_var_list 0 tenv' tenv.v)) st'''.next_uvar st'''.subst constraints2 s`
                 by metis_tac [sub_completion_add_constraints] >>
     `tenv_inv s (env' ++ ienv.inf_v) (bind_var_list 0 tenv' tenv.v)`
                 by (UNABBREV_ALL_TAC >>
                     match_mp_tac tenv_inv_letrec_merge >>fs[]>>
                     imp_res_tac infer_e_wfs>>
                     fs[]>>rfs[]>>
                     metis_tac[pure_add_constraints_wfs,sub_completion_wfs])>>
     `check_env (count (st with next_uvar := st.next_uvar + LENGTH funs).next_uvar) (env' ++ ienv.inf_v)`
                 by (rw [check_env_merge] >|
                     [Q.UNABBREV_TAC `env'` >>
                          rw [check_env_letrec_lem],
                      metis_tac [check_env_more, DECIDE ``x ≤ x+y:num``]]) >>
     `type_funs (tenv with v := bind_var_list 0 tenv' tenv.v) funs
                (MAP2 (\(x,y,z) t. (x, convert_t (t_walkstar s t))) funs funs_ts)`
                 by (first_x_assum match_mp_tac >>
                     rw [] >>
                     metis_tac []) >>
     `t_wfs st''''.subst` by metis_tac [infer_e_wfs, pure_add_constraints_wfs] >>
     `st.next_uvar + LENGTH funs ≤ st''''.next_uvar`
                 by (fs [] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     fs [] >>
                     metis_tac []) >>
     fs [] >>
     `type_e (tenv with v := bind_var_list 0 tenv' tenv.v) e (convert_t (t_walkstar s t))`
             by (first_x_assum match_mp_tac >>
                 rw [] >>
                 metis_tac [check_env_more]) >>
     qexists_tac `tenv'` >>
     (* COMPLETENESS qexists_tac `0` >>*)
     rw [bind_tvar_def] >>
     `tenv' = MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts`
                 by (Q.UNABBREV_TAC `tenv'` >>
                     match_mp_tac letrec_lemma >>
                     imp_res_tac infer_e_wfs >>
                     imp_res_tac pure_add_constraints_apply >>
                     `LENGTH funs = LENGTH funs_ts` by metis_tac [LENGTH_COUNT_LIST] >>
                     fs [GSYM MAP_MAP_o, MAP_ZIP, LENGTH_COUNT_LIST, LENGTH_MAP] >>
                     metis_tac [MAP_MAP_o, combinTheory.o_DEF, sub_completion_apply_list]) >>
     rw [])
 >- (* Tannot*)
    (drule (hd (CONJUNCTS infer_e_wfs)) >>
     disch_then drule >>
     rw [] >>
     drule t_unify_apply >>
     disch_then drule >>
     rw [] >>
     drule t_unify_wfs >>
     disch_then drule >>
     imp_res_tac sub_completion_wfs >>
     rw [] >>
     drule sub_completion_apply >>
     rpt (disch_then drule) >>
     rw [] >>
     drule check_freevars_type_name_subst >>
     rpt (disch_then drule) >>
     rw [] >>
     drule (hd (CONJUNCTS infer_type_subst_nil)) >>
     rw [] >> fs [] >>
     `check_t 0 {} (infer_type_subst [] (type_name_subst tenv.t t))`
       by metis_tac [infer_type_subst_empty_check] >>
     metis_tac [t_walkstar_no_vars, check_freevars_empty_convert_unconvert_id])
 >- (* Tannot*)
    (`type_name_subst tenv.t t = convert_t (t_walkstar s t')`
       by (* This is the previous goal *)
       (drule (hd (CONJUNCTS infer_e_wfs)) >>
        disch_then drule >>
        rw [] >>
        drule t_unify_apply >>
        disch_then drule >>
        rw [] >>
        drule t_unify_wfs >>
        disch_then drule >>
        imp_res_tac sub_completion_wfs >>
        rw [] >>
        drule sub_completion_apply >>
        rpt (disch_then drule) >>
        rw [] >>
        drule check_freevars_type_name_subst >>
        rpt (disch_then drule) >>
        rw [] >>
        drule (hd (CONJUNCTS infer_type_subst_nil)) >>
        rw [] >> fs [] >>
        `check_t 0 {} (infer_type_subst [] (type_name_subst tenv.t t))`
          by metis_tac [infer_type_subst_empty_check] >>
        metis_tac [t_walkstar_no_vars, check_freevars_empty_convert_unconvert_id]) >>
     rw [] >>
     first_x_assum irule >> rw [] >>
     imp_res_tac sub_completion_unify2 >>
     metis_tac [APPEND_ASSOC, APPEND, sub_completion_add_constraints])
 >-
 metis_tac [sub_completion_infer_es]
 >-
 metis_tac [infer_e_wfs, infer_e_next_uvar_mono, check_env_more]
 >-
 rw [type_pes_def, RES_FORALL]
 >-
 (`?t env'. v' = (t,env')` by (PairCases_on `v'` >> metis_tac []) >>
     rw [] >>
     `∃ts. sub_completion (num_tvs tenv.v) (st'''' with subst:= s'').next_uvar (st'''' with subst:= s'').subst ts s`
                   by metis_tac [sub_completion_infer_pes] >>
     fs [] >>
     `∃ts. sub_completion (num_tvs tenv.v) st''''.next_uvar st''''.subst ts s`
              by metis_tac [sub_completion_unify2] >>
     `∃ts. sub_completion (num_tvs tenv.v) (st'' with subst := s').next_uvar (st'' with subst := s').subst ts s`
              by metis_tac [sub_completion_infer] >>
     fs [] >>
     `∃ts. sub_completion (num_tvs tenv.v) st''.next_uvar st''.subst ts s`
              by metis_tac [sub_completion_unify2] >>
     `type_p (num_tvs tenv.v) tenv p (convert_t (t_walkstar s t)) (convert_env s env')`
              by metis_tac [infer_p_sound] >>
     `t_wfs (st'' with subst := s').subst`
           by (rw [] >>
               metis_tac [infer_p_wfs, t_unify_wfs]) >>
     imp_res_tac infer_p_check_t >>
     `check_env (count (st'' with subst:=s').next_uvar) (MAP (λ(n,t). (n,0,t)) (SND (t,env')) ++ ienv.inf_v)`
           by (rw [check_env_merge] >|
               [rw [check_env_def, EVERY_MAP, remove_pair_lem] >>
                    fs [EVERY_MEM] >>
                    rw [] >>
                    qpat_x_assum `!e. MEM e _ ⇒ P e` (fn th => first_assum (mp_tac o MATCH_MP th)) >>
                    PairCases_on `x` >>
                    rw [],
                metis_tac [infer_p_next_uvar_mono, check_env_more]]) >>
     `tenv_inv s (MAP (λ(n,t). (n,0,t)) env' ++ ienv.inf_v) (bind_var_list 0 (convert_env s env') tenv.v)`
              by (
              match_mp_tac tenv_inv_merge>>fs[]>>
              metis_tac[sub_completion_wfs])>>
     `type_e (tenv with v := bind_var_list 0 (convert_env s env') tenv.v) e (convert_t (t_walkstar s t2'))`
               by (first_x_assum match_mp_tac >>
                   rw [] >>
                   metis_tac [check_env_merge, SND, num_tvs_bind_var_list]) >>
     rw [type_pes_cons] >|
     [imp_res_tac infer_p_bindings >>
          metis_tac [APPEND_NIL],
      qexists_tac `(convert_env s env')` >>
           rw [] >>
           imp_res_tac infer_p_wfs >>
           imp_res_tac infer_e_wfs >>
           imp_res_tac t_unify_apply >>
           metis_tac [t_unify_wfs, sub_completion_apply],
      `t_wfs (st'''' with subst := s'').subst`
           by (rw [] >>
               metis_tac [t_unify_wfs, infer_e_wfs]) >>
          `(st.next_uvar ≤ (st'''' with subst := s'').next_uvar)`
                  by (fs [] >>
                      imp_res_tac infer_p_next_uvar_mono >>
                      imp_res_tac infer_e_next_uvar_mono >>
                      fs [] >>
                      decide_tac) >>
          `check_env (count (st'''' with subst := s'').next_uvar) ienv.inf_v` by metis_tac [check_env_more] >>
          metis_tac []])

>- (
 `t_wfs st'''.subst ∧ t_wfs (st with next_uvar := st.next_uvar + 1).subst` by metis_tac [infer_e_wfs, infer_st_rewrs] >>
     imp_res_tac sub_completion_infer_funs >>
     `tenv_inv s ((x,0,Infer_Tuvar st.next_uvar)::ienv.inf_v) (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv.v)`
              by (match_mp_tac tenv_inv_extend0 >>
                  fs[]>>metis_tac[sub_completion_wfs])>>
     `num_tvs (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv.v) = num_tvs tenv.v`
              by fs [num_tvs_def] >>
     `check_env (count (st with next_uvar := st.next_uvar + 1).next_uvar) ienv.inf_v ∧
      check_t 0 (count (st with next_uvar := st.next_uvar + 1).next_uvar) (Infer_Tuvar st.next_uvar)`
                by (rw [check_t_def] >>
                    metis_tac [check_env_more, DECIDE ``x ≤ x + 1:num``]) >>
     `type_e (tenv with v := Bind_name x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenv.v) e (convert_t (t_walkstar s t))`
                 by (first_x_assum match_mp_tac >>
                     rw [] >>
                     metis_tac []) >>
     `check_env (count st'''.next_uvar) ienv.inf_v`
                 by (metis_tac [check_env_more, infer_e_next_uvar_mono]) >>
     `type_funs tenv funs (MAP2 (\(x,y,z) t. (x, convert_t (t_walkstar s t))) funs ts')`
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
                             fs [check_env_bind]) >>
               metis_tac [check_t_more5]],
      imp_res_tac infer_funs_length >>
          rw [ALOOKUP_FAILS, MAP2_MAP, MEM_MAP, MEM_ZIP] >>
          PairCases_on `y` >>
          fs [MEM_MAP, MEM_EL] >>
          metis_tac [FST]]));
end

val _ = export_theory ();
