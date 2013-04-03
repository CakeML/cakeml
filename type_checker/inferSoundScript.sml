open preamble;
open MiniMLTheory MiniMLTerminationTheory inferTheory unifyTheory;

val _ = new_theory "inferSound";

val flookup_thm = Q.prove (
`!f x v. ((FLOOKUP f x = NONE) = x ∉ FDOM f) ∧
         ((FLOOKUP f x = SOME v) = x ∈ FDOM f ∧ (f ' x = v))`,
rw [FLOOKUP_DEF]);

val count_add1 = Q.prove (
`!n. count (n + 1) = n INSERT count n`,
metis_tac [COUNT_SUC, arithmeticTheory.ADD1]);

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

val apply_subst_success = Q.prove (
`!t1 st1 t2 st2.
  (apply_subst t1 st1 = (Success t2, st2))
  =
  ((st2 = st1 with subst := t_collapse st1.subst) ∧
   (t2 = apply_subst_t (t_collapse st1.subst) t1))`,
rw [LET_THM, apply_subst_def] >>
eq_tac >>
rw []);

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

val sub_ext_def = Define `
sub_ext dom num_tvs sub ext =
  (FDOM ext = dom DIFF FDOM sub) ∧
  (!t. t ∈ FRANGE ext ⇒ check_t num_tvs {} t)`;

val check_convert_freevars = Q.prove (
`(!tvs uvs t. check_t tvs uvs t ⇒ (uvs = {}) ⇒ check_freevars tvs [] (convert_t t))`,
ho_match_mp_tac (fetch "-" "check_t_ind") >>
rw [check_freevars_def, check_t_def, convert_t_def] >>
fs [EVERY_MEM, MEM_MAP] >>
metis_tac []);

(*
val infer_e_sound = Q.prove (
`(!menv cenv env e st st' ext tenv t.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    check_menv menv ∧
    infer_invariant st ∧
    sub_ext (count st'.next_uvar) (num_tvs tenv) st'.subst ext ∧
    tenv_rel (st'.subst ⊌ ext) env tenv
    ⇒
    type_e (convert_menv menv) cenv tenv e 
           (convert_t (apply_subst_t (st'.subst ⊌ ext) t))) ∧
 (!menv cenv env es st st' ext tenv ts.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    check_menv menv ∧
    infer_invariant st ∧
    sub_ext (count st'.next_uvar) (num_tvs tenv) st'.subst ext ∧
    tenv_rel (st'.subst ⊌ ext) env tenv
    ⇒
    type_es (convert_menv menv) cenv tenv es 
            (MAP (convert_t o apply_subst_t (st'.subst ⊌ ext)) ts)) ∧
 (!menv cenv env pes t1 t2 st st' tenv ext.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    check_menv menv ∧
    infer_invariant st ∧
    sub_ext (count st'.next_uvar) (num_tvs tenv) st'.subst ext ∧
    tenv_rel (st'.subst ⊌ ext) env tenv
    ⇒
    T) ∧
 (!menv cenv env funs st st' ext tenv.
    (infer_funs menv cenv env funs st = (Success (), st')) ∧
    check_menv menv ∧
    infer_invariant st ∧
    sub_ext (count st'.next_uvar) (num_tvs tenv) st'.subst ext ∧
    tenv_rel (st'.subst ⊌ ext) env tenv
    ⇒
    ?env'. type_funs (convert_menv menv) cenv tenv funs env')`,

ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, st_ex_return_def, st_ex_bind_success, failwith_def] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [apply_subst_t_eqn, convert_t_def, Tbool_def, Tint_def, Tunit_def] >|

[fs [fresh_uvar_success] >>
     rw [apply_subst_t_eqn, convert_t_def] >>
     fs [infer_invariant_def, sub_ext_def, LET_THM, FLOOKUP_FUNION] >>
     every_case_tac >>
     rw [convert_t_def] >>
     fs [flookup_thm, count_add1, FRANGE_DEF, SUBSET_DEF] >>
     metis_tac [IN_INSERT, check_convert_freevars, prim_recTheory.LESS_REFL],

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
