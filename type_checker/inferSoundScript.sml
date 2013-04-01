open preamble;
open MiniMLTheory MiniMLTerminationTheory inferTheory unifyTheory;

val _ = new_theory "inferSound";

val convert_t_def = Define `
(convert_t (Infer_Tvar_db n) = Tvar_db n) ∧
(convert_t (Infer_Tapp ts tc) = Tapp (convert_ts ts) tc) ∧
(convert_ts [] = []) ∧
(convert_ts (t::ts) = convert_t t :: convert_ts ts)`;

val convert_env_def = Define `
(convert_env s [] = []) ∧
(convert_env s ((n,(tvs,t))::env) =
  (n,(tvs,convert_t (apply_subst_t s t)))::convert_env s env)`;

val convert_menv_def = Define `
(convert_menv s [] = []) ∧
(convert_menv s ((mn,env)::menv) =
  ((mn, convert_env s env)::convert_menv s menv))`;

val convert_tenv_def = Define `
(convert_tenv s [] = Empty) ∧
(convert_tenv s ((n,(tvs,t))::tenv) = 
  Bind_name n tvs (convert_t (apply_subst_t s t)) (convert_tenv s tenv))`;

val st_ex_bind_success = Q.prove (
`!f g st st' v. 
 (st_ex_bind f g st = (Success v, st')) =
 ?v' st''. (f st = (Success v', st'')) /\ (g v' st'' = (Success v, st'))`,
rw [st_ex_bind_def] >>
cases_on `f st` >>
rw [] >>
cases_on `q` >>
rw []);

(*
val infer_invariant_def = Define `
infer_invariant st = T`;

val infer_e_sound = Q.prove (
`(!menv cenv env e st st' sub t.
    (infer_e menv cenv env e st = (Success t, st')) ∧
    infer_invariant st ∧
    (sub = t_collapse st'.subst)
    ⇒
    type_e (convert_menv sub menv) cenv (convert_tenv sub env) e 
           (convert_t (apply_subst_t sub t))) ∧
 (!menv cenv env es st st' sub ts.
    (infer_es menv cenv env es st = (Success ts, st')) ∧
    infer_invariant st ∧
    (sub = t_collapse st'.subst)
    ⇒
    type_es (convert_menv sub menv) cenv (convert_tenv sub env) es 
            (MAP (convert_t o apply_subst_t sub) ts)) ∧
 (!menv cenv env pes t1 t2 st st' sub.
    (infer_pes menv cenv env pes t1 t2 st = (Success (), st')) ∧
    infer_invariant st ∧
    (sub = t_collapse st'.subst)
    ⇒
    T) ∧
 (!menv cenv env funs st st' sub env'.
    (infer_funs menv cenv env funs st = (Success (), st')) ∧
    infer_invariant st ∧
    (sub = t_collapse st'.subst)
    ⇒
    ?env'. type_funs (convert_menv sub menv) cenv (convert_tenv sub env) funs env')`,

ho_match_mp_tac infer_e_ind >>
rw [infer_e_def, st_ex_return_def, st_ex_bind_success] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [apply_subst_t_eqn, convert_t_def, Tbool_def, Tint_def, Tunit_def] >|

[fs [fresh_uvar_def] >>
     rw [apply_subst_t_eqn, convert_t_def] >>
     every_case_tac >>
     rw [convert_t_def]
     *)
val _ = export_theory ();
