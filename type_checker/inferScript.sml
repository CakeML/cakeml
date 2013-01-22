open preamble MiniMLTheory MiniMLTerminationTheory;
open check_annotatedTheory;
open stringTheory monadsyntax;

val _ = new_theory "infer";

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *), 
val _ = type_abbrev("M", ``:'a -> ('b, 'c) exc # 'a``);
val st_ex_bind_def = Define `
(st_ex_bind : (α, β, γ) M -> (β -> (α, δ, γ) M) -> (α, δ, γ) M) x f =
  λs.
    case x s of
      (Success y,s) => f y s
    | (Failure e,s) => (Failure e,s)`;

val st_ex_return_def = Define `
(st_ex_return (*: α -> (β, α, γ) M*)) x = 
  λs. (Success x, s)`;

(*
val monad_bind_success = Q.prove (
`!m f r.
  (ex_bind m f = Success r)
  =
  (?r'. (m = Success r') ∧ (f r' = Success r))`,
rw [ex_bind_def] >>
cases_on `m` >>
rw [] >>
metis_tac []);
*)

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val failwith_def = Define `
(failwith : α -> (β, γ, α) M) msg = (\s. (Failure msg, s))`;

val read_def = Define `
(read : (α, α, β) M) =
  \s. (Success s, s)`;

val write_def = Define `
(write : α -> (α, unit, β) M) v =
  \s. (Success (), v)`;

val lookup_st_ex_def = Define `
(lookup_st_ex x [] = failwith ("failed lookup: " ++ x)) ∧
(lookup_st_ex x ((y,v)::e) =
  if x = y then
    return v
  else
    lookup_st_ex x e)`;

val _ = Hol_datatype `
infer_t = 
    Infer_Tvar_db of num
  | Infer_Tapp of infer_t list => tc0
  | Infer_Tfn of infer_t => infer_t
  | Infer_Tuvar of num`;

val infer_t_size_def = fetch "-" "infer_t_size_def";

val _ = Hol_datatype `
elab_st = <| next_uvar : num; 
             constraint_set : (infer_t # infer_t) list; 
             subst : (num |-> infer_t) |>`;

val fresh_uvar_def = Define `
(fresh_uvar : (elab_st, infer_t, α) M) =
  \s. (Success (Infer_Tuvar s.next_uvar), s with <| next_uvar := s.next_uvar + 1 |>)`;

val n_fresh_uvar_def = Define  `
n_fresh_uvar (n:num) =
  if n = 0 then
    return []
  else
    do v <- fresh_uvar;
       vs <- n_fresh_uvar (n - 1);
       return (v::vs)
    od`;

val add_constraint_def = Define `
add_constraint t1 t2 =
  \s. (Success (), s with <| constraint_set := (t1,t2)::s.constraint_set |>)`;

val add_constraints_def = Define `
(add_constraints [] [] =
  return ()) ∧
(add_constraints (t1::ts1) (t2::ts2) =
  do () <- add_constraint t1 t2;
     () <- add_constraints ts1 ts2;
     return ()
  od)`;

val solve_constraints_def = Define `
solve_constraints : (elab_st, unit, 'a) M = ARB`;

val get_subst_def = Define `
get_subst : (elab_st, num |-> infer_t, 'a) M =
  \s. (Success s.subst, s)`;

val infer_type_subst_def = tDefine "infer_type_subst" `
(infer_type_subst s (Tvar tv) =
  case lookup tv s of 
   | SOME t => t) ∧
(infer_type_subst s (Tvar_db n) =
  Infer_Tvar_db n) ∧
(infer_type_subst s (Tapp ts tn) =
  Infer_Tapp (MAP (infer_type_subst s) ts) tn) ∧
(infer_type_subst s (Tfn t1 t2) =
  Infer_Tfn (infer_type_subst s t1) (infer_type_subst s t2))`
(WF_REL_TAC `measure (t_size o SND)` >>
 rw [] >>
 TRY (induct_on `ts`) >>
 rw [t_size_def] >>
 res_tac >>
 decide_tac);

val infer_p_def = tDefine "infer_p" `
(infer_p cenv (Pvar n _) =
  do t <- fresh_uvar;
     return (Pvar n (SOME t), t, [(n,t)])
  od) ∧
(infer_p cenv (Plit (Bool b)) =
  return (Plit (Bool b), Infer_Tapp [] TC_bool, [])) ∧
(infer_p cenv (Plit (IntLit i)) =
  return (Plit (IntLit i), Infer_Tapp [] TC_int, [])) ∧
(infer_p cenv (Plit Unit) =
  return (Plit Unit, Infer_Tapp [] TC_unit, [])) ∧
(infer_p cenv (Pcon cn ps) =
  do (tvs',ts,tn) <- lookup_st_ex cn cenv;
     (ps',ts'',tenv) <- infer_ps cenv ps;
     ts' <- n_fresh_uvar (LENGTH tvs');
     () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
       return (Pcon cn ps', Infer_Tapp ts' tn, tenv)
  od) ∧
(infer_p cenv (Pref p) =
  do (p',t,tenv) <- infer_p cenv p;
    return (Pref p', Infer_Tapp [t] TC_ref, tenv)
  od) ∧
(infer_ps cenv [] =
  return ([], [], [])) ∧
(infer_ps cenv (p::ps) =
  do (p', t, tenv) <- infer_p cenv p; 
     (ps', ts, tenv') <- infer_ps cenv ps; 
     return (p'::ps', t::ts, tenv'++tenv)
  od)`
(WF_REL_TAC `measure (\x. case x of INL (_,p) => pat_size (\x.0:num) p 
                                  | INR (_,ps) => pat1_size (\x.0:num) ps)` >>
 rw []);

val infer_p_ind = fetch "-" "infer_p_ind"

(*
val infer_e_def = Define `
(infer_e cenv env (Raise err) =
  do t <- fresh_uvar;
     return (Raise err, t)
  od) ∧
(infer_e cenv env (Handle e1 x e2) =
  do (e1',t1) <- infer_e cenv env e1;
     (e2',t2) <- infer_e cenv (bind_tenv x 0 (Infer_Tapp [] TC_int) env) e2;
     () <- add_constraint t1 t2;
     return (Handle e1' x e2', t1)
  od) ∧
(infer_e cenv tenv (Lit (Bool b)) =
  return (Lit (Bool b), Infer_Tapp [] TC_bool)) ∧
(infer_e cenv tenv (Lit (IntLit i)) =
  return (Lit (IntLit i), Infer_Tapp [] TC_int)) ∧
(infer_e cenv tenv (Lit Unit) =
  return (Lit Unit, Infer_Tapp [] TC_unit)) ∧
(infer_e cenv env (Var n _) =
  do (tvs,t) <- lookup_tenv_st_ex n 0 env;
     uvs <- n_fresh_uvar tvs;
     return (Var n (SOME uvs), infer_type_subst (ZIP(tvs,uvs)) t)
  od) ∧
(infer_e cenv env (Con cn es) =
  do (tvs',ts,tn) <- lookup_st_ex cn cenv;
     (es',ts'') <- infer_es cenv env es;
     ts' <- n_fresh_uvar (LENGTH tvs');
     () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
       return (Con cn es', Infer_Tapp ts' tn)
  od) ∧
(infer_e cenv env (Fun x _ e) =
  do t1 <- fresh_uvar;
     (e', t2) <- infer_e cenv (bind_tenv x 0 t1 env);
     return (Fun x t1 e', Infer_Tfn t1 t2)
  od) ∧
(infer_e cenv env (Uapp uop e) =
  do (e',t) <- infer_e cenv env e;
     t' <- constrain_uop uop t'
     return (Uapp uop e', t')
  od) ∧
(infer_e cenv env (App op e1 e2) =
  do (e1',t1) <- infer_e cenv env e1;
     (e2',t2) <- infer_e cenv env e2;
     t3 <- constrain_op op t1 t2;
     return (App op e1' e2', t3)
  od) ∧
(infer_e cenv env (Log log e1 e2) =
  do (e1',t1) <- infer_e cenv env e1;
     (e2',t2) <- infer_e cenv env e2;
     () <- add_constraint t1 (Tapp [] TC_bool);
     () <- add_constraint t2 (Tapp [] TC_bool);
     return (Log log e1' e2', Tapp [] TC_bool) 
  od) ∧
(infer_e cenv env (If e1 e2 e3) =
  do (e1',t1) <- infer_e cenv env e1;
     (e2',t2) <- infer_e cenv env e2;
     (e3',t3) <- infer_e cenv env e3;
     () <- add_constraint t1 (Infer_Tapp [] TC_bool);
     () <- add_constraint t2 t3;
     return (If e1' e2' e3', t2)
  od) ∧
(infer_e cenv env (Mat e pes) =
  do (e1',t1) <- infer_e cenv env e;


(infer_e cenv env (Let _ x _ e1 e2) =

(infer_e cenv env (Letrec _ funs e) =

*)
val _ = export_theory ();
