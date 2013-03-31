open preamble MiniMLTheory MiniMLTerminationTheory;
open unifyTheory collapseTheory;
open stringTheory monadsyntax;

val _ = new_theory "infer";

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

val _ = Hol_datatype `
  exc = Success of 'a | Failure of 'b`;

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

val id_to_string_def = Define `
(id_to_string (Short x) = x) ∧
(id_to_string (Long x y) = x ++ "." ++ y)`;

val lookup_st_ex_def = Define `
(lookup_st_ex pr x [] = failwith ("failed lookup: " ++ pr x)) ∧
(lookup_st_ex pr x ((y,v)::e) =
  if x = y then
    return v
  else
    lookup_st_ex pr x e)`;

val _ = Hol_datatype `
elab_st = <| next_uvar : num; 
             subst : 'a |>`;

val fresh_uvar_def = Define `
(fresh_uvar : ('b elab_st, infer_t, α) M) =
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
  \st. 
    case t_unify st.subst t1 t2 of
      | NONE =>
          (Failure "Type mismatch", st)
      | SOME s =>
          (Success (), st with <| subst := s |>)`;

val add_constraints_def = Define `
(add_constraints [] [] =
  return ()) ∧
(add_constraints (t1::ts1) (t2::ts2) =
  do () <- add_constraint t1 t2;
     () <- add_constraints ts1 ts2;
     return ()
  od)`;

val get_next_uvar_def = Define `
get_next_uvar =
  \st. (Success st.next_uvar, st)`;

val get_subst_def = Define `
get_subst =
  \st. (Success st.subst, st)`;

val apply_subst_def = Define `
apply_subst t =
  \st.
    let sub = t_collapse st.subst in
      (Success (apply_subst_t sub t), st with <|subst := sub |>)`;

val apply_subst_list_def = Define `
apply_subst_list ts =
  \st.
    let sub = t_collapse st.subst in
      (Success (MAP (apply_subst_t sub) ts), st with <|subst := sub |>)`;

(* Generalise the unification variables greater than m, starting at deBruijn index n.
 * Return how many were generalised and the generalised type *)
val generalise_def = Define `
(generalise m n (Infer_Tapp ts tc) =
  let (num_gen, ts') = generalise_list m n ts in
    (num_gen, Infer_Tapp ts' tc)) ∧
(generalise m n (Infer_Tuvar uv) =
  if m ≤ uv then
    (1, Infer_Tvar_db n)
  else
    (0, Infer_Tuvar uv)) ∧
(generalise_list m n [] = 
  (0,[])) ∧
(generalise_list m n (t::ts) =
  let (num_gen, t') = generalise m n t in
  let (num_gen', ts') = generalise_list m (num_gen + n) ts in
    (num_gen+num_gen', t'::ts'))`;

val infer_type_subst_def = tDefine "infer_type_subst" `
(infer_type_subst s (Tvar tv) =
  case lookup tv s of 
   | SOME t => t) ∧
(infer_type_subst s (Tvar_db n) =
  Infer_Tvar_db n) ∧
(infer_type_subst s (Tapp ts tn) =
  Infer_Tapp (MAP (infer_type_subst s) ts) tn)`
(WF_REL_TAC `measure (t_size o SND)` >>
 rw [] >>
 TRY (induct_on `ts`) >>
 rw [t_size_def] >>
 res_tac >>
 decide_tac);

val infer_deBruijn_subst_def = tDefine "infer_deBruijn_subst" `
(infer_deBruijn_subst s (Infer_Tvar_db n) =
  EL n s) ∧
(infer_deBruijn_subst s (Infer_Tapp ts tn) =
  Infer_Tapp (MAP (infer_deBruijn_subst s) ts) tn) ∧
(infer_deBruijn_subst s (Infer_Tuvar n) =
  Infer_Tuvar n)`
(WF_REL_TAC `measure (infer_t_size o SND)` >>
 rw [] >>
 TRY (induct_on `ts`) >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val infer_p_def = tDefine "infer_p" `
(infer_p cenv (Pvar n) =
  do t <- fresh_uvar;
     return (t, [(n,t)])
  od) ∧
(infer_p cenv (Plit (Bool b)) =
  return (Infer_Tapp [] TC_bool, [])) ∧
(infer_p cenv (Plit (IntLit i)) =
  return (Infer_Tapp [] TC_int, [])) ∧
(infer_p cenv (Plit Unit) =
  return (Infer_Tapp [] TC_unit, [])) ∧
(infer_p cenv (Pcon cn ps) =
  do (tvs',ts,tn) <- lookup_st_ex id_to_string cn cenv;
     (ts'',tenv) <- infer_ps cenv ps;
     ts' <- n_fresh_uvar (LENGTH tvs');
     () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
       return (Infer_Tapp ts' tn, tenv)
  od) ∧
(infer_p cenv (Pref p) =
  do (t,tenv) <- infer_p cenv p;
    return (Infer_Tapp [t] TC_ref, tenv)
  od) ∧
(infer_ps cenv [] =
  return ([], [])) ∧
(infer_ps cenv (p::ps) =
  do (t, tenv) <- infer_p cenv p; 
     (ts, tenv') <- infer_ps cenv ps; 
     return (t::ts, tenv'++tenv)
  od)`
(WF_REL_TAC `measure (\x. case x of INL (_,p) => pat_size p 
                                  | INR (_,ps) => pat1_size ps)` >>
 rw []);

val infer_p_ind = fetch "-" "infer_p_ind"

val constrain_uop_def = Define `
constrain_uop uop t =
  case uop of
   | Opref => return (Infer_Tapp [t] TC_ref)
   | Opderef =>
       do uvar <- fresh_uvar;
          () <- add_constraint t (Infer_Tapp [uvar] TC_ref);
          return uvar
       od`;

val constrain_op_def = Define `
constrain_op op t1 t2 =
  case op of
   | Opn opn =>
       do () <- add_constraint t1 (Infer_Tapp [] TC_int);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_int)
       od
   | Opb opb => 
       do () <- add_constraint t1 (Infer_Tapp [] TC_int);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_bool)
       od
   | Equality =>
       do () <- add_constraint t1 t2;
          return (Infer_Tapp [] TC_bool)
       od
   | Opapp =>
       do uvar <- fresh_uvar;
          () <- add_constraint t1 (Infer_Tapp [t2;uvar] TC_fn);
          return uvar
       od
   | Opassign =>
       do () <- add_constraint t1 (Infer_Tapp [t2] TC_ref);
          return (Infer_Tapp [] TC_unit)
       od`;

val infer_e_def = tDefine "infer_e" `
(infer_e cenv env (Raise err) =
  do t <- fresh_uvar;
     return t
  od) ∧
(infer_e cenv env (Handle e1 x e2) =
  do t1 <- infer_e cenv env e1;
     t2 <- infer_e cenv (bind x (0,Infer_Tapp [] TC_int) env) e2;
     () <- add_constraint t1 t2;
     return t1
  od) ∧
(infer_e cenv tenv (Lit (Bool b)) =
  return (Infer_Tapp [] TC_bool)) ∧
(infer_e cenv tenv (Lit (IntLit i)) =
  return (Infer_Tapp [] TC_int)) ∧
(infer_e cenv tenv (Lit Unit) =
  return (Infer_Tapp [] TC_unit)) ∧
(infer_e cenv env (Var (Short n)) =
  do (tvs,t) <- lookup_st_ex (\x.x) n env;
     uvs <- n_fresh_uvar tvs;
     return (infer_deBruijn_subst uvs t)
  od) ∧
(infer_e cenv env (Con cn es) =
  do (tvs',ts,tn) <- lookup_st_ex id_to_string cn cenv;
     ts'' <- infer_es cenv env es;
     ts' <- n_fresh_uvar (LENGTH tvs');
     () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
       return (Infer_Tapp ts' tn)
  od) ∧
(infer_e cenv env (Fun x e) =
  do t1 <- fresh_uvar;
     t2 <- infer_e cenv (bind x (0,t1) env) e;
     return (Infer_Tapp [t1;t2] TC_fn)
  od) ∧
(infer_e cenv env (Uapp uop e) =
  do t <- infer_e cenv env e;
     t' <- constrain_uop uop t;
     return t'
  od) ∧
(infer_e cenv env (App op e1 e2) =
  do t1 <- infer_e cenv env e1;
     t2 <- infer_e cenv env e2;
     t3 <- constrain_op op t1 t2;
     return t3
  od) ∧
(infer_e cenv env (Log log e1 e2) =
  do t1 <- infer_e cenv env e1;
     t2 <- infer_e cenv env e2;
     () <- add_constraint t1 (Infer_Tapp [] TC_bool);
     () <- add_constraint t2 (Infer_Tapp [] TC_bool);
     return (Infer_Tapp [] TC_bool) 
  od) ∧
(infer_e cenv env (If e1 e2 e3) =
  do t1 <- infer_e cenv env e1;
     () <- add_constraint t1 (Infer_Tapp [] TC_bool);
     t2 <- infer_e cenv env e2;
     t3 <- infer_e cenv env e3;
     () <- add_constraint t2 t3;
     return t2
  od) ∧
(infer_e cenv env (Mat e pes) =
  if pes = [] then
    failwith "Empty pattern match"
  else
    do t1 <- infer_e cenv env e;
       t2 <- fresh_uvar;
       ()<- infer_pes cenv env pes t1 t2;
       return t2
  od) ∧
(infer_e cenv env (Let x e1 e2) =
  if is_value e1 then
    do n <- get_next_uvar;
       t1 <- infer_e cenv env e1;
       t1' <- apply_subst t1;
       (num_gen,t1'') <- return (generalise n 0 t1');
       t2 <- infer_e cenv (bind x (num_gen,t1'') env) e2;
       return t2
    od
  else
    do t1 <- infer_e cenv env e1;
       t2 <- infer_e cenv (bind x (0,t1) env) e2;
       return t2
    od) ∧
(infer_e cenv env (Letrec funs e) =
  do next <- get_next_uvar;
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (merge (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars) env);
     () <- infer_funs cenv env' funs;
     ts <- apply_subst_list uvars;
     (num_gen,ts') <- return (generalise_list next 0 ts);
     env'' <- return (merge (list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts') env);
     t <- infer_e cenv env'' e;
     return t
  od) ∧
(infer_es cenv env [] =
  return []) ∧
(infer_es cenv env (e::es) =
  do t <- infer_e cenv env e;
     ts <- infer_es cenv env es;
     return (t::ts)
  od) ∧
(infer_pes cenv env [] t1 t2 =
   return ()) ∧
(infer_pes cenv env ((p,e)::pes) t1 t2 =
  do (t1', env') <- infer_p cenv p;
     () <- add_constraint t1 t1';
     t2' <- infer_e cenv (merge (MAP (\(n,t). (n,(0,t))) env') env) e;
     () <- add_constraint t2 t2';
     () <- infer_pes cenv env pes t1 t2;
     return ()
  od) ∧
(infer_funs cenv env [] = return ()) ∧
(infer_funs cenv env ((f, x, e)::funs) =
  do uvar <- fresh_uvar;
     t <- infer_e cenv (bind x (0,uvar) env) e;
     () <- infer_funs cenv env funs;
     return ()
  od)`
(WF_REL_TAC `measure (\x. case x of | INL (_,_,e) => exp_size e
                                    | INR (INL (_,_,es)) => exp6_size es
                                    | INR (INR (INL (_,_,pes,_,_))) => exp4_size pes
                                    | INR (INR (INR (_,_,funs))) => exp1_size funs)` >>
 rw []);

val top_infer_e_def = Define `
top_infer_e cenv env e =
  let init_st = <| next_uvar := 0; subst := FEMPTY |> in
    case (infer_e cenv env e) init_st of
      | (Failure x, st) => Failure x
      | (Success t, st) =>
          let sub = t_collapse st.subst in
            Success (apply_subst_t sub t)`;

val _ = export_theory ();
