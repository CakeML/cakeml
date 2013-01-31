open preamble MiniMLTheory MiniMLTerminationTheory;
open check_annotatedTheory unifyTheory collapseTheory;
open stringTheory monadsyntax;

val _ = new_theory "infer";

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

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
(generalise m n (Infer_Tfn t1 t2) =
  let (num_gen, t1') = generalise m n t1 in
  let (num_gen', t2') = generalise m (n+num_gen) t2 in
    (num_gen + num_gen', Infer_Tfn t1' t2')) ∧
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
  Infer_Tapp (MAP (infer_type_subst s) ts) tn) ∧
(infer_type_subst s (Tfn t1 t2) =
  Infer_Tfn (infer_type_subst s t1) (infer_type_subst s t2))`
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
(infer_deBruijn_subst s (Infer_Tfn t1 t2) =
  Infer_Tfn (infer_deBruijn_subst s t1) (infer_deBruijn_subst s t2)) ∧
(infer_deBruijn_subst s (Infer_Tuvar n) =
  Infer_Tuvar n)`
(WF_REL_TAC `measure (infer_t_size o SND)` >>
 rw [] >>
 TRY (induct_on `ts`) >>
 rw [infer_t_size_def] >>
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
          () <- add_constraint t1 (Infer_Tfn t2 uvar);
          return uvar
       od
   | Opassign =>
       do () <- add_constraint t1 (Infer_Tapp [t2] TC_ref);
          return (Infer_Tapp [] TC_unit)
       od`;

val infer_e_def = tDefine "infer_e" `
(infer_e cenv env (Raise err) =
  do t <- fresh_uvar;
     return (Raise err, t)
  od) ∧
(infer_e cenv env (Handle e1 x e2) =
  do (e1',t1) <- infer_e cenv env e1;
     (e2',t2) <- infer_e cenv (bind x (0,Infer_Tapp [] TC_int) env) e2;
     () <- add_constraint t1 t2;
     return (Handle e1' x e2', t1)
  od) ∧
(infer_e cenv tenv (Lit (Bool b)) =
  return (Lit (Bool b), Infer_Tapp [] TC_bool)) ∧
(infer_e cenv tenv (Lit (IntLit i)) =
  return (Lit (IntLit i), Infer_Tapp [] TC_int)) ∧
(infer_e cenv tenv (Lit Unit) =
  return (Lit Unit, Infer_Tapp [] TC_unit)) ∧
(infer_e cenv env (Var n topts) =
  do (tvs,t) <- lookup_st_ex n env;
     uvs <- n_fresh_uvar tvs;
     return (Var n (SOME uvs), infer_deBruijn_subst uvs t)
  od) ∧
(infer_e cenv env (Con cn es) =
  do (tvs',ts,tn) <- lookup_st_ex cn cenv;
     (es',ts'') <- infer_es cenv env es;
     ts' <- n_fresh_uvar (LENGTH tvs');
     () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
       return (Con cn es', Infer_Tapp ts' tn)
  od) ∧
(infer_e cenv env (Fun x topt e) =
  do t1 <- fresh_uvar;
     (e', t2) <- infer_e cenv (bind x (0,t1) env) e;
     return (Fun x (SOME t1) e', Infer_Tfn t1 t2)
  od) ∧
(infer_e cenv env (Uapp uop e) =
  do (e',t) <- infer_e cenv env e;
     t' <- constrain_uop uop t;
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
     () <- add_constraint t1 (Infer_Tapp [] TC_bool);
     () <- add_constraint t2 (Infer_Tapp [] TC_bool);
     return (Log log e1' e2', Infer_Tapp [] TC_bool) 
  od) ∧
(infer_e cenv env (If e1 e2 e3) =
  do (e1',t1) <- infer_e cenv env e1;
     () <- add_constraint t1 (Infer_Tapp [] TC_bool);
     (e2',t2) <- infer_e cenv env e2;
     (e3',t3) <- infer_e cenv env e3;
     () <- add_constraint t2 t3;
     return (If e1' e2' e3', t2)
  od) ∧
(infer_e cenv env (Mat e pes) =
  if pes = [] then
    failwith "Empty pattern match"
  else
    do (e',t1) <- infer_e cenv env e;
       t2 <- fresh_uvar;
       pes' <- infer_pes cenv env pes t1 t2;
       return (Mat e' pes', t2)
  od) ∧
(infer_e cenv env (Let nopt x topt e1 e2) =
  if is_value e1 then
    do n <- get_next_uvar;
       (e1',t1) <- infer_e cenv env e1;
       t1' <- apply_subst t1;
       (num_gen,t1'') <- return (generalise n 0 t1');
       (e2',t2) <- infer_e cenv (bind x (num_gen,t1'') env) e2;
       return (Let (SOME num_gen) x (SOME t1) e1' e2', t2)
    od
  else
    do (e1',t1) <- infer_e cenv env e1;
       (e2',t2) <- infer_e cenv (bind x (0,t1) env) e2;
       return (Let (SOME 0) x (SOME t1) e1' e2', t2)
    od) ∧
(infer_e cenv env (Letrec nopt funs e) =
  do next <- get_next_uvar;
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (merge (list$MAP2 (\(f,topt1,x,topt2,e) uvar. (f,(0,uvar))) funs uvars) env);
     funs' <- infer_funs cenv env' funs;
     () <- add_constraints uvars (MAP (\(f,topt1,x,topt2,e). THE topt1) funs');
     ts <- apply_subst_list uvars;
     (num_gen,ts') <- return (generalise_list next 0 ts);
     env'' <- return (merge (list$MAP2 (\(f,topt1,x,topt2,e) t. (f,(num_gen,t))) funs ts') env);
     (e',t) <- infer_e cenv env'' e;
     return (Letrec (SOME num_gen) funs' e', t)
  od) ∧
(infer_es cenv env [] =
  return ([],[])) ∧
(infer_es cenv env (e::es) =
  do (e',t) <- infer_e cenv env e;
     (es',ts) <- infer_es cenv env es;
     return (e'::es',t::ts)
  od) ∧
(infer_pes cenv env [] t1 t2 =
   return []) ∧
(infer_pes cenv env ((p,e)::pes) t1 t2 =
  do (p', t1', env') <- infer_p cenv p;
     () <- add_constraint t1 t1';
     (e', t2') <- infer_e cenv (merge (MAP (\(n,t). (n,(0,t))) env') env) e;
     () <- add_constraint t2 t2';
     pes' <- infer_pes cenv env pes t1 t2;
     return ((p',e')::pes')
  od) ∧
(infer_funs cenv env [] = return []) ∧
(infer_funs cenv env ((f, topt1, x, topt2, e)::funs) =
  do uvar <- fresh_uvar;
     (e',t) <- infer_e cenv (bind x (0,uvar) env) e;
     funs' <- infer_funs cenv env funs;
     return ((f, SOME (Infer_Tfn uvar t), x, SOME uvar, e') :: funs')
  od)`
(WF_REL_TAC `measure (\x. case x of | INL (_,_,e) => exp_size (\x.0) e
                                    | INR (INL (_,_,es)) => exp8_size (\x.0) es
                                    | INR (INR (INL (_,_,pes,_,_))) => exp5_size (\x.0) pes
                                    | INR (INR (INR (_,_,funs))) => exp1_size (\x.0) funs)` >>
 rw []);

val apply_subst_p_def = tDefine "apply_subst_p" `
(apply_subst_p s (Pvar n topt) =
  Pvar n (option_map (apply_subst_t s) topt)) ∧
(apply_subst_p s (Plit (Bool b)) =
  Plit (Bool b)) ∧
(apply_subst_p s (Plit (IntLit i)) =
  Plit (IntLit i)) ∧
(apply_subst_p s (Plit Unit) =
  Plit Unit) ∧
(apply_subst_p s (Pcon cn ps) =
  Pcon cn (apply_subst_ps s ps)) ∧
(apply_subst_p s (Pref p) =
  Pref (apply_subst_p s p)) ∧
(apply_subst_ps s [] =
  []) ∧
(apply_subst_ps s (p::ps) =
  apply_subst_p s p :: apply_subst_ps s ps)`
(WF_REL_TAC `measure (\x. case x of INL (_,p) => pat_size (\x.0:num) p 
                                  | INR (_,ps) => pat1_size (\x.0:num) ps)` >>
 rw []);

val apply_subst_e_def = tDefine "apply_subst_e" `
(apply_subst_e s (Raise err) =
  Raise err) ∧
(apply_subst_e s (Handle e1 x e2) =
  Handle (apply_subst_e s e1) x (apply_subst_e s e2)) ∧
(apply_subst_e s (Lit (Bool b)) =
  Lit (Bool b)) ∧
(apply_subst_e s (Lit (IntLit i)) =
  Lit (IntLit i)) ∧
(apply_subst_e s (Lit Unit) =
  Lit Unit) ∧
(apply_subst_e s (Var n topts) =
  Var n (option_map (MAP (apply_subst_t s)) topts)) ∧
(apply_subst_e s (Con cn es) =
  Con cn (apply_subst_es s es)) ∧
(apply_subst_e s (Fun x topt e) =
  Fun x (option_map (apply_subst_t s) topt) (apply_subst_e s e)) ∧
(apply_subst_e s (Uapp uop e) =
  Uapp uop (apply_subst_e s e)) ∧
(apply_subst_e s (App op e1 e2) =
  App op (apply_subst_e s e1) (apply_subst_e s e2)) ∧
(apply_subst_e s (Log log e1 e2) =
  Log log (apply_subst_e s e1) (apply_subst_e s e2)) ∧
(apply_subst_e s (If e1 e2 e3) =
  If (apply_subst_e s e1) (apply_subst_e s e2) (apply_subst_e s e3)) ∧
(apply_subst_e s (Mat e pes) =
  Mat (apply_subst_e s e) (apply_subst_pes s pes)) ∧
(apply_subst_e s (Let nopt x topt e1 e2) =
  Let nopt x (option_map (apply_subst_t s) topt) (apply_subst_e s e1) (apply_subst_e s e2)) ∧
(apply_subst_e s (Letrec nopt funs e) =
  Letrec nopt (apply_subst_funs s funs) (apply_subst_e s e)) ∧
(apply_subst_es s [] =
  [] ) ∧
(apply_subst_es s (e::es) =
  apply_subst_e s e :: apply_subst_es s es) ∧
(apply_subst_pes s [] =
  []) ∧
(apply_subst_pes s ((p,e)::pes) =
  (apply_subst_p s p, apply_subst_e s e) :: apply_subst_pes s pes) ∧
(apply_subst_funs s [] = 
  []) ∧
(apply_subst_funs s ((f, topt1, x, topt2, e)::funs) =
  (f, 
   option_map (apply_subst_t s) topt1,
   x,
   option_map (apply_subst_t s) topt2,
   apply_subst_e s e) ::
  apply_subst_funs s funs)`
(WF_REL_TAC `measure (\x. case x of | INL (_,e) => exp_size (\x.0) e
                                    | INR (INL (_,es)) => exp8_size (\x.0) es
                                    | INR (INR (INL (_,pes))) => exp5_size (\x.0) pes
                                    | INR (INR (INR (_,funs))) => exp1_size (\x.0) funs)` >>
 rw []);

val infer_and_annotate_e_def = Define `
infer_and_annotate_e cenv env e =
  let init_st = <| next_uvar := 0; subst := FEMPTY |> in
    case (infer_e cenv env e) init_st of
      | (Failure x, st) => Failure x
      | (Success (e',t), st) =>
          let sub = t_collapse st.subst in
            Success (apply_subst_e sub e', apply_subst_t sub t)`;

val _ = export_theory ();
