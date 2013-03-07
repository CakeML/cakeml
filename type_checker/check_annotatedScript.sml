open preamble MiniMLTheory MiniMLTerminationTheory;
open stringTheory monadsyntax;

val _ = new_theory "check_annotated";

val _ = Hol_datatype `
  exc = Success of 'a | Failure of 'b`;

val _ = type_abbrev("M", ``:('a, string) exc``);

val ex_bind_def = Define `
  ((ex_bind (x:'a M) (f:'a -> 'b M)) : 'b M) =
    case x of
      Success y => f y
    | Failure e => Failure e`

val ex_return_def = Define `
  ((ex_return (x:'a)) : 'a M) = 
    Success x`;

val monad_bind_success = Q.prove (
`!m f r.
  (ex_bind m f = Success r)
  =
  (?r'. (m = Success r') ∧ (f r' = Success r))`,
rw [ex_bind_def] >>
cases_on `m` >>
rw [] >>
metis_tac []);


(* setup fancy syntax *)

val _ = temp_overload_on ("monad_bind", ``ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``ex_return``);

(* failwith and otherwise *)

val failwith_def = Define `
  ((failwith msg) :'a M) = Failure msg`;

(* others *)


val iter_ex_def = Define `
(iter_ex f [] = 
  return ()) ∧
(iter_ex f (x::y) =
  do () <- f x;
     iter_ex f y
  od)`;

val iter_ex_cong = Q.store_thm ("iter_ex_cong",
`!l1 l2 f g.
  (l1 = l2) ∧ (!x. MEM x l2 ⇒ (f x = g x)) ⇒
  (iter_ex f l1 = iter_ex g l2)`,
induct_on `l1` >>
rw [iter_ex_def, ex_return_def] >>
rw [iter_ex_def, ex_return_def, ex_bind_def] >>
fs [] >>
metis_tac []);

val _ = DefnBase.add_cong iter_ex_cong;

val map_ex_def = tDefine "map_ex" `
(map_ex f [] = 
  return []) ∧
(map_ex f (x::y) =
  do x' <- f x;
     y' <- map_ex f y;
     return (x'::y')
  od)`
(WF_REL_TAC `measure (LENGTH o SND)` >>
 srw_tac [ARITH_ss] []);

val map_ex_cong = Q.store_thm ("map_ex_cong",
`!l1 l2 f g.
  (l1 = l2) ∧ (!x. MEM x l2 ⇒ (f x = g x)) ⇒
  (map_ex f l1 = map_ex g l2)`,
induct_on `l1` >>
rw [map_ex_def, ex_return_def] >>
rw [map_ex_def, ex_return_def, ex_bind_def] >>
fs [] >>
metis_tac []);

val _ = DefnBase.add_cong map_ex_cong;

val id_to_string_def = Define `
(id_to_string (Short x) = x) ∧
(id_to_string (Long x y) = x ++ "." ++ y)`;

val lookup_ex_def = Define `
(lookup_ex x [] = failwith ("failed lookup: " ++ id_to_string x)) ∧
(lookup_ex x ((y,v)::e) =
  if x = y then
    return v
  else
    lookup_ex x e)`;

val lookup_tenv_ex_def = Define `
(lookup_tenv_ex n inc Empty =
   failwith ("failed lookup: " ++ n)) ∧
(lookup_tenv_ex n inc (Bind_tvar tvs e) =
  lookup_tenv_ex n (inc+tvs) e) ∧
(lookup_tenv_ex n inc (Bind_name n' tvs t e) =
  if n' = n then
    return (tvs, deBruijn_inc tvs inc t)
  else
    lookup_tenv_ex n inc e)`;

val check_freevars_ex_def = tDefine "check_freevars_ex" `
(check_freevars_ex dbmax tvs (Tvar tv) = 
  if MEM tv tvs then
    return ()
  else
    failwith ("Free type variable: " ++ tv)) ∧
(check_freevars_ex dbmax tvs (Tapp ts tn) =
  iter_ex (check_freevars_ex dbmax tvs) ts) ∧
(check_freevars_ex dbmax tvs (Tvar_db n) = 
  if n < dbmax then
    return ()
  else
    failwith "Free type variable")`
(WF_REL_TAC `measure (t_size o SND o SND)` >>
 rw [] >>
 induct_on `ts` >>
 fs [] >>
 rw [t_size_def] >>
 res_tac >>
 decide_tac);

val check_p_def = tDefine "check_p" `
(check_p tvs cenv (Pvar n topt) =
  case topt of
     | NONE => failwith ("Missing type annotation for pattern variable: " ++ n)
     | SOME t =>
         do () <- check_freevars_ex tvs [] t;
            return (t, [(n,t)])
         od) ∧
(check_p tvs cenv (Plit (Bool _)) =
  return (Tbool, [])) ∧
(check_p tvs cenv (Plit (IntLit _)) =
  return (Tint, [])) ∧
(check_p tvs cenv (Plit Unit) =
  return (Tunit, [])) ∧
(check_p tvs cenv (Pcon cn ps) =
  (* TODO: ts' should be in an annotation *)
  let ts' = ARB in
  do (tvs',ts,tn) <- lookup_ex cn cenv;
     (ts'', tenv) <- check_ps tvs cenv ps;
     () <- iter_ex (check_freevars_ex tvs []) ts';
     if ¬(LENGTH ts' = LENGTH tvs') then
       failwith "Type constructor applied to the wrong number of arguments"
     else if ¬(ts'' = MAP (type_subst (ZIP(tvs',ts'))) ts) then
       failwith "Type mismatch"
     else
       return (Tapp ts' (TC_name tn), tenv)
     od) ∧
(check_p tvs cenv (Pref p) =
  do (t,tenv) <- check_p tvs cenv p;
    return (Tref t, tenv)
  od) ∧
(check_ps tvs cenv [] =
  return ([], [])) ∧
(check_ps tvs cenv (p::ps) =
  do (t, tenv) <- check_p tvs cenv p; 
     (ts, tenv') <- check_ps tvs cenv ps; 
     return (t::ts, tenv'++tenv)
  od)`
(WF_REL_TAC `measure (\x. case x of INL (_,_,p) => pat_size (\x.0) p 
                                  | INR (_,_,ps) => pat1_size (\x.0) ps)` >>
 rw []);

val check_p_ind = fetch "-" "check_p_ind"

val check_uop_def = Define `
(check_uop Opref t1 =
  return (Tref t1)) ∧
(check_uop Opderef t1 =
  case t1 of
     | Tapp [t1'] TC_ref => return t1'
     | _ => failwith "Dereferencing a non-reference type")`;

val check_op_def = Define `
(check_op Opapp t1 t2 =
  case t1 of
     | Tapp [t2';t3'] TC_fn => 
         if t2 = t2' then
           return t3'
         else
           failwith "Type mismatch"
     | _ => failwith "Applying a non-function type") ∧
(check_op (Opn _) t1 t2 =
  if (t1 = Tint) ∧ (t2 = Tint) then
    return Tint
  else
    failwith "Applying a numeric operator to a non-integer type") ∧
(check_op (Opb _) t1 t2 =
  if (t1 = Tint) ∧ (t2 = Tint) then
    return Tbool
  else
    failwith "Applying a numeric operator to a non-integer type") ∧
(check_op Equality t1 t2 =
  if t1 = t2 then
    return Tbool
  else
    failwith "Type mismatch") ∧
(check_op Opassign t1 t2 =
  case t1 of
     | Tapp [t1'] TC_ref =>
         if (t1' = t2) then
           return Tunit
         else
           failwith "Type mismatch"
     | _ => failwith "Assigning to a non-reference")`;

val check_e_def = tDefine "check_e" `
(check_e cenv tenv (Lit (Bool _)) =
  return Tbool) ∧
(check_e cenv tenv (Lit (IntLit _)) =
  return Tint) ∧
(check_e cenv tenv (Lit Unit) =
  return Tunit) ∧
(check_e cenv tenv (Raise _) =
  (* TODO: t should be in an annotation *)
  let t = ARB in
  do () <-check_freevars_ex (num_tvs tenv) [] t;
     return t
  od) ∧
(check_e cenv tenv (Handle e1 var e2) =
  do t <- check_e cenv tenv e1;
     t' <- check_e cenv (bind_tenv var 0 Tint tenv) e2;
     if ¬(t = t') then
       failwith "Type mismatch"
     else
       return t
  od) ∧
(check_e cenv tenv (Con cn es) =
  (* TODO: ts' should be in an annotation *)
  let ts' = ARB in
  do (tvs,ts,tn) <- lookup_ex cn cenv;
     ts'' <- check_es cenv tenv es;
     () <- iter_ex (check_freevars_ex (num_tvs tenv) []) ts';
     if ¬(LENGTH ts' = LENGTH tvs) then
       failwith "Type constructor applied to the wrong number of arguments"
     else if ¬(ts'' = MAP (type_subst (ZIP(tvs,ts'))) ts) then
       failwith "Type mismatch"
     else
       return (Tapp ts' (TC_name tn))
  od) ∧
(check_e cenv tenv (Var n targs_opt) =
  case targs_opt of
     | NONE => failwith ("Missing type annotation on variable: " ++ n)
     | SOME targs =>
         do (tvs,t) <- lookup_tenv_ex n 0 tenv;
            () <- iter_ex (check_freevars_ex (num_tvs tenv) []) targs;
            if ~(tvs = LENGTH targs) then
              failwith "Type constructor applied to the wrong number of arguments"
            else
              return (deBruijn_subst 0 targs t)
         od) ∧
(check_e cenv tenv (Fun n topt e) =
  case topt of
     | NONE => failwith ("Missing type annotation on function parameter: " ++ n)
     | SOME t1 =>
         do () <- check_freevars_ex (num_tvs tenv) [] t1;
            t2 <- check_e cenv (bind_tenv n 0 t1 tenv) e;
            return (Tfn t1 t2)
         od) /\
(check_e cenv tenv (Uapp uop e) =
  do t1 <- check_e cenv tenv e;
     check_uop uop t1
  od) ∧
(check_e cenv tenv (App op e1 e2) =
  do t1 <- check_e cenv tenv e1;
     t2 <- check_e cenv tenv e2;
     check_op op t1 t2
  od) ∧
(check_e cenv tenv (Log lop e1 e2) =
  do t1 <- check_e cenv tenv e1;
     t2 <- check_e cenv tenv e2;
     if t1 ≠ Tbool ∨ t2 ≠ Tbool then
       failwith "Logical operator given non-bool arguments"
     else
       return Tbool
  od) ∧
(check_e cenv tenv (If e1 e2 e3) =
  do t1 <- check_e cenv tenv e1;
     t2 <- check_e cenv tenv e2;
     t3 <- check_e cenv tenv e3;
     if t1 ≠ Tbool then
       failwith "If operator given non-bool condition"
     else if t2 ≠ t3 then
       failwith "Type mismatch"
     else
       return t2
  od) ∧
(check_e cenv tenv (Mat e pes) =
  case pes of
     | [] => failwith "Empty patterns in case"
     | (p',e')::pes' =>
         do t1 <- check_e cenv tenv e;
            (t1',tenv') <- check_p (num_tvs tenv) cenv p';
            t2 <- check_e cenv (bind_var_list 0 tenv' tenv) e';
            if ~ALL_DISTINCT (pat_bindings p' []) then
              failwith "Duplicate pattern bindings"
            else if t1 ≠ t1' then
              failwith "Type mismatch"
            else
              check_pes cenv tenv pes' t1 t2
         od) ∧
(check_e cenv tenv (Let tvsopt n topt e1 e2) =
  case topt of
     | NONE => failwith ("Missing type annotation on let-bound variable: " ++ n)
     | SOME t1 =>
         case tvsopt of
            | NONE => failwith "Missing type annotation on let"
            | SOME tvs =>
                if tvs = 0 then
                  do t1' <- check_e cenv tenv e1;
                     if t1 ≠ t1' then
                       failwith "Type mismatch"       
                     else 
                       check_e cenv (bind_tenv n 0 t1 tenv) e2
                  od
                else
                  do t1' <- check_e cenv (bind_tvar tvs tenv) e1;
                     t2 <- check_e cenv (bind_tenv n tvs t1' tenv) e2;
                     if ¬is_value e1 then
                       failwith "Value restriction violated"
                     else if t1 ≠ t1' then
                       failwith "Type mismatch"
                     else
                       return t2
                  od) ∧
(check_e cenv tenv (Letrec tvsopt funs e) =
  case tvsopt of
     | NONE =>
         failwith "Missing type annotation on let rec"
     | SOME tvs =>
         do tenv_init <- map_ex (λ(n, t, a, b, c). 
                                    case t of NONE => failwith "Missing annotation" 
                                            | SOME t => return (n,t)) 
                                funs;
            tenv' <- check_funs cenv (bind_var_list 0 tenv_init (bind_tvar tvs tenv)) funs;
            if tenv' = tenv_init then
              check_e cenv (bind_var_list tvs tenv' tenv) e
            else
              failwith "Letrec error"
         od) ∧
(check_es cenv tenv [] = 
  return []) ∧
(check_es cenv tenv (e::es) =
  do t <- check_e cenv tenv e; 
     ts <- check_es cenv tenv es; 
     return (t::ts)
  od) ∧
(check_funs cenv tenv [] =
  return []) ∧
(check_funs cenv tenv ((fn, topt1, n, topt2, e)::funs) =
  case topt1 of
     | SOME (Tapp [t1;t2] TC_fn) => 
         (case topt2 of
            | NONE => failwith "Missing type annotation"
            | SOME t1' =>
                do () <- check_freevars_ex (num_tvs tenv) [] (Tfn t1 t2);
                         t2' <- check_e cenv (bind_tenv n 0 t1' tenv) e;
                         tenv' <- check_funs cenv tenv funs;
                         if t2 ≠ t2' ∨ t1 ≠ t1' then
                           failwith "Type mismatch"
                         else if lookup fn tenv' ≠ NONE then
                           failwith ("Duplicate function name in let rec: " ++ fn)
                         else
                           return ((fn, Tfn t1 t2)::tenv')
                      od)
     | SOME _ => failwith "Bad type annotation"
     | NONE => failwith "Missing type annotation") ∧
(check_pes cenv tenv [] t1 t2 =
  return t2) ∧
(check_pes cenv tenv ((p,e)::pes) t1 t2 =
  do (t1',tenv') <- check_p (num_tvs tenv) cenv p;
     t2' <- check_e cenv (bind_var_list 0 tenv' tenv) e;
     if ~ALL_DISTINCT (pat_bindings p []) then
       failwith "Duplicate pattern bindings"
     else if t1 ≠ t1' ∨ t2 ≠ t2' then
       failwith "Type mismatch"
     else
       check_pes cenv tenv pes t1 t2
  od)`
(WF_REL_TAC `measure (\x. case x of 
                             | INL (_,_,e) => exp_size (\x.0) e
                             | INR (INL (_,_,es)) => exp8_size (\x.0) es
                             | INR (INR (INL (_,_,funs))) => exp1_size (\x.0) funs
                             | INR (INR (INR (_,_,pes,_,_))) => exp5_size (\x.0) pes)` >>
 srw_tac [ARITH_ss] []);

val check_e_ind = fetch "-" "check_e_ind";

val lookup_tenv_ex_correct = Q.prove (
`!n inc tenv l t. 
  (lookup_tenv_ex n inc tenv = Success (l,t))
  =
  (lookup_tenv n inc tenv = SOME (l,t))`,
induct_on `tenv` >>
rw [lookup_tenv_ex_def, lookup_tenv_def, failwith_def, ex_return_def]);

val iter_ex_correct = Q.prove (
`!f l u.
  (iter_ex f l = Success u)
  =
  EVERY (\x. f x = Success ()) l`,
induct_on `l` >>
rw [iter_ex_def, ex_return_def] >>
TRY (cases_on `u`) >>
rw [ex_bind_def] >>
cases_on `f h` >>
rw [] >>
cases_on `a` >>
rw []);

val check_freevars_ex_correct = Q.prove (
`!dbmax tvs t u.
  (check_freevars_ex dbmax tvs t = Success u)
  =
  (check_freevars dbmax tvs t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def, check_freevars_ex_def, failwith_def, ex_return_def] >>
TRY (cases_on `u`) >>
rw [iter_ex_correct, ex_bind_def] >>
eq_tac >>
rw [EVERY_MEM]);

val check_p_sound = Q.store_thm ("check_p_sound",
`(!tvs cenv p t tenv.
   (check_p tvs cenv p = Success (t,tenv)) ⇒ type_p tvs cenv p t tenv) ∧
 (!tvs cenv ps ts tenv.
   (check_ps tvs cenv ps = Success (ts,tenv)) ⇒ type_ps tvs cenv ps ts tenv)`,
ho_match_mp_tac check_p_ind >>
rw [check_p_def] >>
ONCE_REWRITE_TAC [type_p_cases] >>
rw [] >>
fs [monad_bind_success, ex_return_def, check_freevars_ex_correct] >|
[every_case_tac >>
     fs [monad_bind_success, failwith_def],
 every_case_tac >>
     fs [monad_bind_success, failwith_def] >>
     metis_tac [],
 every_case_tac >>
     fs [monad_bind_success, failwith_def, check_freevars_ex_correct] >>
     metis_tac [],
 cheat,
 PairCases_on `r'` >>
     fs [] >>
     metis_tac [],
 PairCases_on `r'` >>
     fs [monad_bind_success] >>
     PairCases_on `r'` >>
     fs [monad_bind_success] >>
     rw [] >>
     metis_tac []]);

val check_e_sound = Q.store_thm ("check_e_sound",
`(!cenv tenv e t. 
    (check_e cenv tenv e = Success t) ⇒ type_e cenv tenv e t) ∧
 (!cenv tenv es ts. 
    (check_es cenv tenv es = Success ts) ⇒ type_es cenv tenv es ts) ∧
 (!cenv tenv funs tenv'. 
    (check_funs cenv tenv funs = Success tenv') ⇒ 
    type_funs cenv tenv funs tenv') ∧
 (!cenv tenv pes t1 t2 t2'. 
    (check_pes cenv tenv pes t1 t2 = Success t2') 
    ⇒ 
    (t2 = t2') ∧
    (∀((p,e) :: set pes).∃ tenv'.
       ALL_DISTINCT (pat_bindings p []) ∧
       type_p (num_tvs tenv) cenv p t1 tenv' ∧
       type_e cenv (bind_var_list 0 tenv' tenv) e t2))`,
ho_match_mp_tac check_e_ind >>
rw [check_e_def, ex_return_def, LET_THM, failwith_def, monad_bind_success] >>
ONCE_REWRITE_TAC [type_e_cases] >>
rw [] >|
[cheat,
 every_case_tac >>
     fs [] >>
     metis_tac [],
 every_case_tac >>
     fs [] >>
     metis_tac [],
 cheat,
 every_case_tac >>
     fs [monad_bind_success] >>
     PairCases_on `r'` >>
     fs [monad_bind_success] >>
     every_case_tac >>
     fs [iter_ex_correct, lookup_tenv_ex_correct, check_freevars_ex_correct] >>
     metis_tac [],
 every_case_tac >>
     fs [monad_bind_success, check_freevars_ex_correct] >>
     metis_tac [],
 cases_on `uop` >>
     fs [check_uop_def, type_uop_def, ex_return_def] >-
     metis_tac [] >>
     qexists_tac `t1` >>
     cases_on `t1` >>
     fs [check_uop_def, failwith_def, ex_return_def] >>
     cases_on `l` >>
     fs [] >>
     every_case_tac >>
     fs [],
 cases_on `op` >>
     fs [Tint_def, Tref_def, check_op_def, type_op_def, ex_return_def] >|
     [qexists_tac `t1` >>
          fs [check_op_def, failwith_def] >>
          qexists_tac `t2` >>
          fs [check_op_def, failwith_def, ex_return_def] >>
          cases_on `(t1 = Tapp [] TC_int) ∧ (t2 = Tapp [] TC_int)` >>
          fs [] >>
          fs [] >>
          rw [],
      qexists_tac `t1` >>
          fs [check_op_def, failwith_def] >>
          qexists_tac `t2` >>
          fs [check_op_def, failwith_def, ex_return_def] >>
          cases_on `(t1 = Tapp [] TC_int) ∧ (t2 = Tapp [] TC_int)` >>
          fs [] >>
          fs [] >>
          rw [],
      every_case_tac >>
          fs [failwith_def] >>
          metis_tac [],
      qexists_tac `t1` >>
          fs [check_op_def, failwith_def] >>
          cases_on `t1` >>
          fs [failwith_def, ex_return_def] >>
          every_case_tac >>
          fs [],
      qexists_tac `t1` >>
          cases_on `t1` >>
          fs [check_op_def, failwith_def] >>
          cases_on `l` >>
          fs [] >>
          cases_on `t''` >>
          fs [] >>
          cases_on `t'` >>
          fs [] >>
          every_case_tac >>
          fs [failwith_def, ex_return_def]],
 every_case_tac >>
     fs [],
 every_case_tac >>
     fs [],
 every_case_tac >>
     fs [],
 every_case_tac >>
     fs [],
 every_case_tac >>
     fs [],
 every_case_tac >>
     fs [],
 cases_on `pes` >>
     fs [RES_FORALL] >>
     PairCases_on `h` >>
     fs [monad_bind_success] >>
     PairCases_on `r'` >>
     fs [monad_bind_success] >>
     every_case_tac >>
     fs [] >>
     qexists_tac `r'0` >>
     rw [] >>
     rw [] >>
     metis_tac [check_p_sound],
 every_case_tac >>
     fs [monad_bind_success] >>
     every_case_tac >>
     fs [],
 every_case_tac >>
     fs [monad_bind_success] >>
     every_case_tac >>
     fs [] >>
     metis_tac [],
 every_case_tac >>
     fs [check_freevars_ex_correct, monad_bind_success] >>
     every_case_tac >>
     fs [check_freevars_ex_correct, monad_bind_success] >>
     fs [Tfn_def] >>
     metis_tac [],
 rw [RES_FORALL],
 PairCases_on `r'` >>
     fs [monad_bind_success] >>
     every_case_tac >>
     fs [],
 PairCases_on `r'` >>
     fs [monad_bind_success] >>
     every_case_tac >>
     fs [RES_FORALL] >>
     rw [] >>
     fs [] >|
     [`type_p (num_tvs tenv) cenv p r'0 r'1 ∧
       type_e cenv (bind_var_list 0 r'1 tenv) e t2` 
                by metis_tac [check_p_sound] >>
          pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
          fs [] >>
          rw [] >>
          metis_tac [],
      PairCases_on `x` >>
          rw [] >>
          res_tac >>
          fs [] >>
          pop_assum MP_TAC >>
          pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
          fs [] >>
          rw [] >>
          metis_tac []]]);

val _ = export_theory ();
