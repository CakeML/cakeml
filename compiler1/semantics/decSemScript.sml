open HolKernel boolLib bossLib Parse lcsymtacs
     conSemTheory

val _ = new_theory"decSem"

(* The values of decLang are the same as conLang.
 *
 * The semantics of decLang differ in that the global environment is now
 * store-like rather than environment-like. The expressions for extending and
 * initialising it modify the global environment (instead of just raising a
 * type error).
 *)

val _ = temp_type_abbrev("count_store_genv", ``:'a count_store_trace # ('a option) list``);

val _ = Define `
 (do_app (((count,s,t),genv):conSem$v count_store_genv) op vs =
  case (op,vs) of
   | (Op op, vs) =>
     (case conSem$do_app (s,t) (Op op) vs of
      | NONE => NONE
      | SOME ((s,t),r) => SOME (((count,s,t),genv),r))
   | (Init_global_var idx, [v]) =>
     if idx < LENGTH genv then
       (case EL idx genv of
        | NONE => SOME (((count,s,t), LUPDATE (SOME v) idx genv), (Rval (Conv NONE [])))
        | SOME x => NONE)
     else NONE
   | _ => NONE)`;

val _ = type_abbrev("all_env", ``:exh_ctors_env # (varN, conSem$v) alist``);

val _ = Hol_reln ` (! ck env l s.
evaluate ck (env:all_env) (s:conSem$v count_store_genv) ((Lit l):conLang$exp) (s, Rval (Litv l)))

/\ (! ck env e s1 s2 v.
(evaluate ck s1 env e (s2, Rval v))
==>
evaluate ck s1 env (Raise e) (s2, Rerr (Rraise v)))

/\ (! ck env e s1 s2 err.
(evaluate ck s1 env e (s2, Rerr err))
==>
evaluate ck s1 env (Raise e) (s2, Rerr err))

/\ (! ck s1 s2 env e v pes.
(evaluate ck s1 env e (s2, Rval v))
==>
evaluate ck s1 env (Handle e pes) (s2, Rval v))

/\ (! ck s1 s2 env e pes v bv.
(evaluate ck env s1 e (s2, Rerr (Rraise v)) /\
evaluate_match ck env s2 v pes v bv)
==>
evaluate ck env s1 (Handle e pes) bv)

/\ (! ck s1 s2 env e pes a.
(evaluate ck env s1 e (s2, Rerr (Rabort a)))
==>
evaluate ck env s1 (Handle e pes) (s2, Rerr (Rabort a)))

/\ (! ck env tag es vs s s'.
(evaluate_list ck env s (REVERSE es) (s', Rval vs))
==>
evaluate ck env s (Con tag es) (s', Rval (Conv tag (REVERSE vs))))

/\ (! ck env tag es err s s'.
(evaluate_list ck env s (REVERSE es) (s', Rerr err))
==>
evaluate ck env s (Con tag es) (s', Rerr err))

/\ (! ck exh env n v s.
(ALOOKUP env n = SOME v)
==>
evaluate ck (exh,env) s (Var_local n) (s, Rval v))

/\ (! ck env n v s genv.
((LENGTH genv > n) /\
(EL n genv = SOME v))
==>
evaluate ck env (s,genv) (Var_global n) ((s,genv), Rval v))

/\ (! ck exh env n e s.
evaluate ck (exh,env) s (Fun n e) (s, Rval (Closure env n e)))

/\ (! ck exh genv env es vs env' e bv s1 s2 t2 count genv'.
(evaluate_list ck (exh,env) (s1,genv) (REVERSE es) (((count,s2,t2),genv'), Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env', e)) /\
(ck ==> count ≠ 0) /\
evaluate ck (exh,env') (((if ck then count-1 else count),s2,t2),genv') e bv)
==>
evaluate ck (exh,env) (s1,genv) (App (Op Opapp) es) bv)

/\ (! ck env es vs env' e s1 s2 t2 count genv.
(evaluate_list ck env s1 (REVERSE es) (((count,s2,t2), genv), Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env', e)) /\
(count = 0) /\
ck)
==>
evaluate ck env s1 (App (Op Opapp) es) (((0,s2,t2),genv), Rerr (Rabort Rtimeout_error)))

/\ (! ck env s1 op es s2 vs s3 res.
(evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) /\
(do_app s2 op (REVERSE vs) = SOME (s3, res)) /\
(op <> Op Opapp))
==>
evaluate ck env s1 (App op es) (s3, res))

/\ (! ck env s1 op es s2 err.
(evaluate_list ck env s1 (REVERSE es) (s2, Rerr err))
==>
evaluate ck env s1 (App op es) (s2, Rerr err))

/\ (! ck env e pes v bv s1 s2.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_match ck env s2 v pes (Conv (SOME (bind_tag, (TypeExn (Short "Bind")))) []) bv)
==>
evaluate ck env s1 (Mat e pes) bv)

/\ (! ck env e pes err s s'.
(evaluate ck env s e (s', Rerr err))
==>
evaluate ck env s (Mat e pes) (s', Rerr err))

/\ (! ck exh env n e1 e2 v bv s1 s2.
(evaluate ck (exh,env) s1 e1 (s2, Rval v) /\
evaluate ck (exh,opt_bind n v env) s2 e2 bv)
==>
evaluate ck (exh,env) s1 (Let n e1 e2) bv)

/\ (! ck env n e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Let n e1 e2) (s', Rerr err))

/\ (! ck exh env funs e bv s.
(ALL_DISTINCT (MAP FST funs) /\
evaluate ck (exh,build_rec_env funs env env) s e bv)
==>
evaluate ck (exh,env) s (Letrec funs e) bv)

/\ (! ck env n s genv.
evaluate ck env (s,genv) (Extend_global n) ((s,(genv++GENLIST (K NONE) n)), Rval (Conv NONE [])))

/\ (! ck env s.
evaluate_list ck env s [] (s, Rval []))

/\ (! ck env e es v vs s1 s2 s3.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_list ck env s2 es (s3, Rval vs))
==>
evaluate_list ck env s1 (e::es) (s3, Rval (v::vs)))

/\ (! ck env e es err s s'.
(evaluate ck env s e (s', Rerr err))
==>
evaluate_list ck env s (e::es) (s', Rerr err))

/\ (! ck env e es v err s1 s2 s3.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_list ck env s2 es (s3, Rerr err))
==>
evaluate_list ck env s1 (e::es) (s3, Rerr err))

/\ (! ck env v s err_v.
evaluate_match ck env s v [] err_v (s, Rerr (Rraise err_v)))

/\ (! ck exh env env' v p pes e bv s t count genv err_v.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch exh s p v env = Match env') /\
evaluate ck (exh,env') ((count,s,t),genv) e bv)
==>
evaluate_match ck (exh,env) ((count,s,t),genv) v ((p,e)::pes) err_v bv)

/\ (! ck exh genv env v p e pes bv s t count err_v.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch exh s p v env = No_match) /\
evaluate_match ck (exh,env) ((count,s,t),genv) v pes err_v bv)
==>
evaluate_match ck (exh,env) ((count,s,t),genv) v ((p,e)::pes) err_v bv)`;

val _ = export_theory()
