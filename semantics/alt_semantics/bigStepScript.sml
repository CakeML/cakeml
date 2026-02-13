(*
  A clocked relational big-step semantics for CakeML. This semantics
  is no longer used in the CakeML development.
*)
Theory bigStep
Ancestors
  namespace ast ffi semanticPrimitives smallStep

val _ = numLib.temp_prefer_num();

(* To get the definition of expression divergence to use in defining definition
 * divergence *)

(* getOpClass as a inductive to make the proofs potentially easier *)
Inductive opClass:
(∀ op. opClass (FFI op) Simple) ∧
(∀ op1 op2 op3. opClass (Shift op1 op2 op3) Simple) ∧
(∀ op. op = Equality ∨ op = Opassign ∨
       op = Opref ∨ op = Aw8alloc ∨ op = Aw8sub ∨ op = Aw8length ∨
       op = Aw8update ∨ op = CopyStrStr ∨ op = CopyStrAw8 ∨
       op = CopyAw8Str ∨ op = CopyAw8Aw8 ∨
       op = Implode ∨ op = Explode ∨ op = Strsub ∨ op = Strlen ∨
       op = Strcat ∨ op = VfromList ∨ op = Vsub ∨ op = Vsub_unsafe ∨
       op = XorAw8Str_unsafe ∨ (∃test ty. op = Test test ty) ∨
       (∃a ty. op = Arith a ty) ∨ (∃ty1 ty2. op = FromTo ty1 ty2) ∨
       op = Vlength ∨ op = Aalloc ∨ op = AallocEmpty ∨ op = Asub ∨
       op = Alength ∨ op = Aupdate ∨ op = Asub_unsafe ∨ op = Aupdate_unsafe ∨
       op = Aw8sub_unsafe ∨ op = Aw8update_unsafe ∨ op = ListAppend ∨
       op = ConfigGC ∨ op = Env_id ∨ op = Opderef ∨ op = AallocFixed
       ⇒
       opClass op Simple) ∧
(* FunApp *)
(opClass Opapp FunApp) ∧
(* Eval *)
(opClass Eval EvalOp) ∧
(* Thunks *)
(opClass (ThunkOp ForceThunk) Force) ∧
(∀op. op ≠ ForceThunk ⇒ opClass (ThunkOp op) Simple)
End

(* ------------------------ Big step semantics -------------------------- *)

(* If the first argument is true, the big step semantics counts down how many
   functions applications have happened, and raises an exception when the counter
   runs out. *)

Inductive evaluate:
(! ck env l s.
T
==>
evaluate ck env s (Lit l) (s, Rval (Litv l)))

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
evaluate_match ck env s2 v pes v bv /\
can_pmatch_all env.c s2.refs (MAP FST pes) v)
==>
evaluate ck env s1 (Handle e pes) bv)

/\ (! ck s1 s2 env e pes a.
(evaluate ck env s1 e (s2, Rerr (Rabort a)))
==>
evaluate ck env s1 (Handle e pes) (s2, Rerr (Rabort a)))

/\ (! ck s1 s2 env e pes v.
(evaluate ck env s1 e (s2, Rerr (Rraise v)) /\
~ (can_pmatch_all env.c s2.refs (MAP FST pes) v))
==>
evaluate ck env s1 (Handle e pes) (s2, Rerr (Rabort Rtype_error)))

/\ (! ck env cn es vs s s' v.
(do_con_check env.c cn (LENGTH es) /\
(build_conv env.c cn (REVERSE vs) = SOME v) /\
evaluate_list ck env s (REVERSE es) (s', Rval vs))
==>
evaluate ck env s (Con cn es) (s', Rval v))

/\ (! ck env cn es s.
(~ (do_con_check env.c cn (LENGTH es)))
==>
evaluate ck env s (Con cn es) (s, Rerr (Rabort Rtype_error)))

/\ (! ck env cn es err s s'.
(do_con_check env.c cn (LENGTH es) /\
evaluate_list ck env s (REVERSE es) (s', Rerr err))
==>
evaluate ck env s (Con cn es) (s', Rerr err))

/\ (! ck env n v s.
(nsLookup env.v n = SOME v)
==>
evaluate ck env s (Var n) (s, Rval v))

/\ (! ck env n s.
(nsLookup env.v n = NONE)
==>
evaluate ck env s (Var n) (s, Rerr (Rabort Rtype_error)))

/\ (! ck env n e s.
T
==>
evaluate ck env s (Fun n e) (s, Rval (Closure env n e)))

/\ (! ck env es vs env' e bv s1 s2.
(evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env', e)) /\
(ck ==> ~ (s2.clock =(( 0 : num)))) /\
(opClass op FunApp) /\
evaluate ck env' (if ck then ( s2 with<| clock := (s2.clock -( 1 : num)) |>) else s2) e bv)
==>
evaluate ck env s1 (App op es) bv)

/\ (! ck env es vs env' e s1 s2.
(evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env', e)) /\
(s2.clock =( 0 : num)) /\
(opClass op FunApp) /\
ck)
==>
evaluate ck env s1 (App op es) (s2, Rerr (Rabort Rtimeout_error)))

/\ (! ck env es vs s1 s2.
(evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) /\
(do_opapp (REVERSE vs) = NONE)) /\
(opClass op FunApp)
==>
evaluate ck env s1 (App op es) (s2, Rerr (Rabort Rtype_error)))

/\ (! ck env op es vs res s1 s2 refs' ffi'.
(evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) /\
(do_app (s2.refs,s2.ffi) op (REVERSE vs) = SOME ((refs',ffi'), res)) /\
(opClass op Simple))
==>
evaluate ck env s1 (App op es) (( s2 with<| refs := refs'; ffi :=ffi' |>), res))

∧

(∀ck env op es vs s1 s2.
  evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) ∧
  opClass op Force ∧
  dest_thunk (REVERSE vs) s2.refs = BadRef
 ⇒ evaluate ck env s1 (App op es) (s2, Rerr (Rabort Rtype_error)))

∧

(∀ck env op es vs s1 s2.
  evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) ∧
  opClass op Force ∧
  dest_thunk (REVERSE vs) s2.refs = NotThunk
 ⇒ evaluate ck env s1 (App op es) (s2, Rerr (Rabort Rtype_error)))

∧

(∀ck env op es vs s1 s2 f.
  evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) ∧
  opClass op Force ∧
  dest_thunk (REVERSE vs) s2.refs = IsThunk NotEvaluated f ∧
  do_opapp [f; Conv NONE []] = NONE
 ⇒ evaluate ck env s1 (App op es) (s2, Rerr (Rabort Rtype_error)))

∧

(∀ck env op es vs v s1 s2.
  evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) ∧
  opClass op Force ∧
  dest_thunk (REVERSE vs) s2.refs = IsThunk Evaluated v
 ⇒ evaluate ck env s1 (App op es) (s2, Rval v))

∧

(∀ck env op es vs s1 s2 f env_e.
  evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) ∧
  opClass op Force ∧
  dest_thunk (REVERSE vs) s2.refs = IsThunk NotEvaluated f ∧
  do_opapp [f; Conv NONE []] = SOME env_e ∧
  ck ∧ s2.clock = 0
 ⇒ evaluate ck env s1 (App op es) (s2, Rerr (Rabort Rtimeout_error)))

∧

(∀ck env op es vs s1 s2 f env' e s3 err.
  evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) ∧
  opClass op Force ∧
  dest_thunk (REVERSE vs) s2.refs = IsThunk NotEvaluated f ∧
  do_opapp [f; Conv NONE []] = SOME (env', e) ∧
  (ck ⇒ s2.clock ≠ 0) ∧
  evaluate ck env' (if ck then (s2 with clock := s2.clock - 1) else s2) e (s3, Rerr err)
 ⇒ evaluate ck env s1 (App op es) (s3, Rerr err))

∧

(∀ck env op es vs s1 s2 f env' e s3 vs2.
  evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) ∧
  opClass op Force ∧
  dest_thunk (REVERSE vs) s2.refs = IsThunk NotEvaluated f ∧
  do_opapp [f; Conv NONE []] = SOME (env', e) ∧
  (ck ⇒ s2.clock ≠ 0) ∧
  evaluate ck env' (if ck then (s2 with clock := s2.clock - 1) else s2) e (s3, Rval vs2) ∧
  update_thunk (REVERSE vs) s3.refs [vs2] = NONE
 ⇒ evaluate ck env s1 (App op es) (s3, Rerr (Rabort Rtype_error)))

∧

(∀ck env op es vs s1 s2 f env' e s3 vs2 refs.
  evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) ∧
  opClass op Force ∧
  dest_thunk (REVERSE vs) s2.refs = IsThunk NotEvaluated f ∧
  do_opapp [f; Conv NONE []] = SOME (env', e) ∧
  (ck ⇒ s2.clock ≠ 0) ∧
  evaluate ck env' (if ck then (s2 with clock := s2.clock - 1) else s2) e (s3, Rval vs2) ∧
  update_thunk (REVERSE vs) s3.refs [vs2] = SOME refs
 ⇒ evaluate ck env s1 (App op es) (s3 with refs := refs, Rval vs2))

/\ (! ck env op es vs s1 s2.
      evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) /\
      do_app (s2.refs,s2.ffi) op (REVERSE vs) = NONE /\
      ¬opClass op FunApp ∧ ¬opClass op Force
==>
      evaluate ck env s1 (App op es) (s2, Rerr (Rabort Rtype_error)))

/\ (! ck env op es err s1 s2.
(evaluate_list ck env s1 (REVERSE es) (s2, Rerr err))
==>
evaluate ck env s1 (App op es) (s2, Rerr err))

/\ (! ck env op e1 e2 v e' bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
(do_log op v e2 = SOME (Exp e')) /\
evaluate ck env s2 e' bv)
==>
evaluate ck env s1 (Log op e1 e2) bv)

/\ (! ck env op e1 e2 v bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
(do_log op v e2 = SOME (Val bv)))
==>
evaluate ck env s1 (Log op e1 e2) (s2, Rval bv))

/\ (! ck env op e1 e2 v s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
(do_log op v e2 = NONE))
==>
evaluate ck env s1 (Log op e1 e2) (s2, Rerr (Rabort Rtype_error)))

/\ (! ck env op e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Log op e1 e2) (s', Rerr err))

/\ (! ck env e1 e2 e3 v e' bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
(do_if v e2 e3 = SOME e') /\
evaluate ck env s2 e' bv)
==>
evaluate ck env s1 (If e1 e2 e3) bv)

/\ (! ck env e1 e2 e3 v s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
(do_if v e2 e3 = NONE))
==>
evaluate ck env s1 (If e1 e2 e3) (s2, Rerr (Rabort Rtype_error)))

/\ (! ck env e1 e2 e3 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (If e1 e2 e3) (s', Rerr err))

/\ (! ck env e pes v bv s1 s2.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_match ck env s2 v pes bind_exn_v bv /\
can_pmatch_all env.c s2.refs (MAP FST pes) v)
==>
evaluate ck env s1 (Mat e pes) bv)

/\ (! ck env e pes err s s'.
(evaluate ck env s e (s', Rerr err))
==>
evaluate ck env s (Mat e pes) (s', Rerr err))

/\ (! ck env e pes v s1 s2.
(evaluate ck env s1 e (s2, Rval v) /\
~ (can_pmatch_all env.c s2.refs (MAP FST pes) v))
==>
evaluate ck env s1 (Mat e pes) (s2, Rerr (Rabort Rtype_error)))

/\ (! ck env n e1 e2 v bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
evaluate ck ( env with<| v := (nsOptBind n v env.v) |>) s2 e2 bv)
==>
evaluate ck env s1 (Let n e1 e2) bv)

/\ (! ck env n e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Let n e1 e2) (s', Rerr err))

/\ (! ck env funs e bv s.
(ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) /\
evaluate ck ( env with<| v := (build_rec_env funs env env.v) |>) s e bv)
==>
evaluate ck env s (Letrec funs e) bv)

/\ (! ck env funs e s.
(~ (ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs)))
==>
evaluate ck env s (Letrec funs e) (s, Rerr (Rabort Rtype_error)))

/\ (! ck env e t s bv.
(evaluate ck env s e bv)
==>
evaluate ck env s (Tannot e t) bv)

/\ (! ck env e l s bv.
(evaluate ck env s e bv)
==>
evaluate ck env s (Lannot e l) bv)

/\ (! ck env s.
T
==>
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

/\ (! ck env v err_v s.
T
==>
evaluate_match ck env s v [] err_v (s, Rerr (Rraise err_v)))

/\ (! ck env env' v p pes e bv err_v s.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch env.c s.refs p v [] = Match env') /\
evaluate ck ( env with<| v := (nsAppend (alist_to_ns env') env.v) |>) s e bv)
==>
evaluate_match ck env s v ((p,e)::pes) err_v bv)

/\ (! ck env v p e pes bv s err_v.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch env.c s.refs p v [] = No_match) /\
evaluate_match ck env s v pes err_v bv)
==>
evaluate_match ck env s v ((p,e)::pes) err_v bv)

/\ (! ck env v p e pes s err_v.
(pmatch env.c s.refs p v [] = Match_type_error)
==>
evaluate_match ck env s v ((p,e)::pes) err_v (s, Rerr (Rabort Rtype_error)))

/\ (! ck env v p e pes s err_v.
(~ (ALL_DISTINCT (pat_bindings p [])))
==>
evaluate_match ck env s v ((p,e)::pes) err_v (s, Rerr (Rabort Rtype_error)))
End

(* The set tid_or_exn part of the state tracks all of the types and exceptions
 * that have been declared *)
Inductive evaluate_dec:
(! ck env p e v env' s1 s2 locs.
(evaluate ck env s1 e (s2, Rval v) /\
ALL_DISTINCT (pat_bindings p []) /\
every_exp (one_con_check env.c) e /\
(pmatch env.c s2.refs p v [] = Match env'))
==>
evaluate_dec ck env s1 (Dlet locs p e) (s2, Rval <| v := (alist_to_ns env'); c := nsEmpty |>))

/\ (! ck env p e v s1 s2 locs.
(evaluate ck env s1 e (s2, Rval v) /\
ALL_DISTINCT (pat_bindings p []) /\
every_exp (one_con_check env.c) e /\
(pmatch env.c s2.refs p v [] = No_match))
==>
evaluate_dec ck env s1 (Dlet locs p e) (s2, Rerr (Rraise bind_exn_v)))

/\ (! ck env p e v s1 s2 locs.
(evaluate ck env s1 e (s2, Rval v) /\
ALL_DISTINCT (pat_bindings p []) /\
every_exp (one_con_check env.c) e /\
(pmatch env.c s2.refs p v [] = Match_type_error))
==>
evaluate_dec ck env s1 (Dlet locs p e) (s2, Rerr (Rabort Rtype_error)))

/\ (! ck env p e s locs.
(~ (ALL_DISTINCT (pat_bindings p []) /\
    every_exp (one_con_check env.c) e))
==>
evaluate_dec ck env s (Dlet locs p e) (s, Rerr (Rabort Rtype_error)))

/\ (! ck env p e err s s' locs.
(evaluate ck env s e (s', Rerr err) /\
ALL_DISTINCT (pat_bindings p []) /\
every_exp (one_con_check env.c) e)
==>
evaluate_dec ck env s (Dlet locs p e) (s', Rerr err))

/\ (! ck env funs s locs.
(ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) /\
 EVERY (λ(f,n,e). every_exp (one_con_check env.c) e) funs)
==>
evaluate_dec ck env s (Dletrec locs funs) (s, Rval <| v := (build_rec_env funs env nsEmpty); c := nsEmpty |>))

/\ (! ck env funs s locs.
(~ (ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) /\
    EVERY (λ(f,n,e). every_exp (one_con_check env.c) e) funs))
==>
evaluate_dec ck env s (Dletrec locs funs) (s, Rerr (Rabort Rtype_error)))

/\ (! ck env tds s locs.
(EVERY check_dup_ctors tds)
==>
evaluate_dec ck env s (Dtype locs tds)
    (( s with<| next_type_stamp := (s.next_type_stamp + LENGTH tds) |>),
     Rval <| v := nsEmpty; c := (build_tdefs s.next_type_stamp tds) |>))

/\ (! ck env tds s locs.
(~ (EVERY check_dup_ctors tds))
==>
evaluate_dec ck env s (Dtype locs tds) (s, Rerr (Rabort Rtype_error)))

/\ (! ck env st x es' n.
(declare_env st.eval_state env = SOME (x, es'))
==>
evaluate_dec ck env st (Denv n)
  (( st with<| eval_state := es' |>), Rval <| v := (nsSing n x) ; c := nsEmpty |>))

/\ (! ck env st n.
(declare_env st.eval_state env = NONE)
==>
evaluate_dec ck env st (Denv n) (st, Rerr (Rabort Rtype_error)))

/\ (! ck env tvs tn t s locs.
T
==>
evaluate_dec ck env s (Dtabbrev locs tvs tn t) (s, Rval <| v := nsEmpty; c := nsEmpty |>))

/\ (! ck env cn ts s locs.
T
==>
evaluate_dec ck env s (Dexn locs cn ts)
    (( s with<| next_exn_stamp := (s.next_exn_stamp +( 1 : num)) |>),
     Rval  <| v := nsEmpty; c := (nsSing cn (LENGTH ts, ExnStamp s.next_exn_stamp)) |>))

/\ (! ck s1 s2 env ds mn new_env.
(evaluate_decs ck env s1 ds (s2, Rval new_env))
==>
evaluate_dec ck env s1 (Dmod mn ds) (s2, Rval <| v := (nsLift mn new_env.v); c := (nsLift mn new_env.c) |>))

/\ (! ck s1 s2 env ds mn err.
(evaluate_decs ck env s1 ds (s2, Rerr err))
==>
evaluate_dec ck env s1 (Dmod mn ds) (s2, Rerr err))

/\ (! ck s1 s2 env lds ds new_env r.
(evaluate_decs ck env s1 lds (s2, Rval new_env) /\
evaluate_decs ck (extend_dec_env new_env env) s2 ds r)
==>
evaluate_dec ck env s1 (Dlocal lds ds) r)

/\ (! ck s1 s2 env lds ds err.
(evaluate_decs ck env s1 lds (s2, Rerr err))
==>
evaluate_dec ck env s1 (Dlocal lds ds) (s2, Rerr err))

/\ (! ck env s.
T
==>
evaluate_decs ck env s [] (s, Rval <| v := nsEmpty; c := nsEmpty |>))

/\ (! ck s1 s2 env d ds e.
(evaluate_dec ck env s1 d (s2, Rerr e))
==>
evaluate_decs ck env s1 (d::ds) (s2, Rerr e))

/\ (! ck s1 s2 s3 env d ds new_env r.
(evaluate_dec ck env s1 d (s2, Rval new_env) /\
evaluate_decs ck (extend_dec_env new_env env) s2 ds (s3, r))
==>
evaluate_decs ck env s1 (d::ds) (s3, combine_dec_result new_env r))
End

Inductive dec_diverges:
(! env st locs p e.
(ALL_DISTINCT (pat_bindings p []) /\
 every_exp (one_con_check env.c) e /\
 e_diverges env (st.refs, st.ffi) e)
==>
dec_diverges env st (Dlet locs p e))

/\ (! st env ds mn.
(decs_diverges env st ds)
==>
dec_diverges env st (Dmod mn ds))

/\ (! st env lds ds st2 new_env.
(evaluate_decs F env st lds (st2, Rval new_env) /\
decs_diverges (extend_dec_env new_env env) st2 ds)
==>
dec_diverges env st (Dlocal lds ds))

/\ (! st env lds ds.
(decs_diverges env st lds)
==>
dec_diverges env st (Dlocal lds ds))

/\ (! st env d ds.
(dec_diverges env st d)
==>
decs_diverges env st (d::ds))

/\ (! s1 s2 env d ds new_env.
(evaluate_dec F env s1 d (s2, Rval new_env) /\
decs_diverges (extend_dec_env new_env env) s2 ds)
==>
decs_diverges env s1 (d::ds))
End
