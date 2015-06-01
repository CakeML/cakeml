open preamble bigStepTheory modLangTheory;

val _ = new_theory "modSem"

(* The values of modLang differ in that the closures do not contain a module
 * environment.
 *
 * The semantics of modLang differ in that there is no module environment menv, nor
 * are top-level bindings added to the normal env, thus when a closure is
 * created, only locals bindings are put into it. There is a global environment
 * genv, which is just a list of the top-level bindings seen so far, with the
 * older bindings nearer the head. Global variable reference expressions simply
 * index into global environment. Top-level let rec declarations evaluate to
 * closures, rather than to recursive closures, since the recursion can be
 * handled through the genv. The expressions bound to top-level lets must
 * evaluate to a tuple with exactly as many things in it as the number of
 * bindings that the let will bind.
 *)

val _ = Datatype`
  v =
    | Litv lit
    | Conv ((conN # tid_or_exn) option) (v list)
    | Closure (envC # (varN, v) alist) varN modLang$exp
    | Recclosure (envC # (varN, v) alist) ((varN # varN # modLang$exp) list) varN
    | Loc num
    | Vectorv (v list)`;

val _ = Define`
  Boolv b = Conv (SOME ((if b then "true" else "false"), TypeId (Short "bool"))) []`;

val _ = type_abbrev( "all_env", ``:(modSem$v option) list # envC # (varN, modSem$v)alist``);

val all_env_to_genv_def = Define `
  all_env_to_genv ((genv,cenv,env):all_env) = genv`;

val all_env_to_cenv_def = Define `
  all_env_to_cenv ((genv,cenv,env):all_env) = cenv`;

val all_env_to_env_def = Define `
  all_env_to_env ((genv,cenv,env):all_env) = env`;

val build_conv_def = Define`
  build_conv (envC:envC) cn vs =
  case cn of
  | NONE => SOME (Conv NONE vs)
  | SOME id =>
    (case lookup_alist_mod_env id envC of
     | NONE => NONE
     | SOME (len,t) => SOME (Conv (SOME (id_to_n id, t)) vs))`;

val build_rec_env_def = Define `
  build_rec_env funs cl_env add_to_env =
    FOLDR (λ(f,x,e) env'. (f, Recclosure cl_env funs f) :: env')
      add_to_env funs`;

val do_eq_def = tDefine"do_eq"`
  (do_eq (Litv l1) (Litv l2) =
   if lit_same_type l1 l2 then Eq_val (l1 = l2)
   else Eq_type_error)
  ∧
  (do_eq (Loc l1) (Loc l2) = Eq_val (l1 = l2))
  ∧
  (do_eq (Conv cn1 vs1) (Conv cn2 vs2) =
   if (cn1 = cn2) ∧ (LENGTH vs1 = LENGTH vs2) then
     do_eq_list vs1 vs2
   else if ctor_same_type cn1 cn2 then
     Eq_val F
   else
     Eq_type_error)
  ∧
  (do_eq (Vectorv vs1) (Vectorv vs2) =
   if LENGTH vs1 = LENGTH vs2 then
     do_eq_list vs1 vs2
   else
     Eq_val F)
  ∧
  (do_eq (Closure _ _ _) (Closure _ _ _) = Eq_closure)
  ∧
  (do_eq (Closure _ _ _) (Recclosure _ _ _) = Eq_closure)
  ∧
  (do_eq (Recclosure _ _ _) (Closure _ _ _) = Eq_closure)
  ∧
  (do_eq (Recclosure _ _ _) (Recclosure _ _ _) = Eq_closure)
  ∧
  (do_eq _ _ = Eq_type_error)
  ∧
  (do_eq_list [] [] = Eq_val T)
  ∧
  (do_eq_list (v1::vs1) (v2::vs2) =
   (case do_eq v1 v2 of
    | Eq_closure => Eq_closure
    | Eq_type_error => Eq_type_error
    | Eq_val r =>
      if r then
        do_eq_list vs1 vs2
      else
        Eq_val F))
  ∧
  (do_eq_list _ _ = Eq_val F)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_size x
                                         | INR (xs,ys) => v4_size xs)`);

val prim_exn_def = Define`
  prim_exn cn = Conv (SOME (cn, TypeExn (Short cn))) []`;

(* Do an application *)
val do_opapp_def = Define `
  do_opapp (genv:modSem$v option list) vs =
  case vs of
    | [Closure (cenv, env) n e; v] =>
      SOME ((genv, cenv, ((n,v) :: env)), e)
    | [Recclosure (cenv, env) funs n; v] =>
      if ALL_DISTINCT (MAP FST funs) then
        (case find_recfun n funs of
         | SOME (n,e) =>
             SOME ((genv, cenv, ((n,v) :: build_rec_env funs (cenv, env) env)), e)
         | NONE => NONE)
      else NONE
    | _ => NONE`;

val v_to_list_def = Define `
  (v_to_list (Conv (SOME (cn, TypeId (Short tn))) []) =
   if (cn = "nil") ∧ (tn = "list") then
     SOME []
   else NONE)
  ∧
  (v_to_list (Conv (SOME (cn,TypeId (Short tn))) [v1;v2]) =
   if (cn = "::") ∧ (tn = "list") then
     (case v_to_list v2 of
      | SOME vs => SOME (v1::vs)
      | NONE => NONE)
   else NONE)
  ∧
  (v_to_list _ = NONE)`;

val v_to_char_list_def = Define `
 (v_to_char_list (Conv (SOME (cn, TypeId (Short tn))) []) =
  if (cn = "nil") ∧ (tn = "list") then
    SOME []
  else NONE)
 ∧
 (v_to_char_list (Conv (SOME (cn,TypeId (Short tn))) [Litv (Char c);v]) =
  if (cn = "::") ∧ (tn = "list") then
    (case v_to_char_list v of
     | SOME cs => SOME (c::cs)
     | NONE => NONE)
  else NONE)
 ∧
 (v_to_char_list _ = NONE)`;

val char_list_to_v_def = Define`
 (char_list_to_v [] =
  Conv (SOME ("nil", TypeId (Short "list"))) [])
 ∧
 (char_list_to_v (c::cs) =
  Conv (SOME ("::", TypeId (Short "list"))) [Litv (Char c); char_list_to_v cs])`;

val do_app_def = Define `
  do_app (s,t) op (vs:modSem$v list) =
  case (op, vs) of
  | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    if ((op = Divide) ∨ (op = Modulo)) ∧ (n2 = 0) then
      SOME ((s,t), Rerr (Rraise (prim_exn "Div")))
    else
      SOME ((s,t), Rval (Litv (IntLit (opn_lookup op n1 n2))))
  | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    SOME ((s,t), Rval (Boolv (opb_lookup op n1 n2)))
  | (Equality, [v1; v2]) =>
    (case do_eq v1 v2 of
     | Eq_type_error => NONE
     | Eq_closure => SOME ((s,t), Rerr (Rraise (prim_exn "Eq")))
     | Eq_val b => SOME ((s,t), Rval (Boolv b)))
  | (Opassign, [Loc lnum; v]) =>
    (case store_assign lnum (Refv v) s of
     | SOME st => SOME ((st,t), Rval (Conv NONE []))
     | NONE => NONE)
  | (Opref, [v]) =>
    let (s',n) = (store_alloc (Refv v) s) in
      SOME ((s',t), Rval (Loc n))
  | (Opderef, [Loc n]) =>
    (case store_lookup n s of
     | SOME (Refv v) => SOME ((s,t),Rval v)
     | _ => NONE)
  | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
    if n < 0 then
      SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
    else
      let (s',lnum) =
        store_alloc (W8array (REPLICATE (Num (ABS ( n))) w)) s
      in
        SOME ((s',t), Rval (Loc lnum))
  | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s of
     | SOME (W8array ws) =>
       if i < 0 then
         SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
           else
             SOME ((s,t), Rval (Litv (Word8 (EL n ws))))
     | _ => NONE)
  | (Aw8length, [Loc n]) =>
    (case store_lookup n s of
     | SOME (W8array ws) =>
       SOME ((s,t),Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
     | _ => NONE)
  | (Aw8update, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
    (case store_lookup lnum s of
     | SOME (W8array ws) =>
       if i < 0 then
         SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
           else
             (case store_assign lnum (W8array (LUPDATE w n ws)) s of
              | NONE => NONE
              | SOME s' => SOME ((s',t), Rval (Conv NONE [])))
     | _ => NONE)
  | (Ord, [Litv (Char c)]) =>
    SOME ((s,t), Rval (Litv(IntLit(int_of_num(ORD c)))))
  | (Chr, [Litv (IntLit i)]) =>
    SOME ((s,t),
          if (i < 0) ∨ (i > 255) then
            Rerr (Rraise (prim_exn "Chr"))
          else
            Rval (Litv(Char(CHR(Num(ABS i))))))
  | (Chopb op, [Litv (Char c1); Litv (Char c2)]) =>
    SOME ((s,t), Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
  | (Implode, [v]) =>
    (case v_to_char_list v of
     | SOME ls =>
       SOME ((s,t), Rval (Litv (StrLit (IMPLODE ls))))
     | NONE => NONE)
  | (Explode, [Litv (StrLit str)]) =>
    SOME ((s,t), Rval (char_list_to_v (EXPLODE str)))
  | (Strlen, [Litv (StrLit str)]) =>
    SOME ((s,t), Rval (Litv(IntLit(int_of_num(STRLEN str)))))
  | (VfromList, [v]) =>
    (case v_to_list v of
     | SOME vs =>
       SOME ((s,t), Rval (Vectorv vs))
     | NONE => NONE)
  | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
    if i < 0 then
      SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
    else
      let n = (Num (ABS i)) in
        if n >= LENGTH vs then
          SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
        else
          SOME ((s,t), Rval (EL n vs))
  | (Vlength, [Vectorv vs]) =>
    SOME ((s,t), Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
  | (Aalloc, [Litv (IntLit n); v]) =>
    if n < 0 then
      SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
    else
      let (s',lnum) =
        store_alloc (Varray (REPLICATE (Num (ABS n)) v)) s
      in
        SOME ((s',t), Rval (Loc lnum))
  | (Asub, [Loc lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s of
     | SOME (Varray vs) =>
     if i < 0 then
       SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
         else
           SOME ((s,t), Rval (EL n vs))
     | _ => NONE)
    | (Alength, [Loc n]) =>
      (case store_lookup n s of
       | SOME (Varray ws) =>
         SOME ((s,t),Rval (Litv (IntLit(int_of_num(LENGTH ws)))))
       | _ => NONE)
  | (Aupdate, [Loc lnum; Litv (IntLit i); v]) =>
    (case store_lookup lnum s of
     | SOME (Varray vs) =>
     if i < 0 then
       SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
         else
           (case store_assign lnum (Varray (LUPDATE v n vs)) s of
            | NONE => NONE
            | SOME s' => SOME ((s',t), Rval (Conv NONE [])))
     | _ => NONE)
  | (FFI n, [Loc lnum]) =>
    (case store_lookup lnum s of
     | SOME (W8array ws) =>
       (case call_FFI n ws t of
        | SOME (ws', t') =>
          (case store_assign lnum (W8array ws') s of
           | SOME s' => SOME ((s', t'), Rval (Conv NONE []))
           | NONE => NONE)
        | NONE => SOME ((s, t), Rerr (Rabort Rffi_error)))
     | _ => NONE)
  | _ => NONE`;

val do_if_def = Define `
 (do_if v e1 e2 =
  if v = Boolv T then
    SOME e1
  else if v = Boolv F then
    SOME e2
  else
    NONE)`;

val pmatch_def = tDefine"pmatch"`
(pmatch envC s (Pvar x) v' env = (Match ((x,v') :: env)))
/\
(pmatch envC s (Plit l) (Litv l') env =
(if l = l' then
    Match env
  else if lit_same_type l l' then
    No_match
  else
    Match_type_error))
/\
(pmatch envC s (Pcon (SOME n) ps) (Conv (SOME (n', t')) vs) env =
((case lookup_alist_mod_env n envC of
      SOME (l, t)=>
        if same_tid t t' /\ (LENGTH ps = l) then
          if same_ctor (id_to_n n, t) (n',t') then
            pmatch_list envC s ps vs env
          else
            No_match
        else
          Match_type_error
    | _ => Match_type_error
  )))
/\
(pmatch envC s (Pcon NONE ps) (Conv NONE vs) env =
(if LENGTH ps = LENGTH vs then
    pmatch_list envC s ps vs env
  else
    Match_type_error))
/\
(pmatch envC s (Pref p) (Loc lnum) env =
((case store_lookup lnum s of
      SOME (Refv v) => pmatch envC s p v env
    | _ => Match_type_error
  )))
/\
(pmatch envC _ _ _ env = Match_type_error)
/\
(pmatch_list envC s [] [] env = (Match env))
/\
(pmatch_list envC s (p::ps) (v::vs) env =
((case pmatch envC s p v env of
      No_match => No_match
    | Match_type_error => Match_type_error
    | Match env' => pmatch_list envC s ps vs env'
  )))
/\
(pmatch_list envC s _ _ env = Match_type_error)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_size p
                                        | INR (a,x,ps,y,z) => pats_size ps)` >>
  srw_tac [ARITH_ss] [terminationTheory.size_abbrevs, astTheory.pat_size_def]);

val (evaluate_rules,evaluate_ind,evaluate_cases) = Hol_reln`
  (∀ck env s l.
  evaluate ck (env:all_env) (s:modSem$v count_store_trace) ((Lit l):modLang$exp) (s, Rval ((Litv l):modSem$v)))

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

/\ (! ck env cn es vs s s' v.
(do_con_check (all_env_to_cenv env) cn (LENGTH es) /\
(build_conv (all_env_to_cenv env) cn (REVERSE vs) = SOME v) /\
evaluate_list ck env s (REVERSE es) (s', Rval vs))
==>
evaluate ck env s (Con cn es) (s', Rval v))

/\ (! ck env cn es err s s'.
(do_con_check (all_env_to_cenv env) cn (LENGTH es) /\
evaluate_list ck env s (REVERSE es) (s', Rerr err))
==>
evaluate ck env s (Con cn es) (s', Rerr err))

/\ (! ck env n v s.
(ALOOKUP (all_env_to_env env) n = SOME v)
==>
evaluate ck env s (Var_local n) (s, Rval v))

/\ (! ck env n v s.
((LENGTH (all_env_to_genv env) > n) /\
(EL n (all_env_to_genv env) = SOME v))
==>
evaluate ck env s (Var_global n) (s, Rval v))

/\ (! ck env n e s.
evaluate ck env s (Fun n e) (s, Rval (Closure (all_env_to_cenv env, all_env_to_env env) n e)))

/\ (! ck env es vs env' e bv s1 s2 t2 count.
(evaluate_list ck env s1 (REVERSE es) ((count,s2,t2), Rval vs) /\
(do_opapp (all_env_to_genv env) (REVERSE vs) = SOME (env', e)) /\
(ck ==> ~ (count =( 0))) /\
evaluate ck env' ((if ck then count -  1 else count),s2,t2) e bv)
==>
evaluate ck env s1 (App Opapp es) bv)

/\ (! ck env es vs env' e s1 s2 count t2.
(evaluate_list ck env s1 (REVERSE es) ((count,s2,t2), Rval vs) /\
(do_opapp (all_env_to_genv env) (REVERSE vs) = SOME (env', e)) /\
(count = 0) /\
ck)
==>
evaluate ck env s1 (App Opapp es) (( 0,s2,t2), Rerr (Rabort Rtimeout_error)))

/\ (! ck env op es vs res s1 s2 s3 t2 t3 count.
(evaluate_list ck env s1 (REVERSE es) ((count,s2,t2), Rval vs) /\
(do_app (s2,t2) op (REVERSE vs) = SOME ((s3,t3), res)) /\
(op <> Opapp))
==>
evaluate ck env s1 (App op es) ((count,s3,t3), res))

/\ (! ck env op es err s1 s2.
(evaluate_list ck env s1 (REVERSE es) (s2, Rerr err))
==>
evaluate ck env s1 (App op es) (s2, Rerr err))

/\ (! ck env e1 e2 e3 v e s1 s2 res.
(evaluate ck env s1 e1 (s2, Rval v)) /\
(do_if v e2 e3 = SOME e) /\
(evaluate ck env s2 e res)
==>
evaluate ck env s1 (If e1 e2 e3) res)

/\ (! ck env e1 e2 e3 s2 err.
(evaluate ck env s1 e1 (s2, Rerr err))
==>
evaluate ck env s1 (If e1 e2 e3) (s2, Rerr err))

/\ (! ck env e pes v bv s1 s2.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_match ck env s2 v pes (Conv (SOME ("Bind", TypeExn (Short "Bind"))) []) bv)
==>
evaluate ck env s1 (Mat e pes) bv)

/\ (! ck env e pes err s s'.
(evaluate ck env s e (s', Rerr err))
==>
evaluate ck env s (Mat e pes) (s', Rerr err))

/\ (! ck genv cenv env n e1 e2 v bv s1 s2.
(evaluate ck (genv,cenv,env) s1 e1 (s2, Rval v) /\
evaluate ck (genv,cenv,opt_bind n v env) s2 e2 bv)
==>
evaluate ck (genv,cenv,env) s1 (Let n e1 e2) bv)

/\ (! ck env n e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Let n e1 e2) (s', Rerr err))

/\ (! ck genv cenv env funs e bv s.
(ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) /\
evaluate ck (genv,cenv,build_rec_env funs (cenv,env) env) s e bv)
==>
evaluate ck (genv,cenv,env) s (Letrec funs e) bv)

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

/\ (! ck genv cenv env env' v p pes e bv err_v s t count.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch cenv s p v env = Match env') /\
evaluate ck (genv,cenv,env') (count,s,t) e bv)
==>
evaluate_match ck (genv,cenv,env) (count,s,t) v ((p,e)::pes) err_v bv)

/\ (! ck genv cenv env v p e pes bv s t count err_v.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch cenv s p v env = No_match) /\
evaluate_match ck (genv,cenv,env) (count,s,t) v pes err_v bv)
==>
evaluate_match ck (genv,cenv,env) (count,s,t) v ((p,e)::pes) err_v bv)`;

val (evaluate_dec_rules,evaluate_dec_ind,evaluate_dec_cases) = Hol_reln ` (! ck genv cenv n e vs s1 s2 tdecs.
(evaluate ck (genv,cenv,[]) s1 e (s2, Rval (Conv NONE vs)) /\
(LENGTH vs = n))
==>
evaluate_dec ck genv cenv (s1,tdecs) (Dlet n e) ((s2,tdecs), Rval ([], vs)))

/\ (! ck genv cenv n e err s s' tdecs.
(evaluate ck (genv,cenv,[]) s e (s', Rerr err))
==>
evaluate_dec ck genv cenv (s,tdecs) (Dlet n e) ((s',tdecs), Rerr err))

/\ (! ck genv cenv funs s.
T
==>
evaluate_dec ck genv cenv s (Dletrec funs) (s, Rval ([], MAP (\ (f,x,e) .  Closure (cenv,[]) x e) funs)))

/\ (! ck mn genv cenv tds s tdecs new_tdecs.
(check_dup_ctors tds /\
(new_tdecs = type_defs_to_new_tdecs mn tds) /\
DISJOINT new_tdecs tdecs /\
ALL_DISTINCT (MAP (\ (tvs,tn,ctors) .  tn) tds))
==>
evaluate_dec ck genv cenv (s,tdecs) (Dtype mn tds) ((s,(new_tdecs UNION tdecs)), Rval (build_tdefs mn tds, [])))

/\ (! ck mn genv cenv cn ts s tdecs.
(~ (TypeExn (mk_id mn cn) IN tdecs))
==>
evaluate_dec ck genv cenv (s,tdecs) (Dexn mn cn ts) ((s, ({TypeExn (mk_id mn cn)} UNION tdecs)), Rval ([(cn, (LENGTH ts, TypeExn (mk_id mn cn)))], [])))`;

val (evaluate_decs_rules,evaluate_decs_ind,evaluate_decs_cases) = Hol_reln ` (! ck genv cenv s.
evaluate_decs ck genv cenv s [] (s, [], [], NONE))

/\ (! ck s1 s2 genv cenv d ds e.
(evaluate_dec ck genv cenv s1 d (s2, Rerr e))
==>
evaluate_decs ck genv cenv s1 (d::ds) (s2, [], [], SOME e))

/\ (! ck s1 s2 s3 genv cenv d ds new_tds' new_tds new_env new_env' r.
(evaluate_dec ck genv cenv s1 d (s2, Rval (new_tds,new_env)) /\
evaluate_decs ck (genv ++ MAP SOME new_env) (merge_alist_mod_env ([],new_tds) cenv) s2 ds (s3, new_tds', new_env', r))
==>
evaluate_decs ck genv cenv s1 (d::ds) (s3, (new_tds' ++ new_tds), (new_env ++ new_env'), r))`;

val mod_cenv_def = Define `
 (mod_cenv (mn:modN option) (cenv:flat_envC) =  
((case mn of
      NONE => ([],cenv)
    | SOME mn => ([(mn,cenv)], [])
  )))`;

val update_mod_state_def = Define `
 (update_mod_state (mn:modN option) mods =  
((case mn of
      NONE => mods
    | SOME mn => {mn} UNION mods
  )))`;


val dec_to_dummy_env_def = Define `

(dec_to_dummy_env (modLang$Dlet n e) = n)
/\
(dec_to_dummy_env (Dletrec funs) = (LENGTH funs))
/\
(dec_to_dummy_env _ = 0)`;

val decs_to_dummy_env_def = Define `
(decs_to_dummy_env [] = 0)
/\
(decs_to_dummy_env (d::ds) = (decs_to_dummy_env ds + dec_to_dummy_env d))`;

val decs_to_types_def = Define `
 (decs_to_types ds =
(FLAT (MAP (λd.
        (case d of
            Dtype mn tds => MAP (λ(tvs,tn,ctors). tn) tds
          | _ => [] ))
     ds)))`;

val no_dup_types_def = Define `
 (no_dup_types ds =
(ALL_DISTINCT (decs_to_types ds)))`;

val prompt_mods_ok_def = Define `
 (prompt_mods_ok mn ds =
(((case mn of
       NONE => LENGTH ds < 2
     | SOME mn => T
   ))
  /\
  (EVERY (λd.
      (case d of
          Dtype mn' _ => mn' = mn
        | Dexn mn' _ _ => mn' = mn
        | _ => T
      ))
    ds)))`;


val (evaluate_decs_rules,evaluate_decs_ind,evaluate_decs_cases) = Hol_reln ` (! ck genv cenv s1 tdecs1 mods ds s2 tdecs2 cenv' env mn.
((! name. (mn = SOME name) ==> ~ (name IN mods)) /\
no_dup_types ds /\
prompt_mods_ok mn ds /\
evaluate_decs ck genv cenv (s1,tdecs1) ds ((s2,tdecs2),cenv',env,NONE))
==>
evaluate_prompt ck genv cenv (s1,tdecs1,mods) (Prompt mn ds) ((s2,tdecs2,update_mod_state mn mods), mod_cenv mn cenv', MAP SOME env, NONE))

/\ (! ck genv cenv s1 tdecs1 mods mn ds s2 tdecs2 cenv' env err.
((! name. (mn = SOME name) ==> ~ (name IN mods)) /\
no_dup_types ds /\
prompt_mods_ok mn ds /\
evaluate_decs ck genv cenv (s1,tdecs1) ds ((s2,tdecs2),cenv',env,SOME err))
==>
evaluate_prompt ck genv cenv (s1,tdecs1,mods) (Prompt mn ds)
                                                  ((s2,tdecs2,update_mod_state mn mods),
                                                   mod_cenv mn cenv',
 (MAP SOME env ++ GENLIST (K NONE) (decs_to_dummy_env ds - LENGTH env)), SOME err))`;

val (evaluate_prog_rules,evaluate_prog_ind,evaluate_prog_cases) = Hol_reln ` (! ck genv cenv s.
T
==>
evaluate_prog ck genv cenv s [] (s, ([],[]), [], NONE))

/\ (! ck genv cenv s1 prompt prompts s2 cenv2 env2 s3 cenv3 env3 r.
(evaluate_prompt ck genv cenv s1 prompt (s2, cenv2, env2, NONE) /\
evaluate_prog ck (genv++env2) (merge_alist_mod_env cenv2 cenv) s2 prompts (s3, cenv3, env3, r))
==>
evaluate_prog ck genv cenv s1 (prompt::prompts) (s3, merge_alist_mod_env cenv3 cenv2, (env2++env3), r))

/\ (! ck genv cenv s1 prompt prompts s2 cenv2 env2 err.
(evaluate_prompt ck genv cenv s1 prompt (s2, cenv2, env2, SOME err))
==>
evaluate_prog ck genv cenv s1 (prompt::prompts) (s2, cenv2, env2, SOME err))`;

val prog_to_mods_def = Define `
 (prog_to_mods prompts =
(FLAT (MAP (λprompt.
        (case prompt of
            Prompt (SOME mn) ds => [mn]
          | _ => [] ))
     prompts)))`;

val no_dup_mods_def = Define `
 (no_dup_mods prompts (_,_,mods) =
(ALL_DISTINCT (prog_to_mods prompts) /\
  DISJOINT (LIST_TO_SET (prog_to_mods prompts)) mods))`;

val prog_to_top_types_def = Define `
 (prog_to_top_types prompts =
(FLAT (MAP (λprompt.
        (case prompt of
            Prompt NONE ds => decs_to_types ds
          | _ => [] ))
     prompts)))`;

val no_dup_top_types_def = Define `
 (no_dup_top_types prompts (_, tids, _) =
(ALL_DISTINCT (prog_to_top_types prompts) /\
  DISJOINT (LIST_TO_SET (MAP (\ tn .  TypeId (Short tn)) (prog_to_top_types prompts))) tids))`;

val evaluate_whole_prog_def = Define `
 (evaluate_whole_prog ck genv cenv s1 prompts (s2, cenv2, env2, res) =
(if no_dup_mods prompts s1 /\ no_dup_top_types prompts s1 /\
     EVERY (λp.  (case p of Prompt mn ds => prompt_mods_ok mn ds )) prompts then
    evaluate_prog ck genv cenv s1 prompts (s2, cenv2, env2, res)
  else
    res = SOME (Rabort Rtype_error)))`;

val _ = export_theory()
