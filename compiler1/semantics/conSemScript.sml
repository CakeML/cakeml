open preamble bigStepTheory conLangTheory mod_to_conTheory

val _ = new_theory"conSem"

(* The values of conLang differ in that the closures do not contain a constructor
 * name environment.
 *
 * The semantics of conLang differ in that there is no lexical constructor name
 * environment. However, there is a mapping (exh_ctors_env) from types to the
 * (arity-indexed) tags of the constructors of that type. This is for use later
 * on in determining whether a pattern match is exhaustive.
 *)

val _ = Datatype`
 v =
  | Litv lit
  | Conv ((num # tid_or_exn) option) (v list)
  | Closure ((varN, v) alist) varN (conLang$exp)
  | Recclosure ((varN, v) alist) ((varN # varN # (conLang$exp)) list) varN
  | Loc num
  | Vectorv (v list)`;

val do_eq_def = tDefine"do_eq"`
  (do_eq ((Litv l1):conSem$v) ((Litv l2):conSem$v) =
   if lit_same_type l1 l2 then Eq_val (l1 = l2)
   else Eq_type_error)
  ∧
  (do_eq (Loc l1) (Loc l2) = Eq_val (l1 = l2))
  ∧
  (do_eq (Conv NONE vs1) (Conv NONE vs2) =
   if LENGTH vs1 = LENGTH vs2 then
     do_eq_list vs1 vs2
   else
     Eq_val F)
  ∧
  (do_eq (Conv (SOME (n1,t1)) vs1) (Conv (SOME (n2,t2)) vs2) =
   if (n1,t1) = (n2,t2) ∧ (LENGTH vs1 = LENGTH vs2) then
     do_eq_list vs1 vs2
   else
     (case (t1,t2) of
      | (TypeId s1,TypeId s2) =>
        if s1 = s2 then
          Eq_val F (* different constructors, same type *)
        else
          Eq_type_error (* type mismatch *)
      | (TypeExn s1, TypeExn s2) =>
        if s1 = s2 then
          (* same exception but different tags or arities *)
          Eq_type_error
        else if (n1 = n2) ∧ (LENGTH vs1 = LENGTH vs2) then
          (* different exceptions but same tag and arity *)
          Eq_type_error
        else
          Eq_val F
      | _ => (* type mismatch *) Eq_type_error))
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
                                        | INR (xs,ys) => v3_size xs)`);

val _ = temp_type_abbrev( "all_env" , ``:(exh_ctors_env # (conSem$v option) list # (varN, conSem$v) alist)``);

val _ = Define `
 (all_env_to_genv ((exh,genv,env):all_env) = genv)`;

val _ = Define `
 (all_env_to_env ((exh,genv,env):all_env) = env)`;

val _ = Define `
  build_rec_env funs cl_env add_to_env =
    FOLDR
      (λ(f,x,e) env'. (f, Recclosure cl_env funs f) :: env')
      add_to_env
      funs`;

val _ = Define `
 (do_opapp vs =
  (case vs of
   | [Closure env n e; v] =>
     SOME (((n,v)::env), e)
   | [Recclosure env funs n; v] =>
     if ALL_DISTINCT (MAP FST funs) then
       (case find_recfun n funs of
        | SOME (n,e) => SOME (((n,v)::build_rec_env funs env env), e)
        | NONE => NONE)
     else NONE
   | _ => NONE))`;

val _ = Define`
  exn_tag "Chr" = chr_tag ∧
  exn_tag "Div" = div_tag ∧
  exn_tag "Eq" = eq_tag ∧
  exn_tag "Subscript" = subscript_tag`

val _ = Define `
  prim_exn cn = (Conv (SOME (exn_tag cn, (TypeExn (Short cn)))) [])`;

val _ = Define `
  (v_to_list (Conv (SOME (tag, (TypeId (Short tn)))) []) =
   if (tag = nil_tag) ∧ (tn = "list") then
     SOME []
   else
     NONE)
  ∧
  (v_to_list (Conv (SOME (tag, (TypeId (Short tn)))) [v1;v2]) =
   if (tag = cons_tag)  ∧ (tn = "list") then
     (case v_to_list v2 of
      | SOME vs => SOME (v1::vs)
      | NONE => NONE)
   else
     NONE)
  ∧
  (v_to_list _ = NONE)`;

val _ = Define `
  (v_to_char_list (Conv (SOME (tag, (TypeId (Short tn)))) []) =
   if (tag = nil_tag) ∧ (tn = "list") then
     SOME []
   else
     NONE)
  ∧
  (v_to_char_list (Conv (SOME (tag, (TypeId (Short tn)))) [Litv (Char c);v]) =
   if (tag = cons_tag) ∧ (tn = "list") then
     (case v_to_char_list v of
      | SOME cs => SOME (c::cs)
      | NONE => NONE)
   else
     NONE)
  ∧
  (v_to_char_list _ = NONE)`;

val _ = Define`
  (char_list_to_v [] = (Conv (SOME (nil_tag, (TypeId (Short "list")))) []))
  ∧
  (char_list_to_v (c::cs) =
   Conv (SOME (cons_tag, (TypeId (Short "list")))) [Litv (Char c); char_list_to_v cs])`;

val _ = Define `
  Boolv b = (Conv (SOME ((if b then true_tag else false_tag), TypeId(Short"bool"))) [])`;

val do_app_def = Define `
  do_app (s,t) op (vs:conSem$v list) =
  case op of
  | Init_global_var _ => NONE
  | Op op => (* copied from modLangSemScript.sml *) (
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
  | _ => NONE
  )`;

val pmatch_def = tDefine"pmatch"`
  (pmatch exh s (Pvar x) v' env = (Match ((x,v')::env)))
  ∧
  (pmatch exh s (Plit l) (Litv l') env =
   if l = l' then
     Match env
   else if lit_same_type l l' then
     No_match
   else
     Match_type_error)
  ∧
  (pmatch exh s (Pcon (SOME (n, (TypeExn t))) ps) (Conv (SOME (n', (TypeExn t'))) vs) env =
   if (n = n') /\ (LENGTH ps = LENGTH vs) then
     if t = t' then
       pmatch_list exh s ps vs env
     else
       Match_type_error
   else if t = t' then
     Match_type_error
   else
     No_match)
  ∧
  (pmatch exh s (Pcon (SOME (n, (TypeId t))) ps) (Conv (SOME (n', (TypeId t'))) vs) env =
   if t = t' then
     (case FLOOKUP exh t of
      | NONE => Match_type_error
      | SOME m =>
        let a = (LENGTH ps) in
        (case lookup a m of
         | NONE => Match_type_error
         | SOME max =>
         if (n = n') /\ (a = LENGTH vs) then
           if n < max then
             pmatch_list exh s ps vs env
           else Match_type_error
         else
           (case lookup (LENGTH vs) m of
            | NONE => Match_type_error
            | SOME max' =>
              if (n < max) /\ (n' < max') then
                No_match
              else Match_type_error)))
   else Match_type_error)
  ∧
  (pmatch exh s (Pcon NONE ps) (Conv NONE vs) env =
   if LENGTH ps = LENGTH vs then
     pmatch_list exh s ps vs env
   else
     Match_type_error)
  ∧
  (pmatch exh s (Pref p) (Loc lnum) env =
   (case store_lookup lnum s of
    | SOME (Refv v) => pmatch exh s p v env
    | _ => Match_type_error))
  ∧
  (pmatch exh _ _ _ env = Match_type_error)
  ∧
  (pmatch_list exh s [] [] env = Match env)
  ∧
  (pmatch_list exh s (p::ps) (v::vs) env =
   (case pmatch exh s p v env of
    | No_match => No_match
    | Match_type_error => Match_type_error
    | Match env' => pmatch_list exh s ps vs env'))
  ∧
  (pmatch_list exh s _ _ env = Match_type_error)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_size p
                                         | INR (a,x,ps,y,z) => pat1_size ps)` >>
   srw_tac [ARITH_ss] [pat_size_def]);

val pat_bindings_def = Define`
  (pat_bindings (conLang$Pvar n) already_bound =
   n::already_bound)
  ∧
  (pat_bindings (Plit l) already_bound =
   already_bound)
  ∧
  (pat_bindings (Pcon _ ps) already_bound =
   pats_bindings ps already_bound)
  ∧
  (pat_bindings (Pref p) already_bound =
   pat_bindings p already_bound)
  ∧
  (pats_bindings [] already_bound =
   already_bound)
  ∧
  (pats_bindings (p::ps) already_bound =
   pats_bindings ps (pat_bindings p already_bound))`;

val _ = Hol_reln ` (! ck env l s.
  evaluate ck (env:all_env) (s:conSem$v count_store_trace) ((Lit l):conLang$exp) (s, Rval ((Litv l):conSem$v)))

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
evaluate ck env s (Fun n e) (s, Rval (Closure (all_env_to_env env) n e)))

/\ (! ck exh genv env es vs env' e bv s1 s2 t2 count.
(evaluate_list ck (exh,genv,env) s1 (REVERSE es) ((count,s2,t2), Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env', e)) /\
(ck ==> ~ (count =( 0))) /\
evaluate ck (exh,genv,env') ((if ck then count -  1 else count),s2,t2) e bv)
==>
evaluate ck (exh,genv,env) s1 (App (Op Opapp) es) bv)

/\ (! ck env es vs env' e s1 s2 t2 count.
(evaluate_list ck env s1 (REVERSE es) ((count,s2,t2), Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env', e)) /\
(count = 0) /\
ck)
==>
evaluate ck env s1 (App (Op Opapp) es) (( 0,s2,t2), Rerr (Rabort Rtimeout_error)))

/\ (! ck env op es vs res s1 s2 s3 t2 t3 count.
(evaluate_list ck env s1 (REVERSE es) ((count,s2,t2), Rval vs) /\
(do_app (s2,t2) op (REVERSE vs) = SOME ((s3,t3), res)) /\
(op <> Op Opapp))
==>
evaluate ck env s1 (App op es) ((count,s3,t3), res))

/\ (! ck env op es err s1 s2.
(evaluate_list ck env s1 (REVERSE es) (s2, Rerr err))
==>
evaluate ck env s1 (App op es) (s2, Rerr err))

/\ (! ck env e pes v bv s1 s2.
(evaluate ck env s1 e (s2, Rval v) /\
evaluate_match ck env s2 v pes (Conv (SOME (bind_tag,(TypeExn (Short "Bind")))) []) bv)
==>
evaluate ck env s1 (Mat e pes) bv)

/\ (! ck env e pes err s s'.
(evaluate ck env s e (s', Rerr err))
==>
evaluate ck env s (Mat e pes) (s', Rerr err))

/\ (! ck exh genv env n e1 e2 v bv s1 s2.
(evaluate ck (exh,genv,env) s1 e1 (s2, Rval v) /\
evaluate ck (exh,genv,opt_bind n v env) s2 e2 bv)
==>
evaluate ck (exh,genv,env) s1 (Let n e1 e2) bv)

/\ (! ck env n e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Let n e1 e2) (s', Rerr err))

/\ (! ck exh genv env funs e bv s.
(ALL_DISTINCT (MAP FST funs) /\
evaluate ck (exh,genv,build_rec_env funs env env) s e bv)
==>
evaluate ck (exh,genv,env) s (Letrec funs e) bv)

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
T
==>
evaluate_match ck env s v [] err_v (s, Rerr (Rraise err_v)))

/\ (! ck exh genv env env' v p pes e bv s t count err_v.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch exh s p v env = Match env') /\
evaluate ck (exh,genv,env') (count,s,t) e bv)
==>
evaluate_match ck (exh,genv,env) (count,s,t) v ((p,e)::pes) err_v bv)

/\ (! ck exh genv env v p e pes bv s t count err_v.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch exh s p v env = No_match) /\
evaluate_match ck (exh,genv,env) (count,s,t) v pes err_v bv)
==>
evaluate_match ck (exh,genv,env) (count,s,t) v ((p,e)::pes) err_v bv)`;

val _ = Hol_reln ` (! ck exh genv n e vs s1 s2.
(evaluate ck (exh,genv,[]) s1 e (s2, Rval (Conv NONE vs)) /\
(LENGTH vs = n))
==>
evaluate_dec ck exh genv s1 (Dlet n e) (s2, Rval vs))

/\ (! ck exh genv n e err s s'.
(evaluate ck (exh,genv,[]) s e (s', Rerr err))
==>
evaluate_dec ck exh genv s (Dlet n e) (s', Rerr err))

/\ (! ck exh genv funs s.
evaluate_dec ck exh genv s (Dletrec funs) (s, Rval (MAP (\ (f,x,e) .  Closure [] x e) funs)))`;

val _ = Hol_reln ` (! ck exh genv s.
evaluate_decs ck exh genv s [] (s, [], NONE))

/\ (! ck exh s1 s2 genv d ds e.
(evaluate_dec ck exh genv s1 d (s2, Rerr e))
==>
evaluate_decs ck exh genv s1 (d::ds) (s2, [], SOME e))

/\ (! ck exh s1 s2 s3 genv d ds new_env new_env' r.
(evaluate_dec ck exh genv s1 d (s2, Rval new_env) /\
evaluate_decs ck exh (genv ++ MAP SOME new_env) s2 ds (s3, new_env', r))
==>
evaluate_decs ck exh genv s1 (d::ds) (s3, (new_env ++ new_env'), r))`;

val _ = Hol_reln ` (! ck exh genv s1 ds s2 env.
(evaluate_decs ck exh genv s1 ds (s2,env,NONE))
==>
evaluate_prompt ck exh genv s1 (Prompt ds) (s2, MAP SOME env, NONE))

/\ (! ck exh genv s1 ds s2 env err.
(evaluate_decs ck exh genv s1 ds (s2,env,SOME err))
==>
evaluate_prompt ck exh genv s1 (Prompt ds) (s2,
 (MAP SOME env ++ GENLIST (K NONE) (num_defs ds - LENGTH env)),
  SOME err))`;

val _ = Hol_reln ` (! ck exh genv s.
evaluate_prog ck exh genv s [] (s, [], NONE))

/\ (! ck exh genv s1 prompt prompts s2 env2 s3 env3 r.
(evaluate_prompt ck exh genv s1 prompt (s2, env2, NONE) /\
evaluate_prog ck exh (genv++env2) s2 prompts (s3, env3, r))
==>
evaluate_prog ck exh genv s1 (prompt::prompts) (s3, (env2++env3), r))

/\ (! ck exh genv s1 prompt prompts s2 env2 err.
(evaluate_prompt ck exh genv s1 prompt (s2, env2, SOME err))
==>
evaluate_prog ck exh genv s1 (prompt::prompts) (s2, env2, SOME err))`;

val _ = export_theory()
