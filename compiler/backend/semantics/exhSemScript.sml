open preamble bigStepTheory exhLangTheory dec_to_exhTheory

val _ = new_theory"exhSem"

(*
 * The values of exhLang differ from decLang in the same way as the
 * expressions.
 *
 * The semantics of exhLang differ in that pattern matches that fall off the end
 * raise a type error, and the mapping from types to constructor tags is
 * ommitted.
 *)

val _ = Datatype`
  v =
   | Litv lit
   | Conv num (v list)
   | Closure ((varN, v) alist) varN exhLang$exp
   | Recclosure ((varN, v) alist) ((varN # varN # exhLang$exp) list) varN
   | Loc num
   | Vectorv (v list)`;

val pmatch_def = tDefine"pmatch"`
  (pmatch s (Pvar x) v' env = (Match ((x,v')::env)))
  ∧
  (pmatch s (Plit l) (Litv l') env =
   if l = l' then
     Match env
   else if lit_same_type l l' then
     No_match
   else
     Match_type_error)
  ∧
  (pmatch s (Pcon n ps) (Conv n' vs) env =
   if (n = n') ∧ (LENGTH ps = LENGTH vs) then
     pmatch_list s ps vs env
   else
     No_match)
  ∧
  (pmatch s (Pref p) (Loc lnum) env =
   (case store_lookup lnum s of
    | SOME (Refv v) => pmatch s p v env
    | _ => Match_type_error))
  ∧
  (pmatch _ _ _ env = Match_type_error)
  ∧
  (pmatch_list s [] [] env = Match env)
  ∧
  (pmatch_list s (p::ps) (v::vs) env =
   (case pmatch s p v env of
    | No_match => No_match
    | Match_type_error => Match_type_error
    | Match env' => pmatch_list s ps vs env'))
  ∧
  (pmatch_list s _ _ env = Match_type_error)`
  (WF_REL_TAC `inv_image $< (\x. case x of INL (x,p,y,z) => pat_size p
                                         | INR (x,ps,y,z) => pat1_size ps)` >>
   srw_tac [ARITH_ss] [pat_size_def]);

val _ = Define `
  build_rec_env funs cl_env add_to_env =
    FOLDR
      (λ(f,x,e) env'. (f,Recclosure cl_env funs f) :: env')
      add_to_env funs`;

val do_eq_def = tDefine"do_eq"`
  (do_eq ((Litv l1):exhSem$v) ((Litv l2):exhSem$v) =
   if lit_same_type l1 l2 then Eq_val (l1 = l2)
   else Eq_type_error)
  ∧
  (do_eq (Loc l1) (Loc l2) = Eq_val (l1 = l2))
  ∧
  (do_eq (Conv tag1 vs1) (Conv tag2 vs2) =
   if tag1 = tag2 ∧ LENGTH vs1 = LENGTH vs2 then
     do_eq_list vs1 vs2
   else
     Eq_val F)
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

val _ = Define `
  prim_exn tag = Conv tag []`;

val _ = Define `
  (v_to_list (Conv tag []) =
   if tag = nil_tag then
     SOME []
   else
     NONE)
  ∧
  (v_to_list (Conv tag [v1;v2]) =
   if tag = cons_tag then
     (case v_to_list v2 of
      | SOME vs => SOME (v1::vs)
      | NONE => NONE)
   else
     NONE)
  ∧
  (v_to_list _ = NONE)`;

val _ = Define `
  (v_to_char_list (Conv tag []) =
   if tag = nil_tag then
     SOME []
   else
     NONE)
  ∧
  (v_to_char_list (Conv tag [Litv (Char c);v]) =
   if tag = cons_tag then
     (case v_to_char_list v of
      | SOME cs => SOME (c::cs)
      | NONE => NONE)
   else
     NONE)
  ∧
  (v_to_char_list _ = NONE)`;

val _ = Define`
  (char_list_to_v [] = (Conv nil_tag []))
  ∧
  (char_list_to_v (c::cs) =
   Conv cons_tag [Litv (Char c); char_list_to_v cs])`;

val _ = Define `
  Boolv b = Conv (if b then true_tag else false_tag) []`;

val _ = type_abbrev("count_store_genv", ``:(num # 'v store # 'ffi ffi_state) # ('v option) list``);

val do_app_def = Define `
  do_app (((cnt,s,t),g):(('ffi,exhSem$v) count_store_genv)) op (vs:exhSem$v list) =
  case op of
  | Init_global_var idx =>
    (case vs of
     | [v] =>
         if idx < LENGTH g then
           (case EL idx g of
            | NONE => SOME (((cnt,s,t), LUPDATE (SOME v) idx g), (Rval (Conv tuple_tag [])))
            | SOME x => NONE)
         else NONE
     | _ => NONE)
  | Op op => (* copied from conSemScript.sml,
                modifications:
                 (s,t) -> ((cnt,s,t),g)
                 (s, t) -> ((cnt,s,t),g)
                 (st,t) -> ((cnt,st,t),g)
                 (s',t) -> ((cnt,s',t),g)
                 (s', t') -> ((cnt,s',t'),g)
                 (* TODO: make the above consistent in earlier definitions of do_app *)
                 prim_exn "Foo" -> prim_exn foo_tag
                 Conv NONE -> Conv tuple_tag
              *)
  (
  case (op, vs) of
  | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    if ((op = Divide) ∨ (op = Modulo)) ∧ (n2 = 0) then
      SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn div_tag)))
    else
      SOME (((cnt,s,t),g), Rval (Litv (IntLit (opn_lookup op n1 n2))))
  | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    SOME (((cnt,s,t),g), Rval (Boolv (opb_lookup op n1 n2)))
  | (Equality, [v1; v2]) =>
    (case do_eq v1 v2 of
     | Eq_type_error => NONE
     | Eq_closure => SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn eq_tag)))
     | Eq_val b => SOME (((cnt,s,t),g), Rval (Boolv b)))
  | (Opassign, [Loc lnum; v]) =>
    (case store_assign lnum (Refv v) s of
     | SOME st => SOME (((cnt,st,t),g), Rval (Conv tuple_tag []))
     | NONE => NONE)
  | (Opref, [v]) =>
    let (s',n) = (store_alloc (Refv v) s) in
      SOME (((cnt,s',t),g), Rval (Loc n))
  | (Opderef, [Loc n]) =>
    (case store_lookup n s of
     | SOME (Refv v) => SOME (((cnt,s,t),g),Rval v)
     | _ => NONE)
  | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
    if n < 0 then
      SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
    else
      let (s',lnum) =
        store_alloc (W8array (REPLICATE (Num (ABS ( n))) w)) s
      in
        SOME (((cnt,s',t),g), Rval (Loc lnum))
  | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s of
     | SOME (W8array ws) =>
       if i < 0 then
         SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
           else
             SOME (((cnt,s,t),g), Rval (Litv (Word8 (EL n ws))))
     | _ => NONE)
  | (Aw8length, [Loc n]) =>
    (case store_lookup n s of
     | SOME (W8array ws) =>
       SOME (((cnt,s,t),g),Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
     | _ => NONE)
  | (Aw8update, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
    (case store_lookup lnum s of
     | SOME (W8array ws) =>
       if i < 0 then
         SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
           else
             (case store_assign lnum (W8array (LUPDATE w n ws)) s of
              | NONE => NONE
              | SOME s' => SOME (((cnt,s',t),g), Rval (Conv tuple_tag [])))
     | _ => NONE)
  | (Ord, [Litv (Char c)]) =>
    SOME (((cnt,s,t),g), Rval (Litv(IntLit(int_of_num(ORD c)))))
  | (Chr, [Litv (IntLit i)]) =>
    SOME (((cnt,s,t),g),
          if (i < 0) ∨ (i > 255) then
            Rerr (Rraise (prim_exn chr_tag))
          else
            Rval (Litv(Char(CHR(Num(ABS i))))))
  | (Chopb op, [Litv (Char c1); Litv (Char c2)]) =>
    SOME (((cnt,s,t),g), Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
  | (Implode, [v]) =>
    (case v_to_char_list v of
     | SOME ls =>
       SOME (((cnt,s,t),g), Rval (Litv (StrLit (IMPLODE ls))))
     | NONE => NONE)
  | (Explode, [Litv (StrLit str)]) =>
    SOME (((cnt,s,t),g), Rval (char_list_to_v (EXPLODE str)))
  | (Strlen, [Litv (StrLit str)]) =>
    SOME (((cnt,s,t),g), Rval (Litv(IntLit(int_of_num(STRLEN str)))))
  | (VfromList, [v]) =>
    (case v_to_list v of
     | SOME vs =>
       SOME (((cnt,s,t),g), Rval (Vectorv vs))
     | NONE => NONE)
  | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
    if i < 0 then
      SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
    else
      let n = (Num (ABS i)) in
        if n >= LENGTH vs then
          SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
        else
          SOME (((cnt,s,t),g), Rval (EL n vs))
  | (Vlength, [Vectorv vs]) =>
    SOME (((cnt,s,t),g), Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
  | (Aalloc, [Litv (IntLit n); v]) =>
    if n < 0 then
      SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
    else
      let (s',lnum) =
        store_alloc (Varray (REPLICATE (Num (ABS n)) v)) s
      in
        SOME (((cnt,s',t),g), Rval (Loc lnum))
  | (Asub, [Loc lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s of
     | SOME (Varray vs) =>
     if i < 0 then
       SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
         else
           SOME (((cnt,s,t),g), Rval (EL n vs))
     | _ => NONE)
    | (Alength, [Loc n]) =>
      (case store_lookup n s of
       | SOME (Varray ws) =>
         SOME (((cnt,s,t),g),Rval (Litv (IntLit(int_of_num(LENGTH ws)))))
       | _ => NONE)
  | (Aupdate, [Loc lnum; Litv (IntLit i); v]) =>
    (case store_lookup lnum s of
     | SOME (Varray vs) =>
     if i < 0 then
       SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           SOME (((cnt,s,t),g), Rerr (Rraise (prim_exn subscript_tag)))
         else
           (case store_assign lnum (Varray (LUPDATE v n vs)) s of
            | NONE => NONE
            | SOME s' => SOME (((cnt,s',t),g), Rval (Conv tuple_tag [])))
     | _ => NONE)
  | (FFI n, [Loc lnum]) =>
    (case store_lookup lnum s of
     | SOME (W8array ws) =>
       (case call_FFI t n ws of
        | (t', ws') =>
          (case store_assign lnum (W8array ws') s of
           | SOME s' => SOME (((cnt,s',t'),g), Rval (Conv tuple_tag []))
           | NONE => NONE))
     | _ => NONE)
  | _ => NONE
  )`;

val pat_bindings_def = Define`
  (pat_bindings (Pvar n) already_bound =
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
evaluate ck (env:(varN,exhSem$v)alist) (s:('ffi,exhSem$v) count_store_genv) ((Lit l):exhLang$exp) (s, Rval (Litv l)))

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
evaluate_match ck env s2 v pes bv)
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
(ALOOKUP env n = SOME v)
==>
evaluate ck env s (Var_local n) (s, Rval v))

/\ (! ck env n v s genv.
((LENGTH genv > n) /\
(EL n genv = SOME v))
==>
evaluate ck env (s,genv) (Var_global n) ((s,genv), Rval v))

/\ (! ck env n e s.
evaluate ck env s (Fun n e) (s, Rval (Closure env n e)))

/\ (! ck genv env es vs env' e bv s1 s2 t2 count genv'.
(evaluate_list ck env (s1,genv) (REVERSE es) (((count,s2,t2),genv'), Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env', e)) /\
(ck ==> ~ (count =( 0))) /\
evaluate ck env' (((if ck then count -  1 else count),s2,t2),genv') e bv)
==>
evaluate ck env (s1,genv) (App (Op Opapp) es) bv)

/\ (! ck env es vs env' e s1 s2 t2 count genv.
(evaluate_list ck env s1 (REVERSE es) (((count,s2,t2), genv), Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env', e)) /\
(count = 0) /\
ck)
==>
evaluate ck env s1 (App (Op Opapp) es) ((( 0,s2,t2),genv), Rerr (Rabort Rtimeout_error)))

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
evaluate_match ck env s2 v pes bv)
==>
evaluate ck env s1 (Mat e pes) bv)

/\ (! ck env e pes err s s'.
(evaluate ck env s e (s', Rerr err))
==>
evaluate ck env s (Mat e pes) (s', Rerr err))

/\ (! ck env n e1 e2 v bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
evaluate ck (opt_bind n v env) s2 e2 bv)
==>
evaluate ck env s1 (Let n e1 e2) bv)

/\ (! ck env n e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Let n e1 e2) (s', Rerr err))

/\ (! ck env funs e bv s.
(ALL_DISTINCT (MAP FST funs) /\
evaluate ck (build_rec_env funs env env) s e bv)
==>
evaluate ck env s (Letrec funs e) bv)

/\ (! ck env n s genv.
evaluate ck env (s,genv) (Extend_global n) ((s,(genv++GENLIST (K NONE) n)), Rval (Conv tuple_tag [])))

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

/\ (! ck env env' v p pes e bv s t count genv.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch s p v env = Match env') /\
evaluate ck env' ((count,s,t),genv) e bv)
==>
evaluate_match ck env ((count,s,t),genv) v ((p,e)::pes) bv)

/\ (! ck genv env v p e pes bv s t count.
(ALL_DISTINCT (pat_bindings p []) /\
(pmatch s p v env = No_match) /\
evaluate_match ck env ((count,s,t),genv) v pes bv)
==>
evaluate_match ck env ((count,s,t),genv) v ((p,e)::pes) bv)`;

val _ = export_theory()
