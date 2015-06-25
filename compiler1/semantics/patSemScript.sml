open preamble bigStepTheory dec_to_exhTheory patLangTheory

val _ = new_theory"patSem"

(*
 * The values and semantics of patLang are the same as exhLang, modulo the
 * changes to expressions.
 *)

val _ = Datatype`
  v =
   | Litv lit
   | Conv num (v list)
   | Closure (v list) patLang$exp
   | Recclosure (v list) (patLang$exp list) num
   | Loc num
   | Vectorv (v list)`;

val _ = Define `
  build_rec_env funs cl_env =
  GENLIST (Recclosure cl_env funs) (LENGTH funs)`;

val _ = Define `
  do_opapp vs =
  (case vs of
   | [Closure env e; v] => SOME ((v::env), e)
   | [Recclosure env funs n; v] =>
     if n < LENGTH funs then
       SOME ((v::((build_rec_env funs env)++env)), EL n funs)
     else NONE
   | _ => NONE)`;

val do_eq_def = tDefine"do_eq"`
  (do_eq ((Litv l1):patSem$v) ((Litv l2):patSem$v) =
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
  (do_eq (Closure _ _) (Closure _ _) = Eq_closure)
  ∧
  (do_eq (Closure _ _) (Recclosure _ _ _) = Eq_closure)
  ∧
  (do_eq (Recclosure _ _ _) (Closure _ _) = Eq_closure)
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
                                        | INR (xs,ys) => v1_size xs)`);

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

val _ = Define `
 (do_app ((cnt,s,t),genv) op vs =
((case (op,vs) of
      (Op (Op (Opn op)), [Litv (IntLit n1); Litv (IntLit n2)]) =>
        if ((op = Divide) \/ (op = Modulo)) /\ (n2 =( 0 : int)) then
          SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn div_tag)))
        else
          SOME (((cnt,s,t),genv), Rval (Litv (IntLit (opn_lookup op n1 n2))))
    | (Op (Op (Opb op)), [Litv (IntLit n1); Litv (IntLit n2)]) =>
        SOME (((cnt,s,t),genv), Rval (Boolv (opb_lookup op n1 n2)))
    | (Op (Op Equality), [v1; v2]) =>
        (case do_eq v1 v2 of
            Eq_type_error => NONE
          | Eq_closure => SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn eq_tag)))
          | Eq_val b => SOME (((cnt,s,t),genv), Rval(Boolv b))
        )
    | (Op (Op Opassign), [Loc lnum; v]) =>
        (case store_assign lnum (Refv v) s of
          SOME st => SOME (((cnt,st,t),genv), Rval (Conv tuple_tag []))
        | NONE => NONE
        )
    | (Op (Op Opderef), [Loc n]) =>
        (case store_lookup n s of
            SOME (Refv v) => SOME (((cnt,s,t),genv),Rval v)
          | _ => NONE
        )
    | (Op (Op Opref), [v]) =>
        let (s',n) = (store_alloc (Refv v) s) in
          SOME (((cnt,s',t),genv), Rval (Loc n))
    | (Op (Init_global_var idx), [v]) =>
        if idx < LENGTH genv then
          (case EL idx genv of
              NONE => SOME (((cnt,s,t), LUPDATE (SOME v) idx genv), Rval (Conv tuple_tag []))
            | SOME _ => NONE
          )
        else
          NONE
    | (Op (Op Aw8alloc), [Litv (IntLit n); Litv (Word8 w)]) =>
        if n <( 0 : int) then
          SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
        else
          let (st,lnum) =
(store_alloc (W8array (REPLICATE (Num (ABS ( n))) w)) s)
          in
            SOME (((cnt,st,t),genv), Rval (Loc lnum))
    | (Op (Op Aw8sub), [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
              else
                let n = (Num (ABS ( i))) in
                  if n >= LENGTH ws then
                    SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
                  else
                    SOME (((cnt,s,t),genv), Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Op (Op Aw8length), [Loc n]) =>
        (case store_lookup n s of
            SOME (W8array ws) =>
              SOME (((cnt,s,t),genv),Rval (Litv (IntLit (int_of_num (LENGTH ws)))))
          | _ => NONE
        )
    | (Op (Op Aw8update), [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
            else
              let n = (Num (ABS ( i))) in
                if n >= LENGTH ws then
                  SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME st => SOME (((cnt,st,t),genv), Rval (Conv tuple_tag []))
                  )
        | _ => NONE
        )
    | (Op (Op Ord), [Litv (Char c)]) =>
          SOME (((cnt,s,t),genv), Rval (Litv(IntLit(int_of_num(ORD c)))))
    | (Op (Op Chr), [Litv (IntLit i)]) =>
        SOME (((cnt,s,t),genv),
(if (i <( 0 : int)) \/ (i >( 255 : int)) then
            Rerr (Rraise (prim_exn chr_tag))
          else
            Rval (Litv(Char(CHR(Num (ABS ( i))))))))
    | (Op (Op (Chopb op)), [Litv (Char c1); Litv (Char c2)]) =>
        SOME (((cnt,s,t),genv), Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
    | (Op (Op Implode), [v]) =>
          (case v_to_char_list v of
            SOME ls =>
              SOME (((cnt,s,t),genv), Rval (Litv (StrLit (IMPLODE ls))))
          | NONE => NONE
          )
    | (Op (Op Explode), [Litv (StrLit str)]) =>
        SOME (((cnt,s,t),genv), Rval (char_list_to_v (EXPLODE str)))
    | (Op (Op Strlen), [Litv (StrLit str)]) =>
        SOME (((cnt,s,t),genv), Rval (Litv(IntLit(int_of_num(STRLEN str)))))
    | (Op (Op VfromList), [v]) =>
          (case v_to_list v of
              SOME vs =>
                SOME (((cnt,s,t),genv), Rval (Vectorv vs))
            | NONE => NONE
          )
    | (Op (Op Vsub), [Vectorv vs; Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
        else
          let n = (Num (ABS ( i))) in
            if n >= LENGTH vs then
              SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
            else
              SOME (((cnt,s,t),genv), Rval (EL n vs))
    | (Op (Op Vlength), [Vectorv vs]) =>
        SOME (((cnt,s,t),genv), Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
    | (Op (Op Aalloc), [Litv (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
        else
          let (s',lnum) =
(store_alloc (Varray (REPLICATE (Num (ABS ( n))) v)) s)
          in
            SOME (((cnt,s',t),genv), Rval (Loc lnum))
    | (Op (Op Asub), [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
              else
                let n = (Num (ABS ( i))) in
                  if n >= LENGTH vs then
                    SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
                  else
                    SOME (((cnt,s,t),genv), Rval (EL n vs))
          | _ => NONE
        )
    | (Op (Op Alength), [Loc n]) =>
        (case store_lookup n s of
            SOME (Varray ws) =>
              SOME (((cnt,s,t),genv),Rval (Litv (IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Op (Op Aupdate), [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
            else
              let n = (Num (ABS ( i))) in
                if n >= LENGTH vs then
                  SOME (((cnt,s,t),genv), Rerr (Rraise (prim_exn subscript_tag)))
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME (((cnt,s',t),genv), Rval (Conv tuple_tag []))
                  )
        | _ => NONE
      )
    | (Op (Op (FFI n)), [Loc lnum]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            (case call_FFI n ws t of
              (ws', t') =>
               (case store_assign lnum (W8array ws') s of
                 SOME s' => SOME (((cnt,s', t'),genv), Rval (Conv tuple_tag []))
               | NONE => NONE))
        | _ => NONE)
    | (Tag_eq n l, [Conv tag vs]) =>
        SOME (((cnt,s,t),genv), Rval (Boolv (tag = n ∧ LENGTH vs = l)))
    | (El n, [Conv _ vs]) =>
        if n < LENGTH vs then
          SOME (((cnt,s,t),genv), Rval (EL n vs))
        else
          NONE
    | _ => NONE
  )))`;

val _ = Define `
  do_if v e1 e2 =
    if v = Boolv T then SOME e1 else
    if v = Boolv F then SOME e2 else NONE`;

val _ = Hol_reln ` (! ck env l s.
evaluate ck (env:patSem$v list) (s:patSem$v count_store_genv) ((Lit l):patLang$exp) (s, Rval (Litv l)))

/\ (! ck env e s1 s2 v.
(evaluate ck s1 env e (s2, Rval v))
==>
evaluate ck s1 env (Raise e) (s2, Rerr (Rraise v)))

/\ (! ck env e s1 s2 err.
(evaluate ck s1 env e (s2, Rerr err))
==>
evaluate ck s1 env (Raise e) (s2, Rerr err))

/\ (! ck s1 s2 env e1 v e2.
(evaluate ck s1 env e1 (s2, Rval v))
==>
evaluate ck s1 env (Handle e1 e2) (s2, Rval v))

/\ (! ck s1 s2 env e1 e2 v bv.
(evaluate ck env s1 e1 (s2, Rerr (Rraise v)) /\
evaluate ck (v::env) s2 e2 bv)
==>
evaluate ck env s1 (Handle e1 e2) bv)

/\ (! ck s1 s2 env e1 e2 a.
(evaluate ck env s1 e1 (s2, Rerr (Rabort a)))
==>
evaluate ck env s1 (Handle e1 e2) (s2, Rerr (Rabort a)))

/\ (! ck env tag es vs s s'.
(evaluate_list ck env s (REVERSE es) (s', Rval vs))
==>
evaluate ck env s (Con tag es) (s', Rval (Conv tag (REVERSE vs))))

/\ (! ck env tag es err s s'.
(evaluate_list ck env s (REVERSE es) (s', Rerr err))
==>
evaluate ck env s (Con tag es) (s', Rerr err))

/\ (! ck env n s.
(LENGTH env > n)
==>
evaluate ck env s (Var_local n) (s, Rval (EL n env)))

/\ (! ck env n v s genv.
((LENGTH genv > n) /\
(EL n genv = SOME v))
==>
evaluate ck env (s,genv) (Var_global n) ((s,genv), Rval v))

/\ (! ck env e s.
T
==>
evaluate ck env s (Fun e) (s, Rval (Closure env e)))

/\ (! ck env s1 es count s2 t2 genv2 vs env2 e2 bv.
(evaluate_list ck env s1 (REVERSE es) (((count,s2,t2),genv2), Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env2, e2)) /\
(ck ==> ~ (count =( 0))) /\
evaluate ck env2 (((if ck then count -  1 else count),s2,t2),genv2) e2 bv)
==>
evaluate ck env s1 (App (Op (Op Opapp)) es) bv)

/\ (! ck env s1 es count s2 t2 genv2 vs env2 e2.
(evaluate_list ck env s1 (REVERSE es) (((count,s2,t2),genv2), Rval vs) /\
(do_opapp (REVERSE vs) = SOME (env2, e2)) /\
(count = 0) /\
ck)
==>
evaluate ck env s1 (App (Op (Op Opapp)) es) ((( 0,s2,t2),genv2), Rerr (Rabort Rtimeout_error)))

/\ (! ck env s1 op es s2 vs s3 res.
(evaluate_list ck env s1 (REVERSE es) (s2, Rval vs) /\
(do_app s2 op (REVERSE vs) = SOME (s3, res)) /\
(op <> Op (Op Opapp)))
==>
evaluate ck env s1 (App op es) (s3, res))

/\ (! ck env s1 op es s2 err.
(evaluate_list ck env s1 (REVERSE es) (s2, Rerr err))
==>
evaluate ck env s1 (App op es) (s2, Rerr err))

/\ (! ck env e1 e2 e3 v e' bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
(do_if v e2 e3 = SOME e') /\
evaluate ck env s2 e' bv)
==>
evaluate ck env s1 (If e1 e2 e3) bv)

/\ (! ck env e1 e2 e3 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (If e1 e2 e3) (s', Rerr err))

/\ (! ck env e1 e2 v bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
evaluate ck (v::env) s2 e2 bv)
==>
evaluate ck env s1 (Let e1 e2) bv)

/\ (! ck env e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Let e1 e2) (s', Rerr err))

/\ (! ck env e1 e2 v bv s1 s2.
(evaluate ck env s1 e1 (s2, Rval v) /\
evaluate ck env s2 e2 bv)
==>
evaluate ck env s1 (Seq e1 e2) bv)

/\ (! ck env e1 e2 err s s'.
(evaluate ck env s e1 (s', Rerr err))
==>
evaluate ck env s (Seq e1 e2) (s', Rerr err))

/\ (! ck env funs e bv s.
(evaluate ck ((build_rec_env funs env)++env) s e bv)
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
evaluate_list ck env s1 (e::es) (s3, Rerr err))`;

val _ = export_theory()
