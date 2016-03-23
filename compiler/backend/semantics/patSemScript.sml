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
  (do_eq (Closure _ _) (Closure _ _) = Eq_val T)
  ∧
  (do_eq (Closure _ _) (Recclosure _ _ _) = Eq_val T)
  ∧
  (do_eq (Recclosure _ _ _) (Closure _ _) = Eq_val T)
  ∧
  (do_eq (Recclosure _ _ _) (Recclosure _ _ _) = Eq_val T)
  ∧
  (do_eq _ _ = Eq_type_error)
  ∧
  (do_eq_list [] [] = Eq_val T)
  ∧
  (do_eq_list (v1::vs1) (v2::vs2) =
   (case do_eq v1 v2 of
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

val _ = Datatype`
  state =
    <| clock   : num
     ; refs    : patSem$v store
     ; ffi     : 'ffi ffi_state
     ; globals : patSem$v option list
     |>`;

val do_app_def = Define `
 (do_app s op vs =
((case (op,vs) of
      (Op (Op (Opn op)), [Litv (IntLit n1); Litv (IntLit n2)]) =>
        if ((op = Divide) \/ (op = Modulo)) /\ (n2 =( 0 : int)) then
          SOME (s, Rerr (Rraise (prim_exn div_tag)))
        else
          SOME (s, Rval (Litv (IntLit (opn_lookup op n1 n2))))
    | (Op (Op (Opb op)), [Litv (IntLit n1); Litv (IntLit n2)]) =>
        SOME (s, Rval (Boolv (opb_lookup op n1 n2)))
    | (Op (Op Equality), [v1; v2]) =>
        (case do_eq v1 v2 of
            Eq_type_error => NONE
          | Eq_val b => SOME (s, Rval(Boolv b))
        )
    | (Op (Op Opassign), [Loc lnum; v]) =>
        (case store_assign lnum (Refv v) s.refs of
          SOME st => SOME (s with refs := st, Rval (Conv tuple_tag []))
        | NONE => NONE
        )
    | (Op (Op Opderef), [Loc n]) =>
        (case store_lookup n s.refs of
            SOME (Refv v) => SOME (s,Rval v)
          | _ => NONE
        )
    | (Op (Op Opref), [v]) =>
        let (s',n) = (store_alloc (Refv v) s.refs) in
          SOME (s with refs := s', Rval (Loc n))
    | (Op (Init_global_var idx), [v]) =>
        if idx < LENGTH s.globals then
          (case EL idx s.globals of
              NONE => SOME ((s with globals := LUPDATE (SOME v) idx s.globals), Rval (Conv tuple_tag []))
            | SOME _ => NONE
          )
        else
          NONE
    | (Op (Op Aw8alloc), [Litv (IntLit n); Litv (Word8 w)]) =>
        if n <( 0 : int) then
          SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
        else
          let (st,lnum) =
(store_alloc (W8array (REPLICATE (Num (ABS ( n))) w)) s.refs)
          in
            SOME (s with refs := st, Rval (Loc lnum))
    | (Op (Op Aw8sub), [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s.refs of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
              else
                let n = (Num (ABS ( i))) in
                  if n >= LENGTH ws then
                    SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
                  else
                    SOME (s, Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Op (Op Aw8length), [Loc n]) =>
        (case store_lookup n s.refs of
            SOME (W8array ws) =>
              SOME (s,Rval (Litv (IntLit (int_of_num (LENGTH ws)))))
          | _ => NONE
        )
    | (Op (Op Aw8update), [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) =>
        (case store_lookup lnum s.refs of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
            else
              let n = (Num (ABS ( i))) in
                if n >= LENGTH ws then
                  SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s.refs of
                      NONE => NONE
                    | SOME st => SOME (s with refs := st, Rval (Conv tuple_tag []))
                  )
        | _ => NONE
        )
    | (Op (Op W8fromInt), [Litv (IntLit i)]) =>
      SOME (s, Rval (Litv (Word8 (i2w i))))
    | (Op (Op W8toInt), [Litv (Word8 w)]) =>
      SOME (s, Rval (Litv (IntLit (w2i w))))
    | (Op (Op Ord), [Litv (Char c)]) =>
          SOME (s, Rval (Litv(IntLit(int_of_num(ORD c)))))
    | (Op (Op Chr), [Litv (IntLit i)]) =>
        SOME (s,
(if (i <( 0 : int)) \/ (i >( 255 : int)) then
            Rerr (Rraise (prim_exn chr_tag))
          else
            Rval (Litv(Char(CHR(Num (ABS ( i))))))))
    | (Op (Op (Chopb op)), [Litv (Char c1); Litv (Char c2)]) =>
        SOME (s, Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
    | (Op (Op Implode), [v]) =>
          (case v_to_char_list v of
            SOME ls =>
              SOME (s, Rval (Litv (StrLit (IMPLODE ls))))
          | NONE => NONE
          )
    | (Op (Op Explode), [Litv (StrLit str)]) =>
        SOME (s, Rval (char_list_to_v (EXPLODE str)))
    | (Op (Op Strlen), [Litv (StrLit str)]) =>
        SOME (s, Rval (Litv(IntLit(int_of_num(STRLEN str)))))
    | (Op (Op VfromList), [v]) =>
          (case v_to_list v of
              SOME vs =>
                SOME (s, Rval (Vectorv vs))
            | NONE => NONE
          )
    | (Op (Op Vsub), [Vectorv vs; Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
        else
          let n = (Num (ABS ( i))) in
            if n >= LENGTH vs then
              SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
            else
              SOME (s, Rval (EL n vs))
    | (Op (Op Vlength), [Vectorv vs]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
    | (Op (Op Aalloc), [Litv (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
        else
          let (s',lnum) =
(store_alloc (Varray (REPLICATE (Num (ABS ( n))) v)) s.refs)
          in
            SOME (s with refs := s', Rval (Loc lnum))
    | (Op (Op Asub), [Loc lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s.refs of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
              else
                let n = (Num (ABS ( i))) in
                  if n >= LENGTH vs then
                    SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
                  else
                    SOME (s, Rval (EL n vs))
          | _ => NONE
        )
    | (Op (Op Alength), [Loc n]) =>
        (case store_lookup n s.refs of
            SOME (Varray ws) =>
              SOME (s,Rval (Litv (IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Op (Op Aupdate), [Loc lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s.refs of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
            else
              let n = (Num (ABS ( i))) in
                if n >= LENGTH vs then
                  SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s.refs of
                      NONE => NONE
                    | SOME s' => SOME (s with refs := s', Rval (Conv tuple_tag []))
                  )
        | _ => NONE
      )
    | (Op (Op (FFI n)), [Loc lnum]) =>
        (case store_lookup lnum s.refs of
          SOME (W8array ws) =>
            (case call_FFI s.ffi n ws of
              (t', ws') =>
               (case store_assign lnum (W8array ws') s.refs of
                 SOME s' => SOME (s with <| refs := s'; ffi := t' |>, Rval (Conv tuple_tag []))
               | NONE => NONE))
        | _ => NONE)
    | (Tag_eq n l, [Conv tag vs]) =>
        SOME (s, Rval (Boolv (tag = n ∧ LENGTH vs = l)))
    | (El n, [Conv _ vs]) =>
        if n < LENGTH vs then
          SOME (s, Rval (EL n vs))
        else
          NONE
    | _ => NONE
  )))`;

val do_app_cases = Q.store_thm("do_app_cases",
  `patSem$do_app s op vs = SOME x ⇒
    (∃z n1 n2. op = (Op (Op (Opn z))) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃z n1 n2. op = (Op (Op (Opb z))) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃v1 v2. op = (Op (Op Equality)) ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = (Op (Op Opassign)) ∧ vs = [Loc lnum; v]) ∨
    (∃n. op = (Op (Op Opderef)) ∧ vs = [Loc n]) ∨
    (∃v. op = (Op (Op Opref)) ∧ vs = [v]) ∨
    (∃idx v. op = (Op (Init_global_var idx)) ∧ vs = [v]) ∨
    (∃n l tag v. op = Tag_eq n l ∧ vs = [Conv tag v]) ∨
    (∃n tag v. op = El n ∧ vs = [Conv tag v]) ∨
    (∃n w. op = (Op (Op Aw8alloc)) ∧ vs = [Litv (IntLit n); Litv (Word8 w)]) ∨
    (∃lnum i. op = (Op (Op Aw8sub)) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op (Op Aw8length)) ∧ vs = [Loc n]) ∨
    (∃lnum i w. op = (Op (Op Aw8update)) ∧ vs = [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) ∨
    (∃w. op = (Op (Op W8toInt)) ∧ vs = [Litv (Word8 w)]) ∨
    (∃n. op = (Op (Op W8fromInt)) ∧ vs = [Litv (IntLit n)]) ∨
    (∃c. op = (Op (Op Ord)) ∧ vs = [Litv (Char c)]) ∨
    (∃n. op = (Op (Op Chr)) ∧ vs = [Litv (IntLit n)]) ∨
    (∃z c1 c2. op = (Op (Op (Chopb z))) ∧ vs = [Litv (Char c1); Litv (Char c2)]) ∨
    (∃s. op = (Op (Op Explode)) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v ls. op = (Op (Op Implode)) ∧ vs = [v] ∧ (v_to_char_list v = SOME ls)) ∨
    (∃s. op = (Op (Op Strlen)) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v vs'. op = (Op (Op VfromList)) ∧ vs = [v] ∧ (v_to_list v = SOME vs')) ∨
    (∃vs' i. op = (Op (Op Vsub)) ∧ vs = [Vectorv vs'; Litv (IntLit i)]) ∨
    (∃vs'. op = (Op (Op Vlength)) ∧ vs = [Vectorv vs']) ∨
    (∃v n. op = (Op (Op Aalloc)) ∧ vs = [Litv (IntLit n); v]) ∨
    (∃lnum i. op = (Op (Op Asub)) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op (Op Alength)) ∧ vs = [Loc n]) ∨
    (∃lnum i v. op = (Op (Op Aupdate)) ∧ vs = [Loc lnum; Litv (IntLit i); v]) ∨
    (∃lnum n. op = (Op (Op (FFI n))) ∧ vs = [Loc lnum])`,
  rw[do_app_def] >>
  pop_assum mp_tac >>
  Cases_on`op` >- (
    simp[] >>
    every_case_tac >> fs[] ) >>
  BasicProvers.CASE_TAC >>
  every_case_tac);

val do_if_def = Define `
  do_if v e1 e2 =
    if v = Boolv T then SOME e1 else
    if v = Boolv F then SOME e2 else NONE`;

val check_clock_def = Define`
  check_clock s' s =
    s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock`;

val check_clock_id = Q.store_thm("check_clock_id",
  `s'.clock ≤ s.clock ⇒ patSem$check_clock s' s = s'`,
  EVAL_TAC >> rw[theorem"state_component_equality"])

val dec_clock_def = Define`
  dec_clock s = s with clock := s.clock -1`;

val evaluate_def = tDefine"evaluate"`
  (evaluate (env:patSem$v list) (s:'ffi patSem$state) ([]:patLang$exp list) = (s,Rval [])) ∧
  (evaluate env s (e1::e2::es) =
    case evaluate env s [e1] of
    | (s', Rval v) =>
        (case evaluate env (check_clock s' s) (e2::es) of
         | (s, Rval vs) => (s, Rval (HD v::vs))
         | res => res)
    | res => res) ∧
  (evaluate env s [(Lit l)] = (s, Rval [Litv l])) ∧
  (evaluate env s [Raise e] =
   case evaluate env s [e] of
   | (s, Rval v) => (s, Rerr (Rraise (HD v)))
   | res => res) ∧
  (evaluate env s [Handle e1 e2] =
   case evaluate env s [e1] of
   | (s', Rerr (Rraise v)) => evaluate (v::env) (check_clock s' s) [e2]
   | res => res) ∧
  (evaluate env s [Con tag es] =
   case evaluate env s (REVERSE es) of
   | (s, Rval vs) => (s, Rval [Conv tag (REVERSE vs)])
   |  res => res) ∧
  (evaluate env s [Var_local n] = (s,
      if n < LENGTH env
      then Rval [EL n env]
      else Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Var_global n] = (s,
      if n < LENGTH s.globals ∧ IS_SOME (EL n s.globals)
      then Rval [THE (EL n s.globals)]
      else Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Fun e] = (s, Rval [Closure env e])) ∧
  (evaluate env s [App op es] =
   case evaluate env s (REVERSE es) of
   | (s', Rval vs) =>
       if op = Op (Op Opapp) then
         (case do_opapp (REVERSE vs) of
          | SOME (env, e) =>
            if s'.clock = 0 ∨ s.clock = 0 then
              (s', Rerr (Rabort Rtimeout_error))
            else
              evaluate env (dec_clock (check_clock s' s)) [e]
          | NONE => (s', Rerr (Rabort Rtype_error)))
       else
       (case (do_app s' op (REVERSE vs)) of
        | NONE => (s', Rerr (Rabort Rtype_error))
        | SOME (s,r) => (s, list_result r))
   | res => res) ∧
  (evaluate env s [If e1 e2 e3] =
   case evaluate env s [e1] of
   | (s', Rval vs) =>
       (case do_if (HD vs) e2 e3 of
        | SOME e => evaluate env (check_clock s' s) [e]
        | NONE => (s', Rerr (Rabort Rtype_error)))
   | res => res) ∧
  (evaluate env s [Let e1 e2] =
   case evaluate env s [e1] of
   | (s', Rval vs) => evaluate (HD vs::env) (check_clock s' s) [e2]
   | res => res) ∧
  (evaluate env s [Seq e1 e2] =
   case evaluate env s [e1] of
   | (s', Rval vs) => evaluate env (check_clock s' s) [e2]
   | res => res) ∧
  (evaluate env s [Letrec funs e] =
   evaluate ((build_rec_env funs env)++env) s [e]) ∧
  (evaluate env s [Extend_global n] =
   (s with globals := s.globals++GENLIST(K NONE) n, Rval [Conv tuple_tag []]))`
  (wf_rel_tac`inv_image ($< LEX $<)
                (λx. case x of (_,s,es) => (s.clock,exp1_size es))` >>
   simp[check_clock_def,dec_clock_def] >>
   rw[do_if_def] >> simp[])

val evaluate_ind = theorem"evaluate_ind"

val evaluate_clock = Q.store_thm("evaluate_clock",
  `(∀env s1 e r s2. evaluate env s1 e = (s2,r) ⇒ s2.clock ≤ s1.clock)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[] >> rw[] >> rfs[] >>
  fs[check_clock_def,dec_clock_def] >> simp[] >>
  imp_res_tac do_app_cases >>
  fs[do_app_def] >>
  every_case_tac >>
  fs[LET_THM,semanticPrimitivesTheory.store_alloc_def,semanticPrimitivesTheory.store_assign_def] >>
  rw[] >> every_case_tac >> fs[] >> rw[] )

val s = ``s:'ffi patSem$state``
val s' = ``s':'ffi patSem$state``
val clean_term =
  term_rewrite
  [``check_clock ^s' ^s = s'``,
   ``^s'.clock = 0 ∨ ^s.clock = 0 ⇔ s'.clock = 0``]

val evaluate_ind = let
  val goal = evaluate_ind |> concl |> clean_term
  (* set_goal([],goal) *)
in prove(goal,
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac evaluate_ind >>
  rw[] >> first_x_assum match_mp_tac >>
  rw[] >> fs[] >>
  res_tac >>
  imp_res_tac evaluate_clock >>
  fsrw_tac[ARITH_ss][check_clock_id])
end
|> curry save_thm "evaluate_ind"

val evaluate_def = let
  val goal = evaluate_def |> concl |> clean_term |> replace_term s' s
  (* set_goal([],goal) *)
in prove(goal,
  rpt strip_tac >>
  rw[Once evaluate_def] >>
  every_case_tac >>
  imp_res_tac evaluate_clock >>
  fs[check_clock_id] >>
  `F` suffices_by rw[] >> decide_tac)
end
|> curry save_thm "evaluate_def"

val semantics_def = Define`
  semantics env st es =
    if ∃k. SND (evaluate env (st with clock := k) es) = Rerr (Rabort Rtype_error)
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate env (st with clock := k) es = (s,r) ∧
        (case s.ffi.final_event of
         | NONE => (∀a. r ≠ Rerr (Rabort a)) ∧ outcome = Success
         | SOME e => outcome = FFI_outcome e) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (FST (evaluate env (st with clock := k) es)).ffi.io_events) UNIV))`;

val _ = map delete_const
  ["do_eq_UNION_aux","do_eq_UNION", "evaluate_tupled_aux"];

val _ = export_theory()
