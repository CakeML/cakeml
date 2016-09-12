open preamble bigStepTheory exhLangTheory

val _ = new_theory"exhSem"

(*
 * The values of exhLang differ from decLang in the same way as the
 * expressions.
 *
 * The semantics of exhLang differ in that pattern matches that fall off the end
 * raise a type error, and the mapping from types to constructor tags is
 * omitted.
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
  (do_eq (Closure _ _ _) (Closure _ _ _) = Eq_val T)
  ∧
  (do_eq (Closure _ _ _) (Recclosure _ _ _) = Eq_val T)
  ∧
  (do_eq (Recclosure _ _ _) (Closure _ _ _) = Eq_val T)
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

val _ = Datatype`
  state =
  <| clock   : num
   ; refs    : exhSem$v store
   ; ffi     : 'ffi ffi_state
   ; globals : exhSem$v option list
   |>`;

val do_app_def = Define `
  do_app (s:'ffi exhSem$state) op (vs:exhSem$v list) =
  case op of
  | Init_global_var idx =>
    (case vs of
     | [v] =>
         if idx < LENGTH s.globals then
           (case EL idx s.globals of
            | NONE => SOME (s with globals := LUPDATE (SOME v) idx s.globals, (Rval (Conv tuple_tag [])))
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
                 ---
                 further modifications added after change from csg to state record
              *)
  (
  case (op, vs) of
  | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    if ((op = Divide) ∨ (op = Modulo)) ∧ (n2 = 0) then
      SOME (s, Rerr (Rraise (prim_exn div_tag)))
    else
      SOME (s, Rval (Litv (IntLit (opn_lookup op n1 n2))))
  | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    SOME (s, Rval (Boolv (opb_lookup op n1 n2)))
  | (Opw wz op, [Litv w1; Litv w2]) =>
     (case do_word_op op wz w1 w2 of
          | NONE => NONE
          | SOME w => SOME (s, Rval (Litv w)))
  | (Shift wz sh n, [Litv w]) =>
      (case do_shift sh n wz w of
         | NONE => NONE
         | SOME w => SOME (s, Rval (Litv w)))
  | (Equality, [v1; v2]) =>
    (case do_eq v1 v2 of
     | Eq_type_error => NONE
     | Eq_val b => SOME (s, Rval (Boolv b)))
  | (Opassign, [Loc lnum; v]) =>
    (case store_assign lnum (Refv v) s.refs of
     | SOME st => SOME (s with refs := st, Rval (Conv tuple_tag []))
     | NONE => NONE)
  | (Opref, [v]) =>
    let (s',n) = (store_alloc (Refv v) s.refs) in
      SOME (s with refs := s', Rval (Loc n))
  | (Opderef, [Loc n]) =>
    (case store_lookup n s.refs of
     | SOME (Refv v) => SOME (s,Rval v)
     | _ => NONE)
  | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
    if n < 0 then
      SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
    else
      let (s',lnum) =
        store_alloc (W8array (REPLICATE (Num (ABS ( n))) w)) s.refs
      in
        SOME (s with refs := s', Rval (Loc lnum))
  | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       if i < 0 then
         SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
           else
             SOME (s, Rval (Litv (Word8 (EL n ws))))
     | _ => NONE)
  | (Aw8length, [Loc n]) =>
    (case store_lookup n s.refs of
     | SOME (W8array ws) =>
       SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
     | _ => NONE)
  | (Aw8update, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       if i < 0 then
         SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
           else
             (case store_assign lnum (W8array (LUPDATE w n ws)) s.refs of
              | NONE => NONE
              | SOME s' => SOME (s with refs := s', Rval (Conv tuple_tag [])))
     | _ => NONE)
  | (WordFromInt wz, [Litv (IntLit i)]) =>
    SOME (s, Rval (Litv (do_word_from_int wz i)))
  | (WordToInt wz, [Litv w]) =>
    (case do_word_to_int wz w of
      | NONE => NONE
      | SOME i => SOME (s, Rval (Litv (IntLit i))))
  | (Ord, [Litv (Char c)]) =>
    SOME (s, Rval (Litv(IntLit(int_of_num(ORD c)))))
  | (Chr, [Litv (IntLit i)]) =>
    SOME (s,
          if (i < 0) ∨ (i > 255) then
            Rerr (Rraise (prim_exn chr_tag))
          else
            Rval (Litv(Char(CHR(Num(ABS i))))))
  | (Chopb op, [Litv (Char c1); Litv (Char c2)]) =>
    SOME (s, Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
  | (Implode, [v]) =>
    (case v_to_char_list v of
     | SOME ls =>
       SOME (s, Rval (Litv (StrLit (IMPLODE ls))))
     | NONE => NONE)
  | (Explode, [Litv (StrLit str)]) =>
    SOME (s, Rval (char_list_to_v (EXPLODE str)))
  | (Strlen, [Litv (StrLit str)]) =>
    SOME (s, Rval (Litv(IntLit(int_of_num(STRLEN str)))))
  | (VfromList, [v]) =>
    (case v_to_list v of
     | SOME vs =>
       SOME (s, Rval (Vectorv vs))
     | NONE => NONE)
  | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
    if i < 0 then
      SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
    else
      let n = (Num (ABS i)) in
        if n >= LENGTH vs then
          SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
        else
          SOME (s, Rval (EL n vs))
  | (Vlength, [Vectorv vs]) =>
    SOME (s, Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
  | (Aalloc, [Litv (IntLit n); v]) =>
    if n < 0 then
      SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
    else
      let (s',lnum) =
        store_alloc (Varray (REPLICATE (Num (ABS n)) v)) s.refs
      in
        SOME (s with refs := s', Rval (Loc lnum))
  | (Asub, [Loc lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s.refs of
     | SOME (Varray vs) =>
     if i < 0 then
       SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
         else
           SOME (s, Rval (EL n vs))
     | _ => NONE)
    | (Alength, [Loc n]) =>
      (case store_lookup n s.refs of
       | SOME (Varray ws) =>
         SOME (s,Rval (Litv (IntLit(int_of_num(LENGTH ws)))))
       | _ => NONE)
  | (Aupdate, [Loc lnum; Litv (IntLit i); v]) =>
    (case store_lookup lnum s.refs of
     | SOME (Varray vs) =>
     if i < 0 then
       SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
         else
           (case store_assign lnum (Varray (LUPDATE v n vs)) s.refs of
            | NONE => NONE
            | SOME s' => SOME (s with refs := s', Rval (Conv tuple_tag [])))
     | _ => NONE)
  | (FFI n, [Loc lnum]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       (case call_FFI s.ffi n ws of
        | (t', ws') =>
          (case store_assign lnum (W8array ws') s.refs of
           | SOME s' => SOME (s with <| refs := s'; ffi := t' |>, Rval (Conv tuple_tag []))
           | NONE => NONE))
     | _ => NONE)
  | _ => NONE
  )`;

val do_app_cases = Q.store_thm("do_app_cases",
  `exhSem$do_app s op vs = SOME x ⇒
    (∃z n1 n2. op = (Op (Opn z)) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃z n1 n2. op = (Op (Opb z)) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃z wz w1 w2. op = (Op (Opw wz z)) ∧ vs = [Litv w1; Litv w2]) ∨
    (∃sh z wz w. op = (Op (Shift wz sh z)) ∧ vs = [Litv w]) ∨
    (∃v1 v2. op = (Op Equality) ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = (Op Opassign) ∧ vs = [Loc lnum; v]) ∨
    (∃n. op = (Op Opderef) ∧ vs = [Loc n]) ∨
    (∃v. op = (Op Opref) ∧ vs = [v]) ∨
    (∃idx v. op = (Init_global_var idx) ∧ vs = [v]) ∨
    (∃n w. op = (Op Aw8alloc) ∧ vs = [Litv (IntLit n); Litv (Word8 w)]) ∨
    (∃lnum i. op = (Op Aw8sub) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op Aw8length) ∧ vs = [Loc n]) ∨
    (∃lnum i w. op = (Op Aw8update) ∧ vs = [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) ∨
    (∃wz w. op = (Op (WordToInt wz)) ∧ vs = [Litv w]) ∨
    (∃wz n. op = (Op (WordFromInt wz)) ∧ vs = [Litv (IntLit n)]) ∨
    (∃c. op = (Op Ord) ∧ vs = [Litv (Char c)]) ∨
    (∃n. op = (Op Chr) ∧ vs = [Litv (IntLit n)]) ∨
    (∃z c1 c2. op = (Op (Chopb z)) ∧ vs = [Litv (Char c1); Litv (Char c2)]) ∨
    (∃s. op = (Op Explode) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v ls. op = (Op Implode) ∧ vs = [v] ∧ (v_to_char_list v = SOME ls)) ∨
    (∃s. op = (Op Strlen) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v vs'. op = (Op VfromList) ∧ vs = [v] ∧ (v_to_list v = SOME vs')) ∨
    (∃vs' i. op = (Op Vsub) ∧ vs = [Vectorv vs'; Litv (IntLit i)]) ∨
    (∃vs'. op = (Op Vlength) ∧ vs = [Vectorv vs']) ∨
    (∃v n. op = (Op Aalloc) ∧ vs = [Litv (IntLit n); v]) ∨
    (∃lnum i. op = (Op Asub) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op Alength) ∧ vs = [Loc n]) ∨
    (∃lnum i v. op = (Op Aupdate) ∧ vs = [Loc lnum; Litv (IntLit i); v]) ∨
    (∃lnum n. op = (Op (FFI n)) ∧ vs = [Loc lnum])`,
  rw[do_app_def] >>
  pop_assum mp_tac >>
  Cases_on`op` >- (
    simp[] >>
    every_case_tac >> fs[] ) >>
  BasicProvers.CASE_TAC >>
  every_case_tac);

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

val check_clock_def = Define`
  check_clock s' s =
    s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock`;

val check_clock_id = Q.store_thm("check_clock_id",
  `s'.clock ≤ s.clock ⇒ exhSem$check_clock s' s = s'`,
  EVAL_TAC >> rw[theorem"state_component_equality"])

val dec_clock_def = Define`
  dec_clock s = s with clock := s.clock -1`;

val evaluate_def = tDefine"evaluate"`
  (evaluate (env:(string,exhSem$v) alist) (s:'ffi exhSem$state) ([]:exhLang$exp list) = (s,Rval [])) ∧
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
  (evaluate env s [Handle e pes] =
   case evaluate env s [e] of
   | (s', Rerr (Rraise v)) => evaluate_match env (check_clock s' s) v pes
   | res => res) ∧
  (evaluate env s [Con tag es] =
   case evaluate env s (REVERSE es) of
   | (s, Rval vs) => (s, Rval [Conv tag (REVERSE vs)])
   | res => res) ∧
  (evaluate env s [Var_local n] = (s,
   case ALOOKUP env n of
   | SOME v => Rval [v]
   | NONE => Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Var_global n] = (s,
   if n < LENGTH s.globals ∧ IS_SOME (EL n s.globals)
   then Rval [THE (EL n s.globals)]
   else Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Fun n e] = (s, Rval [Closure env n e])) ∧
  (evaluate env s [App op es] =
   case evaluate env s (REVERSE es) of
   | (s', Rval vs) =>
       if op = Op Opapp then
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
  (evaluate env s [Mat e pes] =
   case evaluate env s [e] of
   | (s', Rval v) => evaluate_match env (check_clock s' s) (HD v) pes
   | res => res) ∧
  (evaluate env s [Let n e1 e2] =
   case evaluate env s [e1] of
   | (s', Rval vs) => evaluate (opt_bind n (HD vs) env) (check_clock s' s) [e2]
   | res => res) ∧
  (evaluate env s [Letrec funs e] =
   if ALL_DISTINCT (MAP FST funs)
   then evaluate (build_rec_env funs env env) s [e]
   else (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Extend_global n] =
   (s with globals := s.globals++GENLIST(K NONE) n, Rval [Conv tuple_tag []])) ∧
  (evaluate_match env s v [] = (s, Rerr(Rabort Rtype_error))) ∧
  (evaluate_match env s v ((p,e)::pes) =
   if ALL_DISTINCT (pat_bindings p []) then
     case pmatch s.refs p v env of
     | Match env' => evaluate env' s [e]
     | No_match => evaluate_match env s v pes
     | _ => (s, Rerr(Rabort Rtype_error))
   else (s, Rerr(Rabort Rtype_error)))`
  (wf_rel_tac`inv_image ($< LEX $<)
                (λx. case x of (INL(_,s,es)) => (s.clock,exp6_size es)
                             | (INR(_,s,_,pes)) => (s.clock,exp3_size pes))` >>
   simp[check_clock_def,dec_clock_def] >>
   rw[] >> simp[])

val evaluate_ind = theorem"evaluate_ind"

val s = ``s1:'ffi exhSem$state``

val evaluate_clock = Q.store_thm("evaluate_clock",
  `(∀env ^s e r s2. evaluate env s1 e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
   (∀env ^s v pes r s2. evaluate_match env s1 v pes = (s2,r) ⇒ s2.clock ≤ s1.clock)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[] >> rw[] >> rfs[] >>
  fs[check_clock_def,dec_clock_def] >> simp[] >>
  imp_res_tac do_app_cases >>
  fs[do_app_def] >>
  every_case_tac >>
  fs[LET_THM,semanticPrimitivesTheory.store_alloc_def,semanticPrimitivesTheory.store_assign_def] >>
  rw[] >> every_case_tac >> fs[] >> rw[] )

val s = ``s:'ffi exhSem$state``
val s' = ``s':'ffi exhSem$state``
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
  ["do_eq_UNION_aux","do_eq_UNION",
   "pmatch_UNION_aux","pmatch_UNION",
   "evaluate_UNION_aux","evaluate_UNION"];

val _ = export_theory()
