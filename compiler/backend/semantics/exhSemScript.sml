open preamble exhLangTheory backend_commonTheory;
open semanticPrimitivesPropsTheory; (* for do_shift and others *)

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
  (pmatch s Pany v' env = Match env)
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

val vs_to_w8s_def = Define`
  (vs_to_w8s s [] = SOME []) ∧
  (vs_to_w8s s (Loc l::vs) =
   case store_lookup l s of
   | SOME (W8array ws1) =>
     (case vs_to_w8s s vs of
      | SOME ws2 => SOME (ws1++ws2)
      | _ => NONE)
   | _ => NONE) ∧
  (vs_to_w8s _ _ = NONE)`;

val vs_to_string_def = Define`
  (vs_to_string [] = SOME "") ∧
  (vs_to_string (Litv(StrLit s1)::vs) =
   case vs_to_string vs of
   | SOME s2 => SOME (s1++s2)
   | _ => NONE) ∧
  (vs_to_string _ = NONE)`;

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
  | (FP_bop bop, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME (s,Rval (Litv (Word64 (fp_bop bop w1 w2))))
  | (FP_uop uop, [Litv (Word64 w)]) =>
      SOME (s,Rval (Litv (Word64 (fp_uop uop w))))
  | (FP_cmp cmp, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME (s,Rval (Boolv (fp_cmp cmp w1 w2)))
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
  | (CopyStrStr, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len)]) =>
      SOME (s,
      (case copy_array (str,off) len NONE of
        NONE => Rerr (Rraise (prim_exn subscript_tag))
      | SOME cs => Rval (Litv(StrLit(cs)))))
  | (CopyStrAw8, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len);
                  Loc dst;Litv(IntLit dstoff)]) =>
      (case store_lookup dst s.refs of
        SOME (W8array ws) =>
          (case copy_array (str,off) len (SOME(ws_to_chars ws,dstoff)) of
            NONE => SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
          | SOME cs =>
            (case store_assign dst (W8array (chars_to_ws cs)) s.refs of
              SOME s' =>  SOME (s with refs := s', Rval (Conv tuple_tag []))
            | _ => NONE))
      | _ => NONE)
  | (CopyAw8Str, [Loc src;Litv(IntLit off);Litv(IntLit len)]) =>
    (case store_lookup src s.refs of
      SOME (W8array ws) =>
      SOME (s,
        (case copy_array (ws,off) len NONE of
          NONE => Rerr (Rraise (prim_exn subscript_tag))
        | SOME ws => Rval (Litv(StrLit(ws_to_chars ws)))))
    | _ => NONE)
  | (CopyAw8Aw8, [Loc src;Litv(IntLit off);Litv(IntLit len);
                  Loc dst;Litv(IntLit dstoff)]) =>
    (case (store_lookup src s.refs, store_lookup dst s.refs) of
      (SOME (W8array ws), SOME (W8array ds)) =>
        (case copy_array (ws,off) len (SOME(ds,dstoff)) of
          NONE => SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
        | SOME ws =>
            (case store_assign dst (W8array ws) s.refs of
              SOME s' => SOME (s with refs := s', Rval (Conv tuple_tag []))
            | _ => NONE))
    | _ => NONE)
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
  | (Strsub, [Litv (StrLit str); Litv (IntLit i)]) =>
    if i < 0 then
      SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
    else
      let n = (Num (ABS i)) in
        if n >= LENGTH str then
          SOME (s, Rerr (Rraise (prim_exn subscript_tag)))
        else
          SOME (s, Rval (Litv (Char (EL n str))))
  | (Strlen, [Litv (StrLit str)]) =>
    SOME (s, Rval (Litv(IntLit(int_of_num(STRLEN str)))))
  | (Strcat, [v]) =>
      (case v_to_list v of
        SOME vs =>
          (case vs_to_string vs of
            SOME str =>
              SOME (s, Rval (Litv(StrLit str)))
          | _ => NONE)
      | _ => NONE)
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
  | (ConfigGC, [Litv (IntLit n1); Litv (IntLit n2)]) =>
       SOME (s, Rval (Conv tuple_tag []))
  | (FFI n, [Litv (StrLit conf); Loc lnum]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       (case call_FFI s.ffi n (MAP (λc. n2w(ORD c)) conf) ws of
        | (t', ws') =>
          (case store_assign lnum (W8array ws') s.refs of
           | SOME s' => SOME (s with <| refs := s'; ffi := t' |>, Rval (Conv tuple_tag []))
           | NONE => NONE))
     | _ => NONE)
  | _ => NONE
  )`;

val op_thms = { nchotomy = conLangTheory.op_nchotomy, case_def = conLangTheory.op_case_def}
val astop_thms = {nchotomy = astTheory.op_nchotomy, case_def = astTheory.op_case_def}
val modop_thms = {nchotomy = modLangTheory.op_nchotomy, case_def = modLangTheory.op_case_def}
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def}
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def}
val v_thms = { nchotomy = theorem"v_nchotomy", case_def = definition"v_case_def"}
val sv_thms = { nchotomy = semanticPrimitivesTheory.store_v_nchotomy, case_def = semanticPrimitivesTheory.store_v_case_def }
val lit_thms = { nchotomy = astTheory.lit_nchotomy, case_def = astTheory.lit_case_def}
val eqs = LIST_CONJ (map prove_case_eq_thm
  [op_thms, modop_thms, astop_thms, list_thms, option_thms, v_thms, sv_thms, lit_thms])

val do_app_cases = save_thm("do_app_cases",
  ``exhSem$do_app s op vs = SOME x`` |>
  SIMP_CONV(srw_ss()++COND_elim_ss++LET_ss)[PULL_EXISTS, do_app_def, eqs, pair_case_eq]);

val eq_result_CASE_tm = prim_mk_const{Name="eq_result_CASE",Thy="semanticPrimitives"};
val check =
  do_app_cases |> concl |> find_terms TypeBase.is_case
  |> List.map (#1 o strip_comb)
  |> List.all (fn tm => List.exists (same_const tm) [optionSyntax.option_case_tm, eq_result_CASE_tm])
val () = if check then () else raise(ERR"exhSem""do_app_cases failed")

val do_app_cases_none = save_thm("do_app_cases_none",
  ``exhSem$do_app s op vs = NONE`` |>
  SIMP_CONV(srw_ss()++COND_elim_ss++LET_ss)[PULL_EXISTS, do_app_def, eqs, pair_case_eq]);

val pat_bindings_def = Define`
  (pat_bindings ((Pvar n):exhLang$pat) already_bound =
   n::already_bound)
  ∧
  (pat_bindings Pany already_bound = already_bound) ∧
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

val dec_clock_def = Define`
dec_clock s = s with clock := s.clock -1`;

val fix_clock_def = Define `
  fix_clock s (s1,res) = (s1 with clock := MIN s.clock s1.clock,res)`

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (s1,res) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val evaluate_def = tDefine"evaluate"`
  (evaluate (env:(string,exhSem$v) alist) (s:'ffi exhSem$state) ([]:exhLang$exp list) = (s,Rval [])) ∧
  (evaluate env s (e1::e2::es) =
    case fix_clock s (evaluate env s [e1]) of
    | (s, Rval v) =>
        (case evaluate env s (e2::es) of
         | (s, Rval vs) => (s, Rval (HD v::vs))
         | res => res)
    | res => res) ∧
  (evaluate env s [Lit _ l] = (s, Rval [Litv l])) ∧
  (evaluate env s [Raise _ e] =
   case evaluate env s [e] of
   | (s, Rval v) => (s, Rerr (Rraise (HD v)))
   | res => res) ∧
  (evaluate env s [Handle _ e pes] =
   case fix_clock s (evaluate env s [e]) of
   | (s, Rerr (Rraise v)) => evaluate_match env s v pes
   | res => res) ∧
  (evaluate env s [Con _ tag es] =
   case evaluate env s (REVERSE es) of
   | (s, Rval vs) => (s, Rval [Conv tag (REVERSE vs)])
   | res => res) ∧
  (evaluate env s [Var_local _ n] = (s,
   case ALOOKUP env n of
   | SOME v => Rval [v]
   | NONE => Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Var_global _ n] = (s,
   if n < LENGTH s.globals ∧ IS_SOME (EL n s.globals)
   then Rval [THE (EL n s.globals)]
   else Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Fun _ n e] = (s, Rval [Closure env n e])) ∧
  (evaluate env s [App _ op es] =
   case fix_clock s (evaluate env s (REVERSE es)) of
   | (s, Rval vs) =>
       if op = Op Opapp then
         (case do_opapp (REVERSE vs) of
          | SOME (env, e) =>
            if s.clock = 0 then
              (s, Rerr (Rabort Rtimeout_error))
            else
              evaluate env (dec_clock s) [e]
          | NONE => (s, Rerr (Rabort Rtype_error)))
       else
       (case (do_app s op (REVERSE vs)) of
        | NONE => (s, Rerr (Rabort Rtype_error))
        | SOME (s,r) => (s, list_result r))
   | res => res) ∧
  (evaluate env s [Mat _ e pes] =
   case fix_clock s (evaluate env s [e]) of
   | (s, Rval v) => evaluate_match env s (HD v) pes
   | res => res) ∧
  (evaluate env s [Let _ n e1 e2] =
   case fix_clock s (evaluate env s [e1]) of
   | (s, Rval vs) => evaluate (opt_bind n (HD vs) env) s [e2]
   | res => res) ∧
  (evaluate env s [Letrec _ funs e] =
   if ALL_DISTINCT (MAP FST funs)
   then evaluate (build_rec_env funs env env) s [e]
   else (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Extend_global _ n] =
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
                             | (INR(_,s,_,pes)) => (s.clock,exp3_size pes))`
  >> rpt strip_tac
  >> simp[dec_clock_def]
  >> imp_res_tac fix_clock_IMP
  >> rw[]);

val evaluate_ind = theorem"evaluate_ind"

val do_app_clock = Q.store_thm("do_app_clock",
  `exhSem$do_app s op vs = SOME(s',r) ==> s.clock = s'.clock`,
  rpt strip_tac THEN fs[do_app_cases] >> every_case_tac >>
  fs[LET_THM,semanticPrimitivesTheory.store_alloc_def,semanticPrimitivesTheory.store_assign_def] >> rw[])

val evaluate_clock = Q.store_thm("evaluate_clock",
  `(∀env (s1:'a state) e r s2. evaluate env s1 e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
   (∀env (s1:'a state) v pes r s2. evaluate_match env s1 v pes = (s2,r) ⇒ s2.clock ≤ s1.clock)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[dec_clock_def] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> fs[] >>
  imp_res_tac do_app_clock >> fs[]);

val fix_clock_evaluate = Q.store_thm("fix_clock_evaluate",
  `fix_clock s (evaluate env s e) = evaluate env s e`,
  Cases_on `evaluate env s e` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]);

val evaluate_def = save_thm("evaluate_def",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

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
