open preamble conLangTheory backend_commonTheory;
open semanticPrimitivesPropsTheory; (* for do_shift and others *)

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

val _ = Datatype`
  environment = <|
    v   : (varN, conSem$v) alist;
    exh : exh_ctors_env
  |>`;

val _ = Datatype`
  state = <|
    clock   : num;
    refs    : conSem$v store;
    globals : (conSem$v option) list;
    ffi     : 'ffi ffi_state
  |>`;

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

val list_to_v_def = Define `
  list_to_v []      = Conv (SOME (nil_tag, TypeId (Short "list"))) [] /\
  list_to_v (x::xs) = Conv (SOME (cons_tag, TypeId (Short "list"))) [x; list_to_v xs]
  `;

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

val vs_to_string_def = Define`
  (vs_to_string [] = SOME "") ∧
  (vs_to_string (Litv(StrLit s1)::vs) =
   case vs_to_string vs of
   | SOME s2 => SOME (s1++s2)
   | _ => NONE) ∧
  (vs_to_string _ = NONE)`;

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
  | (Opw wz op, [Litv w1; Litv w2]) =>
     (case do_word_op op wz w1 w2 of
          | NONE => NONE
          | SOME w => SOME ((s,t), Rval (Litv w)))
  | (FP_bop bop, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME ((s,t),Rval (Litv (Word64 (fp_bop bop w1 w2))))
  | (FP_uop uop, [Litv (Word64 w)]) =>
      SOME ((s,t),Rval (Litv (Word64 (fp_uop uop w))))
  | (FP_cmp cmp, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME ((s,t),Rval (Boolv (fp_cmp cmp w1 w2)))
  | (Shift wz sh n, [Litv w]) =>
      (case do_shift sh n wz w of
         | NONE => NONE
         | SOME w => SOME ((s,t), Rval (Litv w)))
  | (Equality, [v1; v2]) =>
    (case do_eq v1 v2 of
     | Eq_type_error => NONE
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
  | (WordFromInt wz, [Litv (IntLit i)]) =>
    SOME ((s,t), Rval (Litv (do_word_from_int wz i)))
  | (WordToInt wz, [Litv w]) =>
    (case do_word_to_int wz w of
      | NONE => NONE
      | SOME i => SOME ((s,t), Rval (Litv (IntLit i))))
  | (CopyStrStr, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len)]) =>
      SOME ((s,t),
      (case copy_array (str,off) len NONE of
        NONE => Rerr (Rraise (prim_exn "Subscript"))
      | SOME cs => Rval (Litv(StrLit(cs)))))
  | (CopyStrAw8, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len);
                  Loc dst;Litv(IntLit dstoff)]) =>
      (case store_lookup dst s of
        SOME (W8array ws) =>
          (case copy_array (str,off) len (SOME(ws_to_chars ws,dstoff)) of
            NONE => SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
          | SOME cs =>
            (case store_assign dst (W8array (chars_to_ws cs)) s of
              SOME s' =>  SOME ((s',t), Rval (Conv NONE []))
            | _ => NONE))
      | _ => NONE)
  | (CopyAw8Str, [Loc src;Litv(IntLit off);Litv(IntLit len)]) =>
    (case store_lookup src s of
      SOME (W8array ws) =>
      SOME ((s,t),
        (case copy_array (ws,off) len NONE of
          NONE => Rerr (Rraise (prim_exn "Subscript"))
        | SOME ws => Rval (Litv(StrLit(ws_to_chars ws)))))
    | _ => NONE)
  | (CopyAw8Aw8, [Loc src;Litv(IntLit off);Litv(IntLit len);
                  Loc dst;Litv(IntLit dstoff)]) =>
    (case (store_lookup src s, store_lookup dst s) of
      (SOME (W8array ws), SOME (W8array ds)) =>
        (case copy_array (ws,off) len (SOME(ds,dstoff)) of
          NONE => SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
        | SOME ws =>
            (case store_assign dst (W8array ws) s of
              SOME s' => SOME ((s',t), Rval (Conv NONE []))
            | _ => NONE))
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
  | (Strsub, [Litv (StrLit str); Litv (IntLit i)]) =>
    if i < 0 then
      SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
    else
      let n = (Num (ABS i)) in
        if n >= LENGTH str then
          SOME ((s,t), Rerr (Rraise (prim_exn "Subscript")))
        else
          SOME ((s,t), Rval (Litv(Char(EL n str))))
  | (Strlen, [Litv (StrLit str)]) =>
    SOME ((s,t), Rval (Litv(IntLit(int_of_num(STRLEN str)))))
  | (Strcat, [v]) =>
      (case v_to_list v of
        SOME vs =>
          (case vs_to_string vs of
            SOME str =>
              SOME ((s,t), Rval (Litv(StrLit str)))
          | _ => NONE)
      | _ => NONE)
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
  | (ListAppend, [x1; x2]) =>
      (case (v_to_list x1, v_to_list x2) of
         (SOME xs, SOME ys) => SOME ((s, t), Rval (list_to_v (xs ++ ys)))
       | _ => NONE)
  | (ConfigGC, [Litv (IntLit n1); Litv (IntLit n2)]) =>
       SOME ((s,t), Rval (Conv NONE []))
  | (FFI n, [Litv (StrLit conf); Loc lnum]) =>
    (case store_lookup lnum s of
     | SOME (W8array ws) =>
       (case call_FFI t n (MAP (λc. n2w(ORD c)) conf) ws of
        | (t', ws') =>
          (case store_assign lnum (W8array ws') s of
           | SOME s' => SOME ((s', t'), Rval (Conv NONE []))
           | NONE => NONE))
     | _ => NONE)
  | _ => NONE
  )`;

val pmatch_def = tDefine"pmatch"`
  (pmatch exh s (Pvar x) v' env = (Match ((x,v')::env)))
  ∧
  (pmatch exh s Pany v' env = Match env)
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
  (pat_bindings Pany already_bound = already_bound)
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

val dec_clock_def = Define`
dec_clock s = s with clock := s.clock -1`;

val fix_clock_def = Define `
  fix_clock s (s1,res) = (s1 with clock := MIN s.clock s1.clock,res)`

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (s1,res) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val evaluate_def = tDefine "evaluate"`
  (evaluate (env:conSem$environment) (s:'ffi conSem$state) ([]:conLang$exp list) = (s,Rval [])) ∧
  (evaluate env s (e1::e2::es) =
    case fix_clock s (evaluate env s [e1]) of
    | (s, Rval v) =>
        (case evaluate env s (e2::es) of
         | (s, Rval vs) => (s, Rval (HD v::vs))
         | res => res)
    | res => res) ∧
  (evaluate env s [(Lit _ l)] = (s, Rval [Litv l])) ∧
  (evaluate env s [Raise _ e] =
   case evaluate env s [e] of
   | (s, Rval v) => (s, Rerr (Rraise (HD v)))
   | res => res) ∧
  (evaluate env s [Handle _ e pes] =
   case fix_clock s (evaluate env s [e]) of
   | (s, Rerr (Rraise v)) => evaluate_match env s v pes v
   | res => res) ∧
  (evaluate env s [Con _ tag es] =
   case evaluate env s (REVERSE es) of
   | (s, Rval vs) => (s, Rval [Conv tag (REVERSE vs)])
   | res => res) ∧
  (evaluate env s [Var_local _ n] = (s,
   case ALOOKUP env.v n of
   | SOME v => Rval [v]
   | NONE => Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Var_global _ n] = (s,
   if n < LENGTH s.globals ∧ IS_SOME (EL n s.globals)
   then Rval [THE (EL n s.globals)]
   else Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Fun _ n e] = (s, Rval [Closure env.v n e])) ∧
  (evaluate env s [App _ op es] =
   case fix_clock s (evaluate env s (REVERSE es)) of
   | (s, Rval vs) =>
       if op = Op Opapp then
         (case do_opapp (REVERSE vs) of
          | SOME (env', e) =>
            if s.clock = 0 then
              (s, Rerr (Rabort Rtimeout_error))
            else
              evaluate (env with v := env') (dec_clock s) [e]
          | NONE => (s, Rerr (Rabort Rtype_error)))
       else
       (case (do_app (s.refs,s.ffi) op (REVERSE vs)) of
        | NONE => (s, Rerr (Rabort Rtype_error))
        | SOME ((refs',ffi'),r) => (s with <|refs:=refs';ffi:=ffi'|>, list_result r))
   | res => res) ∧
  (evaluate env s [Mat _ e pes] =
   case fix_clock s (evaluate env s [e]) of
   | (s, Rval v) =>
       evaluate_match env s (HD v) pes
         (Conv (SOME (bind_tag, (TypeExn (Short "Bind")))) [])
   | res => res) ∧
  (evaluate env s [Let _ n e1 e2] =
   case fix_clock s (evaluate env s [e1]) of
   | (s, Rval vs) => evaluate (env with v updated_by opt_bind n (HD vs)) s [e2]
   | res => res) ∧
  (evaluate env s [Letrec _ funs e] =
   if ALL_DISTINCT (MAP FST funs)
   then evaluate (env with v := build_rec_env funs env.v env.v) s [e]
   else (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Extend_global _ n] = (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate_match env s v [] err_v = (s, Rerr(Rraise err_v))) ∧
  (evaluate_match env s v ((p,e)::pes) err_v =
   if ALL_DISTINCT (pat_bindings p []) then
     case pmatch env.exh s.refs p v env.v of
     | Match env' => evaluate (env with v := env') s [e]
     | No_match => evaluate_match env s v pes err_v
     | _ => (s, Rerr(Rabort Rtype_error))
   else (s, Rerr(Rabort Rtype_error)))`
  (wf_rel_tac`inv_image ($< LEX $<)
                (λx. case x of (INL(_,s,es)) => (s.clock,exp6_size es)
                             | (INR(_,s,_,pes,_)) => (s.clock,exp3_size pes))`
  >> rpt strip_tac
  >> simp[dec_clock_def]
  >> imp_res_tac fix_clock_IMP
  >> rw[]);

val evaluate_ind = theorem"evaluate_ind";

val evaluate_clock = Q.store_thm("evaluate_clock",
  `(∀env (s1:'a state) e r s2. evaluate env s1 e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
   (∀env (s1:'a state) v pes v_err r s2. evaluate_match env s1 v pes v_err = (s2,r) ⇒ s2.clock ≤ s1.clock)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[dec_clock_def] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> fs[]);

val fix_clock_evaluate = Q.store_thm("fix_clock_evaluate",
  `fix_clock s (evaluate env s e) = evaluate env s e`,
  Cases_on `evaluate env s e` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]);

val evaluate_def = save_thm("evaluate_def",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

val evaluate_dec_def = Define`
  (evaluate_dec env s (Dlet n e) =
   case evaluate (env with v := []) s [e] of
   | (s, Rval [Conv NONE vs]) =>
     (s, if LENGTH vs = n then Rval vs
         else Rerr (Rabort Rtype_error))
   | (s, Rval _) => (s, Rerr (Rabort Rtype_error))
   | res => res) ∧
  (evaluate_dec env s (Dletrec funs) =
     (s, Rval (MAP (λ(f,x,e). Closure [] x e) funs)))`;

val evaluate_decs_def = Define`
  (evaluate_decs env s [] = (s, [], NONE)) ∧
  (evaluate_decs env s (d::ds) =
   case evaluate_dec env s d of
   | (s, Rval new_env) =>
     (case evaluate_decs env (s with globals updated_by (λg. g ++ MAP SOME new_env)) ds of
      | (s, new_env', r) => (s, new_env ++ new_env', r))
   | (s, Rerr e) => (s, [], SOME e))`;

val evaluate_prompt_def = Define`
  (evaluate_prompt env s (Prompt ds) =
   case evaluate_decs env s ds of
   | (s,env,NONE) => (s,MAP SOME env,NONE)
   | (s,env,SOME err) => (s,MAP SOME env ++ GENLIST (K NONE) (num_defs ds - LENGTH env),SOME err))`;

val evaluate_prog_def = Define`
  (evaluate_prog env s [] = (s, [], NONE)) ∧
  (evaluate_prog env s (prompt::prompts) =
   case evaluate_prompt env s prompt of
   | (s', genv, NONE) =>
     (case evaluate_prog env (s' with globals := s.globals ++ genv) prompts of
      | (s, genv', r) => (s, genv ++ genv', r))
   | res => res)`;

val semantics_def = Define`
  semantics env st prog =
    if ∃k. SND (SND (evaluate_prog env (st with clock := k) prog)) = SOME (Rabort Rtype_error)
      then Fail
    else
    case some res.
      ∃k s g r outcome.
        evaluate_prog env (st with clock := k) prog = (s,g,r) ∧
        (case s.ffi.final_event of
         | NONE => (∀a. r ≠ SOME (Rabort a)) ∧ outcome = Success
         | SOME e => outcome = FFI_outcome e) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (FST (evaluate_prog env (st with clock := k) prog)).ffi.io_events) UNIV))`;

val _ = map delete_const
  ["do_eq_UNION_aux","do_eq_UNION",
   "pmatch_UNION_aux","pmatch_UNION",
   "evaluate_UNION_aux","evaluate_UNION"];

val _ = export_theory()
