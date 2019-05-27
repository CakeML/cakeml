(*
  The formal semantics of flatLang
*)
open preamble flatLangTheory;
open semanticPrimitivesPropsTheory;

val _ = new_theory "flatSem";

(* The values of flatLang differ in that the closures do not environments for
 * global definitions.
 *
 * The semantics of flatLang differ in that there is no module environment menv, nor
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
    | Conv ((ctor_id # type_id) option) (v list)
    | Closure ((varN, v) alist) varN exp
    | Recclosure ((varN, v) alist) ((varN # varN # exp) list) varN
    | Loc num
    | Vectorv (v list)`;

val _ = Datatype`
  state = <|
    clock   : num;
    refs    : v store;
    ffi     : 'ffi ffi_state;
    globals : (v option) list
  |>`;

val _ = Datatype`
  environment = <|
    v : (varN, v) alist;
    (* The set of constructors that exist, according to their id, type and arity *)
    c : ((ctor_id # type_id) # num) set;
    (* T if all patterns are required to be exhaustive *)
    exh_pat : bool;
    (* T if constructors must be declared *)
    check_ctor : bool
  |>`;

val list_id_def = Define `
  list_id = 1n`;

val Boolv_def = Define`
  Boolv b = Conv (SOME (if b then true_tag else false_tag, SOME bool_id)) []`;

val Unitv_def = Define`
  Unitv check_ctor = Conv (if check_ctor then NONE else SOME (0,NONE)) []`;

val bind_exn_v_def = Define `
  bind_exn_v = Conv (SOME (bind_tag, NONE)) []`;

val chr_exn_v_def = Define `
  chr_exn_v = Conv (SOME (chr_tag, NONE)) []`;

val div_exn_v_def = Define `
  div_exn_v = Conv (SOME (div_tag, NONE)) []`;

val subscript_exn_v_def = Define `
  subscript_exn_v = Conv (SOME (subscript_tag, NONE)) []`;

val build_rec_env_def = Define `
  build_rec_env funs cl_env add_to_env =
    FOLDR (λ(f,x,e) env'. (f, Recclosure cl_env funs f) :: env')
      add_to_env funs`;

val ctor_same_type_def = Define `
  (ctor_same_type (SOME (_,t)) (SOME (_,t')) ⇔ t = t') ∧
  (ctor_same_type NONE NONE ⇔ T) ∧
  (ctor_same_type _ _ ⇔ F)`;

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

(* Do an application *)
val do_opapp_def = Define `
  do_opapp vs =
  case vs of
    | [Closure env n e; v] =>
      SOME ((n,v) :: env, e)
    | [Recclosure env funs n; v] =>
      if ALL_DISTINCT (MAP FST funs) then
        (case find_recfun n funs of
         | SOME (n,e) => SOME ((n,v) :: build_rec_env funs env env, e)
         | NONE => NONE)
      else NONE
    | _ => NONE`;

val v_to_list_def = Define `
  (v_to_list (Conv (SOME (cid, tid)) []) =
   if cid = nil_tag ∧ tid = SOME list_id then
     SOME []
   else NONE)
  ∧
  (v_to_list (Conv (SOME (cid, tid)) [v1;v2]) =
   if cid = cons_tag ∧ tid = SOME list_id then
     (case v_to_list v2 of
      | SOME vs => SOME (v1::vs)
      | NONE => NONE)
   else NONE)
  ∧
  (v_to_list _ = NONE)`;

val list_to_v_def = Define `
  (list_to_v [] = Conv (SOME (nil_tag, SOME list_id)) []) ∧
  (list_to_v (x::xs) =
    Conv (SOME (cons_tag, SOME list_id)) [x; list_to_v xs])`;

val v_to_char_list_def = Define `
 (v_to_char_list (Conv (SOME (cid, tid)) []) =
  if cid = nil_tag ∧ tid = SOME list_id then
    SOME []
  else NONE)
 ∧
 (v_to_char_list (Conv (SOME (cid, tid)) [Litv (Char c);v]) =
  if cid = cons_tag ∧ tid = SOME list_id then
    (case v_to_char_list v of
     | SOME cs => SOME (c::cs)
     | NONE => NONE)
  else NONE)
 ∧
 (v_to_char_list _ = NONE)`;

val vs_to_string_def = Define`
  (vs_to_string [] = SOME "") ∧
  (vs_to_string (Litv(StrLit s1)::vs) =
   case vs_to_string vs of
   | SOME s2 => SOME (s1++s2)
   | _ => NONE) ∧
  (vs_to_string _ = NONE)`;

val do_app_def = Define `
  do_app check_ctor s op (vs:flatSem$v list) =
  case (op, vs) of
  | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    if ((op = Divide) ∨ (op = Modulo)) ∧ (n2 = 0) then
      SOME (s, Rerr (Rraise div_exn_v))
    else
      SOME (s, Rval (Litv (IntLit (opn_lookup op n1 n2))))
  | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    SOME (s, Rval (Boolv (opb_lookup op n1 n2)))
  | (FP_top top, [Litv (Word64 w1); Litv (Word64 w2); Litv (Word64 w3)] =>
      SOME (s,Rval (Litv (Word64 (fp_top top w1 w2 w3)))))
  | (FP_bop bop, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME (s,Rval (Litv (Word64 (fp_bop bop w1 w2))))
  | (FP_uop uop, [Litv (Word64 w)]) =>
      SOME (s,Rval (Litv (Word64 (fp_uop uop w))))
  | (FP_cmp cmp, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME (s,Rval (Boolv (fp_cmp cmp w1 w2)))
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
     | SOME s' => SOME (s with refs := s', Rval (Unitv check_ctor))
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
      SOME (s, Rerr (Rraise subscript_exn_v))
    else
      let (s',lnum) =
        store_alloc (W8array (REPLICATE (Num (ABS n)) w)) s.refs
      in
        SOME (s with refs := s', Rval (Loc lnum))
  | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       if i < 0 then
         SOME (s, Rerr (Rraise subscript_exn_v))
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             SOME (s, Rerr (Rraise subscript_exn_v))
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
         SOME (s, Rerr (Rraise subscript_exn_v))
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             SOME (s, Rerr (Rraise subscript_exn_v))
           else
             (case store_assign lnum (W8array (LUPDATE w n ws)) s.refs of
              | NONE => NONE
              | SOME s' => SOME (s with refs := s', Rval (Unitv check_ctor)))
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
        NONE => Rerr (Rraise subscript_exn_v)
      | SOME cs => Rval (Litv(StrLit(cs)))))
  | (CopyStrAw8, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len);
                  Loc dst;Litv(IntLit dstoff)]) =>
      (case store_lookup dst s.refs of
        SOME (W8array ws) =>
          (case copy_array (str,off) len (SOME(ws_to_chars ws,dstoff)) of
            NONE => SOME (s, Rerr (Rraise subscript_exn_v))
          | SOME cs =>
            (case store_assign dst (W8array (chars_to_ws cs)) s.refs of
              SOME s' =>  SOME (s with refs := s', Rval (Unitv check_ctor))
            | _ => NONE))
      | _ => NONE)
  | (CopyAw8Str, [Loc src;Litv(IntLit off);Litv(IntLit len)]) =>
    (case store_lookup src s.refs of
      SOME (W8array ws) =>
      SOME (s,
        (case copy_array (ws,off) len NONE of
          NONE => Rerr (Rraise subscript_exn_v)
        | SOME ws => Rval (Litv(StrLit(ws_to_chars ws)))))
    | _ => NONE)
  | (CopyAw8Aw8, [Loc src;Litv(IntLit off);Litv(IntLit len);
                  Loc dst;Litv(IntLit dstoff)]) =>
    (case (store_lookup src s.refs, store_lookup dst s.refs) of
      (SOME (W8array ws), SOME (W8array ds)) =>
        (case copy_array (ws,off) len (SOME(ds,dstoff)) of
          NONE => SOME (s, Rerr (Rraise subscript_exn_v))
        | SOME ws =>
            (case store_assign dst (W8array ws) s.refs of
              SOME s' => SOME (s with refs := s', Rval (Unitv check_ctor))
            | _ => NONE))
    | _ => NONE)
  | (Ord, [Litv (Char c)]) =>
    SOME (s, Rval (Litv(IntLit(int_of_num(ORD c)))))
  | (Chr, [Litv (IntLit i)]) =>
    SOME (s,
          if (i < 0) ∨ (i > 255) then
            Rerr (Rraise chr_exn_v)
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
      SOME (s, Rerr (Rraise subscript_exn_v))
    else
      let n = (Num (ABS i)) in
        if n >= LENGTH str then
          SOME (s, Rerr (Rraise subscript_exn_v))
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
      SOME (s, Rerr (Rraise subscript_exn_v))
    else
      let n = (Num (ABS i)) in
        if n >= LENGTH vs then
          SOME (s, Rerr (Rraise subscript_exn_v))
        else
          SOME (s, Rval (EL n vs))
  | (Vlength, [Vectorv vs]) =>
    SOME (s, Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
  | (Aalloc, [Litv (IntLit n); v]) =>
    if n < 0 then
      SOME (s, Rerr (Rraise subscript_exn_v))
    else
      let (s',lnum) =
        store_alloc (Varray (REPLICATE (Num (ABS n)) v)) s.refs
      in
        SOME (s with refs := s', Rval (Loc lnum))
  | (Asub, [Loc lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s.refs of
     | SOME (Varray vs) =>
     if i < 0 then
       SOME (s, Rerr (Rraise subscript_exn_v))
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           SOME (s, Rerr (Rraise subscript_exn_v))
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
       SOME (s, Rerr (Rraise subscript_exn_v))
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           SOME (s, Rerr (Rraise subscript_exn_v))
         else
           (case store_assign lnum (Varray (LUPDATE v n vs)) s.refs of
            | NONE => NONE
            | SOME s' => SOME (s with refs := s', Rval (Unitv check_ctor)))
     | _ => NONE)
  | (ListAppend, [x1; x2]) =>
    (case (v_to_list x1, v_to_list x2) of
     | (SOME xs, SOME ys) => SOME (s, Rval (list_to_v (xs ++ ys)))
     | _ => NONE)
  | (ConfigGC, [Litv (IntLit n1); Litv (IntLit n2)]) =>
       SOME (s, Rval (Unitv check_ctor))
  | (FFI n, [Litv(StrLit conf); Loc lnum]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       (case call_FFI s.ffi n (MAP (λc. n2w(ORD c)) conf) ws of
        | FFI_final outcome => SOME(s, Rerr (Rabort (Rffi_error outcome)))
        | FFI_return t' ws' =>
          (case store_assign lnum (W8array ws') s.refs of
           | SOME s' => SOME (s with <| refs := s'; ffi := t'|>, Rval (Unitv check_ctor))
           | NONE => NONE))
     | _ => NONE)
  | (GlobalVarAlloc n, []) =>
    SOME (s with globals := s.globals ++ REPLICATE n NONE, Rval (Unitv check_ctor))
  | (GlobalVarInit n, [v]) =>
    if n < LENGTH s.globals ∧ IS_NONE (EL n s.globals) then
      SOME (s with globals := LUPDATE (SOME v) n s.globals, Rval (Unitv check_ctor))
    else
      NONE
  | (GlobalVarLookup n, []) =>
    if n < LENGTH s.globals ∧ IS_SOME (EL n s.globals) then
      SOME (s, Rval (THE (EL n s.globals)))
    else
      NONE
  | _ => NONE`;

val do_if_def = Define `
 (do_if v e1 e2 =
  if v = Boolv T then
    SOME e1
  else if v = Boolv F then
    SOME e2
  else
      NONE)`;

Theorem do_if_either_or:
   do_if v e1 e2 = SOME e ⇒ e = e1 ∨ e = e2
Proof
  simp [do_if_def]
  THEN1 (Cases_on `v = Boolv T`
  THENL [simp [],
    Cases_on `v = Boolv F` THEN simp []])
QED

val pat_bindings_def = Define `
  (pat_bindings Pany already_bound = already_bound) ∧
  (pat_bindings (Pvar n) already_bound = n::already_bound) ∧
  (pat_bindings (Plit l) already_bound = already_bound) ∧
  (pat_bindings (Pcon _ ps) already_bound = pats_bindings ps already_bound) ∧
  (pat_bindings (Pref p) already_bound = pat_bindings p already_bound) ∧
  (pats_bindings [] already_bound = already_bound) ∧
  (pats_bindings (p::ps) already_bound = pats_bindings ps (pat_bindings p already_bound))`;

val same_ctor_def = Define `
  same_ctor check_type n1 n2 ⇔
    if check_type then
      n1 = n2
    else
      FST n1 = FST n2`;

val pmatch_def = tDefine "pmatch" `
  (pmatch env s (Pvar x) v' bindings = (Match ((x,v') :: bindings))) ∧
  (pmatch env s flatLang$Pany v' bindings = Match bindings) ∧
  (pmatch env s (Plit l) (Litv l') bindings =
    if l = l' then
      Match bindings
    else if lit_same_type l l' then
      No_match
    else
      Match_type_error) ∧
  (pmatch env s (Pcon (SOME n) ps) (Conv (SOME n') vs) bindings =
    if env.check_ctor ∧
       ((n, LENGTH ps) ∉ env.c ∨ ~ctor_same_type (SOME n) (SOME n')) then
      Match_type_error
    else if same_ctor env.check_ctor n n' ∧ LENGTH ps = LENGTH vs then
      pmatch_list env s ps vs bindings
    else
      No_match) ∧
  (pmatch env s (Pcon NONE ps) (Conv NONE vs) bindings =
    if env.check_ctor ∧ LENGTH ps = LENGTH vs then
      pmatch_list env s ps vs bindings
    else
      Match_type_error) ∧
  (pmatch env s (Pref p) (Loc lnum) bindings =
    case store_lookup lnum s of
    | SOME (Refv v) => pmatch env s p v bindings
    | _ => Match_type_error) ∧
  (pmatch env _ _ _ bindings = Match_type_error) ∧
  (pmatch_list env s [] [] bindings = Match bindings) ∧
  (pmatch_list env s (p::ps) (v::vs) bindings =
    case pmatch env s p v bindings of
    | No_match => No_match
    | Match_type_error => Match_type_error
    | Match bindings' => pmatch_list env s ps vs bindings') ∧
  (pmatch_list env s _ _ bindings = Match_type_error)`
 (WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_size p
                                        | INR (a,x,ps,y,z) => pat1_size ps)` >>
  srw_tac [ARITH_ss] [terminationTheory.size_abbrevs, astTheory.pat_size_def]);

val dec_clock_def = Define`
dec_clock s = s with clock := s.clock -1`;

val fix_clock_def = Define `
  fix_clock s (s1,res) = (s1 with clock := MIN s.clock s1.clock,res)`;

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (s1,res) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val evaluate_def = tDefine "evaluate"`
  (evaluate (env:flatSem$environment) (s:'ffi flatSem$state) ([]:flatLang$exp list) = (s,Rval [])) ∧
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
   | (s, Rerr (Rraise v)) => evaluate_match env s v pes v
   | res => res) ∧
  (evaluate env s [Con _ NONE es] =
    if env.check_ctor then
      case evaluate env s (REVERSE es) of
      | (s, Rval vs) => (s,Rval [Conv NONE (REVERSE vs)])
      | res => res
    else
      (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Con _ (SOME cn) es] =
    if env.check_ctor ∧ (cn, LENGTH es) ∉ env.c then
      (s, Rerr (Rabort Rtype_error))
    else
      case evaluate env s (REVERSE es) of
      | (s, Rval vs) => (s, Rval [Conv (SOME cn) (REVERSE vs)])
      | res => res) ∧
  (evaluate env s [Var_local _ n] = (s,
   case ALOOKUP env.v n of
   | SOME v => Rval [v]
   | NONE => Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Fun _ n e] = (s, Rval [Closure env.v n e])) ∧
  (evaluate env s [App _ op es] =
   case fix_clock s (evaluate env s (REVERSE es)) of
   | (s, Rval vs) =>
       if op = flatLang$Opapp then
         (case flatSem$do_opapp (REVERSE vs) of
          | SOME (env', e) =>
            if s.clock = 0 then
              (s, Rerr (Rabort Rtimeout_error))
            else
              evaluate (env with v := env') (dec_clock s) [e]
          | NONE => (s, Rerr (Rabort Rtype_error)))
       else
       (case (do_app env.check_ctor s op (REVERSE vs)) of
        | NONE => (s, Rerr (Rabort Rtype_error))
        | SOME (s',r) => (s', list_result r))
   | res => res) ∧
  (evaluate env s [If _ e1 e2 e3] =
   case fix_clock s (evaluate env s [e1]) of
   | (s, Rval vs) =>
     (case do_if (HD vs) e2 e3 of
      | SOME e => evaluate env s [e]
      | NONE => (s, Rerr (Rabort Rtype_error)))
   | res => res) ∧
  (evaluate env s [Mat _ e pes] =
   case fix_clock s (evaluate env s [e]) of
   | (s, Rval v) =>
       evaluate_match env s (HD v) pes bind_exn_v
   | res => res) ∧
  (evaluate env s [Let _ n e1 e2] =
   case fix_clock s (evaluate env s [e1]) of
   | (s, Rval vs) => evaluate (env with v updated_by opt_bind n (HD vs)) s [e2]
   | res => res) ∧
  (evaluate env s [Letrec _ funs e] =
   if ALL_DISTINCT (MAP FST funs)
   then evaluate (env with v := build_rec_env funs env.v env.v) s [e]
   else (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate_match (env:flatSem$environment) s v [] err_v =
    if env.exh_pat then
      (s, Rerr(Rabort Rtype_error))
    else
      (s, Rerr(Rraise err_v))) ∧
  (evaluate_match env s v ((p,e)::pes) err_v =
   if ALL_DISTINCT (pat_bindings p []) then
     case pmatch env s.refs p v [] of
     | Match env_v' => evaluate (env with v := env_v' ++ env.v) s [e]
     | No_match => evaluate_match env s v pes err_v
     | _ => (s, Rerr(Rabort Rtype_error))
   else (s, Rerr(Rabort Rtype_error)))`
  (wf_rel_tac`inv_image ($< LEX $<)
                (λx. case x of (INL(_,s,es)) => (s.clock,exp6_size es)
                             | (INR(_,s,_,pes,_)) => (s.clock,exp3_size pes))`
  >> rpt strip_tac
  >> simp[dec_clock_def]
  >> imp_res_tac fix_clock_IMP
  >> imp_res_tac do_if_either_or
  >> rw[]);

val evaluate_ind = theorem"evaluate_ind";

val op_thms = { nchotomy = op_nchotomy, case_def = op_case_def};
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def};
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def};
val v_thms = { nchotomy = theorem "v_nchotomy", case_def = fetch "-" "v_case_def"};

val store_v_thms = { nchotomy = semanticPrimitivesTheory.store_v_nchotomy, case_def = semanticPrimitivesTheory.store_v_case_def};
val lit_thms = { nchotomy = astTheory.lit_nchotomy, case_def = astTheory.lit_case_def};
val eq_v_thms = { nchotomy = semanticPrimitivesTheory.eq_result_nchotomy, case_def = semanticPrimitivesTheory.eq_result_case_def};
val wz_thms = { nchotomy = astTheory.word_size_nchotomy, case_def = astTheory.word_size_case_def};

val result_thms = { nchotomy = semanticPrimitivesTheory.result_nchotomy, case_def = semanticPrimitivesTheory.result_case_def };
val ffi_result_thms = { nchotomy = ffiTheory.ffi_result_nchotomy, case_def = ffiTheory.ffi_result_case_def };
val err_thms = { nchotomy = semanticPrimitivesTheory.error_result_nchotomy, case_def = semanticPrimitivesTheory.error_result_case_def }

val eqs = LIST_CONJ (map prove_case_eq_thm
  [op_thms, list_thms, option_thms, v_thms, store_v_thms, lit_thms,
   eq_v_thms, wz_thms, result_thms, ffi_result_thms, err_thms])

val case_eq_thms = save_thm ("case_eq_thms", eqs)

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

val pair_lam_lem = Q.prove (
`!f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)`,
 srw_tac[][]);

val do_app_cases = save_thm ("do_app_cases",
``do_app cc st op vs = SOME (st',v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV));

Theorem do_app_const:
   do_app cc s op vs = SOME (s',r) ⇒ s.clock = s'.clock
Proof
  rw [do_app_cases] >>
  rw [] >>
  rfs []
QED

Theorem evaluate_clock:
   (∀env (s1:'a state) e r s2. evaluate env s1 e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
   (∀env (s1:'a state) v pes v_err r s2. evaluate_match env s1 v pes v_err = (s2,r) ⇒ s2.clock ≤ s1.clock)
Proof
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[dec_clock_def] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> imp_res_tac do_app_const >> fs[]
QED

Theorem fix_clock_evaluate:
   fix_clock s (evaluate env s e) = evaluate env s e
Proof
  Cases_on `evaluate env s e` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]
QED

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

val is_fresh_type_def = Define `
  is_fresh_type type_id env ⇔
    !ctor. ctor ∈ env.c ⇒ !arity id. ctor ≠ ((id, SOME type_id), arity)`;

val is_fresh_exn_def = Define `
  is_fresh_exn exn_id env ⇔
    !ctor. ctor ∈ env.c ⇒ !arity. ctor ≠ ((exn_id, NONE), arity)`;

val evaluate_dec_def = Define`
  (evaluate_dec env s (Dlet e) =
   case evaluate (env with v := []) s [e] of
   | (s, Rval x) =>
     if x = [Unitv env.check_ctor] then
       (s, {}, NONE)
     else
       (s, {}, SOME (Rabort Rtype_error))
   | (s, Rerr e) => (s, {}, SOME e)) ∧
  (evaluate_dec env s (Dtype id ctors) =
    if env.check_ctor then
      if is_fresh_type id env then
        (s,
         { ((idx, SOME id), arity) | ?max. lookup arity ctors = SOME max ∧ idx < max },
         NONE)
      else
        (s, {}, SOME (Rabort Rtype_error))
    else
      (s, {}, NONE)) ∧
  (evaluate_dec env s (Dexn id arity) =
    if env.check_ctor then
      if is_fresh_exn id env then
        (s, {((id, NONE), arity)}, NONE)
      else
        (s, {}, SOME (Rabort Rtype_error))
    else
      (s, {}, NONE))`;

val evaluate_decs_def = Define`
  (evaluate_decs env s [] = (s, {}, NONE)) ∧
  (evaluate_decs env s (d::ds) =
   case evaluate_dec env s d of
   | (s, new_ctors, NONE) =>
     (case evaluate_decs (env with c updated_by $UNION new_ctors) s ds of
      | (s, new_ctors', r) => (s, new_ctors' ∪ new_ctors, r))
   | (s, new_ctors, SOME e) => (s, new_ctors, SOME e))`;

val initial_state_def = Define `
  initial_state ffi k =
    <| clock   := k
     ; refs    := []
     ; ffi     := ffi
     ; globals := [] |>`;

val bool_ctors_def = Define `
  bool_ctors =
    { ((true_tag, SOME bool_id), 0n)
    ; ((false_tag, SOME bool_id), 0n) }`;

val list_ctors_def = Define `
  list_ctors =
    { ((cons_tag, SOME list_id), 2n)
    ; ((nil_tag, SOME list_id), 0n) }`;

val exn_ctors_def = Define `
  exn_ctors =
    { ((div_tag, NONE), 0n)
    ; ((chr_tag, NONE), 0n)
    ; ((subscript_tag, NONE), 0n)
    ; ((bind_tag, NONE), 0n) }`;

val _ = export_rewrites ["bool_ctors_def", "list_ctors_def", "exn_ctors_def"];

val initial_ctors_def = Define `
   initial_ctors = bool_ctors UNION list_ctors UNION exn_ctors`;

val initial_env_def = Define `
  initial_env exh_pat check_ctor =
    <| v          := []
     ; c          := initial_ctors
     ; exh_pat    := exh_pat
     ; check_ctor := check_ctor |>`

val semantics_def = Define`
  semantics exh_pat check_ctor ffi prog =
    if ∃k. (SND o SND) (evaluate_decs (initial_env exh_pat check_ctor)
                                      (initial_state ffi k) prog) =
           SOME (Rabort Rtype_error)
      then Fail
    else
    case some res.
      ∃k s r outcome x.
        evaluate_decs (initial_env exh_pat check_ctor)
                      (initial_state ffi k) prog = (s,x,r) ∧
        (case r of
         | SOME (Rabort (Rffi_error e)) => outcome = FFI_outcome e
         | SOME (Rabort _) => F
         | _ => outcome = Success) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList
             (FST (evaluate_decs (initial_env exh_pat check_ctor)
               (initial_state ffi k) prog)).ffi.io_events) UNIV))`;

val _ = map delete_const
  ["do_eq_UNION_aux","do_eq_UNION",
   "pmatch_UNION_aux","pmatch_UNION",
   "evaluate_UNION_aux","evaluate_UNION"];

val _ = export_theory();
