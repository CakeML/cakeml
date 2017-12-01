open preamble modLangTheory;
open semanticPrimitivesPropsTheory; (* for do_shift and others *)

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
    | Closure (env_ctor # (varN, v) alist) varN modLang$exp
    | Recclosure (env_ctor # (varN, v) alist) ((varN # varN # modLang$exp) list) varN
    | Loc num
    | Vectorv (v list)`;

val _ = Datatype`
  state = <|
    clock   : num;
    refs    : modSem$v store;
    ffi     : 'ffi ffi_state;
    defined_types : tid_or_exn set;
    (* Top level module names *)
    defined_mods : modN set;
    globals : (modSem$v option) list
  |>`;

val _ = Datatype`
  environment = <|
    c : env_ctor;
    v : (varN, modSem$v) alist
  |>`;

val _ = Define`
  Boolv b = Conv (SOME ((if b then "true" else "false"), TypeId (Short "bool"))) []`;

val build_conv_def = Define`
  build_conv (envC:env_ctor) cn vs =
  case cn of
  | NONE => SOME (Conv NONE vs)
  | SOME id =>
    (case nsLookup envC id of
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
                                         | INR (xs,ys) => v4_size xs)`);

val prim_exn_def = Define`
  prim_exn cn = Conv (SOME (cn, TypeExn (Short cn))) []`;

(* Do an application *)
val do_opapp_def = Define `
  do_opapp vs =
  case vs of
    | [Closure (cenv, env) n e; v] =>
      SOME (<|c:=cenv; v:=((n,v) :: env)|>, e)
    | [Recclosure (cenv, env) funs n; v] =>
      if ALL_DISTINCT (MAP FST funs) then
        (case find_recfun n funs of
         | SOME (n,e) =>
             SOME (<|c:=cenv; v:=((n,v) :: build_rec_env funs (cenv, env) env)|>, e)
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

val vs_to_string_def = Define`
  (vs_to_string [] = SOME "") ∧
  (vs_to_string (Litv(StrLit s1)::vs) =
   case vs_to_string vs of
   | SOME s2 => SOME (s1++s2)
   | _ => NONE) ∧
  (vs_to_string _ = NONE)`;

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
  | (FP_bop bop, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME ((s,t),Rval (Litv (Word64 (fp_bop bop w1 w2))))
  | (FP_uop uop, [Litv (Word64 w)]) =>
      SOME ((s,t),Rval (Litv (Word64 (fp_uop uop w))))
  | (FP_cmp cmp, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME ((s,t),Rval (Boolv (fp_cmp cmp w1 w2)))
  | (Opw wz op, [Litv w1; Litv w2]) =>
     (case do_word_op op wz w1 w2 of
          | NONE => NONE
          | SOME w => SOME ((s,t), Rval (Litv w)))
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
          SOME ((s,t), Rval (Litv (Char (EL n str))))
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
  | (ConfigGC, [Litv (IntLit n1); Litv (IntLit n2)]) =>
       SOME ((s,t), Rval (Conv NONE []))
  | (FFI n, [Litv(StrLit conf); Loc lnum]) =>
    (case store_lookup lnum s of
     | SOME (W8array ws) =>
       (case call_FFI t n (MAP (λc. n2w(ORD c)) conf) ws of
        | (t', ws') =>
          (case store_assign lnum (W8array ws') s of
           | SOME s' => SOME ((s', t'), Rval (Conv NONE []))
           | NONE => NONE))
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

val do_if_either_or = Q.store_thm("do_if_is_ether_or",
  `do_if v e1 e2 = SOME e ⇒ e = e1 ∨ e = e2`,
  simp [do_if_def]
  THEN1 (Cases_on `v = Boolv T`
  THENL [simp [],
    Cases_on `v = Boolv F` THEN simp []]))

val pmatch_def = tDefine"pmatch"`
(pmatch envC s (Pvar x) v' env = (Match ((x,v') :: env)))
/\
(pmatch envC s Pany v' env = Match env)
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
((case nsLookup envC n of
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

val dec_clock_def = Define`
dec_clock s = s with clock := s.clock -1`;

val fix_clock_def = Define `
  fix_clock s (s1,res) = (s1 with clock := MIN s.clock s1.clock,res)`;

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (s1,res) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val evaluate_def = tDefine"evaluate"`
  (evaluate (env:modSem$environment) (s:'ffi modSem$state) ([]:modLang$exp list) = (s,Rval [])) ∧
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
  (evaluate env s [Con _ cn es] =
   if do_con_check env.c cn (LENGTH es) then
     case evaluate env s (REVERSE es) of
     | (s, Rval vs) =>
       (s, case build_conv env.c cn (REVERSE vs) of
           | SOME v => Rval [v]
           | NONE => Rerr (Rabort Rtype_error))
     | res => res
   else (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Var_local _ n] = (s,
   case ALOOKUP env.v n of
   | SOME v => Rval [v]
   | NONE => Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Var_global _ n] = (s,
   if n < LENGTH s.globals ∧ IS_SOME (EL n s.globals)
   then Rval [THE (EL n s.globals)]
   else Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Fun _ n e] = (s, Rval [Closure (env.c,env.v) n e])) ∧
  (evaluate env s [App _ op es] =
   case fix_clock s (evaluate env s (REVERSE es)) of
   | (s, Rval vs) =>
       if op = Opapp then
         (case do_opapp (REVERSE vs) of
          | SOME (env', e) =>
            if s.clock = 0 then
              (s, Rerr (Rabort Rtimeout_error))
            else
              evaluate env' (dec_clock s) [e]
          | NONE => (s, Rerr (Rabort Rtype_error)))
       else
       (case (do_app (s.refs,s.ffi) op (REVERSE vs)) of
        | NONE => (s, Rerr (Rabort Rtype_error))
        | SOME ((refs',ffi'),r) => (s with <|refs:=refs';ffi:=ffi'|>, list_result r))
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
       evaluate_match env s (HD v) pes
         (Conv (SOME ("Bind", (TypeExn (Short "Bind")))) [])
   | res => res) ∧
  (evaluate env s [Let _ n e1 e2] =
   case fix_clock s (evaluate env s [e1]) of
   | (s, Rval vs) => evaluate (env with v updated_by opt_bind n (HD vs)) s [e2]
   | res => res) ∧
  (evaluate env s [Letrec _ funs e] =
   if ALL_DISTINCT (MAP FST funs)
   then evaluate (env with v := build_rec_env funs (env.c,env.v) env.v) s [e]
   else (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate_match env s v [] err_v = (s, Rerr(Rraise err_v))) ∧
  (evaluate_match env s v ((p,e)::pes) err_v =
   if ALL_DISTINCT (pat_bindings p []) then
     case pmatch env.c s.refs p v [] of
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

val evaluate_ind = theorem"evaluate_ind"

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
     (s, if LENGTH vs = n then Rval (nsEmpty,vs)
         else Rerr (Rabort Rtype_error))
   | (s, Rval _) => (s, Rerr (Rabort Rtype_error))
   | (s, Rerr e) => (s, Rerr e)) ∧
  (evaluate_dec env s (Dletrec funs) =
     (s, Rval (nsEmpty, MAP (λ(f,x,e). Closure (env.c,[]) x e) funs))) ∧
  (evaluate_dec env s (Dtype mn tds) =
   let new_tdecs = type_defs_to_new_tdecs mn tds in
   if check_dup_ctors tds ∧ DISJOINT new_tdecs s.defined_types ∧
      ALL_DISTINCT (MAP (λ(tvs,tn,ctors). tn) tds)
   then (s with defined_types updated_by ($UNION new_tdecs),
         Rval (build_tdefs mn tds, []))
   else (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate_dec env s (Dexn mn cn ts) =
   if TypeExn (mk_id mn cn) ∈ s.defined_types
   then (s,Rerr (Rabort Rtype_error))
   else (s with defined_types updated_by ($INSERT (TypeExn (mk_id mn cn))),
         Rval (nsSing cn (LENGTH ts, TypeExn (mk_id mn cn)),[])))`;

val evaluate_decs_def = Define`
  (evaluate_decs env s [] = (s, nsEmpty, [], NONE)) ∧
  (evaluate_decs env s (d::ds) =
   case evaluate_dec env s d of
   | (s, Rval (new_tds,new_env)) =>
     (case evaluate_decs
             (env with c updated_by nsAppend new_tds)
             (s with globals updated_by (λg. g ++ MAP SOME new_env))
             ds of
      | (s, new_tds', new_env', r) => (s, nsAppend new_tds' new_tds, new_env ++ new_env', r))
   | (s, Rerr e) => (s, nsEmpty, [], SOME e))`;

val update_mod_state_def = Define `
  update_mod_state (mn:modN option) mods =
    case mn of
      NONE => mods
    | SOME mn => mn INSERT mods`;

val dec_to_dummy_env_def = Define `
  (dec_to_dummy_env (modLang$Dlet n e) = n) ∧
  (dec_to_dummy_env (Dletrec funs) = (LENGTH funs)) ∧
  (dec_to_dummy_env _ = 0)`;

val decs_to_dummy_env_def = Define `
  (decs_to_dummy_env [] = 0) ∧
  (decs_to_dummy_env (d::ds) = (decs_to_dummy_env ds + dec_to_dummy_env d))`;

val decs_to_types_def = Define `
  decs_to_types ds =
    FLAT (MAP (λd.
        (case d of
            Dtype mn tds => MAP (λ(tvs,tn,ctors). tn) tds
          | _ => [] ))
     ds)`;

val no_dup_types_def = Define `
  no_dup_types ds = ALL_DISTINCT (decs_to_types ds)`;

val prompt_mods_ok_def = Define `
  (prompt_mods_ok mn ds ⇔
    (case mn of
       NONE => LENGTH ds < 2
     | _ => T) ∧
    EVERY (λd.
      (case d of
          Dtype (mn'::_) _ => SOME mn' = mn
        | Dexn (mn'::_) _ _ => SOME mn' = mn
        | Dtype [] _ => mn = NONE
        | Dexn [] _ _ => mn = NONE
        | _ => T))
    ds)`;

val evaluate_prompt_def = Define`
  evaluate_prompt env s (Prompt mn ds) =
  if no_dup_types ds ∧ prompt_mods_ok mn ds ∧ mn ∉ IMAGE SOME s.defined_mods then
  let (s, cenv, genv, r) = evaluate_decs env s ds in
    (s with defined_mods updated_by update_mod_state mn,
     option_fold nsLift cenv mn,
     MAP SOME genv ++ (if r = NONE then [] else GENLIST (K NONE) (decs_to_dummy_env ds - LENGTH genv)),
     r)
  else (s, option_fold nsLift nsEmpty mn, [], SOME (Rabort Rtype_error))`;

val evaluate_prompts_def = Define`
  (evaluate_prompts env s [] = (s, nsEmpty, [], NONE)) ∧
  (evaluate_prompts env s (prompt::prompts) =
   case evaluate_prompt env s prompt of
   | (s', cenv, genv, NONE) =>
     (case evaluate_prompts
           (env with c updated_by nsAppend cenv)
           (s' with globals := s.globals ++ genv)
           prompts of
      | (s, cenv', genv', r) => (s, nsAppend cenv' cenv, genv ++ genv', r))
   | res => res)`;

val prog_to_mods_def = Define `
  (prog_to_mods [] = []) ∧
  (prog_to_mods (modLang$Prompt NONE ds :: mods) = prog_to_mods mods) ∧
  (prog_to_mods (modLang$Prompt (SOME mn) ds :: mods) = mn::prog_to_mods mods)`;

val no_dup_mods_def = Define `
  no_dup_mods prompts mods ⇔
    ALL_DISTINCT (prog_to_mods prompts) /\
    DISJOINT (set (prog_to_mods prompts)) mods`;

val prog_to_top_types_def = Define `
  prog_to_top_types prompts =
    FLAT (MAP (λprompt. case prompt of modLang$Prompt NONE ds => decs_to_types ds | _ => []) prompts)`;

val no_dup_top_types_def = Define `
  no_dup_top_types prompts tids ⇔
    ALL_DISTINCT (prog_to_top_types prompts) ∧
    DISJOINT (LIST_TO_SET (MAP (\tn. TypeId (Short tn)) (prog_to_top_types prompts))) tids`;

val evaluate_prog_def = Define `
 (evaluate_prog env s prompts =
  if modSem$no_dup_mods prompts s.defined_mods ∧
     no_dup_top_types prompts s.defined_types ∧
     EVERY (λp. (case p of Prompt mn ds => prompt_mods_ok mn ds)) prompts
  then let (s,_,_,r) = evaluate_prompts env s prompts in (s,r)
  else (s, SOME(Rabort Rtype_error)))`;

val semantics_def = Define`
  semantics env st prog =
    if ∃k. SND (evaluate_prog env (st with clock := k) prog) = SOME (Rabort Rtype_error)
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate_prog env (st with clock := k) prog = (s,r) ∧
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
