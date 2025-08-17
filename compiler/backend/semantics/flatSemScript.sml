(*
  The formal semantics of flatLang
*)
Theory flatSem
Ancestors
  flatLang semanticPrimitivesProps fpSem[qualified] evaluate
Libs
  preamble


val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(* The values of flatLang differ from source semantic values in that
 * the closures do not carry environments for global definitions.
 *
 * The semantics of flatLang differ from source in that there is no
 * module environment menv, nor are top-level bindings added to the
 * normal env, thus when a closure is created, only locals bindings
 * are put into it. There is a global environment genv, which is just
 * a list of the top-level bindings seen so far, with the older
 * bindings nearer the head. Global variable reference expressions
 * simply index into global environment. Top-level let rec
 * declarations evaluate to closures, rather than to recursive
 * closures, since the recursion can be handled through the genv. The
 * expressions bound to top-level lets must evaluate to a tuple with
 * exactly as many things in it as the number of bindings that the let
 * will bind.
 *)

val _ = temp_tight_equality();

Datatype:
  (* 'v *) environment = <|
    v : (varN, 'v) alist
  |>
End

Datatype:
  v =
    | Litv lit
    | Conv ((ctor_id # type_id) option) (v list)
    | Closure (v environment) varN exp
    | Recclosure (v environment) ((varN # varN # exp) list) varN
    | Loc bool num
    | Vectorv (v list)
End

Datatype:
  install_config =
   <| compile : 'c -> flatLang$dec list -> (word8 list # word64 list # 'c) option
    ; compile_oracle : num -> 'c # flatLang$dec list
    |>
End

Datatype:
  state = <|
    clock   : num;
    refs    : v store;
    ffi     : 'ffi ffi_state;
    globals : (v option) list;
    (* The set of constructors that exist, according to their id, type and arity *)
    c : ((ctor_id # type_id) # num) set;
    (* eval or install mode *)
    eval_config : 'c install_config
  |>
End

val s = ``s:('c,'ffi) flatSem$state``

Definition list_id_def:
  list_id = 1n
End

Definition Boolv_def:
  Boolv b = Conv (SOME (if b then true_tag else false_tag, SOME bool_id)) []
End

Definition Unitv_def:
  Unitv = Conv NONE []
End

Definition bind_exn_v_def:
  bind_exn_v = Conv (SOME (bind_tag, NONE)) []
End

Definition chr_exn_v_def:
  chr_exn_v = Conv (SOME (chr_tag, NONE)) []
End

Definition div_exn_v_def:
  div_exn_v = Conv (SOME (div_tag, NONE)) []
End

Definition subscript_exn_v_def:
  subscript_exn_v = Conv (SOME (subscript_tag, NONE)) []
End

Definition build_rec_env_def:
  build_rec_env funs cl_env add_to_env =
    FOLDR (λ(f,x,e) env'. (f, Recclosure cl_env funs f) :: env')
      add_to_env funs
End

Definition ctor_same_type_def:
  (ctor_same_type (SOME (_,t)) (SOME (_,t')) ⇔ t = t') ∧
  (ctor_same_type NONE NONE ⇔ T) ∧
  (ctor_same_type _ _ ⇔ F)
End

Definition do_eq_def:
  (do_eq (Litv l1) (Litv l2) =
   if lit_same_type l1 l2 then Eq_val (l1 = l2)
   else Eq_type_error)
  ∧
  (do_eq (Loc b1 l1) (Loc b2 l2) =
    (if b1 ∧ b2 then Eq_val (l1 = l2) else Eq_type_error))
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
  (do_eq_list _ _ = Eq_val F)
End

(* Do an application *)
Definition do_opapp_def:
  do_opapp vs =
  case vs of
    | [Closure env n e; v] =>
      SOME (env with v updated_by (\env. (n,v) :: env), e)
    | [Recclosure env funs n; v] =>
      if ALL_DISTINCT (MAP FST funs) then
        (case find_recfun n funs of
         | SOME (n,e) => SOME (env with v :=
             (n,v) :: build_rec_env funs env env.v, e)
         | NONE => NONE)
      else NONE
    | _ => NONE
End

Definition v_to_list_def:
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
  (v_to_list _ = NONE)
End

Definition list_to_v_def:
  (list_to_v [] = Conv (SOME (nil_tag, SOME list_id)) []) ∧
  (list_to_v (x::xs) =
    Conv (SOME (cons_tag, SOME list_id)) [x; list_to_v xs])
End

Definition v_to_char_list_def:
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
 (v_to_char_list _ = NONE)
End

Definition vs_to_string_def:
  (vs_to_string [] = SOME "") ∧
  (vs_to_string (Litv(StrLit s1)::vs) =
   case vs_to_string vs of
   | SOME s2 => SOME (s1++s2)
   | _ => NONE) ∧
  (vs_to_string _ = NONE)
End

Definition v_to_bytes_def:
  v_to_bytes lv = some ns. v_to_list lv = SOME (MAP (Litv o Word8) ns)
End

Definition v_to_words_def:
  v_to_words lv = some ns. v_to_list lv = SOME (MAP (Litv o Word64) ns)
End

Definition do_app_def:
  do_app s op (vs:flatSem$v list) =
  case (op, vs) of
  | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    if ((op = Divide) ∨ (op = Modulo)) ∧ (n2 = 0) then
      SOME (s, Rerr (Rraise div_exn_v))
    else
      SOME (s, Rval (Litv (IntLit (opn_lookup op n1 n2))))
  | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
    SOME (s, Rval (Boolv (opb_lookup op n1 n2)))
  | (FP_top t_op, [Litv (Word64 w1); Litv (Word64 w2); Litv (Word64 w3)] =>
      SOME (s,Rval (Litv (Word64 (fp_top_comp t_op w1 w2 w3)))))
  | (FP_bop bop, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME (s,Rval (Litv (Word64 (fp_bop_comp bop w1 w2))))
  | (FP_uop uop, [Litv (Word64 w)]) =>
      SOME (s,Rval (Litv (Word64 (fp_uop_comp uop w))))
  | (FP_cmp cmp, [Litv (Word64 w1); Litv (Word64 w2)]) =>
      SOME (s,Rval (Boolv (fp_cmp_comp cmp w1 w2)))
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
  | (Opassign, [Loc _ lnum; v]) =>
    (case store_assign lnum (Refv v) s.refs of
     | SOME s' => SOME (s with refs := s', Rval Unitv)
     | NONE => NONE)
  | (Opref, [v]) =>
    let (s',n) = (store_alloc (Refv v) s.refs) in
      SOME (s with refs := s', Rval (Loc T n))
  | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
    if n < 0 then
      SOME (s, Rerr (Rraise subscript_exn_v))
    else
      let (s',lnum) =
        store_alloc (W8array (REPLICATE (Num (ABS n)) w)) s.refs
      in
        SOME (s with refs := s', Rval (Loc T lnum))
  | (Aw8sub, [Loc _ lnum; Litv (IntLit i)]) =>
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
  | (Aw8sub_unsafe, [Loc _ lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       if i < 0 then
         NONE
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             NONE
           else
             SOME (s, Rval (Litv (Word8 (EL n ws))))
     | _ => NONE)
  | (Aw8length, [Loc _ n]) =>
    (case store_lookup n s.refs of
     | SOME (W8array ws) =>
       SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
     | _ => NONE)
  | (Aw8update, [Loc _ lnum; Litv(IntLit i); Litv(Word8 w)]) =>
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
              | SOME s' => SOME (s with refs := s', Rval Unitv))
     | _ => NONE)
  | (Aw8update_unsafe, [Loc _ lnum; Litv(IntLit i); Litv(Word8 w)]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       if i < 0 then
         NONE
       else
         let n = (Num (ABS i)) in
           if n >= LENGTH ws then
             NONE
           else
             (case store_assign lnum (W8array (LUPDATE w n ws)) s.refs of
              | NONE => NONE
              | SOME s' => SOME (s with refs := s', Rval Unitv))
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
                  Loc _ dst;Litv(IntLit dstoff)]) =>
      (case store_lookup dst s.refs of
        SOME (W8array ws) =>
          (case copy_array (str,off) len (SOME(ws_to_chars ws,dstoff)) of
            NONE => SOME (s, Rerr (Rraise subscript_exn_v))
          | SOME cs =>
            (case store_assign dst (W8array (chars_to_ws cs)) s.refs of
              SOME s' =>  SOME (s with refs := s', Rval Unitv)
            | _ => NONE))
      | _ => NONE)
  | (CopyAw8Str, [Loc _ src;Litv(IntLit off);Litv(IntLit len)]) =>
    (case store_lookup src s.refs of
      SOME (W8array ws) =>
      SOME (s,
        (case copy_array (ws,off) len NONE of
          NONE => Rerr (Rraise subscript_exn_v)
        | SOME ws => Rval (Litv(StrLit(ws_to_chars ws)))))
    | _ => NONE)
  | (CopyAw8Aw8, [Loc _ src;Litv(IntLit off);Litv(IntLit len);
                  Loc _ dst;Litv(IntLit dstoff)]) =>
    (case (store_lookup src s.refs, store_lookup dst s.refs) of
      (SOME (W8array ws), SOME (W8array ds)) =>
        (case copy_array (ws,off) len (SOME(ds,dstoff)) of
          NONE => SOME (s, Rerr (Rraise subscript_exn_v))
        | SOME ws =>
            (case store_assign dst (W8array ws) s.refs of
              SOME s' => SOME (s with refs := s', Rval Unitv)
            | _ => NONE))
    | _ => NONE)
  | (Aw8xor_unsafe, [Loc _ dst; Litv (StrLit str_arg)]) =>
    (case store_lookup dst s.refs of
     | SOME (W8array ds) =>
         (case xor_bytes (MAP (n2w o ORD) str_arg) ds of
          | NONE => NONE
          | SOME new_bs =>
              (case store_assign dst (W8array new_bs) s.refs of
               | NONE => NONE
               | SOME s' => SOME (s with refs := s', Rval Unitv)))
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
  | (Explode, [Litv (StrLit str)]) =>
    (SOME (s, Rval (list_to_v (MAP (\c. Litv (Char c)) str))))
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
        SOME (s with refs := s', Rval (Loc T lnum))
  | (AallocFixed, vs) =>
    let (s',lnum) =
      store_alloc (Varray vs) s.refs
    in
      SOME (s with refs := s', Rval (Loc T lnum))
  | (Asub, [Loc _ lnum; Litv (IntLit i)]) =>
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
  | (Asub_unsafe, [Loc _ lnum; Litv (IntLit i)]) =>
    (case store_lookup lnum s.refs of
     | SOME (Varray vs) =>
     if i < 0 then
       NONE
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           NONE
         else
           SOME (s, Rval (EL n vs))
     | _ => NONE)
  | (Alength, [Loc _ n]) =>
      (case store_lookup n s.refs of
       | SOME (Varray ws) =>
         SOME (s,Rval (Litv (IntLit(int_of_num(LENGTH ws)))))
       | _ => NONE)
  | (Aupdate, [Loc _ lnum; Litv (IntLit i); v]) =>
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
            | SOME s' => SOME (s with refs := s', Rval Unitv))
     | _ => NONE)
  | (Aupdate_unsafe, [Loc _ lnum; Litv (IntLit i); v]) =>
    (case store_lookup lnum s.refs of
     | SOME (Varray vs) =>
     if i < 0 then
       NONE
     else
       let n = (Num (ABS i)) in
         if n >= LENGTH vs then
           NONE
         else
           (case store_assign lnum (Varray (LUPDATE v n vs)) s.refs of
            | NONE => NONE
            | SOME s' => SOME (s with refs := s', Rval Unitv))
     | _ => NONE)
  | (ListAppend, [x1; x2]) =>
    (case (v_to_list x1, v_to_list x2) of
     | (SOME xs, SOME ys) => SOME (s, Rval (list_to_v (xs ++ ys)))
     | _ => NONE)
  | (ConfigGC, [Litv (IntLit n1); Litv (IntLit n2)]) =>
       SOME (s, Rval Unitv)
  | (FFI n, [Litv(StrLit conf); Loc _ lnum]) =>
    (case store_lookup lnum s.refs of
     | SOME (W8array ws) =>
       (case call_FFI s.ffi (ExtCall n) (MAP (λc. n2w(ORD c)) conf) ws of
        | FFI_final outcome => SOME(s, Rerr (Rabort (Rffi_error outcome)))
        | FFI_return t' ws' =>
          (case store_assign lnum (W8array ws') s.refs of
           | SOME s' => SOME (s with <| refs := s'; ffi := t'|>, Rval Unitv)
           | NONE => NONE))
     | _ => NONE)
  | (GlobalVarAlloc n, []) =>
    SOME (s with globals := s.globals ++ REPLICATE n NONE, Rval Unitv)
  | (GlobalVarInit n, [v]) =>
    if n < LENGTH s.globals ∧ IS_NONE (EL n s.globals) then
      SOME (s with globals := LUPDATE (SOME v) n s.globals, Rval Unitv)
    else
      NONE
  | (GlobalVarLookup n, []) =>
    if n < LENGTH s.globals ∧ IS_SOME (EL n s.globals) then
      SOME (s, Rval (THE (EL n s.globals)))
    else
      NONE
  | (TagLenEq n l, [Conv (SOME (tag,_)) xs]) =>
    SOME (s, Rval (Boolv (tag = n /\ LENGTH xs = l)))
  | (LenEq l, [Conv _ xs]) =>
    SOME (s, Rval (Boolv (LENGTH xs = l)))
 | (El n, [Conv _ vs]) =>
    (if n < LENGTH vs then SOME (s, Rval (EL n vs)) else NONE)
  | (El n, [Loc _ p]) =>
    (if n <> 0 then NONE else
       case store_lookup p s.refs of
       | SOME (Refv v) => SOME (s,Rval v)
       | _ => NONE)
  | (Id, [v1]) =>
    SOME (s, Rval v1)
  | (ThunkOp th_op, vs) =>
     (case (th_op,vs) of
      | (AllocThunk m, [v]) =>
          (let (r,n) = store_alloc (Thunk m v) s.refs in
             SOME (s with refs := r, Rval (Loc F n)))
      | (UpdateThunk m, [Loc _ lnum; v]) =>
          (case store_assign lnum (Thunk m v) s.refs of
           | SOME r => SOME (s with refs := r, Rval (Conv NONE []))
           | NONE => NONE)
      | _ => NONE)
  | _ => NONE
End

Definition do_if_def:
 (do_if v e1 e2 =
  if v = Boolv T then
    SOME e1
  else if v = Boolv F then
    SOME e2
  else
      NONE)
End

Theorem do_if_either_or:
   do_if v e1 e2 = SOME e ⇒ e = e1 ∨ e = e2
Proof
  simp [do_if_def]
  THEN1 (Cases_on `v = Boolv T`
  THENL [simp [],
    Cases_on `v = Boolv F` THEN simp []])
QED

Inductive pmatch_stamps_ok:
  ( (* exception constructors *)
    ((cn, NONE), n_ps) ∈ c
  ==> pmatch_stamps_ok c (SOME (cn, NONE)) (SOME (cn', NONE)) n_ps n_vs) ∧
  ( (* constructors *)
    ((cn, SOME ty_id), n_ps) ∈ c ∧
        ty_id = ty_id' ∧ MEM (cn, n_ps) ctor_set ∧ MEM (cn', n_vs) ctor_set
  ==> pmatch_stamps_ok c (SOME (cn, (SOME (ty_id, ctor_set))))
    (SOME (cn', SOME ty_id')) n_ps n_vs) ∧
  ( (* tuples *)
    n_ps = n_vs
  ==> pmatch_stamps_ok c NONE NONE n_ps n_vs)
End

Definition pmatch_def:
  (pmatch s (Pvar x) v' bindings =
    (Match ((x,v') :: bindings))) ∧
  (pmatch s flatLang$Pany v' bindings = Match bindings) ∧
  (pmatch s (Plit l) (Litv l') bindings =
    if l = l' then
      Match bindings
    else if lit_same_type l l' then
      No_match
    else
      Match_type_error) ∧
  (pmatch s (Pcon stmp ps) (Conv stmp' vs) bindings =
    if ~ pmatch_stamps_ok s.c stmp stmp' (LENGTH ps) (LENGTH vs) then
      Match_type_error
    else if OPTION_MAP FST stmp = OPTION_MAP FST stmp' ∧
            LENGTH ps = LENGTH vs then
      pmatch_list s ps vs bindings
    else
      No_match) ∧
  (pmatch s (Pas p i) v bindings =
    pmatch s p v ((i,v)::bindings)) ∧
  (pmatch s (Pref p) (Loc _ lnum) bindings =
    case store_lookup lnum s.refs of
    | SOME (Refv v) => pmatch s p v bindings
    | _ => Match_type_error) ∧
  (pmatch _ _ _ bindings = Match_type_error) ∧
  (pmatch_list s [] [] bindings = Match bindings) ∧
  (pmatch_list s (p::ps) (v::vs) bindings =
    case pmatch s p v bindings of
    | Match_type_error => Match_type_error
    | Match bindings' => pmatch_list s ps vs bindings'
    | No_match =>
      case pmatch_list s ps vs bindings of
      | Match_type_error => Match_type_error
      | _ => No_match) ∧
  (pmatch_list s _ _ bindings = Match_type_error)
Termination
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,p,y,z) => pat_size p
                                        | INR (x,ps,y,z) => list_size pat_size ps)`
  \\ simp []
End

Definition pmatch_rows_def:
  pmatch_rows [] s v = No_match /\
  pmatch_rows ((p,e)::pes) s v =
    case pmatch s p v [] of
    | Match_type_error => Match_type_error
    | No_match => pmatch_rows pes s v
    | Match env =>
       case pmatch_rows pes s v of
       | Match_type_error => Match_type_error
       | _ => Match (env, p, e)
End

Definition dec_clock_def:
  dec_clock s = s with clock := s.clock -1
End

Definition fix_clock_def:
  fix_clock s (s1,res) = (s1 with clock := MIN s.clock s1.clock,res)
End

Triviality fix_clock_IMP:
  fix_clock s x = (s1,res) ==> s1.clock <= s.clock
Proof
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []
QED

Theorem pmatch_rows_Match_exp_size:
  !pes s v env e.
    pmatch_rows pes s v = Match (env',p,e) ==>
    exp_size e < exp3_size pes
Proof
  Induct \\ fs [pmatch_rows_def,FORALL_PROD,CaseEq"match_result",CaseEq"bool"]
  \\ rw [] \\ res_tac \\ fs [exp_size_def]
QED

Definition is_fresh_type_def:
  is_fresh_type type_id ctors ⇔
    !ctor. ctor ∈ ctors ⇒ !arity id. ctor ≠ ((id, SOME type_id), arity)
End

Definition is_fresh_exn_def:
  is_fresh_exn exn_id ctors ⇔
    !ctor. ctor ∈ ctors ⇒ !arity. ctor ≠ ((exn_id, NONE), arity)
End

Definition do_eval_def:
  do_eval (vs :v list) eval_config =
  (case vs of
    | [v1; v2] =>
      (case (v_to_bytes v1, v_to_words v2) of
       | (SOME bytes, SOME data) =>
         let (st,decs) = eval_config.compile_oracle 0 in
         let new_oracle = shift_seq 1 eval_config.compile_oracle in
         (case eval_config.compile st decs of
          | SOME (bytes',data',st') =>
            if bytes = bytes' ∧ data = data' ∧ decs <> [] ∧
                FST (new_oracle 0) = st' then
              SOME (decs, eval_config with compile_oracle := new_oracle, Unitv)
            else NONE
          | _ => NONE)
       | _ => NONE)
    | _ => NONE)
End

Datatype:
  dest_thunk_ret
    = BadRef
    | NotThunk
    | IsThunk thunk_mode v
End

Definition dest_thunk_def:
  dest_thunk [Loc _ n] st =
    (case store_lookup n st of
     | NONE => BadRef
     | SOME (Thunk Evaluated v) => IsThunk Evaluated v
     | SOME (Thunk NotEvaluated v) => IsThunk NotEvaluated v
     | SOME _ => NotThunk) ∧
  dest_thunk vs st = NotThunk
End

Definition update_thunk_def:
  update_thunk [Loc _ n] st [v] =
    (case dest_thunk [v] st of
     | NotThunk => store_assign n (Thunk Evaluated v) st
     | _ => NONE) ∧
  update_thunk _ st _ = NONE
End

Definition AppUnit_def:
  AppUnit x = flatLang$App None Opapp [x; Con None NONE []]
End

Definition evaluate_def:
  (evaluate (env:v flatSem$environment) ^s ([]:flatLang$exp list) =
    (s,Rval [])) ∧
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
   | (s, Rerr (Rraise v)) =>
       (case pmatch_rows pes s v of
        | Match_type_error => (s, Rerr (Rabort Rtype_error))
        | No_match => (s, Rerr (Rraise v))
        | Match (env', p', e') =>
           if ALL_DISTINCT (pat_bindings p' [])
           then evaluate (env with v := env' ++ env.v) s [e']
           else (s, Rerr (Rabort Rtype_error)))
   | res => res) ∧
  (evaluate env s [Con _ NONE es] =
    case evaluate env s (REVERSE es) of
      | (s, Rval vs) => (s,Rval [Conv NONE (REVERSE vs)])
      | res => res) ∧
  (evaluate env s [Con _ (SOME cn) es] =
    if (cn, LENGTH es) ∈ s.c
    then
      (case evaluate env s (REVERSE es) of
      | (s, Rval vs) => (s, Rval [Conv (SOME cn) (REVERSE vs)])
      | res => res)
    else
      (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Var_local _ n] = (s,
   case ALOOKUP env.v n of
   | SOME v => Rval [v]
   | NONE => Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Fun _ n e] = (s, Rval [Closure env n e])) ∧
  (evaluate env s [App _ op es] =
   case fix_clock s (evaluate env s (REVERSE es)) of
   | (s, Rval vs) =>
       if op = flatLang$Opapp then
         (case flatSem$do_opapp (REVERSE vs) of
          | SOME (env', e) =>
            if s.clock = 0 then
              (s, Rerr (Rabort Rtimeout_error))
            else
              evaluate env' (dec_clock s) [e]
          | NONE => (s, Rerr (Rabort Rtype_error)))
       else if op = flatLang$Eval then
         (case do_eval (REVERSE vs) s.eval_config of
            | SOME (decs, eval_config, retv) =>
              let s = s with <| eval_config := eval_config |> in
              if s.clock = 0 then
                (s, Rerr (Rabort Rtimeout_error))
              else (case evaluate_decs (dec_clock s) decs of
               | (s, NONE) => (s, Rval [retv])
               | (s, SOME e) => (s, Rerr e))
          | NONE => (s, Rerr (Rabort Rtype_error)))
       else if op = ThunkOp ForceThunk then
         (case dest_thunk vs s.refs of
          | BadRef => (s, Rerr (Rabort Rtype_error))
          | NotThunk => (s, Rerr (Rabort Rtype_error))
          | IsThunk Evaluated v => (s, Rval [v])
          | IsThunk NotEvaluated f =>
             if s.clock = 0 then
               (s, Rerr (Rabort Rtimeout_error))
             else
               case evaluate <| v := [("f",f)] |> (dec_clock s)
                      [AppUnit (Var_local None "f")] of
               | (s, Rval vs2) =>
                   (case update_thunk vs s.refs vs2 of
                    | NONE => (s, Rerr (Rabort Rtype_error))
                    | SOME refs => (s with refs := refs, Rval vs2))
               | (s, Rerr e) => (s, Rerr e))
       else
        (case (do_app s op (REVERSE vs)) of
         | NONE => (s, Rerr (Rabort Rtype_error))
         | SOME (s',r) => (s', evaluate$list_result r))
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
       (case pmatch_rows pes s (HD v) of
        | Match_type_error => (s, Rerr (Rabort Rtype_error))
        | No_match => (s, Rerr (Rraise bind_exn_v))
        | Match (env', p', e') =>
           if ALL_DISTINCT (pat_bindings p' [])
           then evaluate (env with v := env' ++ env.v) s [e']
           else (s, Rerr (Rabort Rtype_error)))
   | res => res) ∧
  (evaluate env s [Let _ n e1 e2] =
   case fix_clock s (evaluate env s [e1]) of
   | (s, Rval vs) => evaluate (env with v updated_by opt_bind n (HD vs)) s [e2]
   | res => res) ∧
  (evaluate env s [Letrec _ funs e] =
   if ALL_DISTINCT (MAP FST funs)
   then evaluate (env with v := build_rec_env funs env env.v) s [e]
   else (s, Rerr(Rabort Rtype_error))) ∧
  (evaluate_dec s (Dlet e) =
   case evaluate <| v := [] |> s [e] of
   | (s, Rval x) =>
     if x = [Unitv] then
       (s, NONE)
     else
       (s, SOME (Rabort Rtype_error))
   | (s, Rerr e) => (s, SOME e)) ∧
  (evaluate_dec s (Dtype id ctors) =
    if is_fresh_type id s.c then
      let new_c = { ((idx, SOME id), arity) |
          ?max. lookup arity ctors = SOME max ∧ idx < max } in
      (s with c updated_by $UNION new_c, NONE)
    else
      (s, SOME (Rabort Rtype_error))) ∧
  (evaluate_dec s (Dexn id arity) =
    if is_fresh_exn id s.c then
      (s with c updated_by $UNION {((id, NONE), arity)}, NONE)
    else
      (s, SOME (Rabort Rtype_error))) ∧
  (evaluate_decs s [] = (s, NONE)) ∧
  (evaluate_decs s (d::ds) =
   case fix_clock s (evaluate_dec s d) of
   | (s, NONE) => evaluate_decs s ds
   | (s, SOME e) => (s, SOME e))
Termination
  wf_rel_tac `inv_image ($< LEX $<)
    (\x. case x of
        | INL (env,s,exps) => (s.clock, SUM (MAP exp_size exps) + LENGTH exps)
        | (INR(INL(s,d))) => (s.clock,dec_size d + 1)
        | (INR(INR(s,ds))) => (s.clock,SUM (MAP dec_size ds) + LENGTH ds + 1))`
  \\ simp [exp_size_def, dec_clock_def]
  \\ rw []
  \\ imp_res_tac fix_clock_IMP
  \\ imp_res_tac do_if_either_or
  \\ imp_res_tac pmatch_rows_Match_exp_size
  \\ fs []
  \\ simp [MAP_REVERSE, SUM_REVERSE, exp6_size]
End

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

Theorem case_eq_thms =
  eqs

Triviality pair_case_eq:
  pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v
Proof
  Cases_on `x` >>
 srw_tac[][]
QED

Triviality pair_lam_lem:
  !f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)
Proof
  srw_tac[][]
QED

Theorem do_app_cases =
  ``do_app st op vs = SOME (st',v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem, CaseEq "thunk_op"] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs])

Theorem do_app_const:
   do_app s op vs = SOME (s',r) ⇒ s.clock = s'.clock ∧ s.c = s'.c
Proof
  rw [do_app_cases] >>
  rw [] >>
  rfs []
QED

Theorem evaluate_clock:
   (∀env ^s e r s2. evaluate env s e = (s2,r) ⇒ s2.clock ≤ s.clock) ∧
   (∀^s e r s2. evaluate_dec s e = (s2,r) ⇒ s2.clock ≤ s.clock) ∧
   (∀^s e r s2. evaluate_decs s e = (s2,r) ⇒ s2.clock ≤ s.clock)
Proof
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[dec_clock_def] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> imp_res_tac do_app_const >> fs[]
QED

Theorem fix_clock_evaluate:
   fix_clock s (evaluate env s e) = evaluate env s e /\
   fix_clock s (evaluate_dec s d) = evaluate_dec s d /\
   fix_clock s (evaluate_decs s ds) = evaluate_decs s ds
Proof
  Cases_on `evaluate env s e` \\ fs [fix_clock_def]
  \\ Cases_on `evaluate_dec s d` \\ fs [fix_clock_def]
  \\ Cases_on `evaluate_decs s ds` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]
QED

Theorem evaluate_def[compute,allow_rebind] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_def;

Theorem evaluate_ind[allow_rebind] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind;

Definition bool_ctors_def:
  bool_ctors =
    { ((true_tag, SOME bool_id), 0n)
    ; ((false_tag, SOME bool_id), 0n) }
End

Definition list_ctors_def:
  list_ctors =
    { ((cons_tag, SOME list_id), 2n)
    ; ((nil_tag, SOME list_id), 0n) }
End

Definition exn_ctors_def:
  exn_ctors =
    { ((div_tag, NONE), 0n)
    ; ((chr_tag, NONE), 0n)
    ; ((subscript_tag, NONE), 0n)
    ; ((bind_tag, NONE), 0n) }
End

val _ = export_rewrites ["bool_ctors_def", "list_ctors_def", "exn_ctors_def"];

Definition initial_ctors_def:
   initial_ctors = bool_ctors UNION list_ctors UNION exn_ctors
End

Definition initial_state_def:
  initial_state ffi k ec =
    <| clock       := k
     ; refs        := []
     ; ffi         := ffi
     ; globals     := []
     ; c           := initial_ctors
     ; eval_config := ec
     |> :('c,'ffi) flatSem$state
End

Definition semantics_def:
  semantics (ec:'c install_config) (ffi:'ffi ffi_state) prog =
    if ∃k. SND (evaluate_decs (initial_state ffi k ec) prog)
           = SOME (Rabort Rtype_error)
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate_decs (initial_state ffi k ec) prog = (s,r) ∧
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
             (FST (evaluate_decs (initial_state ffi k ec) prog)).ffi.io_events)
               UNIV))
End

val _ = map (can delete_const)
  ["do_eq_UNION_aux","do_eq_UNION",
   "pmatch_UNION_aux","pmatch_UNION"];

