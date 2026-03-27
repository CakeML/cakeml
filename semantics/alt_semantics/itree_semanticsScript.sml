(*
  An itree-based semantics for CakeML
*)
Theory itree_semantics
Ancestors
  namespace ast ffi semanticPrimitives smallStep fpSem itree
Libs
  BasicProvers dep_rewrite

(******************** do_app ********************)

Datatype:
  app_result = Rval v | Rraise v
End

Overload flit[local] = “λw. Litv (Float64 w)”

Definition thunk_op_def:
  thunk_op (s: v store_v list) th_op vs =
    case (th_op,vs) of
    | (AllocThunk m, [v]) =>
        (let (s',n) = store_alloc (Thunk m v) s in
           SOME (s', Rval (Loc F n)))
    | (UpdateThunk m, [Loc _ lnum; v]) =>
        (case store_assign lnum (Thunk m v) s of
         | SOME s' => SOME (s', Rval (Conv NONE []))
         | NONE => NONE)
    | _ => NONE
End

Definition do_app_def:
  do_app s op vs = case (op, vs) of
      (ListAppend, [x1; x2]) => (
        case (v_to_list x1, v_to_list x2) of
          (SOME xs, SOME ys) => SOME (s, Rval (list_to_v (xs ++ ys)))
        | _ => NONE
      )
    | (Shift W8 op n, [Litv (Word8 w)]) =>
        SOME (s, Rval (Litv (Word8 (shift8_lookup op w n))))
    | (Shift W64 op n, [Litv (Word64 w)]) =>
        SOME (s, Rval (Litv (Word64 (shift64_lookup op w n))))
    | (Equality, [v1; v2]) =>
        (case do_eq v1 v2 of
            Eq_type_error => NONE
          | Eq_val b => SOME (s, Rval (Boolv b))
        )
    | (Arith a ty, vs) =>
        (if EVERY (check_type ty) vs then
           (case do_arith a ty vs of
            | SOME (INR res) => SOME (s, Rval res)
            | SOME (INL exn) => SOME (s, Rraise exn)
            | NONE           => NONE)
         else NONE)
    | (FromTo ty1 ty2, [v]) =>
        (if check_type ty1 v then
           (case do_conversion v ty1 ty2 of
            | SOME (INR res) => SOME (s, Rval res)
            | SOME (INL exn) => SOME (s, Rraise exn)
            | NONE           => NONE)
         else NONE)
    | (Test test test_ty, [v1; v2]) =>
        (case do_test test test_ty v1 v2 of
            Eq_type_error => NONE
          | Eq_val b => SOME (s, Rval (Boolv b))
        )
    | (Opassign, [Loc _ lnum; v]) =>
        (case store_assign lnum (Refv v) s of
            SOME s' => SOME (s', Rval (Conv NONE []))
          | NONE => NONE
        )
    | (Opref, [v]) =>
        let (s',n) = (store_alloc (Refv v) s) in
          SOME (s', Rval (Loc T n))
    | (Opderef, [Loc _ n]) =>
        (case store_lookup n s of
            SOME (Refv v) => SOME (s,Rval v)
          | _ => NONE
        )
    | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
        if n <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let (s',lnum) =
            (store_alloc (W8array (REPLICATE (Num (ABS (I n))) w)) s)
          in
            SOME (s', Rval (Loc T lnum))
    | (Aw8sub, [Loc _ lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                SOME (s, Rraise sub_exn_v)
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH ws then
                    SOME (s, Rraise sub_exn_v)
                  else
                    SOME (s, Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8sub_unsafe, [Loc _ lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (W8array ws) =>
              if i <( 0 : int) then
                NONE
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH ws then
                    NONE
                  else
                    SOME (s, Rval (Litv (Word8 (EL n ws))))
          | _ => NONE
        )
    | (Aw8length, [Loc _ n]) =>
        (case store_lookup n s of
            SOME (W8array ws) =>
              SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aw8update, [Loc _ lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              SOME (s, Rraise sub_exn_v)
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH ws then
                  SOME (s, Rraise sub_exn_v)
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (Aw8update_unsafe, [Loc _ lnum; Litv(IntLit i); Litv(Word8 w)]) =>
        (case store_lookup lnum s of
          SOME (W8array ws) =>
            if i <( 0 : int) then
              NONE
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH ws then
                  NONE
                else
                  (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (CopyStrStr, [Litv(StrLit strng);Litv(IntLit off);Litv(IntLit len)]) =>
        SOME (s,
        (case copy_array (explode strng,off) len NONE of
          NONE => Rraise sub_exn_v
        | SOME cs => Rval (Litv(StrLit(implode (cs))))
        ))
    | (CopyStrAw8, [Litv(StrLit strng);Litv(IntLit off);Litv(IntLit len);
                    Loc _ dst;Litv(IntLit dstoff)]) =>
        (case store_lookup dst s of
          SOME (W8array ws) =>
            (case copy_array (explode strng,off) len (SOME(ws_to_chars ws,dstoff)) of
              NONE => SOME (s, Rraise sub_exn_v)
            | SOME cs =>
              (case store_assign dst (W8array (chars_to_ws cs)) s of
                SOME s' =>  SOME (s', Rval (Conv NONE []))
              | _ => NONE
              )
            )
        | _ => NONE
        )
    | (CopyAw8Str, [Loc _ src;Litv(IntLit off);Litv(IntLit len)]) =>
      (case store_lookup src s of
        SOME (W8array ws) =>
        SOME (s,
          (case copy_array (ws,off) len NONE of
            NONE => Rraise sub_exn_v
          | SOME ws => Rval (Litv(StrLit(implode(ws_to_chars ws))))
          ))
      | _ => NONE
      )
    | (CopyAw8Aw8, [Loc _ src;Litv(IntLit off);Litv(IntLit len);
                    Loc _ dst;Litv(IntLit dstoff)]) =>
      (case (store_lookup src s, store_lookup dst s) of
        (SOME (W8array ws), SOME (W8array ds)) =>
          (case copy_array (ws,off) len (SOME(ds,dstoff)) of
            NONE => SOME (s, Rraise sub_exn_v)
          | SOME ws =>
              (case store_assign dst (W8array ws) s of
                SOME s' => SOME (s', Rval (Conv NONE []))
              | _ => NONE
              )
          )
      | _ => NONE
      )
    | (XorAw8Str_unsafe, [Loc _ dst; Litv (StrLit str_arg)]) =>
        (case store_lookup dst s of
          SOME (W8array bs) =>
            (case xor_bytes (MAP (n2w o ORD) (explode str_arg)) bs of
             | NONE => NONE
             | SOME new_bs =>
                case store_assign dst (W8array new_bs) s of
                | NONE => NONE
                | SOME s' => SOME (s', Rval (Conv NONE [])))
        | _ => NONE
        )
    | (Implode, [v]) =>
          (case v_to_char_list v of
            SOME ls =>
              SOME (s, Rval (Litv (StrLit (implode ls))))
          | NONE => NONE
          )
    | (Explode, [v]) =>
          (case v of
            Litv (StrLit strng) =>
              SOME (s, Rval (list_to_v (MAP (\ c .  Litv (Char c)) (explode strng))))
          | _ => NONE
          )
    | (Strsub, [Litv (StrLit strng); Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let n = (Num (ABS (I i))) in
            if n >= strlen strng then
              SOME (s, Rraise sub_exn_v)
            else
              SOME (s, Rval (Litv (Char (EL n (explode strng)))))
    | (Strlen, [Litv (StrLit strng)]) =>
        SOME (s, Rval (Litv(IntLit(int_of_num(strlen strng)))))
    | (Strcat, [v]) =>
        (case v_to_list v of
          SOME vs =>
            (case vs_to_string vs of
              SOME strng =>
                SOME (s, Rval (Litv(StrLit strng)))
            | _ => NONE
            )
        | _ => NONE
        )
    | (VfromList, [v]) =>
          (case v_to_list v of
              SOME vs =>
                SOME (s, Rval (Vectorv vs))
            | NONE => NONE
          )
    | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let n = (Num (ABS (I i))) in
            if n >= LENGTH vs then
              SOME (s, Rraise sub_exn_v)
            else
              SOME (s, Rval (EL n vs))
    | (Vsub_unsafe, [Vectorv vs; Litv (IntLit i)]) =>
        if 0 ≤ i ∧ Num i < LENGTH vs then
          SOME (s, Rval (EL (Num i) vs))
        else
          NONE
    | (Vlength, [Vectorv vs]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
    | (Aalloc, [Litv (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let (s',lnum) =
            (store_alloc (Varray (REPLICATE (Num (ABS (I n))) v)) s)
          in
            SOME (s', Rval (Loc T lnum))
    | (AallocEmpty, [Conv NONE []]) =>
        let (s',lnum) = (store_alloc (Varray []) s) in
          SOME (s', Rval (Loc T lnum))
    | (AallocFixed, vs) =>
        let (s',lnum) =
          (store_alloc (Varray vs) s)
        in
          SOME (s', Rval (Loc T lnum))
    | (Asub, [Loc _ lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                SOME (s, Rraise sub_exn_v)
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH vs then
                    SOME (s, Rraise sub_exn_v)
                  else
                    SOME (s, Rval (EL n vs))
          | _ => NONE
        )
    | (Asub_unsafe, [Loc _ lnum; Litv (IntLit i)]) =>
        (case store_lookup lnum s of
            SOME (Varray vs) =>
              if i <( 0 : int) then
                NONE
              else
                let n = (Num (ABS (I i))) in
                  if n >= LENGTH vs then
                    NONE
                  else
                    SOME (s, Rval (EL n vs))
          | _ => NONE
        )
    | (Alength, [Loc _ n]) =>
        (case store_lookup n s of
            SOME (Varray ws) =>
              SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aupdate, [Loc _ lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              SOME (s, Rraise sub_exn_v)
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH vs then
                  SOME (s, Rraise sub_exn_v)
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (Aupdate_unsafe, [Loc _ lnum; Litv (IntLit i); v]) =>
        (case store_lookup lnum s of
          SOME (Varray vs) =>
            if i <( 0 : int) then
              NONE
            else
              let n = (Num (ABS (I i))) in
                if n >= LENGTH vs then
                  NONE
                else
                  (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                      NONE => NONE
                    | SOME s' => SOME (s', Rval (Conv NONE []))
                  )
        | _ => NONE
      )
    | (ConfigGC, [Litv (IntLit i); Litv (IntLit j)]) =>
        SOME (s, Rval (Conv NONE []))
    | (Env_id, [Env env (gen, id)]) => SOME (s,
            Rval (Conv NONE [nat_to_v gen; nat_to_v id]))
    | (Env_id, [Conv NONE [gen; id]]) => SOME (s,
            Rval (Conv NONE [gen; id]))
    | (ThunkOp th_op, vs) => thunk_op s th_op vs
    | _ => NONE
End


(******************** expressions ********************)

Datatype:
  ctxt_frame = Craise
             | Chandle ((pat # exp) list)
             | Capp op (v list) (exp list)
             | Cforce num
             | Clog lop exp
             | Cif exp exp
             | Cmat_check ((pat # exp) list) v
             | Cmat ((pat # exp) list) v
             | Clet (varN option) exp
             | Ccon (((modN, conN) id) option) (v list) (exp list)
             | Ctannot ast_t
             | Clannot locs
End

Type "ctxt"[pp] = ``:ctxt_frame # v sem_env``;

Type "small_state"[pp] = ``:v sem_env # v store # exp_val_exn # ctxt list``;

Datatype:
  estep_result = Estep small_state
               | Effi ffiname (word8 list) (word8 list) num
                        (v sem_env) (v store) (ctxt list)
               | Edone
               | Etype_error
End

Definition push_def:
  push env s e c cs : estep_result = Estep (env, s, Exp e, (c,env)::cs)
End

Definition return_def:
  return env s v c : estep_result = Estep (env, s, Val v, c)
End

Definition application_def:
  application op env s vs c : estep_result =
   case getOpClass op of
     FunApp =>
       (case do_opapp vs of
          SOME (env,e) => (Estep (env, s, Exp e, c):estep_result)
        | NONE => Etype_error)
   | Force =>
      (case vs of
         [Loc b n] => (
            case dest_thunk [Loc b n] s of
            | BadRef => Etype_error
            | NotThunk => Etype_error
            | IsThunk Evaluated v => return env s v c
            | IsThunk NotEvaluated f =>
                return env s f
                  ((Capp Opapp [Conv NONE []] [], env)::(Cforce n, env)::c))
        | _ => Etype_error)
   | _ =>
       case op of
       | FFI n => (
         case vs of
           [Litv (StrLit conf); Loc _ lnum] => (
           case store_lookup lnum s of
             SOME (W8array ws) =>
               if n = «» then Estep (env, s, Val $ Conv NONE [], c)
               else Effi (ExtCall n)
                         (MAP (λc. n2w $ ORD c) (explode conf))
                         ws lnum env s c
           | _ => Etype_error)
         | _ => Etype_error)
       | _ =>
           (case do_app s op vs of
              SOME (s', Rraise v) => Estep (env, s, Exn v,c)
              | SOME (s', Rval v) => return env s' v c
              | NONE => Etype_error )
End

Definition continue_def:
  continue s v [] : estep_result = Edone ∧
  continue s v ((Craise, env)::cs) = Estep (env, s, Exn v, cs) ∧
  continue s v ((Chandle pes, env)::c) = return env s v c ∧
  continue s v ((Capp op vs [], env) :: c) = application op env s (v::vs) c ∧
  continue s v ((Capp op vs (e::es), env) :: c) = push env s e (Capp op (v::vs) es) c ∧
  continue s v ((Cforce n, env) :: c) = (
    case dest_thunk [v] s of
    | BadRef => Etype_error
    | NotThunk => (
        case store_assign n (Thunk Evaluated v) s of
        | SOME s' => return env s' v c
        | NONE => Etype_error)
    | IsThunk v3 v4 => Etype_error) ∧
  continue s v ((Clog l e, env) :: c) = (
    case do_log l v e of
      SOME (Exp e) => Estep (env, s, Exp e, c)
    | SOME (Val v) => return env s v c
    | NONE => Etype_error) ∧
  continue s v ((Cif e1 e2, env) :: c) = (
    case do_if v e1 e2 of
      SOME e => Estep (env, s, Exp e, c)
    | NONE => Etype_error) ∧
  continue s v ((Cmat_check pes err_v, env) :: c) = (
    if can_pmatch_all env.c s (MAP FST pes) v then
      Estep (env, s, Val v, (Cmat pes err_v, env)::c)
    else Etype_error) ∧
  continue s v ((Cmat [] err_v, env) :: c) =
    Estep (env, s, Exn err_v, c) ∧
  continue s v ((Cmat ((p,e)::pes) err_v, env) :: c) = (
    if ALL_DISTINCT (pat_bindings p []) then (
      case pmatch env.c s p v [] of
        Match_type_error => Etype_error
      | No_match => Estep (env, s, Val v, (Cmat pes err_v, env)::c)
      | Match env' =>
          Estep (
            env with <| v := nsAppend (alist_to_ns env') env.v |>, s, Exp e, c))
    else Etype_error ) ∧
  continue s v ((Clet n e, env) :: c) =
    Estep (env with <| v := nsOptBind n v env.v |>, s, Exp e, c) ∧
  continue s v ((Ccon n vs [], env) :: c) = (
    if do_con_check env.c n (LENGTH vs + 1n) then (
      case build_conv env.c n (v::vs) of
        NONE => Etype_error
      | SOME v => return env s v c)
    else Etype_error ) ∧
  continue s v ((Ccon n vs (e::es), env) :: c) = (
    if do_con_check env.c n (LENGTH vs + 1n + 1n + LENGTH es) then
      push env s e (Ccon n (v::vs) es) c
    else Etype_error ) ∧
  continue s v ((Ctannot t, env) :: c) = return env s v c ∧
  continue s v ((Clannot l, env) :: c) = return env s v c
End

Definition exn_continue_def:
  exn_continue env s v [] = Edone ∧
  exn_continue env s v ((Chandle pes, env') :: c) =
    return env s v ((Cmat_check pes v, env') :: c) ∧
  exn_continue env s v (_ :: c) = Estep (env, s, Exn v, c)
End

Definition estep_def:
  estep (env, s, Val v, c) : estep_result = continue s v c ∧
  estep (env, s, Exp $ Lit l, c) = return env s (Litv l) c ∧
  estep (env, s, Exp $ Raise e, c) = push env s e Craise c ∧
  estep (env, s, Exp $ Handle e pes, c) = push env s e (Chandle pes) c ∧
  estep (env, s, Exp $ Con n es, c) = (
    if do_con_check env.c n (LENGTH es) then (
      case REVERSE es of
        [] => (
          case build_conv env.c n [] of
            NONE => Etype_error
          | SOME v => return env s v c)
      | e::es => push env s e (Ccon n [] es) c)
    else Etype_error) ∧
  estep (env, s, Exp $ Var n, c) = (
    case nsLookup env.v n of
      NONE => Etype_error
    | SOME v => return env s v c) ∧
  estep (env, s, Exp $ Fun n e, c) = return env s (Closure env n e) c ∧
  estep (env, s, Exp $ App op es, c) = (
    case REVERSE es of
      [] => application op env s [] c
    | (e::es) => push env s e (Capp op [] es) c) ∧
  estep (env, s, Exp $ Log l e1 e2, c) = push env s e1 (Clog l e2) c ∧
  estep (env, s, Exp $ If e1 e2 e3, c) = push env s e1 (Cif e2 e3) c ∧
  estep (env, s, Exp $ Mat e pes, c) = push env s e (Cmat_check pes bind_exn_v) c ∧
  estep (env, s, Exp $ Let n e1 e2, c) = push env s e1 (Clet n e2) c ∧
  estep (env, s, Exp $ Letrec funs e, c) = (
    if ¬ALL_DISTINCT (MAP FST funs) then Etype_error
    else Estep (env with <| v := build_rec_env funs env env.v |>, s, Exp e, c)) ∧
  estep (env, s, Exp $ Tannot e t, c) = push env s e (Ctannot t) c ∧
  estep (env, s, Exp $ Lannot e l, c) = push env s e (Clannot l) c ∧
  estep (env, s, Exn v, c) = exn_continue env s v c
End


(******************** Declarations ********************)

(* State omits FFI and clock *)
Datatype:
  dstate =
  <| refs  : v store
   ; next_type_stamp : num
   ; next_exn_stamp : num
   ; eval_state : eval_state option
   |>
End

Datatype:
  deval =
  | Decl dec
  | ExpVal (v sem_env) exp_val_exn (ctxt list) locs pat
  | Env (v sem_env)
End

Datatype:
  dstep_result =
  | Dstep dstate deval decl_ctxt
  | Dtype_error
  | Ddone
  | Draise v
  | Dffi dstate
      (ffiname # word8 list # word8 list # num # v sem_env # ctxt list)
      locs pat decl_ctxt
End

Definition dreturn_def[simp]:
  dreturn st cs dev = Dstep st dev cs
End

Definition dpush_def[simp]:
  dpush st cs dev c = Dstep st dev (c::cs)
End

Definition dcontinue_def:
  dcontinue env' st [] = Ddone ∧
  dcontinue env' st (Cdmod mn env [] :: cs) =
    dreturn st cs (Env $ lift_dec_env mn (extend_dec_env env' env)) ∧
  dcontinue env' st (Cdmod mn env (d::ds) :: cs) =
    dpush st cs (Decl d) (Cdmod mn (extend_dec_env env' env) ds) ∧
  dcontinue env' st (CdlocalL lenv [] gds :: cs) =
    dpush st cs (Env empty_dec_env)
      (CdlocalG (extend_dec_env env' lenv) empty_dec_env gds) ∧
  dcontinue env' st (CdlocalL lenv (ld::lds) gds :: cs) =
    dpush st cs (Decl ld) (CdlocalL (extend_dec_env env' lenv) lds gds) ∧
  dcontinue env' st (CdlocalG lenv genv [] :: cs) =
    dreturn st cs (Env $ extend_dec_env env' genv) ∧
  dcontinue env' st (CdlocalG lenv genv (gd::gds) :: cs) =
    dpush st cs (Decl gd) (CdlocalG lenv (extend_dec_env env' genv) gds)
End

Definition dstep_def:
  dstep benv st (Decl $ Dlet locs p e) c = (
    if ALL_DISTINCT (pat_bindings p []) ∧
       every_exp (one_con_check (collapse_env benv c).c) e then
      dreturn st c (ExpVal (collapse_env benv c) (Exp e) [] locs p)
    else Dtype_error ) ∧
  dstep benv st (Decl $ Dletrec locs funs) c = (
    if ALL_DISTINCT (MAP FST funs) ∧
       EVERY (\ (x,y,z) .
         every_exp (one_con_check (collapse_env benv c).c) z) funs then
      dreturn st c (Env $
        <| v := build_rec_env funs (collapse_env benv c) nsEmpty; c := nsEmpty |>)
    else Dtype_error) ∧
  dstep benv st (Decl $ Dtype locs tds) c = (
    if EVERY check_dup_ctors tds then
      dreturn (st with next_type_stamp := st.next_type_stamp + LENGTH tds) c
        (Env <| v := nsEmpty; c := build_tdefs st.next_type_stamp tds |>)
    else Dtype_error) ∧
  dstep benv st (Decl $ Dtabbrev locs tvs n t) c = dreturn st c (Env empty_dec_env) ∧
  dstep benv st (Decl $ Dexn locs cn ts) c =
    dreturn (st with next_exn_stamp := st.next_exn_stamp + 1) c
      (Env <| v := nsEmpty; c := nsSing cn (LENGTH ts, ExnStamp st.next_exn_stamp) |>) ∧
  dstep benv st (Decl $ Dmod mn ds) c =
    dpush st c (Env empty_dec_env) (Cdmod mn empty_dec_env ds) ∧
  dstep benv st (Decl $ Dlocal lds gds) c =
    dpush st c (Env empty_dec_env) (CdlocalL empty_dec_env lds gds) ∧
  dstep benv st (Decl $ Denv n) c = (
    case declare_env st.eval_state (collapse_env benv c) of
    | SOME (x, es') =>
      dreturn (st with eval_state := es') c (Env <| v := nsSing n x; c := nsEmpty|>)
    | NONE => Dtype_error) ∧

  dstep benv st (Env env) c = dcontinue env st c ∧

  dstep benv st (ExpVal env (Val v) [] locs p) c = (
    if ALL_DISTINCT (pat_bindings p []) then
      case pmatch (collapse_env benv c).c st.refs p v [] of
      | Match new_vals =>
          dreturn st c (Env <| v := alist_to_ns new_vals; c := nsEmpty |>)
      | No_match => Draise bind_exn_v
      | Match_type_error => Dtype_error
    else Dtype_error ) ∧
  dstep benv st (ExpVal env (Exn v) [] locs p) c = Draise v ∧
  dstep benv st (ExpVal env ev ec locs p) c =
    case estep (env, st.refs, ev, ec) of
    | Estep (env', refs', ev', ec') =>
        dreturn (st with <| refs := refs'; |>) c (ExpVal env' ev' ec' locs p)
    | Etype_error => Dtype_error
    | Edone => Ddone (* cannot happen *)
    | Effi s ws1 ws2 n env' refs' ec' =>
        Dffi (st with refs := refs') (s, ws1, ws2, n, env', ec') locs p c
End

Definition is_halt_def:
  is_halt (Dffi _ _ _ _ _) = T ∧
  is_halt Ddone = T ∧
  is_halt (Draise _) = T ∧
  is_halt Dtype_error = T ∧
  is_halt _ = F
End

Definition step_n_def:
  step_n benv 0 e = e ∧
  step_n benv (SUC n) (Dstep st dev c) = step_n benv n (dstep benv st dev c) ∧
  step_n benv _ e = e
End

Datatype:
  next_res =
  | Ret
  | Div
  | Err
  | Act dstate
      (ffiname # word8 list # word8 list # num # v sem_env # ctxt list)
      locs pat decl_ctxt
End

Definition step_until_halt_def:
  step_until_halt benv d =
    case some n. is_halt (step_n benv n d) of
      NONE => Div
    | SOME n =>
        case step_n benv n d of
        | Dtype_error => Err
        | Dffi st ev locs pat c => Act st ev locs pat c
        | _ => Ret
End

Datatype:
  result = Termination
         | Error
         | FinalFFI (ffiname # word8 list # word8 list) ffi_outcome
End

Definition cml_itree_unfold_err_def:
  cml_itree_unfold_err f =
    itree_unfold_err f
      ((λ(_,_,ws) r. LENGTH ws = LENGTH r),
      FinalFFI, (λe. FinalFFI e FFI_failed))
End

Definition interp_def:
  interp benv e =
    cml_itree_unfold_err
      (λe.
        case step_until_halt benv e of
        | Ret => Ret' Termination
        | Err => Ret' Error
        | Div => Div'
        | Act st (s, ws1, ws2, n, env, cs) locs p c =>
            Vis' (s, ws1, ws2)
              (λr:word8 list.
                dreturn (st with refs := LUPDATE (W8array r) n st.refs) c
                  (ExpVal env (Val $ Conv NONE []) cs locs p)))
      e
End

Definition start_dstate_def:
  start_dstate : dstate =
  <| refs := []; next_type_stamp := 2; next_exn_stamp := 4; eval_state := NONE;
  |>
End

Definition start_env_def:
  start_env : v sem_env =
  <|v := Bind [] [];
    c := Bind [(«::»,2,TypeStamp «::» 1); («[]»,0,TypeStamp «[]» 1);
               («True»,0,TypeStamp «True» 0); («False»,0,TypeStamp «False» 0);
               («Subscript»,0,ExnStamp 3); («Div»,0,ExnStamp 2);
               («Chr»,0,ExnStamp 1); («Bind»,0,ExnStamp 0)] []
  |>
End

Definition itree_semantics_def:
  itree_semantics prog =
  interp start_env (Dstep start_dstate (Decl (Dlocal [] prog)) [])
End

CoInductive safe_itree:
  (safe_itree P (Ret Termination)) ∧
  (safe_itree P (Ret $ FinalFFI e f)) ∧
  (safe_itree P Div) ∧
  ((∀s. P s ⇒ safe_itree P (rest s)) ⇒ safe_itree P (Vis e rest))
End
