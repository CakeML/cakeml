(*
  An itree-based semantics for CakeML
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open namespaceTheory astTheory
     ffiTheory semanticPrimitivesTheory smallStepTheory;
open itreeTheory;

val _ = new_theory "itree_semantics"

(******************** do_app ********************)

Datatype:
  app_result = Rval v | Rraise v
End

Definition do_app_def:
  do_app s op vs = case (op, vs) of
      (ListAppend, [x1; x2]) => (
        case (v_to_list x1, v_to_list x2) of
          (SOME xs, SOME ys) => SOME (s, Rval (list_to_v (xs ++ ys)))
        | _ => NONE
      )
    | (Opn op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        if (op = Divide ∨ op = Modulo) ∧ n2 = 0 then
          SOME (s, Rraise div_exn_v)
        else
          SOME (s, Rval (Litv (IntLit (opn_lookup op n1 n2))))
    | (Opb op, [Litv (IntLit n1); Litv (IntLit n2)]) =>
        SOME (s, Rval (Boolv (opb_lookup op n1 n2)))
    | (Opw W8 op, [Litv (Word8 w1); Litv (Word8 w2)]) =>
        SOME (s, Rval (Litv (Word8 (opw8_lookup op w1 w2))))
    | (Opw W64 op, [Litv (Word64 w1); Litv (Word64 w2)]) =>
        SOME (s, Rval (Litv (Word64 (opw64_lookup op w1 w2))))
    | (Opw W64 op, [FP_WordTree w1; Litv (Word64 w2)]) =>
        let wr1 = (compress_word w1) in
          SOME (s, Rval (Litv (Word64 (opw64_lookup op wr1 w2))))
    | (Opw W64 op, [Litv (Word64 w1); FP_WordTree w2]) =>
        let wr2 = (compress_word w2) in
          SOME (s, Rval (Litv (Word64 (opw64_lookup op w1 wr2))))
    | (Opw W64 op, [FP_WordTree w1; FP_WordTree w2]) =>
        let wr1 = (compress_word w1) in
        let wr2 = (compress_word w2) in
          SOME (s, Rval (Litv (Word64 (opw64_lookup op wr1 wr2))))
    | (FP_top t_op, [v1; v2; v3]) =>
        (case (fp_translate v1, fp_translate v2, fp_translate v3) of
          (SOME (FP_WordTree w1), SOME (FP_WordTree w2), SOME (FP_WordTree w3)) =>
          SOME (s, Rval (FP_WordTree (fp_top t_op w1 w2 w3)))
        | _ => NONE
        )
    | (FP_bop bop, [v1; v2]) =>
        (case (fp_translate v1, fp_translate v2) of
          (SOME (FP_WordTree w1), SOME (FP_WordTree w2)) =>
          SOME (s,Rval (FP_WordTree (fp_bop bop w1 w2)))
        | _ => NONE
        )
    | (FP_uop uop, [v1]) =>
        (case (fp_translate v1) of
          (SOME (FP_WordTree w1)) =>
          SOME (s,Rval (FP_WordTree (fp_uop uop w1)))
        | _ => NONE
        )
    | (FP_cmp cmp, [v1; v2]) =>
        (case (fp_translate v1, fp_translate v2) of
          (SOME (FP_WordTree w1), SOME (FP_WordTree w2)) =>
          SOME (s,Rval (FP_BoolTree (fp_cmp cmp w1 w2)))
        | _ => NONE
        )
    | (FpToWord, [FP_WordTree v1]) => SOME (s, Rval (Litv (Word64 (compress_word v1))))
    | (FpFromWord, [Litv (Word64 v1)]) => (SOME (s, Rval (FP_WordTree (Fp_const v1))))
    | (Real_cmp cmp, [Real v1; Real v2]) =>
        SOME (s, Rval (Boolv (real_cmp cmp v1 v2)))
    | (Real_bop bop, [Real v1; Real v2]) =>
        SOME (s, Rval (Real (real_bop bop v1 v2)))
    | (Real_uop uop, [Real v1]) =>
        SOME (s, Rval (Real (real_uop uop v1)))
    | (RealFromFP, [Litv (Word64 fp)]) =>
        SOME (s, Rval (Real (fp64_to_real fp)))
    | (Shift W8 op n, [Litv (Word8 w)]) =>
        SOME (s, Rval (Litv (Word8 (shift8_lookup op w n))))
    | (Shift W64 op n, [Litv (Word64 w)]) =>
        SOME (s, Rval (Litv (Word64 (shift64_lookup op w n))))
    | (Shift W64 op n, [FP_WordTree fp]) =>
        SOME (s, Rval (Litv (Word64 (shift64_lookup op (compress_word fp) n))))
    | (Equality, [v1; v2]) =>
        (case do_eq v1 v2 of
            Eq_type_error => NONE
          | Eq_val b => SOME (s, Rval (Boolv b))
        )
    | (Opassign, [Loc lnum; v]) =>
        (case store_assign lnum (Refv v) s of
            SOME s' => SOME (s', Rval (Conv NONE []))
          | NONE => NONE
        )
    | (Opref, [v]) =>
        let (s',n) = (store_alloc (Refv v) s) in
          SOME (s', Rval (Loc n))
    | (Opderef, [Loc n]) =>
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
            SOME (s', Rval (Loc lnum))
    | (Aw8sub, [Loc lnum; Litv (IntLit i)]) =>
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
    | (Aw8sub_unsafe, [Loc lnum; Litv (IntLit i)]) =>
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
    | (Aw8length, [Loc n]) =>
        (case store_lookup n s of
            SOME (W8array ws) =>
              SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aw8update, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
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
    | (Aw8update_unsafe, [Loc lnum; Litv(IntLit i); Litv(Word8 w)]) =>
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
    | (WordFromInt W8, [Litv(IntLit i)]) =>
        SOME (s, Rval (Litv (Word8 (i2w i))))
    | (WordFromInt W64, [Litv(IntLit i)]) =>
        SOME (s, Rval (Litv (Word64 (i2w i))))
    | (WordToInt W8, [Litv (Word8 w)]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (WordToInt W64, [Litv (Word64 w)]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num(w2n w)))))
    | (WordToInt W64, [FP_WordTree fp]) =>
        SOME (s, Rval (Litv (IntLit (&w2n (compress_word fp)))))
    | (CopyStrStr, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len)]) =>
        SOME (s,
        (case copy_array (EXPLODE str,off) len NONE of
          NONE => Rraise sub_exn_v
        | SOME cs => Rval (Litv(StrLit(IMPLODE(cs))))
        ))
    | (CopyStrAw8, [Litv(StrLit str);Litv(IntLit off);Litv(IntLit len);
                    Loc dst;Litv(IntLit dstoff)]) =>
        (case store_lookup dst s of
          SOME (W8array ws) =>
            (case copy_array (EXPLODE str,off) len (SOME(ws_to_chars ws,dstoff)) of
              NONE => SOME (s, Rraise sub_exn_v)
            | SOME cs =>
              (case store_assign dst (W8array (chars_to_ws cs)) s of
                SOME s' =>  SOME (s', Rval (Conv NONE []))
              | _ => NONE
              )
            )
        | _ => NONE
        )
    | (CopyAw8Str, [Loc src;Litv(IntLit off);Litv(IntLit len)]) =>
      (case store_lookup src s of
        SOME (W8array ws) =>
        SOME (s,
          (case copy_array (ws,off) len NONE of
            NONE => Rraise sub_exn_v
          | SOME ws => Rval (Litv(StrLit(IMPLODE(ws_to_chars ws))))
          ))
      | _ => NONE
      )
    | (CopyAw8Aw8, [Loc src;Litv(IntLit off);Litv(IntLit len);
                    Loc dst;Litv(IntLit dstoff)]) =>
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
    | (Ord, [Litv (Char c)]) =>
          SOME (s, Rval (Litv(IntLit(int_of_num(ORD c)))))
    | (Chr, [Litv (IntLit i)]) =>
        SOME (s,
          (if (i <( 0 : int)) \/ (i >( 255 : int)) then
            Rraise chr_exn_v
          else
            Rval (Litv(Char(CHR(Num (ABS (I i))))))))
    | (Chopb op, [Litv (Char c1); Litv (Char c2)]) =>
        SOME (s, Rval (Boolv (opb_lookup op (int_of_num(ORD c1)) (int_of_num(ORD c2)))))
    | (Implode, [v]) =>
          (case v_to_char_list v of
            SOME ls =>
              SOME (s, Rval (Litv (StrLit (IMPLODE ls))))
          | NONE => NONE
          )
    | (Explode, [v]) =>
          (case v of
            Litv (StrLit str) =>
              SOME (s, Rval (list_to_v (MAP (\ c .  Litv (Char c)) (EXPLODE str))))
          | _ => NONE
          )
    | (Strsub, [Litv (StrLit str); Litv (IntLit i)]) =>
        if i <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let n = (Num (ABS (I i))) in
            if n >= STRLEN str then
              SOME (s, Rraise sub_exn_v)
            else
              SOME (s, Rval (Litv (Char (EL n (EXPLODE str)))))
    | (Strlen, [Litv (StrLit str)]) =>
        SOME (s, Rval (Litv(IntLit(int_of_num(STRLEN str)))))
    | (Strcat, [v]) =>
        (case v_to_list v of
          SOME vs =>
            (case vs_to_string vs of
              SOME str =>
                SOME (s, Rval (Litv(StrLit str)))
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
    | (Vlength, [Vectorv vs]) =>
        SOME (s, Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
    | (Aalloc, [Litv (IntLit n); v]) =>
        if n <( 0 : int) then
          SOME (s, Rraise sub_exn_v)
        else
          let (s',lnum) =
            (store_alloc (Varray (REPLICATE (Num (ABS (I n))) v)) s)
          in
            SOME (s', Rval (Loc lnum))
    | (AallocEmpty, [Conv NONE []]) =>
        let (s',lnum) = (store_alloc (Varray []) s) in
          SOME (s', Rval (Loc lnum))
    | (AallocFixed, vs) =>
        let (s',lnum) =
          (store_alloc (Varray vs) s)
        in
          SOME (s', Rval (Loc lnum))
    | (Asub, [Loc lnum; Litv (IntLit i)]) =>
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
    | (Asub_unsafe, [Loc lnum; Litv (IntLit i)]) =>
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
    | (Alength, [Loc n]) =>
        (case store_lookup n s of
            SOME (Varray ws) =>
              SOME (s,Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
          | _ => NONE
         )
    | (Aupdate, [Loc lnum; Litv (IntLit i); v]) =>
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
    | (Aupdate_unsafe, [Loc lnum; Litv (IntLit i); v]) =>
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
    | _ => NONE
End


(******************** expressions ********************)

Datatype:
  ctxt_frame = Craise
             | Chandle ((pat # exp) list)
             | Capp op (v list) (exp list)
             | Clog lop exp
             | Cif exp exp
             | Cmat_check ((pat # exp) list) v
             | Cmat ((pat # exp) list) v
             | Clet (varN option) exp
             | Ccon (((modN, conN) id) option) (v list) (exp list)
             | Ctannot ast_t
             | Clannot locs
             | Coptimise optChoice fp_opt
End

Type "ctxt"[pp] = ``:ctxt_frame # v sem_env``;

Type "small_state"[pp] = ``:v sem_env # v store # fpState # exp_val_exn # ctxt list``;

Datatype:
  estep_result = Estep small_state
               | Effi string (word8 list) (word8 list) num
                        (v sem_env) (v store) (ctxt list)
               | Edone
               | Etype_error fpState
End

Definition push_def:
  push env s fp e c cs : estep_result = Estep (env, s, fp, Exp e, (c,env)::cs)
End

Definition return_def:
  return env s fp v c : estep_result = Estep (env, s, fp, Val v, c)
End

Definition fix_fp_state_def:
  fix_fp_state ([]:ctxt list) fp = fp ∧
  fix_fp_state ((Coptimise oldSc sc,env)::ctxt) fp =
  fix_fp_state ctxt (fp with canOpt := oldSc) ∧
  fix_fp_state (c::ctxt) fp = fix_fp_state ctxt fp
End

Definition do_fprw_def:
  do_fprw (v:app_result) fp_opt fp_rws =
  case (v,fp_opt) of
  | (Rval (FP_BoolTree fv),rws) =>
      (case rwAllBoolTree rws fp_rws fv of
         NONE => NONE
       | SOME fv_opt => SOME (Rval (FP_BoolTree fv_opt)))
  | (Rval (FP_WordTree fv), rws) =>
      (case rwAllWordTree rws fp_rws fv of
         NONE => NONE
       | SOME fv_opt => SOME (Rval (FP_WordTree fv_opt)))
  | (Rval r, []) => SOME v
  | (_, _) => NONE
End

Definition application_def:
  application op env s fp vs c : estep_result =
   case getOpClass op of
      FunApp =>
      (case do_opapp vs of
          SOME (env,e) => (Estep (env, s, fp, Exp e, c):estep_result)
        | NONE => Etype_error (fix_fp_state c fp))
    | Icing =>
      (case do_app s op vs of
         NONE => Etype_error (fix_fp_state c fp)
       | SOME (s',r) =>
        let fp_opt =
          (if fp.canOpt = FPScope Opt then
            case (do_fprw r (fp.opts 0) fp.rws) of
            (* if it fails, just use the old value tree *)
              NONE => r
            | SOME r_opt => r_opt
          else r)
        in
        let fpN = (if fp.canOpt = FPScope Opt then shift_fp_state fp else fp) in
        let fp_res =
          (if (isFpBool op)
          then (case fp_opt of
              Rval (FP_BoolTree fv) => Rval (Boolv (compress_bool fv))
            | v => v
            )
          else fp_opt)
        in
          (case fp_res of
              Rraise v => Estep (env,s', fpN, Exn v, c)
            | Rval v => return env s' fpN v c))
    | Reals =>
      if fp.real_sem then
      (case do_app s op vs of
         SOME (s', Rraise v) => Estep (env, s', fp, Exn v, c)
       | SOME (s', Rval v) => return env s' fp v c
       | NONE => Etype_error (fix_fp_state c fp))
      else Etype_error (fix_fp_state c (shift_fp_state fp))
     | _ =>
         case op of
         | FFI n => (
           case vs of
             [Litv (StrLit conf); Loc lnum] => (
             case store_lookup lnum s of
               SOME (W8array ws) =>
                 if n = "" then Estep (env, s, fp, Val $ Conv NONE [], c)
                 else Effi n (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env s c
             | _ => Etype_error (fix_fp_state c fp))
           | _ => Etype_error (fix_fp_state c fp))
         | _ =>
             (case do_app s op vs of
                SOME (s', Rraise v) => Estep (env, s, fp, Exn v,c)
              | SOME (s', Rval v) => return env s' fp v c
              | NONE => Etype_error (fix_fp_state c fp) )
End

Definition continue_def:
  continue s fp v [] : estep_result = Edone ∧
  continue s fp v ((Craise, env)::cs) = Estep (env, s, fp, Exn v, cs) ∧
  continue s fp v ((Chandle pes, env)::c) = return env s fp v c ∧
  continue s fp v ((Capp op vs [], env) :: c) = application op env s fp (v::vs) c ∧
  continue s fp v ((Capp op vs (e::es), env) :: c) = push env s fp e (Capp op (v::vs) es) c ∧
  continue s fp v ((Clog l e, env) :: c) = (
    case do_log l v e of
      SOME (Exp e) => Estep (env, s, fp, Exp e, c)
    | SOME (Val v) => return env s fp v c
    | NONE => Etype_error (fix_fp_state c fp)) ∧
  continue s fp v ((Cif e1 e2, env) :: c) = (
    case do_if v e1 e2 of
      SOME e => Estep (env, s, fp, Exp e, c)
    | NONE => Etype_error (fix_fp_state c fp)) ∧
  continue s fp v ((Cmat_check pes err_v, env) :: c) = (
    if can_pmatch_all env.c s (MAP FST pes) v then
      Estep (env, s, fp, Val v, (Cmat pes err_v, env)::c)
    else Etype_error (fix_fp_state c fp)) ∧
  continue s fp v ((Cmat [] err_v, env) :: c) =
    Estep (env, s, fp, Exn err_v, c) ∧
  continue s fp v ((Cmat ((p,e)::pes) err_v, env) :: c) = (
    if ALL_DISTINCT (pat_bindings p []) then (
      case pmatch env.c s p v [] of
        Match_type_error => Etype_error (fix_fp_state c fp)
      | No_match => Estep (env, s, fp, Val v, (Cmat pes err_v, env)::c)
      | Match env' =>
          Estep (
            env with <| v := nsAppend (alist_to_ns env') env.v |>, s, fp, Exp e, c))
    else Etype_error (fix_fp_state c fp)) ∧
  continue s fp v ((Clet n e, env) :: c) =
    Estep (env with <| v := nsOptBind n v env.v |>, s, fp, Exp e, c) ∧
  continue s fp v ((Ccon n vs [], env) :: c) = (
    if do_con_check env.c n (LENGTH vs + 1n) then (
      case build_conv env.c n (v::vs) of
        NONE => Etype_error (fix_fp_state c fp)
      | SOME v => return env s fp v c)
    else Etype_error (fix_fp_state c fp)) ∧
  continue s fp v ((Ccon n vs (e::es), env) :: c) = (
    if do_con_check env.c n (LENGTH vs + 1n + 1n + LENGTH es) then
      push env s fp e (Ccon n (v::vs) es) c
    else Etype_error (fix_fp_state c fp)) ∧
  continue s fp v ((Ctannot t, env) :: c) = return env s fp v c ∧
  continue s fp v ((Clannot l, env) :: c) = return env s fp v c ∧
  continue s fp v ((Coptimise oldSc sc, env) :: c) =
    return env s (fp with canOpt := oldSc) (HD (do_fpoptimise sc [v])) c
End

Definition exn_continue_def:
  exn_continue env s fp v [] = Edone ∧
  exn_continue env s fp v ((Chandle pes, env') :: c) =
    return env s fp v ((Cmat_check pes v, env') :: c) ∧
  exn_continue env s fp v ((Coptimise oldSc sc, env') :: c) =
    Estep (env, s, fp with canOpt := oldSc, Exn v, c) ∧
  exn_continue env s fp v (_ :: c) = Estep (env, s, fp, Exn v, c)
End

Definition estep_def:
  estep (env, s, fp, Val v, c) : estep_result = continue s fp v c ∧
  estep (env, s, fp, Exp $ Lit l, c) = return env s fp (Litv l) c ∧
  estep (env, s, fp, Exp $ Raise e, c) = push env s fp e Craise c ∧
  estep (env, s, fp, Exp $ Handle e pes, c) = push env s fp e (Chandle pes) c ∧
  estep (env, s, fp, Exp $ Con n es, c) = (
    if do_con_check env.c n (LENGTH es) then (
      case REVERSE es of
        [] => (
          case build_conv env.c n [] of
            NONE => Etype_error (fix_fp_state c fp)
          | SOME v => return env s fp v c)
      | e::es => push env s fp e (Ccon n [] es) c)
    else Etype_error (fix_fp_state c fp)) ∧
  estep (env, s, fp, Exp $ Var n, c) = (
    case nsLookup env.v n of
      NONE => Etype_error (fix_fp_state c fp)
    | SOME v => return env s fp v c) ∧
  estep (env, s, fp, Exp $ Fun n e, c) = return env s fp (Closure env n e) c ∧
  estep (env, s, fp, Exp $ App op es, c) = (
    case REVERSE es of
      [] => application op env s fp [] c
    | (e::es) => push env s fp e (Capp op [] es) c) ∧
  estep (env, s, fp, Exp $ Log l e1 e2, c) = push env s fp e1 (Clog l e2) c ∧
  estep (env, s, fp, Exp $ If e1 e2 e3, c) = push env s fp e1 (Cif e2 e3) c ∧
  estep (env, s, fp, Exp $ Mat e pes, c) = push env s fp e (Cmat_check pes bind_exn_v) c ∧
  estep (env, s, fp, Exp $ Let n e1 e2, c) = push env s fp e1 (Clet n e2) c ∧
  estep (env, s, fp, Exp $ Letrec funs e, c) = (
    if ¬ALL_DISTINCT (MAP FST funs) then Etype_error (fix_fp_state c fp)
    else Estep (env with <| v := build_rec_env funs env env.v |>, s, fp, Exp e, c)) ∧
  estep (env, s, fp, Exp $ Tannot e t, c) = push env s fp e (Ctannot t) c ∧
  estep (env, s, fp, Exp $ Lannot e l, c) = push env s fp e (Clannot l) c ∧
  estep (env, s, fp, Exp $ FpOptimise sc e, c) =
    (let fpN = if fp.canOpt = Strict then fp else fp with canOpt := FPScope sc in
      push env s fpN e (Coptimise fp.canOpt sc) c) ∧
  estep (env, s, fp, Exn v, c) = exn_continue env s fp v c
End


(******************** Declarations ********************)

(* State omits FFI and clock *)
Datatype:
  dstate =
  <| refs  : v store
   ; next_type_stamp : num
   ; next_exn_stamp : num
   ; eval_state : eval_state option
   ; fp_state : fpState
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
  | Dtype_error fpState
  | Ddone
  | Draise (fpState # v)
  | Dffi dstate
      (string # word8 list # word8 list # num # v sem_env # ctxt list)
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
    else Dtype_error st.fp_state) ∧
  dstep benv st (Decl $ Dletrec locs funs) c = (
    if ALL_DISTINCT (MAP FST funs) ∧
       EVERY (\ (x,y,z) .
         every_exp (one_con_check (collapse_env benv c).c) z) funs then
      dreturn st c (Env $
        <| v := build_rec_env funs (collapse_env benv c) nsEmpty; c := nsEmpty |>)
    else Dtype_error st.fp_state) ∧
  dstep benv st (Decl $ Dtype locs tds) c = (
    if EVERY check_dup_ctors tds then
      dreturn (st with next_type_stamp := st.next_type_stamp + LENGTH tds) c
        (Env <| v := nsEmpty; c := build_tdefs st.next_type_stamp tds |>)
    else Dtype_error st.fp_state) ∧
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
    | NONE => Dtype_error st.fp_state) ∧

  dstep benv st (Env env) c = dcontinue env st c ∧

  dstep benv st (ExpVal env (Val v) [] locs p) c = (
    if ALL_DISTINCT (pat_bindings p []) then
      case pmatch (collapse_env benv c).c st.refs p v [] of
      | Match new_vals =>
          dreturn st c (Env <| v := alist_to_ns new_vals; c := nsEmpty |>)
      | No_match => Draise (st.fp_state, bind_exn_v)
      | Match_type_error => Dtype_error st.fp_state
    else Dtype_error st.fp_state) ∧
  dstep benv st (ExpVal env (Exn v) [] locs p) c = Draise (st.fp_state, v) ∧
  dstep benv st (ExpVal env ev ec locs p) c =
    case estep (env, st.refs, st.fp_state, ev, ec) of
    | Estep (env', refs', fp', ev', ec') =>
        dreturn (st with <| refs := refs'; fp_state:= fp' |>) c (ExpVal env' ev' ec' locs p)
    | Etype_error fp => Dtype_error fp
    | Edone => Ddone (* cannot happen *)
    | Effi s ws1 ws2 n env' refs' ec' =>
        Dffi (st with refs := refs') (s, ws1, ws2, n, env', ec') locs p c
End

Definition is_halt_def:
  is_halt (Dffi _ _ _ _ _) = T ∧
  is_halt Ddone = T ∧
  is_halt (Draise _) = T ∧
  is_halt (Dtype_error _) = T ∧
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
      (string # word8 list # word8 list # num # v sem_env # ctxt list)
      locs pat decl_ctxt
End

Definition step_until_halt_def:
  step_until_halt benv d =
    case some n. is_halt (step_n benv n d) of
      NONE => Div
    | SOME n =>
        case step_n benv n d of
        | Dtype_error fp => Err
        | Dffi st ev locs pat c => Act st ev locs pat c
        | _ => Ret
End

Datatype:
  result = Termination
         | Error
         | FinalFFI (string # word8 list # word8 list) ffi_outcome
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

val _ = export_theory();
