(*
  A small-step semantics for CakeML. This semantics is no longer used
  in the main CakeML development, but is used in PureCake and choreographies.
*)
open HolKernel Parse boolLib bossLib;
open libTheory namespaceTheory astTheory ffiTheory semanticPrimitivesTheory;

val _ = numLib.prefer_num();



val _ = new_theory "smallStep"

(* Small-step semantics for expressions, modules, and definitions *)

(* Evaluation contexts
 * The hole is denoted by the unit type
 * The env argument contains bindings for the free variables of expressions in
     the context *)
Datatype:
 ctxt_frame =
    Craise unit
  | Chandle unit ((pat # exp) list)
  | Capp op (v list) unit (exp list)
  | Clog lop unit exp
  | Cif unit exp exp
  (* The value is raised if none of the patterns match *)
  | Cmat_check unit ((pat # exp) list) v
  | Cmat unit ((pat # exp) list) v
  | Clet (varN option) unit exp
  (* Evaluating a constructor's arguments
   * The v list should be in reverse order. *)
  | Ccon (((modN, conN)id)option) (v list) unit (exp list)
  | Ctannot unit ast_t
  | Clannot unit locs
  | Coptimise optChoice fp_opt unit
End

Type ctxt = ``: ctxt_frame # v sem_env``

Datatype:
  exp_val_exn = Exp exp | Val v | Exn v
End

(* State for CEK-style expression evaluation
 * - constructor data
 * - the store
 * - the environment for the free variables of the current expression
 * - the floating-point optimization oracle
 * - the current expression to evaluate, or a value if finished
 * - the context stack (continuation) of what to do once the current expression
 *   is finished.  Each entry has an environment for it's free variables *)

Type small_state = ``: v sem_env # ('ffi, v) store_ffi # fpState # exp_val_exn # ctxt list``

Datatype:
  e_step_result =
     Estep ('ffi small_state)
   | Eabort (fpState # abort)
   | Estuck
End


(* The semantics are deterministic, and presented functionally instead of
 * relationally for proof rather that readability; the steps are very small: we
 * push individual frames onto the context stack instead of finding a redex in a
 * single step *)

(*val push : forall 'ffi. sem_env v -> store_ffi 'ffi v -> exp -> ctxt_frame -> list ctxt -> e_step_result 'ffi*)
val _ = Define `
 ((push:(v)sem_env ->(v)store#'ffi ffi_state -> fpState -> exp -> ctxt_frame ->(ctxt_frame#(v)sem_env)list -> 'ffi e_step_result) env s fp e c' cs=  (Estep (env, s, fp, Exp e, ((c',env)::cs))))`;


(*val return : forall 'ffi. sem_env v -> store_ffi 'ffi v -> v -> list ctxt -> e_step_result 'ffi*)
val _ = Define `
 ((return:(v)sem_env ->(v)store#'ffi ffi_state -> fpState -> v ->(ctxt)list -> 'ffi e_step_result) env s fp v c=  (Estep (env, s, fp, Val v, c)))`;

Definition shift_fp_state_def:
  shift_fp_state fp =
  fp with <| opts := (λ x. fp.opts (x + 1)); choices := fp.choices + 1 |>
End

Definition fix_fp_state_def:
  fix_fp_state [] fp = fp ∧
  fix_fp_state ((Coptimise oldSc sc (),env)::cs) fp = fix_fp_state cs (fp with canOpt := oldSc) ∧
  fix_fp_state (c :: cs) fp = fix_fp_state cs fp
End

(*val application : forall 'ffi. op -> sem_env v -> store_ffi 'ffi v -> list v -> list ctxt -> e_step_result 'ffi*)
val _ = Define `
 (application:op ->(v)sem_env ->(v)store#'ffi ffi_state -> fpState ->(v)list ->(ctxt)list -> 'ffi e_step_result) op env s fp vs c=
   (case getOpClass op of
      FunApp =>
      (case do_opapp vs of
          SOME (env,e) => Estep (env, s, fp, Exp e, c)
        | NONE => Eabort (fix_fp_state c fp, Rtype_error))
    | Icing =>
      (case do_app s op vs of
         NONE => Eabort (fix_fp_state c fp, Rtype_error)
       | SOME (s',r) =>
        let fp_opt =
          (if fp.canOpt = FPScope Opt then
            (case (do_fprw r (fp.opts 0) fp.rws) of
            (* if it fails, just use the old value tree *)
              NONE => r
            | SOME r_opt => r_opt)
            (* If we cannot optimize, we should not allow matching on the structure in the oracle *)
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
              Rerr (Rraise v) => Estep (env,s', fpN, Exn v, c)
            | Rerr (Rabort a) => Eabort (fix_fp_state c fpN, a)
            | Rval v => return env s' fpN v c))
    | Reals =>
      if fp.real_sem then
      (case do_app s op vs of
          SOME (s',r) =>
          (case r of
              Rerr (Rraise v) => Estep (env,s',fp, Exn v,c)
            | Rerr (Rabort a) => Eabort (fix_fp_state c fp, a)
            | Rval v => return env s' fp v c
          )
        | NONE => Eabort (fix_fp_state c fp, Rtype_error))
      else Eabort (fix_fp_state c (shift_fp_state fp), Rtype_error)
     | _ =>
      (case do_app s op vs of
          SOME (s',r) =>
          (case r of
              Rerr (Rraise v) => Estep (env,s', fp, Exn v, c)
            | Rerr (Rabort a) => Eabort (fix_fp_state c fp, a)
            | Rval v => return env s' fp v c
          )
        | NONE => Eabort (fix_fp_state c fp, Rtype_error))
    )`;

(* apply a context to a value *)
(*val continue : forall 'ffi. store_ffi 'ffi v -> fpState -> v -> list ctxt -> e_step_result 'ffi*)
val _ = Define `
 ((continue:(v)store#'ffi ffi_state -> fpState -> v ->(ctxt_frame#(v)sem_env)list -> 'ffi e_step_result) s fp v cs=
   ((case cs of
      [] => Estuck
    | (Craise () , env) :: c => Estep (env, s, fp,Exn v, c)
    | (Chandle ()  pes, env) :: c =>
        return env s fp v c
    | (Capp op vs ()  [], env) :: c =>
        application op env s fp (v::vs) c
    | (Capp op vs ()  (e::es), env) :: c =>
        push env s fp e (Capp op (v::vs) ()  es) c
    | (Clog l ()  e, env) :: c =>
        (case do_log l v e of
            SOME (Exp e) => Estep (env, s, fp, Exp e, c)
          | SOME (Val v) => return env s fp v c
          | NONE => Eabort (fix_fp_state c fp, Rtype_error)
        )
    | (Cif ()  e1 e2, env) :: c =>
        (case do_if v e1 e2 of
            SOME e => Estep (env, s, fp, Exp e, c)
          | NONE => Eabort (fix_fp_state c fp, Rtype_error)
        )
    | (Cmat_check ()  pes err_v, env) :: c =>
        if can_pmatch_all env.c (FST s) (MAP FST pes) v then
          Estep (env, s, fp, Val v, ((Cmat ()  pes err_v,env)::c))
        else
          Eabort (fix_fp_state c fp, Rtype_error)
    | (Cmat ()  [] err_v, env) :: c =>
        Estep (env, s, fp, Exn err_v, c)
    | (Cmat ()  ((p,e)::pes) err_v, env) :: c =>
        if ALL_DISTINCT (pat_bindings p []) then
          (case pmatch env.c (FST s) p v [] of
              Match_type_error => Eabort (fix_fp_state c fp, Rtype_error)
            | No_match => Estep (env, s, fp, Val v, ((Cmat ()  pes err_v,env)::c))
            | Match env' => Estep (( env with<| v := (nsAppend (alist_to_ns env') env.v) |>), s, fp, Exp e, c)
          )
        else
          Eabort (fix_fp_state c fp, Rtype_error)
    | (Clet n ()  e, env) :: c =>
        Estep (( env with<| v := (nsOptBind n v env.v) |>), s, fp, Exp e, c)
    | (Ccon n vs ()  [], env) :: c =>
        if do_con_check env.c n (LENGTH vs +( 1 : num)) then
           (case build_conv env.c n (v::vs) of
               NONE => Eabort (fix_fp_state c fp, Rtype_error)
             | SOME v => return env s fp v c
           )
        else
          Eabort (fix_fp_state c fp, Rtype_error)
    | (Ccon n vs ()  (e::es), env) :: c =>
        if do_con_check env.c n (((LENGTH vs +( 1 : num)) +( 1 : num)) + LENGTH es) then
          push env s fp e (Ccon n (v::vs) ()  es) c
        else
          Eabort (fix_fp_state c fp, Rtype_error)
    | (Ctannot ()  t, env) :: c =>
        return env s fp v c
    | (Clannot ()  l, env) :: c =>
        return env s fp v c
    | (Coptimise oldSc sc (), env) :: c =>
        return env s (fp with canOpt := oldSc) (HD (do_fpoptimise sc [v])) c
  )))`;


(* The single step expression evaluator.  Returns None if there is nothing to
 * do, but no type error.  Returns Type_error on encountering free variables,
 * mis-applied (or non-existent) constructors, and when the wrong kind of value
 * if given to a primitive.  Returns Bind_error when no pattern in a match
 * matches the value.  Otherwise it returns the next state *)

(*val e_step : forall 'ffi. small_state 'ffi -> e_step_result 'ffi*)
val _ = Define `
 ((e_step:(v)sem_env#((v)store#'ffi ffi_state)#fpState#exp_val_exn#(ctxt)list -> 'ffi e_step_result) (env, s, fp, ev, c)=
   ((case ev of
      Val v  =>
        continue s fp v c
    | Exp e =>
        (case e of
            Lit l => return env s fp (Litv l) c
          | Raise e =>
              push env s fp e (Craise () ) c
          | Handle e pes =>
              push env s fp e (Chandle ()  pes) c
          | Con n es =>
              if do_con_check env.c n (LENGTH es) then
                (case REVERSE es of
                    [] =>
                      (case build_conv env.c n [] of
                          NONE => Eabort (fix_fp_state c fp, Rtype_error)
                        | SOME v => return env s fp v c
                      )
                  | e::es =>
                      push env s fp e (Ccon n [] ()  es) c
                )
              else
                Eabort (fix_fp_state c fp, Rtype_error)
          | Var n =>
              (case nsLookup env.v n of
                  NONE => Eabort (fix_fp_state c fp, Rtype_error)
                | SOME v =>
                    return env s fp v c
              )
          | Fun n e => return env s fp (Closure env n e) c
          | App op es =>
              (case REVERSE es of
                  [] => application op env s fp [] c
                | (e::es) => push env s fp e (Capp op [] ()  es) c
              )
          | Log l e1 e2 => push env s fp e1 (Clog l ()  e2) c
          | If e1 e2 e3 => push env s fp e1 (Cif ()  e2 e3) c
          | Mat e pes => push env s fp e (Cmat_check ()  pes bind_exn_v) c
          | Let n e1 e2 => push env s fp e1 (Clet n ()  e2) c
          | Letrec funs e =>
              if ~ (ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs)) then
                Eabort (fix_fp_state c fp, Rtype_error)
              else
                Estep (( env with<| v := (build_rec_env funs env env.v) |>),
                       s, fp, Exp e, c)
          | Tannot e t => push env s fp e (Ctannot ()  t) c
          | Lannot e l => push env s fp e (Clannot ()  l) c
          | FpOptimise sc e =>
              let fpN = if fp.canOpt = Strict then fp else fp with canOpt := FPScope sc in
              push env s fpN e (Coptimise fp.canOpt sc ()) c
        )
    | Exn v =>
       case c of
       | [] => Estuck
       | (Chandle () pes, env') :: c =>
            Estep (env, s, fp, Val v, (Cmat_check () pes v, env') :: c)
       | (Coptimise oldSc sc (), env') :: c =>
           Estep (env, s, fp with canOpt := oldSc , Exn v, c)
       | _ :: c => Estep (env, s, fp, Exn v, c)
  )))`;


(* Define a semantic function using the steps *)

(*val e_step_reln : forall 'ffi. small_state 'ffi -> small_state 'ffi -> bool*)
(*val small_eval : forall 'ffi. sem_env v -> store_ffi 'ffi v -> exp -> list ctxt -> store_ffi 'ffi v * result v v -> bool*)

val _ = Define `
 ((e_step_reln:(v)sem_env#('ffi,(v))store_ffi#fpState#exp_val_exn#(ctxt)list ->(v)sem_env#('ffi,(v))store_ffi#fpState#exp_val_exn#(ctxt)list -> bool) st1 st2=
   (e_step st1 = Estep st2))`;

 val _ = Define `

((small_eval:(v)sem_env ->(v)store#'ffi ffi_state -> fpState -> exp ->(ctxt)list ->((v)store#'ffi ffi_state)#fpState#((v),(v))result -> bool) env s fp e c (s', fp', Rval v)=
   (? env'. (RTC (e_step_reln)) (env,s,fp,Exp e,c) (env',s',fp', Val v,[])))
/\
((small_eval:(v)sem_env ->(v)store#'ffi ffi_state -> fpState -> exp ->(ctxt)list ->((v)store#'ffi ffi_state)#fpState#((v),(v))result -> bool) env s fp e c (s', fp', Rerr (Rraise v))=
   (? env'. (RTC (e_step_reln)) (env,s,fp,Exp e,c) (env',s',fp', Exn v,[])))
/\
((small_eval:(v)sem_env ->(v)store#'ffi ffi_state -> fpState -> exp ->(ctxt)list ->((v)store#'ffi ffi_state)#fpState#((v),(v))result -> bool) env s fp e c (s', fp', Rerr (Rabort a))=
   (? env' e' c' fp''.
    (RTC (e_step_reln)) (env,s,fp,Exp e,c) (env',s',fp'',e',c') /\
    (e_step (env',s',fp'',e',c') = Eabort (fp', a))))`;


(*val e_diverges : forall 'ffi. sem_env v -> store_ffi 'ffi v -> exp -> bool*)
val _ = Define `
 ((e_diverges:(v)sem_env ->(v)store#'ffi ffi_state -> fpState -> exp -> bool) env s fp e=
   (! env' s' e' c' fp'.
    (RTC (e_step_reln)) (env,s,fp,Exp e,[]) (env',s',fp',e',c')
    ==>
(? env'' s'' fp'' e'' c''.
      e_step_reln (env',s',fp',e',c') (env'',s'',fp'',e'',c''))))`;



(* Evaluation contexts for declarations *)

Datatype:
 decl_ctxt_frame =
    Cdmod modN (v sem_env) (dec list)
  | CdlocalL (v sem_env) (dec list) (dec list) (* local env, local and global decs *)
  | CdlocalG (v sem_env) (v sem_env) (dec list)
 (* local and global envs, global decs *)
End

Type decl_ctxt = ``: decl_ctxt_frame list``

Datatype:
 decl_eval =
    Decl dec (* a declaration to evaluate *)
  | ExpVal (v sem_env) exp_val_exn (ctxt list) locs pat (* a Dlet under evaluation *)
  | Env (v sem_env)
 (* an environment to return to parent declaration *)
End

Type small_decl_state = ``: 'ffi state # decl_eval # decl_ctxt``

Datatype:
  decl_step_result =
    Dstep ('ffi small_decl_state)
  | Dabort (fpState # abort)
  | Ddone
  | Draise (fpState # v)
End

(* Helper functions *)

(*val empty_dec_env : forall 'v. sem_env 'v*)
val _ = Define `
 ((empty_dec_env:'v sem_env)=  (<| v := nsEmpty ; c := nsEmpty |>))`;


(*val lift_dec_env : forall 'v. modN -> sem_env 'v -> sem_env 'v*)
val _ = Define `
 ((lift_dec_env:string -> 'v sem_env -> 'v sem_env) mn env=  (<| v := (nsLift mn env.v) ; c := (nsLift mn env.c) |>))`;


(* Get the "current" sem_env given the context *)
(*val collapse_env : sem_env v -> decl_ctxt -> sem_env v*)
 val _ = Define `
 ((collapse_env:(v)sem_env ->(decl_ctxt_frame)list ->(v)sem_env) base c=
   ((case c of
    [] => base
  | Cdmod mn env ds :: cs => extend_dec_env env (collapse_env base cs)
  | CdlocalL lenv lds gds :: cs =>
      extend_dec_env lenv (collapse_env base cs)
  | CdlocalG lenv genv gds :: cs =>
      extend_dec_env (extend_dec_env genv lenv) (collapse_env base cs)
  )))`;



(* Apply a context to the env resulting from evaluating a declaration *)
(*val decl_continue : forall 'ffi. sem_env v -> state 'ffi -> decl_ctxt -> decl_step_result 'ffi*)
val _ = Define `
 ((decl_continue:(v)sem_env -> 'ffi state ->(decl_ctxt_frame)list -> 'ffi decl_step_result) env' st c=
   ((case c of
    [] => Ddone
  | Cdmod mn env [] :: cs =>
      Dstep (st, Env (lift_dec_env mn (extend_dec_env env' env)), cs)
  | Cdmod mn env (d::ds) :: cs =>
      Dstep (st, Decl d, (Cdmod mn (extend_dec_env env' env) ds :: cs))
  | CdlocalL lenv [] gds :: cs =>
      Dstep (st, Env empty_dec_env,
             (CdlocalG (extend_dec_env env' lenv) empty_dec_env gds :: cs))
  | CdlocalL lenv (ld::lds) gds :: cs =>
      Dstep (st, Decl ld, (CdlocalL (extend_dec_env env' lenv) lds gds :: cs))
  | CdlocalG lenv genv [] :: cs => Dstep (st, Env (extend_dec_env env' genv), cs)
  | CdlocalG lenv genv (gd::gds) :: cs =>
      Dstep (st, Decl gd, (CdlocalG lenv (extend_dec_env env' genv) gds :: cs))
  )))`;


(*val decl_step : forall 'ffi. sem_env v -> small_decl_state 'ffi -> decl_step_result 'ffi*)
val _ = Define `
 ((decl_step:(v)sem_env -> 'ffi state#decl_eval#(decl_ctxt_frame)list -> 'ffi decl_step_result) benv (st, dev, c)=
   ((case dev of
    Decl d =>
      (case d of
        Dlet locs p e =>
          if ALL_DISTINCT (pat_bindings p []) ∧
             every_exp (one_con_check (collapse_env benv c).c) e
          then
            Dstep (st, ExpVal (collapse_env benv c) (Exp e) [] locs p, c)
          else Dabort (st.fp_state, Rtype_error)
      | Dletrec locs funs =>
          if ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) ∧
             EVERY (\ (x,y,z) .
               every_exp (one_con_check (collapse_env benv c).c) z) funs
          then
            Dstep (st,
              Env <| v := (build_rec_env funs (collapse_env benv c) nsEmpty); c := nsEmpty |>,
              c)
          else Dabort (st.fp_state, Rtype_error)
      | Dtype locs tds =>
          if EVERY check_dup_ctors tds then
            Dstep (
              ( st with<| next_type_stamp := (st.next_type_stamp + LENGTH tds) |>),
              Env <| v := nsEmpty; c := (build_tdefs st.next_type_stamp tds) |>,
              c)
          else Dabort (st.fp_state, Rtype_error)
      | Dtabbrev locs tvs n t => Dstep (st, Env empty_dec_env, c)
      | Dexn locs cn ts =>
          Dstep (
            ( st with<| next_exn_stamp := (st.next_exn_stamp +( 1 : num)) |>),
            Env <| v := nsEmpty; c := (nsSing cn (LENGTH ts, ExnStamp st.next_exn_stamp)) |>,
            c)
      | Dmod mn ds =>
          Dstep (st, Env empty_dec_env, (Cdmod mn empty_dec_env ds :: c))
      | Dlocal lds gds =>
          Dstep (st, Env empty_dec_env, (CdlocalL empty_dec_env lds gds :: c))
      | Denv n =>
          (case declare_env st.eval_state (collapse_env benv c) of
            SOME (x, es') =>
             Dstep (( st with<| eval_state := es' |>),
              Env <| v := (nsSing n x) ; c := nsEmpty |>, c)
          | NONE => Dabort (st.fp_state, Rtype_error)
          )
      )

  | Env env => decl_continue env st c

  | ExpVal env ev ec locs p =>
      (case (ev, ec) of
        (Val v, []) =>
          if ALL_DISTINCT (pat_bindings p []) then
            (case pmatch (collapse_env benv c).c st.refs p v [] of
              Match new_vals =>
                Dstep (st, Env <| v := (alist_to_ns new_vals); c := nsEmpty |>, c)
            | No_match => Draise (st.fp_state, bind_exn_v)
            | Match_type_error => Dabort (st.fp_state, Rtype_error)
            )
          else Dabort (st.fp_state, Rtype_error)
      | (Exn v, []) => Draise (st.fp_state, v)
      | _ =>
        (case e_step (env, (st.refs, st.ffi), st.fp_state, ev, ec) of
          Estep (env', (refs', ffi'), fp', ev', ec') =>
            Dstep (( st with<| refs := refs' ; ffi := ffi'; fp_state := fp'|>),
              ExpVal env' ev' ec' locs p, c)
        | Eabort (fp, a) => Dabort (fp, a)
        | Estuck => Ddone (* cannot happen *)
        )
      )
  )))`;


(*val decl_step_reln : forall 'ffi. sem_env v -> small_decl_state 'ffi -> small_decl_state 'ffi -> bool*)

(*val small_eval_dec : forall 'ffi. sem_env v -> small_decl_state 'ffi -> state 'ffi * result (sem_env v) v -> bool*)

val _ = Define `
 ((decl_step_reln:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> 'ffi state#decl_eval#decl_ctxt -> bool) env st1 st2=
   (decl_step env st1 = Dstep st2))`;


 val _ = Define `

((small_eval_dec:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> 'ffi state#(((v)sem_env),(v))result -> bool) env dst (st, Rval e)=
   ((RTC (decl_step_reln env)) dst (st, Env e, [])))
/\
((small_eval_dec:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> 'ffi state#(((v)sem_env),(v))result -> bool) env dst (st, Rerr (Rraise v))=
   (? dev' dcs' fp.
    (RTC (decl_step_reln env)) dst (st with fp_state := fp, dev', dcs') /\
    (decl_step env (st with fp_state := fp, dev', dcs') = Draise (st.fp_state, v))))
/\
((small_eval_dec:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> 'ffi state#(((v)sem_env),(v))result -> bool) env dst (st, Rerr (Rabort v))=
   (? dev' dcs' fp.
    (RTC (decl_step_reln env)) dst (st with fp_state := fp, dev', dcs') /\
    (decl_step env (st with fp_state := fp, dev', dcs') = Dabort (st.fp_state, v))))`;


(*val small_decl_diverges : forall 'ffi. sem_env v -> small_decl_state 'ffi -> bool*)
val _ = Define `
 ((small_decl_diverges:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> bool) env a=
   (! b.
    (RTC (decl_step_reln env)) a b
    ==>
  (? c.  decl_step_reln env b c)))`;


val _ = export_theory()
