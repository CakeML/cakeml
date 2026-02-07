(*
  A small-step semantics for CakeML. This semantics is no longer used
  in the main CakeML development, but is used in PureCake and choreographies.
*)
Theory smallStep
Ancestors
  namespace ast ffi semanticPrimitives

val _ = numLib.temp_prefer_num();



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
  | Cforce num
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
End

Type ctxt = ``: ctxt_frame # v sem_env``

Datatype:
  exp_val_exn = Exp exp | Val v | Exn v
End

(* State for CEK-style expression evaluation
 * - constructor data
 * - the store
 * - the environment for the free variables of the current expression
 * - the current expression to evaluate, or a value if finished
 * - the context stack (continuation) of what to do once the current expression
 *   is finished.  Each entry has an environment for it's free variables *)

Type small_state = ``: v sem_env # ('ffi, v) store_ffi # exp_val_exn # ctxt list``

Datatype:
  e_step_result =
     Estep ('ffi small_state)
   | Eabort abort
   | Estuck
End


(* The semantics are deterministic, and presented functionally instead of
 * relationally for proof rather that readability; the steps are very small: we
 * push individual frames onto the context stack instead of finding a redex in a
 * single step *)

(*val push : forall 'ffi. sem_env v -> store_ffi 'ffi v -> exp -> ctxt_frame -> list ctxt -> e_step_result 'ffi*)
Definition push_def:
 (push: v sem_env -> v store#'ffi ffi_state ->
        exp -> ctxt_frame ->(ctxt_frame#v sem_env)list -> 'ffi e_step_result)
   env s e c' cs = (Estep (env, s, Exp e, ((c',env)::cs)))
End


(*val return : forall 'ffi. sem_env v -> store_ffi 'ffi v -> v -> list ctxt -> e_step_result 'ffi*)
Definition return_def:
 ((return:(v)sem_env ->(v)store#'ffi ffi_state -> v ->(ctxt)list -> 'ffi e_step_result) env s v c=  (Estep (env, s, Val v, c)))
End

Definition application_def:
 (application:op ->(v)sem_env ->(v)store#'ffi ffi_state -> (v)list ->(ctxt)list -> 'ffi e_step_result) op env s vs c=
   (case getOpClass op of
      FunApp =>
      (case do_opapp vs of
          SOME (env,e) => Estep (env, s, Exp e, c)
        | NONE => Eabort Rtype_error)
     | Force => (
        case vs of
        | [Loc b n] => (
            case dest_thunk [Loc b n] (FST s) of
            | BadRef => Eabort Rtype_error
            | NotThunk => Eabort Rtype_error
            | IsThunk Evaluated v => Estep (env, s, Val v, c)
            | IsThunk NotEvaluated f =>
                Estep (env, s, Val f,
                       (Capp Opapp [Conv NONE []] () [], env)::(Cforce n, env)::c))
        | _ => Eabort Rtype_error)
     | _ =>
      (case do_app s op vs of
          SOME (s',r) =>
          (case r of
              Rerr (Rraise v) => Estep (env,s', Exn v, c)
            | Rerr (Rabort a) => Eabort a
            | Rval v => return env s' v c
          )
        | NONE => Eabort Rtype_error)
    )
End

(* apply a context to a value *)
(*val continue : forall 'ffi. store_ffi 'ffi v -> v -> list ctxt -> e_step_result 'ffi*)
Definition continue_def:
 ((continue:(v)store#'ffi ffi_state -> v ->(ctxt_frame#(v)sem_env)list -> 'ffi e_step_result) s v cs=
   ((case cs of
      [] => Estuck
    | (Craise () , env) :: c => Estep (env, s, Exn v, c)
    | (Chandle ()  pes, env) :: c =>
        return env s v c
    | (Capp op vs ()  [], env) :: c =>
        application op env s (v::vs) c
    | (Capp op vs ()  (e::es), env) :: c =>
        push env s e (Capp op (v::vs) ()  es) c
    | (Cforce n, env) :: c => (
        case dest_thunk [v] (FST s) of
        | BadRef => Eabort Rtype_error
        | NotThunk => (
            case store_assign n (Thunk Evaluated v) (FST s) of
            | SOME s' => return env (s', SND s) v c
            | NONE => Eabort Rtype_error)
        | IsThunk v3 v4 => Eabort Rtype_error)
    | (Clog l ()  e, env) :: c =>
        (case do_log l v e of
            SOME (Exp e) => Estep (env, s, Exp e, c)
          | SOME (Val v) => return env s v c
          | NONE => Eabort Rtype_error
        )
    | (Cif ()  e1 e2, env) :: c =>
        (case do_if v e1 e2 of
            SOME e => Estep (env, s, Exp e, c)
          | NONE => Eabort Rtype_error
        )
    | (Cmat_check ()  pes err_v, env) :: c =>
        if can_pmatch_all env.c (FST s) (MAP FST pes) v then
          Estep (env, s, Val v, ((Cmat ()  pes err_v,env)::c))
        else
          Eabort Rtype_error
    | (Cmat ()  [] err_v, env) :: c =>
        Estep (env, s, Exn err_v, c)
    | (Cmat ()  ((p,e)::pes) err_v, env) :: c =>
        if ALL_DISTINCT (pat_bindings p []) then
          (case pmatch env.c (FST s) p v [] of
              Match_type_error => Eabort Rtype_error
            | No_match => Estep (env, s, Val v, ((Cmat ()  pes err_v,env)::c))
            | Match env' => Estep (( env with<| v := (nsAppend (alist_to_ns env') env.v) |>), s, Exp e, c)
          )
        else
          Eabort Rtype_error
    | (Clet n ()  e, env) :: c =>
        Estep (( env with<| v := (nsOptBind n v env.v) |>), s, Exp e, c)
    | (Ccon n vs ()  [], env) :: c =>
        if do_con_check env.c n (LENGTH vs +( 1 : num)) then
           (case build_conv env.c n (v::vs) of
               NONE => Eabort Rtype_error
             | SOME v => return env s v c
           )
        else
          Eabort Rtype_error
    | (Ccon n vs ()  (e::es), env) :: c =>
        if do_con_check env.c n (((LENGTH vs +( 1 : num)) +( 1 : num)) + LENGTH es) then
          push env s e (Ccon n (v::vs) ()  es) c
        else
          Eabort Rtype_error
    | (Ctannot ()  t, env) :: c =>
        return env s v c
    | (Clannot ()  l, env) :: c =>
        return env s v c
  )))
End


(* The single step expression evaluator.  Returns None if there is nothing to
 * do, but no type error.  Returns Type_error on encountering free variables,
 * mis-applied (or non-existent) constructors, and when the wrong kind of value
 * if given to a primitive.  Returns Bind_error when no pattern in a match
 * matches the value.  Otherwise it returns the next state *)

(*val e_step : forall 'ffi. small_state 'ffi -> e_step_result 'ffi*)
Definition e_step_def:
 ((e_step:(v)sem_env#((v)store#'ffi ffi_state)#exp_val_exn#(ctxt)list -> 'ffi e_step_result) (env, s, ev, c)=
   ((case ev of
      Val v  =>
        continue s v c
    | Exp e =>
        (case e of
            Lit l => return env s (Litv l) c
          | Raise e =>
              push env s e (Craise () ) c
          | Handle e pes =>
              push env s e (Chandle ()  pes) c
          | Con n es =>
              if do_con_check env.c n (LENGTH es) then
                (case REVERSE es of
                    [] =>
                      (case build_conv env.c n [] of
                          NONE => Eabort Rtype_error
                        | SOME v => return env s v c
                      )
                  | e::es =>
                      push env s e (Ccon n [] ()  es) c
                )
              else
                Eabort Rtype_error
          | Var n =>
              (case nsLookup env.v n of
                  NONE => Eabort Rtype_error
                | SOME v =>
                    return env s v c
              )
          | Fun n e => return env s (Closure env n e) c
          | App op es =>
              (case REVERSE es of
                  [] => application op env s [] c
                | (e::es) => push env s e (Capp op [] ()  es) c
              )
          | Log l e1 e2 => push env s e1 (Clog l ()  e2) c
          | If e1 e2 e3 => push env s e1 (Cif ()  e2 e3) c
          | Mat e pes => push env s e (Cmat_check ()  pes bind_exn_v) c
          | Let n e1 e2 => push env s e1 (Clet n ()  e2) c
          | Letrec funs e =>
              if ~ (ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs)) then
                Eabort Rtype_error
              else
                Estep (( env with<| v := (build_rec_env funs env env.v) |>),
                       s, Exp e, c)
          | Tannot e t => push env s e (Ctannot ()  t) c
          | Lannot e l => push env s e (Clannot ()  l) c
        )
    | Exn v =>
       case c of
       | [] => Estuck
       | (Chandle () pes, env') :: c =>
            Estep (env, s, Val v, (Cmat_check () pes v, env') :: c)
       | _ :: c => Estep (env, s, Exn v, c)
  )))
End


(* Define a semantic function using the steps *)

(*val e_step_reln : forall 'ffi. small_state 'ffi -> small_state 'ffi -> bool*)
(*val small_eval : forall 'ffi. sem_env v -> store_ffi 'ffi v -> exp -> list ctxt -> store_ffi 'ffi v * result v v -> bool*)

Definition e_step_reln_def:
 ((e_step_reln:(v)sem_env#('ffi,(v))store_ffi#exp_val_exn#(ctxt)list ->(v)sem_env#('ffi,(v))store_ffi#exp_val_exn#(ctxt)list -> bool) st1 st2=
   (e_step st1 = Estep st2))
End

Definition small_eval_def:
((small_eval:(v)sem_env ->(v)store#'ffi ffi_state -> exp ->(ctxt)list ->((v)store#'ffi ffi_state)#((v),(v))result -> bool) env s e c (s', Rval v)=
   (? env'. (RTC (e_step_reln)) (env,s,Exp e,c) (env',s',Val v,[])))
/\
((small_eval:(v)sem_env ->(v)store#'ffi ffi_state -> exp ->(ctxt)list ->((v)store#'ffi ffi_state)#(v,v)result -> bool) env s e c (s', Rerr (Rraise v))=
   (? env'. (RTC (e_step_reln)) (env,s,Exp e,c) (env',s',Exn v,[])))
/\
((small_eval:(v)sem_env ->(v)store#'ffi ffi_state -> exp ->(ctxt)list ->((v)store#'ffi ffi_state)#(v,v)result -> bool) env s e c (s', Rerr (Rabort a))=
   (? env' e' c'.
    (RTC (e_step_reln)) (env,s,Exp e,c) (env',s',e',c') /\
    (e_step (env',s',e',c') = Eabort a)))
End


(*val e_diverges : forall 'ffi. sem_env v -> store_ffi 'ffi v -> exp -> bool*)
Definition e_diverges_def:
 ((e_diverges:(v)sem_env ->(v)store#'ffi ffi_state -> exp -> bool) env s e =
   (! env' s' e' c'.
    (RTC (e_step_reln)) (env,s,Exp e,[]) (env',s',e',c')
    ==>
(? env'' s'' e'' c''.
      e_step_reln (env',s',e',c') (env'',s'',e'',c''))))
End



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
  | Dabort abort
  | Ddone
  | Draise v
End

(* Helper functions *)

(*val empty_dec_env : forall 'v. sem_env 'v*)
Definition empty_dec_env_def:
 ((empty_dec_env:'v sem_env)=  (<| v := nsEmpty ; c := nsEmpty |>))
End


(*val lift_dec_env : forall 'v. modN -> sem_env 'v -> sem_env 'v*)
Definition lift_dec_env_def:
 ((lift_dec_env:mlstring -> 'v sem_env -> 'v sem_env) mn env=  (<| v := (nsLift mn env.v) ; c := (nsLift mn env.c) |>))
End


(* Get the "current" sem_env given the context *)
(*val collapse_env : sem_env v -> decl_ctxt -> sem_env v*)
Definition collapse_env_def:
 ((collapse_env:(v)sem_env ->(decl_ctxt_frame)list ->(v)sem_env) base c=
   ((case c of
    [] => base
  | Cdmod mn env ds :: cs => extend_dec_env env (collapse_env base cs)
  | CdlocalL lenv lds gds :: cs =>
      extend_dec_env lenv (collapse_env base cs)
  | CdlocalG lenv genv gds :: cs =>
      extend_dec_env (extend_dec_env genv lenv) (collapse_env base cs)
 )))
End



(* Apply a context to the env resulting from evaluating a declaration *)
(*val decl_continue : forall 'ffi. sem_env v -> state 'ffi -> decl_ctxt -> decl_step_result 'ffi*)
Definition decl_continue_def:
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
  )))
End


(*val decl_step : forall 'ffi. sem_env v -> small_decl_state 'ffi -> decl_step_result 'ffi*)
Definition decl_step_def:
 ((decl_step:(v)sem_env -> 'ffi state#decl_eval#(decl_ctxt_frame)list -> 'ffi decl_step_result) benv (st, dev, c)=
   ((case dev of
    Decl d =>
      (case d of
        Dlet locs p e =>
          if ALL_DISTINCT (pat_bindings p []) ∧
             every_exp (one_con_check (collapse_env benv c).c) e
          then
            Dstep (st, ExpVal (collapse_env benv c) (Exp e) [] locs p, c)
          else Dabort Rtype_error
      | Dletrec locs funs =>
          if ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) ∧
             EVERY (\ (x,y,z) .
               every_exp (one_con_check (collapse_env benv c).c) z) funs
          then
            Dstep (st,
              Env <| v := (build_rec_env funs (collapse_env benv c) nsEmpty); c := nsEmpty |>,
              c)
          else Dabort Rtype_error
      | Dtype locs tds =>
          if EVERY check_dup_ctors tds then
            Dstep (
              ( st with<| next_type_stamp := (st.next_type_stamp + LENGTH tds) |>),
              Env <| v := nsEmpty; c := (build_tdefs st.next_type_stamp tds) |>,
              c)
          else Dabort Rtype_error
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
          | NONE => Dabort Rtype_error
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
            | No_match => Draise bind_exn_v
            | Match_type_error => Dabort Rtype_error
            )
          else Dabort Rtype_error
      | (Exn v, []) => Draise v
      | _ =>
        (case e_step (env, (st.refs, st.ffi), ev, ec) of
          Estep (env', (refs', ffi'), ev', ec') =>
            Dstep (( st with<| refs := refs' ; ffi := ffi'; |>),
              ExpVal env' ev' ec' locs p, c)
        | Eabort a => Dabort a
        | Estuck => Ddone (* cannot happen *)
        )
      )
  )))
End


(*val decl_step_reln : forall 'ffi. sem_env v -> small_decl_state 'ffi -> small_decl_state 'ffi -> bool*)

(*val small_eval_dec : forall 'ffi. sem_env v -> small_decl_state 'ffi -> state 'ffi * result (sem_env v) v -> bool*)

Definition decl_step_reln_def:
 ((decl_step_reln:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> 'ffi state#decl_eval#decl_ctxt -> bool) env st1 st2=
   (decl_step env st1 = Dstep st2))
End


Definition small_eval_dec_def:
((small_eval_dec:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> 'ffi state#(((v)sem_env),(v))result -> bool) env dst (st, Rval e)=
   ((RTC (decl_step_reln env)) dst (st, Env e, [])))
/\
((small_eval_dec:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> 'ffi state#(((v)sem_env),(v))result -> bool) env dst (st, Rerr (Rraise v))=
   (? dev' dcs'.
    (RTC (decl_step_reln env)) dst (st, dev', dcs') /\
    (decl_step env (st, dev', dcs') = Draise v)))
/\
((small_eval_dec:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> 'ffi state#(((v)sem_env),(v))result -> bool) env dst (st, Rerr (Rabort v))=
   (? dev' dcs'.
    (RTC (decl_step_reln env)) dst (st, dev', dcs') /\
    (decl_step env (st, dev', dcs') = Dabort v)))
End


(*val small_decl_diverges : forall 'ffi. sem_env v -> small_decl_state 'ffi -> bool*)
Definition small_decl_diverges_def:
 ((small_decl_diverges:(v)sem_env -> 'ffi state#decl_eval#decl_ctxt -> bool) env a=
   (! b.
    (RTC (decl_step_reln env)) a b
    ==>
  (? c.  decl_step_reln env b c)))
End
