(*
  A copy of the source semantics where Eval is not nondeterministic but
  follows one of the EvalPending, EvalRun, EvalDecs and EvalOracle modes
*)
Theory evalSem
Ancestors
  ast namespace ffi semanticPrimitives evaluate
Libs
  preamble

(* The syntax used here is the source syntax (astTheory), and the
 * semantic values and almost all of the primitives (do_app, pmatch,
 * do_opapp, etc.) are those of the source semantics
 * (semanticPrimitivesTheory).
 *
 * This semantics differs from the source semantics only in how Eval is
 * treated. In the source semantics, a two-argument call to Eval either
 * succeeds, evaluating its declarations and returning the new environment
 * paired with "", or fails, returning the given environment paired with
 * "Compiler error", as decided by the eval oracle. Here the
 * eval_state can be in an EvalPending mode, which waits for a
 * one-argument call to Eval that supplies the compiler state and a
 * closure implementing the compiler and then switches to EvalRun mode
 * (until then, a two-argument call to Eval fails), in an EvalRun mode,
 * where Eval is given only the environment and the declarations and runs
 * the compiler held in the state itself (it fails when the compiler
 * fails), in an EvalDecs mode, where Eval is given the compiler's input
 * and output, checks them and returns just the new environment, or in an
 * EvalOracle mode, where the declarations to be evaluated by Eval are
 * provided by an oracle. The EvalOracle mode is only for use in the
 * compiler proofs. *)

(* Compiler checker for Eval. In the EvalDecs mode, the compiler is
   run (as regular code within the semantics) before Eval is called,
   and these config parameters specify how to interpret the declarations to
   be evaluated and check that the compiler was run correctly.

   Before attempting build a state of this type, find out about
   mk_init_eval_state in source_eval_oracleProof.
*)
Type compiler_args = ``: ((num # num) # v # dec list)``
Type compiler_fun = ``: compiler_args ->
     (v # mlstring # word64 list)option``

Datatype:
 eval_decs_state =
  <|
    compiler : compiler_fun ;
    (* state must be encoded as v somehow *)
    compiler_state : v ;
    env_id_counter : (num # num # num) ;
    (* decs must also be encoded as v *)
    decode_decs : v ->  ( dec list)option ;
    (* the compiler closure given at initialisation (EvalRun mode) *)
    closure : v
  |>
End

Definition add_decs_generation_def:
  add_decs_generation (s:eval_decs_state) =
    case s.env_id_counter of
      (cur_gen,next_id,next_gen) =>
        s with env_id_counter := (next_gen,0,next_gen + 1)
End

(* Concrete, or first-order values, which do not contain code closures and
   are unchanged by many compiler phases. *)
Definition concrete_v_def:
  (concrete_v v ⇔
     case v of
     | Loc _ _ => T
     | Litv _ => T
     | Conv v_ vs => concrete_v_list vs
     | Vectorv vs => concrete_v_list vs
     | _ => F) ∧
  (concrete_v_list [] ⇔ T) ∧
  (concrete_v_list (v::vs) ⇔ concrete_v v ∧ concrete_v_list vs)
Termination
  WF_REL_TAC `measure (λx. case x of INL v => v_size v
                                   | INR vs => list_size v_size vs)`
End

Definition compiler_agrees_def:
  compiler_agrees (f:((num#num)#v#(dec)list ->(v#mlstring#(word64)list)option))
      args (st_v,bs_v,ws_v) ⇔
    case (f args,args,v_to_mlstring bs_v,v_to_word64_list ws_v) of
    | (SOME (st,c_bs,c_ws),(v16,prev_st_v,_),SOME bs,SOME ws) =>
        st = st_v ∧ c_bs = bs ∧ c_ws = ws ∧ concrete_v st_v ∧
        concrete_v prev_st_v
    | _ => F
End

(* cl is a closure that implements the compiler on the declarations
   decoded by decode: in the source semantics without Eval, from any
   state and given enough clock, it returns the result of the compiler,
   or raises Bind when the compiler fails. It may allocate references,
   but changes nothing else in the state. *)
(* the compiler states that successful compilations reach from st0 *)
Inductive compiler_reach:
[~refl:]
  compiler_reach (compiler:compiler_fun) st0 st0
[~step:]
  compiler_reach compiler st0 st1 ∧
  compiler (id,st1,decs) = SOME (st2,bs,ws) ⇒
  compiler_reach compiler st0 st2
End

(* cl implements the compiler on the compiler states reachable from st0 *)
Definition compiler_closure_def:
  compiler_closure (compiler:compiler_fun) decode st0 cl (:'ffi) ⇔
    ∀gen id st_v decs_v decs.
      compiler_reach compiler st0 st_v ∧
      data_v st_v ∧ data_v decs_v ∧ decode decs_v = SOME decs ⇒
      ∃env exp.
        do_opapp [cl; Conv NONE [Conv NONE [nat_to_v gen; nat_to_v id];
                                 st_v; decs_v]] = SOME (env,exp) ∧
        ∀refs po.
          ∃ck refs' po' r.
            (∀(s:'ffi semanticPrimitives$state).
               s.eval_state = NONE ∧ s.refs = refs ∧ s.ptr_eq_oracle = po ⇒
               evaluate$evaluate (s with clock := ck) env [exp] =
                 (s with <| clock := 0; refs := refs ++ refs';
                            ptr_eq_oracle := po' |>, r)) ∧
            case compiler ((gen,id),st_v,decs) of
            | NONE => r = Rerr (Rraise bind_exn_v)
            | SOME (st_v2,bs,ws) =>
                ∃bs_v ws_v.
                  r = Rval [Conv NONE [st_v2; bs_v; ws_v]] ∧
                  v_to_mlstring bs_v = SOME bs ∧
                  v_to_word64_list ws_v = SOME ws
End

(* the pointer equality oracle after the closure cl runs on arg from a
   store refs and a pointer equality oracle po (when cl meets
   compiler_closure, the run does not depend on the rest of the state) *)
Definition closure_ptr_eq_def:
  closure_ptr_eq cl arg refs po (:'ffi) =
    @po'. ∃env exp ck refs' r.
      do_opapp [cl; arg] = SOME (env,exp) ∧
      r ≠ Rerr (Rabort Rtimeout_error) ∧
      ∀(s:'ffi semanticPrimitives$state).
        s.eval_state = NONE ∧ s.refs = refs ∧ s.ptr_eq_oracle = po ⇒
        evaluate$evaluate (s with clock := ck) env [exp] =
          (s with <| clock := 0; refs := refs ++ refs';
                     ptr_eq_oracle := po' |>, r)
End

Type eval_oracle_fun = “:num -> compiler_args”

Datatype:
  eval_oracle_state =
  <|
    oracle : eval_oracle_fun ;
    custom_do_eval : v list -> eval_oracle_fun ->
         ((num # num) # eval_oracle_fun # dec list) option ;
    envs : ((v sem_env) list) list ;
    generation : num
  |>
End

Datatype:
  eval_state =
     EvalDecs eval_decs_state
   | EvalOracle eval_oracle_state
   | EvalRun eval_decs_state
   | EvalPending eval_decs_state
End

Datatype:
  state =
  <| clock : num
   ; refs  : v store
   ; ffi : 'ffi ffi_state
   ; next_type_stamp : num
   ; next_exn_stamp : num
   ; eval_state : eval_state option
   (* oracle deciding whether each successive PtrEq returns the result of
      structural equality (T) or is attenuated to false (F); indexed first by
      install epoch, which advances at every Eval, and then by position
      within that epoch *)
   ; ptr_eq_oracle : num -> num -> bool
   |>
End

(* Primitives that depend on the eval_state *)

Definition lookup_env_def:
  lookup_env s (i,j) =
    case oEL i s.envs of NONE => NONE | SOME gen_envs => oEL j gen_envs
End

Definition add_env_generation_def:
  add_env_generation s =
    s with <|generation := LENGTH s.envs; envs := s.envs ⧺ [[]]|>
End

Definition declare_env_def:
  declare_env (es : eval_state option) env =
    case es of
    | NONE => NONE
    | SOME (EvalDecs s) =>
      (case s.env_id_counter of
         (cur_gen,next_id,next_gen) =>
           SOME
             (Env env (cur_gen,next_id),
              SOME
                (EvalDecs
                   (s with
                    env_id_counter := (cur_gen,next_id + 1,next_gen)))))
    | SOME (EvalRun s) =>
      (case s.env_id_counter of
         (cur_gen,next_id,next_gen) =>
           SOME
             (Env env (cur_gen,next_id),
              SOME
                (EvalRun
                   (s with
                    env_id_counter := (cur_gen,next_id + 1,next_gen)))))
    | SOME (EvalPending s) =>
      (case s.env_id_counter of
         (cur_gen,next_id,next_gen) =>
           SOME
             (Env env (cur_gen,next_id),
              SOME
                (EvalPending
                   (s with
                    env_id_counter := (cur_gen,next_id + 1,next_gen)))))
    | SOME (EvalOracle s') =>
      case oEL s'.generation s'.envs of
      | NONE => NONE
      | SOME gen_envs =>
        SOME
          (Conv NONE [nat_to_v s'.generation; nat_to_v (LENGTH gen_envs)],
           SOME
             (EvalOracle
                (s' with
                 envs := LUPDATE (gen_envs ⧺ [env]) s'.generation s'.envs)))
End

(* get the declarations to be evaluated in the various Eval semantics *)
Definition do_eval_def:
  do_eval vs (es : eval_state option) =
    case (es,vs) of
    | (SOME (EvalDecs s),[Env env id; st_v; decs_v; st_v2; bs_v; ws_v]) =>
      (case s.decode_decs decs_v of
         NONE => NONE
       | SOME decs =>
         if
           st_v = s.compiler_state ∧ concrete_v decs_v ∧
           compiler_agrees s.compiler (id,st_v,decs) (st_v2,bs_v,ws_v)
         then
           SOME
             (env,decs,
              SOME
                (EvalDecs
                   (add_decs_generation (s with compiler_state := st_v2))))
         else NONE)
    | (SOME (EvalOracle s'),vs) =>
      (case s'.custom_do_eval vs s'.oracle of
         NONE => NONE
       | SOME (env_id,oracle,decs) =>
           case lookup_env s' env_id of
             NONE => NONE
           | SOME env =>
               SOME
               (env,decs,
                SOME
                (EvalOracle (add_env_generation (s' with oracle := oracle)))))
    | _ => NONE
End

(* Eval in EvalRun mode: the semantics runs the compiler itself; INR is a
   normal result and INL the result value of a failed Eval *)
Definition do_eval_run_def:
  do_eval_run vs (s : eval_decs_state) =
    case vs of
    | [Env env id; decs_v] =>
      (case s.decode_decs decs_v of
         NONE => NONE
       | SOME decs =>
         if ¬(data_v decs_v ∧ data_v s.compiler_state) then NONE else
         case s.compiler (id,s.compiler_state,decs) of
           NONE => SOME (INL (Conv NONE [Env env id;
                                         Litv (StrLit «Compiler error»)]))
         | SOME (st_v2,_,_) =>
             if data_v st_v2 then
               SOME (INR (env,decs,
                          add_decs_generation (s with compiler_state := st_v2)))
             else NONE)
    | _ => NONE
End

(* the one-argument call to Eval in EvalPending mode: it is given the
   compiler state and a closure implementing the compiler, and switches
   to EvalRun mode *)
Definition do_eval_init_def:
  do_eval_init vs (es : eval_state option) (:'ffi) =
    case (es,vs) of
    | (SOME (EvalPending s),[Conv NONE [st_v; cl]]) =>
        if st_v = s.compiler_state ∧
           compiler_closure s.compiler s.decode_decs s.compiler_state cl (:'ffi)
        then SOME (EvalRun (s with closure := cl)) else NONE
    | _ => NONE
End

(* a two-argument call to Eval that fails: in EvalPending mode, and in
   EvalRun mode when the compiler fails *)
Definition do_eval_fail_def:
  do_eval_fail vs (es : eval_state option) =
    case es of
    | SOME (EvalPending _) =>
        (case vs of
         | [env_v; _] => SOME (Conv NONE [env_v; Litv (StrLit «Compiler error»)])
         | _ => NONE)
    | SOME (EvalRun s) =>
        (case do_eval_run vs s of
         | SOME (INL v) => SOME v
         | _ => NONE)
    | _ => NONE
End

(* the pointer equality oracle after a two-argument call to Eval that
   fails: in EvalRun mode, the compiled code has run the compiler closure *)
Definition eval_fail_ptr_eq_def:
  eval_fail_ptr_eq vs (es : eval_state option) refs po (:'ffi) =
    case (es,vs) of
    | (SOME (EvalRun s),[Env env (gen,id); decs_v]) =>
        closure_ptr_eq s.closure
          (Conv NONE [Conv NONE [nat_to_v gen; nat_to_v id];
                      s.compiler_state; decs_v]) refs po (:'ffi)
    | _ => po
End

(* the result value of a successful Eval, given the eval_state before
   the call and the new environment x: in EvalRun mode, x is paired with
   an empty error message *)
Definition eval_result_def:
  eval_result (es : eval_state option) x =
    case es of
    | SOME (EvalRun _) => Conv NONE [x; Litv (StrLit «»)]
    | _ => x
End

(* conclude an Eval generation *)
Definition reset_env_generation_def:
  reset_env_generation (prior_es : eval_state option)
                       (es : eval_state option) =
    case (prior_es,es) of
    | (SOME (EvalDecs prior_s'),SOME (EvalDecs s')) =>
      (case (prior_s'.env_id_counter,s'.env_id_counter) of
         ((cur_gen,next_id,v5),v6,v8,next_gen) =>
           SOME
             (EvalDecs
                (s' with env_id_counter := (cur_gen,next_id,next_gen))))
    | (SOME (EvalRun prior_s'),SOME (EvalRun s')) =>
      (case (prior_s'.env_id_counter,s'.env_id_counter) of
         ((cur_gen,next_id,v5),v6,v8,next_gen) =>
           SOME
             (EvalRun
                (s' with env_id_counter := (cur_gen,next_id,next_gen))))
    | (SOME (EvalOracle prior_s),SOME (EvalOracle s)) =>
      SOME (EvalOracle (s with generation := prior_s.generation))
    | _ => es
End

(* The semantics is defined here using fix_clock so that HOL4 generates
 * provable termination conditions. However, after termination is proved, we
 * clean up the definition (in HOL4) to remove occurrences of fix_clock. *)

Definition fix_clock_def:
  fix_clock (s:'ffi state) ((s':'ffi state),res) =
    (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)
End

Definition dec_clock_def:
  dec_clock (s:'ffi state) = (s with clock := s.clock − 1)
End

(* a successful call to Eval (failures are handled by do_eval_fail) *)
Definition do_eval_res_def:
  do_eval_res vs (s:'ffi state) :
    'ffi state # (v sem_env # dec list, v) result =
    case do_eval vs s.eval_state of
    | SOME (env1,decs,es1) =>
        (s with <| eval_state := es1
                 ; ptr_eq_oracle := shift_seq 1 s.ptr_eq_oracle |>,
         Rval (env1,decs))
    | NONE =>
      case s.eval_state of
      | SOME (EvalRun r) =>
        (case do_eval_run vs r of
         | SOME (INR (env1,decs,r1)) =>
             (s with <| eval_state := SOME (EvalRun r1)
                      ; ptr_eq_oracle := shift_seq 1 s.ptr_eq_oracle |>,
              Rval (env1,decs))
         | _ => (s,Rerr (Rabort Rtype_error)))
      | _ => (s,Rerr (Rabort Rtype_error))
End

Theorem fix_clock_IMP[local]:
  fix_clock (s:'ffi state) x = (s1,res) ==> s1.clock <= s.clock
Proof
  Cases_on ‘x’ \\ fs [fix_clock_def] \\ rw [] \\ fs []
QED

Definition evaluate_def[nocompute]:
  evaluate st env [] = ((st:'ffi state),Rval [])
  ∧
  evaluate st env (e1::e2::es) =
    (case fix_clock st (evaluate st env [e1]) of
       (st',Rval v1) =>
         (case evaluate st' env (e2::es) of
            (st'',Rval vs) => (st'',Rval (HD v1::vs))
          | (st'',Rerr v8) => (st'',Rerr v8))
     | (st',Rerr v10) => (st',Rerr v10))
  ∧
  evaluate st env [Lit l] = (st,Rval [Litv l])
  ∧
  evaluate st env [Raise e] =
    (case evaluate st env [e] of
       (st',Rval v) => (st',Rerr (Rraise (HD v)))
     | (st',Rerr v8) => (st',Rerr v8))
  ∧
  evaluate st env [Handle e pes] =
    (case fix_clock st (evaluate st env [e]) of
       (st',Rval v7) => (st',Rval v7)
     | (st',Rerr (Rraise v)) =>
       if can_pmatch_all env.c st'.refs (MAP FST pes) v then
         evaluate_match st' env v pes v
       else (st',Rerr (Rabort Rtype_error))
     | (st',Rerr (Rabort v12)) => (st',Rerr (Rabort v12)))
  ∧
  evaluate st env [Con cn es] =
    (if do_con_check env.c cn (LENGTH es) then
       case evaluate st env (REVERSE es) of
         (st',Rval vs) =>
           (case build_conv env.c cn (REVERSE vs) of
              NONE => (st',Rerr (Rabort Rtype_error))
            | SOME v => (st',Rval [v]))
       | (st',Rerr v8) => (st',Rerr v8)
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate st env [Var n] =
    (case nsLookup env.v n of
       NONE => (st,Rerr (Rabort Rtype_error))
     | SOME v => (st,Rval [v]))
  ∧
  evaluate st env [Fun x e] = (st,Rval [Closure env x e])
  ∧
  evaluate st env [App op es] =
   (case fix_clock st (evaluate st env (REVERSE es)) of
    (st', Rval vs) =>
    if op = Opapp then
        (case do_opapp (REVERSE vs) of
          SOME (env',e) =>
            if st'.clock = 0 then
              (st', Rerr (Rabort Rtimeout_error))
            else
              evaluate (dec_clock st') env'  [e]
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
    else if op = ThunkOp ForceThunk then
        (case dest_thunk (REVERSE vs) st'.refs of
         | BadRef => (st', Rerr (Rabort Rtype_error))
         | NotThunk => (st', Rerr (Rabort Rtype_error))
         | IsThunk Evaluated v => (st', Rval [v])
         | IsThunk NotEvaluated f =>
            (case do_opapp [f; Conv NONE []] of
             | SOME (env',e) =>
                 if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error)) else
                   (case evaluate (dec_clock st') env' [e] of
                    | (st2, Rval vs2) =>
                        (case update_thunk (REVERSE vs) st2.refs vs2 of
                         | NONE => (st2, Rerr (Rabort Rtype_error))
                         | SOME refs => (st2 with refs := refs, Rval vs2))
                    | (st2, Rerr e) => (st2, Rerr e))
             | NONE => (st', Rerr (Rabort Rtype_error))))
    else if op = Eval then
      (case do_eval_init (REVERSE vs) st'.eval_state (:'ffi) of
       | SOME es => (st' with eval_state := SOME es, Rval [Conv NONE []])
       | NONE =>
       case do_eval_fail (REVERSE vs) st'.eval_state of
       | SOME v =>
           (st' with ptr_eq_oracle :=
              eval_fail_ptr_eq (REVERSE vs) st'.eval_state st'.refs
                st'.ptr_eq_oracle (:'ffi), Rval [v])
       | NONE =>
        (case fix_clock st' (do_eval_res (REVERSE vs) st') of
          (st1, Rval (env1, decs)) =>
            if st1.clock = 0 then
              (st1, Rerr (Rabort Rtimeout_error))
            else
              (case fix_clock (dec_clock st1)
                      (evaluate_decs (dec_clock st1) env1 decs) of
                (st2, Rval env2) => (case declare_env st2.eval_state
                  (extend_dec_env env2 env1) of
                  SOME (x, es2) => (( st2 with<| eval_state :=
                    (reset_env_generation st'.eval_state es2) |>),
                    Rval [eval_result st'.eval_state x])
                | NONE => (st2, Rerr (Rabort Rtype_error)))
              | (st2, Rerr (Rabort a)) => (st2, Rerr (Rabort a))
              | (st2, Rerr e) => (( st2 with<| eval_state :=
                  (reset_env_generation st'.eval_state st2.eval_state) |>), Rerr e))
        | (st1, Rerr e) => (st1, Rerr e)))
    else if op = PtrEq then
       (case REVERSE vs of
          [v1; v2] =>
            (case do_eq v1 v2 of
               Eq_type_error => (st', Rerr (Rabort Rtype_error))
             | Eq_val b =>
                 (st' with ptr_eq_oracle :=
                    (0 =+ shift_seq 1 (st'.ptr_eq_oracle 0)) st'.ptr_eq_oracle,
                  Rval [Boolv (b ∧ st'.ptr_eq_oracle 0 0)]))
        | _ => (st', Rerr (Rabort Rtype_error)))
    else
        (case do_app (st'.refs,st'.ffi) op (REVERSE vs) of
          NONE => (st', Rerr (Rabort Rtype_error))
        | SOME ((refs,ffi),r) =>
            (( st' with<| refs := refs; ffi := ffi |>), list_result r))
    | res => res)
  ∧
  evaluate st env [Log lop e1 e2] =
    (case fix_clock st (evaluate st env [e1]) of
       (st',Rval v1) =>
         (case do_log lop (HD v1) e2 of
            NONE => (st',Rerr (Rabort Rtype_error))
          | SOME (Exp e) => evaluate st' env [e]
          | SOME (Val v) => (st',Rval [v]))
     | (st',Rerr v9) => (st',Rerr v9))
  ∧
  evaluate st env [If e1 e2 e3] =
    (case fix_clock st (evaluate st env [e1]) of
       (st',Rval v) =>
         (case do_if (HD v) e2 e3 of
            NONE => (st',Rerr (Rabort Rtype_error))
          | SOME e => evaluate st' env [e])
     | (st',Rerr v8) => (st',Rerr v8))
  ∧
  evaluate st env [Mat e pes] =
    (case fix_clock st (evaluate st env [e]) of
       (st',Rval v) =>
         if can_pmatch_all env.c st'.refs (MAP FST pes) (HD v) then
           evaluate_match st' env (HD v) pes bind_exn_v
         else (st',Rerr (Rabort Rtype_error))
     | (st',Rerr v8) => (st',Rerr v8))
  ∧
  evaluate st env [Let xo e1 e2] =
    (case fix_clock st (evaluate st env [e1]) of
       (st',Rval v) =>
         evaluate st' (env with v := nsOptBind xo (HD v) env.v) [e2]
     | (st',Rerr v8) => (st',Rerr v8))
  ∧
  evaluate st env [Letrec funs e] =
    (if ALL_DISTINCT (MAP (λ(x,y,z). x) funs) then
       evaluate st (env with v := build_rec_env funs env env.v) [e]
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate st env [Tannot e t] = evaluate st env [e]
  ∧
  evaluate st env [Lannot e l] = evaluate st env [e]
  ∧
  evaluate st env [Open path e] =
    (case open_dec_env path env of
       NONE => (st,Rerr (Rabort Rtype_error))
     | SOME opened => evaluate st (extend_dec_env opened env) [e])
  ∧
  evaluate_match st env v [] err_v = (st,Rerr (Rraise err_v))
  ∧
  evaluate_match st env v ((p,e)::pes) err_v =
    (if ALL_DISTINCT (pat_bindings p) then
       case pmatch env.c st.refs p v [] of
         No_match => evaluate_match st env v pes err_v
       | Match_type_error => (st,Rerr (Rabort Rtype_error))
       | Match env_v' =>
         evaluate st (env with v := nsAppend (alist_to_ns env_v') env.v) [e]
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate_decs st env [] = (st,Rval <|v := nsEmpty; c := nsEmpty|>)
  ∧
  evaluate_decs st env (d1::d2::ds) =
    (case fix_clock st (evaluate_decs st env [d1]) of
       (st1,Rval env1) =>
         (case evaluate_decs st1 (extend_dec_env env1 env) (d2::ds) of
            (st2,r) => (st2,combine_dec_result env1 r))
     | (st1,Rerr v7) => (st1,Rerr v7))
  ∧
  (* Check constructor applications in their lexical scope, even in bodies
     that this declaration does not evaluate. *)
  evaluate_decs st env [Dlet locs p e] =
    (if ALL_DISTINCT (pat_bindings p) ∧
        check_exp_constructors env.c e
     then
       case evaluate st env [e] of
         (st',Rval v) =>
           (st',
            case pmatch env.c st'.refs p (HD v) [] of
              No_match => Rerr (Rraise bind_exn_v)
            | Match_type_error => Rerr (Rabort Rtype_error)
            | Match new_vals =>
              Rval <|v := alist_to_ns new_vals; c := nsEmpty|>)
       | (st',Rerr err) => (st',Rerr err)
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate_decs st env [Dletrec locs funs] =
    (st,
     if ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
        EVERY (λ(f,n,e). check_exp_constructors env.c e) funs
     then
       Rval <|v := build_rec_env funs env nsEmpty; c := nsEmpty|>
     else Rerr (Rabort Rtype_error))
  ∧
  evaluate_decs st env [Dtype locs tds] =
    (if EVERY check_dup_ctors tds then
       (st with next_type_stamp := st.next_type_stamp + LENGTH tds,
        Rval <|v := nsEmpty; c := build_tdefs st.next_type_stamp tds|>)
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate_decs st env [Dtabbrev locs tvs tn t] =
    (st,Rval <|v := nsEmpty; c := nsEmpty|>)
  ∧
  evaluate_decs st env [Denv n] =
    (case declare_env st.eval_state env of
       NONE => (st,Rerr (Rabort Rtype_error))
     | SOME (x,es') =>
       (st with eval_state := es',Rval <|v := nsSing n x; c := nsEmpty|>))
  ∧
  evaluate_decs st env [Dexn locs cn ts] =
    (st with next_exn_stamp := st.next_exn_stamp + 1,
     Rval
       <|v := nsEmpty;
         c := nsSing cn (LENGTH ts,ExnStamp st.next_exn_stamp)|>)
  ∧
  evaluate_decs st env [Dopen locs path] =
    (case open_dec_env path env of
       NONE => (st,Rerr (Rabort Rtype_error))
     | SOME opened => (st,Rval opened))
  ∧
  evaluate_decs st env [Dmod mn ds] =
    (case evaluate_decs st env ds of
       (st',r) =>
         (st',
          case r of
            Rval env' =>
              Rval <|v := nsLift mn env'.v; c := nsLift mn env'.c|>
          | Rerr err => Rerr err))
  ∧
  evaluate_decs st env [Dlocal lds ds] =
    case fix_clock st (evaluate_decs st env lds) of
      (st1,Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds
    | (st1,Rerr v7) => (st1,Rerr v7)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
         | INL(s,_,es) => (s.clock,list_size exp_size es)
         | INR(INL (s,_,_,pes,_)) => (s.clock,list_size (pair_size pat_size exp_size) pes)
         | INR(INR (s,_,ds)) => (s.clock,list_size dec_size ds))’
  \\ rw [do_if_def,do_log_def,do_eval_res_def,dec_clock_def]
  \\ imp_res_tac fix_clock_IMP \\ fs []
End

(* tidy up evalute_def and evaluate_ind *)

Theorem evaluate_clock:
  (∀(s1:'ffi state) env e r s2.
     evaluate s1 env e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀(s1:'ffi state) env v p v' r s2.
     evaluate_match s1 env v p v' = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀(s1:'ffi state) env ds r s2.
     evaluate_decs s1 env ds = (s2,r) ⇒ s2.clock ≤ s1.clock)
Proof
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  gvs [AllCaseEqs()] >>
  fs[dec_clock_def,fix_clock_def] >> simp[] >>
  imp_res_tac fix_clock_IMP >> fs[] >>
  COND_CASES_TAC >> gs[]
QED

Theorem fix_clock_do_eval_res:
   fix_clock (s:'ffi state) (do_eval_res vs s) = do_eval_res vs s
Proof
  simp [do_eval_res_def]
  \\ rpt (CASE_TAC \\ fs [])
  \\ simp [fix_clock_def, fetch "-" "state_component_equality"]
QED

Theorem fix_clock_evaluate:
   fix_clock (s1:'ffi state) (evaluate s1 env e) = evaluate s1 env e /\
   fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds
Proof
  Cases_on ‘evaluate s1 env e’ \\ fs [fix_clock_def]
  \\ Cases_on ‘evaluate_decs s1 env ds’ \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [arithmeticTheory.MIN_DEF, fetch "-" "state_component_equality"]
QED

Theorem full_evaluate_def[compute] =
  REWRITE_RULE [fix_clock_evaluate, fix_clock_do_eval_res] evaluate_def;

Theorem full_evaluate_ind =
  REWRITE_RULE [fix_clock_evaluate, fix_clock_do_eval_res] evaluate_ind;

(* store evaluate_def and evaluate_ind in parts *)

val eval_pat = “evalSem$evaluate _ _ _”
val evaluate_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term eval_pat)));

val match_pat = “evalSem$evaluate_match _ _ _ _ _”
val evaluate_match_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term match_pat)));

val decs_pat = “evalSem$evaluate_decs _ _ _”
val evaluate_decs_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term decs_pat)));

Theorem evaluate_def[allow_rebind] = LIST_CONJ (evaluate_conjs @ evaluate_match_conjs);

Theorem evaluate_match_def = LIST_CONJ evaluate_match_conjs;

Theorem evaluate_decs_def = LIST_CONJ evaluate_decs_conjs;

Theorem evaluate_ind[allow_rebind] =
  full_evaluate_ind
  |> Q.SPECL [‘P1’,‘P2’,‘λv1 v2 v3. T’]
  |> SIMP_RULE std_ss []
  |> Q.GENL [‘P1’,‘P2’];

Theorem evaluate_match_ind =
  full_evaluate_ind
  |> Q.SPECL [‘λv1 v2 v3. T’,‘P2’,‘λv1 v2 v3. T’]
  |> SIMP_RULE std_ss []
  |> Q.GEN ‘P2’;

Theorem evaluate_decs_ind =
  full_evaluate_ind
  |> Q.SPECL [‘λv1 v2 v3. T’,‘λv1 v2 v3 v4 v5. T’,‘P’]
  |> SIMP_RULE std_ss []
  |> Q.GEN ‘P’;

(* The observable semantics of programs; semantics below corresponds to
   semantics_prog of the source semantics *)

Definition evaluate_prog_with_clock_def:
  evaluate_prog_with_clock (st:'ffi state) env k prog =
    let (st',r) =
      evaluate_decs (st with clock := k) env prog
    in (st'.ffi,r)
End

Definition semantics_determ_def:
  (semantics_determ (st:'ffi state) env prog (Terminate outcome io_list) ⇔
    (* there is a clock for which evaluation terminates, either internally or via
       FFI, and the accumulated io events match the given io_list *)
    (?k ffi r.
      evaluate_prog_with_clock st env k prog = (ffi,r) ∧
      (case r of
       | Rerr (Rabort (Rffi_error outcome')) =>
         outcome = FFI_outcome (outcome')
       | r => r ≠ Rerr (Rabort Rtimeout_error) ∧ outcome = Success) ∧
      (io_list = ffi.io_events) ∧
      (r ≠ Rerr (Rabort Rtype_error)))) ∧
  (semantics_determ st env prog (Diverge io_trace) ⇔
    (* for all clocks, evaluation times out *)
    (!k. ?ffi.
      (evaluate_prog_with_clock st env k prog =
          (ffi, Rerr (Rabort Rtimeout_error)))) ∧
    (* the io_trace is the least upper bound of the set of traces
       produced for each clock *)
     lprefix_lub
       (IMAGE
         (λk. fromList (FST (evaluate_prog_with_clock st env k prog)).io_events)
         UNIV)
       io_trace) ∧
  (semantics_determ st env prog Fail ⇔
    (* there is a clock for which evaluation produces a runtime type error *)
    ∃k.
      SND(evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtype_error))
End

Definition semantics_def:
  semantics (st:'ffi state) env prog b ⇔
    (* the pointer equality oracle is adversarial: a program behaves as it does
       under some oracle *)
    ∃po. semantics_determ (st with ptr_eq_oracle := po) env prog b
End
