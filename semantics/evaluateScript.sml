(*
  Functional big-step semantics for evaluation of CakeML programs.
*)
open HolKernel Parse boolLib bossLib;
open libTheory astTheory namespaceTheory ffiTheory semanticPrimitivesTheory;

val _ = numLib.prefer_num();

val _ = new_theory "evaluate"

(* The semantics is defined here using fix_clock so that HOL4 generates
 * provable termination conditions. However, after termination is proved, we
 * clean up the definition (in HOL4) to remove occurrences of fix_clock. *)

Definition fix_clock_def:
  fix_clock s (s',res) =
    (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)
End

Definition dec_clock_def:
  dec_clock s = (s with clock := s.clock − 1)
End

Definition do_eval_res_def:
  do_eval_res vs s =
    case do_eval vs s.eval_state of
    | NONE => (s,Rerr (Rabort Rtype_error))
    | SOME (env1,decs,es1) => (s with eval_state := es1,Rval (env1,decs))
End

(* list_result is equivalent to map_result (\v. [v]) I, where map_result is
 * defined in evalPropsTheory *)
Definition list_result_def[simp]:
  list_result (Rval v) = Rval [v] ∧
  list_result (Rerr e) = Rerr e
End

Triviality fix_clock_IMP:
  fix_clock s x = (s1,res) ==> s1.clock <= s.clock
Proof
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []
QED

Triviality list_size_REVERSE:
  ∀xs. list_size f (REVERSE xs) = list_size f xs
Proof
  Induct \\ fs [listTheory.list_size_def,listTheory.list_size_append]
QED

Definition evaluate_def[nocompute]:
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env []=  (st, Rval []))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env (e1::e2::es)=
   ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v1) =>
      (case evaluate st' env (e2::es) of
        (st'', Rval vs) => (st'', Rval (HD v1::vs))
      | res => res
      )
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Lit l]=  (st, Rval [Litv l]))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Raise e]=
   ((case evaluate st env [e] of
    (st', Rval v) => (st', Rerr (Rraise (HD v)))
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Handle e pes]=
   ((case fix_clock st (evaluate st env [e]) of
    (st', Rerr (Rraise v)) =>
      if can_pmatch_all env.c st'.refs (MAP FST pes) v
      then evaluate_match st' env v pes v
      else (st', Rerr (Rabort Rtype_error))
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Con cn es]=
   (if do_con_check env.c cn (LENGTH es) then
    (case evaluate st env (REVERSE es) of
      (st', Rval vs) =>
        (case build_conv env.c cn (REVERSE vs) of
          SOME v => (st', Rval [v])
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
    | res => res
    )
  else (st, Rerr (Rabort Rtype_error))))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Var n]=
   ((case nsLookup env.v n of
    SOME v => (st, Rval [v])
  | NONE => (st, Rerr (Rabort Rtype_error))
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Fun x e]=  (st, Rval [Closure env x e]))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [App op es]=
   ((case fix_clock st (evaluate st env (REVERSE es)) of
    (st', Rval vs) =>
      if op = Opapp then
        (case do_opapp (REVERSE vs) of
          SOME (env',e) =>
            if st'.clock =( 0 : num) then
              (st', Rerr (Rabort Rtimeout_error))
            else
              evaluate (dec_clock st') env' [e]
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
      else if op = Eval then
        (case fix_clock st' (do_eval_res (REVERSE vs) st') of
          (st1, Rval (env1, decs)) =>
            if st1.clock =( 0 : num) then
              (st1, Rerr (Rabort Rtimeout_error))
            else
              (case fix_clock (dec_clock st1)
                      (evaluate_decs (dec_clock st1) env1 decs) of
                (st2, Rval env2) => (case declare_env st2.eval_state
                  (extend_dec_env env2 env1) of
                  SOME (x, es2) => (( st2 with<| eval_state :=
                    (reset_env_generation st'.eval_state es2) |>), Rval [x])
                | NONE => (st2, Rerr (Rabort Rtype_error))
                )
              | (st2, Rerr (Rabort a)) => (st2, Rerr (Rabort a))
              | (st2, Rerr e) => (( st2 with<| eval_state :=
                  (reset_env_generation st'.eval_state st2.eval_state) |>), Rerr e)
              )
        | (st1, Rerr e) => (st1, Rerr e)
        )
      else
        (case do_app (st'.refs,st'.ffi) op (REVERSE vs) of
          SOME ((refs,ffi),r) => (( st' with<| refs := refs; ffi := ffi |>), list_result r)
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Log lop e1 e2]=
   ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v1) =>
      (case do_log lop (HD v1) e2 of
        SOME (Exp e) => evaluate st' env [e]
      | SOME (Val v) => (st', Rval [v])
      | NONE => (st', Rerr (Rabort Rtype_error))
      )
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [If e1 e2 e3]=
   ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v) =>
      (case do_if (HD v) e2 e3 of
        SOME e => evaluate st' env [e]
      | NONE => (st', Rerr (Rabort Rtype_error))
      )
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Mat e pes]=
   ((case fix_clock st (evaluate st env [e]) of
    (st', Rval v) =>
      if can_pmatch_all env.c st'.refs (MAP FST pes) (HD v)
      then evaluate_match st' env (HD v) pes bind_exn_v
      else (st', Rerr (Rabort Rtype_error))
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Let xo e1 e2]=
   ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v) => evaluate st' ( env with<| v := (nsOptBind xo (HD v) env.v) |>) [e2]
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Letrec funs e]=
   (if ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) then
    evaluate st ( env with<| v := (build_rec_env funs env env.v) |>) [e]
  else
    (st, Rerr (Rabort Rtype_error))))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Tannot e t]=
   (evaluate st env [e]))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Lannot e l]=
   (evaluate st env [e]))
/\
((evaluate_match:'ffi state ->(v)sem_env -> v ->(pat#exp)list -> v -> 'ffi state#(((v)list),(v))result) st env v [] err_v=  (st, Rerr (Rraise err_v)))
/\
((evaluate_match:'ffi state ->(v)sem_env -> v ->(pat#exp)list -> v -> 'ffi state#(((v)list),(v))result) st env v ((p,e)::pes) err_v=
    (if ALL_DISTINCT (pat_bindings p []) then
    (case pmatch env.c st.refs p v [] of
      Match env_v' => evaluate st ( env with<| v := (nsAppend (alist_to_ns env_v') env.v) |>) [e]
    | No_match => evaluate_match st env v pes err_v
    | Match_type_error => (st, Rerr (Rabort Rtype_error))
    )
  else (st, Rerr (Rabort Rtype_error))))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env []=  (st, Rval <| v := nsEmpty; c := nsEmpty |>))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env (d1::d2::ds)=
   ((case fix_clock st (evaluate_decs st env [d1]) of
    (st1, Rval env1) =>
    (case evaluate_decs st1 (extend_dec_env env1 env) (d2::ds) of
      (st2,r) => (st2, combine_dec_result env1 r)
    )
  | res => res
  )))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dlet locs p e]=
   (if ALL_DISTINCT (pat_bindings p []) then
    (case evaluate st env [e] of
      (st', Rval v) =>
        (st',
         (case pmatch env.c st'.refs p (HD v) [] of
           Match new_vals => Rval <| v := (alist_to_ns new_vals); c := nsEmpty |>
         | No_match => Rerr (Rraise bind_exn_v)
         | Match_type_error => Rerr (Rabort Rtype_error)
         ))
    | (st', Rerr err) => (st', Rerr err)
    )
  else
    (st, Rerr (Rabort Rtype_error))))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dletrec locs funs]=
   (st,
   (if ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) then
     Rval <| v := (build_rec_env funs env nsEmpty); c := nsEmpty |>
   else
     Rerr (Rabort Rtype_error))))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dtype locs tds]=
   (if EVERY check_dup_ctors tds then
    (( st with<| next_type_stamp := (st.next_type_stamp + LENGTH tds) |>),
     Rval <| v := nsEmpty; c := (build_tdefs st.next_type_stamp tds) |>)
  else
    (st, Rerr (Rabort Rtype_error))))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dtabbrev locs tvs tn t]=
   (st, Rval <| v := nsEmpty; c := nsEmpty |>))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Denv n]=
   ((case declare_env st.eval_state env of
    SOME (x, es') => (( st with<| eval_state := es' |>),
        Rval <| v := (nsSing n x); c := nsEmpty |>)
  | NONE => (st, Rerr (Rabort Rtype_error))
  )))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dexn locs cn ts]=
   (( st with<| next_exn_stamp := (st.next_exn_stamp +( 1 : num)) |>),
   Rval <| v := nsEmpty; c := (nsSing cn (LENGTH ts, ExnStamp st.next_exn_stamp)) |>))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dmod mn ds]=
   ((case evaluate_decs st env ds of
    (st', r) =>
      (st',
       (case r of
         Rval env' => Rval <| v := (nsLift mn env'.v); c := (nsLift mn env'.c) |>
       | Rerr err => Rerr err
       ))
  )))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dlocal lds ds]=
   ((case fix_clock st (evaluate_decs st env lds) of
    (st1, Rval env1) =>
    evaluate_decs st1 (extend_dec_env env1 env) ds
  | res => res
  )))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
         | INL(s,_,es) => (s.clock,list_size exp_size es)
         | INR(INL (s,_,_,pes,_)) => (s.clock,list_size (pair_size pat_size exp_size) pes)
         | INR(INR (s,_,ds)) => (s.clock,list_size dec_size ds))’
  \\ rw [do_if_def,do_log_def,do_eval_res_def,dec_clock_def]
  \\ imp_res_tac fix_clock_IMP \\ fs []
  \\ fs [listTheory.list_size_def,dec_size_eq,exp_size_eq,list_size_REVERSE]
End

(* tidy up evalute_def and evaluate_ind *)

Theorem evaluate_clock:
   (∀(s1:'ffi state) env e r s2. evaluate s1 env e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
   (∀(s1:'ffi state) env v p v' r s2. evaluate_match s1 env v p v' = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
   (∀(s1:'ffi state) env ds r s2. evaluate_decs s1 env ds = (s2,r) ⇒ s2.clock ≤ s1.clock)
Proof
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  gvs [AllCaseEqs()] >>
  fs[dec_clock_def,fix_clock_def] >> simp[] >>
  imp_res_tac fix_clock_IMP >> fs[]
QED

Theorem fix_clock_do_eval_res:
   fix_clock s (do_eval_res vs s) = do_eval_res vs s
Proof
  simp [do_eval_res_def]
  \\ rpt (CASE_TAC \\ fs [])
  \\ simp [fix_clock_def, state_component_equality]
QED

Theorem fix_clock_evaluate:
   fix_clock s1 (evaluate s1 env e) = evaluate s1 env e /\
   fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds
Proof
  Cases_on `evaluate s1 env e` \\ fs [fix_clock_def]
  \\ Cases_on `evaluate_decs s1 env ds` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [arithmeticTheory.MIN_DEF,state_component_equality]
QED

Theorem full_evaluate_def[compute] =
  REWRITE_RULE [fix_clock_evaluate, fix_clock_do_eval_res] evaluate_def;

Theorem full_evaluate_ind =
  REWRITE_RULE [fix_clock_evaluate, fix_clock_do_eval_res] evaluate_ind;

(* store evaluate_def and evaluate_ind in parts *)

val eval_pat = ``evaluate$evaluate _ _ _``
val evaluate_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term eval_pat)));

val match_pat = ``evaluate$evaluate_match _ _ _ _ _``
val evaluate_match_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term match_pat)));

val decs_pat = ``evaluate$evaluate_decs _ _ _``
val evaluate_decs_conjs =
  CONJUNCTS full_evaluate_def
  |> filter (fn th => (th |> SPEC_ALL |> concl |> dest_eq |> fst
                          |> can (match_term decs_pat)));

Theorem evaluate_def = LIST_CONJ (evaluate_conjs @ evaluate_match_conjs);

Theorem evaluate_match_def = LIST_CONJ evaluate_match_conjs;

Theorem evaluate_decs_def = LIST_CONJ evaluate_decs_conjs;

Theorem evaluate_ind =
  full_evaluate_ind
  |> Q.SPECL [`P1`,`P2`,`\v1 v2 v3. T`]
  |> SIMP_RULE std_ss []
  |> Q.GENL [`P1`,`P2`];

Theorem evaluate_match_ind =
  full_evaluate_ind
  |> Q.SPECL [`\v1 v2 v3. T`,`P2`,`\v1 v2 v3. T`]
  |> SIMP_RULE std_ss []
  |> Q.GEN `P2`;

Theorem evaluate_decs_ind =
  full_evaluate_ind
  |> Q.SPECL [`\v1 v2 v3. T`,`\v1 v2 v3 v4 v5. T`, `P`]
  |> SIMP_RULE std_ss []
  |> Q.GEN `P`;

val _ = export_theory()
