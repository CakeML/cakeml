open preamble astTheory semanticPrimitivesTheory ffiTheory
open evalPropsTheory
(* ... for map_result and do_log_thm *)

val _ = new_theory"funBigStep";

(* TODO: move *)
val all_env_with_env_def = Define`
  all_env_with_env (all_env:all_env) env =
    ((all_env_to_menv all_env,
      all_env_to_cenv all_env,
      env):all_env)`;

val exp6_size_APPEND = Q.store_thm("exp6_size_APPEND",
  `∀l1 l2. exp6_size (l1 ++ l2) = exp6_size l1 + exp6_size l2`,
  Induct >> simp[exp_size_def])

val exp6_size_REVERSE = Q.store_thm("exp6_size_REVERSE",
  `∀ls. exp6_size (REVERSE ls) = exp6_size ls`,
  ho_match_mp_tac SNOC_INDUCT >>
  simp[exp_size_def,REVERSE_SNOC,SNOC_APPEND,exp6_size_APPEND])
(* -- *)

val _ = Datatype`
  state = <| clock : num
           ; refs  : v store
           ; io    : io_trace
           |>`;

val state_component_equality = theorem"state_component_equality";

val check_clock_def = Define`
  check_clock s' s =
    s' with clock := (if s'.clock ≤ s.clock then s'.clock else s.clock)`;

val check_clock_id = Q.store_thm("check_clock_id",
  `s'.clock ≤ s.clock ⇒ check_clock s' s = s'`,
  EVAL_TAC >> rw[state_component_equality])

val dec_clock_def = Define`
  dec_clock s = s with clock := s.clock - 1`;

val evaluate_def = tDefine "evaluate" `
  (evaluate ([]:exp list,env:all_env,s:funBigStep$state) = (Rval [],s)) ∧
  (evaluate (x::y::xs,env,s) =
   case evaluate ([x],env,s) of
   | (Rval v1,s1) =>
       (case evaluate (y::xs,env,check_clock s1 s) of
        | (Rval vs,s2) => (Rval (HD v1::vs),s2)
        | res => res)
   | res => res) ∧
  (evaluate ([Lit l],env,s) = (Rval [Litv l],s)) ∧
  (evaluate ([Raise e],env,s) =
   case evaluate ([e],env,s) of
   | (Rval v,s) => (Rerr (Rraise (HD v)),s)
   | res => res) ∧
  (evaluate ([Handle e pes],env,s) =
   case evaluate ([e],env,s) of
   | (Rerr (Rraise v),s') => evaluate_match (pes,v,v,env,check_clock s' s)
   | res => res) ∧
  (evaluate ([Con cn es],env,s) =
   if do_con_check (all_env_to_cenv env) cn (LENGTH es) then
     (case evaluate (REVERSE es, env, s) of
      | (Rval vs,s) =>
        (case build_conv (all_env_to_cenv env) cn (REVERSE vs) of
         | SOME v => (Rval [v], s)
         | NONE => (Rerr (Rabort Rtype_error),s))
      | res => res)
   else (Rerr (Rabort Rtype_error),s)) ∧
  (evaluate ([Var n],env,s) =
   case lookup_var_id n env of
   | SOME v => (Rval [v], s)
   | NONE => (Rerr (Rabort Rtype_error), s)) ∧
  (evaluate ([Fun n e],env,s) = (Rval [Closure env n e],s)) ∧
  (evaluate ([App op es],env,s) =
   case evaluate (REVERSE es,env,s) of
   | (Rval vs,s') =>
     if op = Opapp then
       (case do_opapp (REVERSE vs) of
        | SOME (env',e) =>
          if s'.clock ≠ 0 ∧ s.clock ≠ 0 then
            evaluate ([e],env',dec_clock (check_clock s' s))
          else
            (Rerr (Rabort Rtimeout_error),s')
        | NONE => (Rerr (Rabort Rtype_error), s'))
     else
       (case do_app (s'.refs,s'.io) op (REVERSE vs) of
        | (SOME ((refs,io),r)) => (map_result (λv. [v]) I r, s' with <| refs := refs; io := io |>)
        | NONE => (Rerr (Rabort Rtype_error),s'))
   | res => res) ∧
  (evaluate ([Log op e1 e2],env,s) =
   case evaluate ([e1],env,s) of
   | (Rval v1,s') =>
     (case do_log op (HD v1) e2 of
      | SOME (Exp e) => evaluate ([e],env,check_clock s' s)
      | SOME (Val v) => (Rval [v], s')
      | NONE => (Rerr (Rabort Rtype_error), s'))
   | res => res) ∧
  (evaluate ([If e1 e2 e3],env,s) =
   case evaluate ([e1],env,s) of
   | (Rval v,s') =>
     (case do_if (HD v) e2 e3 of
      | SOME e => evaluate ([e],env,check_clock s' s)
      | NONE => (Rerr (Rabort Rtype_error),s'))
   | res => res) ∧
  (evaluate ([Mat e pes],env,s) =
   case evaluate ([e],env,s) of
   | (Rval v,s') =>
       evaluate_match (pes,HD v,Conv(SOME("Bind",TypeExn(Short"Bind")))[],env,check_clock s' s)
   | res => res) ∧
  (evaluate ([Let n e1 e2],env,s) =
   case evaluate ([e1],env,s) of
   | (Rval v,s') => evaluate ([e2],all_env_with_env env (opt_bind n (HD v) (all_env_to_env env)),check_clock s' s)
   | res => res) ∧
  (evaluate ([Letrec funs e],env,s) =
   if ALL_DISTINCT (MAP FST funs) then
     evaluate ([e],all_env_with_env env (build_rec_env funs env (all_env_to_env env)),s)
   else (Rerr (Rabort Rtype_error),s)) ∧
  (evaluate_match ([],v,err_v,env,s) = (Rerr (Rraise err_v),s)) ∧
  (evaluate_match ((p,e)::pes,v,err_v,env,s) =
   if ALL_DISTINCT (pat_bindings p []) then
     (case pmatch (all_env_to_cenv env) s.refs p v (all_env_to_env env) of
      | Match env' => evaluate ([e],all_env_with_env env env',s)
      | No_match => evaluate_match (pes,v,err_v,env,s)
      | Match_type_error => (Rerr (Rabort Rtype_error),s))
   else (Rerr (Rabort Rtype_error), s))`
     (wf_rel_tac`inv_image ($< LEX $<)
                 (λx.
                    case x of
                    | INL(es,_,s) => (s.clock,exps_size es)
                    | INR(pes,_,_,_,s) => (s.clock,pes_size pes))` >>
      rw[terminationTheory.size_abbrevs,exp_size_def,
         check_clock_def,dec_clock_def,LESS_OR_EQ,
         do_if_def,do_log_thm] >>
      simp[exp6_size_REVERSE])

val evaluate_ind = theorem"evaluate_ind";

val evaluate_clock = Q.store_thm("evaluate_clock",
  `(∀p r s2. evaluate p = (r,s2) ⇒ s2.clock ≤ (SND(SND p)).clock) ∧
   (∀p r s2. evaluate_match p = (r,s2) ⇒ s2.clock ≤ (SND(SND(SND(SND p)))).clock)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[] >> rw[] >> rfs[] >>
  fs[check_clock_def,dec_clock_def] >> simp[])

val _ = bring_to_front_overload"evaluate"{Name="evaluate",Thy="funBigStep"};

val evaluate_def = Q.store_thm("evaluate_def",`
  (evaluate ([],env,s) = (Rval [],s)) ∧
  (evaluate (e1::e2::es,env,s) =
   case evaluate ([e1],env,s) of
   | (Rval v1,s) =>
       (case evaluate (e2::es,env,s) of
        | (Rval vs,s) => (Rval (HD v1::vs),s)
        | res => res)
   | res => res) ∧
  (evaluate ([Lit l],env,s) = (Rval [Litv l],s)) ∧
  (evaluate ([Raise e],env,s) =
   case evaluate ([e],env,s) of
   | (Rval v,s) => (Rerr (Rraise (HD v)),s)
   | res => res) ∧
  (evaluate ([Handle e pes],env,s) =
   case evaluate ([e],env,s) of
   | (Rerr (Rraise v),s) => evaluate_match (pes,v,v,env,s)
   | res => res) ∧
  (evaluate ([Con cn es],env,s) =
   if do_con_check (all_env_to_cenv env) cn (LENGTH es) then
     (case evaluate (REVERSE es, env, s) of
      | (Rval vs,s) =>
        (case build_conv (all_env_to_cenv env) cn (REVERSE vs) of
         | SOME v => (Rval [v], s)
         | NONE => (Rerr (Rabort Rtype_error),s))
      | res => res)
   else (Rerr (Rabort Rtype_error),s)) ∧
  (evaluate ([Var n],env,s) =
   case lookup_var_id n env of
   | SOME v => (Rval [v], s)
   | NONE => (Rerr (Rabort Rtype_error), s)) ∧
  (evaluate ([Fun x e],env,s) = (Rval [Closure env x e],s)) ∧
  (evaluate ([App op es],env,s) =
   case evaluate (REVERSE es,env,s) of
   | (Rval vs,s) =>
     if op = Opapp then
       (case do_opapp (REVERSE vs) of
        | SOME (env',e) =>
          if s.clock ≠ 0 then
            evaluate ([e],env',dec_clock s)
          else
            (Rerr (Rabort Rtimeout_error),s)
        | NONE => (Rerr (Rabort Rtype_error), s))
     else
       (case do_app (s.refs,s.io) op (REVERSE vs) of
        | (SOME ((refs,io),r)) => (map_result (λv. [v]) I r, s with <| refs := refs; io := io |>)
        | NONE => (Rerr (Rabort Rtype_error),s))
   | res => res) ∧
  (evaluate ([Log lop e1 e2],env,s) =
   case evaluate ([e1],env,s) of
   | (Rval v1,s) =>
     (case do_log lop (HD v1) e2 of
      | SOME (Exp e) => evaluate ([e],env,s)
      | SOME (Val v) => (Rval [v], s)
      | NONE => (Rerr (Rabort Rtype_error), s))
   | res => res) ∧
  (evaluate ([If e1 e2 e3],env,s) =
   case evaluate ([e1],env,s) of
   | (Rval v,s) =>
     (case do_if (HD v) e2 e3 of
      | SOME e => evaluate ([e],env,s)
      | NONE => (Rerr (Rabort Rtype_error),s))
   | res => res) ∧
  (evaluate ([Mat e pes],env,s) =
   case evaluate ([e],env,s) of
   | (Rval v,s) =>
       evaluate_match (pes,HD v,Conv(SOME("Bind",TypeExn(Short"Bind")))[],env,s)
   | res => res) ∧
  (evaluate ([Let xo e1 e2],env,s) =
   case evaluate ([e1],env,s) of
   | (Rval v,s) => evaluate ([e2],all_env_with_env env (opt_bind xo (HD v) (all_env_to_env env)),s)
   | res => res) ∧
  (evaluate ([Letrec funs e],env,s) =
   if ALL_DISTINCT (MAP FST funs) then
     evaluate ([e],all_env_with_env env (build_rec_env funs env (all_env_to_env env)),s)
   else (Rerr (Rabort Rtype_error),s)) ∧
  (evaluate_match ([],v,err_v,env,s) = (Rerr (Rraise err_v),s)) ∧
  (evaluate_match ((p,e)::pes,v,err_v,env,s) =
   if ALL_DISTINCT (pat_bindings p []) then
     (case pmatch (all_env_to_cenv env) s.refs p v (all_env_to_env env) of
      | Match env' => evaluate ([e],all_env_with_env env env',s)
      | No_match => evaluate_match (pes,v,err_v,env,s)
      | Match_type_error => (Rerr (Rabort Rtype_error),s))
   else (Rerr (Rabort Rtype_error), s))`,
  rpt strip_tac >>
  rw[Once evaluate_def] >>
  every_case_tac >>
  imp_res_tac evaluate_clock >>
  fs[check_clock_id] >>
  `F` suffices_by rw[] >> decide_tac)

val evaluate_ind = Q.store_thm("evaluate_ind",
  `∀P0 P1.
     (∀env s. P0 ([],env,s)) ∧
     (∀x y xs env s.
        (∀v3 s1 v1.
           evaluate ([x],env,s) = (v3,s1) ∧ v3 = Rval v1 ⇒
           P0 (y::xs,env,s1)) ∧ P0 ([x],env,s) ⇒
        P0 (x::y::xs,env,s)) ∧ (∀l env s. P0 ([Lit l],env,s)) ∧
     (∀e env s. P0 ([e],env,s) ⇒ P0 ([Raise e],env,s)) ∧
     (∀e pes env s.
        (∀v3 s' v8 v.
           evaluate ([e],env,s) = (v3,s') ∧ v3 = Rerr v8 ∧
           v8 = Rraise v ⇒
           P1 (pes,v,v,env,s')) ∧ P0 ([e],env,s) ⇒
        P0 ([Handle e pes],env,s)) ∧
     (∀cn es env s.
        (do_con_check (all_env_to_cenv env) cn (LENGTH es) ⇒
         P0 (REVERSE es,env,s)) ⇒
        P0 ([Con cn es],env,s)) ∧ (∀n env s. P0 ([Var n],env,s)) ∧
     (∀n e env s. P0 ([Fun n e],env,s)) ∧
     (∀op es env s.
        (∀v2 s' vs v env' e.
           evaluate (REVERSE es,env,s) = (v2,s') ∧ v2 = Rval vs ∧
           op = Opapp ∧ do_opapp (REVERSE vs) = SOME v ∧ v = (env',e) ∧
           s'.clock ≠ 0 ⇒
           P0 ([e],env',dec_clock s')) ∧
        P0 (REVERSE es,env,s) ⇒
        P0 ([App op es],env,s)) ∧
     (∀op e1 e2 env s.
        (∀v3 s' v1' v1 e.
           evaluate ([e1],env,s) = (v3,s') ∧ v3 = Rval v1' ∧
           do_log op (HD v1') e2 = SOME v1 ∧ v1 = Exp e ⇒
           P0 ([e],env,s')) ∧ P0 ([e1],env,s) ⇒
        P0 ([Log op e1 e2],env,s)) ∧
     (∀e1 e2 e3 env s.
        (∀v3 s' v e.
           evaluate ([e1],env,s) = (v3,s') ∧ v3 = Rval v ∧
           do_if (HD v) e2 e3 = SOME e ⇒
           P0 ([e],env,s')) ∧ P0 ([e1],env,s) ⇒
        P0 ([If e1 e2 e3],env,s)) ∧
     (∀e pes env s.
        (∀v3 s' v.
           evaluate ([e],env,s) = (v3,s') ∧ v3 = Rval v ⇒
           P1
             (pes,HD v,Conv (SOME ("Bind",TypeExn (Short "Bind"))) [],
              env,s')) ∧ P0 ([e],env,s) ⇒
        P0 ([Mat e pes],env,s)) ∧
     (∀n e1 e2 env s.
        (∀v3 s' v.
           evaluate ([e1],env,s) = (v3,s') ∧ v3 = Rval v ⇒
           P0
             ([e2],
              all_env_with_env env
                (opt_bind n (HD v) (all_env_to_env env)),
              s')) ∧ P0 ([e1],env,s) ⇒
        P0 ([Let n e1 e2],env,s)) ∧
     (∀funs e env s.
        (ALL_DISTINCT (MAP FST funs) ⇒
         P0
           ([e],
            all_env_with_env env
              (build_rec_env funs env (all_env_to_env env)),s)) ⇒
        P0 ([Letrec funs e],env,s)) ∧
     (∀v err_v env s. P1 ([],v,err_v,env,s)) ∧
     (∀p e pes v err_v env s.
        (∀env'.
           ALL_DISTINCT (pat_bindings p []) ∧
           pmatch (all_env_to_cenv env) s.refs p v
             (all_env_to_env env) = Match env' ⇒
           P0 ([e],all_env_with_env env env',s)) ∧
        (ALL_DISTINCT (pat_bindings p []) ∧
         pmatch (all_env_to_cenv env) s.refs p v (all_env_to_env env) =
         No_match ⇒
         P1 (pes,v,err_v,env,s)) ⇒
        P1 ((p,e)::pes,v,err_v,env,s)) ⇒
     (∀v0. P0 v0) ∧ (∀v0. P1 v0)`,
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac evaluate_ind >>
  rw[] >> first_x_assum match_mp_tac >>
  rw[] >> fs[] >>
  res_tac >>
  imp_res_tac evaluate_clock >>
  fsrw_tac[ARITH_ss][check_clock_id]);

val _ = delete_const"evaluate_UNION_aux";

val _ = export_theory();
