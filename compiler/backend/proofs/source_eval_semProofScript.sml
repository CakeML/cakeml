(*
  Moves programs from the source semantics to evalSem. A source eval
  state corresponds to an evalSem state in EvalPending mode: a
  one-argument call to Eval initialises Eval in both semantics, and a
  two-argument call, which the source semantics resolves with its eval
  oracle, is resolved in evalSem by running the compiler (or fails when
  Eval has not been initialised). Choosing the eval oracle that answers
  as the compiler makes the two semantics agree. Without an eval state,
  a program means the same in both semantics.
*)
Theory source_eval_semProof
Ancestors
  semanticPrimitives evaluate semantics
  evalSem[qualified] evalSemProps[qualified]
Libs
  preamble

(* the evalSem eval state r corresponds to the source eval state es:
   es has not been initialised and has no history, its init_ok accepts
   exactly the initial
   compiler state of r together with closures that implement the
   compiler of r, and the compiler only produces states that contain
   neither code nor references *)
Definition eval_state_ok_def:
  eval_state_ok (r:evalSem$eval_decs_state) (es:source_eval_state) (:'ffi) ⇔
    es.decode_decs = r.decode_decs ∧
    es.env_id_counter = r.env_id_counter ∧
    ¬es.initialised ∧ es.history = [] ∧
    es.init_ok = (λst cl. st = r.compiler_state ∧
                          evalSem$compiler_closure r.compiler r.decode_decs
                            r.compiler_state cl (:'ffi)) ∧
    data_v r.compiler_state ∧
    (∀id st_v decs st bs ws.
       r.compiler (id,st_v,decs) = SOME (st,bs,ws) ⇒ data_v st)
End

Definition to_evalSem_ok_def:
  to_evalSem_ok (r:evalSem$eval_decs_state option) (s:'ffi semanticPrimitives$state) ⇔
    case (r,s.eval_state) of
    | (NONE,NONE) => T
    | (SOME r,SOME es) => eval_state_ok r es (:'ffi)
    | _ => F
End

(* source states embed into evalSem states with an EvalPending eval_state *)
Definition to_evalSem_def:
  to_evalSem (r:evalSem$eval_decs_state option) (s:'ffi semanticPrimitives$state) =
    <| clock := s.clock
     ; refs := s.refs
     ; ffi := s.ffi
     ; next_type_stamp := s.next_type_stamp
     ; next_exn_stamp := s.next_exn_stamp
     ; eval_state := OPTION_MAP evalSem$EvalPending r
     ; ptr_eq_oracle := s.ptr_eq_oracle |> : 'ffi evalSem$state
End

Theorem to_evalSem_simps[simp]:
  (to_evalSem r s).clock = s.clock ∧
  (to_evalSem r s).refs = s.refs ∧
  (to_evalSem r s).ffi = s.ffi ∧
  (to_evalSem r s).next_type_stamp = s.next_type_stamp ∧
  (to_evalSem r s).next_exn_stamp = s.next_exn_stamp ∧
  (to_evalSem r s).eval_state = OPTION_MAP evalSem$EvalPending r ∧
  (to_evalSem r s).ptr_eq_oracle = s.ptr_eq_oracle
Proof
  simp [to_evalSem_def]
QED

Theorem to_evalSem_updates[simp]:
  (to_evalSem r s with clock := k) = to_evalSem r (s with clock := k) ∧
  (to_evalSem r s with refs := rs) = to_evalSem r (s with refs := rs) ∧
  (to_evalSem r s with <| refs := rs; ffi := f |>) =
    to_evalSem r (s with <| refs := rs; ffi := f |>) ∧
  (to_evalSem r s with ptr_eq_oracle := po) =
    to_evalSem r (s with ptr_eq_oracle := po) ∧
  (to_evalSem r s with next_type_stamp := n) =
    to_evalSem r (s with next_type_stamp := n) ∧
  (to_evalSem r s with next_exn_stamp := n) =
    to_evalSem r (s with next_exn_stamp := n) ∧
  evalSem$dec_clock (to_evalSem r s) = to_evalSem r (evaluate$dec_clock s)
Proof
  simp [to_evalSem_def, evalSemTheory.state_component_equality,
        evalSemTheory.dec_clock_def, evaluateTheory.dec_clock_def]
QED

Theorem to_evalSem_ok_ptr_eq_oracle[simp]:
  to_evalSem_ok r (s with ptr_eq_oracle := po) = to_evalSem_ok r s ∧
  to_evalSem_ok r (s with eval_oracle := eo) = to_evalSem_ok r s
Proof
  simp [to_evalSem_ok_def]
QED

(* ------------------------------------------------------------------ *
   Programs without an eval state
 * ------------------------------------------------------------------ *)

Theorem do_eval_NONE[local,simp]:
  semanticPrimitives$do_eval_init vs NONE = NONE ∧
  semanticPrimitives$do_eval vs NONE = NONE ∧
  evalSem$do_eval_init vs NONE (:'ffi) = NONE ∧
  evalSem$do_eval_fail vs NONE = NONE ∧
  evalSem$do_eval vs NONE = NONE
Proof
  simp [do_eval_init_def, do_eval_def, evalSemTheory.do_eval_init_def,
        evalSemTheory.do_eval_fail_def, evalSemTheory.do_eval_def]
  \\ every_case_tac
QED

Theorem evaluate_to_evalSem_NONE:
  (∀(s:'ffi semanticPrimitives$state) env es s' r.
     evaluate$evaluate s env es = (s',r) ∧ s.eval_state = NONE ⇒
     s'.eval_state = NONE ∧
     evalSem$evaluate (to_evalSem NONE s) env es = (to_evalSem NONE s',r)) ∧
  (∀(s:'ffi semanticPrimitives$state) env v pes err_v s' r.
     evaluate$evaluate_match s env v pes err_v = (s',r) ∧ s.eval_state = NONE ⇒
     s'.eval_state = NONE ∧
     evalSem$evaluate_match (to_evalSem NONE s) env v pes err_v =
       (to_evalSem NONE s',r)) ∧
  (∀(s:'ffi semanticPrimitives$state) env ds s' r.
     evaluate$evaluate_decs s env ds = (s',r) ∧ s.eval_state = NONE ⇒
     s'.eval_state = NONE ∧
     evalSem$evaluate_decs (to_evalSem NONE s) env ds = (to_evalSem NONE s',r))
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rw [full_evaluate_def, evalSemTheory.full_evaluate_def]
  >>~- ([‘op = Opapp’],
    qpat_x_assum ‘∀s' r. evaluate s env (REVERSE es) = _ ∧ _ ⇒ _’ mp_tac
    \\ Cases_on ‘evaluate s env (REVERSE es)’
    \\ simp [] \\ strip_tac
    \\ reverse (Cases_on ‘r'’) >- gvs []
    \\ gvs []
    \\ Cases_on ‘op = Opapp’ >- gvs [AllCaseEqs(), dec_clock_def]
    \\ Cases_on ‘op = ThunkOp ForceThunk’ >- gvs [AllCaseEqs(), dec_clock_def]
    \\ Cases_on ‘op = Eval’
    >- gvs [AllCaseEqs(), do_eval_res_def, evalSemTheory.do_eval_res_def]
    \\ gvs [AllCaseEqs()])
  \\ gvs [AllCaseEqs(), do_eval_res_def, evalSemTheory.do_eval_res_def,
          declare_env_def, evalSemTheory.declare_env_def]
QED

Theorem semantics_determ_to_evalSem_NONE:
  s.eval_state = NONE ⇒
  evalSem$semantics_determ (to_evalSem NONE s) env prog =
  semantics$semantics_determ s env prog
Proof
  strip_tac
  \\ ‘∀k. evalSem$evaluate_prog_with_clock (to_evalSem NONE s) env k prog =
          semantics$evaluate_prog_with_clock s env k prog’
    by (rw [evalSemTheory.evaluate_prog_with_clock_def,
            semanticsTheory.evaluate_prog_with_clock_def]
        \\ Cases_on ‘evaluate_decs (s with clock := k) env prog’
        \\ drule (CONJUNCTS evaluate_to_evalSem_NONE |> last)
        \\ simp [])
  \\ rw [FUN_EQ_THM]
  \\ Cases_on ‘x’
  \\ simp [evalSemTheory.semantics_determ_def, semanticsTheory.semantics_determ_def]
QED

(* ------------------------------------------------------------------ *
   Programs with an eval state
 * ------------------------------------------------------------------ *)

(* the compiler state of r after the successful calls of a history *)
Definition hist_state_def:
  hist_state (r:evalSem$eval_decs_state) st [] = SOME st ∧
  hist_state r st (((id,decs_v):(num # num) # v)::h) =
    case r.decode_decs decs_v of
    | NONE => NONE
    | SOME decs =>
      case r.compiler (id,st,decs) of
      | NONE => NONE
      | SOME (st1,_,_) => hist_state r st1 h
End

(* the eval oracle that answers as the compiler of r; a failing call
   consumes the pointer equality oracle entries that the compiler closure
   consumes when it runs on the call *)
Definition compiler_oracle_def:
  compiler_oracle (r:evalSem$eval_decs_state) (:'ffi) (init,h,(id,decs_v)) =
    ((init ∧
      ∃st decs st1 bs ws.
        hist_state r r.compiler_state h = SOME st ∧
        r.decode_decs decs_v = SOME decs ∧
        r.compiler (id,st,decs) = SOME (st1,bs,ws)),
     λcl refs po.
       case (init,hist_state r r.compiler_state h) of
       | (T,SOME st) =>
           (@k. skip_ptr_eq k po =
                evalSem$closure_ptr_eq cl
                  (Conv NONE [Conv NONE [nat_to_v (FST id); nat_to_v (SND id)];
                              st; decs_v]) refs po (:'ffi))
       | _ => 0)
End

(* the evalSem eval state of a source eval state *)
Definition to_es_def:
  to_es (r:evalSem$eval_decs_state) (es:source_eval_state) =
    if es.initialised then
      evalSem$EvalRun
        (r with <| compiler_state :=
                     THE (hist_state r r.compiler_state es.history);
                   env_id_counter := es.env_id_counter;
                   closure := es.closure |>)
    else evalSem$EvalPending (r with env_id_counter := es.env_id_counter)
End

Definition sim_es_def:
  sim_es (r:evalSem$eval_decs_state option) es =
    case r of NONE => NONE | SOME r => OPTION_MAP (to_es r) es
End

Theorem sim_es_NONE[simp]:
  sim_es r NONE = NONE
Proof
  Cases_on ‘r’ \\ simp [sim_es_def]
QED

Definition sim_state_def:
  sim_state (r:evalSem$eval_decs_state option) (s:'ffi semanticPrimitives$state) =
    <| clock := s.clock
     ; refs := s.refs
     ; ffi := s.ffi
     ; next_type_stamp := s.next_type_stamp
     ; next_exn_stamp := s.next_exn_stamp
     ; eval_state := sim_es r s.eval_state
     ; ptr_eq_oracle := s.ptr_eq_oracle |> : 'ffi evalSem$state
End

Theorem sim_state_simps[simp]:
  (sim_state r s).clock = s.clock ∧
  (sim_state r s).refs = s.refs ∧
  (sim_state r s).ffi = s.ffi ∧
  (sim_state r s).next_type_stamp = s.next_type_stamp ∧
  (sim_state r s).next_exn_stamp = s.next_exn_stamp ∧
  (sim_state r s).eval_state = sim_es r s.eval_state ∧
  (sim_state r s).ptr_eq_oracle = s.ptr_eq_oracle
Proof
  simp [sim_state_def]
QED

Theorem sim_state_updates[simp]:
  (sim_state r s with clock := k) = sim_state r (s with clock := k) ∧
  (sim_state r s with refs := rs) = sim_state r (s with refs := rs) ∧
  (sim_state r s with <| refs := rs; ffi := f |>) =
    sim_state r (s with <| refs := rs; ffi := f |>) ∧
  (sim_state r s with ptr_eq_oracle := po) =
    sim_state r (s with ptr_eq_oracle := po) ∧
  (sim_state r s with next_type_stamp := n) =
    sim_state r (s with next_type_stamp := n) ∧
  (sim_state r s with next_exn_stamp := n) =
    sim_state r (s with next_exn_stamp := n) ∧
  (sim_state r s with eval_state := sim_es r es) =
    sim_state r (s with eval_state := es) ∧
  evalSem$dec_clock (sim_state r s) = sim_state r (evaluate$dec_clock s)
Proof
  simp [sim_state_def, evalSemTheory.state_component_equality,
        evalSemTheory.dec_clock_def, evaluateTheory.dec_clock_def]
QED

(* the invariant of the simulation: the eval oracle is the compiler
   oracle, and the history is empty until Eval is initialised and always
   leads to a compiler state *)
Definition sim_ok_def:
  sim_ok (r:evalSem$eval_decs_state option) (s:'ffi semanticPrimitives$state) ⇔
    case (r,s.eval_state) of
    | (NONE,NONE) => T
    | (SOME r,SOME es) =>
        es.decode_decs = r.decode_decs ∧
        es.init_ok = (λst cl. st = r.compiler_state ∧
                              evalSem$compiler_closure r.compiler r.decode_decs
                                r.compiler_state cl (:'ffi)) ∧
        data_v r.compiler_state ∧
        (∀id st_v decs st bs ws.
           r.compiler (id,st_v,decs) = SOME (st,bs,ws) ⇒ data_v st) ∧
        s.eval_oracle = compiler_oracle r (:'ffi) ∧
        (¬es.initialised ⇒ es.history = []) ∧
        (es.initialised ⇒
         evalSem$compiler_closure r.compiler r.decode_decs r.compiler_state
           es.closure (:'ffi)) ∧
        (∃st. hist_state r r.compiler_state es.history = SOME st)
    | _ => F
End

(* initialisation is never undone *)
Definition init_mono_def:
  init_mono (s:'ffi semanticPrimitives$state) (s':'ffi semanticPrimitives$state) ⇔
    ∀es. s.eval_state = SOME es ∧ es.initialised ⇒
         ∃es'. s'.eval_state = SOME es' ∧ es'.initialised
End

Theorem sim_ok_updates[simp]:
  sim_ok r ((s:'ffi semanticPrimitives$state) with clock := k) = sim_ok r s ∧
  sim_ok r (s with refs := rs) = sim_ok r s ∧
  sim_ok r (s with ffi := (f:'ffi ffi_state)) = sim_ok r s ∧
  sim_ok r (s with <| refs := rs; ffi := (f:'ffi ffi_state) |>) = sim_ok r s ∧
  sim_ok r (s with ptr_eq_oracle := po) = sim_ok r s ∧
  sim_ok r (s with next_type_stamp := n) = sim_ok r s ∧
  sim_ok r (s with next_exn_stamp := n) = sim_ok r s ∧
  sim_ok r (evaluate$dec_clock s) = sim_ok r s
Proof
  simp [sim_ok_def, evaluateTheory.dec_clock_def]
QED

Theorem hist_state_snoc:
  ∀h st.
    hist_state r st (h ++ [(id,decs_v)]) =
    case hist_state r st h of
    | NONE => NONE
    | SOME st1 =>
      case r.decode_decs decs_v of
      | NONE => NONE
      | SOME decs =>
        case r.compiler (id,st1,decs) of
        | NONE => NONE
        | SOME (st2,_,_) => SOME st2
Proof
  Induct \\ simp [hist_state_def]
  \\ PairCases \\ rw [hist_state_def]
  \\ every_case_tac \\ gvs []
QED

Theorem hist_state_data_v:
  ∀h st st1.
    (∀id st_v decs st bs ws.
       r.compiler (id,st_v,decs) = SOME (st,bs,ws) ⇒ data_v st) ∧
    data_v st ∧ hist_state r st h = SOME st1 ⇒ data_v st1
Proof
  Induct \\ simp [hist_state_def]
  \\ PairCases \\ rw [hist_state_def]
  \\ gvs [AllCaseEqs()]
  \\ PairCases_on ‘v2’ \\ metis_tac []
QED

Theorem hist_state_reach:
  ∀h st st1.
    hist_state r st h = SOME st1 ⇒ evalSem$compiler_reach r.compiler st st1
Proof
  Induct \\ simp [hist_state_def, evalSemTheory.compiler_reach_refl]
  \\ PairCases \\ rw [hist_state_def]
  \\ gvs [AllCaseEqs()] \\ PairCases_on ‘v2’
  \\ first_x_assum drule \\ strip_tac
  \\ irule evalSemPropsTheory.compiler_reach_trans
  \\ first_x_assum $ irule_at Any
  \\ irule evalSemTheory.compiler_reach_step
  \\ metis_tac [evalSemTheory.compiler_reach_refl]
QED

(* the eval states before and after a one-argument call to Eval *)
Theorem do_eval_init_sim:
  sim_ok r (s:'ffi semanticPrimitives$state) ⇒
  evalSem$do_eval_init vs (sim_es r s.eval_state) (:'ffi) =
    sim_es r (do_eval_init vs s.eval_state) ∧
  ∀es. do_eval_init vs s.eval_state = SOME es ⇒
       sim_ok r (s with eval_state := SOME es)
Proof
  rw [sim_ok_def]
  \\ Cases_on ‘r’ \\ Cases_on ‘s.eval_state’
  \\ gvs [sim_es_def, do_eval_init_def, evalSemTheory.do_eval_init_def]
  \\ every_case_tac
  \\ gvs [to_es_def, hist_state_def, evalSemTheory.eval_decs_state_component_equality]
  \\ every_case_tac \\ gvs []
QED

(* a two-argument call to Eval *)
Theorem do_eval_res_sim:
  sim_ok r (s:'ffi semanticPrimitives$state) ∧ do_eval_res vs s = (s1,res) ∧
  res ≠ Rerr (Rabort Rtype_error) ⇒
  (∀v. res = Rval (INL v) ⇒
       s1 = s with ptr_eq_oracle :=
              evalSem$eval_fail_ptr_eq vs (sim_es r s.eval_state) s.refs
                s.ptr_eq_oracle (:'ffi) ∧
       evalSem$do_eval_fail vs (sim_es r s.eval_state) = SOME v) ∧
  (∀env1 decs. res = Rval (INR (env1,decs)) ⇒
     evalSem$do_eval_fail vs (sim_es r s.eval_state) = NONE ∧
     evalSem$do_eval_res vs (sim_state r s) =
       (sim_state r s1,Rval (env1,decs)) ∧
     sim_ok r s1 ∧
     (∃es1. s1.eval_state = SOME es1 ∧ es1.initialised) ∧
     (∃pe. s.eval_state = SOME pe ∧ pe.initialised) ∧
     ∀x. evalSem$eval_result (sim_es r s.eval_state) x =
         Conv NONE [x; Litv (StrLit «»)]) ∧
  (∀e. res ≠ Rerr e)
Proof
  strip_tac
  \\ Cases_on ‘r’ \\ Cases_on ‘s.eval_state’
  \\ gvs [sim_ok_def, sim_es_def, do_eval_res_def, do_eval_def, AllCaseEqs()]
  \\ gvs [compiler_oracle_def]
  \\ ‘data_v st’ by metis_tac [hist_state_data_v]
  \\ Cases_on ‘x'.initialised’ \\ gvs [to_es_def]
  \\ gvs [evalSemTheory.do_eval_fail_def, evalSemTheory.do_eval_run_def,
          evalSemTheory.do_eval_res_def, evalSemTheory.do_eval_def,
          hist_state_snoc, evalSemTheory.add_decs_generation_def,
          sim_state_def, sim_es_def, to_es_def,
          evalSemTheory.state_component_equality]
  >- (‘data_v st1’ by metis_tac []
      \\ gvs [evalSemTheory.eval_result_def] \\ metis_tac [])
  \\ gvs [evalSemTheory.eval_fail_ptr_eq_def, evalSemPropsTheory.skip_ptr_eq_0]
  \\ PairCases_on ‘id’
  \\ Cases_on ‘x.compiler ((id0,id1),st,decs)’ \\ gvs []
  >- (
    ‘∃k. closure_ptr_eq x'.closure
           (Conv NONE [Conv NONE [nat_to_v id0; nat_to_v id1]; st; decs_v])
           s.refs s.ptr_eq_oracle (:'ffi) = skip_ptr_eq k s.ptr_eq_oracle’
      by (irule evalSemPropsTheory.compiler_closure_ptr_eq
        \\ metis_tac [hist_state_reach])
    \\ SELECT_ELIM_TAC
    \\ conj_tac >- metis_tac []
    \\ rw [])
  \\ rename1 ‘_ = SOME y’ \\ PairCases_on ‘y’ \\ gvs []
QED

Theorem declare_env_sim:
  sim_ok r (s:'ffi semanticPrimitives$state) ⇒
  evalSem$declare_env (sim_es r s.eval_state) env =
    OPTION_MAP (λ(x,es). (x,sim_es r es)) (declare_env s.eval_state env) ∧
  ∀x es. declare_env s.eval_state env = SOME (x,es) ⇒
         sim_ok r (s with eval_state := es) ∧
         ∀es0. s.eval_state = SOME es0 ∧ es0.initialised ⇒
               ∃es1. es = SOME es1 ∧ es1.initialised
Proof
  strip_tac
  \\ Cases_on ‘r’ \\ Cases_on ‘s.eval_state’
  \\ gvs [sim_ok_def, sim_es_def, declare_env_def, evalSemTheory.declare_env_def]
  \\ rename1 ‘s.eval_state = SOME es0’
  \\ Cases_on ‘es0.env_id_counter’ \\ rename1 ‘_ = (g,rest)’
  \\ PairCases_on ‘rest’
  \\ Cases_on ‘es0.initialised’
  \\ gvs [to_es_def, declare_env_def, evalSemTheory.declare_env_def]
  \\ rw [] \\ gvs [] \\ metis_tac []
QED

Theorem reset_env_generation_sim:
  sim_ok r (s:'ffi semanticPrimitives$state) ∧ p = SOME pe ∧ pe.initialised ∧
  s.eval_state = SOME es ∧ es.initialised ⇒
  evalSem$reset_env_generation (sim_es r p) (sim_es r s.eval_state) =
    sim_es r (reset_env_generation p s.eval_state) ∧
  sim_ok r (s with eval_state := reset_env_generation p s.eval_state) ∧
  ∃es1. reset_env_generation p s.eval_state = SOME es1 ∧ es1.initialised
Proof
  strip_tac
  \\ Cases_on ‘r’ \\ gvs [sim_ok_def, sim_es_def]
  \\ Cases_on ‘pe.env_id_counter’ \\ rename1 ‘pe.env_id_counter = (g1,r1)’
  \\ PairCases_on ‘r1’
  \\ Cases_on ‘es.env_id_counter’ \\ rename1 ‘es.env_id_counter = (g2,r2)’
  \\ PairCases_on ‘r2’
  \\ gvs [to_es_def, reset_env_generation_def,
          evalSemTheory.reset_env_generation_def]
  \\ metis_tac []
QED

Theorem evaluate_sim:
  (∀(s:'ffi semanticPrimitives$state) env es s' res.
     evaluate$evaluate s env es = (s',res) ∧ res ≠ Rerr (Rabort Rtype_error) ∧
     sim_ok r s ⇒
     sim_ok r s' ∧ init_mono s s' ∧
     evalSem$evaluate (sim_state r s) env es = (sim_state r s',res)) ∧
  (∀(s:'ffi semanticPrimitives$state) env v pes err_v s' res.
     evaluate$evaluate_match s env v pes err_v = (s',res) ∧
     res ≠ Rerr (Rabort Rtype_error) ∧ sim_ok r s ⇒
     sim_ok r s' ∧ init_mono s s' ∧
     evalSem$evaluate_match (sim_state r s) env v pes err_v =
       (sim_state r s',res)) ∧
  (∀(s:'ffi semanticPrimitives$state) env ds s' res.
     evaluate$evaluate_decs s env ds = (s',res) ∧
     res ≠ Rerr (Rabort Rtype_error) ∧ sim_ok r s ⇒
     sim_ok r s' ∧ init_mono s s' ∧
     evalSem$evaluate_decs (sim_state r s) env ds = (sim_state r s',res))
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rw [full_evaluate_def, evalSemTheory.full_evaluate_def]
  >~ [‘op = Opapp’] >- (
    qpat_x_assum ‘∀s' res. evaluate s env (REVERSE es) = _ ∧ _ ⇒ _’ mp_tac
    \\ Cases_on ‘evaluate s env (REVERSE es)’
    \\ rename1 ‘evaluate s env (REVERSE es) = (st1,r1)’
    \\ ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
    \\ simp [] \\ strip_tac
    \\ reverse (Cases_on ‘r1’) >- gvs []
    \\ gvs []
    \\ Cases_on ‘op = Opapp’ >- gvs [AllCaseEqs(), evaluateTheory.dec_clock_def]
    \\ Cases_on ‘op = ThunkOp ForceThunk’
    >- gvs [AllCaseEqs(), evaluateTheory.dec_clock_def]
    \\ Cases_on ‘op = Eval’
    >- (
      gvs []
      \\ drule_then (qspec_then ‘REVERSE a’ strip_assume_tac) do_eval_init_sim
      \\ reverse (Cases_on ‘do_eval_init (REVERSE a) st1.eval_state’) \\ gvs []
      \\ Cases_on ‘do_eval_res (REVERSE a) st1’
      \\ rename1 ‘do_eval_res _ _ = (st2,r2)’
      \\ ‘r2 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
      \\ drule_all do_eval_res_sim \\ strip_tac
      \\ Cases_on ‘r2’ \\ gvs []
      \\ rename1 ‘do_eval_res _ _ = (st2,Rval y)’
      \\ reverse (Cases_on ‘y’) \\ gvs []
      \\ rename1 ‘INR p’ \\ PairCases_on ‘p’ \\ gvs []
      \\ Cases_on ‘st2.clock = 0’ \\ gvs []
      \\ Cases_on ‘evaluate_decs (dec_clock st2) p0 p1’
      \\ rename1 ‘evaluate_decs _ _ _ = (st3,r3)’
      \\ ‘r3 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
      \\ qpat_x_assum ‘∀s'' res. (st3,r3) = _ ∧ _ ⇒ _’
           (qspecl_then [‘st3’,‘r3’] mp_tac)
      \\ simp [] \\ strip_tac
      \\ ‘∃es3. st3.eval_state = SOME es3 ∧ es3.initialised’
        by gvs [init_mono_def, evaluateTheory.dec_clock_def]
      \\ Cases_on ‘r3’ \\ gvs []
      >- (
        rename1 ‘(st3,Rval e3)’
        \\ drule declare_env_sim
        \\ disch_then (qspec_then ‘e3 +++ p0’ strip_assume_tac)
        \\ Cases_on ‘declare_env st3.eval_state (e3 +++ p0)’ \\ gvs []
        \\ rename1 ‘declare_env _ _ = SOME xx’ \\ PairCases_on ‘xx’ \\ gvs []
        \\ qpat_x_assum ‘sim_ok r (st3 with eval_state := _)’ assume_tac
        \\ drule reset_env_generation_sim \\ simp []
        \\ disch_then (qspec_then ‘pe’ mp_tac) \\ simp [] \\ strip_tac)
      \\ Cases_on ‘e’ \\ gvs []
      \\ qpat_x_assum ‘sim_ok r st3’ assume_tac
      \\ drule reset_env_generation_sim \\ simp []
      \\ disch_then (qspec_then ‘pe’ mp_tac) \\ simp [] \\ strip_tac
      \\ gvs [sim_state_def, evalSemTheory.state_component_equality])
    \\ gvs [AllCaseEqs()])
  >~ [‘op = Opapp’] >- (
    qpat_x_assum ‘∀s' res. evaluate s env (REVERSE es) = _ ∧ _ ⇒ _’ mp_tac
    \\ Cases_on ‘evaluate s env (REVERSE es)’
    \\ rename1 ‘evaluate s env (REVERSE es) = (st1,r1)’
    \\ ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
    \\ simp [] \\ strip_tac
    \\ reverse (Cases_on ‘r1’) >- gvs []
    \\ gvs []
    \\ Cases_on ‘op = Opapp’
    >- (gvs [AllCaseEqs(), evaluateTheory.dec_clock_def, init_mono_def]
        \\ metis_tac [])
    \\ Cases_on ‘op = ThunkOp ForceThunk’
    >- (gvs [AllCaseEqs(), evaluateTheory.dec_clock_def, init_mono_def]
        \\ metis_tac [])
    \\ Cases_on ‘op = Eval’
    >- (
      gvs []
      \\ drule_then (qspec_then ‘REVERSE a’ strip_assume_tac) do_eval_init_sim
      \\ reverse (Cases_on ‘do_eval_init (REVERSE a) st1.eval_state’) \\ gvs []
      >- gvs [init_mono_def, do_eval_init_def, AllCaseEqs()]
      \\ Cases_on ‘do_eval_res (REVERSE a) st1’
      \\ rename1 ‘do_eval_res _ _ = (st2,r2)’
      \\ ‘r2 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
      \\ drule_all do_eval_res_sim \\ strip_tac
      \\ Cases_on ‘r2’ \\ gvs []
      \\ rename1 ‘do_eval_res _ _ = (st2,Rval y)’
      \\ reverse (Cases_on ‘y’) \\ gvs [init_mono_def]
      \\ rename1 ‘INR p’ \\ PairCases_on ‘p’ \\ gvs []
      \\ Cases_on ‘st2.clock = 0’ \\ gvs [init_mono_def]
      \\ Cases_on ‘evaluate_decs (dec_clock st2) p0 p1’
      \\ rename1 ‘evaluate_decs _ _ _ = (st3,r3)’
      \\ ‘r3 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
      \\ qpat_x_assum ‘∀s'' res. (st3,r3) = _ ∧ _ ⇒ _’
           (qspecl_then [‘st3’,‘r3’] mp_tac)
      \\ simp [] \\ strip_tac
      \\ ‘∃es3. st3.eval_state = SOME es3 ∧ es3.initialised’
        by gvs [init_mono_def, evaluateTheory.dec_clock_def]
      \\ Cases_on ‘r3’ \\ gvs []
      >- (
        rename1 ‘(st3,Rval e3)’
        \\ drule declare_env_sim
        \\ disch_then (qspec_then ‘e3 +++ p0’ strip_assume_tac)
        \\ Cases_on ‘declare_env st3.eval_state (e3 +++ p0)’ \\ gvs []
        \\ rename1 ‘declare_env _ _ = SOME xx’ \\ PairCases_on ‘xx’ \\ gvs []
        \\ qpat_x_assum ‘sim_ok r (st3 with eval_state := _)’ assume_tac
        \\ drule reset_env_generation_sim \\ simp []
        \\ disch_then (qspec_then ‘pe’ mp_tac) \\ simp [] \\ strip_tac
        \\ gvs [init_mono_def])
      \\ Cases_on ‘e’ \\ gvs []
      \\ qpat_x_assum ‘sim_ok r st3’ assume_tac
      \\ drule reset_env_generation_sim \\ simp []
      \\ disch_then (qspec_then ‘pe’ mp_tac) \\ simp [] \\ strip_tac
      \\ gvs [init_mono_def])
    \\ gvs [AllCaseEqs(), init_mono_def])
  >~ [‘op = Opapp’] >- (
    qpat_x_assum ‘∀s' res. evaluate s env (REVERSE es) = _ ∧ _ ⇒ _’ mp_tac
    \\ Cases_on ‘evaluate s env (REVERSE es)’
    \\ rename1 ‘evaluate s env (REVERSE es) = (st1,r1)’
    \\ ‘r1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
    \\ simp [] \\ strip_tac
    \\ reverse (Cases_on ‘r1’) >- gvs []
    \\ gvs []
    \\ Cases_on ‘op = Opapp’ >- gvs [AllCaseEqs(), evaluateTheory.dec_clock_def]
    \\ Cases_on ‘op = ThunkOp ForceThunk’
    >- gvs [AllCaseEqs(), evaluateTheory.dec_clock_def]
    \\ Cases_on ‘op = Eval’
    >- (
      gvs []
      \\ drule_then (qspec_then ‘REVERSE a’ strip_assume_tac) do_eval_init_sim
      \\ reverse (Cases_on ‘do_eval_init (REVERSE a) st1.eval_state’) \\ gvs []
      >- (
          Cases_on ‘r’
          \\ gvs [sim_ok_def, sim_es_def, sim_state_def,
                  evalSemTheory.state_component_equality])
      \\ Cases_on ‘do_eval_res (REVERSE a) st1’
      \\ rename1 ‘do_eval_res _ _ = (st2,r2)’
      \\ ‘r2 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
      \\ drule_all do_eval_res_sim \\ strip_tac
      \\ Cases_on ‘r2’ \\ gvs []
      \\ rename1 ‘do_eval_res _ _ = (st2,Rval y)’
      \\ reverse (Cases_on ‘y’) \\ gvs []
      \\ rename1 ‘INR p’ \\ PairCases_on ‘p’ \\ gvs []
      \\ Cases_on ‘st2.clock = 0’ \\ gvs []
      \\ Cases_on ‘evaluate_decs (dec_clock st2) p0 p1’
      \\ rename1 ‘evaluate_decs _ _ _ = (st3,r3)’
      \\ ‘r3 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
      \\ qpat_x_assum ‘∀s'' res. (st3,r3) = _ ∧ _ ⇒ _’
           (qspecl_then [‘st3’,‘r3’] mp_tac)
      \\ simp [] \\ strip_tac
      \\ ‘∃es3. st3.eval_state = SOME es3 ∧ es3.initialised’
        by gvs [init_mono_def, evaluateTheory.dec_clock_def]
      \\ Cases_on ‘r3’ \\ gvs []
      >- (
        rename1 ‘(st3,Rval e3)’
        \\ drule declare_env_sim
        \\ disch_then (qspec_then ‘e3 +++ p0’ strip_assume_tac)
        \\ Cases_on ‘declare_env st3.eval_state (e3 +++ p0)’ \\ gvs []
        \\ rename1 ‘declare_env _ _ = SOME xx’ \\ PairCases_on ‘xx’ \\ gvs []
        \\ qpat_x_assum ‘sim_ok r (st3 with eval_state := _)’ assume_tac
        \\ drule reset_env_generation_sim \\ simp []
        \\ disch_then (qspec_then ‘pe’ mp_tac) \\ simp [] \\ strip_tac)
      \\ Cases_on ‘e’ \\ gvs []
      \\ qpat_x_assum ‘sim_ok r st3’ assume_tac
      \\ drule reset_env_generation_sim \\ simp []
      \\ disch_then (qspec_then ‘pe’ mp_tac) \\ simp [] \\ strip_tac
      \\ gvs [sim_state_def, evalSemTheory.state_component_equality])
    \\ gvs [AllCaseEqs()])
  \\ gvs [AllCaseEqs(), init_mono_def]
  >>~- ([‘combine_dec_result _ _ ≠ _’],
    ‘r' ≠ Rerr (Rabort Rtype_error)’
      by (strip_tac \\ gvs [combine_dec_result_def])
    \\ gvs [])
  \\ drule declare_env_sim \\ disch_then (qspec_then ‘env’ strip_assume_tac)
  \\ gvs []
QED

Theorem to_evalSem_sim:
  to_evalSem_ok r (s:'ffi semanticPrimitives$state) ⇒
  to_evalSem r s = sim_state r s ∧
  sim_ok r (s with eval_oracle := case r of NONE => K (F,K (K (K 0)))
                                          | SOME r => compiler_oracle r (:'ffi))
Proof
  Cases_on ‘r’ \\ Cases_on ‘s.eval_state’
  \\ rw [to_evalSem_ok_def, eval_state_ok_def, to_evalSem_def, sim_state_def,
         sim_es_def, to_es_def, sim_ok_def, hist_state_def]
  \\ gvs [evalSemTheory.eval_decs_state_component_equality]
  \\ metis_tac []
QED

(* every evalSem behaviour of a program, under any oracle, is a source
   behaviour of it under the same pointer equality oracle and the eval
   oracle that answers as the compiler. Unless the source program can
   fail, evalSem computes the same results. *)
Theorem to_evalSem_semantics:
  to_evalSem_ok r (s:'ffi semanticPrimitives$state) ∧ ¬semantics$semantics_prog s env prog Fail ⇒
  evalSem$semantics (to_evalSem r s) env prog ⊆
  semantics$semantics_prog s env prog
Proof
  rw [SUBSET_DEF, IN_DEF, evalSemTheory.semantics_def,
      semanticsTheory.semantics_prog_def]
  \\ qabbrev_tac ‘eo = case r of NONE => K (F,K (K (K 0)))
                               | SOME r0 => compiler_oracle r0 (:'ffi)’
  \\ qexistsl_tac [‘po’,‘eo’]
  \\ qabbrev_tac ‘s1 = s with <| ptr_eq_oracle := po; eval_oracle := eo |>’
  \\ ‘to_evalSem_ok r s1’ by simp [Abbr ‘s1’]
  \\ ‘to_evalSem r (s with ptr_eq_oracle := po) = to_evalSem r s1’
    by simp [Abbr ‘s1’, to_evalSem_def]
  \\ ‘s1 with eval_oracle := eo = s1’
    by simp [Abbr ‘s1’, semanticPrimitivesTheory.state_component_equality]
  \\ drule to_evalSem_sim \\ strip_tac
  \\ gvs []
  \\ ‘¬semantics_determ s1 env prog Fail’ by metis_tac []
  \\ ‘∀k. evalSem$evaluate_prog_with_clock (sim_state r s1) env k prog =
          semantics$evaluate_prog_with_clock s1 env k prog’
    by (rw [evalSemTheory.evaluate_prog_with_clock_def,
            semanticsTheory.evaluate_prog_with_clock_def]
        \\ Cases_on ‘evaluate_decs (s1 with clock := k) env prog’
        \\ rename1 ‘_ = (s2,r2)’
        \\ ‘r2 ≠ Rerr (Rabort Rtype_error)’
          by (strip_tac \\ gvs [semanticsTheory.semantics_determ_def,
                                semanticsTheory.evaluate_prog_with_clock_def]
              \\ first_x_assum (qspec_then ‘k’ mp_tac) \\ simp [])
        \\ drule (CONJUNCTS evaluate_sim |> last)
        \\ disch_then (qspec_then ‘r’ mp_tac) \\ simp [])
  \\ qpat_x_assum ‘evalSem$semantics_determ (sim_state r s1) _ _ _’ mp_tac
  \\ Cases_on ‘x’
  \\ simp [evalSemTheory.semantics_determ_def,
           semanticsTheory.semantics_determ_def]
  \\ fs [semanticsTheory.semantics_determ_def]
QED
