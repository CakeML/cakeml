open preamble decSemTheory conPropsTheory;

val _ = new_theory"decProps"

val map_state_def = Define`
  map_state f s =
    <|clock := s.clock;
      ffi := s.ffi;
      refs := MAP (map_sv f) s.refs;
      globals := MAP (OPTION_MAP f) s.globals |>`;

val map_state_clock = Q.store_thm("map_state_clock[simp]",
  `(map_state f s).clock = s.clock`,
  srw_tac[][map_state_def]);

val state_every_def = Define`
  state_every P s ⇔ EVERY (sv_every P) s.refs ∧ EVERY (OPTION_EVERY P) s.globals`

val do_app_genv_weakening = Q.prove(
  `decSem$do_app x op vs = SOME (x',c) ⇒
    do_app (x with globals := x.globals ++ y) op vs = SOME (x' with globals := x'.globals ++ y,c)`,
  srw_tac[][do_app_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  fsrw_tac[ARITH_ss][EL_APPEND1,LUPDATE_APPEND1,state_component_equality])

val s = ``s:'ffi decSem$state``

val evaluate_genv_weakening = Q.store_thm ("evaluate_genv_weakening",
  `(∀env ^s es s' r.
     evaluate env s es = (s',r) ⇒
       r ≠ Rerr (Rabort Rtype_error)
       ⇒
       evaluate env (s with globals := s.globals++GENLIST (\x.NONE) l) es =
         (s' with globals := s'.globals++GENLIST (\x.NONE) l,r))∧
   (∀env ^s v pes err_v s' r.
     evaluate_match env s v pes err_v = (s',r) ⇒
       r ≠ Rerr (Rabort Rtype_error)
       ⇒
       evaluate_match env (s with globals := s.globals++GENLIST (\x.NONE) l) v pes err_v =
         (s' with globals := s'.globals++GENLIST (\x.NONE) l,r))`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  fsrw_tac[ARITH_ss][EL_APPEND1] >> rev_full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_genv_weakening >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[dec_clock_def] >>
  simp[state_component_equality,K_DEF,GSYM GENLIST_APPEND])

val evaluate_extend_genv = Q.store_thm ("evaluate_extend_genv",
  `!env s n s' v.
    evaluate env s [Extend_global n] = (s',r)
    ⇔
    r = Rval [Conv NONE []] ∧
    s' = (s with globals := s.globals ++ GENLIST (\x. NONE) n)`,
  srw_tac[][evaluate_def] >>
  metis_tac []);

val prompt_num_defs_def = Define `
  prompt_num_defs (Prompt ds) = num_defs ds`;

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀env (s:'ffi decSem$state) ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
   (∀env (s:'ffi decSem$state) v pes ev s' vs.
      evaluate_match env s v pes ev = (s', Rval vs) ⇒ LENGTH vs = 1)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val evaluate_cons = Q.store_thm("evaluate_cons",
  `evaluate env s (e::es) =
   (case evaluate env s [e] of
    | (s,Rval v) =>
      (case evaluate env s es of
       | (s,Rval vs) => (s,Rval (v++vs))
       | r => r)
    | r => r)`,
  Cases_on`es`>>srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[evaluate_def] >>
  imp_res_tac evaluate_length >> full_simp_tac(srw_ss())[SING_HD]);

val evaluate_sing = Q.store_thm("evaluate_sing",
  `(evaluate env s [e] = (s',Rval vs) ⇒ ∃y. vs = [y]) ∧
   (evaluate_match env s v pes ev = (s',Rval vs) ⇒ ∃y. vs = [y])`,
  srw_tac[][] >> imp_res_tac evaluate_length >> full_simp_tac(srw_ss())[] >> metis_tac[SING_HD])

val do_app_add_to_clock = Q.store_thm("do_app_add_to_clock",
  `(do_app (s with clock := s.clock + extra) op vs =
    OPTION_MAP (λ(s',r). (s' with clock := s'.clock + extra,r)) (do_app s op vs))`,
  full_simp_tac(srw_ss())[do_app_def] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[]>-( every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  reverse(Cases_on`op`>>full_simp_tac(srw_ss())[]) >- ( every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  qmatch_goalsub_rename_tac`op:ast$op` >>
  Cases_on`op`>>full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >>
  srw_tac[][]);

val evaluate_add_to_clock = Q.store_thm("evaluate_add_to_clock",
  `(∀env (s:'ffi decSem$state) es s' r.
       evaluate env s es = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate env (s with clock := s.clock + extra) es =
         (s' with clock := s'.clock + extra,r)) ∧
   (∀env (s:'ffi decSem$state) pes v err_v s' r.
       evaluate_match env s pes v err_v = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate_match env (s with clock := s.clock + extra) pes v err_v =
         (s' with clock := s'.clock + extra,r))`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[do_app_add_to_clock] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def]);

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app s op vs = SOME(s',r) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events ∧
   (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  srw_tac[][do_app_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac conPropsTheory.do_app_io_events_mono);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `(∀env (s:'ffi decSem$state) es s' r.
      evaluate env s es = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)) ∧
   (∀env (s:'ffi decSem$state) pes v err_v s' r.
      evaluate_match env s pes v err_v = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi))`,
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
  imp_res_tac do_app_io_events_mono >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]);

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC)

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `(∀env (s:'ffi decSem$state) es extra.
       (FST(evaluate env s es)).ffi.io_events ≼
       (FST(evaluate env (s with clock := s.clock + extra) es)).ffi.io_events ∧
       (IS_SOME((FST(evaluate env s es)).ffi.final_event) ⇒
        (FST(evaluate env (s with clock := s.clock + extra) es)).ffi =
        (FST(evaluate env s es)).ffi)) ∧
   (∀env (s:'ffi decSem$state) pes v err_v extra.
       (FST(evaluate_match env s pes v err_v)).ffi.io_events ≼
       (FST(evaluate_match env (s with clock := s.clock + extra) pes v err_v)).ffi.io_events ∧
       (IS_SOME((FST(evaluate_match env s pes v err_v)).ffi.final_event) ⇒
        (FST(evaluate_match env (s with clock := s.clock + extra) pes v err_v)).ffi =
        (FST(evaluate_match env s pes v err_v)).ffi))`,
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_to_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
  full_simp_tac(srw_ss())[do_app_add_to_clock,UNCURRY] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  TRY(last_x_assum(qspec_then`extra`mp_tac)>>simp[]>>NO_TAC) >>
  metis_tac[FST,IS_PREFIX_TRANS,evaluate_io_events_mono,PAIR,with_clock_ffi,do_app_io_events_mono]);


val _ = export_theory()
