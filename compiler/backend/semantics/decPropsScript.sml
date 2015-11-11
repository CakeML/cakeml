open preamble decSemTheory;

val _ = new_theory"decProps"

val state_rel_def = Define`
  state_rel R s1 s2 ⇔
    s1.clock = s2.clock ∧
    LIST_REL (sv_rel R) s1.refs s2.refs ∧
    s1.ffi = s2.ffi ∧
    LIST_REL (OPTION_REL R) s1.globals s2.globals`;

val state_rel_refl = store_thm("state_rel_refl[simp]",
  ``∀V s. (∀x. V x x) ⇒ state_rel V s s``,
  rw[state_rel_def] >>
  match_mp_tac EVERY2_refl >>
  rw[optionTheory.OPTREL_def] >>
  Cases_on`x` >> rw[]);

val state_rel_trans = store_thm("csg_rel_trans",
  ``∀V. (∀x y z. V x y ∧ V y z ⇒ V x z) ⇒ ∀x y z. state_rel V x y ∧ state_rel V y z ⇒ state_rel V x z``,
  rw[state_rel_def] >>
  match_mp_tac (MP_CANON EVERY2_trans)
  >- metis_tac[evalPropsTheory.sv_rel_trans] >>
  simp[optionTheory.OPTREL_def] >>
  srw_tac[boolSimps.DNF_ss][] >>
  metis_tac[])

val state_rel_clock = store_thm("state_rel_clock",
  ``state_rel R csg1 csg2 ⇒ csg1.clock = csg2.clock``,
  simp[state_rel_def])

val map_state_def = Define`
  map_state f s =
    <|clock := s.clock;
      ffi := s.ffi;
      refs := MAP (map_sv f) s.refs;
      globals := MAP (OPTION_MAP f) s.globals |>`;

val map_state_clock = Q.store_thm("map_state_clock[simp]",
  `(map_state f s).clock = s.clock`,
  rw[map_state_def]);

val state_every_def = Define`
  state_every P s ⇔ EVERY (sv_every P) s.refs ∧ EVERY (OPTION_EVERY P) s.globals`

val do_app_genv_weakening = prove(
  ``decSem$do_app x op vs = SOME (x',c) ⇒
    do_app (x with globals := x.globals ++ y) op vs = SOME (x' with globals := x'.globals ++ y,c)``,
  rw[do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
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
  rw [evaluate_def] >>
  every_case_tac >> fs[] >> rw[] >> rfs[] >>
  fsrw_tac[ARITH_ss][EL_APPEND1] >> rfs[] >>
  imp_res_tac do_app_genv_weakening >> fs[] >>
  fs[dec_clock_def] >>
  simp[state_component_equality,K_DEF,GSYM GENLIST_APPEND])

val evaluate_extend_genv = Q.store_thm ("evaluate_extend_genv",
  `!env s n s' v.
    evaluate env s [Extend_global n] = (s',r)
    ⇔
    r = Rval [Conv NONE []] ∧
    s' = (s with globals := s.globals ++ GENLIST (\x. NONE) n)`,
  rw [evaluate_def] >>
  metis_tac []);

val prompt_num_defs_def = Define `
  prompt_num_defs (Prompt ds) = num_defs ds`;

val _ = export_theory()
