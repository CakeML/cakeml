open preamble conSemTheory

val _ = new_theory"conProps"

val build_rec_env_help_lem = Q.prove (
  `∀funs env funs'.
    FOLDR (λ(f,x,e) env'. ((f, Recclosure env funs' f) :: env')) env' funs =
    MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs ++ env'`,
  Induct >>
  rw [] >>
  PairCases_on `h` >>
  rw []);

val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
  `∀funs funs' env env'.
    build_rec_env funs env env' =
    MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs ++ env'`,
  rw [build_rec_env_def, build_rec_env_help_lem]);

val pat_bindings_accum = Q.store_thm ("pat_bindings_accum",
  `(!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
   (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)`,
  Induct >>
  rw []
  >- rw [pat_bindings_def]
  >- rw [pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
  >- rw [pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]);

val Boolv_11 = store_thm("Boolv_11[simp]",
  ``Boolv b1 = Boolv b2 ⇔ (b1 = b2)``, EVAL_TAC >> rw[])

val evaluate_list_length = Q.store_thm ("evaluate_list_length",
  `!b env s gtagenv es s' vs.
    conSem$evaluate_list b env s es (s', Rval vs)
    ⇒
    LENGTH es = LENGTH vs`,
  induct_on `es` >>
  rw [] >>
  Cases_on`vs`>>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once conSemTheory.evaluate_cases]) >>
  rw [] >>
  metis_tac []);

val pmatch_list_Pvar = Q.store_thm("pmatch_list_Pvar",
  `∀xs exh vs s env.
     LENGTH xs = LENGTH vs ⇒
     pmatch_list exh s (MAP Pvar xs) vs env = Match (REVERSE(ZIP(xs,vs))++env)`,
  Induct >> simp[LENGTH_NIL_SYM,pmatch_def] >>
  Cases_on`vs`>>simp[pmatch_def]);

val pats_bindings_MAP_Pvar = Q.store_thm("pats_bindings_MAP_Pvar",
  `∀ws ls. pats_bindings (MAP Pvar ws) ls = (REVERSE ws) ++ ls`,
  Induct >> simp[pat_bindings_def]);

val _ = export_theory()
