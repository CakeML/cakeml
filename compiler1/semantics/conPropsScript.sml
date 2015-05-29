open preamble conSemTheory

val _ = new_theory"conProps"

val do_app_cases = Q.store_thm("do_app_cases",
  `conSem$do_app s op vs = SOME x ⇒
    (∃z n1 n2. op = (Op (Opn z)) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃z n1 n2. op = (Op (Opb z)) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃v1 v2. op = (Op Equality) ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = (Op Opassign) ∧ vs = [Loc lnum; v]) ∨
    (∃n. op = (Op Opderef) ∧ vs = [Loc n]) ∨
    (∃v. op = (Op Opref) ∧ vs = [v]) ∨
    (∃n w. op = (Op Aw8alloc) ∧ vs = [Litv (IntLit n); Litv (Word8 w)]) ∨
    (∃lnum i. op = (Op Aw8sub) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op Aw8length) ∧ vs = [Loc n]) ∨
    (∃lnum i w. op = (Op Aw8update) ∧ vs = [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) ∨
    (∃c. op = (Op Ord) ∧ vs = [Litv (Char c)]) ∨
    (∃n. op = (Op Chr) ∧ vs = [Litv (IntLit n)]) ∨
    (∃z c1 c2. op = (Op (Chopb z)) ∧ vs = [Litv (Char c1); Litv (Char c2)]) ∨
    (∃s. op = (Op Explode) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v ls. op = (Op Implode) ∧ vs = [v] ∧ (v_to_char_list v = SOME ls)) ∨
    (∃s. op = (Op Strlen) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v vs'. op = (Op VfromList) ∧ vs = [v] ∧ (v_to_list v = SOME vs')) ∨
    (∃vs' i. op = (Op Vsub) ∧ vs = [Vectorv vs'; Litv (IntLit i)]) ∨
    (∃vs'. op = (Op Vlength) ∧ vs = [Vectorv vs']) ∨
    (∃v n. op = (Op Aalloc) ∧ vs = [Litv (IntLit n); v]) ∨
    (∃lnum i. op = (Op Asub) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op Alength) ∧ vs = [Loc n]) ∨
    (∃lnum i v. op = (Op Aupdate) ∧ vs = [Loc lnum; Litv (IntLit i); v]) ∨
    (∃lnum n. op = (Op (FFI n)) ∧ vs = [Loc lnum])`,
  Cases_on`s`>>rw[conSemTheory.do_app_def] >>
  pop_assum mp_tac >>
  Cases_on`op` >- (
    simp[] >>
    every_case_tac >> fs[] ) >>
  BasicProvers.CASE_TAC);

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
