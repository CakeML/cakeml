open preamble exhSemTheory;

val _ = new_theory"exhProps";

val do_app_cases = Q.store_thm("do_app_cases",
  `exhSem$do_app s op vs = SOME x ⇒
    (∃z n1 n2. op = (Op (Opn z)) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃z n1 n2. op = (Op (Opb z)) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃v1 v2. op = (Op Equality) ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = (Op Opassign) ∧ vs = [Loc lnum; v]) ∨
    (∃n. op = (Op Opderef) ∧ vs = [Loc n]) ∨
    (∃v. op = (Op Opref) ∧ vs = [v]) ∨
    (∃idx v. op = (Init_global_var idx) ∧ vs = [v]) ∨
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
  PairCases_on`s`>>rw[exhSemTheory.do_app_def] >>
  pop_assum mp_tac >>
  Cases_on`op` >- (
    simp[] >>
    every_case_tac >> fs[] ) >>
  BasicProvers.CASE_TAC >>
  every_case_tac);

val build_rec_env_merge = store_thm("build_rec_env_merge",
  ``build_rec_env funs cle env = MAP (λ(f,cdr). (f, (Recclosure cle funs f))) funs ++ env``,
  rw[build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[] >>
  PairCases_on`h` >> rw[])

val Boolv_disjoint = save_thm("Boolv_disjoint",EVAL``exhSem$Boolv T = Boolv F``);

val pmatch_any_match = store_thm("pmatch_any_match",
  ``(∀s p v env env'. pmatch s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch s p v env = Match env') ∧
    (∀s ps vs env env'. pmatch_list s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list s ps vs env = Match env')``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_no_match = store_thm("pmatch_any_no_match",
  ``(∀s p v env. pmatch s p v env = No_match ⇒
       ∀env. pmatch s p v env = No_match) ∧
    (∀s ps vs env. pmatch_list s ps vs env = No_match ⇒
       ∀env. pmatch_list s ps vs env = No_match)``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  imp_res_tac pmatch_any_match >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_match_error = store_thm("pmatch_any_match_error",
  ``(∀s p v env. pmatch s p v env = Match_type_error ⇒
       ∀env. pmatch s p v env = Match_type_error) ∧
    (∀s ps vs env. pmatch_list s ps vs env = Match_type_error ⇒
       ∀env. pmatch_list s ps vs env = Match_type_error)``,
  rw[] >> qmatch_abbrev_tac`X = Y` >> Cases_on`X` >> fs[markerTheory.Abbrev_def] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct
           ,pmatch_any_no_match,pmatch_any_match]);

val pmatch_list_pairwise = store_thm("pmatch_list_pairwise",
  ``∀ps vs s env env'. pmatch_list s ps vs env = Match env' ⇒
      EVERY2 (λp v. ∀env. ∃env'. pmatch s p v env = Match env') ps vs``,
  Induct >> Cases_on`vs` >> simp[pmatch_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  res_tac >> simp[] >> metis_tac[pmatch_any_match])

val _ = store_thm("pmatch_list_snoc_nil[simp]",
  ``∀p ps v vs s env.
      (pmatch_list s [] (SNOC v vs) env = Match_type_error) ∧
      (pmatch_list s (SNOC p ps) [] env = Match_type_error)``,
  Cases_on`ps`>>Cases_on`vs`>>simp[pmatch_def]);

val pmatch_list_snoc = store_thm("pmatch_list_snoc",
  ``∀ps vs p v s env. LENGTH ps = LENGTH vs ⇒
      pmatch_list s (SNOC p ps) (SNOC v vs) env =
      case pmatch_list s ps vs env of
      | Match env' => pmatch s p v env'
      | res => res``,
  Induct >> Cases_on`vs` >> simp[pmatch_def] >> rw[] >>
  BasicProvers.CASE_TAC)

val _ = export_theory()
