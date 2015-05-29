open preamble exhSemTheory;

val _ = new_theory"exhProps";

val build_rec_env_merge = store_thm("build_rec_env_merge",
  ``build_rec_env funs cle env = MAP (λ(f,cdr). (f, (Recclosure cle funs f))) funs ++ env``,
  rw[build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[] >>
  PairCases_on`h` >> rw[])

val _ = export_theory()
