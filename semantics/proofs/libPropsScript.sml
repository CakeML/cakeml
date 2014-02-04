open preamble rich_listTheory optionTheory miscTheory;
open libTheory;

val _ = new_theory "libProps";

val lookup_zip_map = Q.store_thm ("lookup_zip_map",
`!x env keys vals res f res'.
  (LENGTH keys = LENGTH vals) ∧ (env = ZIP (keys,vals)) ∧ (lookup x env = res) ⇒
  (lookup x (ZIP (keys,MAP f vals)) = OPTION_MAP f res)`,
recInduct lookup_ind >>
rw [lookup_def] >>
cases_on `keys` >>
cases_on `vals` >>
fs []);

val lookup_append = Q.store_thm ("lookup_append",
`!x e1 e2.
  lookup x (e1++e2) =
     case lookup x e1 of
        | NONE => lookup x e2
        | SOME v => SOME v`,
induct_on `e1` >>
rw [lookup_def] >>
every_case_tac >>
PairCases_on `h` >>
fs [lookup_def] >>
rw [] >>
fs []);

val lookup_append_none = Q.store_thm ("lookup_append_none",
`!x e1 e2. 
  (lookup x (e1++e2) = NONE) = ((lookup x e1 = NONE) ∧ (lookup x e2 = NONE))`,
rw [lookup_append] >>
eq_tac >>
rw [] >>
cases_on `lookup x e1` >>
rw [] >>
fs []);

val lookup_reverse_none = Q.store_thm ("lookup_reverse_none",
`!x tenvC.
  (lookup x (REVERSE tenvC) = NONE) = (lookup x tenvC = NONE)`,
induct_on `tenvC` >>
rw [] >>
cases_on `h` >>
rw [lookup_def,lookup_append_none]);

val lookup_in = Q.store_thm ("lookup_in",
`!x e v. (lookup x e = SOME v) ⇒ MEM v (MAP SND e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val lookup_in2 = Q.store_thm ("lookup_in2",
`!x e v. (lookup x e = SOME v) ⇒ MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val lookup_notin = Q.store_thm ("lookup_notin",
`!x e. (lookup x e = NONE) = ~MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs []);

val _ = export_theory ();
