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

val lookup_in3 = Q.store_thm ("lookup_in3",
`!x env v. (lookup x env = SOME v) ⇒ MEM (x,v) env`,
 induct_on `env` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 every_case_tac >>
 fs []);

val lookup_notin = Q.store_thm ("lookup_notin",
`!x e. (lookup x e = NONE) = ~MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs []);

val lookup_all_distinct = Q.store_thm ("lookup_all_distinct",
`!l x y.
  ALL_DISTINCT (MAP FST l) ∧
  MEM (x,y) l
  ⇒
  (lookup x l = SOME y)`,
Induct_on `l` >>
rw [lookup_def] >>
rw [lookup_def] >>
PairCases_on `h` >>
rw [] >>
fs [MEM_MAP] >>
metis_tac [FST]);

val flookup_update_list_none = Q.store_thm ("flookup_update_list_none",
`!x m l.
  (FLOOKUP (m |++ l) x = NONE)
  =
  ((FLOOKUP m x = NONE) ∧ (lookup x l = NONE))`,
induct_on `l` >>
rw [FUPDATE_LIST_THM] >>
PairCases_on `h` >>
rw [FLOOKUP_DEF]);

val flookup_update_list_some = Q.store_thm ("flookup_update_list_some",
`!x m l y. 
  (FLOOKUP (m |++ l) x = SOME y)
  =
  ((lookup x (REVERSE l) = SOME y) ∨
   ((lookup x l = NONE) ∧ (FLOOKUP m x = SOME y)))`,
Induct_on `l` >>
rw [FUPDATE_LIST_THM] >>
PairCases_on `h` >>
rw [lookup_append, FLOOKUP_UPDATE] >|
[cases_on `lookup h0 (REVERSE l)` >>
     rw [] >>
     metis_tac [lookup_reverse_none, optionTheory.NOT_SOME_NONE],
 cases_on `lookup x (REVERSE l)` >>
     rw []]);

val lookup_map = Q.store_thm ("lookup_map",
`!n env v f. 
  (lookup n env = SOME v) ⇒ (lookup n (MAP (\(x,y). (x, f y)) env) = SOME (f v))`,
ho_match_mp_tac lookup_ind >>
rw []);

val lookup_reverse = Q.store_thm ("lookup_reverse",
`!env x.
  ALL_DISTINCT (MAP FST env)
  ⇒
  lookup x (REVERSE env) = lookup x env`,
induct_on `env` >>
rw [] >>
cases_on `h` >>
rw [lookup_append] >>
every_case_tac >>
fs [] >>
imp_res_tac lookup_in2);

val _ = export_theory ();
