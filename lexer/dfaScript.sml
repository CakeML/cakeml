(* A theory of paths through deterministic finite automata *)

open preamble;
open stringTheory finite_mapTheory;
open lcsymtacs;

val _ = new_theory "dfa";

val dfa_path_def = Define `
(dfa_path trans start_state end_state [] = (start_state = end_state)) ∧
(dfa_path trans start_state end_state ((c,state)::path) =
  case FLOOKUP trans (start_state,c) of
    | NONE => F
    | SOME new_state =>
        (new_state = state) ∧ dfa_path trans state end_state path)`;

val dfa_path_ind = fetch "-" "dfa_path_ind";

val dfa_path_append = Q.store_thm ("dfa_path_append",
`!trans s1 s2 p1 p2.
  dfa_path trans s1 s2 (p1 ++ p2) =
  ∃s'. dfa_path trans s1 s' p1 ∧ dfa_path trans s' s2 p2`,
ho_match_mp_tac dfa_path_ind >>
rw [dfa_path_def] >>
cases_on `FLOOKUP trans (s1,c)` >>
fs [] >>
metis_tac []);

val dfa_path_extend = Q.store_thm ("dfa_path_extend",
`!trans s1 s2 p c s3.
  dfa_path trans s1 s2 p ∧ (FLOOKUP trans (s2,c) = SOME s3)
  ⇒
  dfa_path trans s1 s3 (p++[(c,s3)])`,
rw [dfa_path_append] >>
rw [dfa_path_def] >>
qexists_tac `s2` >>
rw []);

val dfa_path_last = Q.store_thm ("dfa_path_last",
`!trans s1 s2 p. dfa_path trans s1 s2 p ∧ (p ≠ []) ⇒ ?p' c. p = p' ++ [(c,s2)]`,
Induct_on `p` >>
rw [dfa_path_def] >>
PairCases_on `h` >>
fs [dfa_path_def] >>
every_case_tac >>
fs [] >>
res_tac >>
fs [] >>
cases_on `p = []` >>
fs [dfa_path_def] >>
rw []);

val dfa_path_determ = Q.store_thm ("dfa_path_determ",
`!trans s1 s2 p s2' p'.
  dfa_path trans s1 s2 p ∧ dfa_path trans s1 s2' p' ∧ (MAP FST p = MAP FST p')
  ⇒
  (p = p') ∧ (s2 = s2')`,
Induct_on `p` >>
rw [dfa_path_def] >>
fs [dfa_path_def] >>
cases_on `p'` >>
fs [dfa_path_def] >>
PairCases_on `h` >>
PairCases_on `h'` >>
fs [dfa_path_def] >>
every_case_tac >>
fs [] >>
rw [] >>
metis_tac []);

val _ = export_theory ();
