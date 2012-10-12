open preamble;
open stringTheory finite_mapTheory;
open lcsymtacs;

val split_concat = Q.prove (
`!ss c s.
  (c::s = CONCAT ss)
  ⇒
  ?ss1 s2 ss3. EVERY (\s. s = "") ss1 ∧ (ss = ss1++[c::s2]++ss3)`,
Induct_on `ss` >>
rw [] >>
cases_on `h` >>
fs [] >|
[res_tac >>
     rw [] >>
     qexists_tac `""::ss1` >>
     rw [],
 qexists_tac `[]` >>
     rw []]);

val concat_empties = Q.prove (
`!ss1 ss2. EVERY (\s. s = "") ss1 ⇒ (CONCAT (ss1 ++ ss2) = CONCAT ss2)`,
Induct_on `ss1` >>
rw []);

val _ = new_theory "regexp";

val _ = Hol_datatype `
regexp =
    CharSet of char set
  | StringLit of string
  | Cat of regexp => regexp
  | Star of regexp
  | Plus of regexp
  | Or of regexp list
  | Neg of regexp`;

val regexp_size_def = fetch "-" "regexp_size_def"

val regexp_matches_def = tDefine "regexp_matches" `
(regexp_matches (CharSet ns) s =
  ∃c. c IN ns ∧ (s = [c])) ∧
(regexp_matches (StringLit s') s =
  (s = s')) ∧
(regexp_matches (Cat r1 r2) s =
  ∃s1 s2. regexp_matches r1 s1 ∧ regexp_matches r2 s2 ∧ (s = s1 ++ s2)) ∧
(regexp_matches (Star r) s =
  ∃ss. EVERY (regexp_matches r) ss ∧ (s = FLAT ss)) ∧
(regexp_matches (Plus r) s =
  ∃ss. (ss ≠ []) ∧ EVERY (regexp_matches r) ss ∧ (s = FLAT ss)) ∧
(regexp_matches (Or rs) s =
  EXISTS (\r. regexp_matches r s) rs) ∧
(regexp_matches (Neg r) s =
  ~regexp_matches r s)`
(WF_REL_TAC `measure (\(x,y). regexp_size x)` >>
srw_tac [ARITH_ss] [] >>
Induct_on `rs` >>
rw [regexp_size_def] >>
full_simp_tac (srw_ss()++ARITH_ss) []);

val nullable_def = tDefine "nullable" `
(nullable (CharSet _) = F) ∧
(nullable (StringLit "") = T) ∧
(nullable (StringLit _) = F) ∧
(nullable (Cat r1 r2) = nullable r1 ∧ nullable r2) ∧
(nullable (Star _) = T) ∧
(nullable (Plus r) = nullable r) ∧
(nullable (Or rs) = EXISTS nullable rs) ∧
(nullable (Neg r) = ¬nullable r)`
(WF_REL_TAC `measure regexp_size` >>
srw_tac [ARITH_ss] [] >>
Induct_on `rs` >>
rw [fetch "-" "regexp_size_def"] >>
full_simp_tac (srw_ss()++ARITH_ss) []);


val deriv_def = tDefine "deriv" `
(deriv c (CharSet cs) =
  if c ∈ cs then
    (StringLit "")
  else
    CharSet {}) ∧
(deriv c (StringLit "") =
  CharSet {}) ∧
(deriv c (StringLit (c'::s)) =
  if c = c' then
    StringLit s
  else
    CharSet {}) ∧
(deriv c (Cat r1 r2) =
  let cat = Cat (deriv c r1) r2 in
    if nullable r1 then
      Or [cat; (deriv c r2)]
    else
      cat) ∧
(deriv c (Star r) =
  Cat (deriv c r) (Star r)) ∧
(deriv c (Plus r) = 
  Cat (deriv c r) (Star r)) ∧
(deriv c (Or rs) = Or (MAP (deriv c) rs)) ∧
(deriv c (Neg r) = Neg (deriv c r))`
(WF_REL_TAC `measure (\(x,y). regexp_size y)` >>
srw_tac [ARITH_ss] [] >>
Induct_on `rs` >>
rw [regexp_size_def] >>
full_simp_tac (srw_ss()++ARITH_ss) []);

val deriv_matches_def = Define `
(deriv_matches r "" = nullable r) ∧
(deriv_matches r (c::s) = deriv_matches (deriv c r) s)`;

val nullable_thm = Q.prove (
`!r. nullable r = regexp_matches r ""`,
recInduct (fetch "-" "nullable_ind") >>
rw [nullable_def, regexp_matches_def] >|
[qexists_tac `[]` >>
     rw [],
 eq_tac >>
     rw [] >|
     [qexists_tac `[""]` >>
          rw [],
      cases_on `ss` >>
          fs []],
 fs [EXISTS_MEM] >>
     metis_tac []]);

val deriv_thm = Q.prove (
`(∀r c s. regexp_matches r (c::s) = regexp_matches (deriv c r) s) ∧
 (∀rs c s. regexp_matches (Or rs) (c::s) = regexp_matches (deriv c (Or rs)) s)`,
HO_MATCH_MP_TAC (fetch "-" "regexp_induction") >>
rw [regexp_matches_def, deriv_def, LET_THM] >|
[cases_on `s` >>
     rw [deriv_def, regexp_matches_def],
 eq_tac >>
     rw [regexp_matches_def, nullable_thm] >|
     [cases_on `s1` >>
          fs [] >>
          metis_tac [],
      cases_on `s1` >>
          fs [] >>
          metis_tac [],
      metis_tac [STRCAT_EQNS],
      metis_tac [STRCAT_EQNS],
      metis_tac [STRCAT_EQNS]],
  all_tac,
  all_tac] >>
(eq_tac >>
rw [] >|
[imp_res_tac split_concat >>
     fs [] >>
     rw [] >>
     qexists_tac `s2` >>
     qexists_tac `CONCAT ss3` >>
     rw [] >-
     metis_tac [] >-
     metis_tac [] >>
     `c::s = CONCAT ([c::s2]++ss3)` by metis_tac [concat_empties, APPEND_ASSOC] >>
     fs [],
 qexists_tac `(c :: s1) :: ss` >>
     rw []]));

val regexp_matches_thm = Q.store_thm ("regexp_matches_thm",
`!r s. regexp_matches r s = deriv_matches r s`,
Induct_on `s` >>
rw [deriv_matches_def, nullable_thm] >>
metis_tac [deriv_thm]);

val _ = computeLib.add_persistent_funs 
            ["regexp_matches_thm", "deriv_matches_def", "deriv_def", "nullable_def"];

val _ = export_theory ();
