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

val regexp_alphabet_def = Define `
regexp_alphabet r = { c | ∃s. MEM c s ∧ regexp_matches r s }`;

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

val regexp_char_set_def = Define `
regexp_char_set cs = CharSet cs`;

val regexp_string_lit_def = Define `
(regexp_string_lit "" = Star (CharSet {})) ∧
(regexp_string_lit (c::s) = Cat (CharSet {c}) (regexp_string_lit s))`;

val regexp_cat_def = Define `
regexp_cat r1 r2 =
  if (r1 = CharSet {}) ∨ (r2 = CharSet {}) then
    CharSet {}
  else if r1 = Star (CharSet {}) then
    r2
  else if r2 = Star (CharSet {}) then
    r1
  else
    case r1 of
      | Cat r3 r4 => regexp_cat r3 (Cat r4 r2)
      | _ => Cat r1 r2`;

val regexp_neg_def = Define `
(regexp_neg (Neg r) = r) ∧
(regexp_neg r = (Neg r))`;

val regexp_star_def = Define `
(regexp_star (Star r) = Star r) ∧
(regexp_star r = Star r)`;

val regexp_plus_def = Define `
regexp_plus r = regexp_cat r (regexp_star r)`;

val flatten_or_def = Define `
(flatten_or [] = []) ∧
(flatten_or (Or rs::rs') = rs ++ flatten_or rs') ∧
(flatten_or (r::rs) = r :: flatten_or rs)`;

val regexp_or_def = Define `
regexp_or rs = 
  let rs = flatten_or rs in
    if MEM (Neg (CharSet {})) rs then
      Neg (CharSet {})
    else
      (* TODO: We should sort, remove duplicates, and merge CharSets *)
      case rs of
        | [] => CharSet {}
        | [r] => r
        | res => Or res`;

val normalize_regexp_def = tDefine "normalize_regexp" `
(normalize_regexp (CharSet cs) = 
  regexp_char_set cs) ∧
(normalize_regexp (StringLit s) = 
  regexp_string_lit s) ∧
(normalize_regexp (Cat r1 r2) = 
  regexp_cat (normalize_regexp r1) (normalize_regexp r2)) ∧
(normalize_regexp (Star r) =
  regexp_star (normalize_regexp r)) ∧
(normalize_regexp (Plus r) =
  regexp_plus (normalize_regexp r)) ∧
(normalize_regexp (Or rs) =
  regexp_or (MAP normalize_regexp rs)) ∧
(normalize_regexp (Neg r) =
  regexp_neg (normalize_regexp r))`
(WF_REL_TAC `measure regexp_size` >>
srw_tac [ARITH_ss] [] >>
Induct_on `rs` >>
rw [regexp_size_def] >>
full_simp_tac (srw_ss()++ARITH_ss) []);

val nullable_thm = Q.store_thm ("nullable_thm",
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

val regexp_matches_deriv = Q.store_thm ("regexp_matches_deriv",
`!r s. regexp_matches r s = deriv_matches r s`,
Induct_on `s` >>
rw [deriv_matches_def, nullable_thm] >>
metis_tac [deriv_thm]);

val regexp_matches_eqns = Q.store_thm ("regexp_matches_eqns",
`(!s. regexp_matches (CharSet {}) s = F) ∧
 (!r1 r2 r3 s.
    regexp_matches (Cat (Cat r1 r2) r3) s = 
    regexp_matches (Cat r1 (Cat r2 r3)) s) ∧
 (!s. regexp_matches (Or []) s = F) ∧
 (!s r. regexp_matches (Or [r]) s = regexp_matches r s) ∧
 (!r. (!s. regexp_matches r s = F) ⇒
      (!r' s. regexp_matches (Cat r' r) s = F) ∧
      (!r' s. regexp_matches (Cat r r') s = F) ∧
      (!s. regexp_matches (Star r) s = (s = "")) ∧
      (!s. regexp_matches (Plus r) s = F)) ∧
 (!r. (!s. regexp_matches r s = (s = "")) ⇒
      (!r' s. regexp_matches (Cat r' r) s = regexp_matches r' s) ∧
      (!r' s. regexp_matches (Cat r r') s = regexp_matches r' s) ∧
      (!s. regexp_matches (Star r) s = (s = "")) ∧
      (!s. regexp_matches (Plus r) s = (s = "")))`,
rw [regexp_matches_def] >|
[metis_tac [APPEND_ASSOC],
 eq_tac >>
     rw [] >|
     [metis_tac [concat_empties, APPEND_NIL, FLAT],
      qexists_tac `[]` >>
          rw []], 
 eq_tac >>
     rw [] >|
     [metis_tac [concat_empties, APPEND_NIL, FLAT],
      qexists_tac `[""]` >>
          rw []]]);

val deriv_matches_eqns = 
  save_thm ("deriv_matches_eqns",
            REWRITE_RULE [regexp_matches_deriv] regexp_matches_eqns);

val regexp_matches_ctxt_eqns = Q.store_thm ("regexp_matches_ctxt_eqns",
`!r1 r2. 
  (!s. regexp_matches r1 s = regexp_matches r2 s)
  ⇒
  (!r s. regexp_matches (Cat r1 r) s = regexp_matches (Cat r2 r) s) ∧
  (!r s. regexp_matches (Cat r r1) s = regexp_matches (Cat r r2) s) ∧
  (!s. regexp_matches (Star r1) s = regexp_matches (Star r2) s) ∧
  (!s. regexp_matches (Plus r1) s = regexp_matches (Plus r2) s) ∧
  (!s rs1 rs2. regexp_matches (Or (rs1++r1::rs2)) s = 
               regexp_matches (Or (rs1++r2::rs2)) s) ∧
  (!s. regexp_matches (Neg r1) s = regexp_matches (Neg r2) s)`,
rw [regexp_matches_def]);

val deriv_matches_ctxt_eqns = 
  save_thm ("deriv_matches_ctxt_eqns",
            REWRITE_RULE [regexp_matches_deriv] regexp_matches_ctxt_eqns);

(* We can use this as a quick regexp matcher in the rewriter, but it doesn't
 * handle Neg and diverges on (Star r) where (regexp_matches r "") *)
val regexp_matches_algorithm = Q.store_thm ("regexp_matches_algorithm",
`(!cs r s. 
  regexp_matches (Cat (CharSet cs) r) [] = 
    F) ∧
 (!cs r c s. 
   regexp_matches (Cat (CharSet cs) r) (c::s) = 
     c ∈ cs ∧ regexp_matches r s) ∧
 (!s' r. 
   regexp_matches (Cat (StringLit s') r) [] = 
     (s' = []) ∧ nullable r) ∧
 (!r c s. 
   regexp_matches (Cat (StringLit []) r) (c::s) = 
     regexp_matches r (c::s)) ∧
 (!c' s' r c s. 
   regexp_matches (Cat (StringLit (c'::s')) r) (c::s) = 
     (c = c') ∧ regexp_matches (Cat (StringLit s') r) s) ∧
 (!r1 r2 r3 s. 
   regexp_matches (Cat (Cat r1 r2) r3) s = 
     regexp_matches (Cat r1 (Cat r2 r3)) s) ∧
 (!r1 r2 s. 
   regexp_matches (Cat (Star r1) r2) s = 
     regexp_matches r2 s ∨
     regexp_matches (Cat r1 (Cat (Star r1) r2)) s) ∧
 (!r1 r2 s. 
   regexp_matches (Cat (Plus r1) r2) s = 
     regexp_matches (Cat r1 (Cat (Star r1) r2)) s) ∧
 (!rs r s.
   regexp_matches (Cat (Or rs) r) s =
     EXISTS (\r'. regexp_matches (Cat r' r) s) rs)`,
rw [regexp_matches_def] >>
eq_tac >>
rw [] >>
fs [nullable_thm, EVERY_MEM] >-
metis_tac [APPEND] >-
metis_tac [APPEND_ASSOC] >-
metis_tac [APPEND_ASSOC] >|
[cases_on `ss` >>
     rw [] >>
     DISJ2_TAC >>
     qexists_tac `h` >>
     qexists_tac `CONCAT t ++ s2` >>
     rw [] >>
     fs [] >>
     metis_tac [],
 qexists_tac `""` >>
     qexists_tac `s` >>
     rw [] >>
     qexists_tac `[]` >>
     rw [],
 qexists_tac `s1 ++ CONCAT ss` >>
     qexists_tac `s2'` >>
     rw [] >>
     metis_tac [FLAT, MEM],
 cases_on `ss` >>
     fs [] >>
     qexists_tac `h` >>
     qexists_tac `CONCAT t ++ s2` >>
     rw [] >>
     metis_tac [FLAT, MEM],
 qexists_tac `s1 ++ CONCAT ss` >>
     qexists_tac `s2'` >>
     rw [] >>
     metis_tac [FLAT, MEM],
 fs [EXISTS_MEM] >>
     metis_tac [],
 fs [EXISTS_MEM] >>
     metis_tac []]);

val _ = export_theory ();
