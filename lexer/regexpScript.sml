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
`!ss1. EVERY (\s. s = []) ss1 ⇒ (CONCAT ss1 = [])`,
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

(* Check if a regexp matches nothing.  Neg r should match nothing iff r matches
 * every possible string; however, that is not easy to determine, so we're
 * conservative here and just say that Neg r might always match something *)
val is_regexp_empty_def = tDefine "is_regexp_empty"`
(is_regexp_empty (CharSet cs) = (cs = {})) ∧
(is_regexp_empty (StringLit _) = F) ∧
(is_regexp_empty (Cat r1 r2) = is_regexp_empty r1 ∨ is_regexp_empty r2) ∧
(is_regexp_empty (Star _) = F) ∧
(is_regexp_empty (Plus r) = is_regexp_empty r) ∧
(is_regexp_empty (Or rs) = EVERY is_regexp_empty rs) ∧
(is_regexp_empty (Neg r) = F)`
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

val build_char_set_def = Define `
build_char_set cs = CharSet cs`;

val build_string_lit_def = Define `
(build_string_lit "" = Star (CharSet {})) ∧
(build_string_lit [c] = CharSet {c}) ∧
(build_string_lit (c1::c2::s) = Cat (CharSet {c1}) (build_string_lit (c2::s)))`;

val assoc_cat_def = Define `
(assoc_cat (Cat r1 r2) r3 = Cat r1 (assoc_cat r2 r3)) ∧
(assoc_cat r1 r2 = Cat r1 r2)`;

val build_cat_def = Define `
(build_cat r1 r2 =
  if (r1 = CharSet {}) ∨ (r2 = CharSet {}) then
    CharSet {}
  else if r1 = Star (CharSet {}) then
    r2
  else if r2 = Star (CharSet {}) then
    r1
  else
    assoc_cat r1 r2)`;

val build_neg_def = Define `
(build_neg (Neg r) = r) ∧
(build_neg r = (Neg r))`;

val build_star_def = Define `
(build_star (Star r) = Star r) ∧
(build_star r = Star r)`;

val build_plus_def = Define `
build_plus r = build_cat r (build_star r)`;

val flatten_or_def = Define `
(flatten_or [] = []) ∧
(flatten_or (Or rs::rs') = rs ++ flatten_or rs') ∧
(flatten_or (r::rs) = r :: flatten_or rs)`;

val build_or_def = Define `
build_or rs =
  let rs = flatten_or rs in
    if MEM (Neg (CharSet {})) rs then
      Neg (CharSet {})
    else
      (* TODO: We should sort, remove duplicates, and merge CharSets *)
      case (FILTER (\r. r ≠ CharSet {}) rs) of
        | [] => CharSet {}
        | [r] => r
        | res => Or res`;

val regexp_smart_constructors_def =
  save_thm ("regexp_smart_constructors_def",
            LIST_CONJ [build_or_def, build_plus_def, build_star_def,
            build_cat_def, build_string_lit_def, build_char_set_def,
            assoc_cat_def, build_neg_def]);

val normalize_def = tDefine "normalize" `
(normalize (CharSet cs) =
  build_char_set cs) ∧
(normalize (StringLit s) =
  build_string_lit s) ∧
(normalize (Cat r1 r2) =
  build_cat (normalize r1) (normalize r2)) ∧
(normalize (Star r) =
  build_star (normalize r)) ∧
(normalize (Plus r) =
  build_plus (normalize r)) ∧
(normalize (Or rs) =
  build_or (MAP normalize rs)) ∧
(normalize (Neg r) =
  build_neg (normalize r))`
(WF_REL_TAC `measure regexp_size` >>
srw_tac [ARITH_ss] [] >>
Induct_on `rs` >>
rw [regexp_size_def] >>
full_simp_tac (srw_ss()++ARITH_ss) []);

val normalize_ind =  (fetch "-" "normalize_ind")

val is_normalized_def = tDefine "is_normalized" `
(is_normalized (CharSet cs) =
  T) ∧
(is_normalized (StringLit s) =
  F) ∧
(is_normalized (Cat r1 r2) =
  (r1 ≠ CharSet {}) ∧
  (r2 ≠ CharSet {}) ∧
  (r1 ≠ Star (CharSet {})) ∧
  (r2 ≠ Star (CharSet {})) ∧
  (case r1 of
     | Cat _ _ => F
     | _ => T) ∧
  (is_normalized r1) ∧
  (is_normalized r2)) ∧
(is_normalized (Star r) =
  is_normalized r ∧
  (case r of
     | Star _ => F
     | _ => T)) ∧
(is_normalized (Plus r) =
  F) ∧
(is_normalized (Or rs) =
  LENGTH rs > 1 ∧
  EVERY (\r. is_normalized r ∧
             (case r of
                 | Or _ => F
                 | _ => T) ∧
             (r ≠ Neg (CharSet {})) ∧
             (r ≠ CharSet {}))
        rs) ∧
(is_normalized (Neg r) =
  is_normalized r ∧
  (case r of
     | Neg _ => F
     | _ => T))`
(WF_REL_TAC `measure regexp_size` >>
srw_tac [ARITH_ss] [] >>
Induct_on `rs` >>
rw [regexp_size_def] >>
full_simp_tac (srw_ss()++ARITH_ss) []);


val smart_deriv_def = tDefine "smart_deriv" `
(smart_deriv c (CharSet cs) =
  if c ∈ cs then
    (build_string_lit "")
  else
    build_char_set {}) ∧
(smart_deriv c (StringLit "") =
  build_char_set {}) ∧
(smart_deriv c (StringLit (c'::s)) =
  if c = c' then
    build_string_lit s
  else
    build_char_set {}) ∧
(smart_deriv c (Cat r1 r2) =
  let cat = build_cat (smart_deriv c r1) r2 in
    if nullable r1 then
      build_or [cat; (smart_deriv c r2)]
    else
      cat) ∧
(smart_deriv c (Star r) =
  build_cat (smart_deriv c r) (build_star r)) ∧
(smart_deriv c (Plus r) =
  build_cat (smart_deriv c r) (build_star r)) ∧
(smart_deriv c (Or rs) = build_or (MAP (smart_deriv c) rs)) ∧
(smart_deriv c (Neg r) = build_neg (smart_deriv c r))`
(WF_REL_TAC `measure (\(x,y). regexp_size y)` >>
srw_tac [ARITH_ss] [] >>
Induct_on `rs` >>
rw [regexp_size_def] >>
full_simp_tac (srw_ss()++ARITH_ss) []);

val smart_deriv_matches_def = Define `
(smart_deriv_matches r "" = nullable r) ∧
(smart_deriv_matches r (c::s) = smart_deriv_matches (smart_deriv c r) s)`;

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
     imp_res_tac concat_empties >>
     fs [] >> cheat,
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

val regexp_empty_thm = Q.store_thm ("regexp_empty_thm",
`!r l. is_regexp_empty r ⇒ ~regexp_matches r l`,
recInduct (fetch "-" "is_regexp_empty_ind") >>
rw [is_regexp_empty_def, regexp_matches_def, EVERY_EL] >>
fs [is_regexp_empty_def, MEM_EL] >|
[cases_on `ss` >>
     rw [] >>
     disj1_tac >>
     qexists_tac `0` >>
     decide_tac,
 metis_tac []]);

val assoc_cat_cat = Q.prove (
`!r1 r2. ?r1' r2'. assoc_cat r1 r2 = Cat r1' r2'`,
recInduct (fetch "-" "assoc_cat_ind") >>
rw [assoc_cat_def]);

val normalized_assoc_cat = Q.prove (
`!r1 r2.
  (r1 ≠ CharSet {}) ∧
  (r2 ≠ CharSet {}) ∧
  (r1 ≠ Star (CharSet {})) ∧
  (r2 ≠ Star (CharSet {})) ∧
  is_normalized r1 ∧
  is_normalized r2
  ⇒
  is_normalized (assoc_cat r1 r2)`,
recInduct (fetch "-" "assoc_cat_ind") >>
rw [is_normalized_def, regexp_smart_constructors_def] >>
cases_on `r1` >>
fs [is_normalized_def] >>
metis_tac [assoc_cat_cat, fetch "-" "regexp_distinct"]);

val norm_string_lit = Q.prove (
`!s. is_normalized (build_string_lit s)`,
induct_on `s` >>
     rw [] >>
     fs [is_normalized_def, regexp_smart_constructors_def] >>
     cases_on `s` >>
     fs [is_normalized_def, regexp_smart_constructors_def] >>
     cases_on `t` >>
     rw [] >>
     fs [is_normalized_def, regexp_smart_constructors_def]);

val norm_char_set = Q.prove (
`!cs. is_normalized (build_char_set cs)`,
rw [is_normalized_def, regexp_smart_constructors_def]);

val norm_cat = Q.prove (
`!r1 r2. is_normalized r1 ∧ is_normalized r2 ⇒ is_normalized (build_cat r1 r2)`,
rw [] >>
cases_on `r1` >>
fs [is_normalized_def, regexp_smart_constructors_def] >>
rw [] >>
fs [is_normalized_def, regexp_smart_constructors_def] >>
rw [] >-
metis_tac [assoc_cat_cat, fetch "-" "regexp_distinct"] >-
metis_tac [assoc_cat_cat, fetch "-" "regexp_distinct"] >>
match_mp_tac normalized_assoc_cat >>
rw [is_normalized_def]);

val norm_star = Q.prove (
`!r. is_normalized r ⇒ is_normalized (build_star r)`,
cases_on `r` >>
rw [is_normalized_def, regexp_smart_constructors_def]);

val norm_plus = Q.prove (
`!r. is_normalized r ⇒ is_normalized (build_plus r)`,
cases_on `r` >>
rw [is_normalized_def, regexp_smart_constructors_def] >-
metis_tac [assoc_cat_cat, fetch "-" "regexp_distinct"] >-
metis_tac [assoc_cat_cat, fetch "-" "regexp_distinct"] >>
match_mp_tac normalized_assoc_cat >>
rw [is_normalized_def]);

val norm_neg = Q.prove (
`!r. is_normalized r ⇒ is_normalized (build_neg r)`,
cases_on `r` >>
rw [is_normalized_def, regexp_smart_constructors_def]);

val flatten_or_thm = Q.prove (
`!rs r. MEM r (flatten_or rs) ∧ EVERY is_normalized rs ⇒ ¬?rs'. r = Or rs'`,
recInduct (fetch "-" "flatten_or_ind") >>
rw [flatten_or_def] >>
fs [is_normalized_def, EVERY_MEM] >>
res_tac >>
fs [] >>
cases_on `r` >>
fs []);

val flatten_or_norm = Q.prove (
`!rs r. EVERY is_normalized rs ⇒ EVERY is_normalized (flatten_or rs)`,
recInduct (fetch "-" "flatten_or_ind") >>
rw [flatten_or_def] >>
fs [is_normalized_def, EVERY_MEM]);

val norm_or = Q.prove (
`!rs. EVERY is_normalized rs ⇒ is_normalized (build_or rs)`,
cheat);
(*
rw [build_or_def, is_normalized_def] >>
cases_on `MEM (Neg (CharSet ∅)) rs'` >>
rw [is_normalized_def] >>
`!r. MEM r rs' ⇒ ¬?rs'. r = Or rs'` by metis_tac [flatten_or_thm] >>
cases_on `FILTER (λr. r ≠ CharSet ∅) rs'` >>
fs [is_normalized_def] >>
cases_on `t` >>
fs [is_normalized_def, markerTheory.Abbrev_def, EVERY_MEM] >-
metis_tac [flatten_or_norm, MEM, EVERY_MEM, MEM_FILTER] >>
rw [] >|
[decide_tac,
 metis_tac [flatten_or_norm, MEM, EVERY_MEM, MEM_FILTER, FILTER],
 `¬?rs'. h = Or rs'` by metis_tac [flatten_or_thm, MEM, EVERY_MEM, MEM_FILTER] >>
     cases_on `h` >>
     fs [],
 metis_tac [MEM, EVERY_MEM, MEM_FILTER, FILTER],
 `MEM h (FILTER (λr. r ≠ CharSet ∅) (flatten_or rs))` by metis_tac [MEM] >>
     fs [MEM_FILTER],
 metis_tac [flatten_or_norm, MEM, EVERY_MEM, MEM_FILTER, FILTER],
 `¬?rs'. h' = Or rs'` by metis_tac [flatten_or_thm, MEM, EVERY_MEM, MEM_FILTER] >>
     cases_on `h'` >>
     fs [],
 metis_tac [MEM, EVERY_MEM, MEM_FILTER, FILTER],
 `MEM h' (FILTER (λr. r ≠ CharSet ∅) (flatten_or rs))` by metis_tac [MEM] >>
     fs [MEM_FILTER],
 metis_tac [flatten_or_norm, MEM, EVERY_MEM, MEM_FILTER, FILTER],
 `¬?rs'. r = Or rs'` by metis_tac [flatten_or_thm, MEM, EVERY_MEM, MEM_FILTER] >>
     cases_on `r` >>
     fs [],
 metis_tac [MEM, EVERY_MEM, MEM_FILTER, FILTER],
 `MEM r (FILTER (λr. r ≠ CharSet ∅) (flatten_or rs))` by metis_tac [MEM] >>
     fs [MEM_FILTER]]);*)

val normalize_thm = Q.store_thm ("normalize_thm",
`!r. is_normalized (normalize r)`,
recInduct normalize_ind >>
rw [normalize_def, norm_string_lit, norm_char_set, norm_cat, norm_neg,
    norm_star, norm_plus] >>
metis_tac [norm_or, EVERY_MEM, MEM_MAP]);

val smart_deriv_normalized = Q.store_thm ("smart_deriv_normalized",
`!c r. is_normalized r ⇒ is_normalized (smart_deriv c r)`,
recInduct (fetch "-" "smart_deriv_ind") >>
rw [is_normalized_def, smart_deriv_def, normalize_def, norm_string_lit,
    norm_char_set, norm_cat, norm_neg, norm_star, norm_plus] >|
[Q.UNABBREV_TAC `cat` >>
     cases_on `nullable r1` >>
     rw [is_normalized_def] >|
     [match_mp_tac norm_or >>
          rw [norm_cat],
      rw [norm_cat]],
 match_mp_tac norm_or >>
     rw [EVERY_MAP] >>
     fs [EVERY_MEM]]);

val norm_is_regexp_empty = Q.store_thm ("norm_is_regexp_empty",
`!r. is_normalized r ⇒ (is_regexp_empty r = (r = CharSet {}))`,
recInduct (fetch "-" "is_normalized_ind") >>
rw [is_normalized_def, is_regexp_empty_def] >>
fs [EXISTS_MEM, EVERY_MEM] >>
rw [] >>
cases_on `rs` >>
rw [] >>
fs [] >>
metis_tac []);

val regexp_matches_smart_deriv = Q.store_thm ("regexp_matches_smart_deriv",
`!r s. regexp_matches r s = smart_deriv_matches r s`,
cheat);

val regexp_matches_normalize = Q.store_thm ("regexp_matches_normalize",
`!r s. regexp_matches r s = regexp_matches (normalize r) s`,
cheat);

val _ = export_theory ();
