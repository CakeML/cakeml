(* The specification of a lexer in terms of regular expressions *)
open preamble;
open stringTheory finite_mapTheory rich_listTheory;
open lcsymtacs;
open regexpTheory;

val strcat_lem = Q.prove (
`!s1 s2 s3 s4.
  (STRLEN s1 = STRLEN s3) ∧ (STRCAT s1 s2 = STRCAT s3 s4)
  ⇒
  (s1 = s3) ∧
  (s2 = s4)`,
Induct_on `s1` >>
rw [] >>
Cases_on `s3` >>
fs [] >>
metis_tac []);

val append_length_gt = Q.prove (
`!s1 s2 s3 s4.
  (LENGTH s1 > LENGTH s3) ∧ (s1 ++ s2 = s3 ++ s4) ⇒
  ?c s5. (s1 = s3 ++ c::s5)`,
Induct_on `s1` >>
rw [] >>
cases_on `s3` >>
full_simp_tac (srw_ss()++ARITH_ss) [] >>
rw [] >>
`LENGTH s1 > LENGTH t` by DECIDE_TAC >>
metis_tac []);

val _ = new_theory "lexer_spec";

val _ = type_abbrev ("lexer_spec", ``:(regexp#(string->'a)) list``);

val lexer_spec_matches_prefix_def = Define `
lexer_spec_matches_prefix lexer_spec n tok lexeme s_rest s =
  ∃r f.
    n < LENGTH lexer_spec ∧
    (EL n lexer_spec = (r,f)) ∧
    (tok = f lexeme) ∧
    regexp_matches r lexeme ∧
    (s = lexeme ++ s_rest)`;

val correct_lex_def = Define `
(correct_lex lexer_spec s [] = (s = [])) ∧
(correct_lex lexer_spec s (tok::toks) =
  ∃lexeme n s_rest.
    (lexeme ≠ []) ∧
    lexer_spec_matches_prefix lexer_spec n tok lexeme s_rest s ∧
    correct_lex lexer_spec s_rest toks ∧
    (* Ensure a longest match  *)
    (∀n' tok' lexeme' s_rest'.
        lexer_spec_matches_prefix lexer_spec n' tok' lexeme' s_rest' s ⇒
        (LENGTH lexeme' ≤ LENGTH lexeme)) ∧
    (* Ensure the earliest match of equal length *)
    (∀n' tok' lexeme' s_rest'.
        lexer_spec_matches_prefix lexer_spec n' tok' lexeme' s_rest' s ⇒
        (LENGTH lexeme' ≠ LENGTH lexeme) ∨
        (n ≤ n')))`;

val lexer_spec_matches_prefix_alt_def = Define `
lexer_spec_matches_prefix_alt lexer_spec tok lexeme s_rest s =
  ∃r f. (MEM (r,f) lexer_spec) ∧
        (tok = f lexeme) ∧ regexp_matches r lexeme ∧
        (s = lexeme ++ s_rest)`;

val lexer_spec_matches_equiv = Q.store_thm ("lexer_spec_matches_equiv",
`!lexer_spec tok lexeme s_rest s.
  lexer_spec_matches_prefix_alt lexer_spec tok lexeme s_rest s =
  ?n. lexer_spec_matches_prefix lexer_spec n tok lexeme s_rest s`,
rw [lexer_spec_matches_prefix_def, lexer_spec_matches_prefix_alt_def] >>
EQ_TAC >>
rw [MEM_EL] >>
metis_tac []);

val correct_lex_thm = Q.store_thm ("correct_lex_thm",
`!lexer_spec s tok toks.
 (correct_lex lexer_spec s [] = (s = [])) ∧
 (correct_lex lexer_spec s (tok::toks) =
   ∃lexeme n s_rest.
     (lexeme ≠ []) ∧
     lexer_spec_matches_prefix lexer_spec n tok lexeme s_rest s ∧
     correct_lex lexer_spec s_rest toks ∧
     (* Ensure a longest match  *)
     (∀tok' lexeme' s_rest'.
        (lexeme' ≠ "") ∧
        (s_rest = lexeme'++s_rest') ⇒
        ¬lexer_spec_matches_prefix_alt lexer_spec tok' (lexeme++lexeme') s_rest' s) ∧
     (* Ensure the earliest match of equal length *)
     (∀tok'.
        ¬lexer_spec_matches_prefix_alt (TAKE n lexer_spec) tok' lexeme s_rest s))`,
rw [] >>
rw [Once correct_lex_def] >>
eq_tac >>
rw [lexer_spec_matches_prefix_alt_def, lexer_spec_matches_prefix_def] >|
[qexists_tac `lexeme` >>
     qexists_tac `n` >>
     qexists_tac `s_rest` >>
     rw [] >>
     CCONTR_TAC  >>
     fs [MEM_EL] >>
     rw [] >|
     [`STRLEN (STRCAT lexeme lexeme') ≤ STRLEN lexeme`
                    by metis_tac [] >>
          fs [] >>
          `STRLEN lexeme' = 0` by DECIDE_TAC >>
          cases_on `lexeme'` >>
          fs [],
      `n ≤ LENGTH lexer_spec` by DECIDE_TAC >>
          fs [LENGTH_TAKE] >>
          `(r',f') = EL n' lexer_spec` by metis_tac [EL_TAKE, LENGTH_TAKE] >>
          `n' < LENGTH lexer_spec` by DECIDE_TAC >>
          `n ≤ n'` by metis_tac [LENGTH_TAKE] >>
          DECIDE_TAC],
 qexists_tac `lexeme` >>
     qexists_tac `n` >>
     qexists_tac `s_rest` >>
     rw [] >>
     CCONTR_TAC >>
     fs [] >|
     [`STRLEN lexeme' > STRLEN lexeme` by DECIDE_TAC >>
          `?c lexeme''. lexeme' = lexeme++c::lexeme''`
                   by metis_tac [append_length_gt] >>
          fs [MEM_EL] >>
          rw [] >>
          `c::lexeme'' ≠ ""` by rw [] >>
          metis_tac [APPEND, APPEND_ASSOC],
      `lexeme = lexeme'` by metis_tac [strcat_lem] >>
         `n' < n ∧ n' ≤ LENGTH lexer_spec ∧ n ≤ LENGTH lexer_spec`
                      by DECIDE_TAC >>
          fs [MEM_EL] >>
          rw [] >>
          metis_tac [EL_TAKE, LENGTH_TAKE]]]);

val correct_lex_determ = Q.store_thm ("correct_lex_determ",
`!lexer_spec s toks toks'.
  correct_lex lexer_spec s toks ∧ correct_lex lexer_spec s toks'
  ⇒
  (toks = toks')`,
induct_on `toks` >>
rw [correct_lex_def] >>
Cases_on `toks'` >>
rw [] >>
fs [] >>
rw [] >>
fs [correct_lex_def] >>
rw [] >|
[fs [lexer_spec_matches_prefix_def] >>
     metis_tac [],
 fs [lexer_spec_matches_prefix_def] >>
     metis_tac [],
 res_tac >>
     full_simp_tac (srw_ss()++ARITH_ss) [] >>
     `n = n'` by decide_tac >>
     fs [lexer_spec_matches_prefix_def] >>
     rw [] >>
     fs [] >>
     `STRLEN lexeme = STRLEN lexeme'` by decide_tac >>
     fs [lexer_spec_matches_prefix_def] >>
     rw [] >>
     fs [] >>
     metis_tac [strcat_lem],
 res_tac >>
     full_simp_tac (srw_ss()++ARITH_ss) [] >>
     `STRLEN lexeme = STRLEN lexeme'` by decide_tac >>
     fs [lexer_spec_matches_prefix_def] >>
     rw [] >>
     fs [] >>
     metis_tac [strcat_lem]]);

val _ = export_theory ();
