(* The specification of a lexer in terms of regular expressions *)
open preamble;
open stringTheory finite_mapTheory;
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
