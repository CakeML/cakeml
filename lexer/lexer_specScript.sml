(* The specification of a lexer in terms of regular expressions *)
open preamble;
open stringTheory finite_mapTheory;
open lcsymtacs;

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

val _ = Hol_datatype `
regexp =
    CharSet of char set
  | StringLit of string
  | Cat of regexp => regexp
  | Star of regexp
  | Plus of regexp
  | Or of regexp list
  | Neg of regexp`;

val _ = type_abbrev ("lexer_spec", ``:(regexp#(string->'a)) list``);

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
rw [fetch "-" "regexp_size_def"] >>
full_simp_tac (srw_ss()++ARITH_ss) []);

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
