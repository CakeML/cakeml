open preamble;
open listTheory rich_listTheory intLib;
open Print_astTheory Print_astTerminationTheory SMLlexTheory lexer_specTheory;
open regexpTheory lexer_spec_to_dfaTheory lexer_runtimeTheory;

val _ = new_theory "print_astProofs"

val tree_to_list_acc = Q.store_thm ("tree_to_list_acc",
`!st s1 s2. tree_to_list st (s1 ++ s2) = tree_to_list st s1 ++ s2`,
induct_on `st` >>
rw [tree_to_list_def]);

val tree_to_list_append = Q.store_thm ("tree_to_list_append",
`!st1 st2 s.
  tree_to_list (N st1 st2) s =
  tree_to_list st1 [] ++ tree_to_list st2 [] ++ s`,
induct_on `st1` >>
rw [tree_to_list_def] >>
induct_on `st2` >>
rw [tree_to_list_def] >>
metis_tac [tree_to_list_acc]);

val is_sml_infix_spec = Q.store_thm ("is_sml_infix_spec",
`!s.
  is_sml_infix s =
  MEM s ["mod"; "<>"; ">="; "<="; ":="; "::"; "before"; "div"; "o"; "@"; ">";
         "="; "<"; "/"; "-"; "+"; "*"]`,
rw [] >>
EQ_TAC >>
rw [is_sml_infix_def, LET_THM, SUB_def] >>
fs []);

val num_to_string_to_num = Q.prove (
`!n s. string_to_num (REVERSE (num_to_string n "")) = n`,
cheat);

val num_to_string_digits = Q.prove (
`!n. EVERY (\c. (c = #"0") ∨
                (c = #"1") ∨
                (c = #"2") ∨
                (c = #"3") ∨
                (c = #"4") ∨
                (c = #"5") ∨
                (c = #"6") ∨
                (c = #"7") ∨
                (c = #"8") ∨
                (c = #"9")) (num_to_string n "")`,
cheat);

val num_to_string_not_empty = Q.prove (
`!n. num_to_string n "" ≠ ""`,
cheat);

val int_to_string_to_int_help = Q.prove (
`!n. string_to_int (num_to_string n "") =
     &string_to_num (REVERSE (num_to_string n ""))`,
rw [] >>
cases_on `num_to_string n ""` >>
rw [string_to_int_def] >>
cases_on `h = #"~"` >>
rw [] >>
MP_TAC (Q.SPEC `n` num_to_string_digits) >>
rw []);

val int_to_string_to_int = Q.prove (
`!i. string_to_int (int_to_string i) = i`,
rw [string_to_int_def, int_to_string_def, string_to_num_def,
   int_to_string_to_int_help] >|
[`0 ≤ i` by COOPER_TAC >>
     metis_tac [REVERSE_APPEND, num_to_string_to_num, integerTheory.INT_OF_NUM],
 MP_TAC (Q.SPEC `Num (-i)` num_to_string_to_num) >>
     rw [] >>
     COOPER_TAC]);

val spaces_eqns = Q.prove (
`(!s. spaces 0 s = s) ∧
 (!s n. spaces (SUC n) s = " " ++ spaces n s)`,
CONJ_TAC >-
rw [Once spaces_def] >>
rw [Once spaces_def]);

val is_MiniML_tok_def = Define `
(is_MiniML_tok NewlineT = T) ∧
(is_MiniML_tok (WhitespaceT n) = n > 0) ∧
(is_MiniML_tok (IntT i) = T) ∧
(* TODO: The lazy way out on ids for now *)
(is_MiniML_tok (LongidT id) =
  regexp_matches longid id) ∧
(* TODO: I'm concerned that the SML spec allows empty tyvars *)
(is_MiniML_tok (TyvarT tv) =
  EVERY (\c. MEM c
          "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'")
    tv) ∧
(is_MiniML_tok AndT = T) ∧
(is_MiniML_tok AndalsoT = T) ∧
(is_MiniML_tok CaseT = T) ∧
(is_MiniML_tok DatatypeT = T) ∧
(is_MiniML_tok ElseT = T) ∧
(is_MiniML_tok EndT = T) ∧
(is_MiniML_tok FnT = T) ∧
(is_MiniML_tok IfT = T) ∧
(is_MiniML_tok InT = T) ∧
(is_MiniML_tok LetT = T) ∧
(is_MiniML_tok OfT = T) ∧
(is_MiniML_tok OpT = T) ∧
(is_MiniML_tok OrelseT = T) ∧
(is_MiniML_tok RecT = T) ∧
(is_MiniML_tok ThenT = T) ∧
(is_MiniML_tok ValT = T) ∧
(is_MiniML_tok LparT = T) ∧
(is_MiniML_tok RparT = T) ∧
(is_MiniML_tok CommaT = T) ∧
(is_MiniML_tok SemicolonT = T) ∧
(is_MiniML_tok BarT = T) ∧
(is_MiniML_tok EqualsT = T) ∧
(is_MiniML_tok DarrowT = T) ∧
(is_MiniML_tok ArrowT = T) ∧
(is_MiniML_tok StarT = T) ∧
(is_MiniML_tok TypeT = T) ∧
(is_MiniML_tok WithT = T) ∧
(is_MiniML_tok _ = F)`;

(*
val tok_to_lexeme_def = Define `
(tok_to_lexeme NewlineT = "\n") ∧
(tok_to_lexeme (WhitespaceT n) = spaces n "") ∧
(tok_to_lexeme (IntT i) = int_to_string i) ∧
(tok_to_lexeme (LongidT id) = id) ∧
(tok_to_lexeme (TyvarT tv) = "'" ++ tv) ∧
(tok_to_lexeme AndT = "and") ∧
(tok_to_lexeme AndalsoT = "andalso") ∧
(tok_to_lexeme CaseT = "case") ∧
(tok_to_lexeme DatatypeT = "datatype") ∧
(tok_to_lexeme ElseT = "else") ∧
(tok_to_lexeme EndT = "end") ∧
(tok_to_lexeme FnT = "fn") ∧
(tok_to_lexeme IfT = "if") ∧
(tok_to_lexeme InT = "in") ∧
(tok_to_lexeme LetT = "let") ∧
(tok_to_lexeme OfT = "of") ∧
(tok_to_lexeme OpT = "op") ∧
(tok_to_lexeme OrelseT = "orelse") ∧
(tok_to_lexeme RecT = "rec") ∧
(tok_to_lexeme ThenT = "then") ∧
(tok_to_lexeme ValT = "val") ∧
(tok_to_lexeme LparT = "(") ∧
(tok_to_lexeme RparT = ")") ∧
(tok_to_lexeme CommaT = ",") ∧
(tok_to_lexeme SemicolonT = ";") ∧
(tok_to_lexeme BarT = "|") ∧
(tok_to_lexeme EqualsT = "=") ∧
(tok_to_lexeme DarrowT = "=>") ∧
(tok_to_lexeme ArrowT = "->") ∧
(tok_to_lexeme StarT = "*") ∧
(tok_to_lexeme TypeT = "type") ∧
(tok_to_lexeme WithT = "with")`;
*)

val concat_map_string_help = Q.prove (
`!s. CONCAT (MAP (\x. [x]) s) = s`,
induct_on `s` >>
rw []);

val decint_regexp = Q.prove (
`!i. regexp_matches decint (int_to_string i)`,
rw [regexp_matches_def, decint_def, posdecint_def, negdecint_def,
    digit_def, int_to_string_def] >|
[qexists_tac `["0"]` >>
     rw [],
 DISJ1_TAC >>
     qexists_tac `MAP (\x. [x]) (num_to_string (Num i) "")` >>
     rw [num_to_string_not_empty, EVERY_MAP] >>
     metis_tac [num_to_string_digits, concat_map_string_help],
 DISJ2_TAC >>
     qexists_tac `MAP (\x. [x]) (num_to_string (Num (-i)) "")` >>
     rw [num_to_string_not_empty, EVERY_MAP] >>
     metis_tac [num_to_string_digits, concat_map_string_help]]);

val longid_not_empty = Q.prove (
`!id. regexp_matches longid id ⇒ id ≠ ""`,
rw [longid_def, id_def, regexp_matches_def, symbol_def,
    symbolicid_def, alphanumid_def, letter_def, digit_def] >>
rw [] >>
cases_on `ss'` >>
fs [])

val add_one_ws = Q.prove (
`∀toks. ∃n.
  STRING #" " (tok_list_to_string toks) =
  spaces n (tok_list_to_string toks)`,
rw [] >>
qexists_tac `1` >>
rw [tok_list_to_string_def, tok_to_string_def] >>
rw [Once spaces_def, spaces_eqns]);

val space_append_ws = Q.prove (
`!toks s.
  ?n.
    space_append s (tok_list_to_string toks) =
    s ++ spaces n (tok_list_to_string toks)`,
rw [space_append_def, LET_THM] >|
[all_tac,
 all_tac,
 all_tac,
 all_tac,
 metis_tac [spaces_eqns, add_one_ws]] >>
rw [tok_list_to_string_def, tok_to_string_def] >>
metis_tac [spaces_eqns]);

val remove_ws_toks_def = Define `
remove_ws_toks toks =
  FILTER (\tok. (tok ≠ NewlineT) ∧ (!n. tok ≠ WhitespaceT n)) toks`;

val is_space_def = Define `
is_space c = MEM c [#" "; #"\t"; #"\v"; #"\f"; #"\r"]`;

val lem =
METIS_PROVE [lex_spec_to_dfa_correct, lexer_correct, lexer_eval_thm,
             lexer_versions_thm, APPEND]
``!toks'.
    correct_lex SML_lex_spec x toks' =
    (lexer_eval (lex_spec_transition, lex_spec_finals, SML_lex_spec)
           x = SOME toks')``;

val spaces_1 = Q.prove (
`!s. STRING #" " s = spaces 1 s`,
EVAL_TAC >>
rw []);

local open computeLib in
val _ = set_skip the_compset ``eval_option_case`` (SOME 1);
val _ = set_skip the_compset ``eval_let`` (SOME 1);
val _ = set_skip the_compset ``COND`` (SOME 1);
val _ = set_skip the_compset ``$\/`` NONE;
val _ = set_skip the_compset ``$/\`` (SOME 1);
val _ = add_funs [IN_LIST_TO_SET];
fun find_app_conv const conv tm =
  if is_comb tm then
    if same_const (fst (strip_comb tm)) const then
      conv tm
    else
      NO_CONV tm
  else
    NO_CONV tm;
val lex_one_tac =
CONV_TAC
(DEPTH_CONV
  (find_app_conv
    ``lexer_eval``
    (ONCE_REWRITE_CONV [lexer_eval_def]
     THENC
     ONCE_DEPTH_CONV (find_app_conv ``lexer_get_token_eval`` EVAL_CONV)
     THENC
     SIMP_CONV (srw_ss()) [eval_option_case_def])))
end;

val initial_ws = Q.prove (
`!c s toks.
  correct_lex SML_lex_spec (STRING c s) toks ∧
  is_space c
  ⇒
  (?n toks'. toks = WhitespaceT n::toks')`,
cheat);

val initial_ws2 = Q.prove (
`!s n toks.
  correct_lex SML_lex_spec s (WhitespaceT n::toks)
  ⇒
  correct_lex SML_lex_spec (#" "::s) (WhitespaceT (n+1)::toks)`,
cheat);

val prefix_one_space = Q.prove (
`!s toks.
  correct_lex SML_lex_spec s toks
  ⇒
  ?toks'.
    (correct_lex SML_lex_spec (STRING #" " s) toks') ∧
    (remove_ws_toks toks = remove_ws_toks toks')`,
rw [lem] >>
`(s = "") ∨ (?c s'. (s = c::s') ∧ ¬is_space c) ∨ (?c s'. (s = c::s') ∧ is_space c)`
             by (Cases_on `s` >>
                 rw []) >>
rw [] >|
[pop_assum mp_tac >>
     lex_one_tac >>
     rw [] >>
     qexists_tac `[WhitespaceT 1]` >>
     rw [remove_ws_toks_def] >>
     lex_one_tac >>
     rw [eval_option_case_def],
 lex_one_tac >>
     rw [] >>
     fs [] >|
     [qexists_tac `WhitespaceT 1::toks` >>
          rw [remove_ws_toks_def, eval_option_case_def],
      fs [regexp_smart_constructors_def] >>
          full_case_tac >>
          fs [] >>
          cases_on `c` >>
          fs [is_space_def],
      cases_on `c` >>
          fs [is_space_def],
      cases_on `c` >>
          fs [is_space_def],
      cases_on `c` >>
          fs [is_space_def],
      cases_on `c` >>
          fs [is_space_def],
      cases_on `c` >>
          fs [is_space_def],
      fs [regexp_smart_constructors_def]],
 imp_res_tac initial_ws >>
     fs [lem] >>
     res_tac >>
     rw [remove_ws_toks_def] >>
     qexists_tac `WhitespaceT (n+1)::toks'` >>
     rw [] >>
     match_mp_tac (SIMP_RULE (srw_ss()) [lem] initial_ws2) >>
     rw []]);

val prefix_n_spaces = Q.prove (
`!n s toks.
  correct_lex SML_lex_spec s toks
  ⇒
  ?toks'.
    (correct_lex SML_lex_spec (spaces n s) toks') ∧
    (remove_ws_toks toks = remove_ws_toks toks')`,
Induct_on `n` >>
fs [spaces_eqns] >>
metis_tac [prefix_one_space]);

val space_append_correct = Q.prove (
`!s1 toks1 s2 toks2.
  correct_lex SML_lex_spec s1 toks1 ∧
  correct_lex SML_lex_spec s2 toks2
  ⇒
  ?toks'.
    correct_lex SML_lex_spec (space_append s1 s2) toks' ∧
    (remove_ws_toks (toks1++toks2) = remove_ws_toks toks')`,
cheat);

val lex_int = Q.prove (
`!i. correct_lex SML_lex_spec (int_to_string i) [IntT i]`,
rw [correct_lex_thm] >>
qexists_tac `int_to_string i` >>
rw [lexer_spec_matches_prefix_def] >>
qexists_tac `64` >>
rw [SML_lex_spec_def] >>
rw [int_to_string_to_int, decint_regexp] >|
[rw [int_to_string_def, num_to_string_not_empty],
 cheat]);

val lex_tyvar = Q.prove (
`!s. 
  EVERY (\c. MEM c "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz" ∨ 
             MEM c "0123456789" ∨
             MEM c "_'") s 
 ⇒
 correct_lex SML_lex_spec (STRING #"'" s) [TyvarT s]`,
rw [correct_lex_thm] >>
qexists_tac `STRING #"'" s` >>
rw [lexer_spec_matches_prefix_def] >>
qexists_tac `71` >>
rw [SML_lex_spec_def] >|
[rw [regexp_matches_def, tyvar_def, letter_def, digit_def] >>
     qexists_tac `MAP (\x. [x]) s` >>
     fs [EVERY_MAP, EVERY_EL] >>
     metis_tac [concat_map_string_help],
 cheat]);

val lex_ident = Q.prove (
`!s. regexp_matches longid s ⇒ correct_lex SML_lex_spec s [LongidT s]`,
rw [correct_lex_thm] >>
qexists_tac `s` >>
rw [lexer_spec_matches_prefix_def] >>
qexists_tac `74` >>
rw [SML_lex_spec_def, longid_not_empty] >>
cheat);


local

val tac = 
imp_res_tac (Q.SPEC `1` (SIMP_RULE (srw_ss()) [lem] prefix_n_spaces)) >>
rw [eval_option_case_def] >>
fs [remove_ws_toks_def] >>
metis_tac [];

in

val correct_tok_list_to_string = Q.store_thm ("correct_tok_list_to_string",
`!toks.
  EVERY is_MiniML_tok toks ⇒
  ?toks'.
    correct_lex SML_lex_spec (tok_list_to_string toks) toks' ∧
    (remove_ws_toks toks = remove_ws_toks toks')`,
Induct >>
rw [tok_list_to_string_def, correct_lex_def] >-
(qexists_tac `[]` >>
     rw [remove_ws_toks_def, correct_lex_def] >>
     metis_tac [FILTER]) >>
fs [lem] >>
cases_on `h` >>
fs [is_MiniML_tok_def, remove_ws_toks_def, tok_to_string_def] >>
lex_one_tac >>
rw [spaces_1] >|
[imp_res_tac (Q.SPEC `n` (SIMP_RULE (srw_ss()) [lem] prefix_n_spaces)) >>
     rw [eval_option_case_def] >>
     fs [remove_ws_toks_def] >>
     metis_tac [],
 cheat,
 qexists_tac `LparT::toks'` >>
     rw [] >>
     fs [] >>
     lex_one_tac >>
     rw [eval_option_case_def],
 lex_one_tac >>
     rw [spaces_1] >>
     tac,
 cheat,
 `correct_lex SML_lex_spec ")" [RparT]` 
         by (rw [lem] >>
             lex_one_tac >>
             lex_one_tac >>
             rw [eval_option_case_def]) >>
     fs [lem] >>
     imp_res_tac (SIMP_RULE (srw_ss()) [lem] space_append_correct) >>
     fs [remove_ws_toks_def],
 tac,
 tac,
 tac,
 cheat,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 tac,
 `correct_lex SML_lex_spec (int_to_string i) [IntT i]` 
         by (metis_tac [lex_int]) >>
     fs [lem] >>
     imp_res_tac (SIMP_RULE (srw_ss()) [lem] space_append_correct) >>
     fs [remove_ws_toks_def],
 `correct_lex SML_lex_spec (STRING #"'" s) [TyvarT s]` 
         by (match_mp_tac lex_tyvar >>
             fs [EVERY_MEM] >>
             rw [] >>
             metis_tac []) >>
     fs [lem] >>
     imp_res_tac (SIMP_RULE (srw_ss()) [lem] space_append_correct) >>
     fs [remove_ws_toks_def],
 `correct_lex SML_lex_spec s [LongidT s]` 
         by (metis_tac [lex_ident]) >>
     fs [lem] >>
     imp_res_tac (SIMP_RULE (srw_ss()) [lem] space_append_correct) >>
     fs [remove_ws_toks_def]]);

end;

val _ = export_theory ();
