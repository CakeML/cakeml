open preamble;
open listTheory rich_listTheory intLib;
open Print_astTheory Print_astTerminationTheory SMLlexTheory lexer_specTheory;
open regexpTheory;

val splitp_unsplit = Q.prove (
`!P l l1 l2. FST (SPLITP P l) ++ SND (SPLITP P l) = l`,
Induct_on `l` >>
rw [SPLITP]);

val splitp_fst_every = Q.prove (
`!P l. EVERY ($~ o P) (FST (SPLITP P l))`,
Induct_on `l` >>
rw [SPLITP]);

val splitp_snd_prop = Q.prove (
`!P (x:char) l l'. (SND (SPLITP P l) = x::l') ⇒ P x`,
Induct_on `l` >>
rw [SPLITP] >>
metis_tac []);

val concat_append = Q.prove (
`!x y. CONCAT (x ++ y) = CONCAT x ++ CONCAT y`,
Induct_on `x` >>
rw []);

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

val spaces_append = Q.prove (
`!n s. spaces n s = spaces n "" ++ s`,
recInduct spaces_ind >>
rw [] >>
cases_on `n` >>
rw [spaces_eqns]);

val spaces_len = Q.prove (
`!n s. STRLEN (spaces n s) = n + STRLEN s`,
recInduct spaces_ind >>
rw [] >>
cases_on `n` >>
rw [spaces_eqns] >>
DECIDE_TAC);

val spaces_has_spaces = Q.prove (
`!n. EVERY (λx. MEM x " ") (spaces n "")`,
cheat);

val spaces_not_empty = Q.prove (
`!n. n > 0 ⇒ spaces n "" ≠ ""`,
rw [] >>
CCONTR_TAC >>
fs [] >>
`STRLEN (spaces n "") = STRLEN ""` by metis_tac []>>
fs [spaces_len]);

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

val can_lex_one_token = Q.prove (
`!tok toks.
  is_MiniML_tok tok ⇒
  ?n ws. 
    lexer_spec_matches_prefix SML_lex_spec n tok (tok_to_lexeme tok) 
      (spaces ws (tok_list_to_string toks)) (tok_list_to_string (tok::toks))`,
cases_on `tok` >>
rw [tok_to_string_def, is_MiniML_tok_def, lexer_spec_matches_prefix_def,
    tok_to_lexeme_def] >|
[qexists_tac `1`,
 qexists_tac `0`,
 qexists_tac `3`,
 qexists_tac `4`,
 qexists_tac `5`,
 qexists_tac `6`,
 qexists_tac `7`,
 qexists_tac `11`,
 qexists_tac `12`,
 qexists_tac `13`,
 qexists_tac `18`,
 qexists_tac `21`,
 qexists_tac `22`,
 qexists_tac `24`,
 qexists_tac `25`,
 qexists_tac `27`,
 qexists_tac `28`,
 qexists_tac `31`,
 qexists_tac `35`,
 qexists_tac `36`,
 qexists_tac `40`,
 qexists_tac `43`,
 qexists_tac `44`,
 qexists_tac `46`,
 qexists_tac `48`,
 qexists_tac `54`,
 qexists_tac `55`,
 qexists_tac `56`,
 qexists_tac `59`,
 qexists_tac `64`,
 qexists_tac `71`,
 qexists_tac `74`] >>
rw [SML_lex_spec_def, regexp_matches_def, tok_list_to_string_def,
    tok_to_string_def] >|
[qexists_tac `0` >>
     rw [spaces_len] >|
     [qexists_tac `MAP (\x. [x]) (spaces n "")` >>
          rw [EVERY_MAP] >|
          [metis_tac [spaces_not_empty],
           ASSUME_TAC (Q.SPEC `n` spaces_has_spaces) >>
               fs [EVERY_EL] >>
               metis_tac [],
           metis_tac [concat_map_string_help]],
      metis_tac [spaces_eqns, spaces_append]],
 metis_tac [spaces_eqns],
 metis_tac [spaces_eqns],
 metis_tac [add_one_ws],
 metis_tac [spaces_eqns],
 metis_tac [space_append_ws, STRCAT_def],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [spaces_eqns],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 metis_tac [add_one_ws],
 rw [int_to_string_to_int, decint_regexp] >>
     metis_tac [space_append_ws, STRCAT_def],
 rw [regexp_matches_def, tyvar_def, letter_def, digit_def] >>
     ASSUME_TAC (Q.SPECL [`toks`, `"'" ++ s`] space_append_ws) >>
     rw [] >>
     fs [] >>
     qexists_tac `n` >>
     rw [] >>
     qexists_tac `MAP (\x. [x]) s` >>
     fs [EVERY_MAP, EVERY_EL] >>
     metis_tac [concat_map_string_help],
 metis_tac [space_append_ws, STRCAT_def]]);

val is_space_def = Define `
is_space c = MEM c [#" "; #"\t"; #"\v"; #"\f"; #"\r"]`;

val splitp_spaces_notempty = Q.prove (
`!n s.  (n ≠ 0) ⇒ (FST (SPLITP (\c. ¬is_space c) (spaces n s)) ≠ "")`,
cases_on `n` >>
rw [SPLITP, spaces_eqns, is_space_def]);

val splitp_spaces = Q.prove (
`!n s. 
  SPLITP (\c. ¬is_space c) (spaces n s) 
  =
  (spaces n "" ++ FST (SPLITP (\c. ¬is_space c) s), SND (SPLITP (\c. ¬is_space c) s))`,
Induct_on `n` >>
rw [is_space_def, spaces_eqns,SPLITP] >>
fs [is_space_def]);

val helper_regexp_eqns = Q.prove (
`!s r rs.
  (deriv_matches (Or rs) s = EXISTS (\r. deriv_matches r s) rs)`,
metis_tac [regexp_matches_def, regexp_matches_deriv]);

val matches_init_space = Q.prove (
`!s r f.
  MEM (r,f) SML_lex_spec ∧
  regexp_matches r s ∧
  (?c s'. (s = c::s') ∧ is_space c)
  ⇒
  ((r,f) = EL 1 SML_lex_spec)`,
rw [] >>
qpat_assum `MEM (r,f) SML_lex_spec`
     (STRIP_ASSUME_TAC o 
      SIMP_RULE(srw_ss()) [SML_lex_spec_def, all_SML_regexps]) >>
fs [is_space_def] >>
rw [] >>
fs [regexp_matches_deriv, deriv_matches_def, deriv_def, nullable_def,
    deriv_matches_eqns, LET_THM, helper_regexp_eqns] >>
rw [SML_lex_spec_def]);

val lex_init_ws = Q.prove (
`∀n s toks. 
  let (s1,s2) = SPLITP (λc. ¬is_space c) (spaces n s) in
    (s1 ≠ "") ∧
    correct_lex SML_lex_spec s2 toks
    ⇒
    ∃n'. correct_lex SML_lex_spec (spaces n s) (WhitespaceT (STRLEN s1)::toks)`,
rw [correct_lex_thm] >>
qexists_tac `s1` >>
qexists_tac `1` >>
qexists_tac `s2` >>
rw [] >|
[
rw [lexer_spec_matches_prefix_def, SML_lex_spec_def, regexp_matches_def] >>
     fs [splitp_spaces] >>
     rw [] >|
     [qexists_tac `MAP (λc. [c]) (spaces n "" ++ FST (SPLITP (λc. ¬is_space c) s))` >>
          rw [EVERY_MAP] >|
          [`EVERY (λc. MEM c " ") (spaces n "")` by metis_tac [spaces_has_spaces] >>
               fs [EVERY_EL],
           `EVERY ($~ o (\c. ~is_space c)) (FST (SPLITP (\c. ~is_space c) s))`
                        by metis_tac [splitp_fst_every] >>
               fs [EVERY_EL, is_space_def],
           rw [concat_map_string_help, concat_append]],
      metis_tac [splitp_unsplit, spaces_append, APPEND_ASSOC]],
 CCONTR_TAC >>
     fs [lexer_spec_matches_prefix_alt_def] >>
     rw [] >>
     `EVERY ($~ o (\c. ~is_space c)) s1` by metis_tac [splitp_fst_every, FST] >>
     `?c lexeme. lexeme' = c::lexeme` 
             by (cases_on `lexeme'` >>
                 fs []) >>
     rw [] >>
     fs [] >>
     `?l l'. (SND (SPLITP (λc. ¬is_space c) l) = STRING c l')`
               by metis_tac [SND] >>
     imp_res_tac splitp_snd_prop >>
     fs [] >>
     `(r,f) = EL 1 SML_lex_spec` 
                by (cases_on `s1` >>
                    fs [] >>
                    metis_tac [matches_init_space, APPEND]) >>
     pop_assum (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [SML_lex_spec_def]) >>
     fs [] >>
     rw [] >>
     fs [regexp_matches_def] >>
     `MEM c (CONCAT ss)` by metis_tac [MEM_FLAT, MEM_APPEND, MEM] >>
     fs [EVERY_MEM, MEM_FLAT] >>
     res_tac >>
     rw [] >>
     fs [is_space_def],
 REWRITE_TAC [SML_lex_spec_def, TAKE_compute, TAKE, DECIDE ``1-1=0:num``] >>
     rw [lexer_spec_matches_prefix_alt_def] >>
     CCONTR_TAC >>
     fs [regexp_matches_def] >>
     rw [] >>
     cases_on `n` >>
     fs [spaces_eqns, SPLITP, is_space_def]]);

     (*
`!s toks n. 
  correct_lex SML_lex_spec s toks ⇒
  ?toks'.
    correct_lex SML_lex_spec (spaces n s) toks' ∧
    (remove_ws_toks toks = remove_ws_toks toks')`

STRIP_TAC >>
completeInduct_on `LENGTH s` >>
rw [] >>
cases_on `n = 0` >>
fs [spaces_eqns] >-
metis_tac [] >>
cases_on `STRLEN (SND (SPLITP (λc. ¬is_space c) s)) < STRLEN s` >>
res_tac >>
fs [] >|
[POP_ASSUM (ASSUME_TAC o Q.SPEC `(SND (SPLITP (λc. ¬is_space c) s))`) >>
     rw [] >>

     all_tac,
 qexists_tac `WhitespaceT n::toks` >>
     rw [correct_lex_def, remove_ws_toks_def] >>
     qexists_tac `spaces n ""` >>
     qexists_tac `1` >>
     qexists_tac `s` >>
     rw [lexer_spec_matches_prefix_def, spaces_not_empty] >>
     rw [SML_lex_spec_def] >>
     all_tac]





qexists_tac `WhitespaceT (n + LENGTH (FST (SPLITP (\c. ¬is_space c) s))) :: 

`?s1 s2. (s1,s2) = SPLITP (\c. ¬is_space c) (spaces n s)` 
              by metis_tac [PAIR] >>
fs [splitp_spaces] >>
fs []

`s1 ≠ ""` by metis_tac [splitp_spaces_notempty, FST] >>
`spaces n s = s1 ++ s2` by metis_tac [splitp_unsplit, FST, SND] >>
rw [] >>
`LENGTH s2 < LENGTH s` 
        by 
          
         
 qexists_tac `WhitespaceT n::toks` >>
     rw [remove_ws_toks_def, correct_lex_def] >>
     `n > 0` by DECIDE_TAC >>
     qexists_tac `spaces n ""` >>
     qexists_tac `1` >>
     rw [lexer_spec_matches_prefix_def, spaces_not_empty,
         SML_lex_spec_def] >>
     all_tac]



`!toks. 
  EVERY is_MiniML_tok toks ⇒
  ?toks'. 
    correct_lex SML_lex_spec (tok_list_to_string toks) toks' ∧
    (remove_ws_toks toks = remove_ws_toks toks')`

Induct >>
rw [tok_list_to_string_def, correct_lex_def] >-
(qexists_tac `[]` >>
     rw [remove_ws_toks_def, correct_lex_def] >>
     metis_tac [FILTER]) >>
fs [] >>
`?n ws.
   lexer_spec_matches_prefix SML_lex_spec n h (tok_to_lexeme h)
            (spaces ws (tok_list_to_string toks))
            (tok_list_to_string (h::toks))`
        by metis_tac [can_lex_one_token] >>


lex_init_ws




qexists_tac `h::WhitespaceT ws::toks'` >>
rw [] >|
[rw [correct_lex_def] >>
     qexists_tac `tok_to_lexeme h` >>
     qexists_tac `n` >>
     qexists_tac `tok_list_to_string (WhitespaceT ws :: toks)` >> 
     rw [] >|
     [cases_on `h` >>
          fs [is_MiniML_tok_def] >>
          rw [tok_to_lexeme_def, int_to_string_def, spaces_not_empty,
              num_to_string_not_empty, longid_not_empty],
      fs [tok_list_to_string_def],
      all_tac,
      all_tac,
      all_tac],
 cases_on `h` >>
     fs [is_MiniML_tok_def, remove_ws_toks_def]]
  


qexists_tac `tok_to_string h ""` >>
qexists_tac `number` >>
qexists_tac `tok_list_to_string toks` >>
rw []
*)

val _ = export_theory ();
