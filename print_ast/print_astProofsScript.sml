open preamble;
open Print_astTheory Print_astTerminationTheory SMLlexTheory lexer_specTheory;

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

val is_MiniML_tok_def = Define `
(is_MiniML_tok (WhitespaceT n) = T) ∧
(is_MiniML_tok (IntT i) = T) ∧
(is_MiniML_tok (LongidT id) = T) ∧
(is_MiniML_tok (TyvarT tv) = T) ∧
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
`!tok toks. 
  is_MiniML_tok tok ⇒
  ?n. 
    lexer_spec_matches_prefix SML_lex_spec n tok (tok_to_string tok "") 
      (tok_list_to_string toks) (tok_list_to_string (tok::toks))`

cases_on `tok` >>
rw [tok_to_string_def, is_MiniML_tok_def, lexer_spec_matches_prefix_def] >|
[qexists_tac `1`,
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
 qexists_tac `32`,
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
 qexists_tac `75`] >>
rw [SML_lex_spec_def, regexp_matches_def]



val tok_to_string_nonempty = Q.prove (
`!tok s. tok_to_string tok s ≠ s`,

rw [tok_to_string_def]
cases_on `tok` >>
rw [tok_to_string_def, lexer_spec_matches_prefix_def, tok_list_to_string_def]


`!toks. correct_lex SML_lex_spec (tok_list_to_string toks) toks`

Induct >>
rw [tok_list_to_string_def, correct_lex_def] >>

qexists_tac `tok_to_string h ""` >>
qexists_tac `number` >>
qexists_tac `tok_list_to_string toks` >>
rw []
*)

val _ = export_theory ();
