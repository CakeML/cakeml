open preamble;
open Print_astTheory Print_astTerminationTheory;

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

val is_ocaml_infix_spec = Q.store_thm ("is_ocaml_infix_spec",
`!s.
  is_ocaml_infix s =
  MEM s ["*"; "+"; "-"; "/"; "<"; "<="; "="; ">"; ">="; "mod"]`,
rw [] >>
EQ_TAC >>
rw [is_ocaml_infix_def, LET_THM, SUB_def] >>
fs []);

val _ = export_theory ();
