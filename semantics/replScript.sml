open preamble;
open ASCIInumbersTheory;
open bigStepTheory typeSystemTheory astTheory lexer_funTheory;
open gramTheory cmlPtreeConversionTheory printTheory initialProgramTheory;

val _ = new_theory "repl";

val _ = Hol_datatype `
repl_result =
    Terminate
  | Diverge
  | Result of string => repl_result`;

val _ = hide"state";

val update_repl_state_def = Define `
update_repl_state ast state tdecs tenvT tenvM tenvC tenv store envC r =
  case r of
    | Rval (envM,envE) =>
        <| tdecs := tdecs;
           tenvT := merge_mod_env tenvT state.tenvT;
           tenvM := FUNION tenvM state.tenvM;
           tenvC := merge_alist_mod_env tenvC state.tenvC;
           tenv := bind_var_list2 tenv state.tenv;
           sem_env := <| sem_store := store;
                         sem_envM := envM ++ state.sem_env.sem_envM;
                         sem_envC := merge_alist_mod_env envC state.sem_env.sem_envC;
                         sem_envE := envE ++ state.sem_env.sem_envE |> |>
    | Rerr _ =>
        (* We need to record the attempted module names (if any), so that it
        * can't be defined later.  To avoid the situation where a failing module
        * defines some datatype constructors and puts them into the store before
        * failing. *)
        state with <| sem_env := state.sem_env with sem_store := store;
                      tdecs := tdecs |>`;

val (ast_repl_rules, ast_repl_ind, ast_repl_cases) = Hol_reln `

(!state.
  ast_repl state [] Terminate) ∧

(!state asts top rest tdecs' tenvT' tenvM' tenvC' tenv' store' envC' r.
  (type_top T state.tdecs state.tenvT state.tenvM state.tenvC state.tenv top tdecs' tenvT' tenvM' tenvC' tenv') ∧
  evaluate_top F <| m := state.sem_env.sem_envM; c := state.sem_env.sem_envC; v := state.sem_env.sem_envE |> state.sem_env.sem_store top (store',envC',r) ∧
  ast_repl (update_repl_state top state (union_decls tdecs' state.tdecs) tenvT' tenvM' tenvC' tenv' store' envC' r) asts rest
  ⇒
  ast_repl state (SOME top::asts) (Result (print_result tenv' top r) rest)) ∧

(!state asts top tdecs' tenvT' tenvM' tenvC' tenv'.
  (type_top T state.tdecs state.tenvT state.tenvM state.tenvC state.tenv top tdecs' tenvT' tenvM' tenvC' tenv') ∧
  top_diverges <| m := state.sem_env.sem_envM; c := state.sem_env.sem_envC; v := state.sem_env.sem_envE |> (remove_count state.sem_env.sem_store) top
  ⇒
  ast_repl state (SOME top::asts) Diverge) ∧

(!state asts rest.
  ast_repl state asts rest ∧
  (¬∃tdecs' tenvT' tenvM' tenvC' tenv'.
    type_top T state.tdecs state.tenvT state.tenvM state.tenvC state.tenv top tdecs' tenvT' tenvM' tenvC' tenv')
  ⇒
  ast_repl state (SOME top::asts) (Result "<type error>\n" rest)) ∧

(!state asts rest.
  ast_repl state asts rest
  ⇒
  ast_repl state (NONE::asts) (Result "<parse error>\n" rest))`;

val parse_def = Define`
  parse toks =
    case some pt. valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nREPLTop) ∧
                  ptree_fringe pt = MAP TOK toks
    of
       NONE => NONE
     | SOME p => ptree_REPLTop p
`

val repl_def = Define `
repl init_repl_state input = ast_repl init_repl_state (MAP parse (split_top_level_semi (lexer_fun input)))`;

val _ = export_theory ();
