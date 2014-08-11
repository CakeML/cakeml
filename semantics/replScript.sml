open preamble;
open ASCIInumbersTheory;
open bigStepTheory typeSystemTheory astTheory lexer_funTheory;
open gramTheory cmlPtreeConversionTheory initialProgramTheory;

val _ = new_theory "repl";

val _ = Hol_datatype `
repl_state = <| (* Type system state *)
                tdecs : decls; tenvT : tenvT; tenvM : tenvM; tenvC : tenvC; tenv : tenvE;
                (* Semantics state *)
                sem_env : sem_environment |>`;

val _ = Hol_datatype `
repl_result =
    Terminate
  | Diverge
  | Result of string => repl_result`;

val update_repl_state_def = Define `
update_repl_state ast state tdecs tenvT tenvM tenvC tenv store envC r =
  case r of
    | Rval (envM,envE) =>
        <| tdecs := tdecs;
           tenvT := merge_tenvT tenvT state.tenvT;
           tenvM := tenvM ++ state.tenvM;
           tenvC := merge_tenvC tenvC state.tenvC;
           tenv := bind_var_list2 tenv state.tenv;
           sem_env := <| sem_store := store;
                         sem_envM := envM ++ state.sem_env.sem_envM;
                         sem_envC := merge_envC envC state.sem_env.sem_envC;
                         sem_envE := envE ++ state.sem_env.sem_envE |> |>
    | Rerr _ =>
        (* We need to record the attempted module names (if any), so that it
        * can't be defined later.  To avoid the situation where a failing module
        * defines some datatype constructors and puts them into the store before
        * failing. *)
        state with <| sem_env := state.sem_env with sem_store := store;
                      tdecs := tdecs |>`;

val type_to_string_def = tDefine "type_to_string" `
(type_to_string (Tvar tvn) ⇔ tvn) ∧
(type_to_string (Tvar_db n) ⇔ num_to_dec_string n) ∧
(type_to_string (Tapp [t1;t2] TC_fn) ⇔
  "(" ++ type_to_string t1 ++ "->" ++ type_to_string t2 ++ ")") ∧
(type_to_string (Tapp ts TC_fn) ⇔ "<bad function type>") ∧
(type_to_string (Tapp ts TC_tup) ⇔
  "(" ++ types_to_string ts ++ ")") ∧
(type_to_string (Tapp [] tc) ⇔ tc_to_string tc) ∧
(type_to_string (Tapp ts tc) ⇔
  "(" ++ types_to_string ts ++ ") " ++ tc_to_string tc) ∧
(types_to_string [] ⇔ "") ∧
(types_to_string [t] ⇔ type_to_string t) ∧
(types_to_string (t::ts) ⇔ type_to_string t ++ ", " ++ types_to_string ts)`
(wf_rel_tac `measure (\x. case x of INL x => t_size x | INR x => t1_size x)`);

val print_envM_def = Define `
print_envM envM = CONCAT (MAP (λ(x,m). "module " ++ x ++ " = <structure>\n") envM)`;

val print_envC_def = Define `
print_envC (menvC,envC) = CONCAT (MAP (λ(x,c). x ++ " = <constructor>\n") envC)`;

val print_lit_def = Define `
(print_lit (IntLit i) = int_to_string i) ∧
(print_lit (StrLit s) = string_to_string s) ∧
(print_lit (Word8 w) = "0wx"++(word_to_hex_string w)) ∧
(print_lit (Bool T) = "true") ∧
(print_lit (Bool F) = "false") ∧
(print_lit Unit = "()")`;

val print_v_def = Define `
(print_v (Litv l) = print_lit l) ∧
(print_v (Conv _ _) = "<constructor>") ∧
(print_v (Vectorv _) = "<vector>") ∧
(print_v (Closure _ _ _) = "<fn>") ∧
(print_v (Recclosure _ _ _) = "<fn>") ∧
(print_v (Loc _) = "<ref>")`;

val print_envE_def = Define `
(print_envE [] [] = "") ∧
(print_envE ((x', (n,t))::types) ((x,v)::envE) = 
  "val " ++ x ++ ":" ++ type_to_string t ++ " = " ++ print_v v ++ "\n" ++ print_envE types envE)`;

val print_result_def = Define `
(print_result types (Tdec _) envC (Rval (envM,envE)) = print_envC envC ++ print_envE types envE) ∧
(print_result _ (Tmod mn _ _) _ (Rval _) = "structure "++mn++" = <structure>\n") ∧
(print_result _ _ _ (Rerr Rtimeout_error) = "<timeout error>\n") ∧
(print_result _ _ _ (Rerr Rtype_error) = "<type error>\n") ∧
(print_result _ _ _ (Rerr (Rraise e)) = "raise " ++ print_v e ++ "\n")`;

val tenv_to_string_map_def = Define `
(tenv_to_string_map [] ⇔ FEMPTY) ∧
(tenv_to_string_map ((x, (_, t)) :: tenv) ⇔
  tenv_to_string_map tenv |+ (x, type_to_string t))`;

val remove_count_def = Define `
remove_count ((count,store),tdecls,mods) = (store,tdecls,mods)`;

val (ast_repl_rules, ast_repl_ind, ast_repl_cases) = Hol_reln `

(!state.
  ast_repl state [] [] Terminate) ∧

(!state type_errors asts top rest tdecs' tenvT' tenvM' tenvC' tenv' store' envC' r.
  (type_top state.tdecs state.tenvT state.tenvM state.tenvC state.tenv top tdecs' tenvT' tenvM' tenvC' tenv') ∧
  evaluate_top F (state.sem_env.sem_envM, state.sem_env.sem_envC, state.sem_env.sem_envE) state.sem_env.sem_store top (store',envC',r) ∧
  ast_repl (update_repl_state top state (union_decls tdecs' state.tdecs) tenvT' tenvM' tenvC' tenv' store' envC' r) type_errors asts rest
  ⇒
  ast_repl state (F::type_errors) (SOME top::asts) (Result (print_result tenv' top envC' r) rest)) ∧

(!state type_errors asts top tdecs' tenvT' tenvM' tenvC' tenv'.
  (type_top state.tdecs state.tenvT state.tenvM state.tenvC state.tenv top tdecs' tenvT' tenvM' tenvC' tenv') ∧
  top_diverges (state.sem_env.sem_envM, state.sem_env.sem_envC, state.sem_env.sem_envE) (remove_count state.sem_env.sem_store) top
  ⇒
  ast_repl state (F::type_errors) (SOME top::asts) Diverge) ∧

(!state type_errors asts rest.
  ast_repl state type_errors asts rest
  ⇒
  ast_repl state (T::type_errors) (SOME top::asts) (Result "<type error>\n" rest)) ∧

(!state x type_errors asts rest.
  ast_repl state type_errors asts rest
  ⇒
  ast_repl state (x::type_errors) (NONE::asts) (Result "<parse error>\n" rest))`;

val parse_def = Define`
  parse toks =
    case some pt. valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nREPLTop) ∧
                  ptree_fringe pt = MAP TOK toks
    of
       NONE => NONE
     | SOME p => ptree_REPLTop p
`

val repl_def = Define `
repl init_repl_state type_errors input = ast_repl init_repl_state type_errors (MAP parse (split_top_level_semi (lexer_fun input)))`;

val _ = export_theory ();
