open preamble;
open ASCIInumbersTheory;
open BigStepTheory TypeSystemTheory AstTheory ElabTheory lexer_funTheory;
open gramTheory;

val _ = new_theory "repl";

(* top-level semicolon detector breaks the token list up into chunks.
  the parser turns these chunks into either ast_progs or errors (NONE).
  if it encounters an error, it drops tokens until the next chunk.  *)
val _ = new_constant("parse", ``:token list -> ast_top option list``);

val _ = Hol_datatype `
repl_state = <| (* Elaborator state *)
                type_bindings : typeN list; ctors : ctor_env;
                (* Type system state *)
                tenvM : tenvM; tenvC : tenvC; tenv : tenvE;
                (* Semantics state *)
                envM : envM; envC : envC; store : store; envE : envE |>`;

val init_repl_state_def = Define`
  init_repl_state = <| type_bindings := []; ctors := [];
                       tenvM := []; tenvC := []; tenv := init_tenv;
                       envM := []; envC := []; store := []; envE := init_env |>`

val _ = Hol_datatype `
repl_result = 
    Terminate
  | Diverge
  | Result of string => repl_result`;

val update_repl_state_def = Define `
update_repl_state state type_bindings ctors tenvM tenvC tenv store r =
  case r of
    | Rval (envM,envC,envE) =>
        <| type_bindings := type_bindings ++ state.type_bindings;
           ctors := ctors ++ state.ctors;
           tenvM := tenvM ++ state.tenvM;
           tenvC := tenvC ++ state.tenvC;
           tenv := bind_var_list2 tenv state.tenv;
           store := store;
           envM := envM ++ state.envM;
           envC := envC ++ state.envC;
           envE := envE ++ state.envE |>
    | Rerr _ => 
        state with <| store := store |>`;

val print_envM_def = Define `
print_envM envM = CONCAT (MAP (λ(x,m). "module " ++ x ++ " = <structure>\n") envM)`;

val id_to_string_def = Define `
(id_to_string (Short x) = x) ∧
(id_to_string (Long x y) = x ++ "." ++ y)`;

val print_envC_def = Define `
print_envC envC = CONCAT (MAP (λ(x,c). id_to_string x ++ " = <constructor>") envC)`;

val int_to_string_def = Define `
int_to_string (i:int) =
  if i < 0 then
    "~" ++ toString (Num (0 - i))
  else
    toString (Num i)`;

val print_lit_def = Define `
(print_lit (IntLit i) = int_to_string i) ∧
(print_lit (Bool true) = "true") ∧
(print_lit (Bool false) = "false") ∧
(print_lit Unit = "()")`;

val print_v_def = Define `
(print_v (Litv l) = print_lit l) ∧
(print_v (Conv _ _) = "<constructor>") ∧
(print_v (Closure _ _ _) = "<fn>") ∧
(print_v (Recclosure _ _ _) = "<fn>") ∧
(print_v (Loc _) = "<ref>")`;

val print_envE_def = Define `
print_envE envE = CONCAT (MAP (\(x,v). "val " ++ x ++ " = " ++ print_v v ++ "\n") envE)`;

val print_error_def = Define `
(print_error Bind_error = "<Bind>") ∧
(print_error Div_error = "<Div>") ∧
(print_error (Int_error i) = "<" ++ int_to_string i ++ ">")`;

val print_result_def = Define `
(print_result (Rval (envM,envC,envE)) = 
  print_envM envM ++ print_envC envC ++ print_envE envE) ∧
(print_result (Rerr Rtype_error) = "raise <type error>\n") ∧
(print_result (Rerr (Rraise e)) = "raise " ++ print_error e ++ "\n")`;

val (ast_repl_rules, ast_repl_ind, ast_repl_cases) = Hol_reln `

(!state. 
  ast_repl state [] Terminate) ∧

(!state ast asts top rest type_bindings' ctors' tenvM' tenvC' tenv' store' r.
  (elab_top state.type_bindings state.ctors ast = 
   (type_bindings', ctors', top)) ∧
  (type_top state.tenvM state.tenvC state.tenv top tenvM' tenvC' tenv') ∧
  evaluate_top state.envM state.envC state.store state.envE top (store',r) ∧
  ast_repl (update_repl_state state type_bindings' ctors' tenvM' tenvC' tenv' store' r) asts rest
  ⇒
  ast_repl state (SOME ast::asts) (Result (print_result r) rest)) ∧

(!state ast asts top type_bindings' ctors' tenvM' tenvC' tenv'.
  (elab_top state.type_bindings state.ctors ast = 
   (type_bindings', ctors', top)) ∧
  (type_top state.tenvM state.tenvC state.tenv top tenvM' tenvC' tenv') ∧
  prog_diverges state.envM state.envC state.store state.envE [prog]
  ⇒
  ast_repl state (SOME ast::asts) Diverge) ∧

(!state ast asts rest top type_bindings' ctors'.
  (elab_top state.type_bindings state.ctors ast = 
   (type_bindings', ctors', top)) ∧
  (!tenvM' tenvC' tenv'.
    ¬type_top state.tenvM state.tenvC state.tenv top tenvM' tenvC' tenv') ∧
  ast_repl state asts rest
  ⇒
  ast_repl state (SOME ast::asts) (Result "<type error>" rest)) ∧

(!state asts rest. 
  ast_repl state asts rest
  ⇒
  ast_repl state (NONE::asts) (Result "<parse error>" rest))`;

val repl_def = Define `
repl input = ast_repl init_repl_state (parse (lexer_fun input))`;

val _ = export_theory ();
