open preamble;
open BigStepTheory TypeSystemTheory AstTheory ElabTheory lexer_funTheory;
open gramTheory;

val _ = new_theory "repl";

(* top-level semicolon detector breaks the token list up into chunks.
  the parser turns these chunks into either ast_progs or errors (NONE).
  if it encounters an error, it drops tokens until the next chunk.  *)
val _ = new_constant("parse", ``:token list -> ast_prog option list``);

val _ = new_constant("print_envM", ``:envM -> string``);
val _ = new_constant("print_envC", ``:envC -> string``);
val _ = new_constant("print_envE", ``:envE -> string``);

val _ = new_constant("print_error", ``:error -> string``);

val _ = Hol_datatype `
repl_state = <| (* Elaborator state *)
                type_bindings : typeN list; ctors : ctor_env; bindings : binding_env;
                (* Type system state *)
                tenvM : tenvM; tenvC : tenvC; tenv : tenvE;
                (* Semantics state *)
                envM : envM; envC : envC; store : store; envE : envE |>`;

val init_repl_state_def = Define`
  init_repl_state = <| type_bindings := []; ctors := []; bindings := [];
                       tenvM := []; tenvC := []; tenv := Empty;
                       envM := []; envC := []; store := []; envE := [] |>`

val _ = Hol_datatype `
repl_result = 
    Terminate
  | Diverge
  | Result of string => repl_result`;

val update_repl_state_def = Define `
update_repl_state state type_bindings ctors bindings tenvM tenvC tenv store r =
  case r of
    | Rval (envM,envC,envE) =>
        <| type_bindings := type_bindings ++ state.type_bindings;
           ctors := ctors ++ state.ctors;
           bindings := bindings ++ state.bindings;
           tenvM := tenvM ++ state.tenvM;
           tenvC := tenvC ++ state.tenvC;
           tenv := bind_var_list2 tenv state.tenv;
           store := store;
           envM := envM ++ state.envM;
           envC := envC ++ state.envC;
           envE := envE ++ state.envE |>
    | Rerr _ => 
        state with <| store := store |>`;

val print_result_def = Define `
(print_result (Rval (envM,envC,envE)) = 
  print_envM envM ++ print_envC envC ++ print_envE envE) ∧
(print_result (Rerr Rtype_error) = "<type error>") ∧
(print_result (Rerr (Rraise e)) = print_error e)`;

val (ast_repl_rules, ast_repl_ind, ast_repl_cases) = Hol_reln `

(!state. 
  ast_repl state [] Terminate) ∧

(!state ast asts prog rest type_bindings' ctors' bindings' tenvM' tenvC' tenv' store' r.
  (elab_prog state.type_bindings state.ctors state.bindings ast = 
   (type_bindings', ctors', bindings', prog)) ∧
  (type_prog state.tenvM state.tenvC state.tenv prog tenvM' tenvC' tenv') ∧
  evaluate_prog state.envM state.envC state.store state.envE prog (store',r) ∧
  ast_repl (update_repl_state state type_bindings' ctors' bindings' tenvM' tenvC' tenv' store' r) asts rest
  ⇒
  ast_repl state (SOME ast::asts) (Result (print_result r) rest)) ∧

(!state ast asts prog type_bindings' ctors' bindings' tenvM' tenvC' tenv'.
  (elab_prog state.type_bindings state.ctors state.bindings ast = 
   (type_bindings', ctors', bindings', prog)) ∧
  (type_prog state.tenvM state.tenvC state.tenv prog tenvM' tenvC' tenv') ∧
  prog_diverges state.envM state.envC state.store state.envE prog
  ⇒
  ast_repl state (SOME ast::asts) Diverge) ∧

(!state ast asts rest prog type_bindings' ctors' bindings'.
  (elab_prog state.type_bindings state.ctors state.bindings ast = 
   (type_bindings', ctors', bindings', prog)) ∧
  (!tenvM' tenvC' tenv'.
    ¬type_prog state.tenvM state.tenvC state.tenv prog tenvM' tenvC' tenv') ∧
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
