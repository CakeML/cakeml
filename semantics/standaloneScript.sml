open HolKernel boolLib bossLib
open lexer_funTheory printTheory initialProgramTheory gramTheory cmlPtreeConversionTheory terminationTheory
val _ = new_theory"standalone"

val (ast_standalone_rules,ast_standalone_ind,ast_standalone_cases) = Hol_reln`
  (type_prog state.tdecs state.tenvT state.tenvM state.tenvC state.tenv prog tdecs' tenvT' tenvM' tenvC' tenv' ∧
   evaluate_whole_prog F (state.sem_env.sem_envM, state.sem_env.sem_envC, state.sem_env.sem_envE) state.sem_env.sem_store prog (store',envC',r)
   ⇒
   ast_standalone state F prog (SOME (print_prog_result tenv' r))) ∧
  (type_prog state.tdecs state.tenvT state.tenvM state.tenvC state.tenv prog tdecs' tenvT' tenvM' tenvC' tenv' ∧
   prog_diverges (state.sem_env.sem_envM, state.sem_env.sem_envC, state.sem_env.sem_envE) (remove_count state.sem_env.sem_store) prog
   ⇒
   ast_standalone state F prog NONE) ∧
  (ast_standalone state T prog (SOME "<type error>\n"))`

val parse_def = Define`
  parse toks =
    case some pt. valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTopLevelDecs) ∧
                  ptree_fringe pt = MAP TOK toks
    of
       NONE => NONE
     | SOME p => ptree_TopLevelDecs p`

val standalone_def = Define`
  standalone init_state type_error input =
    case parse (lexer_fun input) of
    | NONE => SOME "<parse error>\n"
    | SOME prog => OPTION_JOIN (some output. ast_standalone init_state type_error prog output)`

val _ = export_theory()
