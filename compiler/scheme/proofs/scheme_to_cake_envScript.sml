(*
  Defines the env and state that results from running evaluate_decs
  through the scheme-to-cake compilers init code.
*)
Theory scheme_to_cake_env
Ancestors
  scheme_ast scheme_semantics scheme_to_cake ml_prog
  scheme_semanticsProps ast evaluate evaluateProps
  semanticPrimitives namespace primTypes namespaceProps integer
Libs
  preamble computeLib ml_progLib

val _ = (max_print_depth := 30);

Definition scheme_init_def:
  scheme_init =
    [scheme_basis_types] ++ scheme_basis ++ [scheme_basis_list; scheme_basis_app]
End

local
val scheme_init_eq = EVAL “scheme_init”;
val prog_tm = scheme_init_eq |> concl |> rand;
val state = ml_progLib.add_prog prog_tm I ml_progLib.init_state;
in

Theorem evaluate_decs_scheme_init_thm =
  state |> ml_progLib.get_thm
        |> SRULE [ML_code_def,Decls_def,ML_code_env_def,GSYM scheme_init_eq] |> cj 2;

Theorem scheme_init_v_defs =
  state |> ml_progLib.get_v_defs |> rev |> LIST_CONJ;

Theorem scheme_init_env_defs =
  find "scheme_to_cake_env_env~def" |> map (fn (_,(th,_,_)) => th) |> rev |> LIST_CONJ;

end
