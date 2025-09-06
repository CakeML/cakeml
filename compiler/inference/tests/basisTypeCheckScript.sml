(*
  This file checks that the CakeML standard basis library passes the
  type inferencer. This file also acts as a test of cv_compute
  evaluation of the type inferencer.
*)
Theory basisTypeCheck
Ancestors
  basisProg infer_cv
Libs
  preamble cv_transLib

val _ = cv_auto_trans inferTheory.init_config_def;

val _ = cv_trans_deep_embedding EVAL basis_def;

val basis_types = cv_eval “infertype_prog init_config basis”;

val print_types = let
  val x = basis_types |> concl |> rhs
  val _ = if can (match_term ``infer$Success _``) x then () else
          if can (match_term ``infer$Failure _``) x then let
            val msg = x |> rand |> rand |> rand
            in case total stringSyntax.fromHOLstring msg of
                SOME s => failwith ("Type inference failed for basis with message: " ^ s)
              | NONE => failwith ("Type inference failed for basis. (Also failed to " ^
                                  "fully evaluate type inferencer error message)")
          end
          else failwith "Failed to fully evaluate type inferencer applied to basis."
  val _ = print "\nTypes of all basis functions:\n\n"
  val strs = EVAL (mk_comb(“inf_env_to_types_string”,rand x))
               |> concl |> rand |> listSyntax.dest_list |> fst
               |> map (stringSyntax.fromHOLstring o rand) |> map print
  val _ = print "\n"
  in () end

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
