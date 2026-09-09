(*
  This file checks that the CakeML standard basis library passes the
  type inferencer. This file also acts as a test of cv_compute
  evaluation of the type inferencer. It writes the inferred signature to
  new_types.txt, which the Holmakefile diffs against basis/types.txt.
*)
Theory basisTypeCheck[no_sig_docs]
Ancestors
  basisProg infer_cv
Libs
  preamble cv_transLib

val _ = cv_auto_trans inferTheory.init_config_def;

val _ = cv_trans_deep_embedding EVAL basis_def;

val basis_types = cv_eval “infertype_prog init_config basis”;

val print_types = let
  val x = basis_types |> concl |> rhs
  val _ = if can (match_term ``M_success _``) x then () else
          if can (match_term ``M_failure _``) x then let
            val msg = x |> rand |> rand |> rand
            in case total stringSyntax.fromHOLstring msg of
                SOME s => failwith ("Type inference failed for basis with message: " ^ s)
              | NONE => failwith ("Type inference failed for basis. (Also failed to " ^
                                  "fully evaluate type inferencer error message)")
          end
          else failwith "Failed to fully evaluate type inferencer applied to basis."
  val strs = EVAL (mk_comb(“inf_env_to_types_string”,rand x))
               |> concl |> rand |> listSyntax.dest_list |> fst
               |> map (stringSyntax.fromHOLstring o rand)
  val _ = print "\nTypes of all basis functions:\n\n"
  val _ = app print strs
  val _ = print "\n"
  (* the same text that the compiler prints for its --types option, i.e. the
     content that basis/types.txt ought to have *)
  val f = TextIO.openOut "new_types.txt"
  val _ = app (fn s => TextIO.output (f,s)) (["\n"] @ strs @ ["\n"])
  val _ = TextIO.closeOut f
  in () end

