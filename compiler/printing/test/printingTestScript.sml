(*
  This file creates some sample declarations and runs the pretty
  printer adjustments over them, confirms that the adjusted decs
  still type check, and exports the s-expressions so that the
  printed strings can be checked with the binary compiler.

  This builds on the inferencer run over the basis in
  basisTypeCheckTheory.
*)
Theory printingTest
Ancestors[qualified]
  basisTypeCheck addPrintVals typeDecToPP printTweaks
  fromSexp
  infer_cv addPrintVals_cv
Libs
  preamble basicComputeLib ml_translatorLib ml_progLib
  basisFunctionsLib cv_transLib astToSexprLib[qualified]

val _ = (max_print_depth := 20);

val _ = print "Setting up test program...\n";

Quote decs = cakeml:
  (* type 'a foo = ('a->int) option; *)
  type ints = int list;
  val (bar: ints) = [];
End

val _ = print "Running inference on basis...\n";

(* Based on repl_init_typesScript.sml *)

fun print_types infer_res = let
  val _ = if can (match_term ``infer$Success _``) infer_res then () else
          if can (match_term ``infer$Failure _``) infer_res then let
            val msg = infer_res |> rand |> rand |> rand |> stringSyntax.fromHOLstring
                      handle HOL_ERR _ =>
                      failwith ("Type inference failed. " ^
                        "(Also failed to fully evaluate type inferencer error message)")
            in failwith ("Type inference failed with message: " ^ msg) end
          else failwith "Failed to fully evaluate type inferencer applied to repl_prog."
  val _ = print "\nTypes of functions:\n\n"
  val infer_res = infer_res |> rand |> rator |> rand
  val strs = EVAL ``inf_env_to_types_string ^infer_res``
               |> concl |> rand |> listSyntax.dest_list |> fst
               |> map (stringSyntax.fromHOLstring o rand) |> map print
  val _ = print "\n"
  in () end

val _ = cv_trans_deep_embedding EVAL basisProgTheory.basis_def;

val basis_infer_res =
  cv_eval “infertype_prog_inc (init_config, start_type_id) basis” |> concl |> rhs;

val _ = print_types basis_infer_res;

val basis_prog_types = basis_infer_res |> rand;
val basis_tn =
  EVAL “init_type_names (FST ^basis_prog_types)” |> concl |> rand;



val _ = print "Adding pretty printing functions + type checking...\n";

val decs_with_pp =
  cv_eval “add_pp_decs ^(basis_tn).pp_fixes ^decs” |> concl |> rand;

val res = (* Success *)
  cv_eval “infertype_prog_inc ^basis_prog_types ^decs_with_pp”

val res = (* Fail *)
  cv_eval “infer_ds (FST ^basis_prog_types) ^decs_with_pp (init_infer_state <| next_id := (SND ^basis_prog_types) |>)”

(* Some of these produce unprovable preconditions. *)
(* val res = cv_trans printTweaksTheory.print_failure_message_def; *)
(* val res = cv_trans_pre "" printTweaksTheory.add_err_message_def; *)
(* val res = cv_trans_pre "" printTweaksTheory.add_print_from_opts_def; *)
(* val res = cv_trans_pre "" printTweaksTheory.add_prints_from_opts_def; *)
(* val res = cv_trans_pre "" printTweaksTheory.add_print_features_def; *)

(* val res = cv_eval “add_print_features ^repl_init_types ^decs”; *)
