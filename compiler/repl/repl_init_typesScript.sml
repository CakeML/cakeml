(*
  This file runs the type inferencer on the declarations of the basis,
  Candle kernel and REPL module, i.e. everything in the user-visible
  initial environment of the read-eval-print loop.
*)
open preamble basicComputeLib cv_transLib infer_cvTheory repl_moduleProgTheory
     repl_check_and_tweakTheory

val _ = new_theory "repl_init_types"

val _ = cv_trans_deep_embedding EVAL repl_moduleProgTheory.repl_prog_def;

val _ = cv_auto_trans inferTheory.init_config_def;

val eval_res_thm =
  cv_eval “infertype_prog_inc (init_config, start_type_id) repl_prog”;

val print_types = let
  val x = eval_res_thm |> concl |> rhs
  val _ = if can (match_term ``infer$Success _``) x then () else
          if can (match_term ``infer$Failure _``) x then let
            val msg = x |> rand |> rand |> rand |> stringSyntax.fromHOLstring
                      handle HOL_ERR _ =>
                      failwith ("Type inference failed. " ^
                        "(Also failed to fully evaluate type inferencer error message)")
            in failwith ("Type inference failed with message: " ^ msg) end
          else failwith "Failed to fully evaluate type inferencer applied to repl_prog."
  val _ = print "\nTypes of all basis, Candle and Repl functions:\n\n"
  val x = x |> rand |> rator |> rand
  val strs = EVAL ``inf_env_to_types_string ^x``
               |> concl |> rand |> listSyntax.dest_list |> fst
               |> map (stringSyntax.fromHOLstring o rand) |> map print
  val _ = print "\n"
  in () end
val result_tm = eval_res_thm |> concl |> rand |> rand
Definition repl_prog_types_def:
  repl_prog_types = ^result_tm
End
val result = eval_res_thm
               |> CONV_RULE (PATH_CONV "rr" (REWR_CONV (GSYM repl_prog_types_def)));

Theorem repl_prog_types_thm = result;

Definition repl_init_types_def:
  repl_init_types = (init_type_names (FST repl_prog_types), repl_prog_types)
End

Theorem repl_init_types_eq = repl_init_types_def
  |> CONV_RULE (RAND_CONV
       (REWRITE_CONV [fetch "-" "repl_prog_types_def"] THENC EVAL));

val env = Decls_repl_prog |> concl |> rator |> rand

Definition repl_prog_env_def:
  repl_prog_env = merge_env ^env init_env
End

val _ = cv_trans locationTheory.unknown_loc_def

Triviality CommandLine_arguments_lemma =
  “case infertype_prog_inc (init_config,start_type_id) repl_prog of
   | Failure _ => F
   | Success env => infertype_prog_inc env
    [Dlet unknown_loc Pany
      (App Opapp
        [Var (Long "CommandLine" (Short "arguments"));
         Con NONE []])] = Success env”
  |> cv_eval |> SRULE [repl_prog_types_thm];

Theorem infertype_prog_inc_CommandLine_arguments:
  infertype_prog_inc repl_prog_types
    [Dlet unknown_loc Pany
      (App Opapp
        [Var (Long "CommandLine" (Short "arguments"));
         Con NONE []])] = Success repl_prog_types
Proof
  rewrite_tac [CommandLine_arguments_lemma]
QED

Triviality Repl_charsFrom_lemma =
  “case infertype_prog_inc (init_config,start_type_id) repl_prog of
   | Failure _ => F
   | Success env => infertype_prog_inc env
    [Dlet unknown_loc Pany
      (App Opapp
        [Var (Long "Repl" (Short "charsFrom"));
         Lit (StrLit "config_enc_str.txt")])] = Success env”
  |> cv_eval |> SRULE [repl_prog_types_thm];

Theorem infertype_prog_inc_Repl_charsFrom:
  infertype_prog_inc repl_prog_types
    [Dlet unknown_loc Pany
      (App Opapp
        [Var (Long "Repl" (Short "charsFrom"));
         Lit (StrLit "config_enc_str.txt")])] = Success repl_prog_types
Proof
  rewrite_tac [Repl_charsFrom_lemma]
QED

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory ();
