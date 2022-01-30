(*
  This file runs the type inferencer on the declarations of the basis,
  Candle kernel and REPL module, i.e. everything in the user-visible
  initial environment of the read-eval-print loop.
*)
open preamble basicComputeLib inferenceComputeLib repl_moduleProgTheory
     repl_check_and_tweakTheory

val _ = new_theory "repl_init_types"

(* -- evaluate type inferencer on repl_prog -- *)

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [inferenceComputeLib.add_inference_compset,
       basicComputeLib.add_basic_compset],
     computeLib.Defs
      [repl_check_and_tweakTheory.infertype_prog_inc_def,
       repl_moduleProgTheory.repl_prog_def],
     computeLib.Tys []
    ] cmp
val inf_eval = computeLib.CBV_CONV cmp;

val _ = (max_print_depth := 20);

local
  val test = inf_eval “infertype_prog_inc (init_config, start_type_id) repl_prog”
in
  val print_types = let
    val x = test |> concl |> rhs
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
  val result_tm = test |> concl |> rand |> rand
  val def = Define ‘repl_prog_types = ^result_tm’
  val result = test |> CONV_RULE (PATH_CONV "rr" (REWR_CONV (GSYM def)))
end

Theorem repl_prog_types_thm = result;

Definition repl_init_types_def:
  repl_init_types =
    (update_type_names (FST repl_prog_types) empty_type_names,repl_prog_types)
End

Theorem repl_init_types_eq = repl_init_types_def
  |> CONV_RULE (RAND_CONV
       (REWRITE_CONV [fetch "-" "repl_prog_types_def"] THENC EVAL));

val env = Decls_repl_prog |> concl |> rator |> rand

Definition repl_prog_env_def:
  repl_prog_env = merge_env ^env init_env
End

val _ = export_theory ();
