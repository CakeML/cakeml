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

val _ = translation_extends "basisProg"
val _ = (use_full_type_names := false);

val res = translate TAKE_def;
val res = translate DROP_def;

Datatype:
  example = Ex_A num (example list) | Ex_B num
End
val res = register_type “:example”;

Definition muddle_def:
  muddle i xs (Ex_A j ys) = Ex_A (i + j) (TAKE 2 xs ++
    DROP 2 (MAP (muddle (i + 1) (DROP 2 xs ++ TAKE 2 ys)) ys)) /\
  muddle i xs (Ex_B n) = Ex_A (i + n) xs
Termination
  WF_REL_TAC `measure (example_size o SND o SND)`
End
val res = translate muddle_def;

Definition x1_def:
  x1 = Ex_A 42 [Ex_B 5; Ex_B 7]
End
val res = translate x1_def;

Definition x2_def:
  x2 = muddle 3 [x1] x1
End
val res = translate x2_def;

Definition x3_def:
  x3 = [muddle 17 [x2; x1] x2]
End
val res = translate x3_def;

Definition x4_def:
  x4 = SOME (Ex_A 3 x3)
End
val res = translate x4_def;

Definition x_list_bool_def:
  x_list_bool = [T; F; T]
End
val res = translate x_list_bool_def;

Definition x_list_chars_def:
  x_list_chars = ["hello"; "there"] ++
    GENLIST (\n. if n < 32 then "dummy" else [CHR n]) 127
End
val res = translate $ EVAL “x_list_chars”;

Definition x_list_strs_def:
  x_list_strs = MAP implode x_list_chars ++ [implode (FLAT x_list_chars)]
End
val res = translate x_list_strs_def;

Definition x_maps_def:
  x_maps = [(1i, mlmap$fromList (mlint$int_cmp) [(1i, "x"); (2, "y")])]
End
val res = translate x_maps_def;

val _ = ml_prog_update remove_snocs;

val prog = get_prog (get_ml_prog_state ());

(* I cannot use add_cakeml here, since add_dec does not support all of these
   shapes as of 2026-01-30. *)
Quote more_decs = cakeml:
  val x_app_list_empty = Nil;

  type 'a foo = ('a->int) option;

  type ints = int list;
  val foo = ([]: ints);
End

Definition test_prog_def:
  test_prog =
    ^(EVAL “DROP (LENGTH basis) (^prog ++ ^more_decs)” |> concl |> rhs)
End


(* Adapted from repl_init_typesScript.sml *)
val _ = print "Doing type inference on basis...\n";

(* Checks whether an evaluation of infertype_prog_inc was successful. *)
fun check eval_res_thm = let
  val x = eval_res_thm |> concl |> rhs
  val _ = if can (match_term ``infer$Success _``) x then () else
          if can (match_term ``infer$Failure _``) x then let
            val msg = x |> rand |> rand |> rand |> stringSyntax.fromHOLstring
                      handle HOL_ERR _ =>
                      failwith ("Type inference failed. " ^
                        "(Also failed to fully evaluate type inferencer error message)")
            in failwith ("Type inference failed with message: " ^ msg) end
          else failwith "Failed to fully evaluate type inferencer."
  in () end

val basis_infer_eval =
  cv_eval “infertype_prog_inc (init_config, start_type_id) basis”;
val _ = check basis_infer_eval;

Definition basis_prog_types_def:
  basis_prog_types = ^(basis_infer_eval |> concl |> rand |> rand)
End

Definition basis_init_types_def:
  basis_init_types = (init_type_names (FST basis_prog_types), basis_prog_types)
End


val _ = print "Adding print features to test program...\n";

(* Some of these produce unprovable preconditions. *)
val res = cv_trans printTweaksTheory.print_failure_message_def;
val res = cv_trans_pre "" printTweaksTheory.add_err_message_def;
val res = cv_trans_pre "" printTweaksTheory.add_print_from_opts_def;
val res = cv_trans_pre "" printTweaksTheory.add_prints_from_opts_def;
val res = cv_trans_pre "" printTweaksTheory.add_print_features_def;
val res = cv_auto_trans_pre "" printTweaksTheory.add_print_then_read_def;

val test_prog_with_pp = cv_eval “add_print_features basis_init_types test_prog”


val _ = print "Doing type inference on full program (basis + test)...\n";

val full_prog = EVAL “basis ++ ^test_prog_with_pp” |> concl |> rhs

val full_prog_infer_eval =
  cv_eval “infertype_prog_inc (init_config, start_type_id) ^full_prog”
val _ = check full_prog_infer_eval;


val _ = print "Exporting full program as s-expression...\n";

val _ = astToSexprLib.write_ast_to_file "example_print.sexp" full_prog;

val _ = print "Success! You can use the binary compiler to check how the strings are printed.\n";

(* val with_pp_eval = EVAL ``add_pp_decs ^basis_tn.pp_fixes test_prog``; *)
(* val with_pp = rhs (concl with_pp_eval); *)

(* val result_tm = eval_res_thm |> concl |> rand |> rand *)

(* Definition test_prog_pp_def: *)
(*   test_prog_pp = ^with_pp *)
(* End *)

(* val _ = cv_trans test_prog_pp_def; *)

(* val infer_example = *)
(*   cv_eval “infertype_prog init_config (basis ++ test_prog_pp)” *)
(*   |> concl |> rand; *)

(* val _ = if can (match_term “infer$Success _”) infer_example then () else *)
(*     (print_term infer_example; failwith ("type inference failed on example prog")) *)

(* Definition example_ienv_def: *)
(*   example_ienv = *)
(*     case ^infer_example of *)
(*     | Success res => res *)
(*     | Failure _ => *)
(*         init_config  (* Testing should have failed before hitting this *) *)
(* End *)

(* val _ = cv_trans example_ienv_def; *)
(* val example_ienv_eq = cv_eval “example_ienv”; *)
(* val example_ienv = example_ienv_eq |> concl |> rhs; *)

(* val example_tn_eval = (REWRITE_CONV [example_ienv_eq] THENC EVAL) *)
(*                        ``init_type_names example_ienv``; *)
(* val example_tn = example_tn_eval |> concl |> rhs; *)


(* val foo = “add_print_features (example_tn)” *)

(*

val _ = print "Fetching type-name info and getting print decs.\n";

val example_prints_eval = EVAL ``val_prints ^basis_tn basis_ienv ^infer_example_ienv``
val example_print_data = concl example_prints_eval |> rhs |> dest_pair |> fst
val example_print_decs_eval = EVAL ``FLAT (MAP SND ^example_print_data)``
val example_print_decs = concl example_print_decs_eval |> rhs |> listSyntax.dest_list |> fst

val _ = print "Type-checking print decs.\n";

val dec_tc_evals = map (fn d => inf_eval ``infer_ds (extend_dec_ienv ^infer_example_ienv basis_ienv)
        [^d] ^infer_example_st``) example_print_decs

val fails = filter (not o can (match_term ``(infer$Success _, _)``) o rhs o concl) dec_tc_evals
val _ = if null fails then () else
    (print_thm (hd fails);
        failwith ("type inference failed on example prog with prints"))

val _ = print "Assembling canonical extended prog.\n";

val assembled = ``add_print_features (^basis_tn, basis_ienv, basis_infer_st.next_id) test_prog``
  |> (SIMP_CONV (srw_ss ()) [add_print_features_def, LET_THM,
        REWRITE_RULE [GSYM test_prog_pp_def] with_pp_eval,
        start_st_eval, infer_example_eval, example_prints_eval]
    THENC inf_eval
  )

val prog_rhs = assembled |> concl |> rhs
val _ = if can (match_term ``(infer$Success _)``) prog_rhs then () else
    (print_term prog_rhs;
        failwith ("test printing/inference assembly failed"))

val _ = print "Writing sexp output.\n"

val upd_prog = rand prog_rhs |> dest_pair |> fst
val full_prog_eval = EVAL ``basis ++ ^upd_prog``;
val full_prog = rhs (concl full_prog_eval);

val res = astToSexprLib.write_ast_to_file "example_print.sexp" full_prog;

val _ = print "Success.\n";

*)
