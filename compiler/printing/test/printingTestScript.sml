(*
  This file creates some sample declarations and runs the pretty
  printer adjustments over them, confirms that the adjusted decs
  still type check, and exports the s-expressions so that the
  printed strings can be checked with the binary compiler.

  This builds on the inferencer run over the basis in
  basisTypeCheckTheory.
*)
Theory printingTest
Ancestors
  basisTypeCheck addPrintVals typeDecToPP printTweaks infer_cv
  fromSexp[qualified]
  infer addPrintVals_cv
Libs
  preamble basicComputeLib ml_translatorLib ml_progLib
  basisFunctionsLib cv_transLib astToSexprLib[qualified]

val _ = (max_print_depth := 20);

val _ = print "Setting up test program...\n";

val _ = translation_extends "basisProg"
val _ = (use_full_type_names := false);

Datatype:
  example = Ex_A num (example list) | Ex_B num
End
val res = register_type “:example”;

val res = translate TAKE_def;
val res = translate DROP_def;

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

Theorem x_list_chars_thm = EVAL “x_list_chars”
val res = translate x_list_chars_thm;

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

val dlet_empty =
  “[Dlet unknown_loc (Pvar «x_app_list_empty») (Con (SOME (Short «Nil»)) [])]”

Quote more_decs = cakeml:
  type 'a foo = ('a->int) option;
  type ints = int list;
  val (bar: ints) = [];
End

val decs =
  EVAL “DROP (LENGTH basis) (^prog ++ ^dlet_empty ++ ^more_decs)” |> concl |> rhs;

(* ************************************************************************** *)

val _ = print "Running inference on basis...\n";

(* Based on repl_init_typesScript.sml *)
fun check infer_res = let
  val _ = if can (match_term ``infer$Success _``) infer_res then
            print "Was Success!" else
          if can (match_term ``infer$Failure _``) infer_res then let
            val msg = infer_res |> rand |> rand |> rand |> stringSyntax.fromHOLstring
                      handle HOL_ERR _ =>
                      failwith ("Was Failure! " ^
                        "(Also failed to fully evaluate error message?)")
            in failwith ("Was Failure! Message: " ^ msg) end
          else failwith "Failed to fully evaluate? (Neither Success nor Failure)"
  val _ = print "\n"
  in () end

fun print_types tm = let
  val _ = print "\nTypes of functions:\n\n"
  val strs = EVAL ``inf_env_to_types_string ^tm``
               |> concl |> rand |> listSyntax.dest_list |> fst
               |> map (stringSyntax.fromHOLstring o rand) |> map print
  val _ = print "\n"
  in () end

val _ = cv_trans_deep_embedding EVAL basisProgTheory.basis_def;

val basis_infer_res =
  cv_eval “infertype_prog_inc (init_config, start_type_id) basis” |> concl |> rhs;
val _ = check basis_infer_res;

val basis_prog_types = basis_infer_res |> rand;
val basis_tn =
  EVAL “init_type_names (FST ^basis_prog_types)” |> concl |> rand;
val basis_ienv =
  EVAL “FST ^basis_prog_types” |> concl |> rand;
val basis_next_id =
  EVAL “SND ^basis_prog_types” |> concl |> rand;

(* ************************************************************************** *)

val _ = print "Adding pretty printing functions + type checking...\n";

(* We start with cv-translating add_print_features. Note that some of these
   cv_trans calls produce (unprovable) preconditions. *)

val res = cv_trans printTweaksTheory.print_failure_message_def;

(* The SRULE is used to make sure that we don't run into issues regarding
   underspecified records, as described above. *)
val res = cv_trans_pre "" (printTweaksTheory.add_err_message_def
                             |> SRULE [init_infer_state_def, GSYM call_infer_def]);
val res = cv_trans_pre "" (printTweaksTheory.add_print_from_opts_def
                             |> SRULE [init_infer_state_def, GSYM call_infer_def]);
val res = cv_trans_pre "" printTweaksTheory.add_prints_from_opts_def;
val res = cv_trans_pre "" (printTweaksTheory.add_print_features_def
                             |> SRULE [init_infer_state_def, GSYM call_infer_def]);

val decs_with_pp_res =
  cv_eval “add_print_features (^basis_tn, ^basis_ienv, ^basis_next_id) ^decs”
    |> concl |> rand |> rhs;
val _ = check decs_with_pp_res;

val decs_with_pp = decs_with_pp_res |> rand |> pairSyntax.dest_pair |> fst;

fun has_failure tm = (can $ find_term $
  aconv “Long «PrettyPrinter» (Short «failure_message»)”) tm

val _ = if has_failure decs_with_pp then
          print "WARNING: decs_with_pp contain at least one failure message!\n"
        else print "Ok - no failure message detected.\n"

val full_prog = cv_eval “basis ++ ^decs_with_pp” |> concl |> rhs;

val full_prog_infer_res =
  cv_eval “infertype_prog_inc (init_config, start_type_id) ^full_prog”
    |> concl |> rhs;

val _ = check full_prog_infer_res;
val _ = print_types (full_prog_infer_res |> rand |> pairSyntax.dest_pair |> fst);

(* ************************************************************************** *)

val _ = print "Writing sexp output...\n"

val _ = astToSexprLib.write_ast_to_file "test_pprint.sexp" full_prog;

val _ = print "Done!\n";

(* ************************************************************************** *)

(* For debugging it is useful to look at the components separately. Here are
   some examples: *)

val decs2 = cv_eval “add_pp_decs ^(basis_tn).pp_fixes ^decs” |> concl |> rand;

(* add_print_features uses infer_ds, but we use call_infer instead. This way we
   avoid giving cv_eval the underspecified record <| next_id := next_id |>,
   which is syntactic sugar for ARB with next_id := 0 *)
val decs2_infer_res =
  cv_eval “call_infer ^basis_ienv ^decs2 ^basis_next_id”
    |> concl |> rand |> rhs;
val _ = check (decs2_infer_res |> pairSyntax.dest_pair |> fst);

val decs_ienv = decs2_infer_res |> pairSyntax.dest_pair |> fst |> rand;

(* update_type_names is called in val_prints *)
val res = cv_eval “update_type_names ^decs_ienv ^basis_tn” |> concl |> rhs;

val ienv2 = cv_eval “extend_dec_ienv ^decs_ienv ^basis_ienv” |> concl |> rand;

val (prints, tn2) =
  cv_eval “val_prints ^basis_tn ^basis_ienv ^decs_ienv”
    |> concl |> rand |> pairSyntax.dest_pair;
