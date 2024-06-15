(*
  Functions for in-logic evaluation of the CakeML compiler.
  These use HOL's cv_compute facility.
*)
structure eval_cake_compileLib :> eval_cake_compileLib =
struct

open preamble cv_transLib;
open exportTheory;
open to_data_cvTheory;

type arch_thms =
  { default_config_def : thm
  , to_livesets_def    : thm
  , compile_cake_def   : thm
  , cv_export_def      : thm }

type comp_input =
  { prefix               : string
  , conf_def             : thm
  , prog_def             : thm
  , output_filename      : string
  , output_conf_filename : string option }

fun write_cv_char_list_to_file filename cv_char_list_tm = let
  val f = TextIO.openOut filename
  fun loop tm = let
    val (n,rest) = cvSyntax.dest_cv_pair tm
    val c = cvSyntax.dest_cv_num n |> numSyntax.int_of_term |> chr
    val _ = TextIO.output1(f,c)
    in loop rest end handle HOL_ERR _ => ();
  val _ = loop cv_char_list_tm
  in TextIO.closeOut f end;

fun eval_cake_compile_general (arch : arch_thms) (input : comp_input) = let
  val { prefix, conf_def, prog_def
      , output_filename , output_conf_filename } = input
  val { default_config_def, to_livesets_def
      , compile_cake_def, cv_export_def } = arch
  fun define_abbrev name tm =
    Feedback.trace ("Theory.allow_rebinds", 1)
      (mk_abbrev (prefix ^ name)) tm
  val conf = conf_def |> concl |> lhs
  val c = backendTheory.config_to_inc_config_def
            |> ISPEC conf |> CONV_RULE (RAND_CONV EVAL)
  val _ = cv_trans_deep_embedding EVAL prog_def
  val input_tm = to_livesets_def |> GEN_ALL
    |> SPEC (prog_def |> concl |> lhs)
    |> SPEC (c |> concl |> rand) |> concl |> lhs |> mk_fst
  val oracles = let
    val graphs = cv_eval input_tm |> rconc
    in reg_allocComputeLib.get_oracle reg_alloc.Irc graphs end
  val oracle_def = define_abbrev "oracle" oracles;
  val _ = cv_trans_deep_embedding EVAL oracle_def
  val oracle_tm = oracle_def |> concl |> lhs
  val c_tm = c |> concl |> lhs
  val c_oracle_tm = backend_cvTheory.inc_set_oracle_def
                      |> SPEC (c |> concl |> rhs)
                      |> SPEC oracle_tm |> concl |> lhs
  val input_tm = compile_cake_def |> GEN_ALL
    |> SPEC (prog_def |> concl |> lhs)
    |> SPEC c_oracle_tm |> concl |> lhs
  val to_option_some = cv_typeTheory.to_option_def |> cj 2
  val to_pair = cv_typeTheory.to_pair_def |> cj 1
  val th1 = cv_eval_raw input_tm
            |> CONV_RULE (PATH_CONV "lr" (REWRITE_CONV [GSYM c]))
  val th2 = th1 |> CONV_RULE (PATH_CONV "r" (REWR_CONV to_option_some))
            handle HOL_ERR _ => failwith "compiler returned NONE"
  val th3 = th2 |> CONV_RULE (PATH_CONV "rr" (REWR_CONV to_pair))
                |> CONV_RULE (PATH_CONV "rrr" (REWR_CONV to_pair))
                |> CONV_RULE (PATH_CONV "rrrr" (REWR_CONV to_pair))
                |> CONV_RULE (PATH_CONV "rrrrr" (REWR_CONV to_pair))
  fun abbrev_inside name path th = let
    val tm = dest_path path (concl th)
    val def = define_abbrev name tm
    in (def, CONV_RULE (PATH_CONV path (REWR_CONV (SYM def))) th) end
  val (code_def,th) = abbrev_inside "code" "rrlr" th3
  val (data_def,th) = abbrev_inside "data" "rrrlr" th
  val (ffis_def,th) = abbrev_inside "ffis" "rrrrlr" th
  val (syms_def,th) = abbrev_inside "syms" "rrrrrlr" th
  val (conf_def,th) = abbrev_inside "conf" "rrrrrr" th
  val result_th = th
  (* --- *)
  val e = cv_export_def |> concl |> strip_forall |> snd |> lhs
  val cv_ty = cvSyntax.cv
  fun get_one_subst name abbrev_def =
    mk_var(name,cvSyntax.cv) |-> (abbrev_def |> concl |> rhs |> rand)
  fun cv_explode e = SPEC e basis_cvTheory.cv_mlstring_explode_def |> concl |> lhs
  fun cv_concat e = SPEC e basis_cvTheory.cv_mlstring_concat_def |> concl |> lhs
  fun cv_append e = SPEC e basis_cvTheory.cv_misc_append_def |> concl |> lhs
  val export_tm = e |> cv_append |> cv_concat |> cv_explode |> subst
    [get_one_subst "cv_ffi_names" ffis_def,
     get_one_subst "cv_data" data_def,
     get_one_subst "cv_bytes" code_def,
     get_one_subst "cv_syms" syms_def]
  val _ = null (free_vars export_tm) orelse failwith "failed to eval export"
  (*
    cv_repLib.cv_rep_for []
    “explode $ concat $ misc$append (x64_export x64_ffis x64_code x64_data x64_syms)”
  *)
  val l = cv_computeLib.cv_compute (cv_transLib.cv_eqs_for export_tm) export_tm
          |> concl |> rhs
  val _ = write_cv_char_list_to_file output_filename l
  val _ = case output_conf_filename of NONE => ()
          | SOME fname => write_cv_char_list_to_file fname
                            (conf_def |> concl |> rhs |> rand)
  in th end

fun eval_cake_compile_with_conf arch prefix conf_def prog_def filename =
  eval_cake_compile_general arch
    { prefix               = prefix
    , conf_def             = conf_def
    , prog_def             = prog_def
    , output_filename      = filename
    , output_conf_filename = NONE };

fun eval_cake_compile arch prefix =
  eval_cake_compile_with_conf arch prefix (#default_config_def arch);

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

end
