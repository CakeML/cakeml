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
  { default_config_def  : thm
  , default_config_simp : thm
  , to_livesets_def     : thm
  , compile_cake_def    : thm
  , compile_cake_imp    : thm
  , cv_export_def       : thm }

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

fun allowing_rebind f = Feedback.trace ("Theory.allow_rebinds", 1) f;

fun eval_cake_compile_general (arch : arch_thms) (input : comp_input) = let
  val _ = (cv_memLib.verbosity_level := cv_memLib.Verbose)
  fun report s = print (String.concat ["eval_cake: ", s, " --- ",
                    Date.toString (Date.fromTimeLocal (Time.now())),"\n"])
  val { prefix, conf_def, prog_def
      , output_filename , output_conf_filename } = input
  val { default_config_def, default_config_simp, to_livesets_def
      , compile_cake_def, compile_cake_imp, cv_export_def } = arch
  fun define_abbrev name tm =
    Feedback.trace ("Theory.allow_rebinds", 1)
      (mk_abbrev (prefix ^ name)) tm
  val conf = conf_def |> concl |> lhs
  val c = backendTheory.config_to_inc_config_def
            |> ISPEC conf |> CONV_RULE (RAND_CONV EVAL)
  val _ = report "config EVAL-ed"
  val _ = allowing_rebind (cv_trans_deep_embedding EVAL) prog_def
  val _ = report "cv_trans_deep_embedding prog_def finished"
  val input_tm = to_livesets_def |> GEN_ALL
    |> SPEC (prog_def |> concl |> lhs)
    |> SPEC (c |> concl |> rand) |> concl |> lhs |> mk_fst
  val oracles = let
    val _ = report "about to run cv_eval on to_livesets_def"
    val graphs = cv_eval input_tm |> rconc
    val _ = report "cv_eval to_livesets finished"
    in reg_allocComputeLib.get_oracle reg_alloc.Irc graphs end
  val _ = report "external register allocation finished"
  val oracle_def = define_abbrev "temp_oracle" oracles;
  val _ = allowing_rebind (cv_trans_deep_embedding EVAL) oracle_def
  val _ = report "cv_trans_deep_embedding oracle_def finished"
  val oracle_tm = oracle_def |> concl |> lhs
  val c_tm = c |> concl |> lhs
  val c_oracle_tm = backendTheory.inc_set_oracle_def
                      |> SPEC (c |> concl |> rhs)
                      |> SPEC oracle_tm |> concl |> lhs
  val input_tm = compile_cake_def |> GEN_ALL
    |> SPEC (prog_def |> concl |> lhs)
    |> SPEC c_oracle_tm |> concl |> lhs
  val to_option_some = cv_typeTheory.to_option_def |> cj 2
  val to_pair = cv_typeTheory.to_pair_def |> cj 1
  val _ = report "about to run cv_eval_raw on complie_cake_def"
  val th1 = cv_eval_raw input_tm
            |> CONV_RULE (PATH_CONV "lr" (REWRITE_CONV [GSYM c]))
  val _ = report "cv_eval_raw complie_cake_def finished"
  val th2 = th1 |> CONV_RULE (PATH_CONV "r" (REWR_CONV to_option_some))
            handle HOL_ERR _ => failwith "compiler returned NONE"
  val c2n_Num = cvTheory.c2n_def |> cj 1
  val th3 = th2 |> CONV_RULE (PATH_CONV "rr" (REWR_CONV to_pair)
                        THENC PATH_CONV "rrr" (REWR_CONV to_pair)
                        THENC PATH_CONV "rrrr" (REWR_CONV to_pair)
                        THENC PATH_CONV "rrrrr" (REWR_CONV to_pair)
                        THENC PATH_CONV "rrrrrr" (REWR_CONV to_pair)
                        THENC PATH_CONV "rrrrrrr" (REWR_CONV to_pair)
                        THENC PATH_CONV "rrrrrrrr" (REWR_CONV to_pair)
                        THENC PATH_CONV "rrrlr" (REWR_CONV c2n_Num)
                        THENC PATH_CONV "rrrrrlr" (REWR_CONV c2n_Num)
                        THENC PATH_CONV "rrrrrrrlr" (REWR_CONV c2n_Num))
  val _ = report "to_pair evaluation finished"
  fun abbrev_inside name path th = let
    val tm = dest_path path (concl th)
    val def = define_abbrev name tm
    in (def, CONV_RULE (PATH_CONV path (REWR_CONV (SYM def))) th) end
  val (code_def,th) = abbrev_inside "code" "rrlr" th3
  val (data_def,th) = abbrev_inside "data" "rrrrlr" th
  val (ffis_def,th) = abbrev_inside "ffis" "rrrrrrlr" th
  val (syms_def,th) = abbrev_inside "syms" "rrrrrrrrlr" th
  val (conf_def,th) = abbrev_inside "conf" "rrrrrrrrr" th
  val _ = report "abbrevations for result defined"
  fun new_spec th =
    new_specification(prefix ^ "compiled",
                      [prefix ^ "oracle", prefix ^ "info"], th)
  val result_th = MATCH_MP compile_cake_imp th
    |> REWRITE_RULE [backendTheory.inc_set_oracle_pull,
                     backendTheory.inc_config_to_config_config_to_inc_config]
    |> REWRITE_RULE [default_config_simp,LENGTH_NIL]
    |> CONV_RULE (UNBETA_CONV oracle_tm)
    |> MATCH_MP backend_asmTheory.exists_oracle
    |> CONV_RULE (PATH_CONV "b" BETA_CONV)
    |> new_spec
  val _ = report "new_spec run on result"
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
     get_one_subst "cv_syms" syms_def,
     (* TODO: exp/ret/pk need to be passed as arguments for in-logic
        Pancake compiler evaluation *)
     mk_var("cv_exp",cvSyntax.cv) |-> cvSyntax.mk_cv_num numSyntax.zero_tm,
     mk_var("cv_ret",cvSyntax.cv) |-> cvSyntax.mk_cv_num numSyntax.zero_tm,
     mk_var("cv_pk",cvSyntax.cv)  |-> cvSyntax.mk_cv_num numSyntax.zero_tm]
  val _ = null (free_vars export_tm) orelse failwith "failed to eval export"
  (*
    cv_repLib.cv_rep_for []
    “explode $ concat $ misc$append (x64_export x64_ffis x64_code x64_data x64_syms)”
  *)
  val _ = report "about to run cv_compute on export"
  val l = cv_computeLib.cv_compute (cv_transLib.cv_eqs_for export_tm) export_tm
          |> concl |> rhs
  val _ = report "cv_compute on export finished"
  val _ = write_cv_char_list_to_file output_filename l
  val _ = case output_conf_filename of NONE => ()
          | SOME fname => write_cv_char_list_to_file fname
                            (conf_def |> concl |> rhs |> rand)
  (* --- *)
  val _ = Theory.delete_binding (prefix ^ "temp_oracle_cv_eq")
  val _ = Theory.delete_binding (prefix ^ "temp_oracle_cv_def")
  val _ = Theory.delete_binding (prefix ^ "temp_oracle_def")
  val _ = Theory.delete_binding (prefix ^ "syms_def")
  val _ = report "theory tidy up finished"
  in result_th end

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

(* --- for debugging ---
   val _ = (max_print_depth := 15);
   val arch = x64_arch_thms;
   val input =
       { prefix               = "x64_"
       , conf_def             = #default_config_def x64_arch_thms
       , prog_def             = Define `prog = [] : ast$dec list`
       , output_filename      = "test.S"
       , output_conf_filename = SOME "test_conf.txt" } : comp_input;
*)

end
