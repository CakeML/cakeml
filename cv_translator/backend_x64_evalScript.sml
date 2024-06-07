(*
  Experiments with evaluating the compiler using cv_compute
*)
open preamble cv_transLib;
open backend_x64_cvTheory x64_configTheory;
open exportTheory export_x64Theory;
open to_data_cvTheory;

val _ = new_theory "backend_x64_eval";

fun dest_path path = let
  fun loop [] = I
    | loop (c::cs) =
         if c = #"r" then loop cs o rand else
         if c = #"l" then loop cs o rator else
         if c = #"a" then loop cs o snd o dest_abs else
         if c = #"b" then loop (#"r" :: #"a" :: cs) else
           failwith ("dest_path does not understand " ^ implode [c])
  in loop (explode path) end

fun write_cv_char_list_to_file filename cv_char_list_tm = let
  val f = TextIO.openOut filename
  fun loop tm = let
    val (n,rest) = cvSyntax.dest_cv_pair tm
    val c = cvSyntax.dest_cv_num n |> numSyntax.int_of_term |> chr
    val _ = TextIO.output1(f,c)
    in loop rest end handle HOL_ERR _ => ();
  val _ = loop cv_char_list_tm
  in TextIO.closeOut f end;

fun compile_cake prefix conf prog filename conf_filename = let
  fun define_abbrev name tm =
    Feedback.trace ("Theory.allow_rebinds", 1)
      (mk_abbrev (prefix ^ name)) tm
  val c = backendTheory.config_to_inc_config_def
            |> ISPEC conf |> CONV_RULE (RAND_CONV EVAL)
  val input_tm = backend_x64Theory.to_livesets_x64_def |> GEN_ALL
    |> SPEC prog |> SPEC (c |> concl |> rand) |> concl |> lhs |> mk_fst
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
  val input_tm = backend_x64Theory.compile_cake_x64_def |> GEN_ALL
    |> SPEC prog |> SPEC c_oracle_tm |> concl |> lhs
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
  val e = cv_x64_export_def |> concl |> strip_forall |> snd |> lhs
  val cv_ty = cvSyntax.cv
  fun get_one_subst name abbrev_def =
    mk_var(name,cvSyntax.cv) |-> (abbrev_def |> concl |> rhs |> rand)
  fun cv_explode e = SPEC e cv_mlstring_explode_def |> concl |> lhs
  fun cv_concat e = SPEC e cv_mlstring_concat_def |> concl |> lhs
  fun cv_append e = SPEC e cv_misc_append_def |> concl |> lhs
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
  val _ = write_cv_char_list_to_file filename l
  val _ = case conf_filename of NONE => ()
          | SOME fname => write_cv_char_list_to_file fname
                            (conf_def |> concl |> rhs |> rand)
  in th end

(*
val _ = (max_print_depth := 15);
val prefix = "x64_"
val conf = “x64_backend_config”
val prog = “[] : ast$dec list”
val filename = "output.S"
val conf_filename = SOME "conf_str.txt"
val res = time (compile_cake prefix conf prog filename) conf_filename;
*)

val _ = export_theory();
