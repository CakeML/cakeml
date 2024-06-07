(*
  Experiments with evaluating the compiler using cv_compute
*)
open preamble cv_transLib;
open backend_x64_cvTheory x64_configTheory;
open exportTheory export_x64Theory;
open to_data_cvTheory;

val _ = new_theory "backend_x64_eval";

fun compile_cake prefix conf prog = let
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
  val th1 = cv_eval input_tm
  val th2 = th1 |> REWRITE_RULE [GSYM c]
  fun follow_path path = let
    fun loop [] tm = tm
      | loop (c::cs) tm =
           if c = #"r" then loop cs (rand tm) else
           if c = #"l" then loop cs (rator tm) else
           if c = #"a" then loop cs (snd (dest_abs tm)) else
             fail()
    in loop (explode path) end
  fun abbrev_inside name path th = let
    val tm = follow_path path (concl th)
    val def = define_abbrev name tm
    in (def, CONV_RULE (PATH_CONV path (REWR_CONV (SYM def))) th) end
  val (conf_def,th) = abbrev_inside "conf" "rrrr" th2
  val (data_def,th) = abbrev_inside "data" "rrrlr" th
  val (code_def,th) = abbrev_inside "code" "rrlr" th
  in (th,code_def,data_def,conf_def) end

(*
val prefix = "x64_"
val conf = “x64_backend_config”
val prog = “[] : ast$dec list”
val (res,_,_,conf_def) = compile_cake prefix conf prog;
*)

val _ = export_theory();
