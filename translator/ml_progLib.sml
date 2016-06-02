structure ml_progLib :> ml_progLib =
struct

open preamble;
open ml_progTheory;

(* state *)

datatype ml_prog_state = ML_code of (thm list) (* state const definitions *) *
                                    (thm list) (* env const definitions *) *
                                    (thm list) (* v const definitions *) *
                                    thm (* ML_code thm *);

(* helper functions *)

fun prove_assum_by_eval th1 = let
  val (x,y) = dest_imp (concl th1)
  val lemma = (EVAL THENC REWRITE_CONV [DISJOINT_set_simp] THENC EVAL) x
  val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV lemma)) th1
  in MP lemma TRUTH end

fun find_name name = let
  val ns = map (#1 o dest_const) (constants (current_theory()))
  fun aux n = let
    val str = name ^ "_" ^ int_to_string n
    in if mem str ns then aux (n+1) else str end
  in aux 0 end

fun define_abbrev for_eval name tm =
  if free_vars tm = [] then let
    val n = mk_var(name,type_of tm)
    val tm = mk_eq(n,tm)
    val def = Definition.new_definition(name,tm)
    val _ = if for_eval then computeLib.add_persistent_funs [name] else ()
    in def end
  else let
    val vs = free_vars tm |> sort
      (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
    val vars = foldr mk_pair (last vs) (butlast vs)
    val n = mk_var(name,mk_type("fun",[type_of vars, type_of tm]))
    val eq_tm = mk_eq(mk_comb(n,vars),tm)
    val def = Definition.new_definition(name,eq_tm)
    val _ = if for_eval then computeLib.add_persistent_funs [name] else ()
    in def end

fun cond_abbrev dest conv name th = let
  val tm = dest th
  val (x,vs) = strip_comb tm handle HOL_ERR _ => (tm,[])
  in if is_const x andalso all is_var vs then (th,[])
     else let
       val def = define_abbrev true (find_name name) tm |> SPEC_ALL
       val th = CONV_RULE (conv (REWR_CONV (GSYM def))) th
       in (th,[def]) end end

fun clean (ML_code (ss,envs,vs,th)) = let
  val (th,new_ss) = cond_abbrev (rand o concl) RAND_CONV "auto_state" th
  val (th,new_envs) = cond_abbrev (rand o rator o concl)
                        (RATOR_CONV o RAND_CONV) "auto_env" th
  in ML_code (new_ss @ ss, new_envs @ envs, vs, th) end

(* --- *)

val init_state =
  ML_code ([SPEC_ALL init_state_def],[init_env_def],[],ML_code_NIL);

fun open_module mn_str (ML_code (ss,envs,vs,th)) =
  ML_code
    (ss,envs,vs,
     MATCH_MP ML_code_new_module th
     |> SPEC (stringSyntax.fromMLstring mn_str)
     |> prove_assum_by_eval)
  handle HOL_ERR _ => failwith("open_module failed for " ^ thm_to_string th)

fun close_module sig_opt (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_close_module th
  val v = th |> concl |> dest_forall |> fst
  val sig_tm = (case sig_opt of
                  NONE => mk_const("NONE",type_of v)
                | SOME tm => optionSyntax.mk_some(tm))
  val th = SPEC sig_tm th
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) (* removes BUTLASTN *)
  in clean (ML_code (ss,envs,vs,th)) end

(*
val tds_tm = ``[]:type_def``
*)

fun add_Dtype tds_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dtype th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dtype th
  val th = SPEC tds_tm th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) (* removes write_tds *)
  in clean (ML_code (ss,envs,vs,th)) end

(*
val n_tm = ``"bar"``
val l_tm = ``[]:t list``
*)

fun add_Dexn n_tm l_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dexn th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dexn th
  val th = SPECL [n_tm,l_tm] th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) (* removes write_tds *)
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dtabbrev l1_tm l2_tm l3_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dtabbrev th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dtabbrev th
  val th = SPECL [l1_tm,l2_tm,l3_tm] th
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dlet eval_thm var_str v_thms (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dlet_var th
  val th = MATCH_MP th eval_thm
           handle HOL_ERR _ => failwith "add_Dlet eval_thm does not match"
  val th = th |> SPEC (stringSyntax.fromMLstring var_str)
  in clean (ML_code (ss,envs,v_thms @ vs,th)) end

val Recclosure_pat =
  semanticPrimitivesTheory.v_nchotomy
  |> SPEC_ALL |> concl |> rand |> rand |> rand |> rator |> rand
  |> dest_exists |> snd
  |> dest_exists |> snd
  |> dest_exists |> snd |> rand

fun add_Dletrec funs v_names (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dletrec th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dletrec th
  val th = SPEC funs th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                  (SIMP_CONV std_ss [write_rec_def,FOLDR,
                    semanticPrimitivesTheory.build_rec_env_def]))
  val tms = rev (find_terms (can (match_term Recclosure_pat)) (concl th))
  val xs = zip v_names tms
  val v_defs = map (fn (x,y) => define_abbrev false x y) xs
  val th = REWRITE_RULE (map GSYM v_defs) th
  in clean (ML_code (ss,envs,v_defs @ vs,th)) end

(*

val s = init_state
val mn_str = "hello"
val s = open_module mn_str s
val s = add_Dtype ``[]:type_def`` s
val s = add_Dletrec
  ``[("foo","x",Var (Short "x"));("var","y",Var (Short "y"))]`` ["foo_v","var_v"] s
val s = close_module NONE s

*)

end
