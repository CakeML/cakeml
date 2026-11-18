(*
  Opt-in translation of pointer equality for global-state monads, where a
  logical oracle in the user's state models the source PtrEq oracle.
  See examples/monadic_ptr_eqScript.sml.
*)
structure ml_monad_oracleLib :> ml_monad_oracleLib =
struct
  open HolKernel boolLib bossLib
  open ml_monadBaseSyntax ml_monad_oracleTheory

  val accessors_ref : thm option ref = ref NONE

  fun start_oracle_translation accessors = accessors_ref := SOME accessors

  fun accessors () =
    case !accessors_ref of
      SOME th => th
    | NONE => raise mk_HOL_ERR "ml_monad_oracleLib" "accessors"
                "Call start_oracle_translation first"

  fun argument n tm = List.nth (snd (strip_comb tm), n)
  fun computation tm = rand (argument 5 tm)

  fun bind_environment z env th = let
    val v = variant (free_varsl (concl th :: hyp th))
      (mk_var ("bound_value", ``:semanticPrimitives$v``))
    val name = mlstringSyntax.mk_mlstring (fst (dest_var z))
    val new_env = ml_translatorSyntax.mk_write (name,v,env)
    val th = INST [env |-> new_env] (DISCH_ALL th)
      |> SIMP_RULE (srw_ss()) [ml_translatorTheory.Eval_Var_SIMP]
      |> UNDISCH_ALL
  in (v,th) end

  fun configure tm th = let
    val th = PART_MATCH computation th tm
    val config = concl (accessors ())
    val target = concl th
    val pattern = pairSyntax.mk_pair (argument 0 target, argument 6 target)
    val actual = pairSyntax.mk_pair (argument 0 config, argument 2 config)
  in
    INST_TY_TERM (match_term pattern actual) th
  end

  fun translate_ptr_eq tm = let
    val (_, _, x, y) = dest_Mptr_eq tm
    val equality = ml_translatorLib.EqualityType_rule [] (type_of x)
    val left = ml_translatorLib.translate_tm x
    val right = ml_translatorLib.translate_tm y
    val result = MATCH_MP EvalOM_PtrEq_Eval
      (LIST_CONJ [accessors (), equality, left, right])
  in
    PART_MATCH computation result tm
  end

  fun translate_term tm =
    if is_Mptr_eq tm then translate_ptr_eq tm
    else if is_st_ex_return tm then let
      val value = ml_translatorLib.translate_tm (dest_st_ex_return tm)
      val exp = argument 1 (concl value)
      val no_ptr = EQT_ELIM (SIMP_CONV (srw_ss())
        [evaluatePropsTheory.no_ptr_eq_def]
        (mk_comb (prim_mk_const {Thy="evaluateProps", Name="no_ptr_eq"}, exp)))
      val result = MATCH_MP EvalOM_return (CONJ value no_ptr)
    in configure tm result end
    else if is_cond tm then let
      val (test,yes,no) = dest_cond tm
      val guard = ml_translatorLib.translate_tm test
      val yes_th = DISCH test (translate_term yes)
      val no_th = DISCH (mk_neg test) (translate_term no)
    in
      MATCH_MP EvalOM_If_Var (LIST_CONJ [guard,yes_th,no_th])
    end
    else if is_st_ex_bind tm then let
      val (x,f) = dest_st_ex_bind tm
      val (z,body) = dest_abs f
      val first = translate_term x
      val second = translate_term body
      val first_tm = concl first
      val second_tm = concl second
      val st = argument 3 first_tm
      val env = argument 2 second_tm
      val next = pairSyntax.mk_snd (mk_comb (x,st))
      val (v,second) = bind_environment z env
        (INST [argument 3 second_tm |-> next] second)
      val second = CONV_RULE
        ((RATOR_CONV o RAND_CONV o RAND_CONV) (UNBETA_CONV z)) second
      val inv = argument 0 (argument 5 first_tm)
      val premise = list_mk_comb (inv,[z,v])
      val second = GENL [z,v] (DISCH premise second)
    in
      MATCH_MP EvalOM_bind (CONJ first second)
    end
    else raise mk_HOL_ERR "ml_monad_oracleLib" "translate_term"
      "Expected Mptr_eq, st_ex_return, st_ex_bind, or a conditional"

  fun translate_function tm = let
    val (z,body) = dest_abs tm
    val monadic = not (is_abs body)
    val th = if monadic then translate_term body
             else translate_function body
    val env = argument (if monadic then 2 else 0) (concl th)
    val (v,th) = bind_environment z env th
    val inv = ml_translatorLib.get_type_inv (type_of z)
    val premise = list_mk_comb (inv,[z,v])
  in
    if monadic then let
      val st = argument 3 (concl th)
      val th = CONV_RULE
        ((RATOR_CONV o RAND_CONV o RAND_CONV) (UNBETA_CONV z)) th
      val th = GENL [z,v,st] (DISCH premise th)
    in MATCH_MP Eval_ArrowOM th end
    else let
      val th = CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV z)) th
      val th = GENL [v,z] (DISCH premise th)
    in MATCH_MP ml_translatorTheory.Eval_Fun th end
  end

  fun translate_definition def = let
    val equation = SPEC_ALL def
    val (lhs,rhs) = dest_eq (concl equation)
    val args = snd (strip_comb lhs)
    val function = list_mk_abs (args,rhs)
    val th = translate_function function
    val function_eq = List.foldr (fn (v,eq) => ABS v eq) equation args
      |> CONV_RULE (LAND_CONV (DEPTH_CONV ETA_CONV))
  in
    REWRITE_RULE [GSYM function_eq] th
  end

  fun oracle_translate def = let
    val name = def |> SPEC_ALL |> concl |> lhs |> strip_comb |> fst
                   |> dest_const |> fst
    val cert = translate_definition def
    val _ = null (hyp cert) orelse raise mk_HOL_ERR "ml_monad_oracleLib"
              "oracle_translate" (name ^ ": undischarged assumptions")
    val state = ml_translatorLib.get_ml_prog_state ()
    val cert = INST [argument 0 (concl cert) |-> ml_progLib.get_env state] cert
    val (parameter,body) = astSyntax.dest_Fun (argument 1 (concl cert))
    val refinement = REWRITE_RULE [ml_translatorTheory.Eval_Fun_rw] cert
    val value_name = ml_translatorLib.find_const_name (name ^ "_v")
    val _ = ml_translatorLib.ml_prog_update
      (ml_progLib.add_Dlet_Fun ``NoLocs`` (mlstringSyntax.mk_mlstring name)
         parameter body value_name)
    val value_def = hd (ml_translatorLib.get_curr_v_defs ())
  in
    REWRITE_RULE [GSYM value_def] refinement
  end
end
