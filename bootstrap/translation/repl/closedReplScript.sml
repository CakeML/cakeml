open HolKernel boolLib bossLib compute_compilerLib
val _ = new_theory"closedRepl"

val _ = max_print_depth := 10;

val eval_fvs = computeLib.CBV_CONV (the_free_vars_compset())

local
   (* vt100 escape string *)
   val ESC = String.str (Char.chr 0x1B)
in
   val inPlaceEcho =
      if !Globals.interactive
         then fn s => print ("\n" ^ s)
      else fn s => print (ESC ^ "[1K" ^ "\n" ^ ESC ^ "[A" ^ s)
end

val FV_decs_replModule_decls = save_thm("FV_decs_replModule_decls",let
  val input = ``FV_decs replModule_decls``
  val th =
    (PURE_ONCE_REWRITE_CONV[replModuleTheory.replModule_decls] THENC
     PURE_REWRITE_CONV [evalPropsTheory.FV_decs_def,listTheory.MAP,
       pairTheory.FST,pairTheory.SND,
       pred_setTheory.INSERT_UNION_EQ,
       pred_setTheory.UNION_EMPTY,listTheory.LIST_TO_SET_THM,
       evalPropsTheory.new_dec_vs_def,astTheory.pat_bindings_def])
         input
  val tm = th |> concl |> rand
  val tms = find_terms (can (match_term ``FV_dec c``)) tm
  val max = length tms
  val _ = print ("\nEvaluating FV_dec " ^ (int_to_string max) ^ " times.\n")
  val n = ref max
  val FV_dec_pat = ``FV_dec x``
  fun FV_dec_conv tm =
    if can (match_term FV_dec_pat) tm then let
      val th = eval_fvs tm
      val _ = (n := !n - 1)
      val _ = (if (!n) mod 5 = 0 then
                 inPlaceEcho (" ... " ^ (int_to_string (!n)) ^ " left to evaluate")
               else print "")
      in th end
    else NO_CONV tm
  val th = CONV_RULE (RAND_CONV (TOP_DEPTH_CONV FV_dec_conv)) th
  val _ = print "\nOnly set operations left to evaluate.\n"
  val th = CONV_RULE (RAND_CONV (PURE_REWRITE_CONV [pred_setTheory.UNION_EMPTY,
            pred_setTheory.INSERT_UNION_EQ,
            pred_setTheory.DIFF_INSERT,
            pred_setTheory.EMPTY_DIFF,
            pred_setTheory.DIFF_EMPTY,
            pred_setTheory.EMPTY_DELETE])) th
  val INSERT_DELETE_pat = ``(x INSERT s) DELETE y``
  val DELETE_DELETE_pat = ``(s DELETE x) DELETE y``
  val IF_T = prove(``(if T then x else y) = x``,SIMP_TAC std_ss [])
  val IF_F = prove(``(if F then x else y) = y``,SIMP_TAC std_ss [])
  fun push_delete_conv tm =
    if can (match_term DELETE_DELETE_pat) tm then
      (REWR_CONV pred_setTheory.DELETE_COMM
       THENC (RATOR_CONV o RAND_CONV) push_delete_conv) tm
    else if can (match_term INSERT_DELETE_pat) tm then let
      val (s,x) = pred_setSyntax.dest_delete tm
      val (y,s) = pred_setSyntax.dest_insert s
      in if aconv x y then
          (REWR_CONV pred_setTheory.DELETE_INSERT
           THENC (RATOR_CONV o RATOR_CONV o RAND_CONV) eval_fvs
           THENC REWR_CONV IF_T THENC push_delete_conv) tm
         else
          (REWR_CONV pred_setTheory.DELETE_INSERT
           THENC (RATOR_CONV o RATOR_CONV o RAND_CONV) eval_fvs
           THENC REWR_CONV IF_F THENC RAND_CONV push_delete_conv) tm
      end
    else TRY_CONV (REWR_CONV pred_setTheory.EMPTY_DELETE) tm
  val th = CONV_RULE (RAND_CONV (REPEATC push_delete_conv)) th
  in th end);

val all_env_dom_init =
  ``all_env_dom ((THE prim_sem_env).sem_envM,
                 (THE prim_sem_env).sem_envC,
                 (THE prim_sem_env).sem_envE)``
  |> (REWRITE_CONV [initSemEnvTheory.prim_sem_env_eq] THENC
      SIMP_CONV std_ss [evalPropsTheory.all_env_dom_def] THENC
      SIMP_CONV (srw_ss()) [pred_setTheory.EXTENSION] THENC
      EVAL)

val closed_top_REPL = store_thm("closed_top_REPL",
  ``closed_top ((THE prim_sem_env).sem_envM,
                (THE prim_sem_env).sem_envC,
                (THE prim_sem_env).sem_envE)
               (Tmod "REPL" NONE replModule_decls)``,
  lcsymtacs.simp[free_varsTheory.closed_top_def,all_env_dom_init,
                 FV_decs_replModule_decls])

val _ = export_theory()
