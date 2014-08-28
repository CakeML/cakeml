open HolKernel boolLib bossLib compute_free_varsLib
val _ = new_theory"closedReplDecs"

val eval_fvs = computeLib.CBV_CONV (the_free_vars_compset())
val FV_decs_ml_repl_module_decls = save_thm("FV_decs_ml_repl_module_decls",
  time (PURE_ONCE_REWRITE_CONV[ml_repl_moduleTheory.ml_repl_module_decls] THENC eval_fvs)
  ``FV_decs ml_repl_module_decls``)

val all_env_dom_init =
  ``all_env_dom ((THE prim_sem_env).sem_envM,(THE prim_sem_env).sem_envC,(THE prim_sem_env).sem_envE)``
  |> (REWRITE_CONV [initSemEnvTheory.prim_sem_env_eq] THENC
      SIMP_CONV std_ss [evalPropsTheory.all_env_dom_def,libTheory.lookup_def] THENC
      SIMP_CONV (srw_ss()) [pred_setTheory.EXTENSION] THENC
      EVAL)

val closed_top_REPL = store_thm("closed_top_REPL",
  ``closed_top ((THE prim_sem_env).sem_envM,(THE prim_sem_env).sem_envC,(THE prim_sem_env).sem_envE) (Tmod "REPL" NONE ml_repl_module_decls)``,
  lcsymtacs.simp[free_varsTheory.closed_top_def,all_env_dom_init,FV_decs_ml_repl_module_decls])

val _ = export_theory()
