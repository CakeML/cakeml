structure repl_computeLib = struct
open preamble repl_funTheory ASCIInumbersLib intLib
open AstTheory inferTheory CompilerTheory compilerTerminationTheory bytecodeEvalTheory
open repl_computeTheory;

val t_unify_wfs = prove(
 ``t_wfs s ∧ (t_unify s t1 t2 = SOME sx) ==> t_wfs sx``,
 metis_tac[unifyTheory.t_unify_unifier])

val t_wfs_FEMPTY = prove(
  ``t_wfs FEMPTY``,
  rw[unifyTheory.t_wfs_def])

val _ = computeLib.add_funs
  [unifyTheory.t_walk_eqn
  ,unifyTheory.t_ext_s_check_eqn
  ,computeLib.lazyfy_thm(bytecodeEvalTheory.bc_eval_def)
  ]
val _ = computeLib.add_funs[listTheory.SUM] (* why isn't this in there already !? *)

val db = ref (Net.insert (rand(concl(t_wfs_FEMPTY)),t_wfs_FEMPTY) Net.empty)
fun t_unify_conv tm = let
  val (_,[s,t1,t2]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPECL [t1,t2] (MATCH_MP unifyTheory.t_unify_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  val th3 = TRANS th1 th2
  val res = rhs(concl th2)
  val _ = if optionSyntax.is_some res then
          db := Net.insert (rand res,PROVE[wfs_s,t_unify_wfs,th3]``^(rator(concl wfs_s)) ^(rand res)``) (!db)
          else ()
  in th3 end
fun t_vwalk_conv tm = let
  val (_,[s,t]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPEC t (MATCH_MP unifyTheory.t_vwalk_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end
fun t_oc_conv tm = let
  val (_,[s,t1,t2]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPECL [t1,t2] (MATCH_MP unifyTheory.t_oc_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end
fun t_walkstar_conv tm = let
  val (_,[s,t]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPEC t (MATCH_MP unifyTheory.t_walkstar_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end

val _ = computeLib.add_convs
[(``t_unify``,3,t_unify_conv)
,(``t_vwalk``,2,t_vwalk_conv)
,(``t_walkstar``,2,t_walkstar_conv)
,(``t_oc``,3,t_oc_conv)
]

(* add repl definitions to the compset *)

val RES_FORALL_set = prove(``RES_FORALL (set ls) P = EVERY P ls``,rw[RES_FORALL_THM,listTheory.EVERY_MEM])

val bc_fetch_aux_zero = prove(
``∀ls n. bc_fetch_aux ls (K 0) n = el_check n (FILTER ($~ o is_Label) ls)``,
Induct >> rw[CompilerLibTheory.el_check_def] >> fs[] >> fsrw_tac[ARITH_ss][] >>
simp[rich_listTheory.EL_CONS,arithmeticTheory.PRE_SUB1])

val _ = computeLib.add_funs
  [ElabTheory.elab_p_def
  ,CompilerLibTheory.find_index_def
  ,CompilerLibTheory.the_def
  ,CompilerLibTheory.lunion_def
  ,CompilerLibTheory.lshift_def
  ,pat_bindings_def
  ,compile_news_def
  ,ToBytecodeTheory.compile_varref_def
  ,CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)compile_def
  ,label_closures_def
  ,remove_mat_var_def
  ,ToIntLangTheory.remove_mat_vp_def
  ,mkshift_def
  ,ToBytecodeTheory.cce_aux_def
  ,exp_to_Cexp_def
  ,ToIntLangTheory.pat_to_Cpat_def
  ,ToIntLangTheory.Cpat_vars_def
  ,generalise_def
  ,RES_FORALL_set
  ,bc_fetch_aux_zero
  ]

val _ = let
  open computeLib
in
  set_skip the_compset ``evalcase_CASE`` (SOME 1);
  set_skip the_compset ``list_CASE`` (SOME 1);
  set_skip the_compset ``option_CASE`` (SOME 1);
  set_skip the_compset ``sum_CASE`` (SOME 1);
  set_skip the_compset ``id_CASE`` (SOME 1);
  set_skip the_compset ``tc0_CASE`` (SOME 1);
  set_skip the_compset ``t_CASE`` (SOME 1);
  set_skip the_compset ``lit_CASE`` (SOME 1);
  set_skip the_compset ``pat_CASE`` (SOME 1);
  set_skip the_compset ``lop_CASE`` (SOME 1);
  set_skip the_compset ``opb_CASE`` (SOME 1);
  set_skip the_compset ``opn_CASE`` (SOME 1);
  set_skip the_compset ``op_CASE`` (SOME 1);
  set_skip the_compset ``uop_CASE`` (SOME 1);
  set_skip the_compset ``error_CASE`` (SOME 1);
  set_skip the_compset ``exp_CASE`` (SOME 1);
  set_skip the_compset ``dec_CASE`` (SOME 1);
  set_skip the_compset ``spec_CASE`` (SOME 1);
  set_skip the_compset ``top_CASE`` (SOME 1);
  set_skip the_compset ``ast_t_CASE`` (SOME 1);
  set_skip the_compset ``ast_pat_CASE`` (SOME 1);
  set_skip the_compset ``ast_exp_CASE`` (SOME 1);
  set_skip the_compset ``ast_dec_CASE`` (SOME 1);
  set_skip the_compset ``ast_spec_CASE`` (SOME 1);
  set_skip the_compset ``ast_top_CASE`` (SOME 1);
  set_skip the_compset ``bc_stack_op_CASE`` (SOME 1);
  set_skip the_compset ``bc_inst_CASE`` (SOME 1);
  set_skip the_compset ``compiler_state_CASE`` (SOME 1);
  set_skip the_compset ``Cpat_CASE`` (SOME 1);
  set_skip the_compset ``exp_to_Cexp_state_CASE`` (SOME 1);
  set_skip the_compset ``compiler_result_CASE`` (SOME 1);
  set_skip the_compset ``call_context_CASE`` (SOME 1);
  set_skip the_compset ``ctbind_CASE`` (SOME 1);
  set_skip the_compset ``COND`` (SOME 1)
end

val eval_compile_primitives = EVAL ``compile_primitives``
val _ = computeLib.del_funs[compile_primitives_def]
val _ = computeLib.add_funs[eval_compile_primitives]
val eval_initial_repl_fun_state = EVAL ``initial_repl_fun_state``
val _ = PolyML.fullGC();
(* too slow!
val eval_initial_bc_state = EVAL ``initial_bc_state``
*)
val _ = computeLib.del_funs[initial_repl_fun_state_def,initial_bc_state_def]
val _ = computeLib.add_funs[eval_initial_repl_fun_state(*,eval_initial_bc_state*)]

val eval_C_main_loop = EVAL``C_main_loop i (s,bs)``
val _ = computeLib.del_funs[main_loop_def]
val _ = computeLib.add_funs[GSYM C_main_loop_def]
val _ = computeLib.set_skip computeLib.the_compset ``C_main_loop`` (SOME 1)
end
