open preamble repl_funTheory wordsLib intLib
open AstTheory inferTheory CompilerTheory compilerTerminationTheory bytecodeEvalTheory
(* need wordsLib to make EVAL work on toString - this should be fixed in HOL *)
(* need intLib to EVAL double negation of ints *)
val _ = new_theory"repl_funExamples"

(* stuff for proving the wfs condition on t_unify etc. *)

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

(*
  val tm = ``t_unify FEMPTY (Infer_Tvar_db 0) (Infer_Tuvar 3)``
  EVAL tm
*)

(* alternative cheating method:
  val cheat_wfs = let val wfs = (mk_thm([],``t_wfs s``)) in
  fn th => PROVE_HYP wfs (UNDISCH(SPEC_ALL th))
  end
  val _ = computeLib.add_funs
  [cheat_wfs unifyTheory.t_unify_eqn
  ,cheat_wfs unifyTheory.t_vwalk_eqn
  ,cheat_wfs unifyTheory.t_oc_eqn
  ]
*)

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
  ,compile_shadows_def
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

val input = ``"val x = true; val y = 2;"``

(* intermediate steps:
  val (tokens,rest_of_input) = EVAL ``lex_until_toplevel_semicolon ^input`` |> concl |> rhs |> rand |> pairSyntax.dest_pair
  val ast_prog = EVAL ``mmlParse$parse ^tokens`` |> concl |> rhs |> rand
  val s = ``init_repl_fun_state``

  val prog = EVAL ``elab_prog ^s.rtypes ^s.rctors ^s.rbindings ^ast_prog``
    |> concl |> rhs |> rand |> rand |> rand

  val res = EVAL ``FST (infer_prog ^s.rmenv ^s.rcenv ^s.rtenv ^prog init_infer_state)``

  val res = EVAL  ``parse_elaborate_typecheck_compile ^tokens init_repl_fun_state``

  val (code,new_s) = res |> concl |> rhs |> rand |> pairSyntax.dest_pair

  val bs = EVAL ``install_code ^code init_bc_state`` |> concl |> rhs

  val new_bs = EVAL ``bc_eval ^bs`` |> concl |> rhs |> rand

  val res = EVAL ``print_result ^new_s ^new_bs`` |> concl |> rhs

  val (tokens,rest_of_input) = EVAL ``lex_until_toplevel_semicolon ^rest_of_input`` |> concl |> rhs |> rand |> pairSyntax.dest_pair
  val ast_prog = EVAL ``mmlParse$parse ^tokens`` |> concl |> rhs |> rand
  val s = new_s
  val bs = new_bs

  val prog = EVAL ``elab_prog ^s.rtypes ^s.rctors ^s.rbindings ^ast_prog``
    |> concl |> rhs |> rand |> rand |> rand

  val res = EVAL  ``parse_elaborate_typecheck_compile ^tokens init_repl_fun_state``

  val (code,new_s) = res |> concl |> rhs |> rand |> pairSyntax.dest_pair

  val bs = EVAL ``install_code ^code ^bs`` |> concl |> rhs

  val new_bs = EVAL ``bc_eval ^bs`` |> concl |> rhs |> rand

  val res = EVAL ``print_result ^new_s ^new_bs`` |> concl |> rhs
*)

val ex1 = time EVAL ``repl_fun ^input``
val _ = save_thm("ex1",ex1)

val input = ``"fun f x = x + 3; f 2;"``

(* intermediate steps:
  val (tokens,rest_of_input) = EVAL ``lex_until_toplevel_semicolon ^input`` |> concl |> rhs |> rand |> pairSyntax.dest_pair
  val ast_prog = EVAL ``mmlParse$parse ^tokens`` |> concl |> rhs |> rand
  val s = ``init_repl_fun_state``

  val prog = EVAL ``elab_prog ^s.rtypes ^s.rctors ^s.rbindings ^ast_prog``
    |> concl |> rhs |> rand |> rand |> rand

  val res = EVAL ``FST (infer_prog ^s.rmenv ^s.rcenv ^s.rtenv ^prog init_infer_state)``

  val res = EVAL  ``parse_elaborate_typecheck_compile ^tokens init_repl_fun_state``

  val (code,new_s) = res |> concl |> rhs |> rand |> pairSyntax.dest_pair

  val bs = EVAL ``install_code ^code init_bc_state`` |> concl |> rhs

  val new_bs = EVAL ``bc_eval ^bs`` |> concl |> rhs |> rand

  val res = EVAL ``print_result ^new_s ^new_bs`` |> concl |> rhs

  val (tokens,rest_of_input) = EVAL ``lex_until_toplevel_semicolon ^rest_of_input`` |> concl |> rhs |> rand |> pairSyntax.dest_pair
  val ast_prog = EVAL ``mmlParse$parse ^tokens`` |> concl |> rhs |> rand
  val s = new_s
  val bs = new_bs

  val prog = EVAL ``elab_prog ^s.rtypes ^s.rctors ^s.rbindings ^ast_prog``
    |> concl |> rhs |> rand |> rand |> rand

  val res = EVAL  ``parse_elaborate_typecheck_compile ^tokens ^new_s``

  val (code,new_s) = res |> concl |> rhs |> rand |> pairSyntax.dest_pair

  val bs = EVAL ``install_code ^code ^bs`` |> concl |> rhs

  val new_bs = EVAL ``bc_eval ^bs`` |> concl |> rhs |> rand

  val res = EVAL ``print_result ^new_s ^new_bs`` |> concl |> rhs
*)

val ex2 = time EVAL ``repl_fun ^input``
val _ = save_thm("ex2",ex2)

val input = ``"datatype foo = C of int | D of bool; fun f x = case x of (C i) => i+1 | D _ => 0; f (C (3));"``

val ex3 = time EVAL ``repl_fun ^input``
val _ = save_thm("ex3",ex3)

val _ = export_theory()
