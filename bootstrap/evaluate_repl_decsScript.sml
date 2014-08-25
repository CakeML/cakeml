open HolKernel boolLib bossLib lcsymtacs pairSyntax listTheory miscLib
open ml_translatorTheory bigStepTheory terminationTheory
open ml_repl_moduleTheory

val _ = new_theory"evaluate_repl_decs"

(* Environment produced by evaluating the repl decs *)

val (repl_store,repl_res) =
  CONJUNCT1 evaluate_repl_decs
  |> concl |> strip_comb
  |> snd |> last
  |> dest_pair
val (x,y) = dest_pair repl_res
val y = rand y
val (y,z) = dest_pair y
val repl_all_env = ``^y,merge_envC ^x (THE prim_sem_env).sem_envC,(THE prim_sem_env).sem_envE``

val repl_decs_cs =
  let
    val cs = listSimps.list_compset()
    val _ = computeLib.add_thms[ml_repl_module_decls] cs
    val _ = computeLib.add_thms[rich_listTheory.LASTN_compute,
                                evalPropsTheory.ctors_of_dec_def,
                                evalPropsTheory.ctors_of_tdef_def] cs
    val _ = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:dec``))
  in
    cs
  end

val last_3_decs = save_thm("last_3_decs",
  computeLib.CBV_CONV repl_decs_cs ``LASTN 3 ml_repl_module_decls``)

val append_3 = save_thm("append_3",
  rich_listTheory.APPEND_BUTLASTN_LASTN |> Q.ISPECL[`3:num`,`ml_repl_module_decls`]
  |> UNDISCH |> SYM |> REWRITE_RULE[last_3_decs]
  |> prove_hyps_by(CONV_TAC(computeLib.CBV_CONV repl_decs_cs)))

val iloc_repl_env_exist =
  MATCH_MP evalPropsTheory.evaluate_Tmod_last3 (CONJUNCT1 evaluate_repl_decs)
  |> SIMP_RULE (srw_ss())[]
  |> C MATCH_MP append_3
  |> REWRITE_RULE[GSYM append_3]

val repl_env_def = new_specification("repl_env_def",["iloc","repl_env"],iloc_repl_env_exist)

val sum_idx = ``21:num``
val sym_idx = ``77:num``
val el_sum = computeLib.CBV_CONV repl_decs_cs ``EL ^sum_idx ml_repl_module_decls``
val take_sum = computeLib.CBV_CONV repl_decs_cs ``TAKE ^sum_idx ml_repl_module_decls``
val drop_sum = computeLib.CBV_CONV repl_decs_cs ``DROP (^sum_idx + 1) ml_repl_module_decls``
val el_sym = computeLib.CBV_CONV repl_decs_cs ``EL ^sym_idx ml_repl_module_decls``
val take_sym = computeLib.CBV_CONV repl_decs_cs ``TAKE ^sym_idx ml_repl_module_decls``
val drop_sym = computeLib.CBV_CONV repl_decs_cs ``DROP (^sym_idx + 1) ml_repl_module_decls``
val length = save_thm("length_repl_decs",computeLib.CBV_CONV repl_decs_cs ``LENGTH ml_repl_module_decls``)
val tdefs_sum = prove(
  ``ml_repl_module_decls = ^(lhs(concl take_sum)) ++ [^(lhs(concl el_sum))] ++ ^(lhs(concl drop_sum))``,
  assume_tac length >>
  rw[LIST_EQ_REWRITE] >>
  Cases_on`x < ^sum_idx` >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_TAKE] >>
  Cases_on`x = ^sum_idx` >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
  simp[rich_listTheory.EL_DROP])
val tdefs_sym = prove(
  ``ml_repl_module_decls = ^(lhs(concl take_sym)) ++ [^(lhs(concl el_sym))] ++ ^(lhs(concl drop_sym))``,
  assume_tac length >>
  rw[LIST_EQ_REWRITE] >>
  Cases_on`x < ^sym_idx` >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_TAKE] >>
  Cases_on`x = ^sym_idx` >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
  simp[rich_listTheory.EL_DROP])

val sum_tags_exist = save_thm("sum_tags_exist",
  MATCH_MP evalPropsTheory.evaluate_Tmod_tys (CONJUNCT1 evaluate_repl_decs)
  |> C MATCH_MP (REWRITE_RULE[el_sum]tdefs_sum) |> GEN_ALL
  |> SIMP_RULE(srw_ss()++boolSimps.DNF_ss)[GSYM AND_IMP_INTRO]
  |> CONJUNCTS
  |> List.map (CONV_RULE(LAND_CONV(PURE_REWRITE_CONV[drop_sum]THENC(computeLib.CBV_CONV repl_decs_cs))))
  |> List.map (SIMP_RULE(srw_ss())[])
  |> LIST_CONJ)

val sym_tags_exist = save_thm("sym_tags_exist",
  MATCH_MP evalPropsTheory.evaluate_Tmod_tys (CONJUNCT1 evaluate_repl_decs)
  |> C MATCH_MP (REWRITE_RULE[el_sym]tdefs_sym) |> GEN_ALL
  |> SIMP_RULE(srw_ss()++boolSimps.DNF_ss)[]
  |> CONJUNCTS
  |> List.map (CONV_RULE(LAND_CONV(PURE_REWRITE_CONV[drop_sym]THENC(computeLib.CBV_CONV repl_decs_cs))))
  |> List.map (SIMP_RULE(srw_ss())[])
  |> LIST_CONJ)

(* Define the compiler calls to bootstrap *)

val compile_repl_decs_def = zDefine`
  compile_repl_decs = compile_top NONE ((FST(THE prim_env)).comp_rs) (Tmod "REPL" NONE ml_repl_module_decls)`

val call_dec = ``Tdec (Dlet (Plit Unit) (App Opapp [Var(Long"REPL""call_repl_step"); Lit Unit]))``

val compile_call_repl_step_def = zDefine`
  compile_call_repl_step = compile_special (FST compile_repl_decs) ^call_dec`

(* Effect of evaluating the call *)

val update_io_def  = Define`
  update_io inp out ((c,s),x,y) =
    ((c,LUPDATE (Refv out) (iloc+1) (LUPDATE (Refv inp) iloc s)),x,y)`

val evaluate_call_repl_step = store_thm("evaluate_call_repl_step",
  ``∀x inp out. INPUT_TYPE x inp ⇒
      ∃out'. OUTPUT_TYPE (basis_repl_step x) out' ∧
      evaluate_top F ^repl_all_env (update_io inp out ^repl_store) ^call_dec
        (update_io inp out' ^repl_store, ([],[]), Rval ([],[]))``,
  rw[evaluate_top_cases,evaluate_dec_cases,Once evaluate_cases,libTheory.emp_def] >>
  rw[Once evaluate_cases,semanticPrimitivesTheory.lookup_var_id_def] >>
  rw[Once evaluate_cases,astTheory.pat_bindings_def] >>
  mp_tac(CONJUNCT2 evaluate_repl_decs) >>
  simp[can_lookup_def] >> strip_tac >>
  strip_assume_tac repl_env_def >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[semanticPrimitivesTheory.all_env_to_cenv_def,libTheory.merge_def] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[libPropsTheory.lookup_append] >> fs[] >>
  rw[semanticPrimitivesTheory.do_opapp_def] >>
  simp[PULL_EXISTS] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  simp[PULL_EXISTS] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[libPropsTheory.lookup_append] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  simp[PULL_EXISTS] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.lookup_var_id_def,libTheory.bind_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  rw[semanticPrimitivesTheory.do_app_def] >>
  rw[Once (CONJUNCT2 evaluate_cases)] >>
  fs[Arrow_def,AppReturns_def] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qx_choose_then`out'`strip_assume_tac) >>
  qexists_tac`out'` >> simp[] >>
  simp[semanticPrimitivesTheory.store_lookup_def] >>
  simp[semanticPrimitivesTheory.store_assign_def] >>
  Cases_on`Tmod_state"REPL"ml_repl_module_decls`>>
  simp[update_io_def,PULL_EXISTS] >>
  qexists_tac`Litv Unit` >>
  simp[pmatch_def] >>
  fs[evaluate_closure_def] >>
  simp[EL_LUPDATE] >>
  imp_res_tac evaluate_empty_store_IMP >>
  Q.PAT_ABBREV_TAC`ss:v count_store = (xx,LUPDATE  a b c)` >>
  first_x_assum(qspec_then`ss`strip_assume_tac) >>
  fs[Abbr`ss`] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[EL_LUPDATE] >>
  simp[semanticPrimitivesTheory.store_v_same_type_def] >>
  rw[LIST_EQ_REWRITE,EL_LUPDATE] )

val _ = export_theory()
