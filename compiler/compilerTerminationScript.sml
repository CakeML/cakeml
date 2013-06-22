open HolKernel boolLib boolSimps bossLib Defn pairTheory pred_setTheory listTheory finite_mapTheory state_transformerTheory lcsymtacs
open terminationTheory CompilerLibTheory CompilerPrimitivesTheory IntLangTheory ToIntLangTheory ToBytecodeTheory CompilerTheory PrinterTheory BytecodeTheory
val _ = new_theory "compilerTermination"

(* size helper theorems *)

val MEM_pair_MAP = store_thm(
"MEM_pair_MAP",
``MEM (a,b) ls ==> MEM a (MAP FST ls) /\ MEM b (MAP SND ls)``,
rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[])

val tac = Induct >- rw[Cexp_size_def,Cpat_size_def,Cv_size_def,ov_size_def] >> srw_tac [ARITH_ss][Cexp_size_def,Cpat_size_def,Cv_size_def,ov_size_def]
fun tm t1 t2 =  ``∀ls. ^t1 ls = SUM (MAP ^t2 ls) + LENGTH ls``
fun size_thm name t1 t2 = store_thm(name,tm t1 t2,tac)
val Cexp1_size_thm = size_thm "Cexp1_size_thm" ``Cexp1_size`` ``Cexp2_size``
val Cexp4_size_thm = size_thm "Cexp4_size_thm" ``Cexp4_size`` ``Cexp_size``
val Cpat1_size_thm = size_thm "Cpat1_size_thm" ``Cpat1_size`` ``Cpat_size``
val Cv1_size_thm = size_thm "Cv1_size_thm" ``Cv1_size`` ``Cv_size``
val ov1_size_thm = size_thm "ov1_size_thm" ``ov1_size`` ``ov_size``

val SUM_MAP_Cexp3_size_thm = store_thm(
"SUM_MAP_Cexp3_size_thm",
``∀env. SUM (MAP Cexp3_size env) =
  SUM (MAP FST env)
+ SUM (MAP Cexp_size (MAP SND env))
+ LENGTH env``,
Induct >- rw[Cexp_size_def] >> Cases >>
srw_tac[ARITH_ss][Cexp_size_def])

val SUM_MAP_Cexp2_size_thm = store_thm("SUM_MAP_Cexp2_size_thm",
  ``∀defs. SUM (MAP Cexp2_size defs) =
    SUM (MAP (option_size (pair_size (λx. x) (pair_size (list_size ccbind_size) (pair_size (list_size (λx. x)) (list_size (λx. x))))) o FST) defs) +
    SUM (MAP (Cexp3_size o SND) defs) +
    LENGTH defs``,
  Induct >- rw[Cexp_size_def] >>
  qx_gen_tac`h` >> PairCases_on`h` >>
  Cases_on`h0`>>srw_tac[ARITH_ss][Cexp_size_def,basicSizeTheory.pair_size_def,arithmeticTheory.ADD1,basicSizeTheory.option_size_def])

val list_size_thm = store_thm(
"list_size_thm",
``∀f ls. list_size f ls = SUM (MAP f ls) + LENGTH ls``,
gen_tac >> Induct >> srw_tac[ARITH_ss][list_size_def])

val bc_value1_size_thm = store_thm(
"bc_value1_size_thm",
``∀ls. bc_value1_size ls = SUM (MAP bc_value_size ls) + LENGTH ls``,
Induct >- rw[BytecodeTheory.bc_value_size_def] >>
srw_tac [ARITH_ss][BytecodeTheory.bc_value_size_def])

(* termination proofs *)

fun register name (def,ind) = let
  val _ = save_thm(name^"_def", def)
  val _ = save_thm(name^"_ind", ind)
  val _ = computeLib.add_persistent_funs [name^"_def"]
in (def,ind) end

val (free_vars_def, free_vars_ind) = register "free_vars" (
  tprove_no_defn ((free_vars_def,free_vars_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL e => Cexp_size e
    | INR (INL es) => Cexp4_size es
    | INR (INR (INL (n,defs))) => Cexp1_size defs
    | INR (INR (INR (n,def))) => Cexp2_size def)`))

val (no_closures_def, no_closures_ind) = register "no_closures" (
  tprove_no_defn ((no_closures_def, no_closures_ind),
  WF_REL_TAC `measure Cv_size` >>
  rw[Cv1_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `Cv_size` mp_tac) >>
  srw_tac[ARITH_ss][]))

val (Cv_to_ov_def,Cv_to_ov_ind) = register "Cv_to_ov" (
  tprove_no_defn ((Cv_to_ov_def,Cv_to_ov_ind),
  WF_REL_TAC `measure (Cv_size o SND o SND)` >>
  rw[Cv1_size_thm] >>
  Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))

val (v_to_ov_def,v_to_ov_ind) = register "v_to_ov" (
  tprove_no_defn ((v_to_ov_def,v_to_ov_ind),
  WF_REL_TAC `measure (v_size o SND)` >>
  rw[v3_size_thm] >>
  Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))

val (mkshift_def,mkshift_ind) = register "mkshift" (
  tprove_no_defn ((mkshift_def,mkshift_ind),
  WF_REL_TAC `measure (Cexp_size o SND o SND)` >>
  srw_tac[ARITH_ss][Cexp4_size_thm,Cexp1_size_thm,SUM_MAP_Cexp3_size_thm] >>
  Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][] >>
  imp_res_tac MEM_pair_MAP >>
  Q.ISPEC_THEN`Cexp2_size`imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][Cexp_size_def]))

val _ = register "remove_mat_var" (
  tprove_no_defn ((remove_mat_var_def,remove_mat_var_ind),
  WF_REL_TAC `measure (LENGTH o SND)` >> rw[]))

val (exp_to_Cexp_def,exp_to_Cexp_ind) = register "exp_to_Cexp" (
  tprove_no_defn ((exp_to_Cexp_def,exp_to_Cexp_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL (_,e) => exp_size e
    | INR (INL (_,defs)) => exp1_size defs
    | INR (INR (INL (_,pes))) => exp4_size pes
    | INR (INR (INR (_,es))) => exp6_size es)`))

val (v_to_Cv_def,v_to_Cv_ind) = register "v_to_Cv" (
  tprove_no_defn ((v_to_Cv_def,v_to_Cv_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL (_,_,v) => v_size v
    | INR (INL (_,_, vs)) => v3_size vs
    | INR (INR (_,_, env)) => v1_size env)`))

val (compile_envref_def, compile_envref_ind) = register "compile_envref" (
  tprove_no_defn ((compile_envref_def, compile_envref_ind),
  WF_REL_TAC `measure (λp. case p of (_,_,CCEnv _) => 0 | (_,_,CCRef _) => 1)`))

val (compile_def, compile_ind) = register "compile" (
  tprove_no_defn ((compile_def, compile_ind),
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
       | INL (_,env,t,sz,s,e) => (Cexp_size e, 3:num)
       | INR (INL (_,env,t,sz,e,n,s,0))=> (Cexp_size e, 4)
       | INR (INL (_,env,t,sz,e,n,s,ns))=> (Cexp_size e + ns, 1)
       | INR (INR (_,env,sz,s,es))=> (SUM (MAP Cexp_size es), 3 + LENGTH es)) ` >>
  srw_tac[ARITH_ss][] >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp_size_def,list_size_thm,SUM_MAP_Cexp3_size_thm] >>
  BasicProvers.CASE_TAC >> fsrw_tac[ARITH_ss][] >>
  BasicProvers.CASE_TAC >> fsrw_tac[ARITH_ss][]))

val _ = register "num_fold" (
  tprove_no_defn ((num_fold_def,num_fold_ind),
  WF_REL_TAC `measure (SND o SND)`))

(* TODO: make zero_ temporary (don't store/export) *)

val zero_vars_def = tDefine "zero_vars"`
  (zero_vars (CRaise e) = CRaise (zero_vars e)) ∧
  (zero_vars (CHandle e1 e2) = CHandle (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CVar _) = CVar (Short 0)) ∧
  (zero_vars (CLit c) = CLit c) ∧
  (zero_vars (CCon cn es) = CCon cn (zero_vars_list es)) ∧
  (zero_vars (CTagEq e n) = CTagEq (zero_vars e) n) ∧
  (zero_vars (CProj e n) = CProj (zero_vars e) n) ∧
  (zero_vars (CLet e1 e2) = CLet (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CLetrec defs e) = CLetrec (zero_vars_defs defs) (zero_vars e)) ∧
  (zero_vars (CCall ck e es) = CCall ck (zero_vars e) (zero_vars_list es)) ∧
  (zero_vars (CPrim1 p1 e2) = CPrim1 p1 (zero_vars e2)) ∧
  (zero_vars (CPrim2 p2 e1 e2) = CPrim2 p2 (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CUpd e1 e2) = CUpd (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CIf e1 e2 e3) = CIf (zero_vars e1) (zero_vars e2) (zero_vars e3)) ∧
  (zero_vars_list [] = []) ∧
  (zero_vars_list (e::es) = (zero_vars e)::(zero_vars_list es)) ∧
  (zero_vars_defs [] = []) ∧
  (zero_vars_defs (def::defs) = (zero_vars_def def)::(zero_vars_defs defs)) ∧
  (zero_vars_def (NONE,(xs,b)) = (NONE,(xs,zero_vars b))) ∧
  (zero_vars_def (SOME x,y) = (SOME x,y))`
  (WF_REL_TAC`inv_image $< (λx. case x of INL e => Cexp_size e |
    INR (INL es) => Cexp4_size es |
    INR (INR (INL defs)) => Cexp1_size defs |
    INR(INR(INR def)) => Cexp2_size def)`)

val zero_vars_list_MAP = store_thm("zero_vars_list_MAP",
  ``(∀ls. (zero_vars_list ls = MAP (zero_vars) ls)) ∧
    (∀ls. (zero_vars_defs ls = MAP (zero_vars_def) ls))``,
  conj_tac >> Induct >> rw[zero_vars_def])
val _ = export_rewrites["zero_vars_def","zero_vars_list_MAP"]

val zero_vars_mkshift = store_thm("zero_vars_mkshift",
  ``∀f k e. zero_vars (mkshift f k e) = zero_vars e``,
  ho_match_mp_tac mkshift_ind >>
  rw[mkshift_def,MAP_MAP_o,combinTheory.o_DEF,LET_THM] >>
  lrw[MAP_EQ_f,UNCURRY] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >> rw[] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fsrw_tac[ARITH_ss][])
val _ = export_rewrites["zero_vars_mkshift"]

val (label_closures_def,label_closures_ind) = register "label_closures" (
  tprove_no_defn ((label_closures_def, label_closures_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (ez,j,e) => Cexp_size (zero_vars e)
    | INR (INL (ez,j,es)) => Cexp4_size (zero_vars_list es)
    | INR (INR (ez,j,nz,k,defs)) => SUM (MAP Cexp2_size (MAP (zero_vars_def o ($, NONE)) defs)))` >>
  srw_tac[ARITH_ss][Cexp_size_def,SUM_MAP_Cexp3_size_thm,Cexp1_size_thm,SUM_MAP_Cexp2_size_thm,basicSizeTheory.pair_size_def] >- (
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    qmatch_abbrev_tac`a + (b + c) < d + ((2 * f) + (g + (h + 1:num)))` >>
    qsuff_tac`a ≤ f ∧ (b = 0) ∧ (c ≤ h)` >- simp[] >>
    unabbrev_all_tac >>
    conj_tac >- simp[rich_listTheory.LENGTH_FILTER_LEQ] >>
    conj_tac >- (
      simp[SUM_eq_0,MEM_MAP,MEM_FILTER] >>
      qx_gen_tac`a` >> fsrw_tac[DNF_ss][] >>
      qx_gen_tac`b` >>
      PairCases_on`b`>>simp[]>>
      simp[basicSizeTheory.option_size_def]) >>
    qmatch_abbrev_tac`SUM (MAP f (FILTER P defs)) ≤ SUM (MAP g defs)` >>
    `MAP f (FILTER P defs) = MAP g (FILTER P defs)` by (
      lrw[MAP_EQ_f,MEM_FILTER,Abbr`f`,Abbr`g`,Abbr`P`] >>
      PairCases_on`x`>>fs[]) >>
    pop_assum SUBST1_TAC >>
    Induct_on`defs` >> simp[] >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    Cases_on`x0`>>simp[Abbr`P`,Abbr`g`]) >>
  fsrw_tac[ARITH_ss][bind_fv_def,LET_THM]))

val _ = register "free_labs" (
  tprove_no_defn ((free_labs_def, free_labs_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (ez,e) => Cexp_size e
    | INR (INL (ez,es)) => Cexp4_size es
    | INR (INR (INL (ez,nz,ix,ds))) => Cexp1_size ds
    | INR (INR (INR (ez,nz,ix,def))) => Cexp2_size def)`))

val _ = register "no_labs" (
  tprove_no_defn ((no_labs_def, no_labs_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (e) => Cexp_size e
    | INR (INL (es)) => Cexp4_size es
    | INR (INR (INL (ds))) => Cexp1_size ds
    | INR (INR (INR (def))) => Cexp2_size def)`))

val _ = register "all_labs" (
  tprove_no_defn ((all_labs_def, all_labs_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (e) => Cexp_size e
    | INR (INL (es)) => Cexp4_size es
    | INR (INR (INL (ds))) => Cexp1_size ds
    | INR (INR (INR (def))) => Cexp2_size def)`))

val (number_constructors_def,number_constructors_ind) = register "number_constructors" (
  tprove_no_defn ((number_constructors_def,number_constructors_ind),
  WF_REL_TAC `measure (LENGTH o FST o SND)` >> rw[]))

val (bv_to_ov_def,bv_to_ov_ind) = register "bv_to_ov" (
  tprove_no_defn ((bv_to_ov_def,bv_to_ov_ind),
  WF_REL_TAC `measure (bc_value_size o SND)` >>
  rw[bc_value1_size_thm] >>
  Q.ISPEC_THEN `bc_value_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))

val _ = register "calculate_labels" (
  tprove_no_defn ((calculate_labels_def,calculate_labels_ind),
  WF_REL_TAC `measure (LENGTH o SND o SND o SND o SND)` >> rw[]))

val _ = register "replace_labels" (
  tprove_no_defn ((replace_labels_def,replace_labels_ind),
  WF_REL_TAC `measure (LENGTH o SND o SND)` >> rw[]))

(*
val _ = register "ov_to_string" (
  tprove_no_defn((ov_to_string_def,ov_to_string_ind),
  WF_REL_TAC`measure ov_size`>>
  srw_tac[ARITH_ss][ov1_size_thm]>>
  Q.ISPEC_THEN`ov_size`imp_res_tac SUM_MAP_MEM_bound>>
  fsrw_tac[ARITH_ss][]))
*)

val _ = register "compile_decs" (
  tprove_no_defn((compile_decs_def,compile_decs_ind),
  WF_REL_TAC`measure (LENGTH o FST o SND)` >> simp[]))

(* export rewrites *)

val _ = export_rewrites
["ToBytecode.emit_def","ToBytecode.get_label_def","ToBytecode.emit_ceref_def","ToBytecode.emit_ceenv_def"
,"ToBytecode.prim1_to_bc_def","ToBytecode.prim2_to_bc_def","Compiler.cmap_def","ToIntLang.cbv_def"
,"ToIntLang.remove_mat_vp_def","free_vars_def","no_closures_def"
,"Cv_to_ov_def","v_to_ov_def"
,"ToBytecode.compile_varref_def","compile_envref_def"
,"mkshift_def"
,"label_closures_def"
,"ToIntLang.Cpat_vars_def"
,"CompilerPrimitives.map_result_def","CompilerPrimitives.every_result_def"
,"IntLang.doPrim2_def","IntLang.CevalPrim2_def","IntLang.CevalUpd_def","IntLang.CevalPrim1_def"
,"free_labs_def","no_labs_def","all_labs_def"
,"IntLang.CDiv_excv_def","IntLang.CBind_excv_def"
,"IntLang.CDiv_exc_def","IntLang.CBind_exc_def"
,"ToIntLang.opn_to_prim2_def"
,"CompilerLib.the_def","CompilerLib.fapply_def"];

val _ = export_theory()
