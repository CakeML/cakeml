open HolKernel boolLib boolSimps bossLib Defn pairTheory pred_setTheory listTheory finite_mapTheory state_transformerTheory lcsymtacs
open MiniMLTheory MiniMLTerminationTheory CompileTheory
val _ = new_theory "compileTermination"

(* size helper theorems *)

val MEM_pair_MAP = store_thm(
"MEM_pair_MAP",
``MEM (a,b) ls ==> MEM a (MAP FST ls) /\ MEM b (MAP SND ls)``,
rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[])

val tac = Induct >- rw[Cexp_size_def,Cpat_size_def,Cv_size_def] >> srw_tac [ARITH_ss][Cexp_size_def,Cpat_size_def,Cv_size_def]
fun tm t1 t2 =  ``∀ls. ^t1 ls = SUM (MAP ^t2 ls) + LENGTH ls``
fun size_thm name t1 t2 = store_thm(name,tm t1 t2,tac)
val Cexp1_size_thm = size_thm "Cexp1_size_thm" ``Cexp1_size`` ``Cexp2_size``
val Cexp4_size_thm = size_thm "Cexp4_size_thm" ``Cexp4_size`` ``Cexp_size``
val Cpat1_size_thm = size_thm "Cpat1_size_thm" ``Cpat1_size`` ``Cpat_size``
val Cv1_size_thm = size_thm "Cv1_size_thm" ``Cv1_size`` ``Cv_size``

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
    SUM (MAP OUTR (FILTER ISR defs)) +
    SUM (MAP (pair_size SUC Cexp_size o OUTL) (FILTER ISL defs)) +
    LENGTH defs``,
  Induct >- rw[Cexp_size_def] >>
  Cases >> srw_tac[ARITH_ss][Cexp_size_def] >>
  Cases_on`x`>>srw_tac[ARITH_ss][Cexp_size_def,basicSizeTheory.pair_size_def,arithmeticTheory.ADD1])

val list_size_thm = store_thm(
"list_size_thm",
``∀f ls. list_size f ls = SUM (MAP f ls) + LENGTH ls``,
gen_tac >> Induct >> srw_tac[ARITH_ss][list_size_def])

val bc_value1_size_thm = store_thm(
"bc_value1_size_thm",
``∀ls. bc_value1_size ls = SUM (MAP bc_value_size ls) + LENGTH ls``,
Induct >- rw[BytecodeTheory.bc_value_size_def] >>
srw_tac [ARITH_ss][BytecodeTheory.bc_value_size_def])

(* semantics definitions *)

fun register name (def,ind) = let
  val _ = save_thm(name^"_def", def)
  val _ = save_thm(name^"_ind", ind)
in (def,ind) end

val Cevaluate_cases = save_thm("Cevaluate_cases",Cevaluate_cases)
val Cevaluate_rules = save_thm("Cevaluate_rules",Cevaluate_rules)
val i0_def = save_thm("i0_def",i0_def)
val Cevaluate_ind = save_thm("Cevaluate_ind",Cevaluate_ind)
val Cevaluate_strongind = save_thm("Cevaluate_strongind",Cevaluate_strongind)
val find_index_def = save_thm("find_index_def",find_index_def)
val Cexp_size_def = save_thm("Cexp_size_def",Cexp_size_def)
val Cv_size_def = save_thm("Cv_size_def",Cv_size_def)
val syneq_cases = save_thm("syneq_cases",syneq_cases)
val syneq_ind = save_thm("syneq_ind",syneq_ind)
val syneq_rules = save_thm("syneq_rules",syneq_rules)
val syneq_exp_cases = save_thm("syneq_exp_cases",syneq_exp_cases)
val syneq_exp_ind = save_thm("syneq_exp_ind",syneq_exp_ind)
val syneq_exp_rules = save_thm("syneq_exp_rules",syneq_exp_rules)
val syneq_cb_aux_def = save_thm("syneq_cb_aux_def",syneq_cb_aux_def)
val syneq_cb_V_def = save_thm("syneq_cb_V_def",syneq_cb_V_def)
val Cpat_vars_def = save_thm("Cpat_vars_def",Cpat_vars_def)
val _ = export_rewrites["Cpat_vars_def"]

val (free_vars_def, free_vars_ind) = register "free_vars" (
  tprove_no_defn ((free_vars_def,free_vars_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL e => Cexp_size e
    | INR b => Cexp2_size b)` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm] >>
  fsrw_tac[][FLOOKUP_DEF]>>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound)
  [`Cexp_size`,`Cexp2_size`] >>
  rw[] >> res_tac >> fs[Cexp_size_def] >> srw_tac[ARITH_ss][]))
val _ = export_rewrites["free_vars_def"];

val (free_labs_def,free_labs_ind) = register "free_labs" (
  tprove_no_defn ((free_labs_def,free_labs_ind),
  (WF_REL_TAC`inv_image ($< LEX $<) (λx. case x of
    INL e => (Cexp_size e,3:num) |
    INR (INL es) => (Cexp2_size es,2) |
    INR (INR (INL defs)) => (Cexp1_size defs,1) |
    INR(INR(INR def)) => (Cexp4_size def,0))`)))

val free_labs_rwt = save_thm("free_labs_rwt",let
  fun f n t = GEN_ALL(SIMP_RULE(srw_ss())[](SPEC t (List.nth(CONJUNCTS free_labs_def,n))))
  val th1 = LIST_CONJ(map(f 0 o rhs o snd o strip_exists)(strip_disj(snd(strip_forall(concl(TypeBase.nchotomy_of``:Cexp``))))))
  val th2 = LIST_CONJ(map(f 1 o rhs o snd o strip_exists o inst[alpha|->``:num#Cexp``,beta|->``:num``])(strip_disj(snd(strip_forall(concl(TypeBase.nchotomy_of``:def``))))))
  val th3 = LIST_CONJ(map(f 2 o rhs o snd o strip_exists o inst[alpha|->``:num#Cexp + num``])(strip_disj(snd(strip_forall(concl(TypeBase.nchotomy_of``:def list``))))))
  val th4 = LIST_CONJ(map(f 3 o rhs o snd o strip_exists o inst[alpha|->``:Cexp``])(strip_disj(snd(strip_forall(concl(TypeBase.nchotomy_of``:Cexp list``))))))
in
LIST_CONJ[th1,th2,th3,th4]
end)
val _ = export_rewrites["free_labs_rwt"]

val (no_closures_def, no_closures_ind) = register "no_closures" (
  tprove_no_defn ((no_closures_def, no_closures_ind),
  WF_REL_TAC `measure Cv_size` >>
  rw[Cv1_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `Cv_size` mp_tac) >>
  srw_tac[ARITH_ss][]))
val _ = export_rewrites["no_closures_def"];

val (Cv_to_ov_def,Cv_to_ov_ind) = register "Cv_to_ov" (
  tprove_no_defn ((Cv_to_ov_def,Cv_to_ov_ind),
  WF_REL_TAC `measure (Cv_size o SND o SND)` >>
  rw[Cv1_size_thm] >>
  Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))
val _ = export_rewrites["Cv_to_ov_def"];

val (v_to_ov_def,v_to_ov_ind) = register "v_to_ov" (
  tprove_no_defn ((v_to_ov_def,v_to_ov_ind),
  WF_REL_TAC `measure (v_size (K 0) o SND)` >>
  rw[v4_size_thm] >>
  Q.ISPEC_THEN `v_size (K 0)` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))
val _ = export_rewrites["v_to_ov_def"];

val _ = save_thm ("map_result_def", map_result_def);
val _ = export_rewrites["map_result_def"];
val _ = save_thm ("every_result_def", every_result_def);
val _ = export_rewrites["every_result_def"]

val _ = save_thm ("doPrim2_def", doPrim2_def);
val _ = export_rewrites["doPrim2_def"];

val _ = save_thm ("CevalPrim2_def", CevalPrim2_def);
val _ = save_thm ("CevalUpd_def", CevalUpd_def);
val _ = save_thm ("CevalPrim1_def", CevalPrim1_def);
val _ = export_rewrites["CevalPrim2_def","CevalUpd_def","CevalPrim1_def"];

(* compiler definitions *)

val (mkshift_def,mkshift_ind) = register "mkshift" (
  tprove_no_defn ((mkshift_def,mkshift_ind),
  WF_REL_TAC `measure (Cexp_size o SND o SND)` >>
  srw_tac[ARITH_ss][Cexp4_size_thm,Cexp1_size_thm,SUM_MAP_Cexp3_size_thm] >>
  Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][] >>
  imp_res_tac MEM_pair_MAP >>
  Q.ISPEC_THEN`Cexp2_size`imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][Cexp_size_def]))
val _ = export_rewrites["mkshift_def"]

val _ = save_thm("remove_mat_vp_def",remove_mat_vp_def)
val _ = export_rewrites["remove_mat_vp_def"]

val _ = register "remove_mat_var" (
  tprove_no_defn ((remove_mat_var_def,remove_mat_var_ind),
  WF_REL_TAC `measure (LENGTH o SND)` >> rw[]))

val (exp_to_Cexp_def,exp_to_Cexp_ind) = register "exp_to_Cexp" (
  tprove_no_defn ((exp_to_Cexp_def,exp_to_Cexp_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL (_,e) => exp_size ARB e
    | INR (INL (_,defs)) => exp1_size ARB defs
    | INR (INR (INL (_,pes))) => exp5_size ARB pes
    | INR (INR (INR (_,es))) => exp8_size ARB es)`))

val (v_to_Cv_def,v_to_Cv_ind) = register "v_to_Cv" (
  tprove_no_defn ((v_to_Cv_def,v_to_Cv_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL (_,v) => v_size ARB v
    | INR (INL (_, vs)) => v4_size ARB vs
    | INR (INR (_, env)) => v1_size ARB env)`))

val pat_to_Cpat_def = save_thm("pat_to_Cpat_def",pat_to_Cpat_def)

val (compile_envref_def, compile_envref_ind) = register "compile_envref" (
  tprove_no_defn ((compile_envref_def, compile_envref_ind),
  WF_REL_TAC `measure (λp. case p of (_,_,CCEnv _) => 0 | (_,_,CCRef _) => 1)`))

val _ = save_thm("compile_varref_def",compile_varref_def)
val _ = export_rewrites["compile_varref_def","compile_envref_def"]

val (compile_def, compile_ind) = register "compile" (
  tprove_no_defn ((compile_def, compile_ind),
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
       | INL (d,env,t,sz,s,e) => (Cexp_size e, 3:num)
       | INR (INL (d,env,t,sz,e,n,s,0))=> (Cexp_size e, 4)
       | INR (INL (d,env,t,sz,e,n,s,ns))=> (Cexp_size e + ns, 1)
       | INR (INR (d,env,sz,s,es))=> (SUM (MAP Cexp_size es), 3 + LENGTH es)) ` >>
  srw_tac[ARITH_ss][] >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp_size_def,list_size_thm,SUM_MAP_Cexp3_size_thm] >>
  BasicProvers.CASE_TAC >> fsrw_tac[ARITH_ss][] >>
  BasicProvers.CASE_TAC >> fsrw_tac[ARITH_ss][]))

val _ = register "num_fold" (
  tprove_no_defn ((num_fold_def,num_fold_ind),
  WF_REL_TAC `measure (SND o SND)`))

val zero_vars_def = tDefine "zero_vars"`
  (zero_vars (CDecl a) = CDecl (MAP (λ(n,m). (0,m)) a)) ∧
  (zero_vars (CRaise b) = CRaise b) ∧
  (zero_vars (CHandle e1 e2) = CHandle (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CVar _) = CVar 0) ∧
  (zero_vars (CLit c) = CLit c) ∧
  (zero_vars (CCon cn es) = CCon cn (zero_vars_list es)) ∧
  (zero_vars (CTagEq e n) = CTagEq (zero_vars e) n) ∧
  (zero_vars (CProj e n) = CProj (zero_vars e) n) ∧
  (zero_vars (CLet e1 e2) = CLet (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CLetrec defs e) = CLetrec (zero_vars_defs defs) (zero_vars e)) ∧
  (zero_vars (CFun def) = CFun (zero_vars_def def)) ∧
  (zero_vars (CCall e es) = CCall (zero_vars e) (zero_vars_list es)) ∧
  (zero_vars (CPrim1 p1 e2) = CPrim1 p1 (zero_vars e2)) ∧
  (zero_vars (CPrim2 p2 e1 e2) = CPrim2 p2 (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CUpd e1 e2) = CUpd (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CIf e1 e2 e3) = CIf (zero_vars e1) (zero_vars e2) (zero_vars e3)) ∧
  (zero_vars_list [] = []) ∧
  (zero_vars_list (e::es) = (zero_vars e)::(zero_vars_list es)) ∧
  (zero_vars_defs [] = []) ∧
  (zero_vars_defs (def::defs) = (zero_vars_def def)::(zero_vars_defs defs)) ∧
  (zero_vars_def (INL (xs,b)) = INL (xs,zero_vars b)) ∧
  (zero_vars_def (INR l) = INR l)`
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
  fsrw_tac[ARITH_ss][])
val _ = export_rewrites["zero_vars_mkshift"]

val (label_closures_def,label_closures_ind) = register "label_closures" (
  tprove_no_defn ((label_closures_def, label_closures_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (ez,ls,e) => Cexp_size (zero_vars e)
    | INR (INL (ez,ls,es)) => Cexp4_size (zero_vars_list es)
    | INR (INR (ez,ls,nz,k,defs)) => SUM (MAP Cexp2_size (MAP (zero_vars_def o INL) defs)))` >>
  srw_tac[ARITH_ss][Cexp_size_def,SUM_MAP_Cexp3_size_thm,Cexp1_size_thm,SUM_MAP_Cexp2_size_thm,basicSizeTheory.pair_size_def] >- (
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    qmatch_abbrev_tac`a + (b + c) < d + ((2 * f) + (g + (h + 1:num)))` >>
    qsuff_tac`a ≤ f ∧ (b = 0) ∧ (c = h)` >- simp[] >>
    unabbrev_all_tac >>
    conj_tac >- simp[rich_listTheory.LENGTH_FILTER_LEQ] >>
    conj_tac >- (
      simp[SUM_eq_0,MEM_MAP,MEM_FILTER] >>
      qx_gen_tac`a` >> fsrw_tac[DNF_ss][] >>
      qx_gen_tac`b` >>
      Cases_on`b`>>simp[]>>
      Cases_on`x`>>simp[] ) >>
    AP_TERM_TAC >>
    AP_TERM_TAC >>
    qmatch_abbrev_tac`FILTER ISL (MAP f (FILTER ISL defs)) = FILTER ISL (MAP g defs)` >>
    `MAP f (FILTER ISL defs) = MAP g (FILTER ISL defs)` by (
      lrw[MAP_EQ_f,MEM_FILTER,Abbr`f`] ) >>
    simp[] >>
    qsuff_tac`MAP g (FILTER ISL defs) = FILTER ISL (MAP g defs)` >- (
      srw_tac[ETA_ss][rich_listTheory.FILTER_FILTER] ) >>
    match_mp_tac rich_listTheory.MAP_FILTER >>
    simp[Abbr`g`] >>
    Cases >> simp[] >>
    qmatch_abbrev_tac`ISL (zero_vars_def (INL y))` >>
    Cases_on`y`>>simp[] ) >>
  simp[bind_fv_def]))

val (body_count_def,body_count_ind) = register"body_count" (
  tprove_no_defn ((body_count_def,body_count_ind),
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
    | INL b => (Cexp_size b, 1:num)
    | INR (INR d) => (Cexp2_size d, 0)
    | INR (INL es) => (Cexp4_size es, 0))` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm] >>
  Q.ISPEC_THEN`Cexp2_size`imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))
val _ = export_rewrites["body_count_def"]

val body_count_list_MAP = store_thm("body_count_list_MAP",
  ``∀ls. body_count_list ls = SUM (MAP body_count ls)``,
  Induct >> rw[])
val _ = export_rewrites["body_count_list_MAP"]

val body_count_mkshift = store_thm("body_count_mkshift",
  ``∀f k e. body_count (mkshift f k e) = body_count e``,
  ho_match_mp_tac mkshift_ind >>
  rw[mkshift_def,MAP_MAP_o,combinTheory.o_DEF] >> rw[] >>
  TRY ( Cases_on`cb`>>fs[]>>BasicProvers.CASE_TAC>>fs[]>>NO_TAC) >>
  AP_TERM_TAC >> lrw[MAP_EQ_f] >>
  simp[Abbr`defs'`,MAP_MAP_o,combinTheory.o_DEF] >>
  lrw[MAP_EQ_f] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  fsrw_tac[ARITH_ss][])
val _ = export_rewrites["body_count_mkshift"]

val body_count_bind_fv = store_thm("body_count_bind_fv",
  ``body_count (bind_fv azb nz ez k).body = body_count (SND azb)``,
  Cases_on`azb` >> rw[bind_fv_def] >> rw[Abbr`e`])

val _ = save_thm("cce_aux_def",cce_aux_def)
val _ = save_thm("compile_code_env_def",compile_code_env_def)
val _ = save_thm("push_lab_def",push_lab_def)
val _ = save_thm("cons_closure_def",cons_closure_def)
val _ = save_thm("update_refptr_def",update_refptr_def)
val _ = save_thm("compile_closures_def",compile_closures_def)

val (number_constructors_def,number_constructors_ind) = register "number_constructors" (
  tprove_no_defn ((number_constructors_def,number_constructors_ind),
  WF_REL_TAC `measure (LENGTH o FST)` >> rw[]))

val (repl_dec_def,repl_dec_ind) = register "repl_dec" (
  tprove_no_defn ((repl_dec_def,repl_dec_ind),
  WF_REL_TAC `measure (dec_size ARB o SND)`))

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

val _ = save_thm("bind_fv_def",bind_fv_def)
val _ = save_thm("compile_labels_def",compile_labels_def)
val _ = save_thm("repl_exp_def",repl_exp_def)
val _ = save_thm("compile_Cexp_def",compile_Cexp_def)
val _ = save_thm("emit_def",emit_def)
val _ = save_thm("pushret_def",pushret_def)
val _ = save_thm("get_labels_def",get_labels_def)
val _ = save_thm("emit_ceref_def",emit_ceref_def)
val _ = save_thm("emit_ceenv_def",emit_ceenv_def)
val _ = save_thm("prim1_to_bc_def",prim1_to_bc_def)
val _ = save_thm("prim2_to_bc_def",prim2_to_bc_def)
val _ = save_thm("compile_decl_def",compile_decl_def)
val _ = save_thm("cmap_def",cmap_def)
val _ = save_thm("cbv_def",cbv_def)
val _ = save_thm("etC_def",etC_def)
val _ = save_thm("closed_cd_def",closed_cd_def)
val _ = save_thm("el_check_def",el_check_def)
val _ = save_thm("shift_def",shift_def)
val _ = export_rewrites["emit_def","get_labels_def","emit_ceref_def","emit_ceenv_def","prim1_to_bc_def","prim2_to_bc_def","cmap_def","cbv_def","etC_def"]

val _ = export_theory()
