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

val (label_defs_def,label_defs_ind) = register "label_defs" (
  tprove_no_defn ((label_defs_def,label_defs_ind),
  WF_REL_TAC `measure (LENGTH o SND o SND o SND)` >> rw[]))

val _ = save_thm("label_closures_def",label_closures_def)

val (count_unlab_def,count_unlab_ind) = register "count_unlab" (
  tprove_no_defn ((count_unlab_def,count_unlab_ind),
  WF_REL_TAC `measure LENGTH` >> rw[]))

val _ = save_thm("imm_unlab_def",imm_unlab_def)

(*
val _ = overload_on("list_max",``MAX_SET o set``)

val mbd_def = tDefine "mbd"`
  (mbd c (CDecl _) = 0) ∧
  (mbd c (CRaise _) = 0) ∧
  (mbd c (CVar _) = 0) ∧
  (mbd c (CLit _) = 0) ∧
  (mbd c (CCon _ es) = list_max (MAP (mbd c) es)) ∧
  (mbd c (CTagEq e _) = mbd c e) ∧
  (mbd c (CProj e _) = mbd c e) ∧
  (mbd c (CLet _ es e) = list_max (MAP (mbd c) (e::es))) ∧
  (mbd c (CLetfun _ _ defs e) = MAX (list_max (MAP (mbd_def c) defs)) (mbd c e)) ∧
  (mbd c (CFun xs cb) = mbd_def c (xs,cb)) ∧
  (mbd c (CCall e es) = list_max (MAP (mbd c) (e::es))) ∧
  (mbd c (CPrim2 _ e1 e2) = MAX (mbd c e1) (mbd c e2)) ∧
  (mbd c (CIf e1 e2 e3) = list_max (MAP (mbd c) [e1;e2;e3])) ∧
  (mbd_def c (_,INL b) = (1 + mbd c b)) ∧
  (mbd_def c (_,INR l) =
    case FLOOKUP c l of
    | SOME b => (1 + mbd (c \\ l) b)
    | NONE => 0)`(
  WF_REL_TAC `inv_image ($< LEX $< LEX $<) (λx. case x of
    | INL (c,b) => (CARD (FDOM c), Cexp_size b, 1:num)
    | INR (c,d) => (CARD (FDOM c), Cexp2_size d, 0))` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm] >>
  srw_tac[ARITH_ss][SUM_MAP_Cexp2_size_thm] >>
  Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][] >>
  TRY (fs[FLOOKUP_DEF] >> Cases_on `CARD (FDOM c)` >> fs[] >> NO_TAC) >>
  qmatch_assum_rename_tac `MEM (a,b) defs`[] >>
  `MEM a (MAP FST defs)` by (rw[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
  `MEM b (MAP SND defs)` by (rw[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
  Q.ISPEC_THEN`Cexp3_size`imp_res_tac SUM_MAP_MEM_bound >>
  Q.ISPEC_THEN`list_size (list_size char_size)`imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][])
*)

val bodies_def = tDefine "bodies"`
  (bodies (CDecl _) = 0) ∧
  (bodies (CRaise _) = 0) ∧
  (bodies (CHandle e1 e2) = bodies e1 + bodies e2) ∧
  (bodies (CVar _) = 0) ∧
  (bodies (CLit _) = 0) ∧
  (bodies (CCon _ es) = SUM (MAP bodies es)) ∧
  (bodies (CTagEq e _) = bodies e) ∧
  (bodies (CProj e _) = bodies e) ∧
  (bodies (CLet e b) = bodies e + bodies b) ∧
  (bodies (CLetrec defs e) = SUM (MAP bod1 defs) + (bodies e)) ∧
  (bodies (CFun cb) = bod1 cb) ∧
  (bodies (CCall e es) = SUM (MAP bodies (e::es))) ∧
  (bodies (CPrim1 _ e) = bodies e) ∧
  (bodies (CPrim2 _ e1 e2) = bodies e1 + bodies e2) ∧
  (bodies (CUpd e1 e2) = bodies e1 + bodies e2) ∧
  (bodies (CIf e1 e2 e3) = SUM (MAP bodies [e1;e2;e3])) ∧
  (bod1 (INL (_,b)) = (1 + bodies b)) ∧
  (bod1 (INR l) = 0)`
  (
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
    | INL b => (Cexp_size b, 1:num)
    | INR d => (Cexp2_size d, 0))` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm] >>
  srw_tac[ARITH_ss][SUM_MAP_Cexp3_size_thm] >>
  Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
  Q.ISPEC_THEN`Cexp2_size`imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][])
val _ = export_rewrites["bodies_def"]

val imm_unlab_list_SUM = store_thm("imm_unlab_list_SUM",
  ``∀ls. imm_unlab_list ls = SUM (MAP imm_unlab ls)``,
  Induct >> rw[imm_unlab_def])

val count_unlab_FILTER = store_thm("count_unlab_FILTER",
  ``count_unlab = LENGTH o (FILTER ISL)``,
  simp[FUN_EQ_THM] >>
  Induct >> rw[count_unlab_def] >>
  Cases_on `h` >>
  fs[count_unlab_def] >>
  srw_tac[ARITH_ss][])

val bodies_ind = theorem"bodies_ind"

val imm_bodies_0 = store_thm("imm_bodies_0",
  ``(∀e. (bodies e = 0) = (imm_unlab e = 0)) ∧
    (∀d. (bod1 d = 0) = (ISR d))``,
  ho_match_mp_tac bodies_ind >>
  rw[imm_unlab_def,imm_unlab_list_SUM] >>
  fs[SUM_eq_0,MEM_MAP,count_unlab_FILTER,NULL_FILTER,GSYM NULL_LENGTH] >>
  TRY (metis_tac[]) >>
  Cases_on `d` >> rw[])

val label_closures_list_mapM = store_thm("label_closures_list_mapM",
  ``label_closures_list = mapM label_closures``,
  fs[Once FUN_EQ_THM] >>
  Induct >> rw[label_closures_def,mapM_cons])
val _ = export_rewrites["label_closures_list_mapM"]

val bodies_mkshift = store_thm("bodies_mkshift",
  ``∀f k e. bodies (mkshift f k e) = bodies e``,
  ho_match_mp_tac mkshift_ind >>
  rw[mkshift_def,MAP_MAP_o,combinTheory.o_DEF] >> rw[] >>
  TRY ( Cases_on`cb`>>fs[]>>BasicProvers.CASE_TAC>>fs[]>>NO_TAC) >>
  AP_TERM_TAC >> lrw[MAP_EQ_f] >>
  simp[Abbr`defs'`,MAP_MAP_o,combinTheory.o_DEF] >>
  lrw[MAP_EQ_f] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  fsrw_tac[ARITH_ss][])
val _ = export_rewrites["bodies_mkshift"]

val label_closures_bodies = store_thm("label_closures_bodies",
  ``(∀e s cd s'. ((cd,s') = label_closures e s) ⇒
                 ∃c. (s'.lcode_env = c++s.lcode_env) ∧
                     (bodies e = list_size (bodies o closure_data_body o SND) c)) ∧
    (∀ds ac nz k s ds' s'. ((ds',s') = label_defs ac nz k ds s) ⇒
                 ∃c. (s'.lcode_env = c++s.lcode_env) ∧
                     (SUM (MAP bod1 ds) = list_size (bodies o closure_data_body o SND) c)) ∧
    (∀x:def. T) ∧ (∀x:(num#Cexp). T) ∧
    (∀es s es' s'. ((es',s') = label_closures_list es s) ⇒
                 ∃c. (s'.lcode_env = c++s.lcode_env) ∧
                     (SUM (MAP bodies es) = list_size (bodies o closure_data_body o SND) c))``,
  ho_match_mp_tac (TypeBase.induction_of``:Cexp``) >>
  srw_tac[DNF_ss][label_closures_def,list_size_thm,SUM_eq_0,MEM_MAP,LENGTH_NIL,UNIT_DEF,BIND_DEF]
  >- (
    qabbrev_tac `q = label_closures e s` >>
    PairCases_on`q`>>fs[] >>
    qabbrev_tac `p = label_closures e' q1` >>
    PairCases_on`p`>>fs[] >>
    first_x_assum (qspecl_then[`q1`,`p0`,`p1`]mp_tac) >>
    first_x_assum (qspecl_then[`s`,`q0`,`q1`]mp_tac) >>
    rw[] >> fs[] >>
    srw_tac[ETA_ss,ARITH_ss][SUM_APPEND] )
  >- (
    Cases_on `mapM label_closures es s` >> fs[] >> rw[] >>
    metis_tac[] )
  >- ( Cases_on `label_closures e s` >> fs[] >> rw[] )
  >- ( Cases_on `label_closures e s` >> fs[] >> rw[] )
  >- (
    qabbrev_tac `q = label_closures e s` >>
    PairCases_on`q`>>fs[] >>
    qabbrev_tac `p = label_closures e' q1` >>
    PairCases_on`p`>>fs[] >>
    first_x_assum (qspecl_then[`q1`,`p0`,`p1`]mp_tac) >>
    first_x_assum (qspecl_then[`s`,`q0`,`q1`]mp_tac) >>
    rw[] >> fs[] >>
    srw_tac[ETA_ss,ARITH_ss][SUM_APPEND] )
  >- (
    qabbrev_tac `p = label_defs [] (LENGTH ds) 0 ds s` >>
    PairCases_on `p` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`[]`,`LENGTH ds`,`0`,`s`,`p0`,`p1`] mp_tac) >> rw[] >> fs[] >>
    qabbrev_tac `q = label_closures e p1` >>
    PairCases_on `q` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >> rw[] >>
    fs[] >> rw[] >>
    srw_tac[ETA_ss,ARITH_ss][SUM_APPEND] )
  >- (
    Cases_on `x` >> TRY (Cases_on`x'`) >> fs[label_defs_def,UNIT_DEF,BIND_DEF,LET_THM] >>
    srw_tac[ARITH_ss][bind_fv_def] >>
    rw[Abbr`e`])
  >- (
    qabbrev_tac `q = label_closures e s` >>
    PairCases_on `q` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`s`,`q0`,`q1`] mp_tac) >> rw[] >>
    fs[UNCURRY] >> rw[] >>
    qabbrev_tac `p = mapM label_closures es q1` >>
    PairCases_on `p` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`q1`,`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ETA_ss,ARITH_ss][SUM_APPEND] )
  >- (
    qabbrev_tac `q = label_closures e s` >>
    PairCases_on `q` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`s`,`q0`,`q1`] mp_tac) >>
    fs[UNCURRY] >> rw[] )
  >- (
    qabbrev_tac `q = label_closures e s` >>
    PairCases_on `q` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspec_then `q1` mp_tac) >>
    first_x_assum (qspecl_then [`s`,`q0`,`q1`] mp_tac) >>
    fs[UNCURRY] >> rw[] >>
    qabbrev_tac `p = label_closures e' q1` >>
    PairCases_on `p` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ETA_ss,ARITH_ss][SUM_APPEND] )
  >- (
    qabbrev_tac `q = label_closures e s` >>
    PairCases_on `q` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspec_then `q1` mp_tac) >>
    first_x_assum (qspecl_then [`s`,`q0`,`q1`] mp_tac) >>
    fs[UNCURRY] >> rw[] >>
    qabbrev_tac `p = label_closures e' q1` >>
    PairCases_on `p` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ETA_ss,ARITH_ss][SUM_APPEND] )
  >- (
    qabbrev_tac `q = label_closures e s` >>
    PairCases_on `q` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspec_then `SND (label_closures e' q1)` mp_tac) >>
    first_x_assum (qspec_then `q1` mp_tac) >>
    first_x_assum (qspecl_then [`s`,`q0`,`q1`] mp_tac) >>
    fs[UNCURRY] >> rw[] >>
    qabbrev_tac `p = label_closures e' q1` >>
    PairCases_on `p` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    qpat_assum `!x. y` mp_tac >>
    first_x_assum (qspecl_then [`p0`,`p1`] mp_tac) >> rw[] >>
    qabbrev_tac `r = label_closures e'' p1` >>
    PairCases_on `r` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`r0`,`r1`] mp_tac) >> rw[] >>
    srw_tac[ETA_ss,ARITH_ss][SUM_APPEND] )
  >- (
    fs[label_defs_def,UNIT_DEF] )
  >- (
    Cases_on `x` >> TRY(Cases_on `x'`) >>
    fs[label_defs_def,BIND_DEF,UNIT_DEF] >>
    res_tac >> fs[] >>
    srw_tac[ARITH_ss][SUM_APPEND,bind_fv_def] >>
    rw[Abbr`e`])
  >- (
    qabbrev_tac `q = label_closures e s` >>
    PairCases_on `q` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`s`,`q0`,`q1`] mp_tac) >> rw[] >>
    fs[UNCURRY] >> rw[] >>
    qabbrev_tac `p = mapM label_closures es q1` >>
    PairCases_on `p` >> pop_assum (assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    first_x_assum (qspecl_then [`q1`,`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ETA_ss,ARITH_ss][SUM_APPEND] ))

val _ = register "repeat_label_closures" (
  tprove_no_defn ((repeat_label_closures_def,repeat_label_closures_ind),
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
    | (INL (e,n,ac)) =>  (bodies e,1:num)
    | (INR (n,ac,ls)) => (list_size (bodies o closure_data_body o SND) ls),0)` >>
  srw_tac[ARITH_ss][list_size_thm] >>
  disj2_tac >>
  imp_res_tac label_closures_bodies >>
  fs[list_size_thm] >>
  srw_tac[ETA_ss,ARITH_ss][combinTheory.o_DEF]))

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
