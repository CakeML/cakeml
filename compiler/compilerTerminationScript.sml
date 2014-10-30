open HolKernel boolLib boolSimps bossLib Defn pairTheory pred_setTheory listTheory finite_mapTheory state_transformerTheory lcsymtacs
open terminationTheory libTheory intLangTheory toIntLangTheory toBytecodeTheory compilerTheory bytecodeTheory
open modLangTheory conLangTheory exhLangTheory patLangTheory;

val _ = new_theory "compilerTermination"

(* size helper theorems *)

val MEM_pair_MAP = store_thm(
"MEM_pair_MAP",
``MEM (a,b) ls ==> MEM a (MAP FST ls) /\ MEM b (MAP SND ls)``,
rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[])

val tac = Induct >- rw[Cexp_size_def,Cv_size_def] >> srw_tac [ARITH_ss][Cexp_size_def,Cv_size_def]
fun tm t1 t2 =  ``∀ls. ^t1 ls = SUM (MAP ^t2 ls) + LENGTH ls``
fun size_thm name t1 t2 = store_thm(name,tm t1 t2,tac)
val Cexp1_size_thm = size_thm "Cexp1_size_thm" ``Cexp1_size`` ``Cexp2_size``
val Cexp4_size_thm = size_thm "Cexp4_size_thm" ``Cexp4_size`` ``Cexp_size``
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
Induct >- rw[bytecodeTheory.bc_value_size_def] >>
srw_tac [ARITH_ss][bytecodeTheory.bc_value_size_def])

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

val (mkshift_def,mkshift_ind) = register "mkshift" (
  tprove_no_defn ((mkshift_def,mkshift_ind),
  WF_REL_TAC `measure (Cexp_size o SND o SND)` >>
  srw_tac[ARITH_ss][Cexp4_size_thm,Cexp1_size_thm,SUM_MAP_Cexp3_size_thm] >>
  Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][] >>
  imp_res_tac MEM_pair_MAP >>
  Q.ISPEC_THEN`Cexp2_size`imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][Cexp_size_def]))

(*
val (exp_to_Cexp_def,exp_to_Cexp_ind) = register "exp_to_Cexp" (
  tprove_no_defn ((exp_to_Cexp_def,exp_to_Cexp_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL e => exp_pat_size e
    | INR es => exp_pat1_size es)`))
*)

val (compile_envref_def, compile_envref_ind) = register "compile_envref" (
  tprove_no_defn ((compile_envref_def, compile_envref_ind),
  WF_REL_TAC `measure (λp. case p of (_,_,CCEnv _) => 0 | (_,_,CCRef _) => 1)`))

(*
val [s1,s2,s3,s4] = CONJUNCTS stackshift_def
val stackshift_alt = prove(
``stackshift j k =
  if k = 0 then ^(rhs(concl(Q.SPEC`j`s1)))
  else if j = 0 then ^(rhs(concl(Q.SPEC`k-1`s2)))
  else if j = 1 then ^(rhs(concl(Q.SPEC`k-1`s3)))
  else ^(rhs(concl(Q.SPECL[`j-2`,`k-1`]s4)))``,
SIMP_TAC(srw_ss()++ARITH_ss)[arithmeticTheory.ADD1] THEN
Cases_on`k`THEN ASM_SIMP_TAC(srw_ss())[stackshift_def] THEN
Cases_on`j`THEN ASM_SIMP_TAC(srw_ss())[stackshift_def] THEN
Cases_on`n'`THEN ASM_SIMP_TAC(srw_ss())[stackshift_def])
|> SIMP_RULE (srw_ss()++ARITH_ss)[arithmeticTheory.ADD1]
val _ = register "stackshift"(stackshift_alt,stackshift_ind)

val [s1,s2] = CONJUNCTS stackshiftaux_def
val stackshiftaux_alt = prove(
``stackshiftaux i j k =
  if i = 0 then ^(rhs(concl(Q.SPECL[`k`,`j`]s1)))
  else ^(rhs(concl(Q.SPECL[`i-1`,`k`,`j`]s2)))``,
SIMP_TAC(srw_ss()++ARITH_ss)[arithmeticTheory.ADD1] THEN
Cases_on`i`THEN ASM_SIMP_TAC(srw_ss())[stackshiftaux_def])
|> SIMP_RULE (srw_ss()++ARITH_ss)[arithmeticTheory.ADD1]
val _ = save_thm("stackshiftaux_alt",stackshiftaux_alt)

val _ = computeLib.del_persistent_consts[``stackshift``,``stackshiftaux``]
val _ = computeLib.add_persistent_funs["stackshiftaux_alt","stackshift_alt"]
*)

val (compile_def, compile_ind) = register "compile" (
  tprove_no_defn ((compile_def, compile_ind),
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
       | INL (env,t,sz,s,e) => (Cexp_size e, 3:num)
       | INR (INL (env,t,sz,e,n,s,0))=> (Cexp_size e, 4)
       | INR (INL (env,t,sz,e,n,s,ns))=> (Cexp_size e + ns, 1)
       | INR (INR (env,sz,s,es))=> (SUM (MAP Cexp_size es), 3 + LENGTH es)) ` >>
  srw_tac[ARITH_ss][] >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp_size_def,list_size_thm,SUM_MAP_Cexp3_size_thm] >>
  BasicProvers.CASE_TAC >> fsrw_tac[ARITH_ss][] >>
  BasicProvers.CASE_TAC >> fsrw_tac[ARITH_ss][]))

val _ = register "PushAnyInt" (
  tprove_no_defn ((PushAnyInt_def,PushAnyInt_ind),
    WF_REL_TAC`inv_image ($< LEX $<) (λx. (if x < 0 then 1:num else 0, Num(ABS x)))` >>
    rw[] >- (
      fs[maxPushInt_def] >>
      disj1_tac >>
      Cases_on`i < 0` >> rw[] >>
      Cases_on`i` >> fs[] )
    >- (
      Cases_on`i`>>fs[maxPushInt_def] >>
      simp[integerTheory.INT_ABS_NUM] )
    >- intLib.COOPER_TAC))

val zero_vars_def = Lib.with_flag (computeLib.auto_import_definitions, false) (tDefine "zero_vars"`
  (zero_vars (CRaise e) = CRaise (zero_vars e)) ∧
  (zero_vars (CHandle e1 e2) = CHandle (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CVar _) = CVar 0) ∧
  (zero_vars (CGvar n) = CGvar n) ∧
  (zero_vars (CLit c) = CLit c) ∧
  (zero_vars (CCon cn es) = CCon cn (zero_vars_list es)) ∧
  (zero_vars (CLet bd e1 e2) = CLet bd (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CLetrec defs e) = CLetrec (zero_vars_defs defs) (zero_vars e)) ∧
  (zero_vars (CCall ck e es) = CCall ck (zero_vars e) (zero_vars_list es)) ∧
  (zero_vars (CPrim1 p1 e2) = CPrim1 p1 (zero_vars e2)) ∧
  (zero_vars (CPrim2 p2 e1 e2) = CPrim2 p2 (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CUpd b e1 e2 e3) = CUpd b (zero_vars e1) (zero_vars e2) (zero_vars e3)) ∧
  (zero_vars (CIf e1 e2 e3) = CIf (zero_vars e1) (zero_vars e2) (zero_vars e3)) ∧
  (zero_vars (CExtG n) = CExtG n) ∧
  (zero_vars_list [] = []) ∧
  (zero_vars_list (e::es) = (zero_vars e)::(zero_vars_list es)) ∧
  (zero_vars_defs [] = []) ∧
  (zero_vars_defs (def::defs) = (zero_vars_def def)::(zero_vars_defs defs)) ∧
  (zero_vars_def (NONE,(xs,b)) = (NONE,(xs,zero_vars b))) ∧
  (zero_vars_def (SOME x,y) = (SOME x,y))`)
  (WF_REL_TAC`inv_image $< (λx. case x of INL e => Cexp_size e |
    INR (INL es) => Cexp4_size es |
    INR (INR (INL defs)) => Cexp1_size defs |
    INR(INR(INR def)) => Cexp2_size def)`)

val zero_vars_list_MAP = prove(
  ``(∀ls. (zero_vars_list ls = MAP (zero_vars) ls)) ∧
    (∀ls. (zero_vars_defs ls = MAP (zero_vars_def) ls))``,
  conj_tac >> Induct >> rw[zero_vars_def])
val _ = augment_srw_ss[rewrites [zero_vars_def,zero_vars_list_MAP]]

val zero_vars_mkshift = prove(
  ``∀f k e. zero_vars (mkshift f k e) = zero_vars e``,
  ho_match_mp_tac mkshift_ind >>
  rw[mkshift_def,MAP_MAP_o,combinTheory.o_DEF,LET_THM] >>
  lrw[MAP_EQ_f,UNCURRY] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >> rw[] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fsrw_tac[ARITH_ss][])
val _ = augment_srw_ss[rewrites [zero_vars_mkshift]]

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

val _ = map delete_const ["zero_vars","zero_vars_list","zero_vars_defs","zero_vars_def","zero_vars_UNION"]
val _ = delete_binding "zero_vars_ind"

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

val (do_Ceq_def,do_Ceq_ind) = register "do_Ceq" (
  tprove_no_defn((do_Ceq_def,do_Ceq_ind),
  WF_REL_TAC`measure (\x. case x of INL (cv,_) => Cv_size cv | INR (cvs,_) => Cv1_size cvs)`));

val (exp_to_i1_def, exp_to_i1_ind) =
  tprove_no_defn ((exp_to_i1_def, exp_to_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y,e) => exp_size e
                                        | INR (INL (x,y,es)) => exps_size es
                                        | INR (INR (INL (x,y,pes))) => pes_size pes
                                        | INR (INR (INR (x,y,funs))) => funs_size funs)` >>
  srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]);
val _ = register "exp_to_i1" (exp_to_i1_def,exp_to_i1_ind);

val (pmatch_i1_def, pmatch_i1_ind) =
  tprove_no_defn ((pmatch_i1_def, pmatch_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_size p
                                        | INR (a,x,ps,y,z) => pats_size ps)` >>
  srw_tac [ARITH_ss] [size_abbrevs, astTheory.pat_size_def]);
val _ = register "pmatch_i1" (pmatch_i1_def,pmatch_i1_ind);

val (do_eq_i1_def, do_eq_i1_ind) =
  tprove_no_defn ((do_eq_i1_def, do_eq_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_i1_size x
                                        | INR (xs,ys) => v_i14_size xs)`);
val _ = register "do_eq_i1" (do_eq_i1_def,do_eq_i1_ind);

val (pat_to_i2_def, pat_to_i2_ind) =
  tprove_no_defn ((pat_to_i2_def, pat_to_i2_ind),
  WF_REL_TAC `inv_image $< (\(x,p). pat_size p)` >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  Induct_on `ps` >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "pat_to_i2" (pat_to_i2_def,pat_to_i2_ind);

val (exp_to_i2_def, exp_to_i2_ind) =
  tprove_no_defn ((exp_to_i2_def, exp_to_i2_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,e) => exp_i1_size e
                                        | INR (INL (x,es)) => exp_i16_size es
                                        | INR (INR (INL (x,pes))) => exp_i13_size pes
                                        | INR (INR (INR (x,funs))) => exp_i11_size funs)`)
val _ = register "exp_to_i2" (exp_to_i2_def,exp_to_i2_ind);

val (pmatch_i2_def, pmatch_i2_ind) =
  tprove_no_defn ((pmatch_i2_def, pmatch_i2_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_i2_size p
                                        | INR (a,x,ps,y,z) => pat_i21_size ps)` >>
  srw_tac [ARITH_ss] [pat_i2_size_def]);
val _ = register "pmatch_i2" (pmatch_i2_def,pmatch_i2_ind);

val (do_eq_i2_def, do_eq_i2_ind) =
  tprove_no_defn ((do_eq_i2_def, do_eq_i2_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_i2_size x
                                        | INR (xs,ys) => v_i23_size xs)`);
val _ = register "do_eq_i2" (do_eq_i2_def,do_eq_i2_ind);

val (is_unconditional_def, is_unconditional_ind) =
  tprove_no_defn((is_unconditional_def, is_unconditional_ind),
  WF_REL_TAC`measure pat_i2_size` >> gen_tac >>
  Induct >> simp[pat_i2_size_def] >>
  rw[] >> res_tac >> simp[pat_i2_size_def])
val _ = register "is_unconditional" (is_unconditional_def, is_unconditional_ind);

val (do_eq_exh_def, do_eq_exh_ind) =
  tprove_no_defn ((do_eq_exh_def, do_eq_exh_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_exh_size x
                                        | INR (xs,ys) => v_exh3_size xs)`);
val _ = register "do_eq_exh" (do_eq_exh_def,do_eq_exh_ind);

val (pmatch_exh_def, pmatch_exh_ind) =
  tprove_no_defn ((pmatch_exh_def, pmatch_exh_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,p,y,z) => pat_exh_size p
                                        | INR (x,ps,y,z) => pat_exh1_size ps)` >>
  srw_tac [ARITH_ss] [pat_exh_size_def]);
val _ = register "pmatch_exh" (pmatch_exh_def,pmatch_exh_ind);

val exp_i23_size_append = prove(
  ``∀p1 p2. exp_i23_size (p1++p2) = exp_i23_size p1 + exp_i23_size p2``,
  Induct >> simp[exp_i2_size_def])

val e2sz_def = Lib.with_flag (computeLib.auto_import_definitions, false) (tDefine"e2sz"`
  (e2sz (If_i2 e1 e2 e3) = e2sz e1 + e2sz e2 + e2sz e3 + 1) ∧
  (e2sz (Raise_i2 e) = e2sz e + 1) ∧
  (e2sz (Letrec_i2 funs e) = e2sz e + f2sz funs + 1) ∧
  (e2sz (Mat_i2 e pes) = e2sz e + p2sz pes + 4) ∧
  (e2sz (Handle_i2 e pes) = e2sz e + p2sz pes + 4) ∧
  (e2sz (App_i2 op es) = l2sz es + 1) ∧
  (e2sz (Let_i2 x e1 e2) = e2sz e1 + e2sz e2 + 1) ∧
  (e2sz (Fun_i2 x e) = e2sz e + 1) ∧
  (e2sz (Con_i2 t es) = l2sz es + 1) ∧
  (e2sz _ = (0:num)) ∧
  (l2sz [] = 0) ∧
  (l2sz (e::es) = e2sz e + l2sz es + 1) ∧
  (p2sz [] = 0) ∧
  (p2sz ((p,e)::pes) = e2sz e + p2sz pes + 1) ∧
  (f2sz [] = 0) ∧
  (f2sz ((f,x,e)::funs) = e2sz e + f2sz funs + 1)`)
  (WF_REL_TAC`inv_image $< (\x. case x of
    | INL (e) => exp_i2_size e
    | INR (INL (es)) => exp_i26_size es
    | INR (INR (INL (pes))) => exp_i23_size pes
    | INR (INR (INR (funs))) => exp_i21_size funs)`)

val p2sz_append = prove(
  ``∀p1 p2. p2sz (p1++p2) = p2sz p1 + p2sz p2``,
  Induct >> simp[e2sz_def] >>
  Cases >> simp[e2sz_def])

val (exp_to_exh_def, exp_to_exh_ind) =
  tprove_no_defn ((exp_to_exh_def, exp_to_exh_ind),
  WF_REL_TAC `inv_image $< (\x. case x of
    | INL (_,e) => e2sz e
    | INR (INL (_,es)) => l2sz es
    | INR (INR (INL (_,pes))) => p2sz pes
    | INR (INR (INR (_,funs))) => f2sz funs)` >>
  simp[e2sz_def] >>
  rw[add_default_def] >>
  simp[p2sz_append,e2sz_def])
val _ = register "exp_to_exh" (exp_to_exh_def,exp_to_exh_ind);

val _ = map delete_const ["e2sz","p2sz","l2sz","f2sz","e2sz_UNION"]
val _ = delete_binding "e2sz_ind"

val (pat_to_exh_def, pat_to_exh_ind) =
  tprove_no_defn ((pat_to_exh_def, pat_to_exh_ind),
  WF_REL_TAC `measure pat_i2_size` >>
  srw_tac [ARITH_ss] [pat_i2_size_def] >>
  Induct_on `ps` >>
  srw_tac [ARITH_ss] [pat_i2_size_def] >>
  srw_tac [ARITH_ss] [pat_i2_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "pat_to_exh" (pat_to_exh_def,pat_to_exh_ind);

val (exp_to_pat_def, exp_to_pat_ind) =
  tprove_no_defn ((exp_to_pat_def, exp_to_pat_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,e) => exp_exh_size e
                                        | INR (INL (bvs,es)) => exp_exh6_size es
                                        | INR (INR (INL (bvs,funs))) => exp_exh1_size funs
                                        | INR (INR (INR (bvs,pes))) => exp_exh3_size pes)`);
val _ = register "exp_to_pat" (exp_to_pat_def,exp_to_pat_ind);

val (pat_to_pat_def, pat_to_pat_ind) =
  tprove_no_defn ((pat_to_pat_def, pat_to_pat_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL p => pat_exh_size p
                                        | INR (n,ps) => pat_exh1_size ps)`);
val _ = register "pat_to_pat" (pat_to_pat_def,pat_to_pat_ind);

val (row_to_pat_def, row_to_pat_ind) =
  tprove_no_defn ((row_to_pat_def, row_to_pat_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,p) => pat_exh_size p
                                        | INR (bvs,n,k,ps) => pat_exh1_size ps)`);
val _ = register "row_to_pat" (row_to_pat_def,row_to_pat_ind);

val (Let_Els_pat_def, Let_Els_pat_ind) =
  tprove_no_defn ((Let_Els_pat_def, Let_Els_pat_ind),
  WF_REL_TAC `measure (FST o SND)`);
val _ = register "Let_Els_pat" (Let_Els_pat_def,Let_Els_pat_ind);

val (do_eq_pat_def, do_eq_pat_ind) =
  tprove_no_defn ((do_eq_pat_def, do_eq_pat_ind),
  WF_REL_TAC`inv_image $< (\x. case x of INL (v1,v2) => v_pat_size v1
                                       | INR (vs1,vs2) => v_pat1_size vs1)`);
val _ = register "do_eq_pat" (do_eq_pat_def,do_eq_pat_ind);


(* export rewrites *)
val _ = export_rewrites
  ["exp_to_pat_def"
  ,"patLang.fo_pat_def"
  ,"patLang.ground_pat_def"
  ,"patLang.pure_op_pat_def"]

(* TODO: add missing *)
val _ = export_rewrites
["toBytecode.emit_def","toBytecode.get_label_def","toBytecode.emit_ceref_def","toBytecode.emit_ceenv_def"
,"toBytecode.prim1_to_bc_def","toBytecode.prim2_to_bc_def"
,"free_vars_def","no_closures_def"
,"toBytecode.compile_varref_def","compile_envref_def"
,"mkshift_def"
,"label_closures_def"
,"intLang.doPrim2_def","intLang.CevalPrim2_def","intLang.CevalPrim2s_def","intLang.CevalPrim2p_def"
,"toIntLang.app_to_il_def","toIntLang.unop_to_il_def","toIntLang.binop_to_il_def"
,"intLang.CevalUpd_def","intLang.CevalPrim1_def"
,"free_labs_def","no_labs_def","all_labs_def"
,"toIntLang.exp_to_Cexp_def","toIntLang.v_to_Cv_def"
,"do_Ceq_def","lib.the_def","lib.fapply_def"];

(*
val _ = export_rewrites
["toBytecode.emit_def","toBytecode.get_label_def","toBytecode.emit_ceref_def","toBytecode.emit_ceenv_def"
,"toBytecode.prim1_to_bc_def","toBytecode.prim2_to_bc_def","compiler.cmap_def","toIntLang.cbv_def"
,"toIntLang.remove_mat_vp_def","free_vars_def","no_closures_def"
,"Cv_to_ov_def","v_to_ov_def"
,"toBytecode.compile_varref_def","compile_envref_def"
,"mkshift_def"
,"label_closures_def"
,"toIntLang.Cpat_vars_def"
,"intLang.doPrim2_def","intLang.CevalPrim2_def","intLang.CevalUpd_def","intLang.CevalPrim1_def"
,"free_labs_def","no_labs_def","all_labs_def"
,"intLang.CDiv_excv_def","intLang.CBind_excv_def","intLang.CEq_excv_def"
,"intLang.CDiv_exc_def","intLang.CBind_exc_def","intLang.CEq_exc_def"
,"toIntLang.opn_to_prim2_def"
,"do_Ceq_def"];
*)

(* compilerLibExtra *)

open SatisfySimps arithmeticTheory miscTheory

val the_find_index_suff = store_thm("the_find_index_suff",
  ``∀P d x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (the d (find_index x ls n))``,
  rw[] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][])

val set_lunion = store_thm("set_lunion",
  ``∀l1 l2. set (lunion l1 l2) = set l1 ∪ set l2``,
  Induct >> simp[lunion_def] >> rw[EXTENSION] >> metis_tac[])
val _ = export_rewrites["set_lunion"]

val set_lshift = store_thm("set_lshift",
  ``∀ls n. set (lshift n ls) = { m-n | m | m ∈ set ls ∧ n ≤ m}``,
  Induct >> rw[lshift_def,EXTENSION,MEM_MAP,MEM_FILTER,EQ_IMP_THM] >>
  srw_tac[ARITH_ss,SATISFY_ss][] >> fsrw_tac[ARITH_ss][] >>
  TRY(qexists_tac`h`>>simp[]>>NO_TAC)>>
  TRY(qexists_tac`v`>>simp[]>>NO_TAC)>>
  TRY(qexists_tac`m`>>simp[]>>NO_TAC))
val _ = export_rewrites["set_lshift"]

val sLet_pat_thm = store_thm("sLet_pat_thm",
  ``sLet_pat e1 e2 =
    if e2 = Var_local_pat 0 then e1 else
    if ground_pat 0 e2 then
      if pure_pat e1 then e2 else Seq_pat e1 e2
    else Let_pat e1 e2``,
  Cases_on`e2`>>rw[sLet_pat_def]>>
  Cases_on`n`>>rw[sLet_pat_def])

(* constants that are just applications of higher-order operators *)

val funs_to_exh_MAP = store_thm("funs_to_exh_MAP",
  ``∀exh funs. funs_to_exh exh funs = MAP (λ(f,x,e). (f,x,exp_to_exh exh e)) funs``,
  Induct_on`funs` >> simp[exp_to_exh_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_exh_def])

val funs_to_i2_MAP = store_thm("funs_to_i2_MAP",
  ``∀g funs. funs_to_i2 g funs = MAP (λ(f,x,e). (f,x,exp_to_i2 g e)) funs``,
  Induct_on`funs` >> simp[exp_to_i2_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_i2_def])

val funs_to_i1_MAP = store_thm("funs_to_i1_MAP",
  ``∀menv env funs. funs_to_i1 menv env funs = MAP (λ(f,x,e). (f,x,exp_to_i1 menv (env \\ x) e)) funs``,
  Induct_on`funs` >> simp[exp_to_i1_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_i1_def])

val free_vars_list_MAP = store_thm("free_vars_list_MAP",
  ``∀es. set (free_vars_list es) = set (FLAT (MAP free_vars es))``,
  Induct >> simp[])

val free_vars_defs_MAP = store_thm("free_vars_defs_MAP",
  ``∀n defs. set (free_vars_defs n defs) = set (FLAT (MAP (free_vars_def n) defs))``,
  gen_tac >> Induct >> simp[])

val exps_to_Cexps_MAP = store_thm("exps_to_Cexps_MAP",
  ``∀es. exps_to_Cexps es = MAP exp_to_Cexp es``,
  Induct >> simp[])
val _ = export_rewrites["exps_to_Cexps_MAP"]

val _ = export_theory()
