(*
  Lemmas for connection to FloVer
*)
(* HOL4 *)
open machine_ieeeTheory realTheory realLib RealArith;
(* CakeML *)
open compilerTheory;
(* FloVer *)
open ExpressionsTheory CommandsTheory IEEE_connectionTheory;
(* Icing *)
open CakeMLtoFloVerTheory;
open preamble;

val _ = new_theory "CakeMLtoFloVerLems";

Definition freevars_def:
  freevars [] = EMPTY /\
  freevars [ast$Var n] = { n } /\
  freevars [Lit l] = EMPTY /\
  freevars [Raise e] = freevars [e] /\
  freevars [Handle e pes] =
    FOLDL (\ vars. \ (p,e). (freevars [e]) UNION vars) (freevars [e]) pes /\
  freevars [Con id es] = freevars es /\
  freevars [Fun s e] = freevars [e] DIFF { Short s } /\
  freevars [App op es] = freevars es /\
  freevars [Log lop e1 e2] = (freevars [e1] UNION freevars [e2]) /\
  freevars [If e1 e2 e3] = (freevars [e1] UNION freevars [e2] UNION freevars [e3]) /\
  freevars [Mat e pes] =
    FOLDL (\ vars. \ (p,e). (freevars [e]) UNION vars) (freevars [e]) pes /\
  freevars [Let x e1 e2] =
    freevars [e1] UNION
    (freevars [e2] DIFF (case x of | NONE => EMPTY | SOME s => { Short s })) /\
  freevars [Letrec fs e] = EMPTY (* TODO *) /\
  freevars [Tannot e t] = freevars [e] /\
  freevars [Lannot e l] = freevars [e] /\
  freevars [FpOptimise opt e] = freevars [e] /\
  freevars (e1::es) =
    freevars [e1] UNION freevars es
Termination
  wf_rel_tac `measure exp6_size` \\ fs[]
  \\ Induct_on `pes` \\ fs[]
  \\ rpt strip_tac \\ simp[astTheory.exp_size_def]  \\ rveq
  \\ res_tac
  >- (simp[astTheory.exp_size_def])
  \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[]
End

Theorem lookupCMLVar_id_l:
  lookupCMLVar x ids = SOME (y, n) ==>
  x = y
Proof
  Induct_on `ids` \\ fs[lookupCMLVar_def, updateTheory.FIND_def]
  \\ strip_tac \\ rename1 `(\ (m,i). x = m) h` \\ Cases_on `h` \\  fs[]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem lookupFloVerVar_id_r:
  lookupFloVerVar n ids = SOME (x,m) ==>
  n = m
Proof
  Induct_on `ids` \\ fs[lookupFloVerVar_def, updateTheory.FIND_def]
  \\ strip_tac \\ rename1 `(\ (m,i). n = i) h` \\ Cases_on `h` \\  fs[]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem toFloVerExp_App_cases:
  ∀ varMap op exps fexp.
    toFloVerExp varMap (ast$App op exps) = SOME fexp ⇒
    (∃ w.
     op = FpFromWord ∧ exps = [Lit (Word64 w)] ∧
     fexp = Expressions$Const M64 w) ∨
    (∃ e fexp2.
       (op = FP_uop FP_Neg ∧ exps = [e] ∧
       toFloVerExp varMap e = SOME fexp2 ∧
       fexp = Unop Neg fexp2)) ∨
    (∃ e1 e2 bop theIds2 freshId2 fexp1 fexp2.
      (op = FP_bop bop ∧ exps = [e1; e2] ∧
       toFloVerExp varMap e1 = SOME fexp1 ∧
       toFloVerExp varMap e2 = SOME fexp2 ∧
       fexp = Binop (fpBopToFloVer bop) fexp1 fexp2)) ∨
    (∃ e1 e2 e3 theIds2 theIds3 freshId2 freshId3 fexp1 fexp2 fexp3.
      (op = FP_top FP_Fma ∧ exps = [e1; e2; e3] ∧
       toFloVerExp varMap e1 = SOME fexp1 ∧
       toFloVerExp varMap e2 = SOME fexp2 ∧
       toFloVerExp varMap e3 = SOME fexp3 ∧
       fexp = Fma fexp2 fexp3 fexp1))
Proof
  fs[toFloVerExp_def, option_case_eq, list_case_eq]
  \\ Cases_on `op` \\ fs[]
  \\ TRY (Cases_on `f`)
  \\ fs[list_case_eq, option_case_eq, pair_case_eq]
  \\ rpt strip_tac \\ fs[] \\ rveq \\ fs[]
  \\ Cases_on `e1` \\ TRY (Cases_on `l`) \\ fs[toFloVerConst_def]
QED

Definition ids_unique_def:
  ids_unique ids (freshId:num) =
  ((! x y z.
    lookupCMLVar x ids = SOME (x, y) /\
    lookupFloVerVar z ids = SOME (x, z) ==>
    z = y) /\
  (! x y z.
    lookupCMLVar (Short x) ids = SOME (Short x, z) /\
    lookupFloVerVar z ids = SOME (Short y, z) ==>
    x = y) /\
  (! x y z.
    lookupCMLVar x ids = SOME (x,z) /\
    lookupCMLVar y ids = SOME (y,z) ==>
    x = y) /\
  (! x y z.
    lookupFloVerVar x ids = SOME (z,x) /\
    lookupFloVerVar y ids = SOME (z,y) ==>
    x = y) /\
  (! x y.
    lookupFloVerVar x ids = SOME (y, x) ==>
    lookupCMLVar y ids = SOME (y,x)) /\
  (! x y.
    lookupCMLVar y ids = SOME (y,x) ==>
    lookupFloVerVar x ids = SOME (y, x)) /\
  (∀ x y.
    MEM (x,y) ids ⇒
    lookupFloVerVar y ids = SOME (x,y) ∧
    lookupCMLVar x ids = SOME (x,y)) ∧
  (! id. freshId <= id ==> lookupFloVerVar id ids = NONE) /\
  (! x y. lookupCMLVar x ids = SOME (x, y) ==>
   y < freshId) /\
  ALL_DISTINCT ids)
End

Theorem lookupCMLVar_appendCMLVar:
  ! x y freshId varMap.
    lookupCMLVar x (appendCMLVar y freshId varMap) =
    case lookupCMLVar y varMap of
    | NONE => lookupCMLVar x ((y,freshId)::varMap)
    | SOME _ => lookupCMLVar x varMap
Proof
  rpt strip_tac \\ fs[appendCMLVar_def]
  \\ TOP_CASE_TAC \\ fs[lookupCMLVar_def, updateTheory.FIND_def]
QED

Theorem lookupFloVerVar_appendCMLVar:
  ! x y freshId varMap.
    lookupFloVerVar x (appendCMLVar y freshId varMap) =
    case lookupCMLVar y varMap of
    | NONE => lookupFloVerVar x ((y, freshId)::varMap)
    | SOME _ => lookupFloVerVar x varMap
Proof
  rpt strip_tac \\ fs[appendCMLVar_def]
  \\ TOP_CASE_TAC \\ fs[lookupFloVerVar_def, updateTheory.FIND_def]
QED

Theorem lookupCMLVar_not_mem:
  ! x ids.
  lookupCMLVar x ids = NONE ==>
  ! y. ~ MEM (x,y) ids
Proof
  Induct_on `ids` \\ fs[lookupCMLVar_def]
  \\ rpt strip_tac \\ rveq \\ fs[updateTheory.FIND_def]
  \\ Cases_on `h` \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ res_tac
QED

Theorem lookupCMLVar_mem:
  ! x y ids.
  lookupCMLVar x ids = SOME (x,y) ==>
  MEM (x,y) ids
Proof
  Induct_on `ids` \\ fs[lookupCMLVar_def]
  \\ rpt strip_tac \\ rveq \\ fs[updateTheory.FIND_def]
  \\ Cases_on `h` \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ res_tac
QED

Theorem lookupFloVerVar_not_mem:
  ! y ids.
  lookupFloVerVar y ids = NONE ==>
  ! x. ~ MEM (x,y) ids
Proof
  Induct_on `ids` \\ fs[lookupFloVerVar_def]
  \\ rpt strip_tac \\ rveq \\ fs[updateTheory.FIND_def]
  \\ Cases_on `h` \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ res_tac
QED

Theorem lookupFloVerVar_mem:
  ! x y ids.
  lookupFloVerVar x ids = SOME (y, x) ==>
  MEM (y, x) ids
Proof
  Induct_on `ids` \\ fs[lookupFloVerVar_def]
  \\ rpt strip_tac \\ rveq \\ fs[updateTheory.FIND_def]
  \\ Cases_on `h` \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ res_tac
QED

val tac =
  fs[lookupFloVerVar_appendCMLVar, lookupCMLVar_appendCMLVar] \\ rfs[]
  \\ fs[lookupFloVerVar_def, lookupCMLVar_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp[updateTheory.FIND_def]
  \\ rpt (TOP_CASE_TAC \\ strip_tac \\ fs[] \\ rveq)
  \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[]
  \\ fs[appendCMLVar_def] \\ TOP_CASE_TAC \\ fs[];

Theorem prepareVars_is_unique:
  ! ids floverVars varMap freshId.
    prepareVars ids = SOME (floverVars, varMap, freshId) ==>
    ids_unique varMap freshId
Proof
  Induct_on `ids` \\ fs[prepareVars_def]
  >- (
    rpt strip_tac \\ fs[] \\ rveq
    \\ fs[ids_unique_def, lookupCMLVar_def, lookupFloVerVar_def,
          updateTheory.FIND_def])
  \\ fs[option_case_eq, pair_case_eq, ids_unique_def]
  \\ rpt strip_tac \\ rveq
  >- (tac)
  >- (tac)
  >- (tac)
  >- (tac)
  >- (tac)
  >- (tac)
  >- (
    fs[lookupFloVerVar_appendCMLVar, appendCMLVar_def] \\ rfs[]
    \\ rveq \\ simp[lookupFloVerVar_def, updateTheory.FIND_def]
    \\ TOP_CASE_TAC \\ rveq \\ fs[]
    >- (res_tac \\ fs[] \\ res_tac \\ fs[])
    \\ res_tac \\ fs[lookupFloVerVar_def])
  >- (
    fs[lookupFloVerVar_appendCMLVar, appendCMLVar_def] \\ rfs[]
    \\ rveq \\ simp[lookupCMLVar_def, updateTheory.FIND_def]
    \\ TOP_CASE_TAC \\ rveq \\ fs[]
    >- (res_tac \\ fs[] \\ res_tac \\ fs[])
    \\ res_tac \\ fs[lookupCMLVar_def])
  >- (tac)
  >- (tac)
  \\ imp_res_tac lookupCMLVar_not_mem \\ fs[appendCMLVar_def]
QED

val id_tac =
  imp_res_tac lookupCMLVar_id_l
  \\ imp_res_tac lookupFloVerVar_id_r
  \\ fs[ids_unique_def] \\ res_tac \\ fs[]
  \\ rveq \\ fs[];

Theorem getInterval_inv:
  getInterval e = SOME (x,lo,hi) ==>
  freevars [e] = { Short x } /\
  ? w1 w2.
  e = Log And (App (FP_cmp FP_LessEqual) [App FpFromWord [Lit (Word64 w1)]; Var (Short x)])
  (App (FP_cmp FP_LessEqual) [Var (Short x); App FpFromWord [Lit (Word64 w2)]]) /\
  lo = fp64_to_real w1 /\
  hi = fp64_to_real w2 /\
  fp64_isFinite w1 /\
  fp64_isFinite w2
Proof
  Cases_on `e` \\ simp[getInterval_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq \\ fs[freevars_def]
QED

Theorem toFloVerPre_freevar_FIND:
  ! cake_P ids floverP dVars.
  toFloVerPre cake_P ids = SOME (floverP, dVars) ==>
  ! x. x IN freevars cake_P ==>
  ? n m. lookupCMLVar x ids = SOME (x, n) /\
  FIND (\ m. n = m) dVars = SOME m
Proof
  ho_match_mp_tac toFloVerPre_ind
  \\ rpt strip_tac \\ fs[toFloVerPre_def]
  \\ qpat_x_assum `_ = SOME (_, _)` mp_tac
  \\ reverse TOP_CASE_TAC \\ fs[]
  >- (
    rpt (TOP_CASE_TAC \\ fs[])
    \\ first_assum (mp_then Any assume_tac getInterval_inv)
    \\ rpt strip_tac \\ fs[] \\ rveq
    \\ first_assum (mp_then Any assume_tac lookupCMLVar_id_l)
    \\ rveq \\ fsrw_tac [SATISFY_ss] [updateTheory.FIND_def])
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ fs[freevars_def]
  >- (
    first_assum (mp_then Any assume_tac getInterval_inv)
    \\ first_assum (mp_then Any assume_tac lookupCMLVar_id_l)
    \\ fs[] \\ rveq
    \\ fsrw_tac [SATISFY_ss] [updateTheory.FIND_def])
  \\ res_tac
  \\ imp_res_tac lookupCMLVar_id_l \\ rveq
  \\ fsrw_tac [SATISFY_ss] [updateTheory.FIND_def]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem toFloVerExp_noDowncast:
  ∀ varMap e theExp.
    toFloVerExp varMap e = SOME theExp ⇒
    noDowncast (toRExp theExp)
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac \\ fs[toFloVerExp_def, toRExp_def, noDowncast_def]
  \\ rveq \\ fs[toRExp_def, noDowncast_def]
  \\ every_case_tac \\ fs[] \\ rveq
  \\ fs[toRExp_def, noDowncast_def]
QED

Theorem toFloVerCmd_noDowncastFun:
  ∀ varMap freshId f theIds freshId2 theCmd.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ⇒
    noDowncastFun (toRCmd theCmd)
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def, toRCmd_def, noDowncastFun_def]
  \\ every_case_tac \\ fs[toRCmd_def, noDowncastFun_def] \\ rveq
  \\ fs[toRCmd_def, noDowncastFun_def]
  \\ irule toFloVerExp_noDowncast \\ asm_exists_tac \\ fs[]
QED

Theorem is64BitEnv_prepareGamma:
  ! floverVars. is64BitEnv (prepareGamma floverVars)
Proof
  Induct_on `floverVars` \\ fs[is64BitEnv_def, prepareGamma_def]
  >- (
   rpt strip_tac
   \\ fs[FloverMapTheory.FloverMapTree_find_def,
         FloverMapTheory.FloverMapTree_empty_def])
  \\ rpt strip_tac \\ fs[FloverMapTheory.map_find_add]
  \\ every_case_tac \\ fs[] \\ res_tac
QED

Theorem toFloVerExp_is64BitEval:
  ∀ varMap e theExp.
    toFloVerExp varMap e = SOME theExp ⇒
    is64BitEval (toRExp theExp)
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac \\ fs[toFloVerExp_def, toRExp_def, is64BitEval_def]
  \\ rveq \\ fs[toRExp_def, is64BitEval_def]
  \\ every_case_tac \\ fs[] \\ rveq
  \\ fs[toRExp_def, is64BitEval_def]
QED

Theorem toFloVerCmd_is64BitBstep:
  ∀ varMap freshId f theIds freshId2 theCmd.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ⇒
    is64BitBstep (toRCmd theCmd)
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def, toRCmd_def, is64BitBstep_def]
  \\ every_case_tac \\ fs[toRCmd_def, is64BitBstep_def] \\ rveq
  \\ fs[toRCmd_def, is64BitBstep_def]
  \\ irule toFloVerExp_is64BitEval \\ asm_exists_tac \\ fs[]
QED

Theorem ids_unique_append:
  ∀ x varMap freshId.
    ids_unique varMap freshId ⇒
    ids_unique (appendCMLVar x freshId varMap) (freshId + 1)
Proof
  rpt strip_tac \\ fs[ids_unique_def]
  \\ rpt conj_tac \\ rpt strip_tac \\ fs[] \\ res_tac
  \\ fs[lookupCMLVar_appendCMLVar, lookupFloVerVar_appendCMLVar]
  \\ every_case_tac
  \\ fs[lookupFloVerVar_def, lookupCMLVar_def, appendCMLVar_def,
        updateTheory.FIND_def]
  \\ every_case_tac \\ rveq \\ fs[] \\ res_tac \\ fs[]
  \\ res_tac \\ fs[]
  \\ irule lookupCMLVar_not_mem \\ fs[lookupCMLVar_def]
QED

Theorem toFloVerCmd_ids_unique:
  ∀ varMap freshId f theIds freshId2 theCmd.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
    ids_unique varMap freshId ⇒
    ids_unique theIds freshId2
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac
  \\ fs[Once toFloVerCmd_def, option_case_eq, pair_case_eq] \\ rveq
  \\ fs[]
  \\ imp_res_tac ids_unique_append
  \\ fs[]
QED

Theorem toFloVerCmd_lookup_mono:
  ∀ ids freshId e ids2 freshId2 theCmd.
    toFloVerCmd ids freshId e = SOME (ids2, freshId2, theCmd) ∧
    ids_unique ids freshId ⇒
    (∀ n x.
      lookupFloVerVar n ids = SOME (x, n) ⇒
      lookupFloVerVar n ids2 = SOME (x,n))
    ∧
    (∀ x n.
      lookupCMLVar x ids = SOME (x,n) ⇒
      lookupCMLVar x ids2 = SOME (x,n))
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac
  \\ qpat_x_assum `toFloVerCmd _ _ _ = SOME _` mp_tac
  \\ simp[Once toFloVerCmd_def] \\ rpt strip_tac
  \\ TRY (fs[option_case_eq, pair_case_eq] \\ rveq \\ fs[])
  \\ fs[]
  \\ last_x_assum mp_tac \\ impl_tac \\ fs[]
  \\ TRY (irule ids_unique_append \\ asm_exists_tac \\ fs[])
  \\ strip_tac
  \\ first_x_assum irule
  \\ fs[lookupFloVerVar_appendCMLVar, lookupCMLVar_appendCMLVar,
        lookupFloVerVar_def, lookupCMLVar_def, updateTheory.FIND_def]
  \\ TOP_CASE_TAC \\ fs[] \\ rveq
  \\ fs[ids_unique_def] \\ fs[lookupFloVerVar_def, lookupCMLVar_def]
  \\ rfs[]
QED

Theorem toRExp_usedVars_agree:
  ! v e.
    v IN (domain (usedVars (toRExp e))) <=>
    v IN domain (usedVars e)
Proof
  Induct_on `e` \\ simp[Once usedVars_def, toRExp_def, domain_union]
  \\ rpt strip_tac \\ TRY EQ_TAC \\ rpt strip_tac \\ res_tac
  \\ fs[Once usedVars_def, domain_union]
  >- (simp[Once usedVars_def])
  >- (simp[Once usedVars_def])
  >- (DISJ2_TAC \\ simp[Once usedVars_def])
  >- (simp[Once usedVars_def])
  >- (DISJ2_TAC \\ simp[Once usedVars_def])
  >- (rpt DISJ2_TAC \\ simp[Once usedVars_def])
  \\ simp[Once usedVars_def]
QED

Theorem toRCmd_freeVars_agree:
  ! v theCmd.
  v IN (domain (freeVars (toRCmd theCmd))) <=>
  v IN domain (freeVars theCmd)
Proof
  Induct_on `theCmd` \\ simp[Once freeVars_def, freevars_def, toRCmd_def, domain_union]
  \\ rpt strip_tac
  >- (
    EQ_TAC \\ rpt strip_tac
    \\ imp_res_tac toRExp_usedVars_agree
    >- (simp[Once freeVars_def, domain_union])
    >- (simp[Once freeVars_def, domain_union])
    >- (pop_assum mp_tac \\ simp[Once freeVars_def]
        \\ rpt strip_tac \\ fs[domain_union, toRExp_usedVars_agree])
    \\ rveq \\ fs[Once freeVars_def, domain_union])
  \\ fs[Once freeVars_def, toRExp_usedVars_agree]
QED

Theorem toFloVerExp_usedvars_freevars:
  ∀ varMap f theExp freshId.
  toFloVerExp varMap f = SOME theExp ∧
  ids_unique varMap freshId ⇒
  ∀ x. x IN domain (usedVars theExp) ⇒
   ∃ y. lookupFloVerVar x varMap = SOME (y,x) ∧
   y IN freevars [f]
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 `App op exps` \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum `toFloVerExp _ _ = SOME _` mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  \\ fs[Once toFloVerExp_def, option_case_eq, pair_case_eq, list_case_eq]
  \\ rveq
  >- (
    fs[usedVars_def] \\ rveq
    \\ imp_res_tac lookupCMLVar_id_l \\ rveq
    \\ fs[ids_unique_def] \\ res_tac \\ fs[freevars_def])
  >- (fs[usedVars_def])
  >- (
    qpat_x_assum `x IN domain (usedVars _)` mp_tac
    \\ simp[Once usedVars_def] \\ strip_tac
    \\ res_tac \\ fs[freevars_def])
  >- (
   qpat_x_assum `x IN domain (usedVars _)` mp_tac
   \\ simp[Once usedVars_def, domain_union] \\ strip_tac
   \\ res_tac \\ fs[freevars_def])
  >- (
   qpat_x_assum `x IN domain (usedVars _)` mp_tac
   \\ simp[Once usedVars_def, domain_union] \\ strip_tac
   \\ res_tac \\ fs[freevars_def])
QED

Theorem toFloVerExp_freevars_usedvars:
  ∀ varMap f theExp freshId.
  toFloVerExp varMap f = SOME theExp ∧
  ids_unique varMap freshId ⇒
  ∀ x. x IN freevars [f] ⇒
   ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧
   y IN domain (usedVars theExp)
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 `App op exps` \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum `toFloVerExp _ _ = SOME _` mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  \\ fs[Once toFloVerExp_def, option_case_eq, pair_case_eq, list_case_eq]
  \\ rveq
  >- (
    fs[freevars_def] \\ rveq
    \\ imp_res_tac lookupCMLVar_id_l \\ rveq
    \\ fs[ids_unique_def] \\ res_tac \\ fs[usedVars_def])
  >- (fs[freevars_def])
  >- (
    qpat_x_assum `x IN freevars _` mp_tac
    \\ simp[Once freevars_def] \\ strip_tac
    \\ res_tac \\ simp[Once usedVars_def])
  >- (
    qpat_x_assum `x IN freevars _` mp_tac
    \\ simp[freevars_def] \\ strip_tac
    \\ res_tac \\ simp[Once usedVars_def, domain_union])
  >- (
    qpat_x_assum `x IN freevars _` mp_tac
    \\ simp[freevars_def] \\ strip_tac
    \\ res_tac \\ simp[Once usedVars_def, domain_union])
QED

Theorem toFloVerCmd_freeVars_freevars:
  ∀ varMap freshId f theIds freshId2 theCmd.
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
  ids_unique varMap freshId ⇒
  ∀ x. x IN freevars [f] ⇒
  ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧
   y IN domain (freeVars theCmd)
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def, option_case_eq, pair_case_eq]
  \\ rveq \\ TRY (qpat_x_assum `x IN freevars _` mp_tac)
  \\ simp[freevars_def]
  \\ rpt strip_tac
  \\ simp[Once freeVars_def, domain_union]
  >- (
    imp_res_tac toFloVerExp_freevars_usedvars
    \\ fs[]
    \\ CCONTR_TAC \\ fs[ids_unique_def]
    \\ rveq \\ fs[] \\ res_tac \\ fs[])
  >- (
    fs[] \\ last_x_assum mp_tac
    \\ impl_tac
    >- (irule ids_unique_append \\ fs[])
    \\ strip_tac
    \\ res_tac \\ fs[lookupCMLVar_appendCMLVar]
    \\ rfs[lookupCMLVar_def, updateTheory.FIND_def]
    \\ CCONTR_TAC \\ fs[ids_unique_def, lookupCMLVar_def]
    \\ rveq \\ fs[] \\ res_tac \\ fs[])
  \\ imp_res_tac toFloVerExp_freevars_usedvars
  \\ fs[freevars_def]
QED

Theorem toFloVerCmd_freevars_freeVars:
  ∀ varMap freshId f theIds freshId2 theCmd.
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
  ids_unique varMap freshId ⇒
  ∀ x. x IN domain (freeVars theCmd) ⇒
  ∃ y. lookupFloVerVar x varMap = SOME (y,x) ∧
   y IN freevars [f]
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def, option_case_eq, pair_case_eq]
  \\ rveq \\ qpat_x_assum `_ IN domain (freeVars _)` mp_tac
  \\ simp[Once freeVars_def, domain_union]
  \\ rpt strip_tac
  \\ simp[freevars_def]
  >- (
    imp_res_tac toFloVerExp_usedvars_freevars
    \\ fs[])
  >- (
    fs[] \\ last_x_assum mp_tac
    \\ impl_tac
    >- (irule ids_unique_append \\ fs[])
    \\ strip_tac
    \\ res_tac \\ fs[lookupFloVerVar_appendCMLVar]
    \\ rfs[lookupFloVerVar_def, updateTheory.FIND_def]
    \\ DISJ2_TAC \\ CCONTR_TAC
    \\ fs[ids_unique_def, lookupCMLVar_def, lookupFloVerVar_def]
    \\ rveq \\ fs[] \\ res_tac \\ fs[])
  \\ imp_res_tac toFloVerExp_usedvars_freevars
  \\ fs[freevars_def]
QED

Theorem prepareVars_agrees_FloVer:
  ! ids floverVars varMap freshId.
  prepareVars ids = SOME (floverVars, varMap, freshId) ==>
  ! x s. lookupFloVerVar x varMap = SOME (s, x) ==>
  ? n. s = Short n /\ MEM n ids /\
  MEM x floverVars
Proof
  Induct_on `ids`
  >- (fs[prepareVars_def, lookupFloVerVar_def, updateTheory.FIND_def])
  \\ fs[prepareVars_def, option_case_eq, pair_case_eq]
  \\ rpt strip_tac \\ rveq
  \\ fs[lookupFloVerVar_appendCMLVar]
  \\ rfs[lookupFloVerVar_def, updateTheory.FIND_def]
  \\ imp_res_tac prepareVars_is_unique
  \\ every_case_tac \\ rveq
  \\ fs[ids_unique_def] \\ res_tac
  \\ rveq \\ fs[]
QED

Theorem checkFreevars_correct:
  checkFreevars xs ys ⇒
  ∀ x.
    MEM x xs ⇒ MEM x ys
Proof
  Induct_on ‘xs’ \\ fs[checkFreevars_def]
  \\ rpt strip_tac \\ rveq \\ fs[]
QED

Theorem MEM_FST:
  ∀ x y ps.
    MEM (x,y) ps ⇒ MEM x (MAP FST ps)
Proof
  Induct_on ‘ps’ \\ fs[MEM]
  \\ rpt strip_tac \\ fs[]
  >- (Cases_on ‘h’ \\ fs[])
  \\ res_tac \\ fs[]
QED

Theorem freevars_list_freevars_exp:
  ∀ varMap f theExp.
  toFloVerExp varMap f = SOME theExp ⇒
  ∀ x. MEM x (freevars_list [f]) ⇒
  x IN freevars [f]
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 `App op exps` \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum `toFloVerExp _ _ = SOME _` mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  \\ fs[Once toFloVerExp_def, option_case_eq, pair_case_eq, list_case_eq]
  \\ rveq
  \\ fs[freevars_list_def, freevars_def]
QED

Theorem freevars_list_freevars_cmd:
  ∀ varMap freshId f theIds freshId2 theExp.
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theExp) ⇒
  ∀ x. MEM x (freevars_list [f]) ⇒
  x IN freevars [f]
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def, option_case_eq, pair_case_eq]
  >- (
    rveq \\ fs[freevars_list_def, freevars_def]
    >- (imp_res_tac freevars_list_freevars_exp \\ fs[])
    \\ fs[MEM_FILTER])
  \\ imp_res_tac freevars_list_freevars_exp \\ fs[]
QED

Theorem freevars_agree_varMap:
  ∀ varMap freshId f theIds freshId2 theExp.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theExp) ∧
    checkFreevars (MAP FST varMap) (freevars_list [f]) ⇒
    ∀ x y. lookupCMLVar x varMap = SOME (x,y) ⇒
      x IN freevars [f]
Proof
  rpt strip_tac
  \\ ‘MEM (x,y) varMap’ by (irule lookupCMLVar_mem \\ fs[])
  \\ ‘MEM x (MAP FST varMap)’ by (irule MEM_FST \\ fsrw_tac [SATISFY_ss] [])
  \\ ‘MEM x (freevars_list [f])’
    by (irule checkFreevars_correct \\ fsrw_tac [SATISFY_ss] [])
  \\ irule freevars_list_freevars_cmd \\ fsrw_tac [SATISFY_ss] []
QED

Theorem freeVars_agree_varMap:
  ∀ varMap freshId f theIds freshId2 theCmd.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
    ids_unique varMap freshId ∧
    checkFreevars (MAP FST varMap) (freevars_list [f]) ⇒
    ∀ x y. lookupFloVerVar y varMap = SOME (x,y) ⇒
      y IN domain (freeVars theCmd)
Proof
  rpt strip_tac
  \\ ‘MEM (x,y) varMap’ by (irule lookupFloVerVar_mem \\ fs[])
  \\ ‘MEM x (MAP FST varMap)’ by (irule MEM_FST \\ fsrw_tac [SATISFY_ss] [])
  \\ ‘MEM x (freevars_list [f])’
    by (irule checkFreevars_correct \\ fsrw_tac [SATISFY_ss] [])
  \\ ‘x IN freevars [f]’ by (irule freevars_list_freevars_cmd \\ fsrw_tac [SATISFY_ss] [])
  \\ imp_res_tac toFloVerCmd_freeVars_freevars
  \\ imp_res_tac toFloVerCmd_ids_unique
  \\ fs[ids_unique_def] \\ res_tac \\ rveq \\ fs[]
QED

val _ = export_theory();
