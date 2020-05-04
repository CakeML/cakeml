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
  freevars [] = EMPTY ∧
  freevars [ast$Var n] = { n } ∧
  freevars [Lit l] = EMPTY ∧
  freevars [Raise e] = freevars [e] ∧
  freevars [Handle e pes] =
    FOLDL (λ vars. λ (p,e). (freevars [e]) ∪ vars) (freevars [e]) pes ∧
  freevars [Con id es] = freevars es ∧
  freevars [Fun s e] = freevars [e] DIFF { Short s } ∧
  freevars [App op es] = freevars es ∧
  freevars [Log lop e1 e2] = (freevars [e1] ∪ freevars [e2]) ∧
  freevars [If e1 e2 e3] = (freevars [e1] ∪ freevars [e2] ∪ freevars [e3]) ∧
  freevars [Mat e pes] =
    FOLDL (λ vars. λ (p,e). (freevars [e]) ∪ vars) (freevars [e]) pes ∧
  freevars [Let x e1 e2] =
    freevars [e1] ∪
    (freevars [e2] DIFF (case x of | NONE => EMPTY | SOME s => { Short s })) ∧
  freevars [Letrec fs e] = EMPTY (* TODO *) ∧
  freevars [Tannot e t] = freevars [e] ∧
  freevars [Lannot e l] = freevars [e] ∧
  freevars [FpOptimise opt e] = freevars [e] ∧
  freevars (e1::es) =
    freevars [e1] ∪ freevars es
Termination
  wf_rel_tac ‘measure exp6_size’ \\ fs[]
  \\ Induct_on ‘pes’ \\ fs[]
  \\ rpt strip_tac \\ simp[astTheory.exp_size_def]  \\ rveq
  \\ res_tac
  >- (simp[astTheory.exp_size_def])
  \\ first_x_assum (qspec_then ‘e’ assume_tac) \\ fs[]
End

Theorem lookupCMLVar_id_l:
  lookupCMLVar x ids = SOME (y, n) ⇒
  x = y
Proof
  Induct_on ‘ids’ \\ fs[lookupCMLVar_def, updateTheory.FIND_def]
  \\ strip_tac \\ rename1 ‘(λ (m,i). x = m) h’ \\ Cases_on ‘h’ \\  fs[]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem lookupFloVerVar_id_r:
  lookupFloVerVar n ids = SOME (x,m) ⇒
  n = m
Proof
  Induct_on ‘ids’ \\ fs[lookupFloVerVar_def, updateTheory.FIND_def]
  \\ strip_tac \\ rename1 ‘(λ (m,i). n = i) h’ \\ Cases_on ‘h’ \\  fs[]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem toFloVerExp_App_cases:
  ∀ varMap freshId op exps theIds1 freshId1 fexp.
    toFloVerExp varMap freshId (App op exps) = SOME (theIds1, freshId1, fexp) ⇒
    (∃ w.
     op = FpFromWord ∧ exps = [Lit (Word64 w)] ∧
     fexp = Expressions$Const M64 w ∧
     varMap = theIds1 ∧ freshId = freshId1) ∨
    (∃ e fexp2.
       (op = FP_uop FP_Neg ∧ exps = [e] ∧
       toFloVerExp varMap freshId e = SOME (theIds1, freshId1, fexp2) ∧
       fexp = Unop Neg fexp2)) ∨
    (∃ e1 e2 bop theIds2 freshId2 fexp1 fexp2.
      (op = FP_bop bop ∧ exps = [e1; e2] ∧
       toFloVerExp varMap freshId e1 = SOME (theIds2, freshId2, fexp1) ∧
       toFloVerExp theIds2 freshId2 e2 = SOME (theIds1, freshId1, fexp2) ∧
       fexp = Binop (fpBopToFloVer bop) fexp1 fexp2)) ∨
    (∃ e1 e2 e3 theIds2 theIds3 freshId2 freshId3 fexp1 fexp2 fexp3.
      (op = FP_top FP_Fma ∧ exps = [e1; e2; e3] ∧
       toFloVerExp varMap freshId e1 = SOME (theIds2, freshId2, fexp1) ∧
       toFloVerExp theIds2 freshId2 e2 = SOME (theIds3, freshId3, fexp2) ∧
       toFloVerExp theIds3 freshId3 e3 = SOME (theIds1, freshId1, fexp3) ∧
       fexp = Fma fexp2 fexp3 fexp1))
Proof
  fs[toFloVerExp_def, option_case_eq, list_case_eq]
  \\ Cases_on ‘op’ \\ fs[]
  \\ TRY (Cases_on ‘f’)
  \\ fs[list_case_eq, option_case_eq, pair_case_eq]
  \\ rpt strip_tac \\ fs[] \\ rveq \\ fs[]
  \\ Cases_on ‘e1’ \\ TRY (Cases_on ‘l’) \\ fs[toFloVerConst_def]
QED

Theorem toFloVerExp_usedVars:
  ∀ ids freshId e ids2 freshId2 fexp.
    toFloVerExp ids freshId e = SOME (ids2, freshId2, fexp) ⇒
    ∀ n. freshId ≤ n ∧ n < freshId2 ⇒
      n IN domain (usedVars (fexp))
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac \\ TRY (fs[toFloVerExp_def] \\ NO_TAC)
  >- (
   qpat_x_assum ‘_ = SOME _’ mp_tac \\ fs[toFloVerExp_def]
   \\ rpt (TOP_CASE_TAC \\ fs[])
   \\ rpt strip_tac \\ rveq \\ fs[usedVars_def])
  \\ first_x_assum (mp_then Any assume_tac toFloVerExp_App_cases)
  \\ fs[] \\ rveq \\ fs[]
  \\ simp[Once usedVars_def, domain_union]
  \\ TRY (metis_tac[])
  \\ TRY (Cases_on ‘n < freshId2'’\\ fs[] \\ metis_tac[])
  \\ TRY (Cases_on ‘n < freshId2'’\\ fs[] \\ TRY (metis_tac[])
          \\ Cases_on ‘n < freshId3’ \\ fs[] \\ metis_tac[])
QED

Theorem getInterval_inv:
  getInterval e = SOME (x,lo,hi) ⇒
  freevars [e] = { Short x } ∧
  ∃ w1 w2.
  e = Log And (App (FP_cmp FP_LessEqual) [Lit (Word64 w1); Var (Short x)])
  (App (FP_cmp FP_LessEqual) [Var (Short x); Lit (Word64 w2)]) ∧
  lo = fp64_to_real w1 ∧
  hi = fp64_to_real w2 ∧
  fp64_isFinite w1 ∧
  fp64_isFinite w2
Proof
  Cases_on ‘e’ \\ simp[getInterval_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq \\ fs[freevars_def]
QED

Theorem toFloVerPre_freevar_FIND:
  ∀ cake_P ids floverP dVars.
  toFloVerPre cake_P ids = SOME (floverP, dVars) ⇒
  ∀ x. x IN freevars cake_P ⇒
  ∃ n m. lookupCMLVar x ids = SOME (x, n) ∧
  FIND (λ m. n = m) dVars = SOME m
Proof
  ho_match_mp_tac toFloVerPre_ind
  \\ rpt strip_tac \\ fs[toFloVerPre_def]
  \\ qpat_x_assum ‘_ = SOME (_, _)’ mp_tac
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

Definition ids_unique_def:
  ids_unique ids (freshId:num) =
  ((∀ x y z.
    lookupCMLVar x ids = SOME (x, y) ∧
    lookupFloVerVar z ids = SOME (x, z) ⇒
    z = y) ∧
  (∀ x y z.
    lookupCMLVar (Short x) ids = SOME (Short x, z) ∧
    lookupFloVerVar z ids = SOME (Short y, z) ⇒
    x = y) ∧
  (∀ x y z.
    lookupCMLVar x ids = SOME (x,z) ∧
    lookupCMLVar y ids = SOME (y,z) ⇒
    x = y) ∧
  (∀ x y z.
    lookupFloVerVar x ids = SOME (z,x) ∧
    lookupFloVerVar y ids = SOME (z,y) ⇒
    x = y) ∧
  (∀ x y.
    lookupFloVerVar x ids = SOME (y, x) ⇒
    lookupCMLVar y ids = SOME (y,x)) ∧
  (∀ x y.
    lookupCMLVar y ids = SOME (y,x) ⇒
    lookupFloVerVar x ids = SOME (y, x)) ∧
  (∀ id. freshId ≤ id ⇒ lookupFloVerVar id ids = NONE) ∧
  (∀ x y. lookupCMLVar x ids = SOME (x, y) ⇒
     y < freshId))
End

Theorem lookupCMLVar_appendCMLVar:
  ∀ x y freshId varMap.
    lookupCMLVar x (appendCMLVar y freshId varMap) =
    case lookupCMLVar y varMap of
    | NONE => lookupCMLVar x ((y,freshId)::varMap)
    | SOME _ => lookupCMLVar x varMap
Proof
  rpt strip_tac \\ fs[appendCMLVar_def]
  \\ TOP_CASE_TAC \\ fs[lookupCMLVar_def, updateTheory.FIND_def]
QED

Theorem lookupFloVerVar_appendCMLVar:
  ∀ x y freshId varMap.
    lookupFloVerVar x (appendCMLVar y freshId varMap) =
    case lookupCMLVar y varMap of
    | NONE => lookupFloVerVar x ((y, freshId)::varMap)
    | SOME _ => lookupFloVerVar x varMap
Proof
  rpt strip_tac \\ fs[appendCMLVar_def]
  \\ TOP_CASE_TAC \\ fs[lookupFloVerVar_def, updateTheory.FIND_def]
QED

Theorem prepareVars_is_unique:
  ∀ ids floverVars varMap freshId.
    prepareVars ids = SOME (floverVars, varMap, freshId) ⇒
    ids_unique varMap freshId
Proof
  Induct_on ‘ids’ \\ fs[prepareVars_def]
  >- (
    rpt strip_tac \\ fs[] \\ rveq
    \\ fs[ids_unique_def, lookupCMLVar_def, lookupFloVerVar_def,
          updateTheory.FIND_def])
  \\ fs[option_case_eq, pair_case_eq, ids_unique_def]
  \\ rpt strip_tac \\ rveq
  \\ fs[lookupFloVerVar_appendCMLVar, lookupCMLVar_appendCMLVar] \\ rfs[]
  \\ fs[lookupFloVerVar_def, lookupCMLVar_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp[updateTheory.FIND_def]
  \\ rpt (TOP_CASE_TAC \\ strip_tac \\ fs[] \\ rveq)
  \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[]
QED

Theorem prepareVars_agrees_CakeML:
  ∀ ids floverVars varMap freshId.
  prepareVars ids = SOME (floverVars, varMap, freshId) ⇒
  ∀ s. MEM s ids ⇒
  ∃ x. lookupCMLVar (Short s) varMap = SOME (Short s, x) ∧
  MEM x floverVars
Proof
  Induct_on ‘ids’ \\ fs[prepareVars_def]
  \\ rpt strip_tac \\ rveq
  \\ fs[option_case_eq, pair_case_eq] \\ rveq
  \\ fs [lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def]
  \\ res_tac
  \\ imp_res_tac prepareVars_is_unique
  \\ ‘s ≠ h’
     by (CCONTR_TAC \\ fs[] \\ rveq \\ fs[ids_unique_def] \\ res_tac)
  \\ fs[]
QED

Theorem prepareVars_agrees_FloVer:
  ∀ ids floverVars varMap freshId.
  prepareVars ids = SOME (floverVars, varMap, freshId) ⇒
  ∀ x s. lookupFloVerVar x varMap = SOME (s, x) ⇒
  ∃ n. s = Short n ∧ MEM n ids ∧
  MEM x floverVars
Proof
  Induct_on ‘ids’
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

Theorem toFloVerExp_noDowncast:
  ∀ varMap freshId e theIds freshId2 theExp.
    toFloVerExp varMap freshId e = SOME (theIds, freshId2, theExp) ⇒
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
  ∀ floverVars. is64BitEnv (prepareGamma floverVars)
Proof
  Induct_on ‘floverVars’ \\ fs[is64BitEnv_def, prepareGamma_def]
  >- (
   rpt strip_tac
   \\ fs[FloverMapTheory.FloverMapTree_find_def,
         FloverMapTheory.FloverMapTree_empty_def])
  \\ rpt strip_tac \\ fs[FloverMapTheory.map_find_add]
  \\ every_case_tac \\ fs[] \\ res_tac
QED

Theorem toFloVerExp_is64BitEval:
  ∀ varMap freshId e theIds freshId2 theExp.
    toFloVerExp varMap freshId e = SOME (theIds, freshId2, theExp) ⇒
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
  \\ every_case_tac \\ fs[lookupFloVerVar_def, lookupCMLVar_def, updateTheory.FIND_def]
  \\ every_case_tac \\ rveq \\ fs[] \\ res_tac \\ fs[]
QED

Theorem toFloVerExp_ids_unique:
  ∀ varMap freshId f theIds freshId2 theExp.
    toFloVerExp varMap freshId f = SOME (theIds, freshId2, theExp) ∧
    ids_unique varMap freshId ⇒
    ids_unique theIds freshId2
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ fs[Once toFloVerExp_def, option_case_eq, pair_case_eq, list_case_eq]
  \\ rveq \\ fs[ids_unique_append]
  \\ Cases_on ‘op’ \\ fs[list_case_eq, option_case_eq, pair_case_eq]
  \\ rveq \\ fs[]
  \\ Cases_on ‘f’ \\ fs[option_case_eq, pair_case_eq]
QED

Theorem toFloVerCmd_ids_unique:
  ∀ varMap freshId f theIds freshId2 theCmd.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ⇒
    ids_unique varMap freshId ⇒
    ids_unique theIds freshId2
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac
  \\ fs[Once toFloVerCmd_def, option_case_eq, pair_case_eq] \\ rveq
  \\ fs[]
  \\ imp_res_tac toFloVerExp_ids_unique
  \\ imp_res_tac ids_unique_append
  \\ fs[]
QED

Theorem toFloVerExp_lookup_mono:
  ∀ ids freshId e ids2 freshId2 fexp.
  toFloVerExp ids freshId e = SOME (ids2, freshId2, fexp) ⇒
  ids_unique ids freshId ⇒
  (∀ n x. lookupFloVerVar n ids = SOME (x, n) ⇒
   lookupFloVerVar n ids2 = SOME (x,n)) ∧
  (∀ x n. lookupCMLVar x ids = SOME (x,n) ⇒
   lookupCMLVar x ids2 = SOME (x,n))
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ fs[lookupFloVerVar_appendCMLVar, lookupFloVerVar_def, ids_unique_def, updateTheory.FIND_def]
    \\ TOP_CASE_TAC \\ fs[] \\ rveq \\ first_x_assum (qspec_then ‘freshId’ assume_tac) \\ fs[])
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, ids_unique_def, updateTheory.FIND_def]
    \\ TOP_CASE_TAC \\ fs[] \\ rveq \\ first_x_assum (qspec_then ‘freshId’ assume_tac) \\ fs[])
  >- (
     rveq \\ fs[])
  >- (
     rveq \\ fs[])
  \\ rveq \\ fs[] \\ rpt strip_tac \\ TRY (Cases_on ‘f’) \\ fs[option_case_eq, pair_case_eq]
  \\ rveq \\ imp_res_tac toFloVerExp_ids_unique
  \\ res_tac \\ res_tac
QED

Theorem toFloVerCmd_lookup_mono:
  ∀ ids freshId e ids2 freshId2 theCmd.
  toFloVerCmd ids freshId e = SOME (ids2, freshId2, theCmd) ⇒
  ids_unique ids freshId ⇒
  (∀ n x. lookupFloVerVar n ids = SOME (x, n) ⇒
   lookupFloVerVar n ids2 = SOME (x,n)) ∧
  (∀ x n. lookupCMLVar x ids = SOME (x,n) ⇒
   lookupCMLVar x ids2 = SOME (x,n))
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac
  \\ qpat_x_assum ‘toFloVerCmd _ _ _ = SOME _’ mp_tac
  \\ simp[Once toFloVerCmd_def] \\ rpt strip_tac
  \\ TRY (fs[option_case_eq, pair_case_eq] \\ rveq \\ imp_res_tac toFloVerExp_lookup_mono)
  \\ fs[]
  \\ last_x_assum mp_tac \\ impl_tac \\ fs[]
  \\ TRY (irule ids_unique_append \\ irule toFloVerExp_ids_unique \\ asm_exists_tac \\ fs[])
  \\ strip_tac
  \\ first_x_assum irule
  \\ fs[lookupFloVerVar_appendCMLVar, lookupCMLVar_appendCMLVar,
        lookupFloVerVar_def, lookupCMLVar_def, updateTheory.FIND_def]
  \\ TOP_CASE_TAC \\ fs[] \\ rveq
  \\ imp_res_tac toFloVerExp_ids_unique
  \\ fs[ids_unique_def] \\ fs[lookupFloVerVar_def, lookupCMLVar_def]
QED

Theorem toFloVerExp_freevars_agree:
  ∀ varMap freshId f theIds freshId2 theExp v.
    toFloVerExp varMap freshId f = SOME (theIds, freshId2, theExp) ∧
    ids_unique varMap freshId ∧
    v ∈ domain (usedVars theExp) ⇒
    ∃ x. lookupFloVerVar v theIds = SOME (x, v) ∧
      x IN freevars [f]
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  \\ fs[Once toFloVerExp_def, option_case_eq, pair_case_eq, list_case_eq]
  \\ rveq
  >- (
    fs[usedVars_def, freevars_def] \\ rveq
    \\ fs[lookupFloVerVar_def, appendCMLVar_def, updateTheory.FIND_def])
  >- (
    fs[usedVars_def, freevars_def] \\ rveq \\ fs[ids_unique_def]
    \\ imp_res_tac lookupCMLVar_id_l \\ rveq
    \\ res_tac \\ fs[])
  >- (
    fs[usedVars_def])
  \\ rveq \\ qpat_x_assum ‘_ IN domain (usedVars _)’ mp_tac
  \\ simp[Once usedVars_def, domain_union] \\ rpt strip_tac
  \\ imp_res_tac toFloVerExp_ids_unique
  \\ TRY (fs[] \\ res_tac \\ fsrw_tac [SATISFY_ss] [freevars_def])
  \\ imp_res_tac toFloVerExp_lookup_mono
  \\ res_tac \\ fs[]
QED

Theorem toFloVerCmd_freevars_agree:
  ∀ varMap freshId f theIds freshId2 theCmd v.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
    ids_unique varMap freshId ∧
    v ∈ domain (freeVars theCmd) ⇒
    ∃ x. lookupFloVerVar v theIds = SOME (x, v) ∧
      x IN freevars [f]
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac
  \\ fs[Once toFloVerCmd_def, option_case_eq, pair_case_eq] \\ rveq
  \\ TRY (fs[Once freeVars_def] \\ imp_res_tac toFloVerExp_freevars_agree \\ fs[] \\ NO_TAC)
  \\ fs[]
  \\ imp_res_tac toFloVerExp_ids_unique
  \\ imp_res_tac toFloVerCmd_ids_unique
  \\ qpat_x_assum ‘v IN domain (freeVars _)’ mp_tac
  \\ rename1 ‘ids_unique (appendCMLVar (Short x) freshId3 ids2) (freshId3 + 1)’
  \\ ‘ids_unique (appendCMLVar (Short x) freshId3 ids2) (freshId3 + 1)’
     by (irule ids_unique_append \\ fs[])
  \\ fs[]
  \\ simp[Once freeVars_def, domain_union] \\ rpt strip_tac \\ fs[]
  >- (
    imp_res_tac toFloVerExp_freevars_agree \\ fs[] \\ rveq
    \\ imp_res_tac toFloVerCmd_lookup_mono \\ fs[]
    \\ rename1 ‘lookupFloVerVar n ids2 = SOME (y,n)’
    \\ ‘lookupFloVerVar n (appendCMLVar (Short x) freshId3 ids2) = SOME (y,n)’
      by (fs[lookupFloVerVar_appendCMLVar, lookupFloVerVar_def,
             updateTheory.FIND_def])
    \\ res_tac \\ fs[freevars_def])
  \\ first_x_assum drule \\ fs[freevars_def] \\ disch_then assume_tac
  \\ fs[]
  \\ Cases_on ‘x' = Short x’ \\ fs[]
  \\ rveq
  \\ ‘lookupCMLVar (Short x) ids3 = SOME (Short x, v)’
    by (fs[ids_unique_def])
  \\ fs[appendCMLVar_def]
  \\ ‘lookupCMLVar (Short x) ((Short x, freshId3)::ids2) = SOME (Short x, freshId3)’
     by EVAL_TAC
  \\ rfs[]
  \\ imp_res_tac toFloVerCmd_lookup_mono
  \\ fs[]
QED

Theorem toRExp_usedVars_agree:
  ∀ v e.
    v IN (domain (usedVars (toRExp e))) ⇒
    v IN domain (usedVars e)
Proof
  Induct_on ‘e’ \\ simp[Once usedVars_def, toRExp_def, domain_union]
  \\ rpt strip_tac \\ res_tac
  \\ simp[Once usedVars_def, domain_union]
QED

Theorem toRCmd_freeVars_agree:
  ∀ v theCmd.
  v IN (domain (freeVars (toRCmd theCmd))) ⇒
  v IN domain (freeVars theCmd)
Proof
  Induct_on ‘theCmd’ \\ simp[Once freeVars_def, toRCmd_def, domain_union]
  \\ rpt strip_tac
  \\ imp_res_tac toRExp_usedVars_agree
  \\ res_tac
  \\ simp[Once freeVars_def, domain_union]
QED

val _ = export_theory();
