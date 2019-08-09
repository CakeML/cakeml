(**
  This file contains proofs about the matching and instantiation functions
  defined in patternScript.sml
  It also contains some compatibility lemmas for rwAllValTree, the value tree
  rewriting function
**)

open fpOptTheory fpValTreeTheory terminationTheory;
open preamble;

val _ = new_theory "fpOptProps";

Theorem substLookup_substUpdate:
  ! s n.
    substLookup s n = NONE ==>
    ! v. substUpdate n v s = NONE
Proof
  Induct_on `s` \\ rpt strip_tac \\ fs[substLookup_def, substUpdate_def]
  \\ Cases_on `h`
  \\ fs[substLookup_def]
  \\ Cases_on `q = n` \\ fs[] \\ res_tac
  \\ Q.ISPEC_THEN `r` (fn thm => fs[thm]) (CONJUNCT2 substUpdate_def)
QED

(* Substitutions are only added to but not overwritten *)
Theorem matchValTree_preserving:
  ! p s1 s2 v.
    matchValTree p v s1 = SOME s2 ==>
    ! n val.
      substLookup s1 n = SOME val ==> substLookup s2 n = SOME val
Proof
  Induct_on `p`
  \\ rpt strip_tac \\ Cases_on `v`
  \\ fs[matchValTree_def] \\ rveq
  \\ fs[option_case_eq] \\ rveq \\ fs[]
  \\ res_tac \\ fs[substAdd_def]
  \\ drule substLookup_substUpdate \\ disch_then assume_tac
  \\ fs[substLookup_def]
  \\ rename [`substLookup s1 m = SOME _`]
  \\ Cases_on `n = m` \\ fs[]
QED

val substMonotone_def = Define `
  substMonotone s1 s2 =
    ! n val. substLookup s1 n = SOME val ==> substLookup s2 n = SOME val`;

(* We can add dummy substitutions *)
Theorem instValTree_weakening:
  ! p v s1 s2.
    substMonotone s1 s2 /\
    instValTree p s1 = SOME v ==>
    instValTree p s2 = SOME v
Proof
  Induct_on `p` \\ rpt strip_tac
  \\ fs[instValTree_def, substMonotone_def, pair_case_eq, option_case_eq]
  \\ rveq \\ res_tac \\ fs[]
QED

(* Sanity lemmas *)
val valSolve_tac =
  irule instValTree_weakening
  \\ asm_exists_tac \\ fs[substMonotone_def]
  \\ rpt strip_tac
  \\ imp_res_tac matchValTree_preserving \\ fs[];

Theorem subst_pat_is_val:
  ! p v s1 s2.
    matchValTree p v s1 = SOME s2 ==>
    instValTree p s2 = SOME v
Proof
  Induct_on `p`
  \\ rpt strip_tac \\ fs[]
  \\ Cases_on `v`
  \\ fs[matchValTree_def, instValTree_def, option_case_eq]
  \\ rveq \\ fs[]
  \\ imp_res_tac substLookup_substUpdate
  \\ fs[substAdd_def, substLookup_def]
  \\ res_tac \\ fs[]
  \\ rpt conj_tac \\ valSolve_tac
QED

Theorem app_match_sym:
  ! p s v.
    instValTree p s = SOME v ==>
    matchValTree p v s = SOME s
Proof
  Induct_on `p`
  \\ rpt strip_tac
  \\ fs[ instValTree_def, matchValTree_def, option_case_eq]
  \\ rveq \\ res_tac
  \\ fs[matchValTree_def]
QED

Theorem rwAllValTree_empty_rewrites[simp]:
  ! canOpt insts v1 v2.
    rwAllValTree insts canOpt [] v1 = SOME v2 ==>
    v1 = v2 /\ insts = []
Proof
  Induct_on `insts` \\ fs[rwAllValTree_def]
  \\ ntac 4 strip_tac \\ CCONTR_TAC \\ fs[]
  \\ Cases_on `h` \\ Cases_on `v1` \\ fs[rwAllValTree_def, nth_def]
QED

Theorem rwAllValTree_id[simp]:
  ! canOpt rws v. ? insts. rwAllValTree insts canOpt rws v = SOME v
Proof
  rpt strip_tac \\ qexists_tac `[]` \\ EVAL_TAC
QED

Theorem nth_EL:
  ! n l x.
    (nth l n = SOME x) ==> (EL (n-1) l = x /\ (n-1) < LENGTH l)
Proof
  Induct_on `l` \\ fs[nth_def] \\ rpt strip_tac
  >- (Cases_on `n = 1` \\ fs[] \\ rveq
      \\ res_tac \\ Cases_on `n` \\ fs[]
      \\ rename [`EL (n - 1) _ = x`]
      \\ Cases_on `n` \\ fs[])
  \\ Cases_on `n` \\ fs[]
  \\ rename [`SUC n < _`] \\ Cases_on `n` \\ fs[]
  \\ res_tac
  \\ fs [GSYM ADD1]
QED

Theorem EL_nth:
  ! n l x.
  EL n l = x /\ n < LENGTH l ==> nth l (n+1) = SOME x
Proof
  Induct_on `l` \\ fs[nth_def]
  \\ rpt strip_tac
  \\ Cases_on `n = 0` \\ fs[]
  \\ Cases_on `n` \\ fs[] \\ res_tac
  \\ fs[ADD1]
QED

Theorem rwAllValTree_up:
  ! insts canOpt rws1 rws2 v1 v2.
    set rws1 SUBSET set rws2 /\
    rwAllValTree insts canOpt rws1 v1 = SOME v2 ==>
    ?insts2. rwAllValTree insts2 canOpt rws2 v1 = SOME v2
Proof
  Induct_on `insts` \\ fs[rwAllValTree_def] \\ rpt strip_tac
  \\ Cases_on `h` \\ rename1 `RewriteApp pth ind`
  \\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ fs[SUBSET_DEF, MEM_EL] \\ imp_res_tac nth_EL
  \\ `?n. n < LENGTH rws2 /\ rw = EL n rws2`
      by (first_x_assum (qspecl_then [`rw`] irule)
          \\ asm_exists_tac \\ imp_res_tac nth_EL \\ asm_exists_tac \\ fs[])
  \\ rename [`rwAllValTree insts3 canOpt rws2 v_new = SOME v2`]
  \\ qexists_tac `RewriteApp pth (n + 1) :: insts3`
  \\ fs[rwAllValTree_def]
  \\ `nth rws2 (n+1) = SOME rw` suffices_by (fs[])
  \\ irule EL_nth \\ fs[]
QED

Theorem rwAllValTree_comp_unop:
  ! v vres insts canOpt rws u.
    rwAllValTree insts canOpt rws v = SOME vres ==>
    ? insts_new.
      rwAllValTree insts_new canOpt rws (Fp_uop u v) = SOME (Fp_uop u vres)
Proof
  Induct_on `insts` \\ rpt strip_tac
  \\ fs[rwAllValTree_def]
  \\ Cases_on `h` \\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspec_then `u` assume_tac) \\ fs[]
  \\ qexists_tac `(RewriteApp (Center f) n):: insts_new`
  \\ fs[rwAllValTree_def, rwFp_pathValTree_def, option_case_eq]
  \\ qexists_tac `Fp_uop u vNew` \\ fs[maybe_map_def]
QED

Theorem rwAllValTree_comp_right:
  ! b v1 v2 vres insts canOpt rws.
    rwAllValTree insts canOpt rws v2 = SOME vres ==>
    ?insts_new.
      rwAllValTree insts_new canOpt rws (Fp_bop b v1 v2) =
        SOME (Fp_bop b v1 vres)
Proof
  Induct_on `insts` \\ rpt strip_tac
  \\ fs[rwAllValTree_def]
  \\ Cases_on `h` \\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v1`, `b`] assume_tac)
  \\ fs[]
  \\ qexists_tac `(RewriteApp (Right f) n):: insts_new`
  \\ fs[rwAllValTree_def, rwFp_pathValTree_def, maybe_map_def]
QED

Theorem rwAllValTree_comp_left:
  ! b v1 v2 vres insts canOpt rws.
    rwAllValTree insts canOpt rws v1 = SOME vres ==>
    ? insts_new.
      rwAllValTree insts_new canOpt rws (Fp_bop b v1 v2) =
        SOME (Fp_bop b vres v2)
Proof
  Induct_on `insts` \\ rpt strip_tac
  \\ fs[rwAllValTree_def]
  \\ Cases_on `h` \\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v2`, `b`] assume_tac)
  \\ fs[]
  \\ qexists_tac `(RewriteApp (Left f) n):: insts_new`
  \\ fs[rwAllValTree_def, rwFp_pathValTree_def, maybe_map_def]
QED

Theorem rwAllValTree_comp_terop_l:
  ! v vres v2 v3 insts canOpt rws t.
    rwAllValTree insts canOpt rws v = SOME vres ==>
    ? insts_new.
      rwAllValTree insts_new canOpt rws (Fp_top t v v2 v3) =
        SOME (Fp_top t vres v2 v3)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllValTree_def]
  \\ Cases_on `h `\\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v3`, `v2`, `t`] assume_tac) \\ fs[]
  \\ qexists_tac `(RewriteApp (Left f) n)::insts_new`
  \\ fs[rwAllValTree_def, rwFp_pathValTree_def, maybe_map_def]
QED

Theorem rwAllValTree_comp_terop_r:
  ! v vres v1 v2 insts canOpt rws t.
    rwAllValTree insts canOpt rws v = SOME vres ==>
    ? insts_new.
      rwAllValTree insts_new canOpt rws (Fp_top t v1 v2 v) =
        SOME (Fp_top t v1 v2 vres)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllValTree_def]
  \\ Cases_on `h `\\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v2`, `v1`, `t`] assume_tac) \\ fs[]
  \\ qexists_tac `(RewriteApp (Right f) n)::insts_new`
  \\ fs[rwAllValTree_def, rwFp_pathValTree_def, maybe_map_def]
QED

Theorem rwAllValTree_comp_terop_c:
  ! v vres v1 v2 insts canOpt rws t.
    rwAllValTree insts canOpt rws v = SOME vres ==>
    ? insts_new.
      rwAllValTree insts_new canOpt rws (Fp_top t v1 v v2) =
        SOME (Fp_top t v1 vres v2)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllValTree_def]
  \\ Cases_on `h `\\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v2`, `v1`, `t`] assume_tac) \\ fs[]
  \\ qexists_tac `(RewriteApp (Center f) n)::insts_new`
  \\ fs[rwAllValTree_def, rwFp_pathValTree_def, maybe_map_def]
QED

Theorem maybe_map_compute_thm:
  maybe_map f v = case v of |NONE => NONE | SOME x => SOME (f x)
Proof
  Cases_on `v` \\ fs[maybe_map_def]
QED

Theorem rwFp_pathValTree_cond_T:
  ! p canOpt rw v v_opt.
    rwFp_pathValTree canOpt rw p v = SOME v_opt ==>
    rwFp_pathValTree T rw p v = SOME v_opt
Proof
  reverse (Induct_on `p`) \\ fs[] \\ rpt strip_tac
  >- (Cases_on `canOpt` \\ fs[rwFp_pathValTree_def])
  \\ Cases_on `v`
  \\ fs[rwFp_pathValTree_def, maybe_map_compute_thm, option_case_eq]
  \\ res_tac \\ rveq \\ fs[]
QED

Theorem rwAllValTree_comp_scope_T:
  ! sc v vres insts canOpt rws t.
    rwAllValTree insts T rws v = SOME vres ==>
    ? insts_new.
      rwAllValTree insts_new canOpt rws (Fp_sc sc v) = SOME (Fp_sc sc vres)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllValTree_def]
  \\ Cases_on `h `\\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`sc`, `vNew`, `vres`, `canOpt`, `rws`] assume_tac) \\ fs[]
  \\ res_tac
  \\ qexists_tac `(RewriteApp (Center f) n)::insts_new`
  \\ Cases_on `sc`
  \\ imp_res_tac rwFp_pathValTree_cond_T
  \\ fs[rwAllValTree_def, rwFp_pathValTree_def, maybe_map_def]
QED

Theorem rwAllValTree_comp_scope:
  ! sc v vres insts canOpt rws t.
    rwAllValTree insts canOpt rws v = SOME vres ==>
    ? insts_new.
      rwAllValTree insts_new canOpt rws (Fp_sc sc v) = SOME (Fp_sc sc vres)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllValTree_def]
  \\ Cases_on `h `\\ fs[rwAllValTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum
      (qspecl_then [`sc`, `vNew`, `vres`, `canOpt`, `rws`] assume_tac) \\ fs[]
  \\ res_tac
  \\ qexists_tac `(RewriteApp (Center f) n)::insts_new`
  \\ Cases_on `sc`
  \\ imp_res_tac rwFp_pathValTree_cond_T
  \\ fs[rwAllValTree_def, rwFp_pathValTree_def, maybe_map_def]
QED

Theorem rwAllValTree_cond_T:
  ! insts. (! canOpt rws v v_opt.
    rwAllValTree insts canOpt rws v = SOME v_opt ==>
    rwAllValTree insts T rws v = SOME v_opt)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllValTree_def]
  \\ Cases_on `h` \\ fs[rwAllValTree_def, option_case_eq]
  \\ imp_res_tac rwFp_pathValTree_cond_T
  \\ asm_exists_tac \\ fs[]
  \\ first_x_assum irule \\ asm_exists_tac \\ fs[]
QED

Theorem rwAllValTree_chaining_exact:
  !v1 v2 v3 insts1 insts2 canOpt rws.
    rwAllValTree insts1 canOpt rws v1 = SOME v2 /\
    rwAllValTree insts2 canOpt rws v2 = SOME v3 ==>
    rwAllValTree (APPEND insts1 insts2) canOpt rws v1 = SOME v3
Proof
  Induct_on `insts1` \\ rpt strip_tac
  \\ fs[rwAllValTree_def]
  \\ Cases_on `h` \\ fs[rwAllValTree_def, option_case_eq]
QED

Theorem rwAllValTree_chaining:
  ! insts1 v1 v2 v3 insts2 canOpt rws.
    rwAllValTree insts1 canOpt rws v1 = SOME v2 /\
    rwAllValTree insts2 canOpt rws v2 = SOME v3 ==>
    ?insts3. rwAllValTree insts3 canOpt rws v1 = SOME v3
Proof
  metis_tac[rwAllValTree_chaining_exact]
QED

(**
 EXPRESSION REWRITING THEOREMS

(**
  Sanity lemma: rewriting on expressions does not introduce new variables
**)
local
  val varMatch_tac =
      imp_res_tac (ONCE_REWRITE_RULE [SUBSET_DEF] FRANGE_FUPDATE_SUBSET)
      \\ fs[matchExpr_def, matchesCexpr_def, option_case_eq, usedVarsExp_def, flookup_thm]
      \\ rveq
      \\ fs[IN_UNION, usedVarsExp_def, SUBSET_DEF];
in
Theorem image_subst_is_usedVars
  `(! e subst s_init pat.
   matchesExpr pat e s_init = SOME subst ==>
   !e_sub. e_sub IN (FRANGE subst) ==>
   e_sub IN (FRANGE s_init) \/
   usedVarsExp (e_sub) SUBSET (usedVarsExp e))
  /\
  (! c subst s_init cpat.
       matchesCexpr cpat c s_init = SOME subst ==>
       ! e_sub. e_sub IN (FRANGE subst) ==>
       e_sub IN (FRANGE s_init) \/
       usedVarsExp (e_sub) SUBSET (usedVarsCexp c))
  /\
  (!l. l = (l:expr list) ==> T)`
  (ho_match_mp_tac expr_induction
  \\ rpt strip_tac \\ fs[] \\ rpt strip_tac
  \\ (Cases_on `pat` ORELSE Cases_on `cpat`)
  \\ fs[matchesExpr_def, matchesCexpr_def, option_case_eq] \\ rveq
  \\ res_tac
  \\ varMatch_tac)
end;

Theorem usedVars_from_image_subst
  `!pat.
    (! e subst.
      appExpr pat subst = SOME e ==>
      usedVarsExp e SUBSET
        { v | ?n e. FLOOKUP subst n = SOME e /\ v IN usedVarsExp e})
    /\
    (! c subst.
      appCexpr pat subst = SOME c ==>
      usedVarsCexp c SUBSET
        { v | ? n e. FLOOKUP subst n = SOME e /\ v IN usedVarsExp e})`
  (Induct_on `pat` \\ rpt strip_tac
  \\ fs[appExpr_def, option_case_eq, usedVarsExp_def, SUBSET_DEF]
  \\ rpt strip_tac \\ rveq \\ fs[Once usedVarsExp_def]
  \\ asm_exists_tac \\ fs[]);

Theorem rewrite_preserves_usedVars
  `(!e e_new lhs rhs subst.
      matchesExpr lhs e FEMPTY = SOME subst /\
      appExpr rhs subst = SOME e_new ==>
      usedVarsExp e_new SUBSET usedVarsExp e) /\
    (!c c_new lhs rhs subst.
      matchesCexpr lhs c FEMPTY = SOME subst /\
      appCexpr rhs subst = SOME c_new ==>
      usedVarsCexp c_new SUBSET usedVarsCexp c)`
  (conj_tac \\ rpt strip_tac
  \\ irule SUBSET_TRANS
  \\ imp_res_tac usedVars_from_image_subst
  \\ asm_exists_tac \\ fs[]
  \\ imp_res_tac image_subst_is_usedVars
  \\ fs[FRANGE_FEMPTY, SUBSET_DEF]
  \\ rpt strip_tac
  \\ fs[FRANGE_FLOOKUP]
  \\ res_tac);

Theorem matchExpr_preserving
  `! p.
    (! e s1 s2.
      matchesExpr p e s1 = SOME s2 ==>
      ! n val.
        FLOOKUP s1 n = SOME val ==> FLOOKUP s2 n = SOME val)
  /\
    (! ce s1 s2.
      matchesCexpr p ce s1 = SOME s2 ==>
      ! n val.
        FLOOKUP s1 n = SOME val ==> FLOOKUP s2 n = SOME val)`
  (Induct_on `p`
  \\ rpt strip_tac \\ fs[]
  \\ (Cases_on `ce` ORELSE Cases_on `e`)
  \\ fs[matchesExpr_def, matchesCexpr_def] \\ rpt strip_tac
  \\ res_tac
  \\ res_tac
  \\ fs[option_case_eq] \\ rveq \\ fs[]
  \\ irule FLOOKUP_SUBMAP \\ asm_exists_tac \\ fs[flookup_thm]);

Theorem appExpr_weakening
  `! p.
      (! e s1 s2.
        (! n val. FLOOKUP s1 n = SOME val ==> FLOOKUP s2 n = SOME val) /\
        appExpr p s1 = SOME e ==>
        appExpr p s2 = SOME e)
  /\
    (! ce s1 s2.
      (! n val. FLOOKUP s1 n = SOME val ==> FLOOKUP s2 n = SOME val) /\
      appCexpr p s1 = SOME ce ==>
      appCexpr p s2 = SOME ce)`
  (Induct_on `p`
  \\ rpt strip_tac \\ fs[]
  \\ fs[appExpr_def, pair_case_eq, option_case_eq]
  \\ res_tac \\ fs[]);

val exprSolve_tac =
  (let
    val thms = CONJ_LIST 2 (SIMP_RULE std_ss [FORALL_AND_THM] appExpr_weakening)
  in
  (irule (hd thms) ORELSE irule (hd (tl thms)))
  end)
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs[]
  \\ rpt strip_tac
  \\ imp_res_tac matchExpr_preserving \\ fs[];

Theorem subst_pat_is_exp
  `! p.
    (! e s1 s2.
          matchesExpr p e s1 = SOME s2 ==>
          appExpr p s2 = SOME e)
  /\
    (! ce s1 s2.
          matchesCexpr p ce s1 = SOME s2 ==>
          appCexpr p s2 = SOME ce)`
  (Induct_on `p`
  \\ rpt strip_tac \\ fs[] \\ rpt strip_tac
  \\ (Cases_on `e` ORELSE Cases_on `ce`)
  \\ fs[matchesExpr_def, matchesCexpr_def, option_case_eq]
  \\ rveq \\ fs[appExpr_def, FLOOKUP_UPDATE]
  \\ res_tac \\ fs[]
  \\ rpt conj_tac \\ exprSolve_tac);
**)

val _ = export_theory();
