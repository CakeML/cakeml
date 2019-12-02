(**
  This file contains proofs about the matching and instantiation functions
  defined in patternScript.sml
  It also contains some compatibility lemmas for rwAllValTree, the value tree
  rewriting function
**)

open fpOptTheory fpValTreeTheory semanticPrimitivesTheory terminationTheory;
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
Theorem matchWordTree_preserving:
  ! p v s1 s2.
    matchWordTree p v s1 = SOME s2 ==>
    ! n val.
      substLookup s1 n = SOME val ==> substLookup s2 n = SOME val
Proof
  ho_match_mp_tac matchWordTree_ind
  \\ rpt strip_tac
  \\ fs[matchWordTree_def] \\ rveq
  \\ fs[option_case_eq] \\ rveq \\ fs[substAdd_def]
  \\ drule substLookup_substUpdate \\ disch_then (qspec_then `v` assume_tac)
  \\ fs[substLookup_def]
  \\ rename [`substLookup s1 m = SOME _`]
  \\ Cases_on `n = m` \\ fs[]
QED

Theorem matchBoolTree_preserving:
  ! p v s1 s2.
    matchBoolTree p v s1 = SOME s2 ==>
    ! n val.
      substLookup s1 n = SOME val ==> substLookup s2 n = SOME val
Proof
  ho_match_mp_tac matchBoolTree_ind
  \\ rpt strip_tac
  \\ fs[matchBoolTree_def] \\ rveq
  \\ fs[option_case_eq] \\ rveq \\ fs[substAdd_def]
  \\ imp_res_tac matchWordTree_preserving \\ res_tac
QED

val substMonotone_def = Define `
  substMonotone s1 s2 =
    ! n val. substLookup s1 n = SOME val ==> substLookup s2 n = SOME val`;

(* We can add dummy substitutions *)
Theorem instWordTree_weakening:
  ! p v s1 s2.
    substMonotone s1 s2 /\
    instWordTree p s1 = SOME v ==>
    instWordTree p s2 = SOME v
Proof
  Induct_on `p` \\ rpt strip_tac
  \\ fs[instWordTree_def, substMonotone_def, pair_case_eq, option_case_eq]
  \\ rveq \\ res_tac \\ fs[]
QED

Theorem instBoolTree_weakening:
  ! p v s1 s2.
    substMonotone s1 s2 /\
    instBoolTree p s1 = SOME v ==>
    instBoolTree p s2 = SOME v
Proof
  Induct_on `p` \\ rpt strip_tac
  \\ imp_res_tac instWordTree_weakening
  \\ fs[instBoolTree_def, substMonotone_def, pair_case_eq, option_case_eq]
  \\ rveq \\ res_tac \\ fs[]
QED

(* Sanity lemmas *)
val wordSolve_tac =
  irule instWordTree_weakening
  \\ asm_exists_tac \\ fs[substMonotone_def]
  \\ rpt strip_tac
  \\ imp_res_tac matchWordTree_preserving \\ fs[];

Theorem subst_pat_is_word:
  ! p v s1 s2.
    matchWordTree p v s1 = SOME s2 ==>
    instWordTree p s2 = SOME v
Proof
  Induct_on `p`
  \\ rpt strip_tac \\ fs[]
  \\ Cases_on `v`
  \\ fs[matchWordTree_def, instWordTree_def, option_case_eq]
  \\ rveq \\ fs[]
  \\ imp_res_tac substLookup_substUpdate
  \\ fs[substAdd_def, substLookup_def]
  \\ res_tac \\ fs[]
  \\ rpt conj_tac \\ wordSolve_tac
QED

val boolSolve_tac =
  irule instWordTree_weakening
  \\ fs[substMonotone_def]
  \\ imp_res_tac matchWordTree_preserving
  \\ imp_res_tac subst_pat_is_word
  \\ asm_exists_tac \\ fs[];

Theorem subst_pat_is_bool:
  ! p v s1 s2.
    matchBoolTree p v s1 = SOME s2 ==>
    instBoolTree p s2 = SOME v
Proof
  Induct_on `p`
  \\ rpt strip_tac \\ fs[]
  \\ Cases_on `v`
  \\ fs[matchBoolTree_def, instBoolTree_def, option_case_eq]
  \\ rveq \\ fs[]
  \\ imp_res_tac substLookup_substUpdate
  \\ fs[substAdd_def, substLookup_def]
  \\ res_tac \\ fs[]
  \\ rpt conj_tac \\ boolSolve_tac
QED

Theorem app_match_sym_word:
  ! p s v.
    instWordTree p s = SOME v ==>
    matchWordTree p v s = SOME s
Proof
  Induct_on `p`
  \\ rpt strip_tac
  \\ fs[instWordTree_def, matchWordTree_def, option_case_eq]
  \\ rveq \\ res_tac
  \\ fs[matchWordTree_def]
QED

Theorem app_match_sym_bool:
  ! p s v.
    instBoolTree p s = SOME v ==>
    matchBoolTree p v s = SOME s
Proof
  Induct_on `p`
  \\ rpt strip_tac
  \\ fs[instBoolTree_def, matchBoolTree_def, option_case_eq]
  \\ imp_res_tac app_match_sym_word
  \\ rveq \\ res_tac
  \\ fs[matchBoolTree_def]
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

Theorem maybe_map_compute_thm:
  maybe_map f v = case v of |NONE => NONE | SOME x => SOME (f x)
Proof
  Cases_on `v` \\ fs[maybe_map_def]
QED

Theorem rwAllWordTree_empty_rewrites[simp]:
  ! insts v1 v2.
    rwAllWordTree insts [] v1 = SOME v2 ==>
    v1 = v2 /\ insts = []
Proof
  Induct_on `insts` \\ fs[rwAllWordTree_def]
  \\ ntac 4 strip_tac \\ CCONTR_TAC \\ fs[]
  \\ Cases_on `h` \\ Cases_on `v1` \\ fs[rwAllWordTree_def, nth_def]
QED

Theorem rwAllBoolTree_empty_rewrites[simp]:
  ! insts v1 v2.
    rwAllBoolTree insts [] v1 = SOME v2 ==>
    v1 = v2 /\ insts = []
Proof
  Induct_on `insts` \\ fs[rwAllBoolTree_def]
  \\ ntac 4 strip_tac \\ CCONTR_TAC \\ fs[]
  \\ Cases_on `h` \\ Cases_on `v1` \\ fs[rwAllBoolTree_def, nth_def]
QED

Theorem rwAllWordTree_id[simp]:
  ! rws v. ? insts. rwAllWordTree insts rws v = SOME v
Proof
  rpt strip_tac \\ qexists_tac `[]` \\ EVAL_TAC
QED

Theorem rwAllBoolTree_id[simp]:
  ! rws v. ? insts. rwAllBoolTree insts rws v = SOME v
Proof
  rpt strip_tac \\ qexists_tac `[]` \\ EVAL_TAC
QED

Theorem rwAllWordTree_up:
  ! insts rws1 rws2 v1 v2.
    set rws1 SUBSET set rws2 /\
    rwAllWordTree insts rws1 v1 = SOME v2 ==>
    ?insts2. rwAllWordTree insts2 rws2 v1 = SOME v2
Proof
  Induct_on `insts` \\ fs[rwAllWordTree_def] \\ rpt strip_tac
  \\ Cases_on `h` \\ rename1 `RewriteApp pth ind`
  \\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ fs[SUBSET_DEF, MEM_EL] \\ imp_res_tac nth_EL
  \\ `?n. n < LENGTH rws2 /\ rw = EL n rws2`
      by (first_x_assum (qspecl_then [`rw`] irule)
          \\ asm_exists_tac \\ imp_res_tac nth_EL \\ asm_exists_tac \\ fs[])
  \\ rename [`rwAllWordTree insts3 rws2 v_new = SOME v2`]
  \\ qexists_tac `RewriteApp pth (n + 1) :: insts3`
  \\ fs[rwAllWordTree_def]
  \\ `nth rws2 (n+1) = SOME rw` suffices_by (fs[])
  \\ irule EL_nth \\ fs[]
QED

Theorem rwAllBoolTree_up:
  ! insts rws1 rws2 v1 v2.
    set rws1 SUBSET set rws2 /\
    rwAllBoolTree insts rws1 v1 = SOME v2 ==>
    ?insts2. rwAllBoolTree insts2 rws2 v1 = SOME v2
Proof
  Induct_on `insts` \\ fs[rwAllBoolTree_def] \\ rpt strip_tac
  \\ Cases_on `h` \\ rename1 `RewriteApp pth ind`
  \\ fs[rwAllBoolTree_def, option_case_eq]
  \\ res_tac
  \\ fs[SUBSET_DEF, MEM_EL] \\ imp_res_tac nth_EL
  \\ `?n. n < LENGTH rws2 /\ rw = EL n rws2`
      by (first_x_assum (qspecl_then [`rw`] irule)
          \\ asm_exists_tac \\ imp_res_tac nth_EL \\ asm_exists_tac \\ fs[])
  \\ rename [`rwAllBoolTree insts3 rws2 v_new = SOME v2`]
  \\ qexists_tac `RewriteApp pth (n + 1) :: insts3`
  \\ fs[rwAllBoolTree_def]
  \\ `nth rws2 (n+1) = SOME rw` suffices_by (fs[])
  \\ irule EL_nth \\ fs[]
QED

Theorem rwAllWordTree_comp_unop:
  ! v vres insts rws u.
    rwAllWordTree insts rws v = SOME vres ==>
    ? insts_new.
      rwAllWordTree insts_new rws (Fp_uop u v) = SOME (Fp_uop u vres)
Proof
  Induct_on `insts` \\ rpt strip_tac
  \\ fs[rwAllWordTree_def]
  \\ Cases_on `h` \\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspec_then `u` assume_tac) \\ fs[]
  \\ qexists_tac `(RewriteApp (Center f) n):: insts_new`
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, option_case_eq]
  \\ qexists_tac `Fp_uop u vNew` \\ fs[maybe_map_def]
QED

Theorem rwAllWordTree_comp_right:
  ! b v1 v2 vres insts rws.
    rwAllWordTree insts rws v2 = SOME vres ==>
    ?insts_new.
      rwAllWordTree insts_new rws (Fp_bop b v1 v2) =
        SOME (Fp_bop b v1 vres)
Proof
  Induct_on `insts` \\ rpt strip_tac
  \\ fs[rwAllWordTree_def]
  \\ Cases_on `h` \\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v1`, `b`] assume_tac)
  \\ fs[]
  \\ qexists_tac `(RewriteApp (Right f) n):: insts_new`
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
QED

Theorem rwAllWordTree_comp_left:
  ! b v1 v2 vres insts rws.
    rwAllWordTree insts rws v1 = SOME vres ==>
    ? insts_new.
      rwAllWordTree insts_new rws (Fp_bop b v1 v2) =
        SOME (Fp_bop b vres v2)
Proof
  Induct_on `insts` \\ rpt strip_tac
  \\ fs[rwAllWordTree_def]
  \\ Cases_on `h` \\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v2`, `b`] assume_tac)
  \\ fs[]
  \\ qexists_tac `(RewriteApp (Left f) n):: insts_new`
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
QED

Theorem rwAllWordTree_comp_terop_l:
  ! v vres v2 v3 insts rws t.
    rwAllWordTree insts rws v = SOME vres ==>
    ? insts_new.
      rwAllWordTree insts_new rws (Fp_top t v v2 v3) =
        SOME (Fp_top t vres v2 v3)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllWordTree_def]
  \\ Cases_on `h `\\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v3`, `v2`, `t`] assume_tac) \\ fs[]
  \\ qexists_tac `(RewriteApp (Left f) n)::insts_new`
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
QED

Theorem rwAllWordTree_comp_terop_r:
  ! v vres v1 v2 insts rws t.
    rwAllWordTree insts rws v = SOME vres ==>
    ? insts_new.
      rwAllWordTree insts_new rws (Fp_top t v1 v2 v) =
        SOME (Fp_top t v1 v2 vres)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllWordTree_def]
  \\ Cases_on `h `\\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v2`, `v1`, `t`] assume_tac) \\ fs[]
  \\ qexists_tac `(RewriteApp (Right f) n)::insts_new`
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
QED

  (*
Theorem rwAllWordTree_comp_terop_c:
  ! v vres v1 v2 insts rws t.
    rwAllWordTree insts rws v = SOME vres ==>
    ? insts_new.
      rwAllWordTree insts_new rws (Fp_top t v1 v v2) =
        SOME (Fp_top t v1 vres v2)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllWordTree_def]
  \\ Cases_on `h `\\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v2`, `v1`, `t`] assume_tac) \\ fs[]
  \\ qexists_tac `(RewriteApp (Center f) n)::insts_new`
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
QED
  *)

Theorem rwAllWordTree_comp_scope_T:
  ! sc v vres insts rws t.
    rwAllWordTree insts rws v = SOME vres ==>
    ? insts_new.
      rwAllWordTree insts_new rws (Fp_wopt sc v) = SOME (Fp_wopt sc vres)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllWordTree_def]
  \\ Cases_on `h `\\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`sc`, `vNew`, `vres`, `rws`] assume_tac) \\ fs[]
  \\ res_tac
  \\ qexists_tac `(RewriteApp (Center f) n)::insts_new`
  \\ Cases_on `sc`
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
QED

Theorem rwAllWordTree_comp_scope:
  ! sc v vres insts rws t.
    rwAllWordTree insts rws v = SOME vres ==>
    ? insts_new.
      rwAllWordTree insts_new rws (Fp_wopt sc v) = SOME (Fp_wopt sc vres)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllWordTree_def]
  \\ Cases_on `h `\\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum
      (qspecl_then [`sc`, `vNew`, `vres`, `rws`] assume_tac) \\ fs[]
  \\ res_tac
  \\ qexists_tac `(RewriteApp (Center f) n)::insts_new`
  \\ Cases_on `sc`
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
QED

 (*
Theorem rwAllWordTree_cond_T:
  ! insts. (! rws v v_opt.
    rwAllWordTree insts rws v = SOME v_opt ==>
    rwAllWordTree insts T rws v = SOME v_opt)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllWordTree_def]
  \\ Cases_on `h` \\ fs[rwAllWordTree_def, option_case_eq]
  \\ imp_res_tac rwFp_pathWordTree_cond_T
  \\ asm_exists_tac \\ fs[]
  \\ first_x_assum irule \\ asm_exists_tac \\ fs[]
QED
*)

Theorem rwAllWordTree_chaining_exact:
  !v1 v2 v3 insts1 insts2 rws.
    rwAllWordTree insts1 rws v1 = SOME v2 /\
    rwAllWordTree insts2 rws v2 = SOME v3 ==>
    rwAllWordTree (APPEND insts1 insts2) rws v1 = SOME v3
Proof
  Induct_on `insts1` \\ rpt strip_tac
  \\ fs[rwAllWordTree_def]
  \\ Cases_on `h` \\ fs[rwAllWordTree_def, option_case_eq]
QED

Theorem rwAllWordTree_chaining:
  ! insts1 v1 v2 v3 insts2 rws.
    rwAllWordTree insts1 rws v1 = SOME v2 /\
    rwAllWordTree insts2 rws v2 = SOME v3 ==>
    ?insts3. rwAllWordTree insts3 rws v1 = SOME v3
Proof
  metis_tac[rwAllWordTree_chaining_exact]
QED

(*
Theorem rwFp_pathBoolTree_cond_T:
  ! p rw v v_opt.
    rwFp_pathBoolTree rw p v = SOME v_opt ==>
    rwFp_pathBoolTree T rw p v = SOME v_opt
Proof
  reverse (Induct_on `p`) \\ fs[] \\ rpt strip_tac
  >- (Cases_on `canOpt` \\ fs[rwFp_pathBoolTree_def])
  \\ Cases_on `v`
  \\ fs[rwFp_pathBoolTree_def, maybe_map_compute_thm, option_case_eq]
  \\ res_tac \\ rveq \\ fs[]
  \\ imp_res_tac rwFp_pathWordTree_cond_T
QED

Theorem rwAllBoolTree_comp_scope_T:
  ! sc v vres insts rws t.
    rwAllBoolTree insts rws v = SOME vres ==>
    ? insts_new.
      rwAllBoolTree insts_new rws (Fp_bopt sc v) = SOME (Fp_bopt sc vres)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllBoolTree_def]
  \\ Cases_on `h `\\ fs[rwAllBoolTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`sc`, `vNew`, `vres`, `rws`] assume_tac) \\ fs[]
  \\ res_tac
  \\ qexists_tac `(RewriteApp (Center f) n)::insts_new`
  \\ Cases_on `sc`
  \\ fs[rwAllBoolTree_def, rwFp_pathBoolTree_def, maybe_map_def]
QED
*)

Theorem rwAllBoolTree_comp_scope:
  ! sc v vres insts rws t.
    rwAllBoolTree insts rws v = SOME vres ==>
    ? insts_new.
      rwAllBoolTree insts_new rws (Fp_bopt sc v) = SOME (Fp_bopt sc vres)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllBoolTree_def]
  \\ Cases_on `h `\\ fs[rwAllBoolTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum
      (qspecl_then [`sc`, `vNew`, `vres`, `rws`] assume_tac) \\ fs[]
  \\ res_tac
  \\ qexists_tac `(RewriteApp (Center f) n)::insts_new`
  \\ Cases_on `sc`
  \\ fs[rwAllBoolTree_def, rwFp_pathBoolTree_def, maybe_map_def]
QED

(*
Theorem rwAllBoolTree_cond_T:
  ! insts. (! rws v v_opt.
    rwAllBoolTree insts rws v = SOME v_opt ==>
    rwAllBoolTree insts T rws v = SOME v_opt)
Proof
  Induct_on `insts` \\ rpt strip_tac \\ fs[rwAllBoolTree_def]
  \\ Cases_on `h` \\ fs[rwAllBoolTree_def, option_case_eq]
  \\ imp_res_tac rwFp_pathBoolTree_cond_T
  \\ asm_exists_tac \\ fs[]
  \\ first_x_assum irule \\ asm_exists_tac \\ fs[]
QED
*)

Theorem rwAllBoolTree_chaining_exact:
  !v1 v2 v3 insts1 insts2 rws.
    rwAllBoolTree insts1 rws v1 = SOME v2 /\
    rwAllBoolTree insts2 rws v2 = SOME v3 ==>
    rwAllBoolTree (APPEND insts1 insts2) rws v1 = SOME v3
Proof
  Induct_on `insts1` \\ rpt strip_tac
  \\ fs[rwAllBoolTree_def]
  \\ Cases_on `h` \\ fs[rwAllBoolTree_def, option_case_eq]
QED

Theorem rwAllBoolTree_chaining:
  ! insts1 v1 v2 v3 insts2 rws.
    rwAllBoolTree insts1 rws v1 = SOME v2 /\
    rwAllBoolTree insts2 rws v2 = SOME v3 ==>
    ?insts3. rwAllBoolTree insts3 rws v1 = SOME v3
Proof
  metis_tac[rwAllBoolTree_chaining_exact]
QED

(* TODO: Move *)
fun impl_subgoal_tac th =
  let
    val hyp_to_prove = lhand (concl th)
  in
    SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end;

Theorem nth_NONE:
  ! xs n.
    LENGTH xs < n ==>
    nth xs n = NONE
Proof
  Induct_on `xs` \\ fs[fpOptTheory.nth_def]
QED

Theorem nth_app:
  ! xs ys x n.
   nth xs n = SOME x ==>
   nth (xs ++ ys) n = SOME x
Proof
  Induct_on `xs` \\ fs[fpOptTheory.nth_def]
  \\ rpt strip_tac \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem rwAllWordTree_append_opt:
  ! sched rws1 rws2 v r.
    rwAllWordTree sched rws1 v = SOME r ==>
    rwAllWordTree sched (rws1 ++ rws2) v = SOME r
Proof
  Induct_on `sched` \\ fs[rwAllWordTree_def] \\ rpt gen_tac
  \\ Cases_on `h` \\ fs[rwAllWordTree_def]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac nth_app \\ fs[]
QED

Theorem do_fprw_up:
  ! v sched1 rws1 rws2 x.
    do_fprw v sched1 rws1 = x /\
    set rws1 SUBSET set rws2 ==>
    ? sched2. do_fprw v sched2 rws2 = x
Proof
  Cases_on `sched1` \\ simp[do_fprw_def]
  \\ rpt strip_tac
  >- (qexists_tac `[]` \\ fs[]
      \\ rpt (TOP_CASE_TAC \\ fs[rwAllWordTree_def, rwAllBoolTree_def]))
  \\ drule rwAllWordTree_up
  \\ drule rwAllBoolTree_up
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ TRY (rpt strip_tac \\ qexists_tac `[RewriteApp Here 0]` \\ fs[] \\ NO_TAC)
  \\ rpt strip_tac \\ res_tac
  \\ TOP_CASE_TAC
  \\ TRY (
    FIRST_X_ASSUM drule \\ disch_then assume_tac \\ fs[]
    \\ qexists_tac `insts2` \\ fs[]
    \\ asm_exists_tac \\ fs[] \\ NO_TAC)
  \\ qexists_tac `[RewriteApp Here (LENGTH rws2 + 1)]`
  \\ fs[rwAllWordTree_def, rwAllBoolTree_def, nth_NONE]
QED

Theorem do_fprw_append_opt:
  ! v sched1 rws1 x.
    do_fprw v sched1 rws1 = x ==>
    ! rws2.
      ? sched2.
      do_fprw v sched2 (rws1 ++ rws2) = x
Proof
  rpt strip_tac \\ drule do_fprw_up \\ disch_then assume_tac
  \\ first_x_assum (qspec_then `rws1 ++ rws2` impl_subgoal_tac)
  \\ fs[SUBSET_DEF] \\ asm_exists_tac \\ fs[]
QED

val _ = export_theory();
