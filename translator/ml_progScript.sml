(*
  Definitions and theorems supporting ml_progLib, which constructs a
  CakeML program and its semantic environment.
*)
Theory ml_prog
Ancestors
  ast semanticPrimitives evaluate semanticPrimitivesProps
  evaluateProps mlstring integer evaluate_dec namespace
  alist_tree primSemEnv[qualified]
Libs
  preamble


val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(* --- env operators --- *)

(* Functions write, write_cons, write_mod, empty_env, merge_env should
   never be expanded by EVAL and are therefore defined using
   nocompute. These should never be exanded by EVAL because that would
   cause very slow appends. *)

Definition write_def[nocompute]:
  write name v (env:v sem_env) = env with v := nsBind name v env.v
End

Definition write_cons_def[nocompute]:
  write_cons n d (env:v sem_env) =
    (env with c := nsAppend (nsSing n d) env.c)
End

Definition empty_env_def[nocompute]:
  (empty_env:v sem_env) = <| v := nsEmpty ; c:= nsEmpty|>
End

Definition write_mod_def[nocompute]:
  write_mod mn (env:v sem_env) env2 =
    env2 with <|
      c := nsAppend (nsLift mn env.c) env2.c
      ; v := nsAppend (nsLift mn env.v) env2.v |>
End

Definition merge_env_def[nocompute]:
  merge_env (env2:v sem_env) env1 =
    <| v := nsAppend env2.v env1.v
     ; c := nsAppend env2.c env1.c|>
End

(* --- balanced env tree --- *)

(* A structured entry: what key k contributes to each env component.
   sv = Short value, sc = Short constructor,
   mv = module value namespace, mc = module constructor namespace *)
Datatype:
  env_entry =
    <| sv : v option
     ; sc : (num # stamp) option
     ; mv : (mlstring, mlstring, v) namespace option
     ; mc : (mlstring, mlstring, (num # stamp)) namespace option
     |>
End

val env_entry_component_equality = fetch "-" "env_entry_component_equality";

(* A balanced tree of env entries, projected to sem_env *)
Datatype:
  env_tree = EnvLeaf mlstring env_entry
           | EnvBranch env_tree env_tree
End

(* Well-formedness: sorted keys with exact first/last bounds *)
Definition env_wf_def:
  env_wf (EnvLeaf k e) k1 k2 = (k1 = k /\ k2 = k) /\
  env_wf (EnvBranch l r) k1 k2 =
    ?kl kr. env_wf l k1 kl /\ env_wf r kr k2 /\ kl < kr
End

Theorem env_wf_branch_inv:
  env_wf (EnvBranch l r) k1 k2 ==>
  ?kl kr. env_wf l k1 kl /\ env_wf r kr k2 /\ kl < kr
Proof
  fs [env_wf_def]
QED

(* Intro rules for building WF bottom-up *)
Theorem env_wf_leaf:
  env_wf (EnvLeaf k e) k k
Proof
  fs [env_wf_def]
QED

Theorem env_wf_branch_intro:
  env_wf l k1 kl /\ env_wf r kr k2 /\ kl < kr ==>
  env_wf (EnvBranch l r) k1 k2
Proof
  rw [env_wf_def] \\ metis_tac []
QED

(* Leaf membership *)
Definition env_leaf_mem_def:
  env_leaf_mem k e (EnvLeaf k2 e2) = (k = k2 /\ e = e2) /\
  env_leaf_mem k e (EnvBranch l r) = (env_leaf_mem k e l \/ env_leaf_mem k e r)
End

(* Subset / containment: structural inclusion in a tree.
   env_sub t1 t2 means every leaf in t1 also occurs in t2.
   Both left and right child rules are unconditional. *)
Definition env_sub_def:
  env_sub t1 t2 = !k e. env_leaf_mem k e t1 ==> env_leaf_mem k e t2
End

Theorem env_sub_refl:
  env_sub t t
Proof
  fs [env_sub_def]
QED

Theorem env_sub_left:
  env_sub t l ==> env_sub t (EnvBranch l r)
Proof
  fs [env_sub_def, env_leaf_mem_def]
QED

Theorem env_sub_right:
  env_sub t r ==> env_sub t (EnvBranch l r)
Proof
  fs [env_sub_def, env_leaf_mem_def]
QED

Theorem env_sub_trans:
  env_sub t1 t2 /\ env_sub t2 t3 ==> env_sub t1 t3
Proof
  fs [env_sub_def]
QED

Theorem env_sub_leaf_self:
  env_sub (EnvLeaf k e) (EnvLeaf k e)
Proof
  fs [env_sub_def]
QED

(* Unified lookup: one HOL function returning an env_entry that packages
   all four component lookups. Paired with nsLookup_all below. *)

Definition empty_entry_def:
  empty_entry = <|sv := NONE; sc := NONE; mv := NONE; mc := NONE|>
End

Definition tree_lookup_def:
  tree_lookup (EnvLeaf k' e) k =
    (if k = k' then e else empty_entry) /\
  tree_lookup (EnvBranch l r) k =
    (let el = tree_lookup l k in
     let er = tree_lookup r k in
       <| sv := OPTION_CHOICE el.sv er.sv
        ; sc := OPTION_CHOICE el.sc er.sc
        ; mv := OPTION_CHOICE el.mv er.mv
        ; mc := OPTION_CHOICE el.mc er.mc |>)
End

(* nsLookup_all_def is defined further below, after nsLookup_Mod1_def. *)

(* Intro rules for env_leaf_mem, for building membership proofs bottom-up *)
Theorem env_leaf_mem_leaf:
  env_leaf_mem k e (EnvLeaf k e)
Proof
  fs [env_leaf_mem_def]
QED

Theorem env_leaf_mem_branch_l:
  env_leaf_mem k e l ==> env_leaf_mem k e (EnvBranch l r)
Proof
  fs [env_leaf_mem_def]
QED

Theorem env_leaf_mem_branch_r:
  env_leaf_mem k e r ==> env_leaf_mem k e (EnvBranch l r)
Proof
  fs [env_leaf_mem_def]
QED

(* Unified tree_lookup hit/miss theorems are defined further below
   after env_wf_bounds_le / env_wf_mem_bounds. *)

(* --- WF structural lemmas --- *)

(* env_wf implies bounds are ordered *)
Theorem env_wf_bounds_le:
  !t k1 k2. env_wf t k1 k2 ==> k1 ≤ k2
Proof
  Induct_on `t` >- fs [env_wf_def, mlstringTheory.mlstring_le_thm]
  \\ rw [env_wf_def]
  \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans]
QED

(* All leaf keys are within the WF bounds *)
Theorem env_wf_mem_bounds:
  !t k1 k2 k e. env_wf t k1 k2 /\ env_leaf_mem k e t ==> k1 ≤ k /\ k ≤ k2
Proof
  Induct_on `t` >- fs [env_wf_def, env_leaf_mem_def, mlstringTheory.mlstring_le_thm]
  \\ rw [env_wf_def, env_leaf_mem_def] \\ res_tac \\ fs []
  \\ imp_res_tac env_wf_bounds_le
  \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans]
QED

(* env_wf means leaf entries for the same key are unique *)
Theorem env_wf_unique:
  !t k1 k2 k e1 e2.
    env_wf t k1 k2 /\ env_leaf_mem k e1 t /\ env_leaf_mem k e2 t ==>
    e1 = e2
Proof
  Induct_on `t`
  \\ rw [env_wf_def, env_leaf_mem_def] \\ res_tac
  \\ imp_res_tac env_wf_mem_bounds
  \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans,
    mlstringTheory.mlstring_lt_nonrefl]
QED

(* The first and second bounds in env_wf are structurally determined by t. *)
Theorem env_wf_bounds_unique:
  !t k1 k1' k2 k2'.
    env_wf t k1 k2 /\ env_wf t k1' k2' ==> k1 = k1' /\ k2 = k2'
Proof
  Induct_on `t` >- fs [env_wf_def]
  \\ rw [env_wf_def] \\ res_tac \\ fs []
QED

(* Given the full branch WF plus the two child WFs at specific bounds,
   the relation < between the children's adjacent bounds
   holds.  Used by the ML driver to derive lt theorems from a parent
   WF that's already in scope, without invoking EVAL via mk_lt_thm. *)
Theorem env_wf_branch_split_lt:
  !l r k1 k2 kl kr.
    env_wf (EnvBranch l r) k1 k2 /\
    env_wf l k1 kl /\ env_wf r kr k2 ==>
    kl < kr
Proof
  rw [env_wf_def]
  \\ imp_res_tac env_wf_bounds_unique
  \\ fs []
QED

(* CPS form for apply_cps: parent WF as an explicit Branch equation so
   INST + PROVE_HYP on (tT, l, r, k1, k2, kl, kr) can discharge it. *)
Theorem env_wf_branch_split_lt_cps:
  tT = EnvBranch l r /\ env_wf tT k1 k2 /\
  env_wf l k1 kl /\ env_wf r kr k2 ==>
  kl < kr
Proof
  rpt strip_tac \\ gvs []
  \\ irule env_wf_branch_split_lt \\ metis_tac []
QED

(* Unified tree_lookup miss theorem: key outside WF bounds ==> empty_entry *)
Theorem tree_lookup_miss:
  !t k1 k2 k. env_wf t k1 k2 /\ (k < k1 \/ k2 < k) ==>
    tree_lookup t k = empty_entry
Proof
  Induct_on `t`
  >- (rw [env_wf_def, tree_lookup_def]
      \\ metis_tac [mlstringTheory.mlstring_lt_nonrefl, empty_entry_def])
  \\ rw [env_wf_def, tree_lookup_def, LET_THM]
  \\ imp_res_tac env_wf_bounds_le
  \\ `tree_lookup t k = empty_entry /\ tree_lookup t' k = empty_entry` by (
    conj_tac >> first_x_assum irule
    >| map qexistsl_tac [[`k1`, `kl`], [`kr`, `k2`]] \\ fs []
    \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans])
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def]
QED

(* If lookups in both children of an EnvBranch yield empty_entry, so does
   the lookup in the branch.  Used by the ML driver to resolve "in-range
   gap" misses via O(log N) recursion instead of unfolding the whole tree. *)
Theorem tree_lookup_branch_empty:
  !l r k.
    tree_lookup l k = empty_entry /\ tree_lookup r k = empty_entry ==>
    tree_lookup (EnvBranch l r) k = empty_entry
Proof
  rw [tree_lookup_def, LET_THM, empty_entry_def, optionTheory.OPTION_CHOICE_def]
QED

(* CPS form for INST + PROVE_HYP *)
Theorem tree_lookup_branch_empty_cps:
  tT = EnvBranch l r /\
  tree_lookup l k = empty_entry /\ tree_lookup r k = empty_entry ==>
  tree_lookup tT k = empty_entry
Proof
  rpt strip_tac \\ gvs []
  \\ irule tree_lookup_branch_empty \\ metis_tac []
QED

(* An "in-range miss" predicate: k is within [k1,k2] but not at any leaf.
   The ML driver carries this up one branch at a time so each outer miss
   needs only two proofs < (for the two leaves adjacent to k),
   instead of an O(depth) cascade. *)
Definition tree_miss_def:
  tree_miss t k1 k2 k <=>
    env_wf t k1 k2 /\
    tree_lookup t k = empty_entry /\
    k1 ≤ k /\ k ≤ k2
End

Theorem tree_miss_imp_lookup:
  !t k1 k2 k. tree_miss t k1 k2 k ==> tree_lookup t k = empty_entry
Proof
  rw [tree_miss_def]
QED

(* Base: a branch whose two subtrees bracket k strictly — the two lt proofs
   are the between < k and the two inner bounds (kL, kR). *)
Theorem tree_miss_gap:
  env_wf tL k1 kL /\ env_wf tR kR k2 /\
  kL < k /\ k < kR ==>
  tree_miss (EnvBranch tL tR) k1 k2 k
Proof
  rw [tree_miss_def]
  >- (rw [env_wf_def]
      \\ qexistsl_tac [`kL`, `kR`] \\ fs []
      \\ metis_tac [mlstringTheory.mlstring_lt_trans])
  >- (rw [tree_lookup_def, LET_THM]
      \\ `tree_lookup tL k = empty_entry` by (
           irule tree_lookup_miss \\ qexistsl_tac [`k1`, `kL`] \\ fs [])
      \\ `tree_lookup tR k = empty_entry` by (
           irule tree_lookup_miss \\ qexistsl_tac [`kR`, `k2`] \\ fs [])
      \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def])
  >- (imp_res_tac env_wf_bounds_le
      \\ metis_tac [mlstringTheory.mlstring_le_thm,
                    mlstringTheory.transitive_mlstring_le,
                    relationTheory.transitive_def])
  >- (imp_res_tac env_wf_bounds_le
      \\ metis_tac [mlstringTheory.mlstring_le_thm,
                    mlstringTheory.transitive_mlstring_le,
                    relationTheory.transitive_def])
QED

(* Step-left: k missed in tL; carry up one level through EnvBranch tL tR.
   tR's lookup is empty because k < kL < kR (all R's leaves are > kR). *)
Theorem tree_miss_branch_l:
  tree_miss tL k1 kL k /\ env_wf (EnvBranch tL tR) k1 k2 ==>
  tree_miss (EnvBranch tL tR) k1 k2 k
Proof
  simp [tree_miss_def] \\ strip_tac
  \\ `?kl kr. env_wf tL k1 kl /\ env_wf tR kr k2 /\ kl < kr`
      by metis_tac [env_wf_branch_inv]
  \\ `kl = kL` by metis_tac [env_wf_bounds_unique]
  \\ gvs []
  \\ `tree_lookup tR k = empty_entry` by (
        irule tree_lookup_miss \\ qexistsl_tac [`kr`, `k2`] \\ fs []
        \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans])
  \\ conj_tac >-
      (rw [tree_lookup_def, LET_THM]
        \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def])
  \\ imp_res_tac env_wf_bounds_le
  \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans]
QED

(* Step-right: symmetric. *)
Theorem tree_miss_branch_r:
  tree_miss tR kR k2 k /\ env_wf (EnvBranch tL tR) k1 k2 ==>
  tree_miss (EnvBranch tL tR) k1 k2 k
Proof
  simp [tree_miss_def] \\ strip_tac
  \\ `?kl kr. env_wf tL k1 kl /\ env_wf tR kr k2 /\ kl < kr`
       by metis_tac [env_wf_branch_inv]
  \\ `kr = kR` by metis_tac [env_wf_bounds_unique]
  \\ gvs []
  \\ `tree_lookup tL k = empty_entry` by (
        irule tree_lookup_miss \\ qexistsl_tac [`k1`, `kl`] \\ fs []
        \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans])
  \\ conj_tac >-
       (rw [tree_lookup_def, LET_THM]
        \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def])
  \\ imp_res_tac env_wf_bounds_le
  \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans]
QED

(* CPS forms for INST + PROVE_HYP in the ML driver. *)
Theorem tree_miss_gap_cps:
  tT = EnvBranch tL tR /\
  env_wf tL k1 kL /\ env_wf tR kR k2 /\
  kL < k /\ k < kR ==>
  tree_miss tT k1 k2 k
Proof
  rpt strip_tac \\ gvs []
  \\ irule tree_miss_gap \\ metis_tac []
QED

Theorem tree_miss_branch_l_cps:
  tT = EnvBranch tL tR /\
  tree_miss tL k1 kL k /\ env_wf tT k1 k2 ==>
  tree_miss tT k1 k2 k
Proof
  rpt strip_tac \\ gvs []
  \\ irule tree_miss_branch_l \\ metis_tac []
QED

Theorem tree_miss_branch_r_cps:
  tT = EnvBranch tL tR /\
  tree_miss tR kR k2 k /\ env_wf tT k1 k2 ==>
  tree_miss tT k1 k2 k
Proof
  rpt strip_tac \\ gvs []
  \\ irule tree_miss_branch_r \\ metis_tac []
QED

Theorem tree_miss_imp_lookup_cps:
  tree_miss t k1 k2 k ==> tree_lookup t k = empty_entry
Proof
  metis_tac [tree_miss_imp_lookup]
QED

(* Unified tree_lookup hit theorem: WF + membership ==> return the entry *)
Theorem tree_lookup_hit:
  !t k1 k2 k e. env_wf t k1 k2 /\ env_leaf_mem k e t ==>
    tree_lookup t k = e
Proof
  Induct_on `t`
  >- (rw [env_wf_def, env_leaf_mem_def, tree_lookup_def])
  \\ rw [env_wf_def, env_leaf_mem_def, tree_lookup_def, LET_THM]
  \\ res_tac
  >- (`tree_lookup t' k = empty_entry` by (
        match_mp_tac tree_lookup_miss \\ qexistsl_tac [`kr`, `k2`]
        \\ imp_res_tac env_wf_mem_bounds \\ fs []
        \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans])
      \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def,
             env_entry_component_equality])
  \\ `tree_lookup t k = empty_entry` by (
        match_mp_tac tree_lookup_miss \\ qexistsl_tac [`k1`, `kl`]
        \\ imp_res_tac env_wf_mem_bounds \\ fs []
        \\ metis_tac [mlstringTheory.mlstring_le_thm, mlstringTheory.mlstring_lt_trans])
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def,
         env_entry_component_equality]
QED

(* --- nsLookup on projected trees --- *)

(*
(* Helpers: nsLookup on merge_env *)
Theorem nsLookup_merge_none:
  nsLookup e1.v (Short k) = NONE /\ nsLookup e2.v (Short k) = NONE ==>
  nsLookup (merge_env e1 e2).v (Short k) = NONE
Proof
  Cases_on `e1.v` \\ Cases_on `e2.v`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
QED

Theorem merge_left_sv:
  nsLookup e1.v (Short k) = r /\ nsLookup e2.v (Short k) = NONE ==>
  nsLookup (merge_env e1 e2).v (Short k) = r
Proof
  Cases_on `e1.v` \\ Cases_on `e2.v`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
  \\ Cases_on `r` \\ fs []
QED

Theorem merge_right_sv:
  nsLookup e1.v (Short k) = NONE ==>
  nsLookup (merge_env e1 e2).v (Short k) = nsLookup e2.v (Short k)
Proof
  Cases_on `e1.v` \\ Cases_on `e2.v`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
QED

(* NONE when key is beyond tree's range *)
Theorem nsLookup_proj_none_right:
  !t k1 k2 k. env_wf t k1 k2 /\ k2 < k ==>
    nsLookup (proj t).v (Short k) = NONE
Proof
  Induct_on `t`
  >- (rw [env_wf_def, proj_def, nsLookup_def, ns_of_sv_def]
      \\ Cases_on `e.sv` \\ fs [ns_of_sv_def]
      \\ strip_tac \\ fs [mlstringTheory.mlstring_lt_nonrefl])
  \\ rw [env_wf_def]
  \\ imp_res_tac env_wf_bounds_le
  \\ `kl < k` by
       (`kl < kr` by fs []
        \\ `kr ≤ k2` by
             (imp_res_tac env_wf_bounds_le \\ fs [])
        \\ fs []
        >- (`kl < k2` by
              (imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                              mlstringTheory.mlstring_lt_trans) \\ fs [])
            \\ imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                              mlstringTheory.mlstring_lt_trans) \\ fs [])
        >- (imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            mlstringTheory.mlstring_lt_trans) \\ fs []))
  \\ `nsLookup (proj t).v (Short k) = NONE` by res_tac
  \\ `nsLookup (proj t').v (Short k) = NONE` by res_tac
  \\ fs [proj_def] \\ imp_res_tac nsLookup_merge_none
QED

Theorem nsLookup_proj_none_left:
  !t k1 k2 k. env_wf t k1 k2 /\ k < k1 ==>
    nsLookup (proj t).v (Short k) = NONE
Proof
  Induct_on `t`
  >- (rw [env_wf_def, proj_def, nsLookup_def, ns_of_sv_def]
      \\ Cases_on `e.sv` \\ fs [ns_of_sv_def]
      \\ strip_tac \\ fs [mlstringTheory.mlstring_lt_nonrefl])
  \\ rw [env_wf_def]
  \\ imp_res_tac env_wf_bounds_le
  \\ `k < kr` by
       (`k1 < kl \/ k1 = kl` by fs []
        \\ fs []
        >- (`k < kl` by
              (imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                              mlstringTheory.mlstring_lt_trans) \\ fs [])
            \\ imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                              mlstringTheory.mlstring_lt_trans) \\ fs [])
        >- (imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            mlstringTheory.mlstring_lt_trans) \\ fs []))
  \\ `nsLookup (proj t).v (Short k) = NONE` by res_tac
  \\ `nsLookup (proj t').v (Short k) = NONE` by res_tac
  \\ fs [proj_def] \\ imp_res_tac nsLookup_merge_none
QED

(* Main lookup theorem: WF + membership => nsLookup result *)
Theorem nsLookup_proj_sv:
  !t k1 k2 k e. env_wf t k1 k2 /\ env_leaf_mem k e t ==>
    nsLookup (proj t).v (Short k) = e.sv
Proof
  Induct_on `t`
  >- (rw [env_wf_def, env_leaf_mem_def, proj_def]
      \\ Cases_on `e.sv` \\ Cases_on `e.mv`
      \\ simp [ns_of_sv_def, ns_of_mod_def, nsLookup_def, ALOOKUP_def])
  >- (rw [env_wf_def, env_leaf_mem_def, proj_def] \\ res_tac
      (* left subcase: k in left, need NONE for right *)
      >- (`nsLookup (proj t').v (Short k) = NONE` by
            (match_mp_tac nsLookup_proj_none_left
             \\ metis_tac [env_wf_mem_bounds, mlstringTheory.mlstring_lt_trans])
          \\ metis_tac [merge_left_sv])
      (* right subcase: k in right, need NONE for left *)
      >- (`nsLookup (proj t).v (Short k) = NONE` by
            (match_mp_tac nsLookup_proj_none_right
             \\ metis_tac [env_wf_mem_bounds, env_wf_bounds_le,
                            mlstringTheory.mlstring_lt_trans])
          \\ metis_tac [merge_right_sv]))
QED *)

(* --- Short constructor lookup --- *)

Theorem nsLookup_merge_none_c:
  nsLookup e1.c (Short k) = NONE /\ nsLookup e2.c (Short k) = NONE ==>
  nsLookup (merge_env e1 e2).c (Short k) = NONE
Proof
  Cases_on `e1.c` \\ Cases_on `e2.c`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
QED

Theorem merge_left_sc:
  nsLookup e1.c (Short k) = r /\ nsLookup e2.c (Short k) = NONE ==>
  nsLookup (merge_env e1 e2).c (Short k) = r
Proof
  Cases_on `e1.c` \\ Cases_on `e2.c`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
  \\ Cases_on `r` \\ fs []
QED

Theorem merge_right_sc:
  nsLookup e1.c (Short k) = NONE ==>
  nsLookup (merge_env e1 e2).c (Short k) = nsLookup e2.c (Short k)
Proof
  Cases_on `e1.c` \\ Cases_on `e2.c`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
QED

(* Theorem nsLookup_proj_none_right_c:
  !t k1 k2 k. env_wf t k1 k2 /\ k2 < k ==>
    nsLookup (proj t).c (Short k) = NONE
Proof
  Induct_on `t`
  >- (rw [env_wf_def, proj_def, nsLookup_def, ns_of_sc_def]
      \\ Cases_on `e.sc` \\ fs [ns_of_sc_def]
      \\ strip_tac \\ fs [mlstringTheory.mlstring_lt_nonrefl])
  \\ rw [env_wf_def]
  \\ imp_res_tac env_wf_bounds_le
  \\ `kl < k` by
       (`kl < kr` by fs []
        \\ `kr < k2 \/ kr = k2` by
             (imp_res_tac env_wf_bounds_le \\ fs [])
        \\ fs []
        >- (imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            mlstringTheory.mlstring_lt_trans)
            \\ imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                              mlstringTheory.mlstring_lt_trans) \\ fs [])
        >- (imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            mlstringTheory.mlstring_lt_trans) \\ fs []))
  \\ res_tac
  \\ fs [proj_def] \\ imp_res_tac nsLookup_merge_none_c
QED

Theorem nsLookup_proj_none_left_c:
  !t k1 k2 k. env_wf t k1 k2 /\ k < k1 ==>
    nsLookup (proj t).c (Short k) = NONE
Proof
  Induct_on `t`
  >- (rw [env_wf_def, proj_def, nsLookup_def, ns_of_sc_def]
      \\ Cases_on `e.sc` \\ fs [ns_of_sc_def]
      \\ strip_tac \\ fs [mlstringTheory.mlstring_lt_nonrefl])
  \\ rw [env_wf_def]
  \\ imp_res_tac env_wf_bounds_le
  \\ `k < kr` by
       (`k1 < kl \/ k1 = kl` by fs []
        \\ fs []
        >- (imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            mlstringTheory.mlstring_lt_trans)
            \\ imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                              mlstringTheory.mlstring_lt_trans) \\ fs [])
        >- (imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            mlstringTheory.mlstring_lt_trans) \\ fs []))
  \\ res_tac
  \\ fs [proj_def] \\ imp_res_tac nsLookup_merge_none_c
QED

Theorem nsLookup_proj_sc:
  !t k1 k2 k e. env_wf t k1 k2 /\ env_leaf_mem k e t ==>
    nsLookup (proj t).c (Short k) = e.sc
Proof
  Induct_on `t`
  >- (rw [env_wf_def, env_leaf_mem_def, proj_def]
      \\ Cases_on `e.sc` \\ Cases_on `e.mc`
      \\ simp [ns_of_sc_def, ns_of_mod_def, nsLookup_def, ALOOKUP_def])
  >- (rw [env_wf_def, env_leaf_mem_def, proj_def] \\ res_tac
      >- (`nsLookup (proj t').c (Short k) = NONE` by
            (match_mp_tac nsLookup_proj_none_left_c
             \\ metis_tac [env_wf_mem_bounds, mlstringTheory.mlstring_lt_trans])
          \\ metis_tac [merge_left_sc])
      >- (`nsLookup (proj t).c (Short k) = NONE` by
            (match_mp_tac nsLookup_proj_none_right_c
             \\ metis_tac [env_wf_mem_bounds, env_wf_bounds_le,
                            mlstringTheory.mlstring_lt_trans])
          \\ metis_tac [merge_right_sc]))
QED *)

(* the components of nsLookup are 'nicer' partial functions *)

Definition nsLookup_Short_def[nocompute]:
  nsLookup_Short ns nm = nsLookup ns (Short nm)
End

Definition nsLookup_Mod1_def[nocompute]:
  nsLookup_Mod1 ns = (case ns of Bind _ ms => ALOOKUP ms)
End

(* The unified sem_env lookup: packages all four component lookups for a key
   into a single env_entry. Paired with tree_lookup (defined above) for the
   equivalence theorem maintained by ml_progLib. *)
Definition nsLookup_all_def:
  nsLookup_all (env : v sem_env) k =
    <| sv := nsLookup env.v (Short k)
     ; sc := nsLookup env.c (Short k)
     ; mv := nsLookup_Mod1 env.v k
     ; mc := nsLookup_Mod1 env.c k |>
End

(* Inductive step lemmas: how nsLookup_all changes under each env-construction
   operation. Chain these with the tree-level equivalent to build the per-env
   (nsLookup_all env = tree_lookup tree_const) theorem. *)

Theorem nsLookup_all_write:
  !n v env k. nsLookup_all (write n v env) k =
    if k = n then
      <| sv := SOME v
       ; sc := (nsLookup_all env k).sc
       ; mv := (nsLookup_all env k).mv
       ; mc := (nsLookup_all env k).mc |>
    else nsLookup_all env k
Proof
  rw [nsLookup_all_def, write_def]
  \\ Cases_on `env.v`
  \\ fs [nsBind_def, nsLookup_def, nsLookup_Mod1_def]
QED

Theorem nsLookup_all_write_cons:
  !n c env k. nsLookup_all (write_cons n c env) k =
    if k = n then
      <| sv := (nsLookup_all env k).sv
       ; sc := SOME c
       ; mv := (nsLookup_all env k).mv
       ; mc := (nsLookup_all env k).mc |>
    else nsLookup_all env k
Proof
  rw [nsLookup_all_def, write_cons_def]
  \\ Cases_on `env.c`
  \\ fs [nsSing_def, nsBind_def, nsAppend_def, nsLookup_def, nsLookup_Mod1_def]
QED

Theorem nsLookup_all_write_mod:
  !mn mod_env env k. nsLookup_all (write_mod mn mod_env env) k =
    if k = mn then
      <| sv := (nsLookup_all env k).sv
       ; sc := (nsLookup_all env k).sc
       ; mv := SOME mod_env.v
       ; mc := SOME mod_env.c |>
    else nsLookup_all env k
Proof
  rw [nsLookup_all_def, write_mod_def]
  \\ Cases_on `env.v` \\ Cases_on `env.c`
  \\ fs [nsLift_def, nsAppend_def, nsLookup_def, nsLookup_Mod1_def,
         alistTheory.ALOOKUP_APPEND]
QED

Theorem nsLookup_all_merge_env:
  !env1 env2 k. nsLookup_all (merge_env env1 env2) k =
    (let e1 = nsLookup_all env1 k in
     let e2 = nsLookup_all env2 k in
       <| sv := OPTION_CHOICE e1.sv e2.sv
        ; sc := OPTION_CHOICE e1.sc e2.sc
        ; mv := OPTION_CHOICE e1.mv e2.mv
        ; mc := OPTION_CHOICE e1.mc e2.mc |>)
Proof
  rw [nsLookup_all_def, merge_env_def]
  \\ Cases_on `env1.v` \\ Cases_on `env2.v`
  \\ Cases_on `env1.c` \\ Cases_on `env2.c`
  \\ fs [nsAppend_def, nsLookup_def, nsLookup_Mod1_def,
         alistTheory.ALOOKUP_APPEND]
  \\ rpt (CASE_TAC \\ fs [])
QED

Theorem nsLookup_all_empty_env:
  !k. nsLookup_all empty_env k = empty_entry
Proof
  fs [nsLookup_all_def, empty_env_def, nsEmpty_def, nsLookup_def,
      nsLookup_Mod1_def, empty_entry_def]
QED

(* CPS-style tree-level versions of write / write_cons / write_mod:
   given nsLookup_all env = tree_lookup T, inserting a new binding is
   equivalent to branching on a singleton leaf on the LEFT (priority). *)

Theorem nsLookup_all_write_tree_cps:
  !n v env tT tL Tnew.
    nsLookup_all env = tree_lookup tT /\
    tL = EnvLeaf n (empty_entry with sv := SOME v) /\
    Tnew = EnvBranch tL tT ==>
    nsLookup_all (write n v env) = tree_lookup Tnew
Proof
  rpt strip_tac \\ gvs []
  \\ simp [FUN_EQ_THM] \\ gen_tac
  \\ simp [nsLookup_all_write, tree_lookup_def, LET_THM, empty_entry_def,
           optionTheory.OPTION_CHOICE_def]
  \\ `nsLookup_all env x = tree_lookup tT x` by fs [FUN_EQ_THM]
  \\ rw [] \\ fs [] \\ rw [] \\ simp [env_entry_component_equality]
QED

Theorem nsLookup_all_write_cons_tree_cps:
  !n c env tT tL Tnew.
    nsLookup_all env = tree_lookup tT /\
    tL = EnvLeaf n (empty_entry with sc := SOME c) /\
    Tnew = EnvBranch tL tT ==>
    nsLookup_all (write_cons n c env) = tree_lookup Tnew
Proof
  rpt strip_tac \\ gvs []
  \\ simp [FUN_EQ_THM] \\ gen_tac
  \\ simp [nsLookup_all_write_cons, tree_lookup_def, LET_THM, empty_entry_def,
           optionTheory.OPTION_CHOICE_def]
  \\ `nsLookup_all env x = tree_lookup tT x` by fs [FUN_EQ_THM]
  \\ rw [] \\ fs [] \\ rw [] \\ simp [env_entry_component_equality]
QED

Theorem nsLookup_all_write_mod_tree_cps:
  !n mod_env env tT tL Tnew.
    nsLookup_all env = tree_lookup tT /\
    tL = EnvLeaf n ((empty_entry with mv := SOME mod_env.v)
                                 with mc := SOME mod_env.c) /\
    Tnew = EnvBranch tL tT ==>
    nsLookup_all (write_mod n mod_env env) = tree_lookup Tnew
Proof
  rpt strip_tac \\ gvs []
  \\ simp [FUN_EQ_THM] \\ gen_tac
  \\ simp [nsLookup_all_write_mod, tree_lookup_def, LET_THM, empty_entry_def,
           optionTheory.OPTION_CHOICE_def]
  \\ `nsLookup_all env x = tree_lookup tT x` by fs [FUN_EQ_THM]
  \\ rw [] \\ fs [] \\ rw [] \\ simp [env_entry_component_equality]
QED

(* Tree-backed pfun_eqs: from a function-level equivalence
   nsLookup_all env = tree_lookup tree, derive the four partial-function
   forms that nsLookup_conv / alist_treeLib normally work with. *)
Theorem nsLookup_pf_from_tree:
  !env tree.
    nsLookup_all env = tree_lookup tree ==>
    nsLookup_Short env.v = (\k. (tree_lookup tree k).sv) /\
    nsLookup_Short env.c = (\k. (tree_lookup tree k).sc) /\
    nsLookup_Mod1 env.v = (\k. (tree_lookup tree k).mv) /\
    nsLookup_Mod1 env.c = (\k. (tree_lookup tree k).mc)
Proof
  rpt strip_tac
  \\ simp [FUN_EQ_THM, nsLookup_Short_def]
  \\ gen_tac
  \\ qspecl_then [`env`, `k`] assume_tac nsLookup_all_def
  \\ `nsLookup_all env k = tree_lookup tree k` by metis_tac []
  \\ fs []
QED

(* Direct projection theorems: the nsLookup_{Short,Mod1} functions on
   env.{v,c} are just field projections of `nsLookup_all env k`.  Used by
   nsLookup_tree_conv: SPECL [env, k] one of these, ONCE_REWRITE_RULE with
   the env's tree-equivalence (nsLookup_all env = tree_lookup T), substitute
   the concrete tree_lookup result, EVAL the field projection. *)
Theorem nsLookup_Short_v_via_all:
  nsLookup_Short env.v k = (nsLookup_all env k).sv
Proof
  rw [nsLookup_Short_def, nsLookup_all_def]
QED

Theorem nsLookup_Short_c_via_all:
  nsLookup_Short env.c k = (nsLookup_all env k).sc
Proof
  rw [nsLookup_Short_def, nsLookup_all_def]
QED

Theorem nsLookup_Mod1_v_via_all:
  nsLookup_Mod1 env.v k = (nsLookup_all env k).mv
Proof
  rw [nsLookup_all_def]
QED

Theorem nsLookup_Mod1_c_via_all:
  nsLookup_Mod1 env.c k = (nsLookup_all env k).mc
Proof
  rw [nsLookup_all_def]
QED

(* Merge-env push-down: when both sides have a tree equivalence, the
   combination is exactly tree_lookup (EnvBranch T1 T2). Holds
   unconditionally; WF of the combined tree requires disjoint ranges, handled
   separately by env_wf_branch_intro. *)
Theorem nsLookup_all_merge_tree:
  !e1 e2 T1 T2.
    nsLookup_all e1 = tree_lookup T1 /\
    nsLookup_all e2 = tree_lookup T2 ==>
    nsLookup_all (merge_env e1 e2) = tree_lookup (EnvBranch T1 T2)
Proof
  rpt strip_tac
  \\ simp [FUN_EQ_THM]
  \\ gen_tac
  \\ simp [nsLookup_all_merge_env, tree_lookup_def, LET_THM]
  \\ `nsLookup_all e1 x = tree_lookup T1 x` by fs [FUN_EQ_THM]
  \\ `nsLookup_all e2 x = tree_lookup T2 x` by fs [FUN_EQ_THM]
  \\ simp []
QED

Theorem nsLookup_all_merge_tree_cps:
  !e1 e2 T1 T2 T3.
    nsLookup_all e1 = tree_lookup T1 /\
    nsLookup_all e2 = tree_lookup T2 /\
    T3 = EnvBranch T1 T2 ==>
    nsLookup_all (merge_env e1 e2) = tree_lookup T3
Proof
  metis_tac [nsLookup_all_merge_tree]
QED

(* Tree-side insertion lemmas: how tree_lookup changes when we structurally
   insert or update a leaf. The ML chains these as it walks the tree during
   insertion, building the per-env equivalence proof. *)

Theorem tree_lookup_prepend:
  !t k1 k2 n entry k.
    env_wf t k1 k2 /\ n < k1 ==>
    tree_lookup (EnvBranch (EnvLeaf n entry) t) k =
      if k = n then entry else tree_lookup t k
Proof
  rpt gen_tac \\ strip_tac
  \\ rw [tree_lookup_def, LET_THM]
  \\ TRY (`tree_lookup t k = empty_entry` by
        (match_mp_tac tree_lookup_miss \\ qexistsl_tac [`k1`,`k2`] \\ fs []))
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def,
         env_entry_component_equality]
QED

Theorem tree_lookup_append:
  !t k1 k2 n entry k.
    env_wf t k1 k2 /\ k2 < n ==>
    tree_lookup (EnvBranch t (EnvLeaf n entry)) k =
      if k = n then entry else tree_lookup t k
Proof
  rpt gen_tac \\ strip_tac
  \\ rw [tree_lookup_def, LET_THM]
  \\ TRY (`tree_lookup t k = empty_entry` by
        (match_mp_tac tree_lookup_miss \\ qexistsl_tac [`k1`,`k2`] \\ fs []))
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def,
         env_entry_component_equality]
QED

(* Propagate a local update to the right through a branch *)
Theorem tree_lookup_branch_right_update:
  !l k1 k2 r r' n entry.
    env_wf l k1 k2 /\ k2 < n /\
    (!k. tree_lookup r' k = if k = n then entry else tree_lookup r k) ==>
    !k. tree_lookup (EnvBranch l r') k =
          if k = n then entry else tree_lookup (EnvBranch l r) k
Proof
  rw [tree_lookup_def, LET_THM]
  \\ TRY (`tree_lookup l n = empty_entry` by
            (match_mp_tac tree_lookup_miss \\ qexistsl_tac [`k1`,`k2`] \\ fs []))
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def,
         env_entry_component_equality]
  \\ rw []
QED

(* --- merge_env rebalance infrastructure ---
   combine_entries + flatten_tree + alist_lookup + merge_alists + build_tree
   are the building blocks for rebalancing two WF trees into one on merge_env.
   Proofs of the remaining correctness theorems (alist_lookup_merge_alists,
   tree_lookup_of_build_tree, env_wf_build_tree, tree_merge_spec) are in flight. *)

Definition combine_entries_def:
  combine_entries e1 e2 =
    <| sv := OPTION_CHOICE e1.sv e2.sv
     ; sc := OPTION_CHOICE e1.sc e2.sc
     ; mv := OPTION_CHOICE e1.mv e2.mv
     ; mc := OPTION_CHOICE e1.mc e2.mc |>
End

Definition flatten_tree_def:
  flatten_tree (EnvLeaf k e) = [(k, e)] /\
  flatten_tree (EnvBranch l r) = flatten_tree l ++ flatten_tree r
End

Definition alist_lookup_def:
  (alist_lookup ([]:(mlstring # env_entry) list) (k:mlstring) = empty_entry) /\
  (alist_lookup ((k',e)::xs) k =
     if k = k' then combine_entries e (alist_lookup xs k)
     else alist_lookup xs k)
End

Definition merge_alists_def:
  (merge_alists ([]:(mlstring # env_entry) list) bs = bs) /\
  (merge_alists (a::as) [] = a::as) /\
  (merge_alists ((k1,e1)::as) ((k2,e2)::bs) =
     if k1 = k2 then (k1, combine_entries e1 e2) :: merge_alists as bs
     else if k1 < k2 then (k1,e1) :: merge_alists as ((k2,e2)::bs)
     else (k2,e2) :: merge_alists ((k1,e1)::as) bs)
End

Theorem OPTION_CHOICE_assoc:
  !x y z. OPTION_CHOICE x (OPTION_CHOICE y z) = OPTION_CHOICE (OPTION_CHOICE x y) z
Proof
  Cases \\ Cases \\ fs [optionTheory.OPTION_CHOICE_def]
QED

Theorem combine_entries_empty_left:
  !e. combine_entries empty_entry e = e
Proof
  rw [combine_entries_def, empty_entry_def, optionTheory.OPTION_CHOICE_def]
  \\ rw [env_entry_component_equality]
QED

Theorem combine_entries_empty_right:
  !(e:env_entry). combine_entries e empty_entry = e
Proof
  rw [combine_entries_def, empty_entry_def, optionTheory.OPTION_CHOICE_def]
  \\ rw [env_entry_component_equality]
  \\ Cases_on `e.sv` \\ Cases_on `e.sc` \\ Cases_on `e.mv` \\ Cases_on `e.mc`
  \\ fs []
QED

Theorem combine_entries_assoc:
  !(e1:env_entry) e2 e3.
    combine_entries e1 (combine_entries e2 e3) =
    combine_entries (combine_entries e1 e2) e3
Proof
  rpt gen_tac
  \\ fs [combine_entries_def, env_entry_component_equality,
         GSYM OPTION_CHOICE_assoc]
QED

(* --- Commutativity of record updates through combine_entries ---
   When the LHS has a definite field (SOME _), combine_entries lifts that
   fupd outside.  Together with combine_entries_empty_left, these rules let
   simp eliminate combine_entries from stacked-fupd entries. *)
Theorem combine_entries_sv_fupd:
  !v e1 e2.
    combine_entries (e1 with sv := SOME v) e2 =
    (combine_entries e1 e2) with sv := SOME v
Proof
  rw [combine_entries_def, env_entry_component_equality,
      optionTheory.OPTION_CHOICE_def]
QED

Theorem combine_entries_sc_fupd:
  !c e1 e2.
    combine_entries (e1 with sc := SOME c) e2 =
    (combine_entries e1 e2) with sc := SOME c
Proof
  rw [combine_entries_def, env_entry_component_equality,
      optionTheory.OPTION_CHOICE_def]
QED

Theorem combine_entries_mv_fupd:
  !m e1 e2.
    combine_entries (e1 with mv := SOME m) e2 =
    (combine_entries e1 e2) with mv := SOME m
Proof
  rw [combine_entries_def, env_entry_component_equality,
      optionTheory.OPTION_CHOICE_def]
QED

Theorem combine_entries_mc_fupd:
  !n e1 e2.
    combine_entries (e1 with mc := SOME n) e2 =
    (combine_entries e1 e2) with mc := SOME n
Proof
  rw [combine_entries_def, env_entry_component_equality,
      optionTheory.OPTION_CHOICE_def]
QED

Theorem alist_lookup_append:
  !xs ys k. alist_lookup (xs ++ ys) k =
              combine_entries (alist_lookup xs k) (alist_lookup ys k)
Proof
  Induct
  >- simp [alist_lookup_def, combine_entries_empty_left]
  \\ Cases \\ rw [alist_lookup_def]
  \\ simp [combine_entries_assoc]
QED

Theorem tree_lookup_flatten:
  !t k. tree_lookup t k = alist_lookup (flatten_tree t) k
Proof
  Induct
  >- (rw [tree_lookup_def, flatten_tree_def, alist_lookup_def]
      \\ fs [combine_entries_empty_right])
  \\ rw [tree_lookup_def, flatten_tree_def, alist_lookup_append,
         combine_entries_def, LET_THM]
QED

Theorem alist_lookup_lt_first:
  !xs k. SORTED mlstring_lt (MAP FST xs) /\
         (xs <> [] ==> k < FST (HD xs)) ==>
          alist_lookup xs k = empty_entry
Proof
  Induct \\ fs [alist_lookup_def]
  \\ Cases \\ rw [alist_lookup_def, combine_entries_empty_left]
  >- fs [mlstringTheory.mlstring_lt_nonrefl]
  \\ first_x_assum match_mp_tac
  \\ Cases_on `xs` \\ fs [sortingTheory.SORTED_DEF]
  \\ Cases_on `h` \\ fs [sortingTheory.SORTED_DEF]
  \\ metis_tac [mlstringTheory.mlstring_lt_trans]
QED

(* --- Primitives for merge_env rebalancing ---
   Rotation, commute (with disjoint-range side-condition), coalesce, cong.
   The ML drives the sequence of moves; each one is a one-step rewrite. *)

Theorem tree_lookup_rotate_right:
  tree_lookup (EnvBranch (EnvBranch A B) C) =
  tree_lookup (EnvBranch A (EnvBranch B C))
Proof
  rw [FUN_EQ_THM, tree_lookup_def, LET_THM]
  \\ simp [GSYM OPTION_CHOICE_assoc]
QED

Theorem tree_lookup_rotate_left:
  tree_lookup (EnvBranch A (EnvBranch B C)) =
  tree_lookup (EnvBranch (EnvBranch A B) C)
Proof
  rw [FUN_EQ_THM, tree_lookup_def, LET_THM]
  \\ simp [OPTION_CHOICE_assoc]
QED

Theorem tree_lookup_coalesce_leaves:
  !k e1 e2. tree_lookup (EnvBranch (EnvLeaf k e1) (EnvLeaf k e2)) =
            tree_lookup (EnvLeaf k (combine_entries e1 e2))
Proof
  rw [FUN_EQ_THM, tree_lookup_def, LET_THM]
  \\ rw [combine_entries_def, empty_entry_def, optionTheory.OPTION_CHOICE_def]
  \\ fs [env_entry_component_equality]
QED

Theorem tree_lookup_branch_cong:
  tree_lookup l = tree_lookup l' /\ tree_lookup r = tree_lookup r' ==>
    tree_lookup (EnvBranch l r) = tree_lookup (EnvBranch l' r')
Proof
  rw [FUN_EQ_THM, tree_lookup_def, LET_THM]
  \\ `tree_lookup l' k = tree_lookup l k` by fs [FUN_EQ_THM]
  \\ `tree_lookup r' k = tree_lookup r k` by fs [FUN_EQ_THM]
  \\ simp []
QED

(* Commute B and C within a left-skewed branch, when their key ranges
   are disjoint. The disjoint-keys form is the primitive; the WF form
   follows. *)
Theorem tree_lookup_commute_disjoint:
  (!k. tree_lookup B k = empty_entry \/ tree_lookup C k = empty_entry) ==>
    tree_lookup (EnvBranch (EnvBranch A B) C) =
    tree_lookup (EnvBranch (EnvBranch A C) B)
Proof
  rw [FUN_EQ_THM, tree_lookup_def, LET_THM]
  \\ pop_assum (qspec_then `x` assume_tac)
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def]
QED

(* Top-level sibling swap, derived from the disjoint-range commute on the
   trivial "outer" position.  Used by push-leaf when the pushed leaf's key
   sorts before the whole target tree. *)
Theorem tree_lookup_swap_disjoint:
  (!k. tree_lookup X k = empty_entry \/ tree_lookup Y k = empty_entry) ==>
  tree_lookup (EnvBranch X Y) = tree_lookup (EnvBranch Y X)
Proof
  rw [FUN_EQ_THM, tree_lookup_def, LET_THM]
  \\ pop_assum (qspec_then `x` assume_tac)
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def]
QED

Theorem tree_lookup_swap:
  env_wf X kX1 kX2 /\ env_wf Y kY1 kY2 /\
  (kX2 < kY1 \/ kY2 < kX1) ==>
  tree_lookup (EnvBranch X Y) = tree_lookup (EnvBranch Y X)
Proof
  rpt strip_tac
  \\ match_mp_tac tree_lookup_swap_disjoint
  \\ gen_tac
  (* Sub-goal 1: kX2 < kY1 *)
  >- (Cases_on `k < kY1`
      >- (disj2_tac \\ match_mp_tac tree_lookup_miss
          \\ qexistsl_tac [`kY1`, `kY2`] \\ simp [])
      \\ disj1_tac \\ match_mp_tac tree_lookup_miss
      \\ qexistsl_tac [`kX1`, `kX2`] \\ simp [] \\ disj2_tac
      \\ `kY1 = k \/ kY1 < k` by
           (Q.SPECL_THEN [`kY1`, `k`] mp_tac mlstringTheory.mlstring_lt_cases
            \\ fs [])
      \\ fs []
      \\ imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                        mlstringTheory.mlstring_lt_trans) \\ fs [])
  (* Sub-goal 2: kY2 < kX1 — symmetric *)
  \\ Cases_on `k < kX1`
  >- (disj1_tac \\ match_mp_tac tree_lookup_miss
      \\ qexistsl_tac [`kX1`, `kX2`] \\ simp [])
  \\ disj2_tac \\ match_mp_tac tree_lookup_miss
  \\ qexistsl_tac [`kY1`, `kY2`] \\ simp [] \\ disj2_tac
  \\ `kX1 = k \/ kX1 < k` by
       (Q.SPECL_THEN [`kX1`, `k`] mp_tac mlstringTheory.mlstring_lt_cases
        \\ fs [])
  \\ fs []
  \\ imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                    mlstringTheory.mlstring_lt_trans) \\ fs []
QED

Theorem tree_lookup_swap_cps:
  tT = EnvBranch X Y /\ tT' = EnvBranch Y X /\
  env_wf X kX1 kX2 /\ env_wf Y kY1 kY2 /\
  (kX2 < kY1 \/ kY2 < kX1) ==>
  tree_lookup tT = tree_lookup tT'
Proof
  rpt strip_tac \\ gvs []
  \\ match_mp_tac tree_lookup_swap \\ metis_tac []
QED

(* WF-friendly commute: caller supplies two WF theorems and a single bound
   ordering, no ∀k disjointness proof needed. *)
Theorem tree_lookup_commute:
  env_wf B kB1 kB2 /\ env_wf C kC1 kC2 /\
  (kB2 < kC1 \/ kC2 < kB1) ==>
    tree_lookup (EnvBranch (EnvBranch A B) C) =
    tree_lookup (EnvBranch (EnvBranch A C) B)
Proof
  rpt strip_tac
  \\ match_mp_tac tree_lookup_commute_disjoint
  \\ gen_tac
  (* Sub-goal 1: kB2 < kC1 *)
  >- (Cases_on `k < kC1`
      >- (disj2_tac \\ match_mp_tac tree_lookup_miss
          \\ qexistsl_tac [`kC1`, `kC2`] \\ simp [])
      \\ disj1_tac \\ match_mp_tac tree_lookup_miss
      \\ qexistsl_tac [`kB1`, `kB2`] \\ simp [] \\ disj2_tac
      \\ `kC1 = k \/ kC1 < k` by
           (Q.SPECL_THEN [`kC1`, `k`] mp_tac mlstringTheory.mlstring_lt_cases
            \\ fs [])
      \\ fs []
      \\ imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                        mlstringTheory.mlstring_lt_trans) \\ fs [])
  (* Sub-goal 2: kC2 < kB1 — symmetric *)
  \\ Cases_on `k < kB1`
  >- (disj1_tac \\ match_mp_tac tree_lookup_miss
      \\ qexistsl_tac [`kB1`, `kB2`] \\ simp [])
  \\ disj2_tac \\ match_mp_tac tree_lookup_miss
  \\ qexistsl_tac [`kC1`, `kC2`] \\ simp [] \\ disj2_tac
  \\ `kB1 = k \/ kB1 < k` by
       (Q.SPECL_THEN [`kB1`, `k`] mp_tac mlstringTheory.mlstring_lt_cases
        \\ fs [])
  \\ fs []
  \\ imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO]
                    mlstringTheory.mlstring_lt_trans) \\ fs []
QED

(* Leaf-level update: replace entry at a leaf *)
Theorem tree_lookup_replace_leaf:
  !n old_entry new_entry k.
    tree_lookup (EnvLeaf n new_entry) k =
      if k = n then new_entry
      else tree_lookup (EnvLeaf n old_entry) k
Proof
  rw [tree_lookup_def]
QED

(* Propagate a local update to the left through a branch *)
Theorem tree_lookup_branch_left_update:
  !r k1 k2 l l' n entry.
    env_wf r k1 k2 /\ n < k1 /\
    (!k. tree_lookup l' k = if k = n then entry else tree_lookup l k) ==>
    !k. tree_lookup (EnvBranch l' r) k =
          if k = n then entry else tree_lookup (EnvBranch l r) k
Proof
  rw [tree_lookup_def, LET_THM]
  \\ TRY (`tree_lookup r n = empty_entry` by
            (match_mp_tac tree_lookup_miss \\ qexistsl_tac [`k1`,`k2`] \\ fs []))
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def,
         env_entry_component_equality]
  \\ rw []
QED

(* --- CPS-form primitives ---
   Each lemma takes equations of the form  T = EnvBranch l r  or
   T = EnvLeaf k e  as premises. When the ML driver has a constant for
   a node, it passes the Definition; when the node is a raw EnvBranch,
   it passes REFL. This unifies the constant and raw cases so the
   conclusion is always about the "outer" names (which may themselves
   be constants), keeping saved theorems compact. *)

Theorem tree_lookup_rotate_right_cps:
  tL = EnvBranch tA tB /\ tT = EnvBranch tL tC /\
  tR = EnvBranch tB tC /\ tT' = EnvBranch tA tR ==>
  tree_lookup tT = tree_lookup tT'
Proof
  rpt strip_tac \\ gvs [] \\ simp [tree_lookup_rotate_right]
QED

Theorem tree_lookup_rotate_left_cps:
  tR = EnvBranch tB tC /\ tT = EnvBranch tA tR /\
  tL = EnvBranch tA tB /\ tT' = EnvBranch tL tC ==>
  tree_lookup tT = tree_lookup tT'
Proof
  rpt strip_tac \\ gvs [] \\ simp [tree_lookup_rotate_left]
QED

Theorem tree_lookup_coalesce_leaves_cps:
  tL1 = EnvLeaf k e1 /\ tL2 = EnvLeaf k e2 /\ tT = EnvBranch tL1 tL2 /\
  tL = EnvLeaf k (combine_entries e1 e2) ==>
  tree_lookup tT = tree_lookup tL
Proof
  rpt strip_tac \\ gvs [] \\ simp [tree_lookup_coalesce_leaves]
QED

Theorem tree_lookup_branch_cong_cps:
  tT = EnvBranch l r /\ tT' = EnvBranch l' r' /\
  tree_lookup l = tree_lookup l' /\ tree_lookup r = tree_lookup r' ==>
  tree_lookup tT = tree_lookup tT'
Proof
  rpt strip_tac \\ gvs []
  \\ metis_tac [tree_lookup_branch_cong]
QED

Theorem tree_lookup_commute_cps:
  tLinner = EnvBranch tA tB /\ tT = EnvBranch tLinner tC /\
  tLinner' = EnvBranch tA tC /\ tT' = EnvBranch tLinner' tB /\
  env_wf tB kB1 kB2 /\ env_wf tC kC1 kC2 /\
  (kB2 < kC1 \/ kC2 < kB1) ==>
  tree_lookup tT = tree_lookup tT'
Proof
  rpt strip_tac \\ gvs [] \\ metis_tac [tree_lookup_commute]
QED

Theorem env_wf_leaf_cps:
  tT = EnvLeaf k e ==> env_wf tT k k
Proof
  rw [env_wf_def]
QED

Theorem env_wf_branch_intro_cps:
  tT = EnvBranch l r /\ env_wf l k1 kl /\ env_wf r kr k2 /\ kl < kr ==>
  env_wf tT k1 k2
Proof
  rpt strip_tac \\ gvs []
  \\ match_mp_tac env_wf_branch_intro \\ metis_tac []
QED

Theorem tree_lookup_prepend_cps:
  tL = EnvLeaf n entry /\ tT = EnvBranch tL t /\
  env_wf t k1 k2 /\ n < k1 ==>
  !k. tree_lookup tT k = if k = n then entry else tree_lookup t k
Proof
  rpt strip_tac \\ gvs []
  \\ match_mp_tac tree_lookup_prepend \\ metis_tac []
QED

Theorem tree_lookup_append_cps:
  tL = EnvLeaf n entry /\ tT = EnvBranch t tL /\
  env_wf t k1 k2 /\ k2 < n ==>
  !k. tree_lookup tT k = if k = n then entry else tree_lookup t k
Proof
  rpt strip_tac \\ gvs []
  \\ match_mp_tac tree_lookup_append \\ metis_tac []
QED

Theorem tree_lookup_branch_right_update_cps:
  tT = EnvBranch l r /\ tT' = EnvBranch l r' /\
  env_wf l k1 k2 /\ k2 < n /\
  (!k. tree_lookup r' k = if k = n then entry else tree_lookup r k) ==>
  !k. tree_lookup tT' k = if k = n then entry else tree_lookup tT k
Proof
  rpt strip_tac \\ gvs []
  \\ irule tree_lookup_branch_right_update \\ metis_tac []
QED

Theorem tree_lookup_branch_left_update_cps:
  tT = EnvBranch l r /\ tT' = EnvBranch l' r /\
  env_wf r k1 k2 /\ n < k1 /\
  (!k. tree_lookup l' k = if k = n then entry else tree_lookup l k) ==>
  !k. tree_lookup tT' k = if k = n then entry else tree_lookup tT k
Proof
  rpt strip_tac \\ gvs []
  \\ irule tree_lookup_branch_left_update \\ metis_tac []
QED

Theorem tree_lookup_replace_leaf_cps:
  tTold = EnvLeaf n old_entry /\ tTnew = EnvLeaf n new_entry ==>
  !k. tree_lookup tTnew k = if k = n then new_entry else tree_lookup tTold k
Proof
  rpt strip_tac \\ gvs [tree_lookup_def]
QED

(* CPS forms of env_leaf_mem so the ML driver can construct membership
   proofs in terms of the constant-backed tree_tms, matching the shape
   used by WF theorems. *)

Theorem env_leaf_mem_leaf_cps:
  tT = EnvLeaf k e ==> env_leaf_mem k e tT
Proof
  rw [env_leaf_mem_def]
QED

Theorem env_leaf_mem_branch_l_cps:
  tT = EnvBranch l r /\ env_leaf_mem k e l ==> env_leaf_mem k e tT
Proof
  rw [env_leaf_mem_def]
QED

Theorem env_leaf_mem_branch_r_cps:
  tT = EnvBranch l r /\ env_leaf_mem k e r ==> env_leaf_mem k e tT
Proof
  rw [env_leaf_mem_def]
QED

(* --- Mod1 (module) lookup on projected trees --- *)

Theorem nsLookup_Mod1_merge_none_v:
  nsLookup_Mod1 e1.v mnm = NONE /\ nsLookup_Mod1 e2.v mnm = NONE ==>
  nsLookup_Mod1 (merge_env e1 e2).v mnm = NONE
Proof
  Cases_on `e1.v` \\ Cases_on `e2.v`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_Mod1_def, ALOOKUP_APPEND]
QED

Theorem merge_left_mv:
  nsLookup_Mod1 e1.v mnm = r /\ nsLookup_Mod1 e2.v mnm = NONE ==>
  nsLookup_Mod1 (merge_env e1 e2).v mnm = r
Proof
  Cases_on `e1.v` \\ Cases_on `e2.v`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_Mod1_def, ALOOKUP_APPEND]
  \\ Cases_on `r` \\ fs []
QED

Theorem merge_right_mv:
  nsLookup_Mod1 e1.v mnm = NONE ==>
  nsLookup_Mod1 (merge_env e1 e2).v mnm = nsLookup_Mod1 e2.v mnm
Proof
  Cases_on `e1.v` \\ Cases_on `e2.v`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_Mod1_def, ALOOKUP_APPEND]
QED

Theorem nsLookup_Mod1_merge_none_c:
  nsLookup_Mod1 e1.c mnm = NONE /\ nsLookup_Mod1 e2.c mnm = NONE ==>
  nsLookup_Mod1 (merge_env e1 e2).c mnm = NONE
Proof
  Cases_on `e1.c` \\ Cases_on `e2.c`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_Mod1_def, ALOOKUP_APPEND]
QED

Theorem merge_left_mc:
  nsLookup_Mod1 e1.c mnm = r /\ nsLookup_Mod1 e2.c mnm = NONE ==>
  nsLookup_Mod1 (merge_env e1 e2).c mnm = r
Proof
  Cases_on `e1.c` \\ Cases_on `e2.c`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_Mod1_def, ALOOKUP_APPEND]
  \\ Cases_on `r` \\ fs []
QED

Theorem merge_right_mc:
  nsLookup_Mod1 e1.c mnm = NONE ==>
  nsLookup_Mod1 (merge_env e1 e2).c mnm = nsLookup_Mod1 e2.c mnm
Proof
  Cases_on `e1.c` \\ Cases_on `e2.c`
  \\ fs [merge_env_def, nsAppend_def, nsLookup_Mod1_def, ALOOKUP_APPEND]
QED

Theorem nsLookup_eq:
   nsLookup ns (Short nm) = nsLookup_Short ns nm /\
    nsLookup ns (Long mnm id) = (case nsLookup_Mod1 ns mnm of
      NONE => NONE | SOME ns2 => nsLookup ns2 id)
Proof
  fs [nsLookup_Short_def]
  \\ Cases_on `ns`
  \\ fs[nsLookup_Mod1_def, nsLookup_def]
QED

(* base facts about the partial functions *)

Theorem option_choice_f_apply:
   option_choice_f f g x = OPTION_CHOICE (f x) (g x)
Proof
  fs [option_choice_f_def]
QED

Theorem nsLookup_Short_Bind:
   nsLookup_Short (Bind ss ms) = ALOOKUP ss
Proof
  fs [nsLookup_Short_def, nsLookup_def, FUN_EQ_THM]
QED

Theorem nsLookup_Short_nsAppend:
   nsLookup_Short (nsAppend ns1 ns2)
    = option_choice_f (nsLookup_Short ns1) (nsLookup_Short ns2)
Proof
  Cases_on `ns1` \\ Cases_on `ns2`
  \\ fs [nsLookup_Short_Bind, nsAppend_def,
    alookup_append_option_choice_f]
QED

Theorem nsLookup_Mod1_Bind:
   nsLookup_Mod1 (Bind ss ms) nm = ALOOKUP ms nm
Proof
  fs [nsLookup_Mod1_def]
QED

Theorem nsLookup_Mod1_nsAppend:
   nsLookup_Mod1 (nsAppend ns1 ns2)
    = option_choice_f (nsLookup_Mod1 ns1) (nsLookup_Mod1 ns2)
Proof
  Cases_on `ns1` \\ Cases_on `ns2`
  \\ fs [nsLookup_Mod1_def, nsAppend_def,
    alookup_append_option_choice_f]
QED

Theorem nsLookup_Short_nsLift:
   nsLookup_Short (nsLift mnm ns) = ALOOKUP []
Proof
  Cases_on `ns` \\ fs [nsLift_def, nsLookup_Short_Bind]
QED

Theorem nsLookup_Mod1_nsLift:
   nsLookup_Mod1 (nsLift mnm ns) = ALOOKUP [(mnm, ns)]
Proof
  Cases_on `ns` \\ fs [nsLift_def, nsLookup_Mod1_def]
QED

Theorem nsLookup_pf_nsBind:
   nsLookup_Short (nsBind n v ns)
        = option_choice_f (ALOOKUP [(n, v)]) (nsLookup_Short ns) /\
  nsLookup_Mod1 (nsBind n v ns) = nsLookup_Mod1 ns
Proof
  Cases_on `ns`
  \\ fs [nsLookup_Short_def,nsLookup_Mod1_def, FUN_EQ_THM,
    write_def,nsLookup_def,nsBind_def,option_choice_f_def]
  \\ rpt strip_tac
  \\ fs [] \\ CASE_TAC \\ fs []
QED

(* equalities on these partial functions for the various env operators *)

Theorem nsLookup_write_eqs:
   nsLookup_Short ((write n v env).c) = nsLookup_Short env.c /\
    nsLookup_Mod1 ((write n v env).c) = nsLookup_Mod1 env.c /\
    nsLookup_Mod1 ((write n v env).v) = nsLookup_Mod1 env.v /\
    nsLookup_Short ((write n v env).v) = option_choice_f (ALOOKUP [(n, v)])
        (nsLookup_Short env.v)
Proof
  fs[write_def, nsLookup_pf_nsBind]
QED

Theorem nsLookup_write_cons_eqs:
   nsLookup_Short ((write_cons n v env).v) = nsLookup_Short env.v /\
    nsLookup_Mod1 ((write_cons n v env).v) = nsLookup_Mod1 env.v /\
    nsLookup_Mod1 ((write_cons n v env).c) = nsLookup_Mod1 env.c /\
    nsLookup_Short ((write_cons n v env).c) = option_choice_f (ALOOKUP [(n, v)])
        (nsLookup_Short env.c)
Proof
  fs[write_cons_def, nsLookup_pf_nsBind]
QED

Theorem nsLookup_merge_env_eqs:
   nsLookup_Short ((merge_env env env2).v)
        = option_choice_f (nsLookup_Short env.v) (nsLookup_Short env2.v) /\
    nsLookup_Mod1 ((merge_env env env2).v)
        = option_choice_f (nsLookup_Mod1 env.v) (nsLookup_Mod1 env2.v) /\
    nsLookup_Short ((merge_env env env2).c)
        = option_choice_f (nsLookup_Short env.c) (nsLookup_Short env2.c) /\
    nsLookup_Mod1 ((merge_env env env2).c)
        = option_choice_f (nsLookup_Mod1 env.c) (nsLookup_Mod1 env2.c)
Proof
  fs[merge_env_def, nsLookup_Short_nsAppend, nsLookup_Mod1_nsAppend]
QED

Theorem nsLookup_write_mod_eqs:
   nsLookup_Short ((write_mod mnm env env2).v) = nsLookup_Short env2.v /\
    nsLookup_Mod1 ((write_mod mnm env env2).v)
        = option_choice_f (ALOOKUP [(mnm, env.v)]) (nsLookup_Mod1 env2.v) /\
    nsLookup_Short ((write_mod mnm env env2).c) = nsLookup_Short env2.c /\
    nsLookup_Mod1 ((write_mod mnm env env2).c)
        = option_choice_f (ALOOKUP [(mnm, env.c)]) (nsLookup_Mod1 env2.c)
Proof
  fs[write_mod_def, nsLookup_Short_nsAppend, nsLookup_Mod1_nsAppend,
    nsLookup_Short_nsLift, nsLookup_Mod1_nsLift,
    alookup_empty_option_choice_f]
QED

Theorem nsLookup_empty_eqs:
   nsLookup_Short empty_env.v = ALOOKUP [] /\
    nsLookup_Mod1 empty_env.v = ALOOKUP [] /\
    nsLookup_Short empty_env.c = ALOOKUP [] /\
    nsLookup_Mod1 empty_env.c = ALOOKUP []
Proof
  fs[empty_env_def, nsEmpty_def, nsLookup_Short_Bind, nsLookup_Mod1_def]
QED

(* nonsense theorem instantiated when env's are defined *)

Theorem nsLookup_eq_format:
   !env:v sem_env.
     (nsLookup_Short env.v = nsLookup_Short env.v) /\
     (nsLookup_Short env.c = nsLookup_Short env.c) /\
     (nsLookup_Mod1 env.v = nsLookup_Mod1 env.v) /\
     (nsLookup_Mod1 env.c = nsLookup_Mod1 env.c)
Proof
  rewrite_tac []
QED

(* some shorthands that are allowed to EVAL are below *)

Definition write_rec_def:
  write_rec funs env1 env =
    FOLDR (\f env. write (FST f) (Recclosure env1 funs (FST f)) env) env funs
End

Theorem write_rec_thm:
   write_rec funs env1 env =
    env with v := build_rec_env funs env1 env.v
Proof
  fs [write_rec_def,build_rec_env_def]
  \\ qspec_tac (`Recclosure env1 funs`,`hh`)
  \\ qspec_tac (`env`,`env`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
  \\ fs [write_def]
QED

Definition write_conses_def:
  write_conses [] env = env /\
  write_conses ((n,y)::xs) env =
    write_cons n y (write_conses xs env)
End

Definition write_tdefs_def:
  write_tdefs n [] env = env /\
  write_tdefs n ((x,_,condefs)::tds) env =
    write_tdefs (n+1) tds (write_conses (REVERSE (build_constrs n condefs)) env)
End

Theorem write_conses_v[local]:
    !xs env. (write_conses xs env).v = env.v
Proof
  Induct \\ fs [write_conses_def,FORALL_PROD,write_cons_def]
QED

Theorem write_tdefs_lemma[local]:
    !tds env n.
      write_tdefs n tds env =
      merge_env <|v := nsEmpty; c := build_tdefs n tds|> env
Proof
  Induct \\ fs [write_tdefs_def,merge_env_def,build_tdefs_def,FORALL_PROD]
  \\ rw [write_conses_v]
  \\ rewrite_tac [GSYM namespacePropsTheory.nsAppend_assoc]
  \\ AP_TERM_TAC
  \\ Q.SPEC_TAC (`REVERSE (build_constrs n p_2)`,`xs`)
  \\ Induct \\ fs [write_conses_def,FORALL_PROD,write_cons_def]
QED

Theorem write_tdefs_thm:
   write_tdefs n tds empty_env =
    <|v := nsEmpty; c := build_tdefs n tds|>
Proof
  fs [write_tdefs_lemma,empty_env_def,merge_env_def]
QED

Theorem merge_env_write_conses[local]:
    !xs env. merge_env (write_conses xs env1) env2 =
             write_conses xs (merge_env env1 env2)
Proof
  Induct \\ fs [write_conses_def,FORALL_PROD]
  \\ fs [write_cons_def,merge_env_def,sem_env_component_equality]
QED

Theorem merge_env_write_tdefs[local]:
    !tds n env1 env2.
      merge_env (write_tdefs n tds env1) env2 =
      write_tdefs n tds (merge_env env1 env2)
Proof
  Induct \\ fs [write_tdefs_def,FORALL_PROD,merge_env_write_conses]
QED

(* it's not clear if these are still needed, but ml_progComputeLib and
   cfTacticsLib want them to be present. *)

Theorem nsLookup_nsAppend_Short[compute]:
    (nsLookup (nsAppend e1 e2) (Short id) =
    case nsLookup e1 (Short id) of
      NONE =>
        nsLookup e2 (Short id)
    | SOME v => SOME v)
Proof
  every_case_tac>>
  Cases_on`nsLookup e2(Short id)`>>
  fs[namespacePropsTheory.nsLookup_nsAppend_some,
     namespacePropsTheory.nsLookup_nsAppend_none,id_to_mods_def]
QED

Theorem write_simp[compute]:
   (write n v env).c = env.c /\
    nsLookup (write n v env).v (Short q) =
      if n = q then SOME v else nsLookup env.v (Short q)
Proof
  IF_CASES_TAC>>fs[write_def,namespacePropsTheory.nsLookup_nsBind]
QED

Theorem write_cons_simp[compute]:
   (write_cons n v env).v = env.v /\
    nsLookup (write_cons n v env).c (Short q) =
      if n = q then SOME v else nsLookup env.c (Short q)
Proof
  IF_CASES_TAC>>fs[write_cons_def,namespacePropsTheory.nsLookup_nsBind]
QED

Theorem write_mod_simp[compute]:
   (nsLookup (write_mod mn env env2).v (Short q) =
    nsLookup env2.v (Short q)) ∧
   (nsLookup (write_mod mn env env2).c (Short c) =
    nsLookup env2.c (Short c)) ∧
   (nsLookup (write_mod mn env env2).v (Long mn' r) =
    if mn = mn' then nsLookup env.v r
    else nsLookup env2.v (Long mn' r)) ∧
   (nsLookup (write_mod mn env env2).c (Long mn' s) =
    if mn = mn' then nsLookup env.c s
    else nsLookup env2.c (Long mn' s))
Proof
  rw[write_mod_def]
QED

Theorem empty_simp[compute]:
   nsLookup empty_env.v q = NONE /\
   nsLookup empty_env.c q = NONE
Proof
  fs [empty_env_def]
QED
(* the components of nsLookup are 'nicer' partial functions *)

(* --- declarations --- *)

Definition Decls_def:
  Decls env s1 ds env2 s2 <=>
    s1.clock = s2.clock /\
    ?ck1 ck2. evaluate_dec_list (s1 with clock := ck1) env ds =
                                (s2 with clock := ck2, Rval env2)
End

Definition Prog_def:
  Prog env s1 ds env2 s2 <=>
    s1.clock = s2.clock /\
    ?ck1 ck2. evaluate_decs (s1 with clock := ck1) env ds =
                            (s2 with clock := ck2, Rval env2)
End

Theorem Decls_Dtype:
   !env s tds env2 s2 locs.
      Decls env s [Dtype locs tds] env2 s2 <=>
      EVERY check_dup_ctors tds /\
      s2 = s with <| next_type_stamp := (s.next_type_stamp + LENGTH tds) |> /\
      env2 = write_tdefs s.next_type_stamp tds empty_env
Proof
  SIMP_TAC std_ss [Decls_def,evaluate_dec_list_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,write_tdefs_thm]
QED

Theorem Decls_Dexn:
   !env s n l env2 s2 locs.
      Decls env s [Dexn locs n l] env2 s2 <=>
      s2 = s with <| next_exn_stamp := (s.next_exn_stamp + 1) |> /\
      env2 = write_cons n (LENGTH l, ExnStamp s.next_exn_stamp) empty_env
Proof
  SIMP_TAC std_ss [Decls_def,evaluate_dec_list_def,write_cons_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,write_tdefs_thm]
  \\ fs [nsBind_def,nsEmpty_def,nsSing_def,empty_env_def]
QED

Theorem Decls_Dtabbrev:
   !env s x y z env2 s2 locs.
      Decls env s [Dtabbrev locs x y z] env2 s2 <=>
      s2 = s ∧ env2 = empty_env
Proof
  fs [Decls_def,evaluate_dec_list_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  \\ rveq \\ fs [state_component_equality,empty_env_def]
QED

Definition eval_rel_def:
  eval_rel s1 env e s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate (s1 with clock := ck1) env [e] =
                (s2 with clock := ck2,Rval [x])
End

Theorem eval_rel_alt:
   eval_rel s1 env e s2 x <=>
    s2.clock = s1.clock ∧
    ∃ck. evaluate (s1 with clock := ck) env [e] = (s2,Rval [x])
Proof
  reverse eq_tac \\ rw [] \\ fs [eval_rel_def]
  THEN1 (qexists_tac `ck` \\ fs [state_component_equality])
  \\ drule evaluatePropsTheory.evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `s2.clock` strip_assume_tac)
  \\ rename [`evaluate (s1 with clock := ck) env [e]`]
  \\ qexists_tac `ck` \\ fs [state_component_equality]
QED

Definition eval_list_rel_def:
  eval_list_rel s1 env e s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate (s1 with clock := ck1) env e =
                (s2 with clock := ck2,Rval x)
End

Definition eval_match_rel_def:
  eval_match_rel s1 env v pats err_v s2 x <=>
    s1.clock = s2.clock /\
    ?ck1 ck2.
       evaluate_match
                (s1 with clock := ck1) env v pats err_v =
                (s2 with clock := ck2,Rval [x])
End

(* Delays the write *)
Theorem Decls_Dlet:
   !env s1 v e s2 env2 locs.
      Decls env s1 [Dlet locs (Pvar v) e] env2 s2 <=>
      ?x. eval_rel s1 env e s2 x /\ (env2 = write v x empty_env)
Proof
  simp [Decls_def,evaluate_dec_list_def,eval_rel_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [bool_case_eq]
  THEN1
   (FULL_CASE_TAC
    \\ Cases_on `r` \\ fs [pat_bindings_def,ALL_DISTINCT,MEM,
         pmatch_def,combine_dec_result_def] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq
    \\ fs [write_def,empty_env_def] \\ asm_exists_tac \\ fs [])
  \\ fs [pat_bindings_def,ALL_DISTINCT,MEM,
         pmatch_def,combine_dec_result_def]
  \\ qexists_tac `ck1` \\ qexists_tac `ck2`
  \\ fs [write_def,empty_env_def]
QED

Theorem FOLDR_LEMMA[local]:
  ∀xs ys. FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) [] xs ++ ys =
          FOLDR (\(x1,x2,x3) x4. (x1, f x1 x2 x3) :: x4) ys xs
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) [FORALL_PROD]
QED

(* Delays the write in build_rec_env *)
Theorem Decls_Dletrec:
   ∀env s1 funs s2 env2 locs.
      Decls env s1 [Dletrec locs funs] env2 s2 <=>
      (s2 = s1) /\
      ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
      (env2 = write_rec funs env empty_env)
Proof
  simp [Decls_def,evaluate_dec_list_def,bool_case_eq,PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ fs [state_component_equality,write_rec_def]
  \\ fs[write_def,write_rec_thm,empty_env_def,build_rec_env_def]
  \\ rpt (pop_assum kall_tac)
  \\ qspec_tac (`Recclosure env funs`,`xx`)
  \\ qspec_tac (`nsEmpty:env_val`,`nn`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
  \\ pop_assum (assume_tac o GSYM) \\ fs []
QED

Theorem Decls_Dmod:
   Decls env1 s1 [Dmod mn ds] env2 s2 <=>
   ?s env.
      Decls env1 s1 ds env s /\ s2 = s /\
      env2 = write_mod mn env empty_env
Proof
  fs [Decls_def,Decls_def,evaluate_dec_list_def,PULL_EXISTS,
      combine_dec_result_def,write_mod_def,empty_env_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ fs [pair_case_eq,result_case_eq]
  \\ rveq \\ fs [] \\ asm_exists_tac \\ fs []
QED

Theorem Decls_Dlocal:
   Decls env st lds env2 st2
    ==> Decls (merge_env env2 env) st2 ds env3 st3
    ==> Decls env st [Dlocal lds ds] env3 st3
Proof
  fs [Decls_def,evaluate_dec_list_def,extend_dec_env_def,merge_env_def]
  \\ rw [pair_case_eq, result_case_eq]
  \\ imp_res_tac evaluate_dec_list_set_clock
  \\ fs [] \\ metis_tac []
QED

Theorem Decls_Denv:
  ∀env s1 v s2 env2.
    Decls env s1 [Denv v] env2 s2 ⇔
    ∃env1 es.
      declare_env s1.eval_state env = SOME (env1, es) ∧
      s2 = s1 with eval_state := es ∧
      env2 = write v env1 empty_env
Proof
  rw[Decls_def, evaluate_dec_list_def]
  \\ TOP_CASE_TAC
  \\ PairCases_on`x`
  \\ simp[write_def,empty_env_def,state_component_equality]
  \\ rw[nsEmpty_def, nsSing_def, nsBind_def]
  \\ rw[EQ_IMP_THM]
QED

Theorem Decls_NIL:
   !env s n l env2 s2.
      Decls env s [] env2 s2 <=>
      s2 = s ∧ env2 = empty_env
Proof
  fs [Decls_def,evaluate_dec_list_def,state_component_equality,empty_env_def]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem Decls_CONS:
   !s1 s3 env1 d ds1 ds2 env3.
      Decls env1 s1 (d::ds2) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 [d] envA s2 /\
         Decls (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA
Proof
  rw[Decls_def,PULL_EXISTS,evaluate_dec_list_def]
  \\ reverse (rw[EQ_IMP_THM]) \\ fs []
  THEN1
   (once_rewrite_tac [evaluate_dec_list_cons]
    \\ imp_res_tac evaluate_dec_list_add_to_clock \\ fs []
    \\ first_x_assum (qspec_then `ck1'` assume_tac)
    \\ qexists_tac `ck1+ck1'` \\ fs []
    \\ fs [merge_env_def,extend_dec_env_def,combine_dec_result_def]
    \\ fs [state_component_equality])
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [evaluate_dec_list_cons]
  \\ fs [pair_case_eq,result_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
  \\ gvs [evaluate_dec_list_def]
  \\ Cases_on `r` \\ fs [combine_dec_result_def]
  \\ rveq \\ fs []
  \\ qexists_tac `env1'` \\ fs []
  \\ qexists_tac `a` \\ fs []
  \\ qexists_tac `s1' with clock := s3.clock` \\ fs [merge_env_def]
  \\ qexists_tac `ck1` \\ fs [state_component_equality]
  \\ qexists_tac `s1'.clock` \\ fs [state_component_equality]
  \\ `(s1' with clock := s1'.clock) = s1'` by fs [state_component_equality]
  \\ fs [extend_dec_env_def]
  \\ fs [state_component_equality]
QED

Theorem merge_env_empty_env:
   merge_env env empty_env = env /\
   merge_env empty_env env = env
Proof
  rw [merge_env_def,empty_env_def]
QED

Theorem merge_env_assoc:
   merge_env env1 (merge_env env2 env3) = merge_env (merge_env env1 env2) env3
Proof
  fs [merge_env_def]
QED

Theorem Decls_APPEND:
   !s1 s3 env1 ds1 ds2 env3.
      Decls env1 s1 (ds1 ++ ds2) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 ds1 envA s2 /\
         Decls (merge_env envA env1) s2 ds2 envB s3 /\
         env3 = merge_env envB envA
Proof
  Induct_on `ds1` \\ fs [APPEND,Decls_NIL,merge_env_empty_env]
  \\ once_rewrite_tac [Decls_CONS]
  \\ fs [PULL_EXISTS,merge_env_assoc] \\ metis_tac []
QED

Theorem Decls_SNOC:
   !s1 s3 env1 ds1 d env3.
      Decls env1 s1 (SNOC d ds1) env3 s3 =
      ?envA envB s2.
         Decls env1 s1 ds1 envA s2 /\
         Decls (merge_env envA env1) s2 [d] envB s3 /\
         env3 = merge_env envB envA
Proof
  METIS_TAC [SNOC_APPEND, Decls_APPEND]
QED

Theorem Decls_set_eval_state:
  Decls env1 s1 ds env2 s2 ∧ s1.eval_state = NONE ⇒
  ∀es.
    Decls env1 (s1 with eval_state := es) ds env2
               (s2 with eval_state := es)
Proof
  rw [Decls_def]
  \\ drule_then (qspec_then ‘es’ assume_tac) eval_dec_list_no_eval_simulation
  \\ gvs []
  \\ pop_assum $ irule_at Any
QED

(* The translator and CF tools use the following definition of ML_code
   to build (and verify) an ML program within the logic. The goal is to
   prove 'Decls' of the completed list of declarations. The program is
   constructed one statement at a time, with facts about the resulting
   environment built over time. There is a list of currently open blocks
   (e.g. struct and local constructs) so that the contents of modules and
   local objects can also be built up one statement at a time.
*)

Definition ML_code_env_def:
  (ML_code_env env [] = env) ∧
  (ML_code_env env ((comm, st, decls, res_env) :: bls)
        = merge_env res_env (ML_code_env env bls))
End

Definition ML_code_def:
  (ML_code env [] res_st <=> T) ∧
  (ML_code env (((comment : mlstring # mlstring), st, decls, res_env) :: bls) res_st <=>
     ML_code env bls st ∧
     Decls (ML_code_env env bls) st decls res_env res_st)
End

(* retreive the Decls from a toplevel ML_code *)
Theorem ML_code_Decls:
  ML_code env1 [(comm, st1, prog, env2)] st2 ==>
    Decls env1 st1 prog env2 st2
Proof
  fs [ML_code_def, ML_code_env_def]
QED

(* an empty program *)
local open primSemEnvTheory in

local
  val init_env_tm =
    ``SND (THE (prim_sem_env (ARB:unit ffi_state)))``
    |> (SIMP_CONV std_ss [primSemEnvTheory.prim_sem_env_eq] THENC EVAL)
    |> concl |> rand
  val init_state_tm =
    ``FST(THE (prim_sem_env (ffi:'ffi ffi_state)))``
    |> (SIMP_CONV std_ss [primSemEnvTheory.prim_sem_env_eq] THENC EVAL)
    |> concl |> rand
in
  (* init_env_def should not be unpacked by EVAL. Queries will be handled
     by the nsLookup_conv apparatus, which will use the pfun_eqs thm below. *)
Definition init_env_def[nocompute]:
  init_env = ^init_env_tm
End

Definition init_state_def:
  init_state ffi = ^init_state_tm
End
end

Theorem init_state_env_thm:
   THE (prim_sem_env ffi) = (init_state ffi,init_env)
Proof
  rewrite_tac[prim_sem_env_eq,THE_DEF,init_state_def,init_env_def]
QED

Theorem nsLookup_init_env_pfun_eqs =
  [``nsLookup_Short init_env.c``, ``nsLookup_Short init_env.v``,
    ``nsLookup_Mod1 init_env.c``, ``nsLookup_Mod1 init_env.v``]
  |> map (SIMP_CONV bool_ss
        [init_env_def, nsLookup_Short_Bind, nsLookup_Mod1_def,
            namespace_case_def, sem_env_accfupds, K_DEF])
  |> LIST_CONJ;

(* The balanced env_tree for init_env: 8 leaves, one per built-in
   constructor, keys sorted by (mlstring_lt).  Built as 15 named
   Definitions (init_env_1 .. init_env_15) with per-node env_wf
   theorems, via SML helpers.  init_env_15 is the root. *)
local
  val env_tree_ty = ``:env_tree``
  val env_leaf_tm = prim_mk_const {Thy = "ml_prog", Name = "EnvLeaf"}
  val env_branch_tm = prim_mk_const {Thy = "ml_prog", Name = "EnvBranch"}
  val env_wf_tm = prim_mk_const {Thy = "ml_prog", Name = "env_wf"}
  val empty_entry_tm = prim_mk_const {Thy = "ml_prog", Name = "empty_entry"}
  val env_entry_sc_fupd =
      prim_mk_const {Thy = "ml_prog",
                     Name = "recordtype.env_entry.seldef.sc_fupd"}
  val mlstring_lt_tm =
      prim_mk_const {Thy = "mlstring", Name = "mlstring_lt"}
  fun mk_sc_entry stamp_tm = let
    val some_tm = optionSyntax.mk_some stamp_tm
    val k_tm = combinSyntax.mk_K_1 (some_tm, type_of some_tm)
  in list_mk_icomb (env_entry_sc_fupd, [k_tm, empty_entry_tm]) end
  val all_defs : thm list ref = ref []
  val counter = ref 0
  fun next_name () = (counter := !counter + 1;
                      "init_env_" ^ Int.toString (!counter))
  fun wf_bounds wf = let
    val args = wf |> concl |> strip_comb |> snd
  in (List.nth (args, 1), List.nth (args, 2)) end
  fun mk_leaf key stamp_tm = let
    val nm = next_name ()
    val key_tm = mlstringSyntax.mk_mlstring key
    val entry_tm = mk_sc_entry stamp_tm
    val tree_tm = list_mk_icomb (env_leaf_tm, [key_tm, entry_tm])
    val def = new_definition (nm ^ "_def",
                mk_eq (mk_var (nm, env_tree_ty), tree_tm))
    val const_tm = def |> concl |> lhs
    val wf_goal = list_mk_icomb (env_wf_tm, [const_tm, key_tm, key_tm])
    val wf = prove (wf_goal, simp [def, env_wf_def])
    val _ = save_thm (nm ^ "_wf", wf)
    val _ = all_defs := def :: !all_defs
  in wf end
  fun mk_branch wfL wfR = let
    val nm = next_name ()
    val constL = wfL |> concl |> strip_comb |> snd |> hd
    val constR = wfR |> concl |> strip_comb |> snd |> hd
    val tree_tm = list_mk_icomb (env_branch_tm, [constL, constR])
    val def = new_definition (nm ^ "_def",
                mk_eq (mk_var (nm, env_tree_ty), tree_tm))
    val (k1L, kL) = wf_bounds wfL
    val (kR, k2R) = wf_bounds wfR
    val lt_thm = EQT_ELIM (EVAL (list_mk_icomb (mlstring_lt_tm, [kL, kR])))
    val wf_inline =
        MATCH_MP env_wf_branch_intro (LIST_CONJ [wfL, wfR, lt_thm])
    val wf = ONCE_REWRITE_RULE [SYM def] wf_inline
    val _ = save_thm (nm ^ "_wf", wf)
    val _ = all_defs := def :: !all_defs
  in wf end
in
  val envt1  = mk_leaf "::"        ``(2n, TypeStamp (strlit "::") 1n)``
  val envt2  = mk_leaf "Bind"      ``(0n, ExnStamp 0n)``
  val envt3  = mk_leaf "Chr"       ``(0n, ExnStamp 1n)``
  val envt4  = mk_leaf "Div"       ``(0n, ExnStamp 2n)``
  val envt5  = mk_leaf "False"     ``(0n, TypeStamp (strlit "False") 0n)``
  val envt6  = mk_leaf "Subscript" ``(0n, ExnStamp 3n)``
  val envt7  = mk_leaf "True"      ``(0n, TypeStamp (strlit "True") 0n)``
  val envt8  = mk_leaf "[]"        ``(0n, TypeStamp (strlit "[]") 1n)``
  val envt9  = mk_branch envt1 envt2
  val envt10 = mk_branch envt3 envt4
  val envt11 = mk_branch envt5 envt6
  val envt12 = mk_branch envt7 envt8
  val envt13 = mk_branch envt9  envt10
  val envt14 = mk_branch envt11 envt12
  val envt15 = mk_branch envt13 envt14
  val init_env_all_defs = List.rev (!all_defs)
end

Theorem nsLookup_all_init_env:
  nsLookup_all init_env = tree_lookup init_env_15
Proof
  rw ([FUN_EQ_THM, nsLookup_all_def, init_env_def,
       tree_lookup_def, nsLookup_def, nsLookup_Mod1_def, empty_entry_def]
      @ init_env_all_defs)
  \\ EVAL_TAC \\ rw []
QED

end

Theorem ML_code_NIL:
   ML_code init_env [((«Toplevel», «»), init_state ffi, [], empty_env)]
    (init_state ffi)
Proof
  fs [ML_code_def,Decls_NIL]
QED

(* opening and closing of modules *)

Theorem ML_code_new_block:
   !comm2. ML_code inp_env ((comm, st, decls, env) :: bls) st2 ==>
    let env2 = ML_code_env inp_env ((comm, st, decls, env) :: bls) in
    ML_code inp_env ((comm2, st2, [], empty_env)
        :: (comm, st, decls, env) :: bls) st2
Proof
  fs [ML_code_def] \\ rw [Decls_NIL] \\ EVAL_TAC
QED

Theorem ML_code_close_module:
   ML_code inp_env (((«Module», mn), m_i_st, m_decls, m_env)
        :: (comm, st, decls, env) :: bls) st2
    ==> let env2 = write_mod mn m_env env
        in ML_code inp_env ((comm, st, SNOC (Dmod mn m_decls) decls,
            env2) :: bls) st2
Proof
  rw [ML_code_def, ML_code_env_def]
  \\ fs [SNOC_APPEND,Decls_APPEND]
  \\ asm_exists_tac \\ fs [Decls_Dmod,PULL_EXISTS]
  \\ asm_exists_tac
  \\ fs [write_mod_def,merge_env_def,empty_env_def]
QED

Theorem ML_code_close_local:
   ML_code inp_env (((«Local», ln2), l2_i_st, l2_decls, l2_env)
        :: ((«Local», ln1), l1_i_st, l1_decls, l1_env)
        :: (comm, st, decls, env) :: bls) st2
    ==> let env2 = merge_env l2_env env
        in ML_code inp_env ((comm, st, SNOC (Dlocal l1_decls l2_decls) decls,
            env2) :: bls) st2
Proof
  rw [ML_code_def, ML_code_env_def]
  \\ fs [SNOC_APPEND,Decls_APPEND] \\ metis_tac [Decls_Dlocal]
QED

(* appending a Dtype *)

Theorem ML_code_Dtype:
   !tds locs. ML_code inp_env ((comm, s1, prog, env2) :: bls) s2 ==>
     EVERY check_dup_ctors tds ==>
     let nts = s2.next_type_stamp in
     let s3 = (s2 with next_type_stamp := nts + LENGTH tds) in
     let env3 = write_tdefs nts tds env2 in
     ML_code inp_env ((comm, s1, SNOC (Dtype locs tds) prog, env3) :: bls) s3
Proof
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dtype,merge_env_empty_env]
  \\ rw [] \\ rpt (asm_exists_tac \\ fs [])
  \\ fs [merge_env_write_tdefs] \\ AP_TERM_TAC
  \\ fs [merge_env_def,empty_env_def,sem_env_component_equality]
QED

(* appending a Dexn *)

Theorem ML_code_Dexn:
   !n l locs. ML_code inp_env ((comm, s1, prog, env2) :: bls) s2 ==>
     let nes = s2.next_exn_stamp in
     let s3 = s2 with next_exn_stamp := nes + 1 in
     let env3 = write_cons n (LENGTH l,ExnStamp nes) env2 in
     ML_code inp_env ((comm, s1, SNOC (Dexn locs n l) prog, env3) :: bls) s3
Proof
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dexn,merge_env_empty_env]
  \\ rw [] \\ rpt (asm_exists_tac \\ fs [])
  \\ fs [write_cons_def,merge_env_def,empty_env_def,sem_env_component_equality]
QED

(* appending a Dtabbrev *)

Theorem ML_code_Dtabbrev:
   !x y z locs. ML_code inp_env ((comm, s1, prog, env2) :: bls) s2 ==>
     ML_code inp_env ((comm, s1, SNOC (Dtabbrev locs x y z) prog, env2) :: bls)
       s2
Proof
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dtabbrev,merge_env_empty_env]
QED

(* appending a Letrec *)

Theorem build_rec_env_APPEND[local]:
  nsAppend (build_rec_env funs cl_env nsEmpty) add_to_env =
   build_rec_env funs cl_env add_to_env
Proof
  fs [build_rec_env_def] \\ qspec_tac (`Recclosure cl_env funs`,`xxx`)
  \\ qspec_tac (`add_to_env`,`xs`)
  \\ Induct_on `funs` \\ fs [FORALL_PROD]
QED

Theorem ML_code_Dletrec:
   !fns locs. ML_code env0 ((comm, s1, prog, env2) :: bls) s2 ==>
      ALL_DISTINCT (MAP (λ(x,y,z). x) fns) ==>
      let code_env = ML_code_env env0 ((comm, s1, prog, env2) :: bls) in
      let env3 = write_rec fns code_env env2 in
      ML_code env0 ((comm, s1, SNOC (Dletrec locs fns) prog, env3) :: bls) s2
Proof
  fs [ML_code_def,SNOC_APPEND,Decls_APPEND,Decls_Dletrec,ML_code_env_def]
  \\ rw [] \\ asm_exists_tac
  \\ fs [merge_env_def,write_rec_thm,empty_env_def,sem_env_component_equality]
  \\ fs [build_rec_env_APPEND]
QED

(* appending a Let *)

Theorem ML_code_Dlet_var:
  ∀cenv e s3 x n locs. ML_code env0 ((comm, s1, prog, env1) :: bls) s2 ==>
    eval_rel s2 cenv e s3 x ==>
    cenv = ML_code_env env0 ((comm, s1, prog, env1) :: bls) ==>
    let env2 = write n x env1 in let s3_abbrev = s3 in
    ML_code env0 ((comm, s1, SNOC (Dlet locs (Pvar n) e) prog, env2)
        :: bls) s3_abbrev
Proof
  fs [ML_code_def,ML_code_env_def,SNOC_APPEND,Decls_APPEND,Decls_Dlet]
  \\ rw [] \\ asm_exists_tac \\ fs [PULL_EXISTS]
  \\ fs [write_def,merge_env_def,empty_env_def,sem_env_component_equality]
QED

Theorem ML_code_Dlet_var_lit:
  ∀loc name l. ML_code env0 ((comm, s1, prog, env1)::bls) s2 ⇒
    let env2 = write name (Litv l) env1 in let s3_abbrev = s2 in
      ML_code env0 ((comm,s1,SNOC (Dlet loc (Pvar name) (Lit l)) prog,env2)::bls) s3_abbrev
Proof
  rpt strip_tac
  \\ irule ML_code_Dlet_var \\ fs []
  \\ pop_assum $ irule_at Any
  \\ fs [eval_rel_def,evaluateTheory.evaluate_def]
  \\ fs [semanticPrimitivesTheory.state_component_equality]
QED

Theorem ML_code_Dlet_Fun:
  ∀n v e locs. ML_code env0 ((comm, s1, prog, env1) :: bls) s2 ==>
    let code_env = ML_code_env env0 ((comm, s1, prog, env1) :: bls) in
    let v_abbrev = Closure code_env v e in
    let env2 = write n v_abbrev env1 in
    ML_code env0 ((comm, s1, SNOC (Dlet locs (Pvar n) (Fun v e)) prog,
        env2) :: bls) s2
Proof
  rw [] \\ imp_res_tac ML_code_Dlet_var
  \\ fs [evaluate_def,state_component_equality,eval_rel_def]
QED

Theorem ML_code_Dlet_Var_Var:
  ∀n vname locs. ML_code env0 ((comm, s1, prog, env1) :: bls) s2 ==>
    let cenv = ML_code_env env0 ((comm, s1, prog, env1) :: bls) in
    ∀x. nsLookup cenv.v vname = SOME x ==>
    let env2 = write n x env1 in
    ML_code env0 ((comm, s1, SNOC (Dlet locs (Pvar n) (Var vname)) prog, env2)
        :: bls) s2
Proof
  rw []
  \\ irule (SIMP_RULE std_ss [LET_THM] ML_code_Dlet_var) \\ fs []
  \\ first_x_assum $ irule_at $ Pos hd
  \\ fs [eval_rel_def,evaluate_def,state_component_equality]
QED

Theorem ML_code_Dlet_Var_Ref_Var:
  ∀n vname locs. ML_code env0 ((comm, s1, prog, env1) :: bls) s2 ==>
    let cenv = ML_code_env env0 ((comm, s1, prog, env1) :: bls) in
    ∀x. nsLookup cenv.v vname = SOME x ==>
    let len = LENGTH s2.refs in
    let loc = Loc T len in
    let env2 = write n loc env1 in
    let s2_abbrev = s2 with refs := s2.refs ++ [Refv x] in
    ML_code env0 ((comm, s1, SNOC (Dlet locs (Pvar n) (App Opref [Var vname])) prog, env2)
        :: bls) s2_abbrev
Proof
  rw []
  \\ irule (SIMP_RULE std_ss [LET_THM] ML_code_Dlet_var) \\ fs []
  \\ first_x_assum $ irule_at $ Pos hd
  \\ fs [eval_rel_def,evaluate_def,state_component_equality,AllCaseEqs(),
         do_app_def,store_alloc_def, getOpClass_def]
QED

(* appending an environment *)

Definition declare_env_rel_def:
  declare_env_rel s2 env1 s3 envv ⇔
  ∃es.
    declare_env s2.eval_state env1 = SOME (envv, es) ∧
    s3 = s2 with eval_state := es
End

Theorem ML_code_Denv:
  ∀n cenv s3 envv.
    ML_code env0 ((comm,s1,prog,env1)::bls) s2 ⇒
    declare_env_rel s2 cenv s3 envv ⇒
    cenv = ML_code_env env0 ((comm,s1,prog,env1)::bls) ⇒
    let
      env2 = write n envv env1;
      s3_abbrev = s3
    in
    ML_code env0 ((comm,s1,SNOC (Denv n) prog,env2)::bls) s3_abbrev
Proof
  rw[ML_code_def, SNOC_APPEND, Decls_APPEND, Decls_Denv,
     declare_env_rel_def, ML_code_env_def]
  \\ first_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ rw[write_def, merge_env_def, empty_env_def,
        sem_env_component_equality]
QED

(* setting the eval_state *)

Theorem ML_code_set_eval_state: (* only supported at the top-level for simplicity *)
  ML_code env0 [(comm,s1,prog,env1)] s2 ⇒
  s1.eval_state = NONE ⇒
  ∀es. ML_code env0 [(comm,s1 with eval_state := SOME es,prog,env1)]
                          (s2 with eval_state := SOME es)
Proof
  rw [ML_code_def]
  \\ drule_all Decls_set_eval_state
  \\ fs []
QED

(* lookup function definitions *)

Definition lookup_var_def:
  lookup_var name (env:v sem_env) = nsLookup env.v (Short name)
End

Definition lookup_cons_def:
  lookup_cons name (env:v sem_env) = nsLookup env.c name
End

(* the old lookup formulation worked via nsLookup/mod_defined,
   and mod_defined is still used in various characteristic scripts
   so we supply an eval theorem that maps to the new approach. *)

Definition mod_defined_def[nocompute]:
  mod_defined env n =
    ∃p1 p2 e3.
      p1 ≠ [] ∧ id_to_mods n = p1 ++ p2 ∧
      nsLookupMod env p1 = SOME e3
End

Theorem mod_defined_nsLookup_Mod1[compute]:
   mod_defined env id = (case id of Short _ => F
        | Long mn _ => (case nsLookup_Mod1 env mn of NONE => F | _ => T))
Proof
  PURE_CASE_TAC \\ fs [id_to_mods_def, mod_defined_def]
    \\ Cases_on `env`
    \\ fs [Once EXISTS_LIST, nsLookupMod_def, nsLookup_Mod1_def]
    \\ PURE_CASE_TAC \\ fs [Once EXISTS_LIST, nsLookupMod_def]
QED

(* theorems about old lookup functions *)
(* FIXME: everything below this line is unlikely to be needed. *)

Theorem nsLookupMod_nsBind[local]:
  p ≠ [] ⇒
  nsLookupMod (nsBind k v env) p = nsLookupMod env p
Proof
  Cases_on`env`>>fs[nsBind_def]>> Induct_on`p`>>
  fs[nsLookupMod_def]
QED

Theorem nsLookup_write:
   (nsLookup (write n v env).v (Short name) =
       if n = name then SOME v else nsLookup env.v (Short name)) /\
   (nsLookup (write n v env).v (Long mn lname)  =
       nsLookup env.v (Long mn lname)) /\
   (nsLookup (write n v env).c a = nsLookup env.c a) /\
   (mod_defined (write n v env).v x = mod_defined env.v x) /\
   (mod_defined (write n v env).c x = mod_defined env.c x)
Proof
  fs [write_def] \\ rw []
  \\ metis_tac[nsLookupMod_nsBind,mod_defined_def]
QED

Theorem nsLookup_write_cons:
   (nsLookup (write_cons n v env).v a = nsLookup env.v a) /\
   (nsLookup (write_cons n d env).c (Short name) =
     if name = n then SOME d else nsLookup env.c (Short name)) /\
   (mod_defined (write_cons n d env).v x = mod_defined env.v x) /\
   (mod_defined (write_cons n d env).c x = mod_defined env.c x) /\
   (nsLookup (write_cons n d env).c (Long mn lname) =
    nsLookup env.c (Long mn lname))
Proof
  fs [write_cons_def] \\ rw [] \\
  metis_tac[nsLookupMod_nsBind,mod_defined_def]
QED

Theorem nsLookup_empty:
   (nsLookup empty_env.v a = NONE) /\
   (nsLookup empty_env.c b = NONE) /\
   (mod_defined empty_env.v x = F) /\
   (mod_defined empty_env.c x = F)
Proof
  rw[empty_env_def, nsLookup_def, mod_defined_def,
    nsLookupMod_def] \\ Cases_on`p1` \\ fs[]
QED

val nsLookupMod_nsAppend = Q.prove(`
  nsLookupMod (nsAppend env1 env2) p =
  if p = [] then SOME (nsAppend env1 env2)
  else
    case nsLookupMod env1 p of
      SOME v => SOME v
    | NONE =>
      if (∃p1 p2 e3. p1 ≠ [] ∧ p = p1 ++ p2 ∧ nsLookupMod env1 p1 = SOME e3) then NONE
      else nsLookupMod env2 p`,
  IF_CASES_TAC>-
    fs[nsLookupMod_def]>>
  BasicProvers.TOP_CASE_TAC>>
  rw[]>>
  TRY(Cases_on`nsLookupMod env2 p`)>>
  fs[namespacePropsTheory.nsLookupMod_nsAppend_none,namespacePropsTheory.nsLookupMod_nsAppend_some]>>
  metis_tac[option_CLAUSES]) |> GEN_ALL;

Theorem nsLookup_write_mod:
   (nsLookup (write_mod mn env1 env2).v (Short n) =
    nsLookup env2.v (Short n)) /\
   (nsLookup (write_mod mn env1 env2).c (Short n) =
    nsLookup env2.c (Short n)) /\
   (mod_defined (write_mod mn env1 env2).v (Long mn' r) =
     ((mn = mn') \/ mod_defined env2.v (Long mn' r))) /\
   (mod_defined (write_mod mn env1 env2).c (Long mn' r) =
     if mn = mn' then T
     else mod_defined env2.c (Long mn' r)) /\
   (nsLookup (write_mod mn env1 env2).v (Long mn1 ln) =
    if mn = mn1 then nsLookup env1.v ln else
      nsLookup env2.v (Long mn1 ln)) /\
   (nsLookup (write_mod mn env1 env2).c (Long mn1 ln) =
    if mn = mn1 then nsLookup env1.c ln else
      nsLookup env2.c (Long mn1 ln))
Proof
  fs [write_mod_def,mod_defined_def] \\
  EVAL_TAC \\
  fs[GSYM nsLift_def,id_to_mods_def,nsLookupMod_nsAppend] \\
  simp[] >> CONJ_TAC>>
  (eq_tac
  >-
    (strip_tac>>
    Cases_on`p1`>>fs[]>>
    fs[namespacePropsTheory.nsLookupMod_nsLift]>>
    Cases_on`mn=h`>>fs[]>>
    qexists_tac`h::t`>>fs[])
  >>
  Cases_on`mn=mn'`>>fs[]
  >-
    (qexists_tac`[mn']`>>fs[namespacePropsTheory.nsLookupMod_nsLift,nsLookupMod_def])
  >>
    strip_tac>>
    asm_exists_tac>>fs[namespacePropsTheory.nsLookupMod_nsLift,nsLookupMod_def]>>
    Cases_on`p1`>>fs[]>> rw[]>>
    Cases_on`p1'`>>fs[]>>
    metis_tac[])
QED

Theorem nsLookup_merge_env:
   (nsLookup (merge_env e1 e2).v (Short n) =
      case nsLookup e1.v (Short n) of
      | NONE => nsLookup e2.v (Short n)
      | SOME x => SOME x) /\
   (nsLookup (merge_env e1 e2).c (Short n) =
      case nsLookup e1.c (Short n) of
      | NONE => nsLookup e2.c (Short n)
      | SOME x => SOME x) /\
   (nsLookup (merge_env e1 e2).v (Long mn ln) =
      case nsLookup e1.v (Long mn ln) of
      | NONE => if mod_defined e1.v (Long mn ln) then NONE
                else nsLookup e2.v (Long mn ln)
      | SOME x => SOME x) /\
   (nsLookup (merge_env e1 e2).c (Long mn ln) =
      case nsLookup e1.c (Long mn ln) of
      | NONE => if mod_defined e1.c (Long mn ln) then NONE
                else nsLookup e2.c (Long mn ln)
      | SOME x => SOME x) ∧
   (mod_defined (merge_env e1 e2).v x =
   (mod_defined e1.v x ∨ mod_defined e2.v x)) /\
   (mod_defined (merge_env e1 e2).c x =
   (mod_defined e1.c x ∨ mod_defined e2.c x))
Proof
  fs [merge_env_def,mod_defined_def] \\ rw[] \\ every_case_tac
  \\ fs[namespacePropsTheory.nsLookup_nsAppend_some]
  THEN1 (Cases_on `nsLookup e2.v (Short n)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ rw [] \\ fs [namespaceTheory.id_to_mods_def])
  THEN1 (Cases_on `nsLookup e2.c (Short n)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ rw [] \\ fs [namespaceTheory.id_to_mods_def])
  THEN1 (Cases_on `nsLookup e2.v (Long mn ln)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ metis_tac [mod_defined_def])
  THEN1 (Cases_on `nsLookup e2.v (Long mn ln)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ fs [mod_defined_def] \\ rw []
         \\ CCONTR_TAC \\ Cases_on `nsLookupMod e1.v p1` \\ fs []
         \\ metis_tac [])
  THEN1 (Cases_on `nsLookup e2.c (Long mn ln)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ metis_tac [mod_defined_def])
  THEN1 (Cases_on `nsLookup e2.c (Long mn ln)`
         \\ fs [namespacePropsTheory.nsLookup_nsAppend_none,
                namespacePropsTheory.nsLookup_nsAppend_some]
         \\ fs [mod_defined_def] \\ rw []
         \\ CCONTR_TAC \\ Cases_on `nsLookupMod e1.c p1` \\ fs []
         \\ metis_tac [])
  THEN1
    (EVAL_TAC>>fs[nsLookupMod_nsAppend]>>eq_tac>>rw[]>>rfs[]
    >-
      (every_case_tac>>
      metis_tac[])
    >-
      (asm_exists_tac>>fs[])
    >>
      Cases_on`mod_defined e1.v x`>>fs[mod_defined_def]
      >-
        (rveq>>asm_exists_tac>>qexists_tac`p2'`>>fs[])
      >>
      asm_exists_tac>>fs[]>>
      first_assum(qspecl_then[`p1`,`p2`] assume_tac)>>rfs[]>>
      Cases_on`nsLookupMod e1.v p1`>>fs[]>>
      rw[]>>
      rename[`nsLookupMod _ xx`,`p1 ++ p2`,`xx ++ p3`] >>
      first_x_assum(qspecl_then[`xx`,`p3++p2`]mp_tac) >>
      fs[])
  THEN1
    (EVAL_TAC>>fs[nsLookupMod_nsAppend]>>eq_tac>>rw[]>>rfs[]
    >-
      (every_case_tac>>
      metis_tac[])
    >-
      (asm_exists_tac>>fs[])
    >>
      Cases_on`mod_defined e1.c x`>>fs[mod_defined_def]
      >-
        (rveq>>asm_exists_tac>>qexists_tac`p2'`>>fs[])
      >>
      asm_exists_tac>>fs[]>>
      first_assum(qspecl_then[`p1`,`p2`] assume_tac)>>rfs[]>>
      Cases_on`nsLookupMod e1.c p1`>>fs[]>>
      rw[]>>
      rename[`nsLookupMod _ xx`,`p1 ++ p2`,`xx ++ p3`] >>
      first_x_assum(qspecl_then[`xx`,`p3++p2`]mp_tac) >>
      fs[])
QED

Theorem nsLookup_nsBind_compute[compute]:
   (nsLookup (nsBind n v e) (Short n1) =
    if n = n1 then SOME v else nsLookup e (Short n1)) /\
   (nsLookup (nsBind n v e) (Long l1 l2) = nsLookup e (Long l1 l2))
Proof
  rw [namespacePropsTheory.nsLookup_nsBind]
QED

Theorem nsLookup_nsAppend[compute] =
  nsLookup_merge_env
  |> SIMP_RULE (srw_ss()) [merge_env_def]
  |> Q.INST [`e1`|->`<|c:=e1c;v:=e1v|>`,`e2`|->`<|c:=e2c;v:=e2v|>`]
  |> SIMP_RULE (srw_ss()) []

(* Base case for mod_defined (?) *)
Theorem mod_defined_base[compute]:
   mod_defined (Bind _ []) _ = F
Proof
  rw[mod_defined_def]>>Cases_on`p1`>>EVAL_TAC
QED


(* --- the rest of this file might be unused junk --- *)

(* misc theorems about lookup functions *)

(* No idea why this is sparated out *)
Theorem lookup_var_write:
   (lookup_var v (write w x env) = if v = w then SOME x else lookup_var v env) /\
    (nsLookup (write w x env).v (Short v)  =
       if v = w then SOME x else nsLookup env.v (Short v) ) /\
   (nsLookup (write w x env).v (Long mn lname)  =
       nsLookup env.v (Long mn lname)) ∧
    (lookup_cons name (write w x env) = lookup_cons name env)
Proof
  fs [lookup_var_def,write_def,lookup_cons_def] \\ rw []
QED

Theorem lookup_var_write_mod:
   (lookup_var v (write_mod mn e1 env) = lookup_var v env) /\
   (lookup_cons (Long mn1 (Short name)) (write_mod mn2 e1 env) =
    if mn1 = mn2 then
      lookup_cons (Short name) e1
    else
      lookup_cons (Long mn1 (Short name)) env) /\
   (lookup_cons (Short name) (write_mod mn2 e1 env) =
    lookup_cons (Short name) env)
Proof
  fs [lookup_var_def,write_mod_def, lookup_cons_def] \\ rw []
QED

Theorem lookup_var_write_cons:
   (lookup_var v (write_cons n d env) = lookup_var v env) /\
   (lookup_cons (Short name) (write_cons n d env) =
     if name = n then SOME d else lookup_cons (Short name) env) /\
   (lookup_cons (Long l full_name) (write_cons n d env) =
    lookup_cons (Long l full_name) env) /\
   (nsLookup (write_cons n d env).v x = nsLookup env.v x)
Proof
  fs [lookup_var_def,write_cons_def,lookup_cons_def] \\ rw []
QED

Theorem lookup_var_empty_env:
   (lookup_var v empty_env = NONE) /\
    (nsLookup empty_env.v (Short k) = NONE) /\
    (nsLookup empty_env.v (Long mn m) = NONE) /\
    (lookup_cons name empty_env = NONE)
Proof
  fs[lookup_var_def,empty_env_def,lookup_cons_def]
QED

(*
Theorem lookup_var_merge_env:
   (lookup_var v1 (merge_env e1 e2) =
       case lookup_var v1 e1 of
       | NONE => lookup_var v1 e2
       | res => res) /\
    (lookup_cons name (merge_env e1 e2) =
       case lookup_cons name e1 of
       | NONE => lookup_cons name e2
       | res => res)
Proof
  fs [lookup_var_def,lookup_cons_def,merge_env_def] \\ rw[] \\ every_case_tac \\
  fs[namespacePropsTheory.nsLookup_nsAppend_some]
  >-
    (Cases_on`nsLookup e2.v (Short v1)`>>
    fs[namespacePropsTheory.nsLookup_nsAppend_none,
       namespacePropsTheory.nsLookup_nsAppend_some,namespaceTheory.id_to_mods_def])
  \\ ... (* TODO *)
QED);
*)

Definition prog_syntax_ok_def:
  prog_syntax_ok prog = IS_SOME (check_cons_dec_list init_env.c prog)
End

Theorem prog_syntax_ok_isPREFIX:
  ∀p1 p2. prog_syntax_ok p1 ∧ isPREFIX p2 p1 ⇒ prog_syntax_ok p2
Proof
  rw [prog_syntax_ok_def,IS_SOME_EXISTS]
  \\ drule_then irule check_cons_dec_list_isPREFIX \\ fs []
QED

Theorem Decls_IMP_Prog:
  Decls init_env s1 ds env2 s2 ⇒
  prog_syntax_ok ds ⇒
  Prog init_env s1 ds env2 s2
Proof
  rw []
  \\ gvs [Decls_def,Prog_def,evaluate_dec_list_eq_evaluate_decs,prog_syntax_ok_def]
  \\ last_x_assum $ irule_at Any
QED

Theorem prog_syntax_ok_semantics:
  prog_syntax_ok prog ⇒
  semantics_dec_list st init_env prog = semantics_prog st init_env prog
Proof
  simp [FUN_EQ_THM] \\ strip_tac \\ Cases
  \\ gvs [semanticsTheory.semantics_prog_def, semantics_dec_list_def]
  \\ gvs [prog_syntax_ok_def, evaluate_dec_list_eq_evaluate_decs,
          semanticsTheory.evaluate_prog_with_clock_def,
          evaluate_decTheory.evaluate_dec_list_with_clock_def]
QED
