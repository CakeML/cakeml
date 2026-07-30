(*
  Correctness for the source_dce pass.
*)
Theory source_dceProof
Ancestors
  source_dce evaluate evaluateProps semanticPrimitives
  semanticPrimitivesProps misc[qualified] semantics ast
  source_evalProof namespace primSemEnv[qualified]
Libs
  preamble


Definition fvs_def:
  fvs (Raise e) = fvs e ∧
  fvs (Handle e pes) = fvs e ∪ fvs_pes pes ∧
  fvs (ast$Lit l) = {} ∧
  fvs (Con cn es) = fvs_list es ∧
  fvs (Var v) = {v} ∧
  fvs (Fun x e) = fvs e DELETE Short x ∧
  fvs (App op es) = fvs_list es ∧
  fvs (Log lop e1 e2) = fvs e1 ∪ fvs e2 ∧
  fvs (If e1 e2 e3) = fvs e1 ∪ fvs e2 ∪ fvs e3 ∧
  fvs (Mat e pes) = fvs e ∪ fvs_pes pes ∧
  fvs (Let NONE e1 e2) = fvs e1 ∪ fvs e2 ∧
  fvs (Let (SOME x) e1 e2) = fvs e1 ∪ (fvs e2 DELETE Short x) ∧
  fvs (Letrec funs e) =
    (fvs_funs funs ∪ fvs e) DIFF set (MAP (Short o FST) funs) ∧
  fvs (Tannot e t) = fvs e ∧
  fvs (Lannot e l) = fvs e ∧
  fvs_list [] = {} ∧
  fvs_list (e::es) = fvs e ∪ fvs_list es ∧
  fvs_pes [] = {} ∧
  fvs_pes ((p,e)::pes) =
    (fvs e DIFF set (MAP Short (pat_bindings p))) ∪ fvs_pes pes ∧
  fvs_funs [] = {} ∧
  fvs_funs ((g,x,e)::funs) = (fvs e DELETE Short x) ∪ fvs_funs funs
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL e => exp_size e
                           | INR (INL es) => list_size exp_size es
                           | INR (INR (INL pes)) =>
                               list_size (pair_size pat_size exp_size) pes
                           | INR (INR (INR funs)) =>
                               list_size (pair_size mlstring_size
                                 (pair_size mlstring_size exp_size)) funs)’
End

(* the set of names that an implementation-level names value stands for *)

Definition names_set_def:
  names_set ((shorts,longs):names) =
    IMAGE Short (FDOM shorts) ∪ longs_set longs ∧
  longs_set (Names []) = {} ∧
  longs_set (Names ((mn,s)::xs)) =
    IMAGE (Long mn) (names_set s) ∪
    (longs_set (Names xs) DIFF IMAGE (Long mn) UNIV)
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL s => long_names_size (SND s) + 1
                           | INR l => long_names_size l)’
  \\ simp [list_size_def, basicSizeTheory.pair_size_def]
End

Theorem names_set_empty_names[local,simp]:
  names_set empty_names = {}
Proof
  simp [names_set_def, empty_names_def]
QED

(* longs_set follows lookup_mod, i.e. a shadowed module entry contributes
   nothing, and everything it contains is a Long name *)
Theorem longs_set_thms[local]:
  (∀longs mn id.
     Long mn id ∈ longs_set longs ⇔ id ∈ names_set (lookup_mod longs mn)) ∧
  (∀longs n. Short n ∉ longs_set longs)
Proof
  qsuff_tac ‘∀xs. (∀mn id. Long mn id ∈ longs_set (Names xs) ⇔
                           id ∈ names_set (lookup_mod (Names xs) mn)) ∧
                  (∀n. Short n ∉ longs_set (Names xs))’
  >- (rw [] \\ Cases_on ‘longs’ \\ metis_tac [])
  \\ Induct \\ gvs [names_set_def, lookup_mod_def]
  \\ PairCases \\ rw [names_set_def, lookup_mod_def] \\ gvs []
QED

Theorem is_used_names_set[local]:
  ∀s n. is_used s n ⇔ Short n ∈ names_set s
Proof
  Cases \\ gvs [is_used_def, names_set_def, longs_set_thms]
QED

Theorem names_set_strip_mod[local]:
  ∀s mn id. Long mn id ∈ names_set s ⇔ id ∈ names_set (strip_mod mn s)
Proof
  Cases \\ gvs [names_set_def, strip_mod_def, longs_set_thms]
QED

Theorem longs_set_upd_alist[local]:
  ∀xs mn t id.
    names_set t = id INSERT names_set (lookup_mod (Names xs) mn) ⇒
    longs_set (Names (upd_alist xs mn t)) = Long mn id INSERT longs_set (Names xs)
Proof
  Induct \\ gvs [upd_alist_def, names_set_def, lookup_mod_def]
  \\ rpt gen_tac \\ PairCases_on ‘h’
  \\ rw [upd_alist_def, names_set_def, lookup_mod_def]
  >- (gvs [EXTENSION] \\ metis_tac [])
  \\ last_x_assum drule \\ strip_tac \\ gvs []
  \\ gvs [EXTENSION] \\ metis_tac []
QED

Theorem names_set_add_name[local,simp]:
  ∀id s. names_set (add_name s id) = id INSERT names_set s
Proof
  Induct \\ Cases_on ‘s’ \\ rename [‘(shorts,longs)’] \\ Cases_on ‘longs’
  \\ gvs [add_name_def, names_set_def, insert_mod_def]
  >- (gvs [EXTENSION] \\ metis_tac [])
  \\ gen_tac
  \\ qspecl_then [‘l’,‘m’,‘add_name (lookup_mod (Names l) m) id’,‘id’] mp_tac
       longs_set_upd_alist
  \\ gvs [] \\ strip_tac \\ gvs [EXTENSION] \\ metis_tac []
QED

Theorem lookup_mod_insert_mod[local]:
  ∀l mn t mn'.
    lookup_mod (insert_mod l mn t) mn' =
    if mn' = mn then t else lookup_mod l mn'
Proof
  Cases \\ gvs [insert_mod_def, lookup_mod_def]
  \\ Induct_on ‘l'’ \\ gvs [upd_alist_def, lookup_mod_def]
  >- rw []
  \\ PairCases \\ rw [upd_alist_def, lookup_mod_def] \\ gvs []
QED

(* union_names keeps all the names of both arguments *)
Theorem names_set_union_names[local]:
  (∀a b. names_set a ∪ names_set b ⊆ names_set (union_names a b)) ∧
  (∀l1 l2. longs_set l1 ∪ longs_set l2 ⊆ longs_set (union_longs l1 l2))
Proof
  ho_match_mp_tac union_names_ind \\ rpt conj_tac \\ rpt gen_tac
  \\ rpt strip_tac
  >- (gvs [union_names_def, names_set_def, SUBSET_DEF] \\ metis_tac [])
  >- (gvs [union_names_def] \\ gvs [names_set_def])
  \\ once_rewrite_tac [union_names_def]
  \\ irule SUBSET_TRANS
  \\ first_assum $ irule_at Any
  \\ gvs [SUBSET_DEF] \\ rpt strip_tac
  >- (Cases_on ‘x’
      \\ gvs [longs_set_thms, lookup_mod_insert_mod, names_set_def]
      \\ rw [] \\ gvs [longs_set_thms]
      \\ gvs [lookup_mod_def] \\ metis_tac [])
  \\ Cases_on ‘x’ \\ gvs [longs_set_thms, lookup_mod_insert_mod]
  \\ rw [] \\ gvs [names_set_def]
QED

(* the pointwise form of names_set_union_names: going through SUBSET_DEF and
   IN_UNION in a first-order prover makes the used-set proofs depend on metis
   finding the right instance *)
Theorem IN_names_set_union_names[local]:
  (x ∈ names_set a ⇒ x ∈ names_set (union_names a b)) ∧
  (x ∈ names_set b ⇒ x ∈ names_set (union_names a b))
Proof
  rpt strip_tac
  \\ qspecl_then [‘a’,‘b’] mp_tac (cj 1 names_set_union_names)
  \\ rewrite_tac [SUBSET_DEF]
  \\ disch_then (qspec_then ‘x’ mp_tac)
  \\ simp []
QED

Theorem names_set_free_vars[local]:
  (∀locals acc e.
     names_set (free_vars locals acc e) =
     names_set acc ∪ (fvs e DIFF IMAGE Short (set locals))) ∧
  (∀locals acc es.
     names_set (free_vars_list locals acc es) =
     names_set acc ∪ (fvs_list es DIFF IMAGE Short (set locals))) ∧
  (∀locals acc pes.
     names_set (free_vars_pes locals acc pes) =
     names_set acc ∪ (fvs_pes pes DIFF IMAGE Short (set locals))) ∧
  (∀locals acc funs.
     names_set (free_vars_funs locals acc funs) =
     names_set acc ∪ (fvs_funs funs DIFF IMAGE Short (set locals)))
Proof
  ho_match_mp_tac free_vars_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  \\ gvs [free_vars_def, fvs_def, names_set_add_name, LIST_TO_SET_MAP]
  \\ rw [] \\ gvs [names_set_add_name, EXTENSION, MEM_MAP] \\ metis_tac []
QED

Theorem fvs_list_APPEND[local]:
  ∀xs ys. fvs_list (xs ++ ys) = fvs_list xs ∪ fvs_list ys
Proof
  Induct \\ gvs [fvs_def, UNION_ASSOC]
QED

Theorem fvs_list_REVERSE[local,simp]:
  ∀es. fvs_list (REVERSE es) = fvs_list es
Proof
  Induct \\ gvs [fvs_def, fvs_list_APPEND] \\ gvs [EXTENSION] \\ metis_tac []
QED

(* declarations that are all dropped leave the set of used names alone *)
Theorem dce_decs_empty_used[local]:
  (∀used ds ds1 used1.
     dce_decs used ds = (ds1,used1) ∧ append ds1 = [] ⇒ used1 = used) ∧
  (∀used d ds1 used1.
     dce_dec used d = (ds1,used1) ∧ append ds1 = [] ⇒ used1 = used)
Proof
  ho_match_mp_tac dce_decs_ind \\ rpt conj_tac \\ rpt gen_tac
  \\ gvs [dce_decs_def] \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs ()] \\ every_case_tac \\ gvs []
  \\ res_tac \\ gvs []
QED

(* build_conv only depends on the constructor's stamp, not on its arguments *)
Theorem build_conv_thm[local]:
  build_conv c cn vs1 = SOME v1 ⇒
  ∃s. v1 = Conv s vs1 ∧ ∀vs2. build_conv c cn vs2 = SOME (Conv s vs2)
Proof
  Cases_on ‘cn’ \\ gvs [build_conv_def]
  \\ Cases_on ‘nsLookup c x’ \\ gvs []
  \\ strip_tac \\ PairCases_on ‘x'’ \\ gvs []
QED

Inductive v_rel:
[~Litv:]
  ∀f lit.
    v_rel f ((Litv lit):semanticPrimitives$v) ((Litv lit):semanticPrimitives$v)
[~Loc:]
  ∀f loc1 loc2 b.
    FLOOKUP f loc1 = SOME loc2 ⇒
    v_rel f (Loc b loc1) (Loc b loc2)
[~Conv:]
  ∀f vs1 vs2 c.
    LIST_REL (v_rel f) vs1 vs2 ⇒
    v_rel f (Conv c vs1) (Conv c vs2)
[~Vectorv:]
  ∀f vs1 vs2.
    LIST_REL (v_rel f) vs1 vs2 ⇒
    v_rel f (Vectorv vs1) (Vectorv vs2)
[~Closure:]
  ∀f env1 env2 v e.
    env1.c = env2.c ∧
    (∀x v1.
       x ∈ fvs e ∧ x ≠ Short v ∧ nsLookup env1.v x = SOME v1 ⇒
       ∃v2. nsLookup env2.v x = SOME v2 ∧ v_rel f v1 v2) ⇒
    v_rel f (Closure env1 v e) (Closure env2 v e)
[~Recclosure:]
  ∀f env1 env2 funs n.
    env1.c = env2.c ∧
    (∀x v1.
       x ∈ fvs_funs funs ∧ ¬MEM x (MAP (Short o FST) funs) ∧
       nsLookup env1.v x = SOME v1 ⇒
       ∃v2. nsLookup env2.v x = SOME v2 ∧ v_rel f v1 v2) ⇒
    v_rel f (Recclosure env1 funs n) (Recclosure env2 funs n)
End

(* f maps the locations of s1 that are still reachable to the locations
   they have in s2; it must be injective, since do_eq compares locations.
   Everything in the state other than the store and eval state are kept equal. *)
Definition state_rel_def:
  state_rel f s1 s2 ⇔
    INJ (FAPPLY f) (FDOM f) UNIV ∧
    (∀loc1 loc2.
       FLOOKUP f loc1 = SOME loc2 ⇒
       ∃sv1 sv2.
         store_lookup loc1 s1.refs = SOME sv1 ∧
         store_lookup loc2 s2.refs = SOME sv2 ∧
         sv_rel (v_rel f) sv1 sv2) ∧
    s1.clock = s2.clock ∧
    s1.ffi = s2.ffi ∧
    s1.next_type_stamp = s2.next_type_stamp ∧
    s1.next_exn_stamp = s2.next_exn_stamp ∧
    ∀x. s1.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev
End

Definition env_rel_def:
  env_rel f names env1 env2 ⇔
    env1.c = env2.c ∧
    ∀x v1.
      x ∈ names ∧ nsLookup env1.v x = SOME v1 ⇒
      ∃v2. nsLookup env2.v x = SOME v2 ∧ v_rel f v1 v2
End

Theorem v_rel_submap[local]:
  ∀f1 f2 v1 v2. v_rel f1 v1 v2 ∧ f1 ⊑ f2 ⇒ v_rel f2 v1 v2
Proof
  Induct_on ‘v_rel’ \\ rw []
  \\ simp [Once v_rel_cases]
  \\ gvs [LIST_REL_EL_EQN]
  \\ metis_tac [FLOOKUP_SUBMAP]
QED

Theorem env_rel_submap[local]:
  ∀f1 f2 names env1 env2.
    env_rel f1 names env1 env2 ∧ f1 ⊑ f2 ⇒ env_rel f2 names env1 env2
Proof
  gvs [env_rel_def] \\ metis_tac [v_rel_submap]
QED

Theorem env_rel_SUBSET[local]:
  ∀f names1 names2 env1 env2.
    env_rel f names1 env1 env2 ∧ names2 ⊆ names1 ⇒ env_rel f names2 env1 env2
Proof
  gvs [env_rel_def, SUBSET_DEF] \\ metis_tac []
QED

(* the form in which the two are used: the map grows as evaluation proceeds
   and each subexpression needs fewer names than the whole *)
Theorem env_rel_mono[local]:
  ∀f1 f2 names1 names2 env1 env2.
    env_rel f1 names1 env1 env2 ∧ f1 ⊑ f2 ∧ names2 ⊆ names1 ⇒
    env_rel f2 names2 env1 env2
Proof
  metis_tac [env_rel_submap, env_rel_SUBSET]
QED

Theorem env_rel_nsOptBind[local]:
  ∀f names env1 env2 xo v1 v2 names2.
    env_rel f names env1 env2 ∧ v_rel f v1 v2 ∧
    names2 DIFF (case xo of NONE => {} | SOME x => {Short x}) ⊆ names ⇒
    env_rel f names2 (env1 with v := nsOptBind xo v1 env1.v)
                     (env2 with v := nsOptBind xo v2 env2.v)
Proof
  Cases_on ‘xo’ \\ gvs [env_rel_def, SUBSET_DEF, namespaceTheory.nsOptBind_def]
  \\ rw [] \\ rename [‘nsLookup _ id = SOME _’]
  \\ Cases_on ‘id = Short x’ \\ gvs []
QED

Theorem ALOOKUP_LIST_REL[local]:
  ∀bs1 bs2.
    LIST_REL (λx y. FST x = FST y ∧ R (SND x) (SND y)) bs1 bs2 ⇒
    ∀x. case ALOOKUP bs1 x of
        | NONE => ALOOKUP bs2 x = NONE
        | SOME v1 => ∃v2. ALOOKUP bs2 x = SOME v2 ∧ R v1 v2
Proof
  Induct \\ gvs [PULL_EXISTS] \\ PairCases \\ PairCases \\ rw [] \\ gvs []
  \\ first_x_assum drule \\ disch_then (qspec_then ‘x’ mp_tac) \\ rw []
QED

(* the bindings that pmatch produces are added to both environments *)
Theorem env_rel_nsAppend[local]:
  ∀f names names2 env1 env2 bs1 bs2.
    env_rel f names env1 env2 ∧
    LIST_REL (λx y. FST x = FST y ∧ v_rel f (SND x) (SND y)) bs1 bs2 ∧
    names2 DIFF set (MAP (Short o FST) bs1) ⊆ names ⇒
    env_rel f names2 (env1 with v := nsAppend (alist_to_ns bs1) env1.v)
                     (env2 with v := nsAppend (alist_to_ns bs2) env2.v)
Proof
  rw [env_rel_def, namespacePropsTheory.nsLookup_nsAppend_some]
  \\ gvs [namespacePropsTheory.nsLookup_alist_to_ns_some,
          namespacePropsTheory.nsLookup_alist_to_ns_none]
  \\ drule ALOOKUP_LIST_REL
  >- (disch_then (qspec_then ‘x'’ mp_tac) \\ gvs [] \\ strip_tac \\ gvs [])
  \\ ‘x ∈ names’ by
       (gvs [SUBSET_DEF] \\ first_x_assum irule
        \\ gvs [MEM_MAP, PULL_EXISTS, FORALL_PROD] \\ Cases_on ‘x’ \\ gvs []
        \\ CCONTR_TAC \\ gvs [ALOOKUP_NONE, MEM_MAP, FORALL_PROD])
  \\ first_x_assum drule_all \\ strip_tac \\ gvs [] \\ strip_tac
  \\ Cases_on ‘x’ \\ gvs []
  >- (first_x_assum (qspec_then ‘n’ mp_tac) \\ simp [] \\ strip_tac
      \\ rw [] \\ Cases_on ‘p1’ \\ gvs [])
  \\ rw [] \\ Cases_on ‘p1’ \\ gvs []
QED

Theorem pmatch_v_rel[local]:
  (∀envC refs1 p v1 bs1 refs2 v2 bs2 f.
     v_rel f v1 v2 ∧
     LIST_REL (λx y. FST x = FST y ∧ v_rel f (SND x) (SND y)) bs1 bs2 ∧
     (∀loc1 loc2.
        FLOOKUP f loc1 = SOME loc2 ⇒
        ∃sv1 sv2.
          store_lookup loc1 refs1 = SOME sv1 ∧
          store_lookup loc2 refs2 = SOME sv2 ∧ sv_rel (v_rel f) sv1 sv2) ⇒
     case pmatch envC refs1 p v1 bs1 of
     | Match bs1' =>
         ∃bs2'.
           pmatch envC refs2 p v2 bs2 = Match bs2' ∧
           LIST_REL (λx y. FST x = FST y ∧ v_rel f (SND x) (SND y)) bs1' bs2'
     | No_match => pmatch envC refs2 p v2 bs2 = No_match
     | _ => T) ∧
  (∀envC refs1 ps vs1 bs1 refs2 vs2 bs2 f.
     LIST_REL (v_rel f) vs1 vs2 ∧
     LIST_REL (λx y. FST x = FST y ∧ v_rel f (SND x) (SND y)) bs1 bs2 ∧
     (∀loc1 loc2.
        FLOOKUP f loc1 = SOME loc2 ⇒
        ∃sv1 sv2.
          store_lookup loc1 refs1 = SOME sv1 ∧
          store_lookup loc2 refs2 = SOME sv2 ∧ sv_rel (v_rel f) sv1 sv2) ⇒
     case pmatch_list envC refs1 ps vs1 bs1 of
     | Match bs1' =>
         ∃bs2'.
           pmatch_list envC refs2 ps vs2 bs2 = Match bs2' ∧
           LIST_REL (λx y. FST x = FST y ∧ v_rel f (SND x) (SND y)) bs1' bs2'
     | No_match => pmatch_list envC refs2 ps vs2 bs2 = No_match
     | _ => T)
Proof
  ho_match_mp_tac pmatch_ind \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  >~ [‘pmatch envC refs1 (Plit l) (Litv l') bs1’]
  >- (qpat_x_assum ‘v_rel _ _ _’ (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once v_rel_cases])
      \\ gvs [pmatch_def] \\ rw [] \\ gvs [pmatch_def])
  >~ [‘pmatch envC refs1 (Pcon (SOME n) ps) (Conv (SOME stamp') vs1) bs1’]
  >- (qpat_x_assum ‘v_rel _ _ _’ (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once v_rel_cases])
      \\ gvs [pmatch_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
      \\ Cases_on ‘nsLookup envC n’ \\ gvs []
            \\ PairCases_on ‘x’ \\ gvs [] \\ rw [] \\ gvs []
      \\ first_x_assum drule_all \\ gvs [])
  >~ [‘pmatch envC refs1 (Pcon NONE ps) (Conv NONE vs1) bs1’]
  >- (qpat_x_assum ‘v_rel _ _ _’ (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once v_rel_cases])
      \\ gvs [pmatch_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ gvs [] \\ rw [] \\ gvs []
      \\ first_x_assum drule_all \\ gvs [])
  >~ [‘pmatch envC refs1 (Pref p) (Loc b lnum) bs1’]
  >- (qpat_x_assum ‘v_rel _ _ _’ (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once v_rel_cases])
      \\ gvs [pmatch_def]
      \\ qpat_assum ‘∀loc1 loc2. FLOOKUP _ _ = _ ⇒ _’ drule \\ strip_tac
      \\ gvs [] \\ Cases_on ‘sv1’ \\ Cases_on ‘sv2’ \\ gvs []
      \\ last_x_assum drule
      \\ disch_then (qspecl_then [‘refs2’,‘bs2’] mp_tac)
      \\ impl_tac \\ gvs [])
  >~ [‘pmatch envC refs1 (Pas p i) v1 bs1’]
  >- (gvs [pmatch_def] \\ last_x_assum irule \\ gvs [])
  >~ [‘pmatch envC refs1 (Ptannot p t) v1 bs1’]
  >- (gvs [pmatch_def] \\ last_x_assum irule \\ gvs [])
  >~ [‘pmatch_list envC refs1 (p::ps) (v1::vs1) bs1’]
  >- (gvs [pmatch_def]
      \\ Cases_on ‘pmatch envC refs1 p v1 bs1’ \\ gvs []
      >- (last_x_assum drule_all \\ strip_tac \\ gvs []
          \\ Cases_on ‘pmatch_list envC refs1 ps vs1 bs1’ \\ gvs []
          \\ last_x_assum drule_all \\ strip_tac \\ gvs [])
      \\ last_x_assum drule_all \\ strip_tac \\ gvs [])
  \\ gvs [pmatch_def]
QED

Theorem can_pmatch_all_v_rel[local]:
  ∀ps envC refs1 refs2 v1 v2 f.
    can_pmatch_all envC refs1 ps v1 ∧ v_rel f v1 v2 ∧
    (∀loc1 loc2.
       FLOOKUP f loc1 = SOME loc2 ⇒
       ∃sv1 sv2.
         store_lookup loc1 refs1 = SOME sv1 ∧
         store_lookup loc2 refs2 = SOME sv2 ∧ sv_rel (v_rel f) sv1 sv2) ⇒
    can_pmatch_all envC refs2 ps v2
Proof
  Induct \\ gvs [can_pmatch_all_def] \\ rpt gen_tac \\ strip_tac
  \\ qspecl_then [‘envC’,‘refs1’,‘h’,‘v1’,‘[]’,‘refs2’,‘v2’,‘[]’,‘f’]
       mp_tac (cj 1 pmatch_v_rel)
  \\ Cases_on ‘pmatch envC refs1 h v1 []’ \\ gvs []
  \\ strip_tac \\ gvs [] \\ last_x_assum irule \\ metis_tac []
QED

Theorem v_rel_bind_exn_v[local,simp]:
  v_rel f bind_exn_v bind_exn_v
Proof
  simp [semanticPrimitivesTheory.bind_exn_v_def, Once v_rel_cases]
QED

Theorem ALOOKUP_rec_env[local]:
  ∀xs funs env x.
    ALOOKUP (MAP (λ(f,n,e). (f,Recclosure env funs f)) xs) x =
    if MEM x (MAP FST xs) then SOME (Recclosure env funs x) else NONE
Proof
  Induct \\ gvs [] \\ PairCases \\ rw [] \\ gvs []
QED

Theorem env_rel_build_rec_env[local]:
  ∀f names names2 env1 env2 funs.
    env_rel f names env1 env2 ∧
    fvs_funs funs DIFF set (MAP (Short o FST) funs) ⊆ names ∧
    names2 DIFF set (MAP (Short o FST) funs) ⊆ names ⇒
    env_rel f names2 (env1 with v := build_rec_env funs env1 env1.v)
                     (env2 with v := build_rec_env funs env2 env2.v)
Proof
  rw [env_rel_def, build_rec_env_merge,
      namespacePropsTheory.nsLookup_nsAppend_some]
  \\ gvs [namespacePropsTheory.nsLookup_alist_to_ns_some,
          namespacePropsTheory.nsLookup_alist_to_ns_none, ALOOKUP_rec_env]
  \\ gvs [AllCaseEqs()]
  >- (irule v_rel_Recclosure \\ gvs [SUBSET_DEF] \\ metis_tac [])
  \\ ‘x ∈ names’ by
       (gvs [SUBSET_DEF] \\ first_x_assum irule
        \\ gvs [MEM_MAP, PULL_EXISTS, FORALL_PROD] \\ Cases_on ‘x’ \\ gvs [])
  \\ first_x_assum drule_all \\ strip_tac \\ gvs []
  \\ qexists_tac ‘v2’ \\ gvs [] \\ disj2_tac \\ rw [] \\ Cases_on ‘p1’ \\ gvs []
QED

Theorem env_rel_build_rec_env_unused[local]:
  ∀f names env1 env2 funs.
    env_rel f names env1 env2 ∧ EVERY (λ(g,x,e). Short g ∉ names) funs ⇒
    env_rel f names (env1 with v := build_rec_env funs env1 env1.v) env2
Proof
  rw [env_rel_def, build_rec_env_merge,
      namespacePropsTheory.nsLookup_nsAppend_some]
  \\ gvs [namespacePropsTheory.nsLookup_alist_to_ns_some, ALOOKUP_rec_env]
  \\ gvs [AllCaseEqs(), EVERY_MEM, MEM_MAP, FORALL_PROD]
  \\ PairCases_on ‘y’ \\ gvs [] \\ res_tac \\ gvs []
QED

Theorem extend_dec_env_build_rec_env[local]:
  extend_dec_env <|v := build_rec_env funs env nsEmpty; c := nsEmpty|> env =
  env with v := build_rec_env funs env env.v
Proof
  gvs [extend_dec_env_def, build_rec_env_merge, sem_env_component_equality,
       namespacePropsTheory.nsAppend_assoc]
QED

Theorem names_set_delete_names[local]:
  ∀ns s. names_set (delete_names s ns) = names_set s DIFF IMAGE Short (set ns)
Proof
  Induct \\ gvs [delete_names_def] \\ Cases_on ‘s’
  \\ gvs [delete_name_def, names_set_def, EXTENSION]
  \\ rpt gen_tac \\ Cases_on ‘x’ \\ gvs [] \\ eq_tac \\ rw []
  \\ gvs [longs_set_thms]
QED

Theorem v_rel_Boolv[local,simp]:
  ∀f b v. v_rel f (Boolv b) v ⇔ v = Boolv b
Proof
  rw [semanticPrimitivesTheory.Boolv_def]
  \\ simp [Once v_rel_cases] \\ metis_tac []
QED

(* -------------------------------------------------------------------------
   Towards the App case: do_app maps related values and states to related
   values and states, possibly allocating (which extends f). This follows
   the approach of do_app_update in compiler/repl/evaluate_skipScript.sml.
   ------------------------------------------------------------------------- *)

Theorem sv_rel_submap[local]:
  sv_rel (v_rel f) sv1 sv2 ∧ f ⊑ f' ⇒ sv_rel (v_rel f') sv1 sv2
Proof
  strip_tac \\ irule sv_rel_mono \\ first_assum $ irule_at Any
  \\ metis_tac [v_rel_submap]
QED

(* inversion of v_rel on the source value; not a simp rule, since the
   declaration-level proofs below rely on v_rel staying folded *)
Theorem v_rel_simps[local]:
  (v_rel f (Litv l) v ⇔ v = Litv l) ∧
  (v_rel f (Loc b n) v ⇔ ∃m. v = Loc b m ∧ FLOOKUP f n = SOME m) ∧
  (v_rel f (Conv c vs) v ⇔ ∃ws. v = Conv c ws ∧ LIST_REL (v_rel f) vs ws) ∧
  (v_rel f (Vectorv vs) v ⇔ ∃ws. v = Vectorv ws ∧ LIST_REL (v_rel f) vs ws) ∧
  (v_rel f (Env e i) v ⇔ F) ∧
  (v_rel f (Closure e1 x body) v ⇔
     ∃e2. v = Closure e2 x body ∧ e1.c = e2.c ∧
          ∀y v1. y ∈ fvs body ∧ y ≠ Short x ∧ nsLookup e1.v y = SOME v1 ⇒
                 ∃v2. nsLookup e2.v y = SOME v2 ∧ v_rel f v1 v2) ∧
  (v_rel f (Recclosure e1 funs g) v ⇔
     ∃e2. v = Recclosure e2 funs g ∧ e1.c = e2.c ∧
          ∀y v1. y ∈ fvs_funs funs ∧ ¬MEM y (MAP (Short o FST) funs) ∧
                 nsLookup e1.v y = SOME v1 ⇒
                 ∃v2. nsLookup e2.v y = SOME v2 ∧ v_rel f v1 v2)
Proof
  rpt conj_tac \\ simp [Once v_rel_cases] \\ metis_tac []
QED

Theorem state_rel_store_lookup[local]:
  state_rel f s1 s2 ∧ FLOOKUP f n = SOME m ⇒
  ∃sv1 sv2. store_lookup n s1.refs = SOME sv1 ∧
            store_lookup m s2.refs = SOME sv2 ∧ sv_rel (v_rel f) sv1 sv2
Proof
  gvs [state_rel_def] \\ metis_tac []
QED

(* allocation: the fresh source location is not in FDOM f and the fresh
   target location is not in its range, so f can be extended *)
Theorem state_rel_alloc[local]:
  state_rel f s1 s2 ∧ sv_rel (v_rel f) sv1 sv2 ⇒
  f ⊑ f |+ (LENGTH s1.refs, LENGTH s2.refs) ∧
  state_rel (f |+ (LENGTH s1.refs, LENGTH s2.refs))
    (s1 with refs := s1.refs ++ [sv1]) (s2 with refs := s2.refs ++ [sv2])
Proof
  strip_tac
  \\ ‘LENGTH s1.refs ∉ FDOM f’ by
       (gvs [state_rel_def, store_lookup_def, FLOOKUP_DEF] \\ CCONTR_TAC
        \\ gvs [] \\ res_tac \\ gvs [])
  \\ conj_asm1_tac >- gvs [SUBMAP_FUPDATE_EQN]
  \\ gvs [state_rel_def, FLOOKUP_UPDATE, store_lookup_def]
  \\ rw [] \\ gvs [EL_APPEND1, EL_APPEND2]
  >- (gvs [INJ_DEF, FAPPLY_FUPDATE_THM] \\ rw [] \\ gvs []
      \\ gvs [FLOOKUP_DEF] \\ first_x_assum drule \\ strip_tac \\ gvs [])
  >- (irule sv_rel_submap \\ qexists_tac ‘f’ \\ gvs [SUBMAP_FUPDATE_EQN])
  >- (‘loc1 < LENGTH s1.refs’ by metis_tac [] \\ simp [])
  >- (‘loc2 < LENGTH s2.refs’ by metis_tac [] \\ simp [])
  \\ ‘loc1 < LENGTH s1.refs ∧ loc2 < LENGTH s2.refs ∧
      sv_rel (v_rel f) (EL loc1 s1.refs) (EL loc2 s2.refs)’ by metis_tac []
  \\ gvs [EL_APPEND1]
  \\ irule sv_rel_submap
  \\ qexists_tac ‘f’ \\ gvs [SUBMAP_FUPDATE_EQN]
QED

(* assignment: the source and target locations are related by f, so by
   injectivity no other related pair is disturbed *)
Theorem state_rel_assign[local]:
  state_rel f s1 s2 ∧ FLOOKUP f n = SOME m ∧ sv_rel (v_rel f) sv1 sv2 ∧
  store_assign n sv1 s1.refs = SOME refs1 ⇒
  ∃refs2. store_assign m sv2 s2.refs = SOME refs2 ∧
          state_rel f (s1 with refs := refs1) (s2 with refs := refs2)
Proof
  strip_tac
  \\ drule_all state_rel_store_lookup \\ strip_tac
  \\ gvs [store_assign_def, store_lookup_def]
  \\ ‘store_v_same_type s2.refs❲m❳ sv2’ by
    (qpat_x_assum ‘store_v_same_type _ _’ mp_tac
     \\ rpt (qpat_x_assum ‘sv_rel _ _ _’ mp_tac)
     \\ rpt (pop_assum kall_tac)
     \\ Cases_on ‘s1.refs❲n❳’ \\ Cases_on ‘s2.refs❲m❳’
     \\ Cases_on ‘sv1’ \\ Cases_on ‘sv2’
     \\ gvs [store_v_same_type_def])
  \\ gvs [state_rel_def, store_lookup_def, EL_LUPDATE]
  \\ rpt gen_tac \\ strip_tac
  \\ first_assum drule \\ strip_tac \\ gvs []
  \\ rw [] \\ gvs []
  \\ gvs [INJ_DEF, FLOOKUP_DEF]
QED

(* equality: locations are compared, so this is where the injectivity of f
   is needed *)
Theorem v_rel_do_eq[local]:
  (∀x1 y1 x2 y2.
     v_rel f x1 x2 ∧ v_rel f y1 y2 ∧ INJ (FAPPLY f) (FDOM f) UNIV ⇒
     do_eq x1 y1 = do_eq x2 y2) ∧
  (∀x1 y1 x2 y2.
     LIST_REL (v_rel f) x1 x2 ∧ LIST_REL (v_rel f) y1 y2 ∧
     INJ (FAPPLY f) (FDOM f) UNIV ⇒
     do_eq_list x1 y1 = do_eq_list x2 y2)
Proof
  ho_match_mp_tac do_eq_ind \\ rpt strip_tac
  \\ gvs [do_eq_def, v_rel_simps]
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ rw [] \\ gvs []
  \\ gvs [INJ_DEF, FLOOKUP_DEF]
  >~ [‘do_eq_list’] >-
   (qpat_x_assum ‘∀x2 y2. _’ (qspecl_then [‘y’,‘y'’] mp_tac)
    \\ impl_tac >- gvs []
    \\ strip_tac \\ gvs []
    \\ CASE_TAC \\ gvs [] \\ IF_CASES_TAC \\ gvs [])
  \\ metis_tac []
QED

Theorem v_rel_v_to_list[local]:
  ∀x1 x2. v_rel f x1 x2 ⇒
          OPTREL (LIST_REL (v_rel f)) (v_to_list x1) (v_to_list x2)
Proof
  ho_match_mp_tac v_to_list_ind \\ rpt strip_tac
  \\ gvs [v_to_list_def, v_rel_simps]
  \\ rw [] \\ gvs [OPTREL_def, v_to_list_def]
  \\ res_tac \\ gvs [OPTREL_def, AllCaseEqs()]
QED

Theorem v_rel_list_to_v[local]:
  ∀xs ys. LIST_REL (v_rel f) xs ys ⇒ v_rel f (list_to_v xs) (list_to_v ys)
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [list_to_v_def, v_rel_simps]
QED

Theorem v_rel_vs_to_string[local]:
  ∀xs ys. LIST_REL (v_rel f) xs ys ⇒ vs_to_string xs = vs_to_string ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [vs_to_string_def]
  \\ rpt strip_tac
  \\ rename [‘v_rel f v w’]
  \\ Cases_on ‘v’ \\ gvs [v_rel_simps, vs_to_string_def]
  \\ rename [‘Litv l’] \\ Cases_on ‘l’ \\ gvs [vs_to_string_def]
  \\ res_tac \\ gvs []
QED

Theorem v_rel_v_to_char_list[local]:
  ∀x1 x2. v_rel f x1 x2 ⇒ v_to_char_list x1 = v_to_char_list x2
Proof
  ho_match_mp_tac v_to_char_list_ind \\ rpt strip_tac
  \\ gvs [v_to_char_list_def, v_rel_simps]
  \\ rw [] \\ gvs [v_to_char_list_def]
  \\ res_tac \\ gvs []
QED

(* the typed operations only ever look at literals and booleans, and v_rel
   relates those only to themselves *)
Theorem v_rel_check_type[local]:
  ∀ty v1 v2. v_rel f v1 v2 ⇒
             (check_type ty v1 ⇔ check_type ty v2) ∧
             (check_type ty v1 ⇒ v1 = v2)
Proof
  rpt gen_tac \\ Cases_on ‘v1’ \\ gvs [v_rel_simps]
  \\ rpt strip_tac \\ gvs []
  \\ Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ gvs [check_type_def, semanticPrimitivesTheory.Boolv_def]
  \\ rename [‘LIST_REL _ xs ys’]
  \\ Cases_on ‘xs’ \\ Cases_on ‘ys’ \\ gvs []
QED

Theorem v_rel_EVERY_check_type[local]:
  ∀vs ws. LIST_REL (v_rel f) vs ws ∧ EVERY (check_type ty) vs ⇒ vs = ws
Proof
  Induct \\ Cases_on ‘ws’ \\ gvs [] \\ metis_tac [v_rel_check_type]
QED

Theorem v_rel_dest_Litv[local]:
  ∀v1 v2. v_rel f v1 v2 ⇒ dest_Litv v1 = dest_Litv v2
Proof
  Cases \\ gvs [v_rel_simps] \\ rw [] \\ gvs []
QED

Theorem v_rel_do_test[local]:
  v_rel f v1 w1 ∧ v_rel f v2 w2 ⇒ do_test test ty v1 v2 = do_test test ty w1 w2
Proof
  strip_tac
  \\ imp_res_tac v_rel_dest_Litv
  \\ ‘(check_type ty v1 ⇔ check_type ty w1) ∧ (check_type ty v1 ⇒ v1 = w1)’ by
       metis_tac [v_rel_check_type]
  \\ ‘(check_type ty v2 ⇔ check_type ty w2) ∧ (check_type ty v2 ⇒ v2 = w2)’ by
       metis_tac [v_rel_check_type]
  \\ Cases_on ‘test’ \\ gvs [do_test_def]
  \\ rw [] \\ gvs []
QED

(* the values that the primitives build have no locations in them *)
Theorem v_rel_refl[local]:
  (∀l. v_rel f (Litv l) (Litv l)) ∧
  (∀c. v_rel f (Conv c []) (Conv c [])) ∧
  (∀n. v_rel f (nat_to_v n) (nat_to_v n)) ∧
  v_rel f sub_exn_v sub_exn_v ∧ v_rel f chr_exn_v chr_exn_v ∧
  v_rel f div_exn_v div_exn_v
Proof
  gvs [v_rel_simps, semanticPrimitivesTheory.nat_to_v_def,
       semanticPrimitivesTheory.sub_exn_v_def,
       semanticPrimitivesTheory.chr_exn_v_def,
       semanticPrimitivesTheory.div_exn_v_def]
QED

Theorem v_rel_do_arith_res[local]:
  ∀a ty vs x.
    do_arith a ty vs = SOME x ⇒
    (∀e. x = INL e ⇒ v_rel f e e) ∧ (∀v. x = INR v ⇒ v_rel f v v)
Proof
  rpt gen_tac
  \\ Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ gvs [do_arith_def, AllCaseEqs()]
  \\ rw [] \\ gvs [v_rel_refl]
QED

Theorem v_rel_do_conversion_res[local]:
  ∀v ty1 ty2 x.
    do_conversion v ty1 ty2 = SOME x ⇒
    (∀e. x = INL e ⇒ v_rel f e e) ∧ (∀w. x = INR w ⇒ v_rel f w w)
Proof
  rpt gen_tac
  \\ Cases_on ‘ty1’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ Cases_on ‘ty2’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ gvs [do_conversion_def, AllCaseEqs()]
  \\ rw [] \\ gvs [v_rel_refl]
QED

(* the shapes of store contents that do_app reads *)
Theorem state_rel_store_lookup_type[local]:
  state_rel f s1 s2 ∧ FLOOKUP f n = SOME m ⇒
  (∀ws. store_lookup n s1.refs = SOME (W8array ws) ⇒
        store_lookup m s2.refs = SOME (W8array ws)) ∧
  (∀v. store_lookup n s1.refs = SOME (Refv v) ⇒
       ∃w. store_lookup m s2.refs = SOME (Refv w) ∧ v_rel f v w) ∧
  (∀vs. store_lookup n s1.refs = SOME (Varray vs) ⇒
        ∃xs. store_lookup m s2.refs = SOME (Varray xs) ∧
             LIST_REL (v_rel f) vs xs)
Proof
  strip_tac \\ drule_all state_rel_store_lookup \\ strip_tac
  \\ Cases_on ‘sv1’ \\ Cases_on ‘sv2’ \\ gvs []
QED

Theorem state_rel_alloc_fresh[local]:
  state_rel f s1 s2 ∧ sv_rel (v_rel f) sv1 sv2 ⇒
  ∃f'. f ⊑ f' ∧
       state_rel f' (s1 with refs := s1.refs ++ [sv1])
                    (s2 with refs := s2.refs ++ [sv2]) ∧
       FLOOKUP f' (LENGTH s1.refs) = SOME (LENGTH s2.refs)
Proof
  strip_tac \\ drule_all state_rel_alloc \\ strip_tac
  \\ qexists_tac ‘f |+ (LENGTH s1.refs, LENGTH s2.refs)’
  \\ gvs [FLOOKUP_UPDATE]
QED

Theorem state_with_id[local]:
  ((s:'ffi semanticPrimitives$state) with refs := s.refs = s) ∧
  ((s:'ffi semanticPrimitives$state) with <|refs := r; ffi := s.ffi|> =
   s with refs := r)
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

(* thunks, for the Force class of App; the BadRef outcome cannot arise for
   related values, since v_rel only relates locations that state_rel maps *)
Theorem state_rel_dest_thunk[local]:
  state_rel f s1 s2 ∧ LIST_REL (v_rel f) vs ws ⇒
  (∀m v1. dest_thunk vs s1.refs = IsThunk m v1 ⇒
          ∃v2. dest_thunk ws s2.refs = IsThunk m v2 ∧ v_rel f v1 v2) ∧
  (dest_thunk vs s1.refs = NotThunk ⇒ dest_thunk ws s2.refs = NotThunk)
Proof
  strip_tac \\ Cases_on ‘vs’ \\ gvs [dest_thunk_def]
  \\ Cases_on ‘t’ \\ gvs [dest_thunk_def]
  \\ Cases_on ‘h’ \\ gvs [v_rel_simps, dest_thunk_def]
  \\ drule_all state_rel_store_lookup \\ strip_tac
  \\ gvs [] \\ Cases_on ‘sv1’ \\ Cases_on ‘sv2’ \\ gvs []
  \\ rename [‘Thunk md’] \\ Cases_on ‘md’ \\ gvs []
QED

Theorem state_rel_update_thunk[local]:
  state_rel f s1 s2 ∧ LIST_REL (v_rel f) vs ws ∧ LIST_REL (v_rel f) vs' ws' ∧
  update_thunk vs s1.refs vs' = SOME refs1 ⇒
  ∃refs2. update_thunk ws s2.refs ws' = SOME refs2 ∧
          state_rel f (s1 with refs := refs1) (s2 with refs := refs2)
Proof
  strip_tac
  \\ gvs [oneline update_thunk_def, AllCaseEqs()]
  \\ gvs [v_rel_simps]
  \\ rename [‘v_rel f v w’]
  \\ ‘dest_thunk [w] s2.refs = NotThunk’ by
    (irule (cj 2 state_rel_dest_thunk) \\ rpt (first_assum $ irule_at Any)
     \\ gvs [])
  \\ gvs []
  \\ irule state_rel_assign \\ gvs []
  \\ first_assum $ irule_at Any \\ gvs []
QED

Theorem fvs_find_recfun[local]:
  ∀funs g x e.
    find_recfun g funs = SOME (x,e) ⇒ fvs e DELETE Short x ⊆ fvs_funs funs
Proof
  Induct \\ simp [Once find_recfun_def]
  \\ PairCases \\ rw [] \\ gvs [fvs_def, SUBSET_DEF]
  \\ rw [] \\ res_tac \\ gvs []
QED

(* function application: the closure carries exactly the bindings that the
   body's free variables need *)
Theorem do_opapp_v_rel[local]:
  LIST_REL (v_rel f) vs ws ∧ do_opapp vs = SOME (env1,e) ⇒
  ∃env2. do_opapp ws = SOME (env2,e) ∧ env_rel f (fvs e) env1 env2
Proof
  strip_tac
  \\ gvs [semanticPrimitivesPropsTheory.do_opapp_cases, v_rel_simps]
  >~ [‘build_rec_env’] >-
   (rename [‘env_rel f (fvs e)
               (ea with v := nsBind x a (build_rec_env funs ea ea.v))
               (eb with v := nsBind x b (build_rec_env funs eb eb.v))’]
    \\ ‘env_rel f (fvs e DELETE Short x)
          (ea with v := build_rec_env funs ea ea.v)
          (eb with v := build_rec_env funs eb eb.v)’ by
         (irule env_rel_build_rec_env
          \\ qexists_tac ‘fvs_funs funs DIFF set (MAP (Short o FST) funs)’
          \\ gvs [env_rel_def]
          \\ drule fvs_find_recfun \\ gvs [SUBSET_DEF] \\ rw [] \\ res_tac
          \\ gvs [])
    \\ gvs [env_rel_def] \\ rw []
    \\ gvs [namespacePropsTheory.nsLookup_nsBind]
    \\ rename [‘nsLookup _ z = SOME _’] \\ Cases_on ‘z = Short x’ \\ gvs [])
  \\ gvs [env_rel_def] \\ rw []
  \\ gvs [namespacePropsTheory.nsLookup_nsBind]
  \\ rename [‘nsBind y’] \\ Cases_on ‘x = Short y’ \\ gvs []
QED

Theorem do_app_v_rel[local]:
  state_rel f s1 s2 ∧ LIST_REL (v_rel f) vs ws ∧
  do_app (s1.refs,s1.ffi) op vs = SOME ((refs1,ffi1),r) ∧
  r ≠ Rerr (Rabort Rtype_error) ⇒
  ∃f' refs2 ffi2 r'.
    do_app (s2.refs,s2.ffi) op ws = SOME ((refs2,ffi2),r') ∧ f ⊑ f' ∧
    state_rel f' (s1 with <| refs := refs1; ffi := ffi1 |>)
                 (s2 with <| refs := refs2; ffi := ffi2 |>) ∧
    result_rel (v_rel f') (v_rel f') r r'
Proof
  strip_tac
  \\ ‘INJ (FAPPLY f) (FDOM f) UNIV’ by gvs [state_rel_def]
  (* allocating operations: f is extended with the fresh location *)
  \\ Cases_on ‘op = Opref ∨ op = Aw8alloc ∨ op = Aalloc ∨
               op = AallocEmpty ∨ op = AallocFixed’
  >-
   (gvs [semanticPrimitivesPropsTheory.do_app_cases, v_rel_simps,
         store_alloc_def]
    \\ gvs [state_with_id, v_rel_refl]
    (* the negative-length cases raise Subscript and allocate nothing *)
    \\ ((irule state_rel_alloc_fresh \\ gvs [LIST_REL_EL_EQN, EL_REPLICATE])
        ORELSE (qexists_tac ‘f’ \\ gvs [])))
  (* thunk operations either allocate or assign *)
  \\ Cases_on ‘∃th_op. op = ThunkOp th_op’
  >-
   (gvs [semanticPrimitivesPropsTheory.do_app_cases]
    \\ gvs [oneline thunk_op_def, AllCaseEqs(), v_rel_simps, store_alloc_def]
    \\ gvs [state_with_id, v_rel_refl]
    >~ [‘store_assign’] >-
     (qexists_tac ‘f’ \\ gvs []
      \\ irule state_rel_assign
      \\ qpat_assum ‘store_assign _ _ s1.refs = SOME _’ $ irule_at Any
      \\ gvs [])
    \\ irule state_rel_alloc_fresh \\ gvs [])
  (* equality and the comparisons *)
  \\ Cases_on ‘op = Equality ∨ ∃t ty. op = Test t ty’
  >-
   (gvs [semanticPrimitivesPropsTheory.do_app_cases, v_rel_simps]
    \\ qexists_tac ‘f’ \\ gvs [state_with_id, v_rel_refl]
    \\ imp_res_tac v_rel_do_test
    \\ metis_tac [cj 1 v_rel_do_eq])
  (* arithmetic and conversions: the arguments are literals, hence equal *)
  \\ Cases_on ‘(∃a ty. op = Arith a ty) ∨ ∃ty1 ty2. op = FromTo ty1 ty2’
  >-
   (gvs [semanticPrimitivesPropsTheory.do_app_cases, v_rel_simps]
    \\ qexists_tac ‘f’ \\ gvs [state_with_id, v_rel_refl]
    \\ imp_res_tac v_rel_EVERY_check_type
    \\ imp_res_tac v_rel_check_type
    \\ imp_res_tac v_rel_do_arith_res
    \\ imp_res_tac v_rel_do_conversion_res
    \\ gvs [state_with_id, v_rel_refl]
    \\ CASE_TAC \\ gvs [state_with_id])
  (* foreign calls: the byte arrays and the ffi states are equal *)
  \\ Cases_on ‘∃n. op = FFI n’
  >-
   (‘s1.ffi = s2.ffi’ by gvs [state_rel_def]
    \\ gvs [semanticPrimitivesPropsTheory.do_app_cases, v_rel_simps]
    \\ imp_res_tac state_rel_store_lookup_type \\ gvs []
    \\ qexists_tac ‘f’ \\ gvs [state_with_id, v_rel_refl]
    \\ gvs [AllCaseEqs()]
    >~ [‘store_assign m2 (W8array bs) s2.refs’] >-
     (‘∃refs2. store_assign m2 (W8array bs) s2.refs = SOME refs2 ∧
               state_rel f (s1 with refs := refs1) (s2 with refs := refs2)’ by
        (irule state_rel_assign
         \\ qpat_assum ‘store_assign _ _ s1.refs = SOME _’ $ irule_at Any
         \\ gvs [])
      \\ gvs [] \\ gvs [state_rel_def, v_rel_refl])
    \\ gvs [state_rel_def])
  (* everything else leaves f and the store alone, except for the
     operations that assign to an existing location *)
  \\ gvs [semanticPrimitivesPropsTheory.do_app_cases, v_rel_simps]
  \\ qexists_tac ‘f’
  \\ gvs [state_with_id, v_rel_refl]
  \\ imp_res_tac state_rel_store_lookup_type \\ gvs []
  \\ gvs [SF DNF_ss, state_with_id, v_rel_refl]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ imp_res_tac v_rel_v_to_list
  \\ imp_res_tac v_rel_v_to_char_list
  \\ gvs [OPTREL_def, state_with_id, v_rel_refl]
  \\ imp_res_tac v_rel_vs_to_string
  \\ gvs [state_with_id, v_rel_refl]
  \\ gvs [LIST_REL_EL_EQN]
  >~ [‘MAP (λc. Litv (Char c))’] >-
   (irule v_rel_list_to_v \\ gvs [LIST_REL_EL_EQN, EL_MAP, v_rel_refl])
  >~ [‘list_to_v (_ ++ _)’] >-
   (irule v_rel_list_to_v \\ irule EVERY2_APPEND_suff \\ gvs [LIST_REL_EL_EQN])
  \\ irule state_rel_assign
  \\ qpat_assum ‘store_assign _ _ s1.refs = SOME _’ $ irule_at Any
  \\ gvs [LIST_REL_EL_EQN, EL_LUPDATE] \\ rw [] \\ gvs []
QED

Theorem evaluate_v_rel[local]:
  (∀(s1:'ffi semanticPrimitives$state) env1 es s1' res1.
     evaluate s1 env1 es = (s1',res1) ∧
     res1 ≠ Rerr (Rabort Rtype_error) ⇒
     ∀f s2 env2.
       state_rel f s1 s2 ∧ env_rel f (fvs_list es) env1 env2 ⇒
       ∃f' s2' res2.
         evaluate s2 env2 es = (s2',res2) ∧ f ⊑ f' ∧
         state_rel f' s1' s2' ∧
         result_rel (LIST_REL (v_rel f')) (v_rel f') res1 res2) ∧
  (∀(s1:'ffi semanticPrimitives$state) env1 v1 pes err_v1 s1' res1.
     evaluate_match s1 env1 v1 pes err_v1 = (s1',res1) ∧
     res1 ≠ Rerr (Rabort Rtype_error) ⇒
     ∀f s2 env2 v2 err_v2.
       state_rel f s1 s2 ∧ env_rel f (fvs_pes pes) env1 env2 ∧
       v_rel f v1 v2 ∧ v_rel f err_v1 err_v2 ⇒
       ∃f' s2' res2.
         evaluate_match s2 env2 v2 pes err_v2 = (s2',res2) ∧ f ⊑ f' ∧
         state_rel f' s1' s2' ∧
         result_rel (LIST_REL (v_rel f')) (v_rel f') res1 res2)
Proof
  ho_match_mp_tac evaluate_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  >~ [‘evaluate _ _ []’]                >- suspend "empty"
  >~ [‘e1::e2::es’]                     >- suspend "cons"
  >~ [‘Lit l’]                          >- suspend "Lit"
  >~ [‘Raise e’]                        >- suspend "Raise"
  >~ [‘Handle e pes’]                   >- suspend "Handle"
  >~ [‘Con cn es’]                      >- suspend "Con"
  >~ [‘Var n’]                          >- suspend "Var"
  >~ [‘Fun n e’]                        >- suspend "Fun"
  >~ [‘App op es’]                      >- suspend "App"
  >~ [‘Log lop e1 e2’]                  >- suspend "Log"
  >~ [‘If e1 e2 e3’]                    >- suspend "If"
  >~ [‘Mat e pes’]                      >- suspend "Mat"
  >~ [‘Let xo e1 e2’]                   >- suspend "Let"
  >~ [‘Letrec funs e’]                  >- suspend "Letrec"
  >~ [‘Tannot e t’]                     >- suspend "Tannot"
  >~ [‘Lannot e l’]                     >- suspend "Lannot"
  >~ [‘evaluate_match _ _ _ [] _’]      >- suspend "match_empty"
  >~ [‘evaluate_match _ _ _ ((p,e)::pes) _’] >- suspend "match_cons"
QED

Resume evaluate_v_rel[empty]:
  gvs [evaluate_def] \\ qexists_tac ‘f’ \\ gvs []
QED

Resume evaluate_v_rel[cons]:
  gvs [evaluate_def, CaseEq "prod"]
  \\ rename [‘evaluate s1 env1 [e1] = (st1,r1)’]
  \\ Cases_on ‘r1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘env2’ mp_tac
  \\ impl_tac
  >- (drule_then irule env_rel_mono \\ simp [fvs_def])
  \\ strip_tac \\ fs []
  \\ reverse $ Cases_on ‘r1’ \\ gvs [CaseEq"prod", PULL_EXISTS]
  >- (pop_assum $ irule_at Any \\ simp [])
  \\ Cases_on ‘v2 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘env2’ mp_tac
  \\ impl_tac
  >- (drule_then irule env_rel_mono \\ simp [fvs_def]
      \\ simp [SUBSET_DEF])
  \\ strip_tac \\ gvs []
  \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
  \\ gvs [AllCaseEqs()]
  \\ qpat_x_assum ‘state_rel _ _ _’ $ irule_at Any
  \\ gvs [] \\ imp_res_tac SUBMAP_TRANS \\ simp []
  \\ drule_then irule v_rel_submap \\ simp []
QED

Resume evaluate_v_rel[Lit]:
  gvs [evaluate_def] \\ qexists_tac ‘f’ \\ gvs [v_rel_Litv]
QED

Resume evaluate_v_rel[Raise]:
  gvs [evaluate_def, AllCaseEqs (), fvs_def]
  \\ last_x_assum drule \\ gvs [] \\ disch_then drule_all \\ strip_tac
  \\ gvs [] \\ first_x_assum $ irule_at Any \\ gvs []
  \\ imp_res_tac evaluate_length \\ gvs [LENGTH_EQ_NUM_compute]
QED

Resume evaluate_v_rel[Handle]:
  gvs [evaluate_def, CaseEq "prod"]
  \\ rename [‘evaluate s1 env1 [e] = (st1,r1)’]
  \\ Cases_on ‘r1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘env2’ mp_tac)
  \\ impl_tac
  >- (drule_then irule env_rel_mono \\ simp [fvs_def, SUBSET_DEF])
  \\ strip_tac \\ fs []
  \\ Cases_on ‘r1’
  \\ gvs [CaseEq"prod", CaseEq"bool", CaseEq"error_result", PULL_EXISTS]
  >- (pop_assum $ irule_at Any \\ simp [])
  >- (‘env1.c = env2.c’ by gvs [env_rel_def]
      \\ ‘can_pmatch_all env2.c s2'.refs (MAP FST pes) v'’ by
           (irule can_pmatch_all_v_rel
            \\ first_assum $ irule_at Any \\ gvs [state_rel_def] \\ metis_tac [])
      \\ gvs []
      \\ last_x_assum drule
      \\ disch_then (qspecl_then [‘env2’,‘v'’,‘v'’] mp_tac)
      \\ impl_tac
      >- (gvs [] \\ drule_then irule env_rel_mono \\ simp [fvs_def, SUBSET_DEF])
      \\ strip_tac \\ gvs []
      \\ first_assum $ irule_at Any \\ imp_res_tac SUBMAP_TRANS \\ simp [])
  \\ first_assum $ irule_at Any \\ simp []
QED

Resume evaluate_v_rel[Con]:
  gvs [evaluate_def, CaseEq "prod", CaseEq "bool"]
  \\ rename [‘evaluate s1 env1 _ = (st1,r1)’]
  \\ Cases_on ‘r1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘env2’ mp_tac
  \\ impl_tac
  >- (drule_then irule env_rel_mono \\ simp [fvs_def])
  \\ strip_tac
  \\ ‘env1.c = env2.c’ by gvs [env_rel_def]
  \\ ‘do_con_check env2.c cn (LENGTH es)’ by
       gvs []
  \\ gvs []
  \\ reverse $ Cases_on ‘r1’ \\ gvs []
  >- (first_assum $ irule_at Any \\ simp [])
  \\ gvs [AllCaseEqs()]
  \\ drule build_conv_thm \\ strip_tac \\ gvs []
  \\ simp [Once v_rel_cases]
  \\ first_assum $ irule_at Any \\ simp []
QED

Resume evaluate_v_rel[Var]:
  gvs [evaluate_def, AllCaseEqs (), env_rel_def, fvs_def]
  \\ qexists_tac ‘f’ \\ gvs []
QED

Resume evaluate_v_rel[Fun]:
  gvs [evaluate_def] \\ qexists_tac ‘f’ \\ gvs []
  \\ irule v_rel_Closure \\ gvs [env_rel_def, fvs_def]
QED

Resume evaluate_v_rel[App]:
  rename [‘evaluate s1 env1 [App op es] = (s2,r2)’]
  \\ qpat_x_assum ‘evaluate s1 env1 [App op es] = (s2,r2)’ mp_tac
  \\ rewrite_tac [evaluate_def]
  \\ Cases_on ‘evaluate s1 env1 (REVERSE es)’
  \\ qabbrev_tac ‘cl = getOpClass’ \\ gvs []
  \\ strip_tac
  \\ Cases_on ‘r = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘env2’ mp_tac
  \\ impl_tac
  >-
   (irule env_rel_mono
    \\ irule_at Any SUBMAP_REFL
    \\ first_x_assum $ irule_at Any
    \\ gvs [fvs_def])
  \\ strip_tac
  \\ simp []
  \\ reverse $ Cases_on ‘r’ \\ gvs []
  >- (pop_assum $ irule_at Any \\ gvs [])
  \\ Cases_on ‘op = Eval’
  >-
   (gvs [Abbr‘cl’]
    \\ gvs [do_eval_res_def]
    \\ qsuff_tac ‘do_eval (REVERSE a) q.eval_state = NONE’
    >- (strip_tac \\ gvs [])
    \\ simp [do_eval_def, AllCaseEqs(), PULL_EXISTS]
    \\ qpat_x_assum ‘_ = (s2,r2)’ kall_tac
    \\ ‘∀x. q.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev’ by fs [state_rel_def]
    \\ Cases_on ‘q.eval_state’ \\ gvs []
    \\ Cases_on ‘a’ using SNOC_CASES
    \\ full_simp_tac std_ss [REVERSE_SNOC]
    \\ simp [] \\ Cases_on ‘x’ \\ gvs []
    \\ gvs [LIST_REL_SNOC]
    \\ fs [Once v_rel_cases])
  (* name the two evaluations and the extended map, so that nothing below
     depends on the variable names gvs happened to invent *)
  \\ rename [‘evaluate _ env1 (REVERSE es) = (t1,Rval _)’,
             ‘evaluate _ env2 (REVERSE es) = (t2,Rval _)’,
             ‘state_rel g t1 t2’, ‘LIST_REL (v_rel g) xs ys’]
  \\ ‘LIST_REL (v_rel g) (REVERSE xs) (REVERSE ys)’ by gvs [LIST_REL_REVERSE_EQ]
  \\ ‘t1.clock = t2.clock’ by gvs [state_rel_def]
  \\ Cases_on ‘cl op’ \\ gvs []
  (* EvalOp is only reachable for op = Eval, which is done above *)
  >-
   (qpat_x_assum ‘cl op = EvalOp’ mp_tac \\ gvs [Abbr‘cl’]
    \\ Cases_on ‘op’ \\ gvs [] \\ rw [])
  (* function application *)
  >-
   (gvs [AllCaseEqs()]
    \\ rename [‘do_opapp (REVERSE xs) = SOME (envA,e)’]
    \\ ‘LIST_REL (v_rel g) (REVERSE xs) (REVERSE ys)’ by
         gvs [LIST_REL_REVERSE_EQ]
    \\ drule_all do_opapp_v_rel \\ strip_tac
    \\ rename [‘do_opapp (REVERSE ys) = SOME (envB,e)’]
    \\ gvs []
    >- (first_assum $ irule_at Any \\ gvs [])
    \\ ‘state_rel g (dec_clock t1) (dec_clock t2) ∧
        env_rel g (fvs_list [e]) envA envB’ by
         gvs [state_rel_def, evaluateTheory.dec_clock_def, fvs_def]
    \\ last_x_assum drule_all \\ strip_tac \\ gvs []
    \\ first_assum $ irule_at Any
    \\ imp_res_tac SUBMAP_TRANS \\ gvs [])
  (* forcing a thunk *)
  >-
   (‘LIST_REL (v_rel g) (REVERSE xs) (REVERSE ys)’ by gvs [LIST_REL_REVERSE_EQ]
    \\ drule_all state_rel_dest_thunk \\ strip_tac
    \\ gvs [AllCaseEqs()]
    >- (first_assum $ irule_at Any \\ gvs [])
    \\ rename [‘dest_thunk (REVERSE ys) t2.refs = IsThunk NotEvaluated w’,
               ‘do_opapp [v; Conv NONE []] = SOME (envA,e)’]
    \\ ‘LIST_REL (v_rel g) [v; Conv NONE []] [w; Conv NONE []]’ by
         gvs [v_rel_refl]
    \\ drule_all do_opapp_v_rel \\ strip_tac
    \\ rename [‘do_opapp [w; Conv NONE []] = SOME (envB,e)’]
    \\ gvs []
    >- (first_assum $ irule_at Any \\ gvs [])
    \\ ‘state_rel g (dec_clock t1) (dec_clock t2) ∧
        env_rel g (fvs_list [e]) envA envB’ by
         gvs [state_rel_def, evaluateTheory.dec_clock_def, fvs_def]
    \\ last_x_assum drule_all \\ strip_tac \\ gvs []
    >-
     (rename [‘state_rel h u1 u2’]
      \\ ‘LIST_REL (v_rel h) (REVERSE xs) (REVERSE ys)’ by
           (gvs [LIST_REL_EL_EQN, LIST_REL_REVERSE_EQ] \\ rw []
            \\ metis_tac [v_rel_submap])
      \\ drule_all state_rel_update_thunk \\ strip_tac
      \\ gvs [] \\ first_assum $ irule_at Any \\ gvs []
      \\ imp_res_tac SUBMAP_TRANS \\ gvs [])
    \\ first_assum $ irule_at Any \\ imp_res_tac SUBMAP_TRANS \\ gvs [])
  (* the simple operations *)
  \\ gvs [AllCaseEqs()]
  \\ ‘LIST_REL (v_rel g) (REVERSE xs) (REVERSE ys)’ by gvs [LIST_REL_REVERSE_EQ]
  \\ drule_all do_app_v_rel
  \\ strip_tac \\ gvs []
  \\ first_assum $ irule_at Any
  \\ imp_res_tac SUBMAP_TRANS \\ gvs []
  \\ rename [‘list_result res1’] \\ Cases_on ‘res1’ \\ gvs [list_result_def]
QED

Resume evaluate_v_rel[Log]:
  gvs [evaluate_def, CaseEq "prod"]
  \\ rename [‘evaluate s1 env1 [e1] = (st1,r1)’]
  \\ Cases_on ‘r1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘env2’ mp_tac
  \\ impl_tac
  >- (drule_then irule env_rel_mono \\ simp [fvs_def])
  \\ strip_tac \\ fs []
  \\ reverse $ Cases_on ‘r1’ \\ gvs [CaseEq"prod", PULL_EXISTS]
  >- (pop_assum $ irule_at Any \\ simp [])
  \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
  \\ ‘v = v''’ by (qpat_x_assum ‘_ = (s1',res1)’ mp_tac
                   \\ rw [do_log_def, AllCaseEqs()] \\ gvs [])
  \\ gvs []
  \\ Cases_on ‘do_log lop v e2’ \\ fs []
  \\ rename [‘do_log lop v e2 = SOME x’] \\ Cases_on ‘x’ \\ fs []
  >- (first_x_assum drule
      \\ disch_then $ qspec_then ‘env2’ mp_tac
      \\ impl_tac
      >- (drule_then irule env_rel_mono \\ simp [fvs_def]
          \\ gvs [do_log_def, AllCaseEqs()] \\ simp [SUBSET_DEF])
      \\ strip_tac \\ fs []
      \\ first_assum $ irule_at Any \\ imp_res_tac SUBMAP_TRANS \\ simp [])
  \\ qexists_tac ‘f'’ \\ gvs [do_log_def, AllCaseEqs()]
QED

Resume evaluate_v_rel[If]:
  gvs [evaluate_def, CaseEq "prod"]
  \\ rename [‘evaluate s1 env1 [e1] = (st1,r1)’]
  \\ Cases_on ‘r1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘env2’ mp_tac
  \\ impl_tac
  >- (drule_then irule env_rel_mono \\ simp [fvs_def, SUBSET_DEF])
  \\ strip_tac \\ fs []
  \\ reverse $ Cases_on ‘r1’ \\ gvs [CaseEq"prod", PULL_EXISTS]
  >- (pop_assum $ irule_at Any \\ simp [])
  \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ gvs []
  \\ ‘v = v''’ by (qpat_x_assum ‘_ = (s1',res1)’ mp_tac
                   \\ rw [do_if_def, AllCaseEqs()] \\ gvs [])
  \\ gvs []
  \\ Cases_on ‘do_if v e2 e3’ \\ fs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘env2’ mp_tac
  \\ impl_tac
  >- (drule_then irule env_rel_mono \\ simp [fvs_def]
      \\ gvs [do_if_def, AllCaseEqs()] \\ simp [SUBSET_DEF])
  \\ strip_tac \\ fs []
  \\ first_assum $ irule_at Any \\ imp_res_tac SUBMAP_TRANS \\ simp []
QED

Resume evaluate_v_rel[Mat]:
  gvs [evaluate_def, CaseEq "prod"]
  \\ rename [‘evaluate s1 env1 [e] = (st1,r1)’]
  \\ Cases_on ‘r1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then ‘env2’ mp_tac)
  \\ impl_tac
  >- (drule_then irule env_rel_mono \\ simp [fvs_def, SUBSET_DEF])
  \\ strip_tac \\ fs []
  \\ reverse $ Cases_on ‘r1’ \\ gvs [CaseEq"prod", CaseEq"bool", PULL_EXISTS]
  >- (pop_assum $ irule_at Any \\ simp [])
  \\ imp_res_tac evaluate_length \\ gvs [LENGTH_EQ_NUM_compute]
  \\ ‘env1.c = env2.c’ by gvs [env_rel_def]
  \\ ‘can_pmatch_all env2.c s2'.refs (MAP FST pes) h’ by
       (irule can_pmatch_all_v_rel
        \\ first_assum $ irule_at Any \\ gvs [state_rel_def] \\ metis_tac [])
  \\ gvs []
  \\ last_x_assum drule
  \\ disch_then (qspecl_then [‘env2’,‘h’,‘bind_exn_v’] mp_tac)
  \\ impl_tac
  >- (gvs [] \\ drule_then irule env_rel_mono \\ simp [fvs_def, SUBSET_DEF])
  \\ strip_tac \\ gvs []
  \\ first_assum $ irule_at Any \\ imp_res_tac SUBMAP_TRANS \\ simp []
QED

Resume evaluate_v_rel[Let]:
  gvs [evaluate_def, CaseEq "prod"]
  \\ rename [‘evaluate s1 env1 [e1] = (st1,r1)’]
  \\ Cases_on ‘r1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule
  \\ disch_then $ qspec_then ‘env2’ mp_tac
  \\ impl_tac
  >- (drule_then irule env_rel_mono
      \\ Cases_on ‘xo’ \\ simp [fvs_def, SUBSET_DEF])
  \\ strip_tac \\ fs []
  \\ reverse $ Cases_on ‘r1’ \\ gvs [CaseEq"prod", PULL_EXISTS]
  >- (pop_assum $ irule_at Any \\ simp [])
  \\ imp_res_tac evaluate_length \\ gvs [LENGTH_EQ_NUM_compute]
  \\ rename [‘v_rel f1 v1 v2’]
  \\ last_x_assum $ qspecl_then
       [‘f1’,‘s2'’,‘env2 with v := nsOptBind xo v2 env2.v’] mp_tac
  \\ impl_tac
  >- (simp [] \\ irule env_rel_nsOptBind \\ conj_tac >- simp []
      \\ qexists_tac ‘fvs_list [Let xo e1 e2]’ \\ conj_tac
      >- (Cases_on ‘xo’ \\ gvs [fvs_def, SUBSET_DEF])
      \\ drule_then irule env_rel_mono \\ simp [])
  \\ strip_tac \\ fs []
  \\ first_assum $ irule_at Any \\ imp_res_tac SUBMAP_TRANS \\ simp []
QED

Resume evaluate_v_rel[Letrec]:
  gvs [evaluate_def, AllCaseEqs()]
  \\ last_x_assum drule \\ gvs []
  \\ disch_then $ qspec_then ‘env2 with v := build_rec_env funs env2 env2.v’
       mp_tac
  \\ impl_tac
  >- (irule env_rel_build_rec_env
      \\ qexists_tac ‘fvs_list [Letrec funs e]’ \\ gvs [fvs_def]
      \\ gvs [SUBSET_DEF])
  \\ strip_tac \\ gvs []
  \\ first_assum $ irule_at Any \\ gvs []
QED

Resume evaluate_v_rel[Tannot]:
  gvs [evaluate_def, fvs_def] \\ last_x_assum irule \\ gvs [fvs_def]
QED

Resume evaluate_v_rel[Lannot]:
  gvs [evaluate_def, fvs_def] \\ last_x_assum irule \\ gvs [fvs_def]
QED

Resume evaluate_v_rel[match_empty]:
  gvs [evaluate_def] \\ qexists_tac ‘f’ \\ gvs []
QED

Resume evaluate_v_rel[match_cons]:
  gvs [evaluate_def, CaseEq "bool"]
  \\ ‘env1.c = env2.c’ by gvs [env_rel_def]
  \\ qspecl_then [‘env1.c’,‘s1.refs’,‘p’,‘v1’,‘[]’,‘s2.refs’,‘v2’,
                  ‘[]’,‘f’] mp_tac (cj 1 pmatch_v_rel)
  \\ impl_tac >- gvs [state_rel_def]
  \\ Cases_on ‘pmatch env1.c s1.refs p v1 []’ \\ gvs []
  >- (strip_tac \\ gvs []
      \\ last_x_assum irule \\ gvs []
      \\ drule_then irule env_rel_mono \\ simp [fvs_def, SUBSET_DEF])
  \\ strip_tac \\ gvs []
  \\ imp_res_tac (cj 1 pmatch_extend) \\ gvs []
  \\ last_x_assum irule \\ gvs []
  \\ irule env_rel_nsAppend \\ conj_tac >- simp []
  \\ qexists_tac ‘fvs_pes ((p,e)::pes)’ \\ simp []
  \\ gvs [fvs_def, SUBSET_DEF, MAP_MAP_o]
  \\ qpat_x_assum ‘MAP FST a = pat_bindings p’ (assume_tac o GSYM)
  \\ gvs [MAP_MAP_o]
QED

Finalise evaluate_v_rel[local]

(* evaluation of a pure expression only extends the store *)

Definition pure_st_def:
  pure_st (s:'ffi semanticPrimitives$state) s' ⇔
    s'.clock = s.clock ∧ s'.ffi = s.ffi ∧
    s'.next_type_stamp = s.next_type_stamp ∧
    s'.next_exn_stamp = s.next_exn_stamp ∧
    ((∀x. s.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev) ⇒
     (∀x. s'.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev)) ∧
    ∃extra. s'.refs = s.refs ++ extra
End

Theorem pure_st_refl[local,simp]:
  pure_st s s
Proof
  gvs [pure_st_def]
QED

Theorem pure_st_trans[local]:
  pure_st s1 s2 ∧ pure_st s2 s3 ⇒ pure_st s1 s3
Proof
  gvs [pure_st_def] \\ rw [] \\ gvs []
QED

Theorem state_rel_pure_st[local]:
  state_rel f s1 s2 ∧ pure_st s1 s1' ⇒ state_rel f s1' s2
Proof
  gvs [pure_st_def, state_rel_def] \\ rw [] \\ res_tac \\ gvs []
  \\ gvs [store_lookup_def, EL_APPEND1]
  \\ res_tac \\ gvs []
  \\ first_x_assum drule \\ strip_tac \\ gvs []
QED

Theorem pure_op_do_app[local]:
  pure_op op ∧ do_app (refs,ffi) op vs = SOME ((refs',ffi'),r) ⇒
  refs' = refs ∧ ffi' = ffi ∧ ∃v. r = Rval v
Proof
  Cases_on ‘op’ \\ gvs [pure_op_def, do_app_def, AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
  \\ gvs [do_arith_def, do_conversion_def, AllCaseEqs()]
  >~ [‘do_conversion v ty1 ty2’]
  >- (Cases_on ‘ty1’ \\ Cases_on ‘ty2’
      \\ gvs [do_conversion_def, AllCaseEqs()]
      \\ Cases_on ‘w’ \\ gvs [do_conversion_def, AllCaseEqs()])
  \\ Cases_on ‘p’ \\ gvs [do_arith_def, AllCaseEqs()]
  \\ Cases_on ‘w’ \\ gvs [do_arith_def, AllCaseEqs()]
QED

Theorem alloc_op_do_app[local]:
  alloc_op op ∧ do_app (refs,ffi) op vs = SOME ((refs',ffi'),r) ⇒
  ffi' = ffi ∧ (∃extra. refs' = refs ++ extra) ∧ ∃v. r = Rval v
Proof
  strip_tac \\ gvs [alloc_op_def, AllCaseEqs()]
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, thunk_op_def]
QED

Theorem alloc_len_do_app[local]:
  do_app (refs,ffi) op (Litv (IntLit n)::rest) = SOME ((refs',ffi'),r) ∧
  (op = Aalloc ∨ op = Aw8alloc) ∧ 0 ≤ n ⇒
  ffi' = ffi ∧ (∃extra. refs' = refs ++ extra) ∧ ∃v. r = Rval v
Proof
  strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def]
  \\ intLib.COOPER_TAC
QED

Theorem dest_int_lit_thm[local]:
  ∀e n s env s' res.
    dest_int_lit e = SOME n ∧ evaluate s env [e] = (s',res) ⇒
    res = Rval [Litv (IntLit n)] ∧ s' = s
Proof
  ho_match_mp_tac dest_int_lit_ind
  \\ gvs [dest_int_lit_def, evaluate_def, AllCaseEqs()]
QED

Theorem alloc_app_do_app[local]:
  alloc_app op es ∧ evaluate s env (REVERSE es) = (st',Rval vs) ∧
  do_app (st'.refs,st'.ffi) op (REVERSE vs) = SOME ((refs,ffi),r) ⇒
  ffi = st'.ffi ∧ (∃extra. refs = st'.refs ++ extra) ∧ ∃v. r = Rval v
Proof
  strip_tac \\ gvs [alloc_app_def]
  >- (drule_all alloc_op_do_app \\ strip_tac \\ gvs [])
  \\ Cases_on ‘es’ \\ gvs [AllCaseEqs()]
  \\ gvs [evaluate_append, AllCaseEqs()]
  \\ Cases_on ‘dest_int_lit h’ \\ gvs []
  \\ drule dest_int_lit_thm \\ disch_then drule \\ strip_tac \\ gvs []
  \\ gvs [REVERSE_APPEND]
  \\ drule alloc_len_do_app \\ simp [] \\ strip_tac \\ gvs []
QED

(* a total pattern always matches *)
Theorem total_pat_pmatch[local]:
  (∀envC refs p v bs. total_pat p ⇒ pmatch envC refs p v bs ≠ No_match) ∧
  (∀envC refs ps vs bs.
     total_pat_list ps ⇒ pmatch_list envC refs ps vs bs ≠ No_match)
Proof
  ho_match_mp_tac pmatch_ind \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  \\ gvs [pmatch_def, total_pat_def, AllCaseEqs()]
QED

Theorem pure_exp_list_APPEND[local]:
  ∀xs ys. pure_exp_list (xs++ys) ⇔ pure_exp_list xs ∧ pure_exp_list ys
Proof
  Induct \\ gvs [pure_exp_def] \\ metis_tac []
QED

Theorem pure_exp_list_REVERSE[local,simp]:
  ∀es. pure_exp_list (REVERSE es) ⇔ pure_exp_list es
Proof
  Induct \\ gvs [pure_exp_def, pure_exp_list_APPEND] \\ metis_tac []
QED

Theorem pure_exp_evaluate[local]:
  (∀(s:'ffi semanticPrimitives$state) env es s' res.
     evaluate s env es = (s',res) ∧ pure_exp_list es ∧
     res ≠ Rerr (Rabort Rtype_error) ⇒
     (∃vs. res = Rval vs) ∧ pure_st s s') ∧
  (∀(s:'ffi semanticPrimitives$state) env v pes err_v s' res.
     evaluate_match s env v pes err_v = (s',res) ∧ pure_exp_pes pes ∧
     EXISTS total_pat (MAP FST pes) ∧
     res ≠ Rerr (Rabort Rtype_error) ⇒
     (∃vs. res = Rval vs) ∧ pure_st s s')
Proof
  ho_match_mp_tac evaluate_ind \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >~ [‘App op es’]
  >- (‘getOpClass op = Simple’ by
        (Cases_on ‘op’
         \\ gvs [pure_exp_def, pure_op_def, alloc_app_def, alloc_op_def]
         \\ Cases_on ‘t’
         \\ gvs [pure_exp_def, pure_op_def, alloc_app_def, alloc_op_def])
      \\ gvs [pure_exp_def]
      \\ reverse (Cases_on ‘pure_op op’) \\ gvs []
      >- (gvs [evaluate_def, pure_exp_list_REVERSE, AllCaseEqs()]
          \\ drule_all pure_op_do_app \\ strip_tac \\ gvs [pure_st_def])
      \\ gvs [evaluate_def, pure_exp_list_REVERSE, AllCaseEqs()]
      \\ drule_all alloc_app_do_app \\ strip_tac \\ gvs [pure_st_def])
  \\ gvs [evaluate_def, pure_exp_def, pure_st_refl, pure_exp_list_REVERSE,
          AllCaseEqs()]
  \\ imp_res_tac pure_st_trans \\ gvs []
  \\ gvs [do_log_def, do_if_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
  \\ metis_tac [cj 1 total_pat_pmatch]
QED

(* pruning a pattern only drops bindings that are unused *)

Theorem prune_pat_list_LENGTH[local,simp]:
  ∀used ps. LENGTH (prune_pat_list used ps) = LENGTH ps
Proof
  Induct_on ‘ps’ \\ gvs [prune_pat_def]
QED

Theorem prune_pat_bindings[local]:
  (∀p used.
     set (pat_bindings (prune_pat used p)) ⊆ set (pat_bindings p) ∧
     (ALL_DISTINCT (pat_bindings p) ⇒
      ALL_DISTINCT (pat_bindings (prune_pat used p)))) ∧
  (∀ps used.
     set (pats_bindings (prune_pat_list used ps)) ⊆ set (pats_bindings ps) ∧
     (ALL_DISTINCT (pats_bindings ps) ⇒
      ALL_DISTINCT (pats_bindings (prune_pat_list used ps))))
Proof
  ho_match_mp_tac astTheory.pat_induction
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  \\ gvs [prune_pat_def, astTheory.pat_bindings_def, ALL_DISTINCT_APPEND]
  \\ rw [] \\ gvs [prune_pat_def, astTheory.pat_bindings_def,
                   ALL_DISTINCT_APPEND]
  \\ gvs [SUBSET_DEF] \\ metis_tac []
QED

(* the bindings of a pruned pattern are those of the original, restricted
   to the names that are used *)
Definition binds_rel_def:
  binds_rel f used bs1 bs2 ⇔
    (∀x. MEM x (MAP FST bs2) ⇒ MEM x (MAP FST bs1)) ∧
    ∀x v1. Short x ∈ names_set used ∧ ALOOKUP bs1 x = SOME v1 ⇒
           ∃v2. ALOOKUP bs2 x = SOME v2 ∧ v_rel f v1 v2
End

Theorem binds_rel_cons_unused[local]:
  binds_rel f used bs1 bs2 ∧ ¬is_used used x ⇒
  binds_rel f used ((x,v1)::bs1) bs2
Proof
  gvs [binds_rel_def, is_used_names_set] \\ rw [] \\ gvs []
  \\ Cases_on ‘x = x'’ \\ gvs []
QED

Theorem binds_rel_cons[local]:
  binds_rel f used bs1 bs2 ∧ v_rel f v1 v2 ⇒
  binds_rel f used ((x,v1)::bs1) ((x,v2)::bs2)
Proof
  gvs [binds_rel_def] \\ rw [] \\ gvs []
  \\ Cases_on ‘x = x'’ \\ gvs []
QED

Theorem pmatch_prune_pat[local]:
  (∀envC refs1 p v1 bs1 refs2 v2 bs2 f used.
     v_rel f v1 v2 ∧ binds_rel f used bs1 bs2 ∧
     (∀loc1 loc2.
        FLOOKUP f loc1 = SOME loc2 ⇒
        ∃sv1 sv2.
          store_lookup loc1 refs1 = SOME sv1 ∧
          store_lookup loc2 refs2 = SOME sv2 ∧ sv_rel (v_rel f) sv1 sv2) ⇒
     case pmatch envC refs1 p v1 bs1 of
     | Match bs1' =>
         ∃bs2'. pmatch envC refs2 (prune_pat used p) v2 bs2 = Match bs2' ∧
                binds_rel f used bs1' bs2'
     | No_match => pmatch envC refs2 (prune_pat used p) v2 bs2 = No_match
     | _ => T) ∧
  (∀envC refs1 ps vs1 bs1 refs2 vs2 bs2 f used.
     LIST_REL (v_rel f) vs1 vs2 ∧ binds_rel f used bs1 bs2 ∧
     (∀loc1 loc2.
        FLOOKUP f loc1 = SOME loc2 ⇒
        ∃sv1 sv2.
          store_lookup loc1 refs1 = SOME sv1 ∧
          store_lookup loc2 refs2 = SOME sv2 ∧ sv_rel (v_rel f) sv1 sv2) ⇒
     case pmatch_list envC refs1 ps vs1 bs1 of
     | Match bs1' =>
         ∃bs2'.
           pmatch_list envC refs2 (prune_pat_list used ps) vs2 bs2 =
             Match bs2' ∧ binds_rel f used bs1' bs2'
     | No_match =>
         pmatch_list envC refs2 (prune_pat_list used ps) vs2 bs2 = No_match
     | _ => T)
Proof
  ho_match_mp_tac pmatch_ind \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  >~ [‘pmatch envC refs1 (Pvar x) v1 bs1’]
  >- (gvs [pmatch_def, prune_pat_def] \\ rw [] \\ gvs [pmatch_def]
      >- (irule binds_rel_cons \\ gvs [])
      \\ irule binds_rel_cons_unused \\ gvs [])
  >~ [‘pmatch envC refs1 (Plit l) (Litv l') bs1’]
  >- (qpat_x_assum ‘v_rel _ _ _’ (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once v_rel_cases])
      \\ gvs [pmatch_def, prune_pat_def] \\ rw [] \\ gvs [pmatch_def])
  >~ [‘pmatch envC refs1 (Pcon (SOME n) ps) (Conv (SOME stamp') vs1) bs1’]
  >- (qpat_x_assum ‘v_rel _ _ _’ (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once v_rel_cases])
      \\ gvs [pmatch_def, prune_pat_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
      \\ Cases_on ‘nsLookup envC n’ \\ gvs []
            \\ PairCases_on ‘x’ \\ gvs [] \\ rw [] \\ gvs []
      \\ first_x_assum drule_all \\ gvs [])
  >~ [‘pmatch envC refs1 (Pcon NONE ps) (Conv NONE vs1) bs1’]
  >- (qpat_x_assum ‘v_rel _ _ _’ (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once v_rel_cases])
      \\ gvs [pmatch_def, prune_pat_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ gvs [] \\ rw [] \\ gvs []
      \\ first_x_assum drule_all \\ gvs [])
  >~ [‘pmatch envC refs1 (Pref p) (Loc b lnum) bs1’]
  >- (qpat_x_assum ‘v_rel _ _ _’ (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once v_rel_cases])
      \\ gvs [pmatch_def, prune_pat_def]
      \\ qpat_assum ‘∀loc1 loc2. FLOOKUP _ _ = _ ⇒ _’ drule \\ strip_tac
      \\ gvs [] \\ Cases_on ‘sv1’ \\ Cases_on ‘sv2’ \\ gvs []
      \\ last_x_assum drule
      \\ disch_then (qspecl_then [‘refs2’,‘bs2’,‘used’] mp_tac)
      \\ impl_tac \\ gvs [])
  >~ [‘pmatch envC refs1 (Pas p i) v1 bs1’]
  >- (gvs [pmatch_def, prune_pat_def] \\ rw [] \\ gvs [pmatch_def]
      >- (last_x_assum irule \\ gvs [] \\ irule binds_rel_cons \\ gvs [])
      \\ last_x_assum irule \\ gvs [] \\ irule binds_rel_cons_unused
      \\ gvs [])
  >~ [‘pmatch envC refs1 (Ptannot p t) v1 bs1’]
  >- (gvs [pmatch_def, prune_pat_def] \\ last_x_assum irule \\ gvs [])
  >~ [‘pmatch_list envC refs1 (p::ps) (v1::vs1) bs1’]
  >- (gvs [pmatch_def, prune_pat_def]
      \\ Cases_on ‘pmatch envC refs1 p v1 bs1’ \\ gvs []
      >- (last_x_assum drule_all \\ strip_tac \\ gvs []
          \\ Cases_on ‘pmatch_list envC refs1 ps vs1 bs1’ \\ gvs []
          \\ last_x_assum drule_all \\ strip_tac \\ gvs [])
      \\ last_x_assum drule_all \\ strip_tac \\ gvs [])
  \\ gvs [pmatch_def, prune_pat_def]
QED

Theorem env_rel_nsAppend_unused[local]:
  ∀f names env1 env2 bs.
    env_rel f names env1 env2 ∧ (∀x. MEM x (MAP FST bs) ⇒ Short x ∉ names) ⇒
    env_rel f names (env1 with v := nsAppend (alist_to_ns bs) env1.v) env2
Proof
  rw [env_rel_def, namespacePropsTheory.nsLookup_nsAppend_some]
  \\ gvs [namespacePropsTheory.nsLookup_alist_to_ns_some,
          namespacePropsTheory.nsLookup_alist_to_ns_none]
  \\ gvs [ALOOKUP_NONE, MEM_MAP]
  \\ metis_tac [ALOOKUP_MEM, MEM_MAP, FST]
QED

Theorem env_rel_nsAppend_binds[local]:
  ∀f used env1 env2 bs1 bs2.
    env_rel f (names_set used DIFF IMAGE Short (set (MAP FST bs1))) env1 env2 ∧
    binds_rel f used bs1 bs2 ⇒
    env_rel f (names_set used)
      (env1 with v := nsAppend (alist_to_ns bs1) env1.v)
      (env2 with v := nsAppend (alist_to_ns bs2) env2.v)
Proof
  rw [env_rel_def, namespacePropsTheory.nsLookup_nsAppend_some]
  \\ gvs [namespacePropsTheory.nsLookup_alist_to_ns_some,
          namespacePropsTheory.nsLookup_alist_to_ns_none]
  \\ gvs [binds_rel_def]
  >- (res_tac \\ gvs [])
  \\ ‘∀x'. x = Short x' ⇒ ¬MEM x' (MAP FST bs1)’ by
       (rw [] \\ gvs [ALOOKUP_NONE])
  \\ first_x_assum drule_all \\ strip_tac \\ gvs []
  \\ qexists_tac ‘v2’ \\ gvs [] \\ disj2_tac
  \\ rw [] >- (gvs [ALOOKUP_NONE] \\ metis_tac [])
  \\ Cases_on ‘p1’ \\ gvs []
QED

Theorem extend_dec_env_alist[local]:
  extend_dec_env <|v := alist_to_ns bs; c := nsEmpty|> env =
  env with v := nsAppend (alist_to_ns bs) env.v
Proof
  gvs [extend_dec_env_def, sem_env_component_equality]
QED

(* nsAppend's lookup as a deterministic rewrite: the side conditions of
   nsLookup_nsAppend_some/none amount to a single module lookup, since a
   failed one-step module lookup makes every longer path fail too *)
Theorem nsLookup_Long_nsLookupMod[local]:
  ∀e mn y.
    nsLookup e (Long mn y) =
    case nsLookupMod e [mn] of NONE => NONE | SOME m => nsLookup m y
Proof
  Cases \\ rpt gen_tac
  \\ gvs [namespaceTheory.nsLookup_def, namespaceTheory.nsLookupMod_def]
  \\ every_case_tac \\ gvs []
QED

Theorem nsLookup_alist_to_ns_eq[local]:
  nsLookup (alist_to_ns bs) (Short n) = ALOOKUP bs n ∧
  nsLookup (alist_to_ns bs) (Long mn y) = NONE
Proof
  gvs [namespaceTheory.alist_to_ns_def, namespaceTheory.nsLookup_def]
QED

Theorem nsLookup_nsLift_eq[local]:
  nsLookup (nsLift mn A) (Short n) = NONE ∧
  nsLookup (nsLift mn A) (Long mn' y) = (if mn' = mn then nsLookup A y else NONE)
Proof
  rw [namespaceTheory.nsLift_def, namespaceTheory.nsLookup_def]
QED

Theorem nsLookup_nsAppend_eq[local]:
  ∀e1 e2 id.
    nsLookup (nsAppend e1 e2) id =
    case id of
    | Short n => (case nsLookup e1 (Short n) of
                  | NONE => nsLookup e2 (Short n)
                  | SOME v => SOME v)
    | Long mn y => (case nsLookupMod e1 [mn] of
                    | NONE => nsLookup e2 (Long mn y)
                    | SOME m => nsLookup e1 (Long mn y))
Proof
  rpt gen_tac \\ Cases_on ‘e1’ \\ Cases_on ‘e2’ \\ Cases_on ‘id’
  \\ gvs [namespaceTheory.nsAppend_def, namespaceTheory.nsLookup_def,
          namespaceTheory.nsLookupMod_def, ALOOKUP_APPEND]
  \\ every_case_tac \\ gvs []
QED

Theorem nsLookupMod_nsAppend[local]:
  ∀e1 e2 mn.
    nsLookupMod (nsAppend e1 e2) [mn] =
    case nsLookupMod e1 [mn] of
    | NONE => nsLookupMod e2 [mn]
    | SOME m => SOME m
Proof
  rpt gen_tac \\ Cases_on ‘e1’ \\ Cases_on ‘e2’
  \\ gvs [namespaceTheory.nsAppend_def, namespaceTheory.nsLookupMod_def,
          ALOOKUP_APPEND]
  \\ every_case_tac \\ gvs []
QED

Theorem nsLookupMod_nsLift[local,simp]:
  nsLookupMod (nsLift mn e) [mn'] = if mn' = mn then SOME e else NONE
Proof
  rw [namespaceTheory.nsLift_def, namespaceTheory.nsLookupMod_def]
QED

(* the two value namespaces have the same top-level modules; without this a
   Long name could fall through an nsAppend on one side but not the other *)
Definition mods_rel_def:
  mods_rel v1 v2 ⇔ ∀mn. nsLookupMod v1 [mn] = NONE ⇔ nsLookupMod v2 [mn] = NONE
End

Theorem mods_rel_refl[local,simp]:
  mods_rel v v
Proof
  gvs [mods_rel_def]
QED

Theorem mods_rel_nsAppend[local]:
  mods_rel a1 a2 ∧ mods_rel b1 b2 ⇒ mods_rel (nsAppend a1 b1) (nsAppend a2 b2)
Proof
  gvs [mods_rel_def, nsLookupMod_nsAppend] \\ rw []
  \\ rpt (first_x_assum (qspec_then ‘mn’ mp_tac))
  \\ every_case_tac \\ gvs []
QED

Theorem mods_rel_alist[local,simp]:
  mods_rel (alist_to_ns bs1) (alist_to_ns bs2) ∧
  mods_rel (alist_to_ns bs1) nsEmpty ∧
  mods_rel nsEmpty (alist_to_ns bs2)
Proof
  gvs [mods_rel_def]
QED

(* only Dlet, Dletrec and Denv ever shrink the set of used names, and they
   only remove Short names *)
Theorem dce_decs_longs[local]:
  (∀used ds ds1 used1.
     dce_decs used ds = (ds1,used1) ⇒
     ∀mn y. Long mn y ∈ names_set used ⇒ Long mn y ∈ names_set used1) ∧
  (∀used d ds1 used1.
     dce_dec used d = (ds1,used1) ⇒
     ∀mn y. Long mn y ∈ names_set used ⇒ Long mn y ∈ names_set used1)
Proof
  ho_match_mp_tac dce_decs_ind \\ rpt conj_tac \\ rpt gen_tac
  \\ gvs [dce_decs_def] \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()] \\ res_tac \\ gvs []
  \\ gvs [update_names_def, free_vars_dec_def, dec_binds_def,
          names_set_free_vars, names_set_delete_names]
  \\ metis_tac [IN_names_set_union_names]
QED

(* a name only leaves the used set when the declarations bind it *)
Theorem dce_decs_binds[local]:
  ∀(s1:'ffi semanticPrimitives$state) env1 ds s1' new1 used ds1 used1.
    evaluate_decs s1 env1 ds = (s1',Rval new1) ∧
    dce_decs used ds = (ds1,used1) ⇒
    ∀n. Short n ∈ names_set used ∧ nsLookup new1.v (Short n) = NONE ⇒
        Short n ∈ names_set used1
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >~ [‘evaluate_decs s1 env1 (d1::d2::ds)’]
  >- (qpat_x_assum ‘dce_decs used (d1::d2::ds) = _’ mp_tac
      \\ once_rewrite_tac [dce_decs_def]
      \\ rpt (pairarg_tac \\ simp []) \\ strip_tac
      \\ Cases_on ‘dce_decs used (d2::ds)’ \\ gvs []
      \\ rename [‘dce_decs used (d2::ds) = (dsB,usedB)’]
      \\ Cases_on ‘dce_dec usedB d1’ \\ gvs []
      \\ rename [‘dce_dec usedB d1 = (dsA,usedA)’]
      \\ qpat_x_assum ‘evaluate_decs s1 env1 (d1::d2::ds) = _’ mp_tac
      \\ once_rewrite_tac [evaluate_decs_cons]
      \\ Cases_on ‘evaluate_decs s1 env1 [d1]’ \\ simp []
      \\ rename [‘evaluate_decs s1 env1 [d1] = (t1,r1)’]
      \\ Cases_on ‘r1’ \\ simp []
      \\ Cases_on ‘evaluate_decs t1 (a +++ env1) (d2::ds)’ \\ simp []
      \\ rename [‘evaluate_decs t1 (a +++ env1) (d2::ds) = (t2,r2)’]
      \\ Cases_on ‘r2’ \\ simp [combine_dec_result_def]
      \\ strip_tac \\ gvs []
      \\ gvs [nsLookup_nsAppend_eq, AllCaseEqs()]
      \\ last_x_assum (qspecl_then [‘used’,‘dsB’,‘usedB’] mp_tac) \\ simp []
      \\ strip_tac
      \\ first_x_assum
           (qspecl_then [‘usedB’,‘SmartAppend dsA Nil’,‘usedA’] mp_tac)
      \\ simp [dce_decs_def])
  >~ [‘evaluate_decs s1 env1 [Dlet locs p e]’]
  >- (gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def]
      \\ Cases_on ‘can_remove used (Dlet locs p e)’ \\ gvs []
      \\ imp_res_tac (cj 1 pmatch_extend) \\ gvs []
      \\ gvs [update_names_def, dec_binds_def, free_vars_dec_def,
              names_set_free_vars, names_set_delete_names]
      \\ gvs [nsLookup_alist_to_ns_eq, ALOOKUP_NONE])
  >~ [‘evaluate_decs s1 env1 [Dletrec locs funs]’]
  >- (gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def]
      \\ Cases_on ‘can_remove used (Dletrec locs funs)’ \\ gvs []
      \\ gvs [update_names_def, dec_binds_def, free_vars_dec_def,
              names_set_free_vars, names_set_delete_names, build_rec_env_merge,
              nsLookup_alist_to_ns_eq, ALOOKUP_rec_env, AllCaseEqs()])
  >~ [‘evaluate_decs s1 env1 [Denv n]’]
  >- (gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def,
           can_remove_def, update_names_def, dec_binds_def, free_vars_dec_def,
           names_set_delete_names, is_used_names_set,
           namespacePropsTheory.nsLookup_nsBind]
      \\ rw [] \\ gvs []
      \\ Cases_on ‘Short n ∉ names_set used’ \\ gvs [names_set_delete_names])
  >~ [‘evaluate_decs s1 env1 [Dmod mn ds]’]
  >- (gvs [dce_decs_def, evaluate_decs_def]
      \\ rpt (pairarg_tac \\ gvs [])
      \\ gvs [AllCaseEqs()]
      \\ metis_tac [IN_names_set_union_names])
  >~ [‘evaluate_decs s1 env1 [Dlocal lds ds]’]
  >- (gvs [dce_decs_def, evaluate_decs_def]
      \\ rpt (pairarg_tac \\ gvs [])
      \\ gvs [AllCaseEqs()]
      >- (last_x_assum drule \\ simp [])
      \\ metis_tac [IN_names_set_union_names])
  \\ gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def,
          can_remove_def, update_names_def, dec_binds_def, free_vars_dec_def,
          names_set_delete_names, is_used_names_set,
          namespacePropsTheory.nsLookup_nsBind]
  \\ rw [] \\ gvs []
QED

(* declarations that the pass drops leave the state essentially unchanged,
   introduce no constructors, and bind no name that is used later *)
Theorem dce_decs_dropped[local]:
  ∀(s1:'ffi semanticPrimitives$state) env1 ds s1' res1 used ds1 used1.
    evaluate_decs s1 env1 ds = (s1',res1) ∧ res1 ≠ Rerr (Rabort Rtype_error) ∧
    dce_decs used ds = (ds1,used1) ∧ append ds1 = [] ⇒
    pure_st s1 s1' ∧
    ∃new1. res1 = Rval new1 ∧ new1.c = nsEmpty ∧
           (∀mn. nsLookupMod new1.v [mn] = NONE) ∧
           ∀x v. nsLookup new1.v x = SOME v ⇒ x ∉ names_set used
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >~ [‘evaluate_decs s1 env1 (d1::d2::ds)’]
  >- (qpat_x_assum ‘dce_decs used (d1::d2::ds) = _’ mp_tac
      \\ once_rewrite_tac [dce_decs_def]
      \\ rpt (pairarg_tac \\ simp []) \\ strip_tac
      \\ Cases_on ‘dce_decs used (d2::ds)’ \\ gvs []
      \\ rename [‘dce_decs used (d2::ds) = (dsB,usedB)’]
      \\ Cases_on ‘dce_dec usedB d1’ \\ gvs []
      \\ rename [‘dce_dec usedB d1 = (dsA,usedA)’]
      \\ ‘usedA = usedB’ by metis_tac [dce_decs_empty_used]
      \\ gvs []
      \\ qpat_x_assum ‘evaluate_decs s1 env1 (d1::d2::ds) = _’ mp_tac
      \\ once_rewrite_tac [evaluate_decs_cons]
      \\ Cases_on ‘evaluate_decs s1 env1 [d1]’ \\ simp []
      \\ rename [‘evaluate_decs s1 env1 [d1] = (t1,r1)’]
      \\ reverse (Cases_on ‘r1’) \\ simp []
      >- (strip_tac \\ gvs []
          \\ first_x_assum (qspecl_then
               [‘usedA’,‘SmartAppend dsA Nil’,‘usedA’] mp_tac)
          \\ gvs [dce_decs_def])
      \\ Cases_on ‘evaluate_decs t1 (a +++ env1) (d2::ds)’ \\ gvs []
      \\ strip_tac
      \\ ‘r ≠ Rerr (Rabort Rtype_error)’ by
           (strip_tac \\ gvs [combine_dec_result_def])
      \\ last_x_assum drule \\ simp [] \\ disch_then drule \\ simp []
      \\ strip_tac
      \\ first_x_assum (qspecl_then
           [‘usedA’,‘SmartAppend dsA Nil’,‘usedA’] mp_tac)
      \\ simp [dce_decs_def] \\ strip_tac
      \\ gvs [combine_dec_result_def, extend_dec_env_def]
      \\ rpt conj_tac
      >- (irule pure_st_trans \\ metis_tac [])
      >- gvs [nsLookupMod_nsAppend]
      \\ rw [] \\ gvs [namespacePropsTheory.nsLookup_nsAppend_some]
      \\ ‘usedA = used’ by metis_tac [cj 1 dce_decs_empty_used]
      \\ gvs [] \\ metis_tac [])
  >~ [‘evaluate_decs s1 env1 [Dlet locs p e]’]
  >- (gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def,
           can_remove_def]
      \\ Cases_on ‘pure_exp e ∧ total_pat p ∧
                   EVERY (λn. ¬is_used used n) (pat_bindings p)’
      \\ gvs []
      >~ [‘pmatch env1.c s1'.refs p (HD v) [] = No_match’]
      >- metis_tac [cj 1 total_pat_pmatch]
      >~ [‘evaluate s1 env1 [e] = (s1',Rerr err)’]
      >- (drule (cj 1 pure_exp_evaluate) \\ gvs [pure_exp_def])
      \\ imp_res_tac (cj 1 pmatch_extend) \\ gvs []
      \\ drule (cj 1 pure_exp_evaluate) \\ gvs [pure_exp_def]
      \\ strip_tac
      \\ gvs [namespacePropsTheory.nsLookup_alist_to_ns_some, EVERY_MEM,
              is_used_names_set]
      \\ rw [] \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [MEM_MAP] \\ res_tac \\ gvs []
      \\ first_x_assum irule \\ gvs [GSYM MEM_MAP]
      \\ metis_tac [MEM_MAP, FST])
  >~ [‘evaluate_decs s1 env1 [Dletrec locs funs]’]
  >- (gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def,
           can_remove_def]
      \\ gvs [build_rec_env_merge,
              namespacePropsTheory.nsLookup_nsAppend_some,
              namespacePropsTheory.nsLookup_alist_to_ns_some, ALOOKUP_rec_env]
      \\ gvs [AllCaseEqs(), EVERY_MEM, FORALL_PROD, is_used_names_set, MEM_MAP]
      \\ rw [] \\ res_tac \\ gvs []
      \\ Cases_on ‘∀p_1 p_1' p_2.
                      MEM (p_1,p_1',p_2) funs ⇒ Short p_1 ∉ names_set used’
      \\ gvs [] \\ PairCases_on ‘y’ \\ gvs [] \\ res_tac \\ gvs [])
  >~ [‘evaluate_decs s1 env1 [Denv n]’]
  >- (gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def,
           can_remove_def]
      \\ gvs [pure_st_def, is_used_names_set,
              namespacePropsTheory.nsLookup_nsBind]
      \\ rw [] \\ gvs []
      \\ Cases_on ‘Short n ∉ names_set used’ \\ gvs []
      \\ gvs [declare_env_def, AllCaseEqs()])
  (* a module is never dropped: it is kept, possibly emptied *)
  >~ [‘evaluate_decs s1 env1 [Dmod mn ds]’]
  >- (gvs [dce_decs_def] \\ rpt (pairarg_tac \\ gvs [])
      \\ gvs [AllCaseEqs()])
  >~ [‘evaluate_decs s1 env1 [Dlocal lds ds]’]
  >- (gvs [dce_decs_def, evaluate_decs_def] \\ rpt (pairarg_tac \\ gvs [])
      \\ gvs [AllCaseEqs()]
      >- (last_x_assum drule \\ simp [] \\ strip_tac
          \\ first_x_assum drule \\ gvs [NULL_EQ] \\ strip_tac
          \\ irule pure_st_trans \\ metis_tac [])
      \\ first_x_assum drule \\ gvs [NULL_EQ])
  \\ gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def,
          can_remove_def]
  \\ gvs []
QED

(* lifting into a module just prepends a module entry, so a lookup in
   nsAppend (nsLift mn A) B goes to A for names qualified by mn and to B
   for everything else *)
Theorem nsLookup_nsAppend_nsLift[local]:
  ∀mn A B id.
    nsLookup (nsAppend (nsLift mn A) B) id =
    case id of
    | Short x => nsLookup B (Short x)
    | Long mn' y => if mn' = mn then nsLookup A y else nsLookup B (Long mn' y)
Proof
  rpt gen_tac \\ Cases_on ‘B’ \\ Cases_on ‘id’
  \\ gvs [namespaceTheory.nsLift_def, namespaceTheory.nsAppend_def,
          namespaceTheory.nsLookup_def]
  \\ rw []
QED

(* The two environments that a declaration list adds, related on their own,
   i.e. without the enclosing environment. Dmod needs this: the module's
   environment is not extended with the outer one, so a name that the source
   module binds must be found in the target module itself. Both directions
   are needed, because a lookup that misses the first component of an
   nsAppend must miss it on both sides for the fall-through to agree. *)
Definition new_rel_def:
  new_rel f names new1 new2 ⇔
    new1.c = new2.c ∧
    mods_rel new1.v new2.v ∧
    ∀x. x ∈ names ⇒
        case nsLookup new1.v x of
        | NONE => nsLookup new2.v x = NONE
        | SOME v1 => ∃v2. nsLookup new2.v x = SOME v2 ∧ v_rel f v1 v2
End

Theorem new_rel_mono[local]:
  ∀f1 f2 names1 names2 new1 new2.
    new_rel f1 names1 new1 new2 ∧ f1 ⊑ f2 ∧ names2 ⊆ names1 ⇒
    new_rel f2 names2 new1 new2
Proof
  rw [new_rel_def]
  \\ ‘x ∈ names1’ by gvs [SUBSET_DEF]
  \\ first_x_assum drule
  \\ Cases_on ‘nsLookup new1.v x’ \\ gvs []
  \\ metis_tac [v_rel_submap]
QED

Theorem new_rel_empty[local,simp]:
  new_rel f names <|v := nsEmpty; c := nsEmpty|> <|v := nsEmpty; c := nsEmpty|>
Proof
  gvs [new_rel_def]
QED

(* the source binds names that are not used and the target binds nothing *)
Theorem new_rel_unused[local]:
  ∀f names ns.
    (∀x v. nsLookup ns x = SOME v ⇒ x ∉ names) ∧
    (∀mn. nsLookupMod ns [mn] = NONE) ⇒
    new_rel f names <|v := ns; c := nsEmpty|> <|v := nsEmpty; c := nsEmpty|>
Proof
  rw [new_rel_def, mods_rel_def] \\ gvs []
  \\ Cases_on ‘nsLookup ns x’ \\ gvs []
  \\ res_tac \\ gvs []
QED

Theorem new_rel_binds[local]:
  ∀f used bs1 bs2.
    binds_rel f used bs1 bs2 ⇒
    new_rel f (names_set used)
      <|v := alist_to_ns bs1; c := nsEmpty|>
      <|v := alist_to_ns bs2; c := nsEmpty|>
Proof
  rw [new_rel_def, binds_rel_def] \\ Cases_on ‘x’
  \\ gvs [nsLookup_alist_to_ns_eq]
  \\ every_case_tac \\ gvs []
  \\ gvs [ALOOKUP_NONE] \\ metis_tac [ALOOKUP_MEM, MEM_MAP, FST]
QED

Theorem new_rel_build_rec_env[local]:
  ∀f names names2 env1 env2 funs.
    env_rel f names env1 env2 ∧
    fvs_funs funs DIFF set (MAP (Short o FST) funs) ⊆ names ⇒
    new_rel f names2 <|v := build_rec_env funs env1 nsEmpty; c := nsEmpty|>
                     <|v := build_rec_env funs env2 nsEmpty; c := nsEmpty|>
Proof
  rw [new_rel_def, build_rec_env_merge] \\ Cases_on ‘x’
  \\ gvs [nsLookup_alist_to_ns_eq, ALOOKUP_rec_env]
  \\ rw [] \\ irule v_rel_Recclosure
  \\ gvs [env_rel_def, SUBSET_DEF] \\ metis_tac []
QED

(* Dmod: the two module environments, lifted *)
Theorem new_rel_nsLift[local]:
  ∀f used mn A1 Ac1 A2 Ac2.
    new_rel f (names_set (strip_mod mn used))
      <|v := A1; c := Ac1|> <|v := A2; c := Ac2|> ⇒
    new_rel f (names_set used)
      <|v := nsLift mn A1; c := nsLift mn Ac1|>
      <|v := nsLift mn A2; c := nsLift mn Ac2|>
Proof
  rw [new_rel_def, mods_rel_def] \\ gvs []
  \\ Cases_on ‘x’ \\ gvs [nsLookup_nsLift_eq]
  \\ rw [] \\ gvs [names_set_strip_mod]
QED

(* the workhorse for extending an environment: a lookup that the added
   environment misses falls through on both sides at once *)
Theorem env_rel_extend_dec_env[local]:
  ∀f names names2 new1 new2 env1 env2.
    new_rel f names new1 new2 ∧ env_rel f names2 env1 env2 ∧
    (∀x. x ∈ names ∧ nsLookup new1.v x = NONE ⇒ x ∈ names2) ⇒
    env_rel f names (extend_dec_env new1 env1) (extend_dec_env new2 env2)
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [new_rel_def, mods_rel_def, env_rel_def, extend_dec_env_def]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt (first_x_assum (qspec_then ‘x’ mp_tac)) \\ gvs []
  \\ Cases_on ‘x’ \\ gvs [nsLookup_nsAppend_eq, nsLookup_Long_nsLookupMod]
  \\ every_case_tac \\ gvs []
  \\ rpt strip_tac \\ gvs []
  \\ metis_tac []
QED

Theorem new_rel_extend[local]:
  ∀f names names2 new1 new2 env1 env2.
    new_rel f names new1 new2 ∧ new_rel f names2 env1 env2 ∧
    (∀x. x ∈ names ∧ nsLookup new1.v x = NONE ⇒ x ∈ names2) ⇒
    new_rel f names (extend_dec_env new1 env1) (extend_dec_env new2 env2)
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [new_rel_def, extend_dec_env_def]
  \\ conj_tac >- (irule mods_rel_nsAppend \\ gvs [])
  \\ gen_tac \\ strip_tac
  \\ Cases_on ‘x’
  >~ [‘Long m i’] >-
   (‘(nsLookupMod new1.v [m] = NONE) ⇔ (nsLookupMod new2.v [m] = NONE)’ by
       gvs [mods_rel_def]
    \\ gvs [nsLookup_nsAppend_eq, nsLookup_Long_nsLookupMod]
    \\ Cases_on ‘nsLookupMod new1.v [m]’ \\ gvs []
    >- (‘Long m i ∈ names2’ by
          (first_x_assum irule \\ gvs [nsLookup_Long_nsLookupMod])
        \\ qpat_x_assum ‘∀x. x ∈ names2 ⇒ _’ (qspec_then ‘Long m i’ mp_tac)
        \\ gvs [nsLookup_Long_nsLookupMod])
    \\ Cases_on ‘nsLookupMod new2.v [m]’ \\ gvs []
    \\ qpat_x_assum ‘∀x. x ∈ names ⇒ _’ (qspec_then ‘Long m i’ mp_tac)
    \\ gvs [nsLookup_Long_nsLookupMod])
  \\ gvs [nsLookup_nsAppend_eq]
  \\ qpat_x_assum ‘∀x. x ∈ names ⇒ _’ (qspec_then ‘Short n’ mp_tac) \\ gvs []
  \\ Cases_on ‘nsLookup new1.v (Short n)’ \\ gvs []
  \\ strip_tac \\ gvs []
QED

(* Dlocal: the local declarations are added on the source side only, so they
   must not bind any name that is used *)
Theorem env_rel_extend_unused[local]:
  ∀f names new1 env1 env2.
    env_rel f names env1 env2 ∧ new1.c = nsEmpty ∧
    (∀mn. nsLookupMod new1.v [mn] = NONE) ∧
    (∀x v. nsLookup new1.v x = SOME v ⇒ x ∉ names) ⇒
    env_rel f names (extend_dec_env new1 env1) env2
Proof
  rw [env_rel_def, extend_dec_env_def]
  \\ qpat_x_assum ‘nsLookup _ _ = SOME _’ mp_tac
  \\ Cases_on ‘x’ \\ gvs [nsLookup_nsAppend_eq, nsLookup_Long_nsLookupMod]
  \\ rw [] \\ res_tac \\ gvs []
  \\ Cases_on ‘nsLookup new1.v (Short n)’ \\ gvs [] \\ res_tac
QED

(* the same with extend_dec_env unfolded, which is the form the declaration
   goals are in, since extend_dec_env_def is a simplification rule *)
Theorem new_rel_extend_alt[local]:
  ∀f names names2 new1 new2 env1 env2.
    new_rel f names new1 new2 ∧ new_rel f names2 env1 env2 ∧
    (∀x. x ∈ names ∧ nsLookup new1.v x = NONE ⇒ x ∈ names2) ⇒
    new_rel f names
      <|v := nsAppend new1.v env1.v; c := nsAppend new1.c env1.c|>
      <|v := nsAppend new2.v env2.v; c := nsAppend new2.c env2.c|>
Proof
  rpt strip_tac \\ drule_all new_rel_extend \\ gvs [extend_dec_env_def]
QED

(* what Dmod needs: the module envs only have to agree on the names that
   are used qualified by mn *)
Theorem env_rel_Dmod[local]:
  ∀f names mn A Ac A' Ac' env1 env2.
    env_rel f names env1 env2 ∧ Ac = Ac' ∧
    (∀y v. Long mn y ∈ names ∧ nsLookup A y = SOME v ⇒
           ∃v2. nsLookup A' y = SOME v2 ∧ v_rel f v v2) ⇒
    env_rel f names
      (<|v := nsLift mn A; c := nsLift mn Ac|> +++ env1)
      (<|v := nsLift mn A'; c := nsLift mn Ac'|> +++ env2)
Proof
  rw [env_rel_def, extend_dec_env_def]
  \\ gvs [nsLookup_nsAppend_nsLift]
  \\ Cases_on ‘x’ \\ gvs [] \\ rw [] \\ gvs []
  \\ metis_tac []
QED

Theorem has_Denv_decs_append[local]:
  ∀xs ys. has_Denv_decs (xs ++ ys) ⇔ has_Denv_decs xs ∨ has_Denv_decs ys
Proof
  Induct \\ gvs [has_Denv_dec_def] \\ metis_tac []
QED

Theorem extend_dec_env_assoc[local]:
  extend_dec_env a (extend_dec_env b c) = extend_dec_env (extend_dec_env a b) c
Proof
  gvs [extend_dec_env_def, namespacePropsTheory.nsAppend_assoc]
QED

Theorem evaluate_decs_v_rel[local]:
  ∀(s1:'ffi semanticPrimitives$state) env1 ds s1' res1.
    evaluate_decs s1 env1 ds = (s1',res1) ∧
    res1 ≠ Rerr (Rabort Rtype_error) ⇒
    ∀f s2 env2 used ds1 used1.
      dce_decs used ds = (ds1,used1) ∧
      ¬has_Denv_decs (append ds1) ∧
      state_rel f s1 s2 ∧
      env_rel f (names_set used1) env1 env2 ⇒
      ∃f' s2' res2.
        evaluate_decs s2 env2 (append ds1) = (s2',res2) ∧ f ⊑ f' ∧
        state_rel f' s1' s2' ∧
        result_rel
          (λnew1 new2.
             env_rel f' (names_set used)
               (extend_dec_env new1 env1) (extend_dec_env new2 env2) ∧
             new_rel f' (names_set used) new1 new2)
          (v_rel f') res1 res2
Proof
  ho_match_mp_tac evaluate_decs_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  >~ [‘evaluate_decs _ _ []’]        >- suspend "empty"
  >~ [‘d1::d2::ds’]                  >- suspend "cons"
  >~ [‘Dlet locs p e’]               >- suspend "Dlet"
  >~ [‘Dletrec locs funs’]           >- suspend "Dletrec"
  >~ [‘Dtype locs tds’]              >- suspend "Dtype"
  >~ [‘Dtabbrev locs tvs tn t’]      >- suspend "Dtabbrev"
  >~ [‘Denv n’]                      >- suspend "Denv"
  >~ [‘Dexn locs cn ts’]             >- suspend "Dexn"
  >~ [‘Dmod mn ds’]                  >- suspend "Dmod"
  >~ [‘Dlocal lds ds’]               >- suspend "Dlocal"
QED

Resume evaluate_decs_v_rel[empty]:
  gvs [evaluate_def, dce_decs_def] \\ qexists_tac ‘f’
  \\ gvs [env_rel_def, extend_dec_env_def]
QED

Resume evaluate_decs_v_rel[cons]:
  qpat_x_assum ‘dce_decs used (d1::d2::ds) = _’ mp_tac
  \\ once_rewrite_tac [dce_decs_def]
  \\ rpt (pairarg_tac \\ simp []) \\ strip_tac
  \\ Cases_on ‘dce_decs used (d2::ds)’ \\ gvs []
  \\ rename [‘dce_decs used (d2::ds) = (dsB,usedB)’]
  \\ Cases_on ‘dce_dec usedB d1’ \\ gvs []
  \\ rename [‘dce_dec usedB d1 = (dsA,usedA)’]
  \\ gvs [has_Denv_decs_append]
  \\ simp [evaluate_decs_append]
  \\ qpat_x_assum ‘evaluate_decs s1 env1 (d1::d2::ds) = _’ mp_tac
  \\ once_rewrite_tac [evaluate_decs_cons]
  \\ Cases_on ‘evaluate_decs s1 env1 [d1]’ \\ simp []
  \\ rename [‘evaluate_decs s1 env1 [d1] = (t1,r1)’]
  \\ Cases_on ‘r1’ \\ simp []
  >- (strip_tac
      \\ Cases_on ‘evaluate_decs t1 (a +++ env1) (d2::ds)’ \\ gvs []
      \\ rename [‘evaluate_decs t1 (a +++ env1) (d2::ds) = (t2,r2)’]
      \\ ‘r2 ≠ Rerr (Rabort Rtype_error)’ by
           (strip_tac \\ gvs [combine_dec_result_def])
      \\ last_x_assum drule \\ strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ last_x_assum (qspecl_then
           [‘f’,‘s2’,‘env2’,‘usedB’,‘SmartAppend dsA Nil’,‘usedA’] mp_tac)
      \\ impl_tac >- gvs [dce_decs_def]
      \\ strip_tac \\ gvs []
      \\ first_x_assum drule_all \\ strip_tac \\ gvs []
      \\ imp_res_tac SUBMAP_TRANS \\ simp []
      \\ Cases_on ‘r2’ \\ gvs [combine_dec_result_def, extend_dec_env_assoc]
      \\ qpat_x_assum ‘state_rel _ t2 _’ $ irule_at Any \\ simp []
      \\ rpt conj_tac
      >- gvs [extend_dec_env_def]
      (* the two result environments on their own: what the tail adds, and
         what the head adds for the names the tail leaves unbound *)
      \\ irule new_rel_extend_alt
      \\ conj_tac >- gvs []
      \\ qexists_tac ‘names_set usedB’
      \\ conj_tac
      >- (rw [] \\ Cases_on ‘x’ \\ gvs []
          >- (qpat_x_assum ‘evaluate_decs t1 _ (d2::ds) = _’ assume_tac
              \\ drule dce_decs_binds \\ disch_then drule \\ gvs [])
          \\ drule (cj 1 dce_decs_longs) \\ gvs [])
      \\ irule new_rel_mono
      \\ qpat_x_assum ‘new_rel _ (names_set usedB) a new2’ $ irule_at Any
      \\ gvs [])
  \\ strip_tac \\ gvs []
  \\ first_x_assum (qspecl_then
       [‘f’,‘s2’,‘env2’,‘usedB’,‘SmartAppend dsA Nil’,‘usedA’] mp_tac)
  \\ impl_tac >- gvs [dce_decs_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘state_rel _ s1' _’ $ irule_at Any \\ simp []
QED

Resume evaluate_decs_v_rel[Dlet]:
  gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def]
  \\ Cases_on ‘can_remove used (Dlet locs p e)’ \\ gvs []
  (* removed: the pattern is total, so it cannot fail to match *)
  >- (gvs [can_remove_def] \\ metis_tac [cj 1 total_pat_pmatch])
  (* kept, no match: the pruned pattern does not match either *)
  >- (‘ALL_DISTINCT (pat_bindings (prune_pat used p))’ by
        metis_tac [prune_pat_bindings]
      \\ ‘env1.c = env2.c’ by gvs [env_rel_def]
      \\ ‘every_exp (one_con_check env2.c) e’ by
           gvs []
      \\ gvs [evaluate_decs_def]
      \\ drule (cj 1 evaluate_v_rel) \\ gvs []
      \\ disch_then (qspecl_then [‘f’,‘s2’,‘env2’] mp_tac)
      \\ impl_tac
      >- (gvs [] \\ drule_then irule env_rel_mono
          \\ gvs [update_names_def, dec_binds_def, free_vars_dec_def,
                  names_set_free_vars, SUBSET_DEF, fvs_def])
      \\ strip_tac \\ gvs []
      \\ imp_res_tac evaluate_length \\ gvs [LENGTH_EQ_NUM_compute]
      \\ qspecl_then [‘env1.c’,‘s1'.refs’,‘p’,‘h'’,‘[]’,‘s2''.refs’,
                      ‘h’,‘[]’,‘f''’,‘used’] mp_tac (cj 1 pmatch_prune_pat)
      \\ impl_tac >- gvs [state_rel_def, binds_rel_def]
      \\ gvs [] \\ strip_tac \\ gvs []
      \\ first_assum $ irule_at Any \\ gvs [])
  (* removed: evaluating the declaration only extends the store, and none of
     the names it binds is used *)
  >- (gvs [can_remove_def, extend_dec_env_alist]
      \\ drule (cj 1 pure_exp_evaluate) \\ gvs [pure_exp_def] \\ strip_tac
      \\ qexists_tac ‘f’ \\ gvs []
      \\ conj_tac >- (irule state_rel_pure_st \\ metis_tac [])
      \\ ‘∀x v. nsLookup (alist_to_ns new_vals) x = SOME v ⇒
                x ∉ names_set used’ by
           (imp_res_tac (cj 1 pmatch_extend) \\ gvs []
            \\ gvs [EVERY_MEM, is_used_names_set]
            \\ rpt gen_tac \\ Cases_on ‘x’ \\ gvs [nsLookup_alist_to_ns_eq]
            \\ rw [] \\ imp_res_tac ALOOKUP_MEM \\ gvs [MEM_MAP]
            \\ res_tac \\ gvs []
            \\ first_x_assum irule
            \\ qpat_x_assum ‘MAP FST _ = pat_bindings p’ (assume_tac o GSYM)
            \\ gvs [MEM_MAP] \\ qexists_tac ‘(n,v')’ \\ gvs [])
      \\ conj_tac
      >- (‘<|v := nsEmpty; c := nsEmpty|> +++ env2 = env2’ by
             gvs [extend_dec_env_def, sem_env_component_equality]
          \\ gvs []
          \\ irule env_rel_nsAppend_unused \\ gvs []
          \\ rw []
          \\ ‘∃v. ALOOKUP new_vals x = SOME v’ by
               (Cases_on ‘ALOOKUP new_vals x’ \\ gvs [ALOOKUP_NONE])
          \\ first_x_assum irule
          \\ gvs [nsLookup_alist_to_ns_eq] \\ metis_tac [])
      \\ irule new_rel_unused \\ gvs [])
  (* kept, match: the pruned pattern binds the used names to related values *)
  >- (‘ALL_DISTINCT (pat_bindings (prune_pat used p))’ by
        metis_tac [prune_pat_bindings]
      \\ ‘env1.c = env2.c’ by gvs [env_rel_def]
      \\ ‘every_exp (one_con_check env2.c) e’ by
           gvs []
      \\ gvs [evaluate_decs_def]
      \\ drule (cj 1 evaluate_v_rel) \\ gvs []
      \\ disch_then (qspecl_then [‘f’,‘s2’,‘env2’] mp_tac)
      \\ impl_tac
      >- (gvs [] \\ drule_then irule env_rel_mono
          \\ gvs [update_names_def, dec_binds_def, free_vars_dec_def,
                  names_set_free_vars, SUBSET_DEF, fvs_def])
      \\ strip_tac \\ gvs []
      \\ imp_res_tac evaluate_length \\ gvs [LENGTH_EQ_NUM_compute]
      \\ qspecl_then [‘env1.c’,‘s1'.refs’,‘p’,‘h'’,‘[]’,‘s2''.refs’,
                      ‘h’,‘[]’,‘f''’,‘used’] mp_tac (cj 1 pmatch_prune_pat)
      \\ impl_tac >- gvs [state_rel_def, binds_rel_def]
      \\ gvs [] \\ strip_tac \\ gvs [extend_dec_env_alist]
      \\ first_assum $ irule_at Any \\ gvs []
      \\ conj_tac
      >- (irule env_rel_nsAppend_binds
          \\ first_assum $ irule_at Any
          \\ imp_res_tac (cj 1 pmatch_extend) \\ gvs []
          \\ drule_then irule env_rel_mono \\ gvs []
          \\ gvs [update_names_def, dec_binds_def, free_vars_dec_def,
                  names_set_free_vars, names_set_delete_names, SUBSET_DEF])
      \\ irule new_rel_binds \\ gvs [])
  (* removed: a pure expression cannot raise *)
  >- (gvs [can_remove_def] \\ drule (cj 1 pure_exp_evaluate)
      \\ gvs [pure_exp_def])
  (* kept, exception *)
  \\ ‘ALL_DISTINCT (pat_bindings (prune_pat used p))’ by
       metis_tac [prune_pat_bindings]
  \\ ‘env1.c = env2.c’ by gvs [env_rel_def]
  \\ ‘every_exp (one_con_check env2.c) e’ by
       gvs []
  \\ gvs [evaluate_decs_def]
  \\ drule (cj 1 evaluate_v_rel) \\ gvs []
  \\ disch_then (qspecl_then [‘f’,‘s2’,‘env2’] mp_tac)
  \\ impl_tac
  >- (gvs [] \\ drule_then irule env_rel_mono
      \\ gvs [update_names_def, dec_binds_def, free_vars_dec_def,
              names_set_free_vars, SUBSET_DEF, fvs_def])
  \\ strip_tac \\ gvs []
  \\ first_assum $ irule_at Any \\ simp []
QED

Resume evaluate_decs_v_rel[Dletrec]:
  gvs [dce_decs_def, evaluate_decs_def, AllCaseEqs(), prune_dec_def]
  \\ Cases_on ‘can_remove used (Dletrec locs funs)’
  \\ gvs [evaluate_decs_def, extend_dec_env_build_rec_env]
  >- (qexists_tac ‘f’ \\ gvs []
      \\ ‘∀g x e. MEM (g,x,e) funs ⇒ Short g ∉ names_set used’ by
           gvs [can_remove_def, EVERY_MEM, FORALL_PROD, is_used_names_set]
      \\ conj_tac
      >- (‘<|v := nsEmpty; c := nsEmpty|> +++ env2 = env2’ by
             gvs [extend_dec_env_def, sem_env_component_equality]
          \\ gvs []
          \\ irule env_rel_build_rec_env_unused
          \\ gvs [EVERY_MEM, FORALL_PROD]
          \\ asm_rewrite_tac [])
      \\ irule new_rel_unused
      \\ gvs [build_rec_env_merge, ALOOKUP_rec_env]
      \\ rpt gen_tac \\ Cases_on ‘x’
      \\ gvs [nsLookup_alist_to_ns_eq, ALOOKUP_rec_env]
      \\ rw [] \\ gvs [MEM_MAP] \\ PairCases_on ‘y’ \\ gvs [] \\ res_tac)
  \\ ‘env1.c = env2.c’ by gvs [env_rel_def]
  \\ ‘EVERY (λ(f,n,e). every_exp (one_con_check env2.c) e) funs’ by
       gvs []
  \\ gvs [extend_dec_env_build_rec_env]
  \\ qexists_tac ‘f’ \\ gvs []
  \\ conj_tac
  >- (irule env_rel_build_rec_env \\ first_assum $ irule_at Any
      \\ gvs [update_names_def, dec_binds_def, free_vars_dec_def,
              names_set_free_vars, names_set_delete_names, LIST_TO_SET_MAP,
              SUBSET_DEF, MAP_MAP_o])
  \\ irule new_rel_build_rec_env \\ first_assum $ irule_at Any
  \\ gvs [update_names_def, dec_binds_def, free_vars_dec_def,
          names_set_free_vars, names_set_delete_names, LIST_TO_SET_MAP,
          SUBSET_DEF, MAP_MAP_o]
QED

Resume evaluate_decs_v_rel[Dtype]:
  gvs [dce_decs_def, can_remove_def, prune_dec_def, evaluate_decs_def,
       update_names_def, dec_binds_def, free_vars_dec_def, delete_names_def,
       AllCaseEqs ()]
  \\ qexists_tac ‘f’
  \\ gvs [state_rel_def, extend_dec_env_def, env_rel_def]
  \\ gvs [new_rel_def]
QED

Resume evaluate_decs_v_rel[Dtabbrev]:
  gvs [dce_decs_def, can_remove_def, evaluate_decs_def]
  \\ qexists_tac ‘f’ \\ gvs [extend_dec_env_def, env_rel_def]
QED

Resume evaluate_decs_v_rel[Denv]:
  gvs [dce_decs_def, can_remove_def, prune_dec_def, evaluate_decs_def]
  \\ pairarg_tac
  \\ gvs [AllCaseEqs(), has_Denv_dec_def]
  \\ qexists_tac ‘f’
  \\ gvs [extend_dec_env_def, env_rel_def, state_rel_def]
  \\ conj_tac >- gvs [declare_env_def, AllCaseEqs()]
  \\ conj_tac
  >- (Cases
      \\ gvs [namespacePropsTheory.nsLookup_nsBind]
      \\ rewrite_tac [GSYM AND_IMP_INTRO]
      \\ ntac 2 strip_tac
      \\ DEP_REWRITE_TAC [namespacePropsTheory.nsLookup_nsBind]
      \\ gvs [] \\ CCONTR_TAC \\ gvs [is_used_names_set])
  \\ irule new_rel_unused
  \\ gvs [namespaceTheory.nsSing_def, namespaceTheory.nsLookupMod_def]
  \\ gvs [is_used_names_set]
QED

Resume evaluate_decs_v_rel[Dexn]:
  gvs [dce_decs_def, can_remove_def, prune_dec_def, evaluate_decs_def,
       update_names_def, dec_binds_def, free_vars_dec_def, delete_names_def]
  \\ qexists_tac ‘f’
  \\ gvs [state_rel_def, extend_dec_env_def, env_rel_def]
  \\ gvs [new_rel_def]
QED

Resume evaluate_decs_v_rel[Dmod]:
  gvs [dce_decs_def, evaluate_decs_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs(), NULL_EQ]
  (* the module compiles away: it is kept but emptied, and by
     dce_decs_dropped its body changes nothing that is used *)
  >- (drule dce_decs_dropped
      \\ disch_then (qspecl_then [‘strip_mod mn used’,‘ds1'’,‘used1'’] mp_tac)
      \\ simp [] \\ strip_tac
      \\ gvs [evaluate_decs_def]
      \\ qexists_tac ‘f’ \\ gvs []
      \\ conj_tac >- (irule state_rel_pure_st \\ metis_tac [])
      \\ conj_tac
      >- (irule env_rel_Dmod \\ gvs []
          \\ rw [] \\ res_tac \\ gvs [names_set_strip_mod])
      \\ irule new_rel_nsLift \\ gvs [new_rel_def, mods_rel_def]
      \\ rw [] \\ Cases_on ‘nsLookup env'.v x’ \\ gvs [] \\ res_tac)
  (* the module is kept with a non-empty body: the body's induction
     hypothesis relates the two module environments on their own, which is
     exactly what env_rel_Dmod and new_rel_nsLift need *)
  >- (last_x_assum (qspecl_then [‘f’,‘s2’,‘env2’,‘strip_mod mn used’,
                                 ‘ds1'’,‘used1'’] mp_tac)
      \\ impl_tac
      >- (gvs [has_Denv_dec_def]
          \\ drule_then irule env_rel_mono
          \\ gvs [] \\ irule SUBSET_TRANS
          \\ irule_at Any (cj 1 names_set_union_names) \\ gvs [SUBSET_DEF])
      \\ strip_tac \\ gvs [evaluate_decs_def]
      \\ qpat_x_assum ‘state_rel _ s1' _’ $ irule_at Any \\ simp []
      \\ conj_tac
      >- (irule env_rel_Dmod \\ rpt conj_tac
          >- (rw [] \\ qpat_x_assum ‘new_rel _ _ env' new2’ mp_tac
              \\ rw [new_rel_def]
              \\ gvs [names_set_strip_mod]
              \\ first_x_assum drule \\ gvs [])
          >- (qpat_x_assum ‘new_rel _ _ env' new2’ mp_tac
              \\ rw [new_rel_def])
          \\ drule_then irule env_rel_mono
          \\ gvs [] \\ irule SUBSET_TRANS
          \\ irule_at Any (cj 1 names_set_union_names) \\ gvs [SUBSET_DEF])
      \\ irule new_rel_nsLift \\ gvs [sem_env_component_equality])
  (* the body raises: dropped declarations cannot, so only the kept case
     is possible *)
  >- (drule dce_decs_dropped
      \\ disch_then (qspecl_then [‘strip_mod mn used’,‘ds1'’,‘used1'’] mp_tac)
      \\ simp [])
  \\ last_x_assum (qspecl_then [‘f’,‘s2’,‘env2’,‘strip_mod mn used’,
                                ‘ds1'’,‘used1'’] mp_tac)
  \\ impl_tac
  >- (gvs [has_Denv_dec_def]
      \\ drule_then irule env_rel_mono
      \\ gvs [] \\ irule SUBSET_TRANS
      \\ irule_at Any (cj 1 names_set_union_names) \\ gvs [SUBSET_DEF])
  \\ strip_tac \\ gvs [evaluate_decs_def]
  \\ qpat_x_assum ‘state_rel _ s1' _’ $ irule_at Any \\ simp []
QED

Resume evaluate_decs_v_rel[Dlocal]:
  gvs [dce_decs_def, evaluate_decs_def] \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs(), NULL_EQ]
  (* the local declarations are all dropped: by dce_decs_dropped they bind
     nothing that is used, so the body can be run without them *)
  >- (qpat_x_assum ‘evaluate_decs s1 env1 lds = _’ assume_tac
      \\ drule dce_decs_dropped
      \\ disch_then (qspecl_then [‘used1’,‘lds1’,‘used2’] mp_tac)
      \\ simp [] \\ strip_tac
      \\ last_x_assum
           (qspecl_then [‘f’,‘s2’,‘env2’,‘used’,‘ds1'’,‘used1’] mp_tac)
      \\ impl_tac
      >- (gvs [] \\ conj_tac
          >- (irule state_rel_pure_st \\ metis_tac [])
          \\ irule env_rel_extend_unused \\ gvs [])
      \\ strip_tac \\ gvs []
      \\ qpat_x_assum ‘state_rel _ s1' _’ $ irule_at Any \\ simp []
      \\ Cases_on ‘res1’ \\ gvs []
      \\ irule env_rel_extend_dec_env
      \\ conj_tac
      >- (qexists_tac ‘names_set used1’
          \\ conj_tac
          >- (rw [] \\ Cases_on ‘x’ \\ gvs []
              >- (qpat_x_assum ‘evaluate_decs st1 _ ds = _’ assume_tac
                  \\ drule dce_decs_binds \\ disch_then drule \\ gvs [])
              \\ qpat_x_assum ‘dce_decs used ds = _’ assume_tac
              \\ drule (cj 1 dce_decs_longs) \\ gvs [])
          \\ irule env_rel_mono
          \\ qpat_x_assum ‘env_rel f (names_set used1) env1 env2’ $ irule_at Any
          \\ gvs [])
      \\ gvs [])
  (* the local declarations are kept: the locals' induction hypothesis
     supplies the environment the body's induction hypothesis needs, and
     the body's new_rel then strips both local environments away *)
  >- (qpat_x_assum ‘∀a b c d e g. dce_decs _ lds = _ ∧ _ ⇒ _’
        (qspecl_then [‘f’,‘s2’,‘env2’,‘used1'’,‘lds1’,‘used2’] mp_tac)
      \\ impl_tac
      >- (gvs [has_Denv_dec_def]
          \\ drule_then irule env_rel_mono
          \\ gvs [] \\ irule SUBSET_TRANS
          \\ irule_at Any (cj 1 names_set_union_names) \\ gvs [SUBSET_DEF])
      \\ strip_tac \\ gvs []
      \\ last_x_assum (qspecl_then [‘f''’,‘s2''’,‘new2 +++ env2’,‘used’,
                                    ‘ds1'’,‘used1'’] mp_tac)
      \\ impl_tac >- gvs [has_Denv_dec_def]
      \\ strip_tac \\ gvs [evaluate_decs_def]
      \\ qpat_x_assum ‘state_rel _ s1' _’ $ irule_at Any
      \\ ‘f ⊑ f'''’ by imp_res_tac SUBMAP_TRANS
      \\ simp []
      \\ Cases_on ‘res1’ \\ gvs []
      \\ irule env_rel_extend_dec_env
      \\ conj_tac
      >- (qexists_tac ‘names_set used’ \\ conj_tac >- gvs []
          \\ irule env_rel_mono
          \\ qpat_x_assum
               ‘env_rel f (names_set (union_names used used2)) env1 env2’
               $ irule_at Any
          \\ gvs [] \\ irule SUBSET_TRANS
          \\ irule_at Any (cj 1 names_set_union_names) \\ gvs [SUBSET_DEF])
      \\ gvs [])
  (* dropped local declarations cannot raise *)
  >- (drule dce_decs_dropped
      \\ disch_then (qspecl_then [‘used1’,‘lds1’,‘used2’] mp_tac) \\ simp [])
  (* kept local declarations raise on both sides *)
  \\ last_x_assum (qspecl_then [‘f’,‘s2’,‘env2’,‘used1'’,‘lds1’,‘used2’] mp_tac)
  \\ impl_tac
  >- (gvs [has_Denv_dec_def]
      \\ drule_then irule env_rel_mono
      \\ gvs [] \\ irule SUBSET_TRANS
      \\ irule_at Any (cj 1 names_set_union_names) \\ gvs [SUBSET_DEF])
  \\ strip_tac \\ gvs [evaluate_decs_def]
  \\ qpat_x_assum ‘state_rel _ s1' _’ $ irule_at Any \\ simp []
QED

Finalise evaluate_decs_v_rel[local]

Theorem env_rel_nsEmpty[local,simp]:
  env.v = nsEmpty ⇒ env_rel f names env env
Proof
  gvs [env_rel_def] \\ Cases \\ gvs [nsEmpty_def, nsLookup_def]
QED

Theorem evaluate_prog_with_clock_correct[local]:
  evaluate_prog_with_clock s env k prog = (ffi,r1) ∧
  r1 ≠ Rerr (Rabort Rtype_error) ∧
  dce_decs empty_names prog = (res,x') ∧
  ¬has_Denv_decs (append res) ∧
  (∀x. s.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev) ∧
  env.v = nsEmpty ⇒
  ∃r2. evaluate_prog_with_clock s env k (append res) = (ffi,r2) ∧
       result_rel (λx y. T) (λx y. T) r1 r2
Proof
  rpt strip_tac
  \\ gvs [evaluate_prog_with_clock_def]
  \\ Cases_on ‘evaluate_decs (s with clock := k) env prog’ \\ gvs []
  \\ drule evaluate_decs_v_rel \\ gvs []
  \\ disch_then $ qspecl_then [‘FEMPTY’,‘s with clock := k’,‘env’,
                               ‘empty_names’,‘res’,‘x'’] mp_tac
  \\ gvs [env_rel_nsEmpty]
  \\ strip_tac \\ gvs [] \\ gvs [state_rel_def]
  \\ Cases_on ‘r’ \\ Cases_on ‘res2’ \\ gvs []
  \\ Cases_on ‘e’ \\ Cases_on ‘e'’ \\ gvs []
QED

Theorem dce_decs_semantics[local]:
  env.v = nsEmpty ∧
  dce_decs empty_names prog = (res,x) ∧
  ¬has_Denv_decs (append res) ∧
  (∀x. s.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev) ∧
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (append res) outcome
Proof
  Cases_on ‘outcome’ \\ fs [SF CONJ_ss]
  >~ [‘Terminate x y’] >-
   (rw [semantics_prog_def]
    \\ drule_all evaluate_prog_with_clock_correct
    \\ strip_tac
    \\ first_x_assum $ irule_at Any
    \\ Cases_on ‘r’ \\ gvs [result_rel_def]
    \\ Cases_on ‘e’ \\ gvs [exc_rel_def])
  \\ rw [semantics_prog_def]
  >-
   (first_x_assum $ qspec_then ‘k’ strip_assume_tac
    \\ drule evaluate_prog_with_clock_correct \\ gvs [])
  \\ pop_assum mp_tac
  \\ match_mp_tac (METIS_PROVE [] “b1=b2 ⇒ b1 ⇒ b2”)
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw [FUN_EQ_THM]
  \\ Cases_on ‘evaluate_prog_with_clock s env k prog’ \\ fs []
  \\ drule evaluate_prog_with_clock_correct \\ fs []
  \\ rpt $ first_x_assum $ qspec_then ‘k’ assume_tac
  \\ gvs []
QED

Theorem compile_semantics:
  env.v = nsEmpty ∧
  (∀x. s.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev) ∧
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (source_dce$compile_decs prog) outcome
Proof
  rw [source_dceTheory.compile_decs_def]
  \\ Cases_on ‘dce_decs empty_names prog’
  \\ irule dce_decs_semantics \\ gvs []
  \\ metis_tac []
QED
