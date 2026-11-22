(*
  Correctness for the source_eval_init pass, which runs within evalSem
  before source_to_source. The input program runs in the EvalPending
  mode, and the compiled program runs in the EvalDecs mode.
*)
Theory source_eval_initProof
Ancestors
  ast mlstring namespace semanticPrimitives semanticPrimitivesProps
  namespaceProps source_eval_init evalSem
  evalSemProps source_adjust_decsProof source_eval_semProof
Libs
  preamble

(* ------------------------------------------------------------------ *
   Renaming
 * ------------------------------------------------------------------ *)

Theorem explode_rename:
  explode (rename n) =
    case explode n of #"$"::_ => #"$"::explode n | _ => explode n
Proof
  rw [rename_def] \\ every_case_tac \\ simp []
QED

Theorem rename_11[simp]:
  rename x = rename y ⇔ x = y
Proof
  eq_tac \\ simp []
  \\ disch_then (mp_tac o AP_TERM “explode”)
  \\ rewrite_tac [explode_rename]
  \\ every_case_tac \\ rw []
  \\ metis_tac [mlstringTheory.explode_11]
QED

Theorem rename_not_prelude[simp]:
  rename n ≠ «$init» ∧ rename n ≠ «$eval» ∧
  «$init» ≠ rename n ∧ «$eval» ≠ rename n
Proof
  rw [] \\ disch_then (mp_tac o AP_TERM “explode”)
  \\ rewrite_tac [explode_rename]
  \\ every_case_tac \\ gvs []
QED

Theorem rename_id_11[simp]:
  ∀x y. rename_id x = rename_id y ⇔ x = y
Proof
  Induct \\ Cases_on ‘y’ \\ simp [rename_id_def]
QED

Theorem rename_id_not_prelude[simp]:
  rename_id id ≠ Short «$init» ∧ rename_id id ≠ Short «$eval»
Proof
  Cases_on ‘id’ \\ simp [rename_id_def]
QED

Theorem id_to_mods_rename_id[simp]:
  ∀id. id_to_mods (rename_id id) = id_to_mods id
Proof
  Induct \\ simp [rename_id_def, id_to_mods_def]
QED

Overload compile_funs = “MAP (λ(f:mlstring,x:mlstring,e). (rename f, rename x, compile_exp e))”

Theorem MAP_FST_compile_funs:
  MAP (λ(f,x,e). f) (compile_funs funs) = MAP rename (MAP (λ(f,x,e). f) funs)
Proof
  Induct_on ‘funs’ \\ simp [FORALL_PROD]
QED

Theorem ALL_DISTINCT_MAP_rename[simp]:
  ALL_DISTINCT (MAP rename xs) = ALL_DISTINCT xs
Proof
  Induct_on ‘xs’ \\ simp [MEM_MAP]
QED

Theorem find_recfun_compile_funs:
  find_recfun (rename n) (compile_funs funs) =
  OPTION_MAP (λ(x,e). (rename x, compile_exp e)) (find_recfun n funs)
Proof
  Induct_on ‘funs’ \\ simp [FORALL_PROD]
  \\ once_rewrite_tac [find_recfun_def] \\ rw []
QED

Theorem pat_bindings_compile_pat:
  (∀p. pat_bindings (compile_pat p) = MAP rename (pat_bindings p)) ∧
  (∀ps. pats_bindings (MAP compile_pat ps) = MAP rename (pats_bindings ps))
Proof
  ho_match_mp_tac pat_bindings_ind
  \\ rw [pat_bindings_def, compile_pat_def]
QED

Theorem ALL_DISTINCT_pat_bindings_compile_pat[simp]:
  ALL_DISTINCT (pat_bindings (compile_pat p)) = ALL_DISTINCT (pat_bindings p)
Proof
  simp [pat_bindings_compile_pat]
QED

Theorem check_exp_constructors_compile_exp[simp]:
  ∀e envc. check_exp_constructors envc (compile_exp e) =
           check_exp_constructors envc e
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rw [compile_exp_def]
  \\ every_case_tac
  \\ gvs [check_exp_constructors_def, EVERY_MAP, EVERY_MEM, FORALL_PROD,
          do_con_check_def]
  \\ metis_tac []
QED

(* ------------------------------------------------------------------ *
   Namespaces with renamed variable names
 * ------------------------------------------------------------------ *)

Theorem nsLookup_nsAppend_Short:
  nsLookup (nsAppend a b) (Short n) =
    case nsLookup a (Short n) of NONE => nsLookup b (Short n) | r => r
Proof
  Cases_on ‘a’ \\ Cases_on ‘b’
  \\ simp [nsAppend_def, nsLookup_def, alistTheory.ALOOKUP_APPEND]
  \\ every_case_tac
QED

Theorem nsLookup_Long:
  nsLookup a (Long m id) =
    case nsLookupMod a [m] of NONE => NONE | SOME x => nsLookup x id
Proof
  Cases_on ‘a’ \\ simp [nsLookup_def, nsLookupMod_def]
  \\ every_case_tac \\ simp [nsLookupMod_def]
QED

Theorem nsLookupMod_cons:
  nsLookupMod a (m::p) =
    case nsLookupMod a [m] of NONE => NONE | SOME x => nsLookupMod x p
Proof
  Cases_on ‘a’ \\ simp [nsLookupMod_def]
  \\ every_case_tac \\ simp [nsLookupMod_def]
QED

Theorem nsLookupMod_nsAppend_sing:
  nsLookupMod (nsAppend a b) [m] =
    case nsLookupMod a [m] of NONE => nsLookupMod b [m] | r => r
Proof
  Cases_on ‘a’ \\ Cases_on ‘b’
  \\ simp [nsAppend_def, nsLookupMod_def, alistTheory.ALOOKUP_APPEND]
  \\ every_case_tac \\ gvs [nsLookupMod_def]
QED

(* ns2 binds the renamed names of ns1, and also the names in X *)
Definition ns_rel_def:
  ns_rel R X (ns1:(mlstring,mlstring,'a) namespace)
             (ns2:(mlstring,mlstring,'b) namespace) ⇔
    (∀id. OPTREL R (nsLookup ns1 id) (nsLookup ns2 (rename_id id))) ∧
    (∀p. nsLookupMod ns1 p = NONE ⇔ nsLookupMod ns2 p = NONE) ∧
    (∀id x. nsLookup ns2 id = SOME x ⇒ (∃id0. id = rename_id id0) ∨ id ∈ X)
End

Theorem ns_rel_mono[mono]:
  (∀x y. R x y ⇒ R' x y) ⇒ ns_rel R X a b ⇒ ns_rel R' X a b
Proof
  rw [ns_rel_def] \\ metis_tac [OPTREL_MONO]
QED

Theorem ns_rel_nsAppend:
  ns_rel R {} a1 a2 ∧ ns_rel R X b1 b2 ⇒
  ns_rel R X (nsAppend a1 b1) (nsAppend a2 b2)
Proof
  rw [ns_rel_def]
  >- (
    Cases_on ‘id’ \\ simp [rename_id_def, nsLookup_nsAppend_Short]
    >- (
      qpat_x_assum ‘∀id. OPTREL R (nsLookup a1 id) _’ (qspec_then ‘Short n’ mp_tac)
      \\ qpat_x_assum ‘∀id. OPTREL R (nsLookup b1 id) _’ (qspec_then ‘Short n’ mp_tac)
      \\ simp [rename_id_def]
      \\ every_case_tac \\ simp [OPTREL_def])
    \\ qpat_x_assum ‘∀id. OPTREL R (nsLookup a1 id) _’ (qspec_then ‘Long m i’ mp_tac)
    \\ qpat_x_assum ‘∀id. OPTREL R (nsLookup b1 id) _’ (qspec_then ‘Long m i’ mp_tac)
    \\ qpat_x_assum ‘∀p. nsLookupMod a1 p = NONE ⇔ _’ (qspec_then ‘[m]’ mp_tac)
    \\ simp [rename_id_def, nsLookup_Long, nsLookupMod_nsAppend_sing]
    \\ every_case_tac \\ simp [OPTREL_def])
  >- (
    Cases_on ‘p’ \\ simp [nsLookupMod_def]
    \\ qpat_assum ‘∀p. nsLookupMod a1 p = NONE ⇔ _’ (qspec_then ‘h::t’ mp_tac)
    \\ qpat_x_assum ‘∀p. nsLookupMod b1 p = NONE ⇔ _’ (qspec_then ‘h::t’ mp_tac)
    \\ qpat_x_assum ‘∀p. nsLookupMod a1 p = NONE ⇔ _’ (qspec_then ‘[h]’ mp_tac)
    \\ once_rewrite_tac [nsLookupMod_cons]
    \\ simp [nsLookupMod_nsAppend_sing]
    \\ every_case_tac \\ simp [nsLookupMod_def])
  \\ Cases_on ‘id’ \\ gvs [nsLookup_nsAppend_Short]
  >- (every_case_tac \\ gvs [] \\ metis_tac [])
  \\ qpat_x_assum ‘∀id x. nsLookup a2 id = _ ⇒ _’ (qspec_then ‘Long m i’ mp_tac)
  \\ qpat_x_assum ‘∀id x. nsLookup b2 id = _ ⇒ _’ (qspec_then ‘Long m i’ mp_tac)
  \\ pop_assum mp_tac
  \\ simp [nsLookup_Long, nsLookupMod_nsAppend_sing]
  \\ every_case_tac
QED

Theorem ns_rel_nsAppend_prelude:
  ns_rel R {} a1 a2 ⇒
  nsLookup (nsAppend a2 b2) (Short «$init») = nsLookup b2 (Short «$init») ∧
  nsLookup (nsAppend a2 b2) (Short «$eval») = nsLookup b2 (Short «$eval»)
Proof
  rw [ns_rel_def, nsLookup_nsAppend_Short]
  \\ every_case_tac \\ gvs []
  \\ res_tac \\ gvs []
QED

Theorem ns_rel_alist_to_ns:
  LIST_REL (λ(n1,x1) (n2,x2). n2 = rename n1 ∧ R x1 x2) l1 l2 ⇒
  ns_rel R {} (alist_to_ns l1) (alist_to_ns l2)
Proof
  rw [ns_rel_def]
  >- (
    Cases_on ‘id’ \\ simp [rename_id_def, alist_to_ns_def, nsLookup_def]
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘l2’ \\ Induct_on ‘l1’ \\ simp [FORALL_PROD, PULL_EXISTS]
    \\ rw [] \\ simp [])
  >- (Cases_on ‘p’ \\ simp [nsLookupMod_def])
  \\ Cases_on ‘id’ \\ gvs [alist_to_ns_def, nsLookup_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ qid_spec_tac ‘l2’ \\ Induct_on ‘l1’ \\ simp [FORALL_PROD, PULL_EXISTS]
  \\ rw [] \\ gvs [AllCaseEqs()]
  >- (qexists_tac ‘Short p_1’ \\ simp [rename_id_def])
  \\ metis_tac []
QED

Theorem nsBind_alist:
  nsBind n v ns = nsAppend (alist_to_ns [(n,v)]) ns
Proof
  Cases_on ‘ns’ \\ simp [nsBind_def, nsAppend_def, alist_to_ns_def]
QED

Theorem nsSing_alist:
  nsSing n v = alist_to_ns [(n,v)]
Proof
  rewrite_tac [nsSing_def, alist_to_ns_def]
QED

Theorem nsEmpty_alist:
  nsEmpty = alist_to_ns []
Proof
  simp [nsEmpty_def, alist_to_ns_def]
QED

Theorem ns_rel_nsBind:
  R x1 x2 ∧ ns_rel R X a1 a2 ⇒
  ns_rel R X (nsBind n x1 a1) (nsBind (rename n) x2 a2)
Proof
  rewrite_tac [nsBind_alist] \\ strip_tac
  \\ irule ns_rel_nsAppend
  \\ conj_tac >- simp []
  \\ irule ns_rel_alist_to_ns \\ simp []
QED

Theorem ns_rel_nsLift:
  ns_rel R {} a1 a2 ⇒ ns_rel R {} (nsLift mn a1) (nsLift mn a2)
Proof
  rw [ns_rel_def, nsLookup_nsLift, nsLookupMod_nsLift]
  >- (Cases_on ‘id’ \\ simp [rename_id_def] \\ rw [] \\ simp [OPTREL_def])
  >- (Cases_on ‘p’ \\ simp [] \\ rw [])
  \\ Cases_on ‘id’ \\ gvs [AllCaseEqs()]
  \\ res_tac \\ gvs []
  \\ qexists_tac ‘Long m id0’ \\ simp [rename_id_def]
QED

Theorem nsLookupMod_SOME_nsLookup:
  ∀p a m id. nsLookupMod a p = SOME m ⇒
    nsLookup m id = nsLookup a (FOLDR Long id p)
Proof
  Induct \\ simp [nsLookupMod_def]
  \\ rpt gen_tac
  \\ once_rewrite_tac [nsLookupMod_cons]
  \\ simp [nsLookup_Long, AllCaseEqs(), PULL_EXISTS]
  \\ metis_tac []
QED

Theorem nsLookupMod_SOME_nsLookupMod:
  ∀p a m q. nsLookupMod a p = SOME m ⇒
    nsLookupMod m q = nsLookupMod a (p ++ q)
Proof
  Induct \\ simp [nsLookupMod_def]
  \\ rpt gen_tac
  \\ once_rewrite_tac [nsLookupMod_cons]
  \\ simp [AllCaseEqs(), PULL_EXISTS]
  \\ metis_tac []
QED

Theorem rename_id_FOLDR_Long:
  ∀p. rename_id (FOLDR Long id p) = FOLDR Long (rename_id id) p
Proof
  Induct \\ simp [rename_id_def]
QED

Theorem FOLDR_Long_eq_rename_id:
  ∀p id id0. FOLDR Long id p = rename_id id0 ⇒ ∃id1. id = rename_id id1
Proof
  Induct
  >- (rw [] \\ qexists_tac ‘id0’ \\ simp [])
  \\ rw [] \\ Cases_on ‘id0’ \\ gvs [rename_id_def]
QED

Theorem ns_rel_nsOpen:
  ns_rel R X a1 a2 ∧ (∀x. x ∈ X ⇒ ∃n. x = Short n) ∧
  nsOpen p a1 = SOME m1 ⇒
  ∃m2. nsOpen p a2 = SOME m2 ∧ ns_rel R {} m1 m2
Proof
  rw [nsOpen_eq_some]
  \\ gvs [ns_rel_def]
  \\ ‘nsLookupMod a2 p ≠ NONE’ by metis_tac [NOT_NONE_SOME]
  \\ Cases_on ‘nsLookupMod a2 p’ \\ gvs []
  \\ rename1 ‘nsLookupMod a2 p = SOME m2’
  \\ imp_res_tac nsLookupMod_SOME_nsLookup
  \\ imp_res_tac nsLookupMod_SOME_nsLookupMod
  \\ simp [GSYM rename_id_FOLDR_Long]
  \\ rw []
  \\ qpat_x_assum ‘∀id x. nsLookup a2 id = SOME x ⇒ _’ drule
  \\ strip_tac
  >- metis_tac [FOLDR_Long_eq_rename_id]
  \\ res_tac \\ Cases_on ‘p’ \\ gvs []
QED

Theorem ns_rel_FOLDR_rec[local]:
  ∀l. (∀f. MEM f (MAP (λ(f,x,e). f) l) ⇒
           R (Recclosure env1 funs f) (Recclosure env2 funs2 (rename f))) ∧
      ns_rel R X a1 a2 ⇒
      ns_rel R X
        (FOLDR (λ(f,x,e) env'. nsBind f (Recclosure env1 funs f) env') a1 l)
        (FOLDR (λ(f,x,e) env'. nsBind f (Recclosure env2 funs2 f) env') a2
           (compile_funs l))
Proof
  Induct \\ simp [FORALL_PROD]
  \\ rw [] \\ irule ns_rel_nsBind \\ gvs []
QED

Theorem ns_rel_build_rec_env:
  (∀f. MEM f (MAP (λ(f,x,e). f) funs) ⇒
       R (Recclosure env1 funs f)
         (Recclosure env2 (compile_funs funs) (rename f))) ∧
  ns_rel R X a1 a2 ⇒
  ns_rel R X (build_rec_env funs env1 a1)
             (build_rec_env (compile_funs funs) env2 a2)
Proof
  rw [build_rec_env_def]
  \\ irule ns_rel_FOLDR_rec \\ simp []
QED

(* ------------------------------------------------------------------ *
   Value relation
 * ------------------------------------------------------------------ *)

Overload prelude_names = “{Short «$init»; Short «$eval»}”

(* fr maps the references of the input program to those of the compiled
   program, and pe is the environment of the $init and $eval closures *)
Inductive v_rel:
[~Litv:]
  (∀fr pe l. v_rel fr pe (Litv l) (Litv l))
[~Conv:]
  (∀fr pe t xs ys.
     LIST_REL (v_rel fr pe) xs ys ⇒ v_rel fr pe (Conv t xs) (Conv t ys))
[~Vectorv:]
  (∀fr pe xs ys.
     LIST_REL (v_rel fr pe) xs ys ⇒ v_rel fr pe (Vectorv xs) (Vectorv ys))
[~Loc:]
  (∀fr pe b l1 l2.
     FLOOKUP fr l1 = SOME l2 ⇒ v_rel fr pe (Loc b l1) (Loc b l2))
[~Closure:]
  (∀fr pe env1 env2 n e.
     env_rel fr pe env1 env2 ⇒
     v_rel fr pe (Closure env1 n e) (Closure env2 (rename n) (compile_exp e)))
[~Recclosure:]
  (∀fr pe env1 env2 funs n.
     env_rel fr pe env1 env2 ⇒
     v_rel fr pe (Recclosure env1 funs n)
                 (Recclosure env2 (compile_funs funs) (rename n)))
[~Env:]
  (∀fr pe env1 env2 id.
     env_rel fr pe env1 env2 ⇒ v_rel fr pe (Env env1 id) (Env env2 id))
[~env_rel:]
  (∀fr pe env1 env2.
     env2.c = env1.c ∧
     ns_rel (v_rel fr pe) prelude_names env1.v env2.v ∧
     nsLookup env2.v (Short «$init») = SOME (Closure pe «x» init_body) ∧
     nsLookup env2.v (Short «$eval») = SOME (Closure pe «x» eval_body) ⇒
     env_rel fr pe env1 env2)
End

Theorem v_rel_def =
  [“v_rel fr pe (Conv opt vs) v”,
   “v_rel fr pe (Closure env n x) v”,
   “v_rel fr pe (Recclosure env f n) v”,
   “v_rel fr pe (Vectorv vs) v”,
   “v_rel fr pe (Litv lit) v”,
   “v_rel fr pe (Loc b loc) v”,
   “v_rel fr pe (Env env ns) v”]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem env_rel_def =
  “env_rel fr pe env1 env2” |> SIMP_CONV std_ss [Once v_rel_cases];

(* relation for the declarations that a declaration adds *)
Definition nenv_rel_def:
  nenv_rel fr pe (env1:v sem_env) (env2:v sem_env) ⇔
    env2.c = env1.c ∧ ns_rel (v_rel fr pe) {} env1.v env2.v
End

Theorem v_rel_SUBMAP:
  (∀fr pe v1 v2. v_rel fr pe v1 v2 ⇒
     ∀fr'. fr ⊑ fr' ⇒ v_rel fr' pe v1 v2) ∧
  (∀fr pe env1 env2. env_rel fr pe env1 env2 ⇒
     ∀fr'. fr ⊑ fr' ⇒ env_rel fr' pe env1 env2)
Proof
  ho_match_mp_tac v_rel_ind \\ rw []
  \\ simp [Once v_rel_cases]
  >~ [‘FLOOKUP’] >- metis_tac [FLOOKUP_SUBMAP]
  >~ [‘ns_rel’] >- (
    irule ns_rel_mono \\ first_assum (irule_at Any) \\ simp [])
  \\ irule LIST_REL_mono \\ first_assum (irule_at Any) \\ simp []
QED

(* used to forget references that only the compiled program has *)
Theorem v_rel_restrict:
  (∀fr1 pe v1 v2. v_rel fr1 pe v1 v2 ⇒
     ∀fr w. fr ⊑ fr1 ∧ v_rel fr pe v1 w ⇒ v_rel fr pe v1 v2) ∧
  (∀fr1 pe env1 env2. env_rel fr1 pe env1 env2 ⇒
     ∀fr env3. fr ⊑ fr1 ∧ env_rel fr pe env1 env3 ⇒ env_rel fr pe env1 env2)
Proof
  ho_match_mp_tac v_rel_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once v_rel_cases] \\ rw []
  \\ simp [Once v_rel_cases]
  >~ [‘FLOOKUP’] >- (
    imp_res_tac FLOOKUP_SUBMAP \\ gvs [])
  >~ [‘ns_rel’] >- (
    gvs [ns_rel_def] \\ rw []
    \\ rpt (first_x_assum (qspec_then ‘id’ mp_tac))
    \\ Cases_on ‘nsLookup env1.v id’ \\ simp [OPTREL_def]
    \\ rw [] \\ gvs [] \\ metis_tac [])
  \\ gvs [LIST_REL_EL_EQN] \\ metis_tac []
QED

Theorem env_rel_extend_dec_env:
  nenv_rel fr pe n1 n2 ∧ env_rel fr pe e1 e2 ⇒
  env_rel fr pe (extend_dec_env n1 e1) (extend_dec_env n2 e2)
Proof
  rw [nenv_rel_def, env_rel_def, extend_dec_env_def]
  >- (irule ns_rel_nsAppend \\ simp [])
  \\ drule ns_rel_nsAppend_prelude \\ simp []
QED

Theorem nenv_rel_extend_dec_env:
  nenv_rel fr pe n1 n2 ∧ nenv_rel fr pe m1 m2 ⇒
  nenv_rel fr pe (extend_dec_env n1 m1) (extend_dec_env n2 m2)
Proof
  rw [nenv_rel_def, extend_dec_env_def]
  \\ irule ns_rel_nsAppend \\ simp []
QED

Theorem env_rel_nsBind:
  env_rel fr pe e1 e2 ∧ v_rel fr pe x1 x2 ⇒
  env_rel fr pe (e1 with v := nsBind n x1 e1.v)
                (e2 with v := nsBind (rename n) x2 e2.v)
Proof
  rw [env_rel_def]
  \\ irule ns_rel_nsBind \\ simp []
QED

Theorem env_rel_nsOptBind:
  env_rel fr pe e1 e2 ∧ v_rel fr pe x1 x2 ⇒
  env_rel fr pe (e1 with v := nsOptBind xo x1 e1.v)
                (e2 with v := nsOptBind (OPTION_MAP rename xo) x2 e2.v)
Proof
  Cases_on ‘xo’ \\ rw [nsOptBind_def]
  \\ irule env_rel_nsBind \\ simp []
QED

Theorem env_rel_alist_to_ns:
  env_rel fr pe e1 e2 ∧
  LIST_REL (λ(n1,x1) (n2,x2). n2 = rename n1 ∧ v_rel fr pe x1 x2) bs1 bs2 ⇒
  env_rel fr pe (e1 with v := nsAppend (alist_to_ns bs1) e1.v)
                (e2 with v := nsAppend (alist_to_ns bs2) e2.v)
Proof
  rw [env_rel_def]
  \\ drule_then assume_tac ns_rel_alist_to_ns
  >- (irule ns_rel_nsAppend \\ simp [])
  \\ drule ns_rel_nsAppend_prelude \\ simp []
QED

Theorem nsLookup_build_rec_env_prelude[local]:
  nsLookup (build_rec_env (compile_funs funs) env base) (Short «$init») =
  nsLookup base (Short «$init») ∧
  nsLookup (build_rec_env (compile_funs funs) env base) (Short «$eval») =
  nsLookup base (Short «$eval»)
Proof
  rw [nsLookup_build_rec_env] \\ gvs [MEM_MAP, EXISTS_PROD]
QED

Theorem env_rel_build_rec_env:
  env_rel fr pe e1 e2 ∧ env_rel fr pe cl1 cl2 ⇒
  env_rel fr pe (e1 with v := build_rec_env funs cl1 e1.v)
                (e2 with v := build_rec_env (compile_funs funs) cl2 e2.v)
Proof
  rw [] \\ simp [Once env_rel_def]
  \\ gvs [Once env_rel_def, nsLookup_build_rec_env_prelude]
  \\ irule ns_rel_build_rec_env \\ simp [v_rel_def]
QED

Theorem nenv_rel_build_rec_env:
  env_rel fr pe cl1 cl2 ⇒
  nenv_rel fr pe <| v := build_rec_env funs cl1 nsEmpty; c := nsEmpty |>
                 <| v := build_rec_env (compile_funs funs) cl2 nsEmpty;
                    c := nsEmpty |>
Proof
  rw [nenv_rel_def]
  \\ irule ns_rel_build_rec_env \\ simp [v_rel_def]
  \\ rewrite_tac [nsEmpty_alist]
  \\ irule ns_rel_alist_to_ns \\ simp []
QED

Theorem nenv_rel_alist_to_ns:
  LIST_REL (λ(n1,x1) (n2,x2). n2 = rename n1 ∧ v_rel fr pe x1 x2) bs1 bs2 ⇒
  nenv_rel fr pe <| v := alist_to_ns bs1; c := c |>
                 <| v := alist_to_ns bs2; c := c |>
Proof
  rw [nenv_rel_def] \\ irule ns_rel_alist_to_ns \\ simp []
QED

Theorem nenv_rel_nsEmpty:
  nenv_rel fr pe <| v := nsEmpty; c := c |> <| v := nsEmpty; c := c |>
Proof
  rw [nenv_rel_def] \\ rewrite_tac [nsEmpty_alist]
  \\ irule ns_rel_alist_to_ns \\ simp []
QED

Theorem nenv_rel_nsSing:
  v_rel fr pe x1 x2 ⇒
  nenv_rel fr pe <| v := nsSing n x1; c := nsEmpty |>
                 <| v := nsSing (rename n) x2; c := nsEmpty |>
Proof
  rw [nenv_rel_def] \\ rewrite_tac [nsSing_alist]
  \\ irule ns_rel_alist_to_ns \\ simp []
QED

Theorem nenv_rel_nsLift:
  nenv_rel fr pe n1 n2 ⇒
  nenv_rel fr pe <| v := nsLift mn n1.v; c := nsLift mn n1.c |>
                 <| v := nsLift mn n2.v; c := nsLift mn n2.c |>
Proof
  rw [nenv_rel_def] \\ irule ns_rel_nsLift \\ simp []
QED

Theorem env_rel_open_dec_env:
  env_rel fr pe e1 e2 ∧ open_dec_env path e1 = SOME o1 ⇒
  ∃o2. open_dec_env path e2 = SOME o2 ∧ nenv_rel fr pe o1 o2
Proof
  rw [env_rel_def, open_dec_env_def, AllCaseEqs(), nenv_rel_def]
  \\ drule ns_rel_nsOpen
  \\ disch_then (qspecl_then [‘path’,‘env_v’] mp_tac)
  \\ impl_tac >- (rw [] \\ simp [])
  \\ rw [] \\ simp []
QED

Theorem nenv_rel_SUBMAP:
  nenv_rel fr pe n1 n2 ∧ fr ⊑ fr' ⇒ nenv_rel fr' pe n1 n2
Proof
  rw [nenv_rel_def] \\ irule ns_rel_mono
  \\ first_assum (irule_at Any) \\ metis_tac [v_rel_SUBMAP]
QED

Theorem env_rel_SUBMAP:
  env_rel fr pe e1 e2 ∧ fr ⊑ fr' ⇒ env_rel fr' pe e1 e2
Proof
  metis_tac [v_rel_SUBMAP]
QED

(* ------------------------------------------------------------------ *
   References and states
 * ------------------------------------------------------------------ *)

Definition ref_rel_def:
  ref_rel f (Refv v) (Refv w) = f v w ∧
  ref_rel f (Varray vs) (Varray ws) = LIST_REL f vs ws ∧
  ref_rel f (W8array a) (W8array b) = (a = b) ∧
  ref_rel f (Thunk m1 v1) (Thunk m2 v2) = (m1 = m2 ∧ f v1 v2) ∧
  ref_rel f _ _ = F
End

Theorem ref_rel_mono:
  ref_rel P x y ∧ (∀a b. P a b ⇒ Q a b) ⇒ ref_rel Q x y
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ rw [ref_rel_def]
  \\ irule LIST_REL_mono \\ first_assum (irule_at Any) \\ simp []
QED

Definition refs_rel_def:
  refs_rel fr pe (refs1:v store_v list) (refs2:v store_v list) ⇔
    FDOM fr = count (LENGTH refs1) ∧
    (∀n. n < LENGTH refs1 ⇒
         ∃m. FLOOKUP fr n = SOME m ∧ m < LENGTH refs2 ∧
             ref_rel (v_rel fr pe) (EL n refs1) (EL m refs2)) ∧
    (∀n1 n2 m. FLOOKUP fr n1 = SOME m ∧ FLOOKUP fr n2 = SOME m ⇒ n1 = n2)
End

Definition prelude_loc_def:
  prelude_loc pe n =
    case nsLookup pe.v (Short n) of SOME (Loc _ p) => p | _ => 0
End

Definition prelude_vals_def:
  prelude_vals pe (refs:v store_v list) =
    MAP (λn. EL (prelude_loc pe n) refs) [«pending»; «state»; «compiler»]
End

Definition prelude_ok_def:
  prelude_ok fr pe (refs:v store_v list) ⇔
    (∀n. MEM n [«pending»; «state»; «compiler»] ⇒
         nsLookup pe.v (Short n) = SOME (Loc T (prelude_loc pe n)) ∧
         prelude_loc pe n < LENGTH refs ∧
         prelude_loc pe n ∉ FRANGE fr) ∧
    ALL_DISTINCT (MAP (prelude_loc pe) [«pending»; «state»; «compiler»])
End

(* the eval states of the input and the compiled program *)
Definition eval_rel_def:
  (eval_rel C fr pe (SOME (EvalPending r)) (t:'ffi evalSem$state) ⇔
     t.eval_state = SOME (EvalDecs (adjust_decs inc_compile_decs C r)) ∧
     decs_factor inc_compile_decs C r ∧
     EL (prelude_loc pe «pending») t.refs = Refv (Litv (IntLit 1)) ∧
     (∃v. EL (prelude_loc pe «state») t.refs = Refv v) ∧
     (∃v. EL (prelude_loc pe «compiler») t.refs = Refv v)) ∧
  (eval_rel C fr pe (SOME (EvalRun r)) t ⇔
     (∃cl0. t.eval_state =
              SOME (EvalDecs (adjust_decs inc_compile_decs C
                                (r with closure := cl0)))) ∧
     decs_factor inc_compile_decs C r ∧
     EL (prelude_loc pe «pending») t.refs = Refv (Litv (IntLit 0)) ∧
     (∃v. EL (prelude_loc pe «state») t.refs = Refv v ∧
          v_rel fr pe r.compiler_state v) ∧
     (∃c'. EL (prelude_loc pe «compiler») t.refs = Refv c' ∧
           v_rel fr pe r.closure c' ∧
           compiler_closure r.compiler r.decode_decs r.compiler_state
             r.closure (:'ffi))) ∧
  (eval_rel C fr pe es t ⇔ F)
End

(* H is true exactly when the input program has an eval state. Without
   an eval state, the input program cannot call Eval and G fixes the
   eval state and the prelude references of the compiled program. *)
Definition state_rel_def:
  state_rel H G C fr pe (s:'ffi evalSem$state) (t:'ffi evalSem$state) ⇔
    t.clock = s.clock ∧ t.ffi = s.ffi ∧
    t.next_type_stamp = s.next_type_stamp ∧
    t.next_exn_stamp = s.next_exn_stamp ∧
    t.ptr_eq_oracle = s.ptr_eq_oracle ∧
    refs_rel fr pe s.refs t.refs ∧ prelude_ok fr pe t.refs ∧
    (if s.eval_state = NONE then
       ¬H ∧ G = (t.eval_state, prelude_vals pe t.refs)
     else H ∧ eval_rel C fr pe s.eval_state t)
End

Definition res_rel_def[simp]:
  (res_rel f g (Rval e) (Rval e1) ⇔ f e e1) ∧
  (res_rel f g (Rerr (Rraise e)) (Rerr (Rraise e1)) ⇔ g e e1) ∧
  (res_rel f g (Rerr (Rabort e)) (Rerr (Rabort e1)) ⇔ e = e1) ∧
  (res_rel f g x y ⇔ F)
End

Theorem res_rel_abort[simp]:
  res_rel f g (Rerr (Rabort a)) r ⇔ r = Rerr (Rabort a)
Proof
  Cases_on ‘r’ \\ simp [] \\ Cases_on ‘e’ \\ simp [] \\ metis_tac []
QED

Theorem res_rel_Rval[simp]:
  res_rel f g (Rval x) r ⇔ ∃y. r = Rval y ∧ f x y
Proof
  Cases_on ‘r’ \\ simp [] \\ Cases_on ‘e’ \\ simp []
QED

Theorem res_rel_Rraise[simp]:
  res_rel f g (Rerr (Rraise x)) r ⇔ ∃y. r = Rerr (Rraise y) ∧ g x y
Proof
  Cases_on ‘r’ \\ simp [] \\ Cases_on ‘e’ \\ simp []
QED

Theorem LIST_REL_v_rel_SUBMAP:
  LIST_REL (v_rel fr pe) xs ys ∧ fr ⊑ fr' ⇒ LIST_REL (v_rel fr' pe) xs ys
Proof
  rw [] \\ irule LIST_REL_mono \\ first_assum (irule_at Any)
  \\ metis_tac [v_rel_SUBMAP]
QED

(* ------------------------------------------------------------------ *
   Primitives
 * ------------------------------------------------------------------ *)

Theorem v_rel_Boolv:
  v_rel fr pe v w ⇒ (v = Boolv b ⇔ w = Boolv b)
Proof
  Cases_on ‘b’ \\ rw [Boolv_def] \\ eq_tac \\ rw []
  \\ gvs [v_rel_def]
  \\ Cases_on ‘v’ \\ gvs [v_rel_def]
QED

Theorem data_v_v_rel:
  (∀v. data_v v ⇒ ∀w. v_rel fr pe v w ⇔ w = v) ∧
  (∀vs. data_v_list vs ⇒ ∀ws. LIST_REL (v_rel fr pe) vs ws ⇔ ws = vs)
Proof
  ho_match_mp_tac data_v_ind \\ rw []
  >- (Cases_on ‘v’ \\ gvs [Once data_v_def, v_rel_def])
  \\ qpat_x_assum ‘data_v_list (_::_)’
       (strip_assume_tac o ONCE_REWRITE_RULE [data_v_def])
  \\ gvs []
QED

Theorem data_v_list_EVERY[simp]:
  ∀vs. data_v_list vs = EVERY data_v vs
Proof
  Induct \\ simp [data_v_def]
QED

Theorem data_v_simps[simp]:
  data_v (Litv l) ∧
  (data_v (Conv t vs) ⇔ EVERY data_v vs) ∧
  (data_v (Vectorv vs) ⇔ EVERY data_v vs) ∧
  ¬data_v (Loc b n) ∧ ¬data_v (Closure env x e) ∧
  ¬data_v (Recclosure env funs f) ∧ ¬data_v (Env env id)
Proof
  simp [data_v_def]
QED

Theorem v_to_list_data_v:
  ∀v xs. v_to_list v = SOME xs ∧ EVERY data_v xs ⇒ data_v v
Proof
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def, AllCaseEqs()]
  \\ gvs []
QED

Theorem maybe_all_list_v_to_word64[local]:
  ∀xs ws. maybe_all_list (MAP v_to_word64 xs) = SOME ws ⇒ EVERY data_v xs
Proof
  Induct \\ simp [Once maybe_all_list_def]
  \\ rw [AllCaseEqs(), v_to_word64_def] \\ gvs []
  \\ first_x_assum irule \\ metis_tac []
QED

Theorem v_to_word64_list_data_v:
  v_to_word64_list v = SOME ws ⇒ data_v v
Proof
  rw [v_to_word64_list_def, AllCaseEqs()]
  \\ irule v_to_list_data_v \\ first_assum (irule_at Any)
  \\ irule maybe_all_list_v_to_word64 \\ metis_tac []
QED

Theorem do_eq_rel:
  (∀v1 w1 v2 w2.
     v_rel fr pe v1 v2 ∧ v_rel fr pe w1 w2 ∧
     (∀n1 n2 m. FLOOKUP fr n1 = SOME m ∧ FLOOKUP fr n2 = SOME m ⇒ n1 = n2) ⇒
     do_eq v1 w1 = do_eq v2 w2) ∧
  (∀vs1 ws1 vs2 ws2.
     LIST_REL (v_rel fr pe) vs1 vs2 ∧ LIST_REL (v_rel fr pe) ws1 ws2 ∧
     (∀n1 n2 m. FLOOKUP fr n1 = SOME m ∧ FLOOKUP fr n2 = SOME m ⇒ n1 = n2) ⇒
     do_eq_list vs1 ws1 = do_eq_list vs2 ws2)
Proof
  ho_match_mp_tac do_eq_ind \\ rw []
  \\ gvs [v_rel_def, do_eq_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  >- (Cases_on ‘b1 ∧ b2’ \\ gvs [] \\ eq_tac \\ rw [] \\ gvs [] \\ res_tac)
  \\ rpt (first_x_assum drule_all) \\ rw []
  \\ every_case_tac \\ gvs []
QED

Theorem do_compare_rel:
  (∀v1 w1 v2 w2.
     v_rel fr pe v1 v2 ∧ v_rel fr pe w1 w2 ∧
     (∀n1 n2 m. FLOOKUP fr n1 = SOME m ∧ FLOOKUP fr n2 = SOME m ⇒ n1 = n2) ⇒
     do_compare v1 w1 = do_compare v2 w2) ∧
  (∀vs1 ws1 vs2 ws2.
     LIST_REL (v_rel fr pe) vs1 vs2 ∧ LIST_REL (v_rel fr pe) ws1 ws2 ∧
     (∀n1 n2 m. FLOOKUP fr n1 = SOME m ∧ FLOOKUP fr n2 = SOME m ⇒ n1 = n2) ⇒
     do_compare_list vs1 ws1 = do_compare_list vs2 ws2)
Proof
  ho_match_mp_tac do_compare_ind \\ rw []
  \\ gvs [v_rel_def, do_compare_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs [NULL_LENGTH]
  >~ [‘if b1 ∧ b2 then _ else _’] >- (
    Cases_on ‘l1 = l2’ \\ gvs [] \\ metis_tac [])
  >~ [‘ctor_same_type _ _’] >- (
    ‘(vs1 = [] ⇔ ys = []) ∧ (ws1 = [] ⇔ ys' = [])’ by metis_tac [LENGTH_NIL]
    \\ simp [] \\ rw [] \\ gvs [])
  >~ [‘do_compare _ _’] >- (
    ‘do_compare v1 w1 = do_compare y y'’ by (first_x_assum irule \\ simp [])
    \\ Cases_on ‘do_compare y y'’ \\ gvs [] \\ rw [] \\ gvs [])
  \\ rw [] \\ gvs []
QED

Theorem refs_rel_store_lookup:
  refs_rel fr pe refs1 refs2 ∧ FLOOKUP fr n = SOME m ∧
  store_lookup n refs1 = SOME x ⇒
  ∃y. store_lookup m refs2 = SOME y ∧ ref_rel (v_rel fr pe) x y
Proof
  rw [refs_rel_def, store_lookup_def]
  \\ qpat_x_assum ‘∀n. n < LENGTH refs1 ⇒ _’ drule \\ rw [] \\ gvs []
QED

Theorem pmatch_rel:
  (∀envC refs1 p v1 bs1 refs2 v2 bs2.
     pmatch envC refs1 p v1 bs1 ≠ Match_type_error ∧
     refs_rel fr pe refs1 refs2 ∧ v_rel fr pe v1 v2 ∧
     LIST_REL (λ(n1,x1) (n2,x2). n2 = rename n1 ∧ v_rel fr pe x1 x2) bs1 bs2 ⇒
     case pmatch envC refs1 p v1 bs1 of
     | No_match => pmatch envC refs2 (compile_pat p) v2 bs2 = No_match
     | Match bs1' =>
         ∃bs2'. pmatch envC refs2 (compile_pat p) v2 bs2 = Match bs2' ∧
                LIST_REL (λ(n1,x1) (n2,x2). n2 = rename n1 ∧ v_rel fr pe x1 x2)
                  bs1' bs2'
     | Match_type_error => F) ∧
  (∀envC refs1 ps vs1 bs1 refs2 vs2 bs2.
     pmatch_list envC refs1 ps vs1 bs1 ≠ Match_type_error ∧
     refs_rel fr pe refs1 refs2 ∧ LIST_REL (v_rel fr pe) vs1 vs2 ∧
     LIST_REL (λ(n1,x1) (n2,x2). n2 = rename n1 ∧ v_rel fr pe x1 x2) bs1 bs2 ⇒
     case pmatch_list envC refs1 ps vs1 bs1 of
     | No_match =>
         pmatch_list envC refs2 (MAP compile_pat ps) vs2 bs2 = No_match
     | Match bs1' =>
         ∃bs2'. pmatch_list envC refs2 (MAP compile_pat ps) vs2 bs2 = Match bs2' ∧
                LIST_REL (λ(n1,x1) (n2,x2). n2 = rename n1 ∧ v_rel fr pe x1 x2)
                  bs1' bs2'
     | Match_type_error => F)
Proof
  ho_match_mp_tac pmatch_ind \\ rw []
  \\ gvs [pmatch_def, compile_pat_def, v_rel_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  >- suspend "lit"
  >- suspend "con"
  >- suspend "tup"
  >- suspend "ref"
  \\ suspend "list"
QED

Resume pmatch_rel[lit]:
  Cases_on ‘l = l'’ \\ gvs [] \\ Cases_on ‘lit_same_type l l'’ \\ gvs []
QED

Resume pmatch_rel[con]:
  Cases_on ‘nsLookup envC n’ \\ gvs []
  \\ rename1 ‘SOME p’ \\ PairCases_on ‘p’ \\ gvs []
  \\ Cases_on ‘same_type p1 stamp' ∧ LENGTH ps = p0’ \\ gvs []
  \\ Cases_on ‘same_ctor p1 stamp'’ \\ gvs []
  \\ Cases_on ‘LENGTH ys = LENGTH ps’ \\ gvs []
  \\ first_x_assum drule_all \\ simp []
QED

Resume pmatch_rel[tup]:
  Cases_on ‘LENGTH ps = LENGTH ys’ \\ gvs []
  \\ first_x_assum drule_all \\ simp []
QED

Resume pmatch_rel[ref]:
  Cases_on ‘store_lookup lnum refs1’ \\ gvs []
  \\ rename1 ‘store_lookup lnum refs1 = SOME x’
  \\ drule_all refs_rel_store_lookup \\ strip_tac
  \\ Cases_on ‘x’ \\ gvs [ref_rel_def]
  \\ rename1 ‘ref_rel _ (Refv _) y’ \\ Cases_on ‘y’ \\ gvs [ref_rel_def]
  \\ first_x_assum irule \\ simp []
QED

Resume pmatch_rel[list]:
  Cases_on ‘pmatch envC refs1 p v1 bs1’ \\ gvs []
  >~ [‘pmatch envC refs1 p v1 bs1 = Match bs’] >- (
    qpat_x_assum ‘∀refs2 v2 bs2. _ ⇒ ∃bs2'. pmatch _ _ _ _ _ = _ ∧ _’
      drule_all
    \\ strip_tac \\ simp []
    \\ first_x_assum drule_all \\ simp [])
  \\ Cases_on ‘pmatch_list envC refs1 ps vs1 bs1’ \\ gvs []
  \\ first_x_assum drule_all \\ rw [] \\ simp []
QED

Finalise pmatch_rel;

Theorem can_pmatch_all_rel:
  ∀pats.
    can_pmatch_all envC refs1 pats v1 ∧
    refs_rel fr pe refs1 refs2 ∧ v_rel fr pe v1 v2 ⇒
    can_pmatch_all envC refs2 (MAP compile_pat pats) v2
Proof
  Induct \\ rw [can_pmatch_all_def]
  \\ qspecl_then [‘envC’,‘refs1’,‘h’,‘v1’,‘[]’,‘refs2’,‘v2’,‘[]’] mp_tac
       (CONJUNCT1 pmatch_rel)
  \\ simp [] \\ Cases_on ‘pmatch envC refs1 h v1 []’ \\ gvs []
  \\ rw [] \\ simp []
QED

Theorem do_opapp_rel:
  do_opapp vs1 = SOME (env1,e) ∧ LIST_REL (v_rel fr pe) vs1 vs2 ⇒
  ∃env2. do_opapp vs2 = SOME (env2,compile_exp e) ∧ env_rel fr pe env1 env2
Proof
  rw [do_opapp_def, AllCaseEqs()] \\ gvs [v_rel_def]
  >- (irule env_rel_nsBind \\ simp [])
  \\ gvs [MAP_FST_compile_funs, find_recfun_compile_funs]
  \\ qmatch_asmsub_rename_tac ‘env_rel fr pe cl1 cl2’
  \\ ‘env_rel fr pe (cl1 with v := build_rec_env funs cl1 cl1.v)
        (cl2 with v := build_rec_env (compile_funs funs) cl2 cl2.v)’
    by (irule env_rel_build_rec_env \\ simp [])
  \\ drule_all env_rel_nsBind \\ simp []
QED

Theorem build_conv_rel:
  build_conv envc cn vs1 = SOME v1 ∧ LIST_REL (v_rel fr pe) vs1 vs2 ⇒
  ∃v2. build_conv envc cn vs2 = SOME v2 ∧ v_rel fr pe v1 v2
Proof
  rw [build_conv_def, AllCaseEqs()] \\ simp [v_rel_def]
QED

(* ------------------------------------------------------------------ *
   The store
 * ------------------------------------------------------------------ *)

(* the compiled program may change its store at locations that are in
   the range of the location map, and it may extend its store *)
Theorem state_rel_update_refs:
  state_rel H G C fr pe s t ∧ fr ⊑ fr1 ∧ refs_rel fr1 pe refs1 refs2 ∧
  LENGTH t.refs ≤ LENGTH refs2 ∧
  (∀p. p < LENGTH t.refs ∧ p ∉ FRANGE fr ⇒
       EL p refs2 = EL p t.refs ∧ p ∉ FRANGE fr1) ⇒
  state_rel H G C fr1 pe (s with refs := refs1) (t with refs := refs2)
Proof
  simp [state_rel_def] \\ strip_tac
  \\ gvs [prelude_ok_def, DISJ_IMP_THM, FORALL_AND_THM]
  \\ res_tac \\ Cases_on ‘s.eval_state’ \\ gvs [prelude_vals_def]
  \\ rename1 ‘SOME es’ \\ Cases_on ‘es’ \\ gvs [eval_rel_def]
  \\ metis_tac [v_rel_SUBMAP]
QED

Theorem state_rel_store_lookup:
  state_rel H G C fr pe s t ∧ FLOOKUP fr n = SOME m ∧
  store_lookup n s.refs = SOME x ⇒
  ∃y. store_lookup m t.refs = SOME y ∧ ref_rel (v_rel fr pe) x y
Proof
  rw [state_rel_def] \\ drule_all refs_rel_store_lookup \\ simp []
QED

Theorem state_rel_lookup_Refv:
  state_rel H G C fr pe s t ∧ FLOOKUP fr n = SOME m ∧
  store_lookup n s.refs = SOME (Refv v) ⇒
  ∃w. store_lookup m t.refs = SOME (Refv w) ∧ v_rel fr pe v w
Proof
  rw [] \\ drule_all state_rel_store_lookup \\ rw []
  \\ Cases_on ‘y’ \\ gvs [ref_rel_def]
QED

Theorem state_rel_lookup_W8array:
  state_rel H G C fr pe s t ∧ FLOOKUP fr n = SOME m ∧
  store_lookup n s.refs = SOME (W8array ws) ⇒
  store_lookup m t.refs = SOME (W8array ws)
Proof
  rw [] \\ drule_all state_rel_store_lookup \\ rw []
  \\ Cases_on ‘y’ \\ gvs [ref_rel_def]
QED

Theorem state_rel_lookup_Varray:
  state_rel H G C fr pe s t ∧ FLOOKUP fr n = SOME m ∧
  store_lookup n s.refs = SOME (Varray vs) ⇒
  ∃ws. store_lookup m t.refs = SOME (Varray ws) ∧ LIST_REL (v_rel fr pe) vs ws
Proof
  rw [] \\ drule_all state_rel_store_lookup \\ rw []
  \\ Cases_on ‘y’ \\ gvs [ref_rel_def]
QED

Theorem state_rel_store_assign:
  state_rel H G C fr pe s t ∧ FLOOKUP fr n = SOME m ∧
  store_assign n x s.refs = SOME refs1 ∧ ref_rel (v_rel fr pe) x y ⇒
  ∃refs2. store_assign m y t.refs = SOME refs2 ∧
          state_rel H G C fr pe (s with refs := refs1) (t with refs := refs2)
Proof
  simp [store_assign_def] \\ strip_tac
  \\ ‘refs_rel fr pe s.refs t.refs’ by gvs [state_rel_def]
  \\ ‘m < LENGTH t.refs ∧ ref_rel (v_rel fr pe) (EL n s.refs) (EL m t.refs)’
    by (gvs [refs_rel_def]
        \\ qpat_x_assum ‘∀n. n < LENGTH s.refs ⇒ _’ drule \\ rw [] \\ gvs [])
  \\ ‘store_v_same_type (EL m t.refs) y’
    by (Cases_on ‘EL n s.refs’ \\ Cases_on ‘EL m t.refs’ \\ Cases_on ‘x’
        \\ Cases_on ‘y’ \\ gvs [ref_rel_def, store_v_same_type_def])
  \\ gvs [] \\ irule state_rel_update_refs \\ simp []
  \\ first_assum (irule_at Any) \\ simp [EL_LUPDATE]
  \\ conj_tac
  >- (
    gvs [refs_rel_def, EL_LUPDATE] \\ rpt strip_tac
    \\ qpat_x_assum ‘∀n. n < LENGTH s.refs ⇒ _’ drule \\ strip_tac
    \\ simp [] \\ Cases_on ‘n' = n’ \\ gvs [] \\ rw [] \\ metis_tac [])
  \\ rw [] \\ gvs [FRANGE_FLOOKUP] \\ metis_tac []
QED

Theorem state_rel_assign_W8array:
  state_rel H G C fr pe s t ∧ FLOOKUP fr n = SOME m ∧
  store_assign n (W8array ws) s.refs = SOME refs1 ⇒
  ∃refs2. store_assign m (W8array ws) t.refs = SOME refs2 ∧
          state_rel H G C fr pe (s with refs := refs1) (t with refs := refs2)
Proof
  strip_tac \\ irule state_rel_store_assign \\ simp []
  \\ qexistsl_tac [‘n’, ‘W8array ws’] \\ simp [ref_rel_def]
QED

Theorem ref_rel_SUBMAP:
  ref_rel (v_rel fr pe) x y ∧ fr ⊑ fr1 ⇒ ref_rel (v_rel fr1 pe) x y
Proof
  rw [] \\ irule ref_rel_mono \\ first_assum (irule_at Any)
  \\ metis_tac [v_rel_SUBMAP]
QED

Theorem state_rel_store_alloc:
  state_rel H G C fr pe s t ∧ ref_rel (v_rel fr pe) x y ⇒
  ∃fr1. fr ⊑ fr1 ∧
        state_rel H G C fr1 pe (s with refs := s.refs ++ [x])
                               (t with refs := t.refs ++ [y]) ∧
        FLOOKUP fr1 (LENGTH s.refs) = SOME (LENGTH t.refs)
Proof
  rw []
  \\ ‘refs_rel fr pe s.refs t.refs’ by gvs [state_rel_def]
  \\ qexists_tac ‘fr |+ (LENGTH s.refs, LENGTH t.refs)’
  \\ ‘LENGTH s.refs ∉ FDOM fr’ by gvs [refs_rel_def]
  \\ ‘∀k m. FLOOKUP fr k = SOME m ⇒ k < LENGTH s.refs ∧ m < LENGTH t.refs’
    by (gvs [refs_rel_def] \\ rpt gen_tac \\ strip_tac
        \\ ‘k < LENGTH s.refs’ by gvs [FLOOKUP_DEF] \\ res_tac \\ gvs [])
  \\ ‘fr ⊑ fr |+ (LENGTH s.refs, LENGTH t.refs)’ by simp [SUBMAP_FUPDATE_EQN]
  \\ simp [FLOOKUP_UPDATE]
  \\ irule state_rel_update_refs \\ simp []
  \\ first_assum (irule_at Any) \\ simp [EL_APPEND1, DOMSUB_NOT_IN_DOM]
  \\ gvs [refs_rel_def, FLOOKUP_UPDATE] \\ rpt conj_tac
  >- simp [EXTENSION]
  >- (
    rpt strip_tac \\ Cases_on ‘n = LENGTH s.refs’
    \\ gvs [EL_LENGTH_APPEND, EL_APPEND1]
    >- (irule ref_rel_SUBMAP \\ first_assum (irule_at Any) \\ simp [])
    \\ ‘n < LENGTH s.refs’ by decide_tac
    \\ first_x_assum drule \\ strip_tac \\ simp [EL_APPEND1]
    \\ irule ref_rel_SUBMAP \\ first_assum (irule_at Any) \\ simp [])
  \\ rw [] \\ gvs [] \\ res_tac \\ gvs [] \\ CCONTR_TAC \\ gvs []
  \\ res_tac \\ gvs []
QED

(* ------------------------------------------------------------------ *
   Values given to and returned by primitive operations
 * ------------------------------------------------------------------ *)

Theorem v_rel_data_v_refl:
  data_v v ⇒ v_rel fr pe v v
Proof
  metis_tac [data_v_v_rel]
QED

Theorem v_rel_data_v:
  data_v v ⇒ (v_rel fr pe v w ⇔ w = v)
Proof
  metis_tac [data_v_v_rel]
QED

Theorem data_v_exn_values[simp]:
  data_v sub_exn_v ∧ data_v div_exn_v ∧ data_v chr_exn_v ∧ data_v bind_exn_v
Proof
  EVAL_TAC
QED

Theorem v_rel_list_to_v:
  ∀xs ys. LIST_REL (v_rel fr pe) xs ys ⇒
          v_rel fr pe (list_to_v xs) (list_to_v ys)
Proof
  Induct \\ simp [list_to_v_def, v_rel_def, PULL_EXISTS]
QED

Theorem v_rel_v_to_list:
  ∀v xs w. v_to_list v = SOME xs ∧ v_rel fr pe v w ⇒
           ∃ys. v_to_list w = SOME ys ∧ LIST_REL (v_rel fr pe) xs ys
Proof
  ho_match_mp_tac v_to_list_ind
  \\ rw [v_to_list_def, AllCaseEqs()] \\ gvs [v_rel_def, v_to_list_def]
  \\ res_tac \\ simp []
QED

Theorem v_rel_v_to_char_list:
  ∀v cs w. v_to_char_list v = SOME cs ∧ v_rel fr pe v w ⇒
           v_to_char_list w = SOME cs
Proof
  ho_match_mp_tac v_to_char_list_ind
  \\ rw [v_to_char_list_def, AllCaseEqs()]
  \\ gvs [v_rel_def, v_to_char_list_def] \\ res_tac \\ simp []
QED

Theorem v_rel_vs_to_string:
  ∀vs str ws. vs_to_string vs = SOME str ∧ LIST_REL (v_rel fr pe) vs ws ⇒
              vs_to_string ws = SOME str
Proof
  ho_match_mp_tac vs_to_string_ind
  \\ rw [vs_to_string_def, AllCaseEqs()]
  \\ gvs [v_rel_def, vs_to_string_def] \\ res_tac \\ simp []
QED

Theorem v_rel_check_type:
  v_rel fr pe v w ⇒ (check_type ty w ⇔ check_type ty v) ∧
                    (check_type ty v ⇒ w = v)
Proof
  Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ rw [check_type_def] \\ gvs [v_rel_def, Boolv_def]
  \\ Cases_on ‘v’ \\ gvs [v_rel_def]
  \\ rename1 ‘LIST_REL _ xs ys’ \\ Cases_on ‘xs’ \\ gvs []
QED

Theorem LIST_REL_check_type:
  LIST_REL (v_rel fr pe) vs ws ∧ EVERY (check_type ty) vs ⇒ ws = vs
Proof
  rw [LIST_REL_EL_EQN, EVERY_EL, LIST_EQ_REWRITE]
  \\ metis_tac [v_rel_check_type]
QED

Theorem v_rel_dest_Litv:
  v_rel fr pe v w ⇒ dest_Litv w = dest_Litv v
Proof
  Cases_on ‘v’ \\ rw [v_rel_def] \\ simp []
QED

Theorem do_test_rel:
  v_rel fr pe v1 w1 ∧ v_rel fr pe v2 w2 ∧
  do_test test ty v1 v2 = Eq_val b ⇒
  do_test test ty w1 w2 = Eq_val b
Proof
  strip_tac \\ imp_res_tac v_rel_check_type \\ imp_res_tac v_rel_dest_Litv
  \\ Cases_on ‘test’ \\ gvs [do_test_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

Theorem data_v_Boolv[simp]:
  data_v (Boolv b)
Proof
  Cases_on ‘b’ \\ simp [Boolv_def]
QED

Theorem data_v_list_to_v[simp]:
  ∀xs. data_v (list_to_v xs) ⇔ EVERY data_v xs
Proof
  Induct \\ simp [list_to_v_def]
QED

Theorem do_arith_data_v:
  do_arith a ty vs = SOME r ⇒ data_v (case r of INL x => x | INR x => x)
Proof
  Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ rw [do_arith_def, AllCaseEqs()]
  \\ simp [div_exn_v_def]
QED

Theorem do_conversion_data_v:
  do_conversion v ty1 ty2 = SOME r ⇒
  data_v (case r of INL x => x | INR x => x)
Proof
  Cases_on ‘ty1’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ Cases_on ‘ty2’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ rw [do_conversion_def, AllCaseEqs()]
  \\ simp [chr_exn_v_def]
QED

Theorem state_rel_index_witness_length:
  state_rel H G C fr pe s t ∧ v_rel fr pe v w ⇒
  index_witness_length t.refs w = index_witness_length s.refs v
Proof
  Cases_on ‘v’ \\ rw [v_rel_def] \\ simp [index_witness_length_def]
  >~ [‘Litv l’] >- (Cases_on ‘l’ \\ simp [index_witness_length_def])
  >~ [‘LENGTH _ = LENGTH _’] >- (imp_res_tac LIST_REL_LENGTH \\ simp [])
  \\ ‘∃x. store_lookup n s.refs = SOME x’
    by gvs [state_rel_def, refs_rel_def, store_lookup_def, FLOOKUP_DEF]
  \\ drule_all state_rel_store_lookup \\ strip_tac \\ simp []
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [ref_rel_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ simp []
QED

Theorem state_rel_unsafe_index_bound:
  state_rel H G C fr pe s t ∧ LIST_REL (v_rel fr pe) vs ws ⇒
  unsafe_index_bound t.refs ws = unsafe_index_bound s.refs vs
Proof
  Cases_on ‘vs’ \\ rw [] \\ simp [unsafe_index_bound_def]
  \\ rename1 ‘LIST_REL _ rest _’ \\ Cases_on ‘rest’ \\ gvs []
  \\ simp [unsafe_index_bound_def]
  \\ drule_all state_rel_index_witness_length \\ simp []
QED

Theorem copy_array_rel_imp:
  (copy_array (xs,off) len NONE = SOME zs ∧ LIST_REL R xs ys ⇒
   ∃zs'. copy_array (ys,off) len NONE = SOME zs' ∧ LIST_REL R zs zs') ∧
  (copy_array (xs,off) len NONE = NONE ∧ LIST_REL R xs ys ⇒
   copy_array (ys,off) len NONE = NONE) ∧
  (copy_array (xs,off) len (SOME (ds,doff)) = SOME zs ∧
   LIST_REL R xs ys ∧ LIST_REL R ds es ⇒
   ∃zs'. copy_array (ys,off) len (SOME (es,doff)) = SOME zs' ∧
         LIST_REL R zs zs') ∧
  (copy_array (xs,off) len (SOME (ds,doff)) = NONE ∧
   LIST_REL R xs ys ∧ LIST_REL R ds es ⇒
   copy_array (ys,off) len (SOME (es,doff)) = NONE)
Proof
  rpt conj_tac \\ rpt strip_tac \\ imp_res_tac LIST_REL_LENGTH
  \\ gvs [copy_array_def, AllCaseEqs()]
  \\ rpt (irule_at Any EVERY2_APPEND_suff)
  \\ rpt (irule_at Any EVERY2_TAKE) \\ rpt (irule_at Any EVERY2_DROP)
  \\ simp []
QED

Theorem state_rel_do_eq:
  state_rel H G C fr pe s t ∧ v_rel fr pe v1 w1 ∧ v_rel fr pe v2 w2 ⇒
  do_eq w1 w2 = do_eq v1 v2
Proof
  rw [state_rel_def, refs_rel_def]
  \\ irule (GSYM (CONJUNCT1 do_eq_rel)) \\ metis_tac []
QED

Theorem state_rel_do_compare:
  state_rel H G C fr pe s t ∧ v_rel fr pe v1 w1 ∧ v_rel fr pe v2 w2 ⇒
  do_compare w1 w2 = do_compare v1 v2
Proof
  rw [state_rel_def, refs_rel_def]
  \\ irule (GSYM (CONJUNCT1 do_compare_rel)) \\ metis_tac []
QED

Theorem dest_thunk_rel:
  state_rel H G C fr pe s t ∧ LIST_REL (v_rel fr pe) vs ws ⇒
  case dest_thunk vs s.refs of
  | BadRef => dest_thunk ws t.refs = BadRef
  | NotThunk => dest_thunk ws t.refs = NotThunk
  | IsThunk m v => ∃w. dest_thunk ws t.refs = IsThunk m w ∧ v_rel fr pe v w
Proof
  strip_tac
  \\ Cases_on ‘∃b n. vs = [Loc b n]’
  >- (
    gvs [v_rel_def, dest_thunk_def]
    \\ Cases_on ‘store_lookup n s.refs’ \\ gvs []
    >- gvs [state_rel_def, refs_rel_def, store_lookup_def, FLOOKUP_DEF]
    \\ drule_all state_rel_store_lookup \\ strip_tac \\ simp []
    \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [ref_rel_def]
    \\ rename1 ‘Thunk m’ \\ Cases_on ‘m’ \\ rw [])
  \\ ‘dest_thunk vs s.refs = NotThunk ∧ dest_thunk ws t.refs = NotThunk’
    by (Cases_on ‘vs’ \\ gvs [dest_thunk_def]
        \\ rename1 ‘v_rel _ _ h _’ \\ Cases_on ‘h’ \\ gvs [v_rel_def]
        \\ rename1 ‘LIST_REL _ rest _’ \\ Cases_on ‘rest’
        \\ gvs [dest_thunk_def])
  \\ simp []
QED

Theorem state_rel_bad_thunk_update:
  state_rel H G C fr pe s t ∧ v_rel fr pe v w ∧
  ¬bad_thunk_update m v s.refs ⇒
  ¬bad_thunk_update m w t.refs
Proof
  strip_tac \\ ‘LIST_REL (v_rel fr pe) [v] [w]’ by simp []
  \\ drule_all dest_thunk_rel \\ gvs [bad_thunk_update_def]
  \\ Cases_on ‘dest_thunk [v] s.refs’ \\ rw []
QED

Theorem state_rel_update_thunk:
  state_rel H G C fr pe s t ∧ LIST_REL (v_rel fr pe) vs ws ∧
  LIST_REL (v_rel fr pe) xs ys ∧ update_thunk vs s.refs xs = SOME refs1 ⇒
  ∃refs2. update_thunk ws t.refs ys = SOME refs2 ∧
          state_rel H G C fr pe (s with refs := refs1) (t with refs := refs2)
Proof
  strip_tac
  \\ gvs [oneline update_thunk_def, AllCaseEqs(), v_rel_def]
  \\ rename1 ‘dest_thunk [x] s.refs = NotThunk’
  \\ rename1 ‘v_rel fr pe x y’
  \\ ‘LIST_REL (v_rel fr pe) [x] [y]’ by simp []
  \\ drule_all dest_thunk_rel \\ simp [] \\ strip_tac
  \\ irule state_rel_store_assign
  \\ qpat_assum ‘store_assign _ _ s.refs = SOME _’ (irule_at Any)
  \\ simp [ref_rel_def]
QED

(* ------------------------------------------------------------------ *
   Primitive operations
 * ------------------------------------------------------------------ *)

Theorem state_rel_ffi:
  state_rel H G C fr pe s t ⇒ t.ffi = s.ffi
Proof
  simp [state_rel_def]
QED

Theorem state_rel_update_ffi:
  state_rel H G C fr pe ((s:'ffi evalSem$state) with refs := r1)
                        (t with refs := r2) ⇒
  state_rel H G C fr pe (s with <| refs := r1; ffi := (f:'ffi ffi_state) |>)
                        (t with <| refs := r2; ffi := f |>)
Proof
  simp [state_rel_def] \\ strip_tac
  \\ Cases_on ‘s.eval_state’ \\ gvs [prelude_vals_def]
  \\ rename1 ‘SOME es’ \\ Cases_on ‘es’ \\ gvs [eval_rel_def]
  \\ metis_tac []
QED

Theorem state_with_ffi[local,simp]:
  (t:'ffi evalSem$state).ffi = f ⇒
  t with <| refs := r; ffi := f |> = t with refs := r ∧
  t with ffi := f = t ∧
  t with refs := t.refs = t
Proof
  simp [evalSemTheory.state_component_equality]
QED

(* each of the theorems below proves this for some of the primitive
   operations; do_app_rel puts them together *)
val op_goal =
  “do_app (s.refs,s.ffi) op vs = SOME ((refs1,ffi1),r) ∧
   state_rel H G C fr pe (s:'ffi evalSem$state) (t:'ffi evalSem$state) ∧
   LIST_REL (v_rel fr pe) vs ws ⇒
   ∃fr1 refs2 r2.
     do_app (t.refs,t.ffi) op ws = SOME ((refs2,ffi1),r2) ∧
     fr ⊑ fr1 ∧
     state_rel H G C fr1 pe (s with <| refs := refs1; ffi := ffi1 |>)
                            (t with <| refs := refs2; ffi := ffi1 |>) ∧
     res_rel (v_rel fr1 pe) (v_rel fr1 pe) r r2”

Theorem op_refs:
  op = Opref ∨ op = Opassign ∨ op = Opderef ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_lookup_Refv
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def, store_alloc_def]
  >>~- ([‘store_assign’],
        irule_at Any SUBMAP_REFL \\ irule state_rel_store_assign
        \\ qpat_assum ‘store_assign _ _ s.refs = SOME _’ (irule_at Any)
        \\ gvs [ref_rel_def])
  >>~- ([‘FLOOKUP _ (LENGTH _)’],
        irule state_rel_store_alloc \\ gvs [ref_rel_def])
  \\ irule_at Any SUBMAP_REFL \\ gvs []
QED

Theorem op_byte_arrays:
  op = Aw8alloc ∨ op = Aw8sub ∨ op = Aw8sub_unsafe ∨ op = Aw8length ∨
  op = Aw8update ∨ op = Aw8update_unsafe ∨ op = Aw8subBit ∨
  op = Aw8subBit_unsafe ∨ op = Aw8updateBit ∨ op = Aw8updateBit_unsafe ∨
  op = Aw8ScanEq ∨ op = Aw8ScanNeq ∨ op = XorAw8Str_unsafe ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_lookup_W8array
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def, store_alloc_def]
  >>~- ([‘store_assign’],
        irule_at Any SUBMAP_REFL \\ irule state_rel_store_assign
        \\ qpat_assum ‘store_assign _ _ s.refs = SOME _’ (irule_at Any)
        \\ gvs [ref_rel_def])
  >>~- ([‘FLOOKUP _ (LENGTH _)’],
        irule state_rel_store_alloc \\ gvs [ref_rel_def])
  \\ irule_at Any SUBMAP_REFL \\ gvs []
QED

Theorem op_copy:
  op = CopyStrStr ∨ op = CopyStrAw8 ∨ op = CopyAw8Str ∨ op = CopyAw8Aw8 ∨
  op = CopyVecVec ∨ op = CopyVecArr ∨ op = CopyArrVec ∨ op = CopyArrArr ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_lookup_W8array
  \\ imp_res_tac state_rel_lookup_Varray
  \\ imp_res_tac copy_array_rel_imp
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def, store_alloc_def]
  >>~- ([‘store_assign’],
        irule_at Any SUBMAP_REFL \\ irule state_rel_store_assign
        \\ qpat_assum ‘store_assign _ _ s.refs = SOME _’ (irule_at Any)
        \\ gvs [ref_rel_def])
  \\ irule_at Any SUBMAP_REFL \\ gvs []
QED

Theorem op_str:
  op = Implode ∨ op = Explode ∨ op = Strsub ∨ op = Strsub_unsafe ∨
  op = Strlen ∨ op = Strcat ∨ op = StrScanEq ∨ op = StrScanNeq ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac v_rel_v_to_char_list
  \\ imp_res_tac v_rel_v_to_list
  \\ imp_res_tac v_rel_vs_to_string
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def]
  \\ irule_at Any SUBMAP_REFL \\ gvs [v_rel_data_v_refl, EVERY_MAP]
QED

Theorem op_lists:
  op = ListAppend ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac v_rel_v_to_list
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def]
  \\ irule_at Any SUBMAP_REFL \\ gvs []
  \\ irule v_rel_list_to_v \\ irule LIST_REL_APPEND_suff \\ simp []
QED

Theorem op_vectors:
  op = VfromList ∨ op = Vsub ∨ op = Vsub_unsafe ∨ op = Vlength ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac v_rel_v_to_list
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def]
  \\ irule_at Any SUBMAP_REFL \\ gvs [LIST_REL_EL_EQN]
QED

Theorem op_arrays:
  op = Aalloc ∨ op = AallocEmpty ∨ op = AallocFixed ∨ op = Asub ∨
  op = Asub_unsafe ∨ op = Alength ∨ op = Aupdate ∨ op = Aupdate_unsafe ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_lookup_Varray
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def, store_alloc_def]
  >>~- ([‘store_assign’],
        irule_at Any SUBMAP_REFL \\ irule state_rel_store_assign
        \\ qpat_assum ‘store_assign _ _ s.refs = SOME _’ (irule_at Any)
        \\ gvs [ref_rel_def]
        \\ irule EVERY2_LUPDATE_same \\ simp [])
  >>~- ([‘FLOOKUP _ (LENGTH _)’],
        irule state_rel_store_alloc \\ gvs [ref_rel_def]
        \\ simp [LIST_REL_REPLICATE_same])
  \\ irule_at Any SUBMAP_REFL \\ gvs [LIST_REL_EL_EQN]
QED

Theorem op_eq:
  op = Equality ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_do_eq
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def]
  \\ irule_at Any SUBMAP_REFL \\ gvs []
QED

Theorem op_poly_compare:
  op = PolyCompare ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), v_rel_def, PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_do_compare
  \\ gvs []
  \\ irule_at Any SUBMAP_REFL \\ gvs []
QED

Theorem op_arith:
  (∃a ty. op = Arith a ty) ∨ (∃ty1 ty2. op = FromTo ty1 ty2) ∨
  (∃test ty. op = Test test ty) ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac LIST_REL_check_type
  \\ imp_res_tac v_rel_check_type
  \\ imp_res_tac do_test_rel
  \\ imp_res_tac do_arith_data_v
  \\ imp_res_tac do_conversion_data_v
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def]
  \\ irule_at Any SUBMAP_REFL \\ gvs [v_rel_data_v_refl]
QED

Theorem op_unsafe_index:
  (∃a. op = UnsafeIndexArith a) ∨ (∃test. op = UnsafeIndexTest test) ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), do_unsafe_index_arith_def,
          do_unsafe_index_test_def, v_rel_def, PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_unsafe_index_bound
  \\ imp_res_tac do_arith_data_v
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def, do_unsafe_index_arith_def, do_unsafe_index_test_def]
  \\ irule_at Any SUBMAP_REFL \\ gvs [v_rel_data_v_refl]
QED

Theorem op_ffi:
  op = ConfigGC ∨ (∃n. op = FFI n) ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_lookup_W8array
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def]
  \\ irule_at Any SUBMAP_REFL \\ gvs []
  \\ drule_all state_rel_assign_W8array \\ strip_tac
  \\ qexists_tac ‘refs2’ \\ simp [state_rel_update_ffi]
QED

Theorem op_env_id:
  op = Env_id ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, AllCaseEqs(), store_alloc_def, v_rel_def, v_rel_data_v,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ gvs [do_app_def]
  \\ irule_at Any SUBMAP_REFL \\ gvs [v_rel_data_v_refl, nat_to_v_def]
QED

Theorem op_thunk:
  (∃th_op. op = ThunkOp th_op) ⇒
  ^op_goal
Proof
  rpt strip_tac
  \\ gvs [do_app_def, thunk_op_def, AllCaseEqs(), store_alloc_def, v_rel_def,
          PULL_EXISTS]
  \\ imp_res_tac state_rel_ffi
  \\ imp_res_tac state_rel_bad_thunk_update
  \\ rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
  \\ gvs [do_app_def, thunk_op_def, store_alloc_def]
  >>~- ([‘store_assign’],
        irule_at Any SUBMAP_REFL \\ irule state_rel_store_assign
        \\ qpat_assum ‘store_assign _ _ s.refs = SOME _’ (irule_at Any)
        \\ gvs [ref_rel_def])
  \\ irule state_rel_store_alloc \\ gvs [ref_rel_def]
QED

Theorem do_app_rel:
  ^op_goal
Proof
  EVERY (map assume_tac
    [op_refs, op_byte_arrays, op_copy, op_str, op_lists, op_vectors,
     op_arrays, op_eq, op_poly_compare, op_arith, op_unsafe_index, op_ffi,
     op_env_id, op_thunk])
  \\ Cases_on ‘op’ \\ fs [] \\ simp [do_app_def]
QED

Theorem with_clock_same[local,simp]:
  (t:'ffi evalSem$state) with clock := t.clock = t ∧
  t with <| clock := t.clock; next_type_stamp := n |> =
    t with next_type_stamp := n ∧
  t with <| clock := t.clock; next_exn_stamp := n |> =
    t with next_exn_stamp := n ∧
  t with <| clock := t.clock; eval_state := es |> = t with eval_state := es
Proof
  simp [evalSemTheory.state_component_equality]
QED

Theorem lift_clock[local]:
  (∀(s:'ffi evalSem$state) env es s1 r extra.
     evaluate s env es = (s1,r) ∧ r ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate (s with clock := s.clock + extra) env es =
       (s1 with clock := s1.clock + extra,r)) ∧
  (∀(s:'ffi evalSem$state) env v pes err_v s2 r2 extra.
     evaluate_match s env v pes err_v = (s2,r2) ∧
     r2 ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate_match (s with clock := s.clock + extra) env v pes err_v =
       (s2 with clock := s2.clock + extra,r2)) ∧
  (∀(s:'ffi evalSem$state) env ds s3 r3 extra.
     evaluate_decs s env ds = (s3,r3) ∧ r3 ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate_decs (s with clock := s.clock + extra) env ds =
       (s3 with clock := s3.clock + extra,r3))
Proof
  metis_tac [evaluate_add_to_clock_all]
QED

Theorem lift_exp[local]:
  ∀s env es s1 r. evaluate (s:'ffi evalSem$state) env es = (s1,r) ⇒
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∀extra. evaluate (s with clock := s.clock + extra) env es =
              (s1 with clock := s1.clock + extra,r)
Proof
  metis_tac [lift_clock]
QED

Theorem lift_match[local]:
  ∀s env v pes err_v s1 r.
    evaluate_match (s:'ffi evalSem$state) env v pes err_v = (s1,r) ⇒
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∀extra. evaluate_match (s with clock := s.clock + extra) env v pes err_v =
              (s1 with clock := s1.clock + extra,r)
Proof
  metis_tac [lift_clock]
QED

Theorem lift_decs[local]:
  ∀s env ds s1 r. evaluate_decs (s:'ffi evalSem$state) env ds = (s1,r) ⇒
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∀extra. evaluate_decs (s with clock := s.clock + extra) env ds =
              (s1 with clock := s1.clock + extra,r)
Proof
  metis_tac [lift_clock]
QED

Theorem state_rel_clock:
  state_rel H G C fr pe s t ⇒
  state_rel H G C fr pe (s with clock := k) (t with clock := k)
Proof
  rw [state_rel_def] \\ gvs []
  \\ Cases_on ‘s.eval_state’ \\ gvs [prelude_vals_def]
  \\ rename1 ‘SOME es’ \\ Cases_on ‘es’ \\ gvs [eval_rel_def]
  \\ metis_tac []
QED

Theorem state_rel_stamps:
  state_rel H G C fr pe s t ⇒
  state_rel H G C fr pe (s with next_type_stamp := n)
                        (t with next_type_stamp := n) ∧
  state_rel H G C fr pe (s with next_exn_stamp := n)
                        (t with next_exn_stamp := n) ∧
  state_rel H G C fr pe (s with ptr_eq_oracle := po)
                        (t with ptr_eq_oracle := po)
Proof
  rw [state_rel_def] \\ gvs []
  \\ Cases_on ‘s.eval_state’ \\ gvs [prelude_vals_def]
  \\ rename1 ‘SOME es’ \\ Cases_on ‘es’ \\ gvs [eval_rel_def]
  \\ metis_tac []
QED

Theorem state_rel_eval_state:
  state_rel H G C fr pe s t ⇒
  s.eval_state = NONE ∨
  ∃r. s.eval_state = SOME (EvalPending r) ∨ s.eval_state = SOME (EvalRun r)
Proof
  rw [state_rel_def] \\ Cases_on ‘s.eval_state’ \\ gvs []
  \\ rename1 ‘SOME ev’ \\ Cases_on ‘ev’ \\ gvs [eval_rel_def]
QED

(* the input program calls Eval with one or two arguments *)
Theorem state_rel_eval_arity:
  state_rel H G C fr pe (s:'ffi evalSem$state) t ⇒
  (LENGTH xs ≠ 1 ⇒ do_eval_init xs s.eval_state (:'ffi) = NONE) ∧
  (LENGTH xs ≠ 2 ⇒ do_eval_fail xs s.eval_state = NONE) ∧
  (LENGTH xs ≠ 2 ⇒ do_eval_res xs s = (s,Rerr (Rabort Rtype_error)))
Proof
  strip_tac \\ drule state_rel_eval_state \\ strip_tac
  \\ gvs [do_eval_init_def, do_eval_res_def, do_eval_def, do_eval_run_def,
          do_eval_fail_def]
  \\ every_case_tac \\ gvs []
QED

Theorem refs_rel_LUPDATE:
  refs_rel fr pe refs1 refs2 ∧ p ∉ FRANGE fr ⇒
  refs_rel fr pe refs1 (LUPDATE x p refs2)
Proof
  rw [refs_rel_def, EL_LUPDATE] \\ res_tac \\ simp []
  \\ rw [] \\ gvs [FRANGE_FLOOKUP]
QED

(* the compiled program runs the body of $init *)
Theorem evaluate_init_body:
  state_rel H G C fr pe (s:'ffi evalSem$state) t ∧
  do_eval_init [v] s.eval_state (:'ffi) = SOME es ∧ v_rel fr pe v w ⇒
  ∃refs.
    evaluate t (pe with v := nsBind «x» w pe.v) [init_body] =
      (t with refs := refs,Rval [Conv NONE []]) ∧
    state_rel H G C fr pe (s with eval_state := SOME es) (t with refs := refs)
Proof
  rw [do_eval_init_def, AllCaseEqs()] \\ gvs [v_rel_def]
  \\ gvs [state_rel_def, eval_rel_def]
  \\ gvs [prelude_ok_def, DISJ_IMP_THM, FORALL_AND_THM]
  \\ simp [init_body_def, full_evaluate_def, can_pmatch_all_def, pmatch_def,
           do_app_def, store_assign_def, nsOptBind_def, nsLookup_nsBind,
           store_v_same_type_def, EL_LUPDATE, pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘t with refs := new_refs’
  \\ qexists_tac ‘new_refs’ \\ simp [Abbr ‘new_refs’, EL_LUPDATE]
  \\ conj_tac >- (rpt (irule refs_rel_LUPDATE \\ simp []))
  \\ gvs [adjust_decs_def, decs_factor_def,
          evalSemTheory.eval_decs_state_component_equality]
QED

Theorem state_rel_declare_env:
  state_rel H G C fr pe s t ∧ env_rel fr pe env env2 ∧
  declare_env s.eval_state env = SOME (x,es1) ⇒
  ∃x2 es2. declare_env t.eval_state env2 = SOME (x2,es2) ∧
           v_rel fr pe x x2 ∧
           state_rel H G C fr pe (s with eval_state := es1)
                                 (t with eval_state := es2)
Proof
  rw [state_rel_def]
  \\ Cases_on ‘s.eval_state’ \\ gvs [declare_env_def]
  \\ rename1 ‘SOME es’ \\ Cases_on ‘es’ \\ gvs [eval_rel_def, declare_env_def]
  \\ rename1 ‘decs_factor _ _ r’
  \\ Cases_on ‘r.env_id_counter’ \\ rename1 ‘_ = (g,rest)’
  \\ PairCases_on ‘rest’
  \\ gvs [adjust_decs_def, v_rel_def, eval_rel_def, decs_factor_def]
  \\ metis_tac []
QED

Theorem env_rel_lookup:
  env_rel fr pe env env2 ∧ nsLookup env.v id = SOME v ⇒
  ∃v2. nsLookup env2.v (rename_id id) = SOME v2 ∧ v_rel fr pe v v2
Proof
  rw [env_rel_def, ns_rel_def]
  \\ qpat_x_assum ‘∀id. OPTREL _ _ _’ (qspec_then ‘id’ mp_tac)
  \\ simp [OPTREL_def]
QED

Theorem do_if_rel:
  v_rel fr pe v w ∧ do_if v e1 e2 = SOME e ⇒
  do_if w (compile_exp e1) (compile_exp e2) = SOME (compile_exp e)
Proof
  strip_tac \\ imp_res_tac v_rel_Boolv \\ gvs [do_if_def, AllCaseEqs()]
QED

Theorem do_log_rel_Exp:
  v_rel fr pe v w ∧ do_log l v e = SOME (Exp e1) ⇒
  do_log l w (compile_exp e) = SOME (Exp (compile_exp e1))
Proof
  strip_tac \\ imp_res_tac v_rel_Boolv \\ gvs [do_log_def, AllCaseEqs()]
QED

Theorem do_log_rel_Val:
  v_rel fr pe v w ∧ do_log l v e = SOME (Val v1) ⇒
  do_log l w (compile_exp e) = SOME (Val w) ∧ v1 = v
Proof
  strip_tac \\ imp_res_tac v_rel_Boolv \\ gvs [do_log_def, AllCaseEqs()]
QED

(* a program in EvalRun mode stays in EvalRun mode *)
Theorem evaluate_EvalRun:
  (∀(s:'ffi evalSem$state) env es s1 r.
     evaluate s env es = (s1,r) ⇒
     ∀x. s.eval_state = SOME (EvalRun x) ⇒ ∃y. s1.eval_state = SOME (EvalRun y)) ∧
  (∀(s:'ffi evalSem$state) env v pes err_v s1 r.
     evaluate_match s env v pes err_v = (s1,r) ⇒
     ∀x. s.eval_state = SOME (EvalRun x) ⇒ ∃y. s1.eval_state = SOME (EvalRun y)) ∧
  (∀(s:'ffi evalSem$state) env ds s1 r.
     evaluate_decs s env ds = (s1,r) ⇒
     ∀x. s.eval_state = SOME (EvalRun x) ⇒ ∃y. s1.eval_state = SOME (EvalRun y))
Proof
  ho_match_mp_tac full_evaluate_ind \\ rpt conj_tac
  \\ rpt (rpt gen_tac \\ disch_tac)
  \\ gvs [full_evaluate_def, AllCaseEqs(), dec_clock_def]
  \\ gvs [do_eval_res_def, do_eval_def, do_eval_run_def, declare_env_def,
          reset_env_generation_def, AllCaseEqs()]
  >~ [‘do_eval_init _ _ _ = SOME _’] >- gvs [do_eval_init_def, AllCaseEqs()]
  \\ Cases_on ‘y.env_id_counter’ \\ rename1 ‘_ = (g1,rest1)’
  \\ PairCases_on ‘rest1’ \\ gvs []
  \\ Cases_on ‘y'.env_id_counter’ \\ rename1 ‘_ = (g2,rest2)’
  \\ PairCases_on ‘rest2’ \\ gvs []
QED

Theorem ref_rel_restrict:
  ref_rel (v_rel fr1 pe) x y ∧ fr ⊑ fr1 ∧ ref_rel (v_rel fr pe) x z ⇒
  ref_rel (v_rel fr pe) x y
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ Cases_on ‘z’ \\ rw [ref_rel_def]
  \\ gvs [LIST_REL_EL_EQN] \\ metis_tac [v_rel_restrict]
QED

Theorem refs_rel_restrict:
  refs_rel fr pe refs1 refs2 ∧ fr ⊑ fr1 ∧
  refs_rel fr1 pe (refs1 ++ extra) refs3 ⇒
  refs_rel fr pe refs1 refs3
Proof
  rw [refs_rel_def]
  \\ qpat_x_assum ‘∀n. n < LENGTH refs1 ⇒ _’ drule \\ strip_tac
  \\ qpat_x_assum ‘∀n. n < _ + _ ⇒ _’ (qspec_then ‘n’ mp_tac)
  \\ simp [EL_APPEND1] \\ strip_tac
  \\ imp_res_tac FLOOKUP_SUBMAP \\ gvs []
  \\ metis_tac [ref_rel_restrict]
QED

Theorem prelude_ok_SUBMAP:
  prelude_ok fr1 pe refs ∧ fr ⊑ fr1 ⇒ prelude_ok fr pe refs
Proof
  rw [prelude_ok_def] \\ gvs [DISJ_IMP_THM, FORALL_AND_THM, FRANGE_FLOOKUP]
  \\ metis_tac [FLOOKUP_SUBMAP]
QED

(* eval_rel only looks at the eval state and the prelude references *)
Theorem eval_rel_cong:
  eval_rel C fr pe es (t:'ffi evalSem$state) ∧
  (t1:'ffi evalSem$state).eval_state = t.eval_state ∧
  prelude_vals pe t1.refs = prelude_vals pe t.refs ⇒
  eval_rel C fr pe es t1
Proof
  Cases_on ‘es’ \\ simp [eval_rel_def]
  \\ rename1 ‘SOME ev’ \\ Cases_on ‘ev’ \\ rw [eval_rel_def, prelude_vals_def]
QED

(* the input program without its eval state *)
Theorem state_rel_no_eval:
  state_rel H G C fr pe s (t:'ffi evalSem$state) ⇒
  state_rel F (t.eval_state,prelude_vals pe t.refs) C fr pe
    (s with <| clock := k; eval_state := NONE |>) (t with clock := k)
Proof
  rw [state_rel_def]
QED

(* after the compiled program has run code that the input program has
   not run, which only allocated references *)
Theorem state_rel_restore:
  state_rel H G C fr pe s (t:'ffi evalSem$state) ∧ fr ⊑ fr1 ∧
  state_rel F (t.eval_state,prelude_vals pe t.refs) C fr1 pe
    (s with <| clock := k; refs := s.refs ++ refs; eval_state := NONE;
               ptr_eq_oracle := po |>) t1 ⇒
  state_rel H G C fr pe (s with ptr_eq_oracle := po) (t1 with clock := s.clock)
Proof
  simp [state_rel_def] \\ strip_tac
  \\ ‘refs_rel fr pe s.refs t1.refs’ by metis_tac [refs_rel_restrict]
  \\ ‘prelude_ok fr pe t1.refs’ by metis_tac [prelude_ok_SUBMAP]
  \\ Cases_on ‘s.eval_state’ \\ gvs []
  \\ irule eval_rel_cong \\ qexists_tac ‘t’ \\ simp []
QED

(* ------------------------------------------------------------------ *
   Simulation
 * ------------------------------------------------------------------ *)

Definition exp_sim_def:
  exp_sim H (:'ffi) ⇔
    ∀(s:'ffi evalSem$state) env es s1 r G C fr pe t env2.
      evaluate s env es = (s1,r) ∧ r ≠ Rerr (Rabort Rtype_error) ∧
      state_rel H G C fr pe s t ∧ env_rel fr pe env env2 ⇒
      ∃ck fr1 t1 r1.
        evaluate (t with clock := t.clock + ck) env2 (MAP compile_exp es) =
          (t1,r1) ∧
        fr ⊑ fr1 ∧ state_rel H G C fr1 pe s1 t1 ∧
        res_rel (LIST_REL (v_rel fr1 pe)) (v_rel fr1 pe) r r1
End

Theorem eval_fail_ptr_eq_EvalPending[local,simp]:
  eval_fail_ptr_eq vs (SOME (EvalPending r)) refs po (:'ffi) = po
Proof
  simp [eval_fail_ptr_eq_def] \\ every_case_tac \\ simp []
QED

(* $eval fails when $init has not been called *)
Theorem evaluate_eval_body_pending:
  state_rel H G C fr pe (s:'ffi evalSem$state) t ∧
  s.eval_state = SOME (EvalPending r) ⇒
  evaluate t (pe with v := nsBind «x» (Conv NONE [w1; w2]) pe.v) [eval_body] =
    (t,Rval [Conv NONE [w1; Litv (StrLit «Compiler error»)]])
Proof
  rw [state_rel_def] \\ gvs [eval_rel_def]
  \\ gvs [prelude_ok_def, DISJ_IMP_THM, FORALL_AND_THM]
  \\ simp [eval_body_def, full_evaluate_def, can_pmatch_all_def, pmatch_def,
           pat_bindings_def, do_app_def, store_lookup_def, nsLookup_nsBind,
           nsOptBind_def, lit_same_type_def, eval_fail_def, do_con_check_def,
           build_conv_def]
QED

(* the compiled program runs the compiler closure, which the input
   program does not run: by compiler_closure, it would run correctly in
   the source semantics, and by exp_sim, so does its compiled version *)
Theorem compiler_closure_run:
  exp_sim F (:'ffi) ∧ state_rel H G C fr pe (s:'ffi evalSem$state) t ∧
  compiler_closure comp dec st0 c (:'ffi) ∧ compiler_reach comp st0 st_v ∧
  v_rel fr pe c c' ∧
  data_v st_v ∧ data_v decs_v ∧ dec decs_v = SOME decs ⇒
  ∃env e ck t1 res.
    do_opapp [c'; Conv NONE [Conv NONE [nat_to_v gen; nat_to_v id];
                             st_v; decs_v]] = SOME (env,e) ∧
    (∀k. evaluate (t with clock := ck + k) env [e] = (t1 with clock := k,res)) ∧
    t1.eval_state = t.eval_state ∧
    state_rel H G C fr pe
      (s with ptr_eq_oracle :=
         closure_ptr_eq c (Conv NONE [Conv NONE [nat_to_v gen; nat_to_v id];
                                      st_v; decs_v])
           s.refs s.ptr_eq_oracle (:'ffi))
      (t1 with clock := s.clock) ∧
    (comp ((gen,id),st_v,decs) = NONE ⇒ res = Rerr (Rraise bind_exn_v)) ∧
    (∀st_v2 bs ws.
       comp ((gen,id),st_v,decs) = SOME (st_v2,bs,ws) ∧ data_v st_v2 ⇒
       ∃bs_v ws_v. res = Rval [Conv NONE [st_v2; bs_v; ws_v]] ∧
                   v_to_mlstring bs_v = SOME bs ∧
                   v_to_word64_list ws_v = SOME ws)
Proof
  rpt strip_tac
  \\ gvs [compiler_closure_def]
  \\ first_x_assum (qspecl_then [‘gen’,‘id’,‘st_v’,‘decs_v’,‘decs’] mp_tac)
  \\ simp [] \\ strip_tac
  \\ first_x_assum (qspecl_then [‘s.refs’,‘s.ptr_eq_oracle’] strip_assume_tac)
  \\ ‘r ≠ Rerr (Rabort Rtimeout_error)’
    by (Cases_on ‘comp ((gen,id),st_v,decs)’ \\ gvs []
        \\ rename1 ‘_ = SOME x’ \\ PairCases_on ‘x’ \\ gvs [])
  \\ qmatch_asmsub_abbrev_tac ‘do_opapp [c; arg]’
  \\ ‘closure_ptr_eq c arg s.refs s.ptr_eq_oracle (:'ffi) = po'’
    by (irule evalSemPropsTheory.closure_ptr_eq_thm \\ metis_tac [])
  \\ simp []
  \\ ‘LIST_REL (v_rel fr pe) [c; arg] [c'; arg]’
    by simp [Abbr ‘arg’, v_rel_data_v_refl, nat_to_v_def]
  \\ drule_all do_opapp_rel \\ strip_tac
  \\ first_x_assum (qspec_then
       ‘<| clock := 0; refs := s.refs; ffi := s.ffi;
           next_type_stamp := s.next_type_stamp;
           next_exn_stamp := s.next_exn_stamp; eval_state := NONE;
           ptr_eq_oracle := s.ptr_eq_oracle;
           eval_oracle := K (F,K (K (K 0))) |>’ mp_tac)
  \\ simp [] \\ strip_tac
  \\ drule (CONJUNCT1 evaluate_to_evalSem_NONE) \\ simp [to_evalSem_def]
  \\ qmatch_goalsub_abbrev_tac ‘evalSem$evaluate s0 env [exp] = (s1,r)’
  \\ ‘s0 = s with <| clock := ck; eval_state := NONE |> ∧
      s1 = s with <| clock := 0; eval_state := NONE; refs := s.refs ++ refs';
                     ptr_eq_oracle := po' |>’
    by simp [Abbr ‘s0’, Abbr ‘s1’, evalSemTheory.state_component_equality]
  \\ simp [] \\ strip_tac
  \\ ‘r ≠ Rerr (Rabort Rtype_error)’
    by (strip_tac \\ Cases_on ‘comp ((gen,id),st_v,decs)’ \\ gvs []
        \\ rename1 ‘_ = SOME x’ \\ PairCases_on ‘x’ \\ gvs [])
  \\ drule_then (qspec_then ‘ck’ assume_tac) state_rel_no_eval
  \\ qpat_x_assum ‘exp_sim _ _’ (assume_tac o REWRITE_RULE [exp_sim_def])
  \\ first_x_assum drule_all \\ strip_tac
  \\ qpat_x_assum ‘evaluate _ env2 _ = (t1,r1)’
       (assume_tac o SIMP_RULE (srw_ss()) [])
  \\ ‘t1.clock = 0 ∧ t1.eval_state = t.eval_state’ by gvs [state_rel_def]
  \\ ‘r1 ≠ Rerr (Rabort Rtimeout_error)’
    by (strip_tac \\ Cases_on ‘comp ((gen,id),st_v,decs)’ \\ gvs []
        \\ rename1 ‘_ = SOME x’ \\ PairCases_on ‘x’ \\ gvs [])
  \\ qpat_assum ‘evaluate _ env2 _ = (t1,r1)’ (mp_tac o MATCH_MP lift_exp)
  \\ simp [] \\ strip_tac
  \\ drule_all state_rel_restore \\ strip_tac
  \\ qexistsl_tac [‘ck + ck'’,‘t1’,‘r1’] \\ simp []
  \\ Cases_on ‘comp ((gen,id),st_v,decs)’ \\ gvs [v_rel_data_v]
  \\ rename1 ‘_ = SOME x’ \\ PairCases_on ‘x’ \\ gvs [v_rel_def]
  \\ rpt strip_tac
  \\ ‘data_v bs_v ∧ data_v ws_v’
    by (gvs [v_to_mlstring_def, AllCaseEqs()]
        \\ metis_tac [v_to_word64_list_data_v])
  \\ gvs [v_rel_data_v]
QED

Theorem data_v_concrete_v:
  (∀v. data_v v ⇒ concrete_v v) ∧
  (∀vs. data_v_list vs ⇒ concrete_v_list vs)
Proof
  ho_match_mp_tac data_v_ind \\ rw []
  \\ gvs [Once data_v_def, Once concrete_v_def]
  \\ every_case_tac \\ gvs [concrete_v_def]
QED

(* $eval in EvalRun mode: the compiled program runs the compiler closure,
   stores the new compiler state and calls Eval in EvalDecs mode *)
Theorem evaluate_eval_body_run:
  exp_sim F (:'ffi) ∧ state_rel H G C fr pe (s:'ffi evalSem$state) t ∧
  s.eval_state = SOME (EvalRun r) ∧ env_rel fr pe env1 env2 ∧
  r.decode_decs decs_v = SOME decs ∧ data_v decs_v ∧
  data_v r.compiler_state ⇒
  let env_pe = pe with v := nsBind «x» (Conv NONE [Env env2 id; decs_v]) pe.v in
  (r.compiler (id,r.compiler_state,decs) = NONE ⇒
   ∃ck t1.
     (∀k. evaluate (t with clock := ck + k) env_pe [eval_body] =
            (t1 with clock := k,
             Rval [Conv NONE [Env env2 id; Litv (StrLit «Compiler error»)]])) ∧
     state_rel H G C fr pe
       (s with ptr_eq_oracle :=
          eval_fail_ptr_eq [Env env1 id; decs_v] s.eval_state s.refs
            s.ptr_eq_oracle (:'ffi))
       (t1 with clock := s.clock)) ∧
  (∀st_v2 rest.
     r.compiler (id,r.compiler_state,decs) = SOME (st_v2,rest) ∧
     data_v st_v2 ⇒
     ∃ck t1.
       state_rel H G C fr pe
         (s with <| eval_state :=
                      SOME (EvalRun (add_decs_generation
                                       (r with compiler_state := st_v2)));
                    ptr_eq_oracle := shift_seq 1 s.ptr_eq_oracle |>)
         (t1 with clock := s.clock) ∧
       evaluate (t with clock := ck) env_pe [eval_body] =
         (t1 with clock := 0,Rerr (Rabort Rtimeout_error)) ∧
       ∀k. evaluate (t with clock := ck + k + 1) env_pe [eval_body] =
             case evaluate_decs (t1 with clock := k) env2
                    (MAP compile_dec decs) of
             | (st2,Rval env3) =>
                 (case declare_env st2.eval_state (extend_dec_env env3 env2) of
                  | NONE => (st2,Rerr (Rabort Rtype_error))
                  | SOME (x,es2) =>
                      (st2 with eval_state :=
                         reset_env_generation t.eval_state es2,
                       Rval [Conv NONE [x; Litv (StrLit «»)]]))
             | (st2,Rerr (Rraise v)) =>
                 (st2 with eval_state :=
                    reset_env_generation t.eval_state st2.eval_state,
                  Rerr (Rraise v))
             | (st2,Rerr (Rabort a)) => (st2,Rerr (Rabort a)))
Proof
  simp [] \\ strip_tac
  \\ qpat_assum ‘state_rel _ _ _ _ _ _ _’
       (strip_assume_tac o REWRITE_RULE [state_rel_def])
  \\ gvs [eval_rel_def, prelude_ok_def, DISJ_IMP_THM, FORALL_AND_THM]
  \\ ‘v = r.compiler_state’ by metis_tac [v_rel_data_v]
  \\ gvs []
  \\ PairCases_on ‘id’
  \\ ‘compiler_reach r.compiler r.compiler_state r.compiler_state’
    by simp [compiler_reach_refl]
  \\ drule_all compiler_closure_run
  \\ disch_then (qspecl_then [‘id1’,‘id0’] strip_assume_tac)
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  >- (
    qexistsl_tac [‘ck + 1’,‘t1’] \\ gvs [eval_fail_ptr_eq_def]
    \\ simp [eval_body_def, full_evaluate_def, can_pmatch_all_def, pmatch_def,
             pat_bindings_def, do_app_def, store_lookup_def, nsLookup_nsBind,
             nsOptBind_def, lit_same_type_def, do_con_check_def,
             build_conv_def, dec_clock_def, eval_fail_def])
  \\ PairCases_on ‘rest’ \\ first_x_assum drule_all \\ strip_tac
  \\ gvs []
  \\ qmatch_asmsub_abbrev_tac ‘state_rel _ _ _ _ _ (s with ptr_eq_oracle := po1)’
  \\ ‘∃k. po1 = skip_ptr_eq k s.ptr_eq_oracle’
    by (simp [Abbr ‘po1’]
        \\ irule evalSemPropsTheory.compiler_closure_ptr_eq
        \\ metis_tac [])
  \\ ‘shift_seq 1 po1 = shift_seq 1 s.ptr_eq_oracle’ by simp []
  \\ ‘compiler_closure r.compiler r.decode_decs st_v2 r.closure (:'ffi)’
    by (irule compiler_closure_reach \\ first_assum $ irule_at Any
        \\ irule compiler_reach_step \\ metis_tac [compiler_reach_refl])
  \\ qpat_assum ‘state_rel _ _ _ _ _ _ (t1 with clock := _)’
       (strip_assume_tac o REWRITE_RULE [state_rel_def])
  \\ gvs [eval_rel_def, prelude_ok_def, DISJ_IMP_THM, FORALL_AND_THM]
  \\ ‘C ((id0,id1),r.compiler_state,inc_compile_decs decs) =
      SOME (st_v2,rest0,rest1)’ by gvs [decs_factor_def]
  \\ ‘concrete_v decs_v ∧ concrete_v st_v2 ∧ concrete_v r.compiler_state’
    by simp [data_v_concrete_v]
  \\ qpat_assum ‘∀k. evaluate _ env [e] = _’
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC ‘0’)
  \\ qexistsl_tac [‘ck + 1’,
       ‘t1 with <| refs := LUPDATE (Refv st_v2) (prelude_loc pe «state») t1.refs;
                   eval_state := SOME (EvalDecs (add_decs_generation
                     (adjust_decs inc_compile_decs C (r with closure := cl0') with
                        compiler_state := st_v2)));
                   ptr_eq_oracle := shift_seq 1 t1.ptr_eq_oracle |>’]
  \\ simp [eval_body_def, full_evaluate_def, can_pmatch_all_def, pmatch_def,
           pat_bindings_def, do_app_def, store_lookup_def, nsLookup_nsBind,
           nsOptBind_def, lit_same_type_def, do_con_check_def,
           build_conv_def, dec_clock_def, store_assign_def,
           store_v_same_type_def, EL_LUPDATE, do_eval_init_def,
           do_eval_res_def, do_eval_def, adjust_decs_def, compiler_agrees_def,
           do_eval_fail_def, eval_result_def]
  \\ simp [inc_compile_decs_def]
  \\ reverse conj_tac >- (gen_tac \\ rpt (TOP_CASE_TAC \\ gvs []))
  \\ simp [state_rel_def, eval_rel_def, EL_LUPDATE, refs_rel_LUPDATE,
           prelude_ok_def, v_rel_data_v_refl]
  \\ gvs [DISJ_IMP_THM, add_decs_generation_def, adjust_decs_def,
          decs_factor_def, v_rel_data_v_refl]
  \\ Cases_on ‘r.env_id_counter’ \\ rename1 ‘_ = (g,ctr)’
  \\ PairCases_on ‘ctr’ \\ gvs [v_rel_data_v_refl]
  \\ metis_tac []
QED

(* Eval in EvalRun mode and in EvalDecs mode conclude in the same way *)
Theorem state_rel_reset_env_generation:
  state_rel H G C fr pe s (t:'ffi evalSem$state) ∧
  s.eval_state = SOME (EvalRun y) ⇒
  state_rel H G C fr pe
    (s with eval_state :=
       reset_env_generation (SOME (EvalRun p)) s.eval_state)
    (t with eval_state :=
       reset_env_generation
         (SOME (EvalDecs (adjust_decs inc_compile_decs C (p with closure := cl))))
         t.eval_state)
Proof
  rw [state_rel_def] \\ gvs [eval_rel_def]
  \\ Cases_on ‘p.env_id_counter’ \\ rename1 ‘_ = (g1,ctr1)’
  \\ PairCases_on ‘ctr1’
  \\ Cases_on ‘y.env_id_counter’ \\ rename1 ‘_ = (g2,ctr2)’
  \\ PairCases_on ‘ctr2’
  \\ gvs [reset_env_generation_def, adjust_decs_def, eval_rel_def,
          decs_factor_def]
  \\ metis_tac []
QED

Theorem pmatch_list_REPLICATE_Pany[local]:
  ∀n vs env.
    pmatch_list envC st (REPLICATE n Pany) vs env =
    if LENGTH vs = n then Match env else Match_type_error
Proof
  Induct >> Cases_on `vs` >> rw [pmatch_def]
QED

Theorem v_rel_check_shape[local]:
  (∀c sa x y. v_rel fr pe x y ∧ check_shape c sa x ⇒ check_shape c sa y) ∧
  (∀c sas xs ys.
     LIST_REL (v_rel fr pe) xs ys ∧ check_shapes c sas xs ⇒
     check_shapes c sas ys)
Proof
  ho_match_mp_tac check_shape_ind \\ rw [check_shape_def]
  >- metis_tac [v_rel_check_type]
  >- (
    Cases_on ‘x’ \\ gvs [pmatch_def, v_rel_def]
    \\ rename [‘Conv oo _’] \\ Cases_on ‘oo’
    \\ gvs [pmatch_def, AllCaseEqs(), pmatch_list_REPLICATE_Pany]
    \\ imp_res_tac LIST_REL_LENGTH \\ gvs [] \\ metis_tac [])
  >- (
    Cases_on ‘x’ \\ gvs [v_rel_def]
    \\ rename [‘case oo of NONE => _ | SOME _ => _’]
    \\ Cases_on ‘oo’ \\ gvs [SF SFY_ss])
  >- (
    imp_res_tac v_rel_v_to_list
    \\ Cases_on ‘v_to_list x’ \\ gvs []
    \\ gvs [EVERY_MEM, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, SF SFY_ss]
    \\ metis_tac [])
  \\ gvs [check_shape_def, SF SFY_ss]
QED

(* the case for Eval needs the simulation for programs without an eval
   state, which is the instance of this theorem where H is false *)
Theorem compile_evaluate_lemma:
  (H ⇒ exp_sim F (:'ffi)) ⇒
  (∀(s:'ffi evalSem$state) env es s1 r.
     evaluate s env es = (s1,r) ∧ r ≠ Rerr (Rabort Rtype_error) ⇒
     ∀G C fr pe t env2.
       state_rel H G C fr pe s t ∧ env_rel fr pe env env2 ⇒
       ∃ck fr1 t1 r1.
         evaluate (t with clock := t.clock + ck) env2 (MAP compile_exp es) =
           (t1,r1) ∧
         fr ⊑ fr1 ∧ state_rel H G C fr1 pe s1 t1 ∧
         res_rel (LIST_REL (v_rel fr1 pe)) (v_rel fr1 pe) r r1) ∧
  (∀(s:'ffi evalSem$state) env v pes err_v s1 r.
     evaluate_match s env v pes err_v = (s1,r) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
     ∀G C fr pe t env2 v2 err_v2.
       state_rel H G C fr pe s t ∧ env_rel fr pe env env2 ∧
       v_rel fr pe v v2 ∧ v_rel fr pe err_v err_v2 ⇒
       ∃ck fr1 t1 r1.
         evaluate_match (t with clock := t.clock + ck) env2 v2
           (MAP (λ(p,e). (compile_pat p, compile_exp e)) pes) err_v2 =
           (t1,r1) ∧
         fr ⊑ fr1 ∧ state_rel H G C fr1 pe s1 t1 ∧
         res_rel (LIST_REL (v_rel fr1 pe)) (v_rel fr1 pe) r r1) ∧
  (∀(s:'ffi evalSem$state) env ds s1 r.
     evaluate_decs s env ds = (s1,r) ∧ r ≠ Rerr (Rabort Rtype_error) ⇒
     ∀G C fr pe t env2.
       state_rel H G C fr pe s t ∧ env_rel fr pe env env2 ⇒
       ∃ck fr1 t1 r1.
         evaluate_decs (t with clock := t.clock + ck) env2
           (MAP compile_dec ds) = (t1,r1) ∧
         fr ⊑ fr1 ∧ state_rel H G C fr1 pe s1 t1 ∧
         res_rel (nenv_rel fr1 pe) (v_rel fr1 pe) r r1)
Proof
  disch_tac
  \\ ho_match_mp_tac (name_ind_cases [] full_evaluate_ind)
  \\ rpt conj_tac
  \\ rpt (rpt gen_tac \\ disch_tac)
  \\ pop_assum strip_assume_tac
  >~ [‘evalSem$evaluate _ _ [] = _’] >- suspend "nil"
  >~ [‘evalSem$evaluate _ _ (_::_::_) = _’] >- suspend "cons"
  >~ [‘evalSem$evaluate _ _ [Lit _] = _’] >- suspend "Lit"
  >~ [‘evalSem$evaluate _ _ [Raise _] = _’] >- suspend "Raise"
  >~ [‘evalSem$evaluate _ _ [Handle _ _] = _’] >- suspend "Handle"
  >~ [‘evalSem$evaluate _ _ [Con _ _] = _’] >- suspend "Con"
  >~ [‘evalSem$evaluate _ _ [Var _] = _’] >- suspend "Var"
  >~ [‘evalSem$evaluate _ _ [Fun _ _] = _’] >- suspend "Fun"
  >~ [‘evalSem$evaluate _ _ [App _ _] = _’] >- suspend "App"
  >~ [‘evalSem$evaluate _ _ [Log _ _ _] = _’] >- suspend "Log"
  >~ [‘evalSem$evaluate _ _ [If _ _ _] = _’] >- suspend "If"
  >~ [‘evalSem$evaluate _ _ [Mat _ _] = _’] >- suspend "Mat"
  >~ [‘evalSem$evaluate _ _ [Let _ _ _] = _’] >- suspend "Let"
  >~ [‘evalSem$evaluate _ _ [Letrec _ _] = _’] >- suspend "Letrec"
  >~ [‘evalSem$evaluate _ _ [Tannot _ _] = _’] >- suspend "Tannot"
  >~ [‘evalSem$evaluate _ _ [Lannot _ _] = _’] >- suspend "Lannot"
  >~ [‘evalSem$evaluate _ _ [Open _ _] = _’] >- suspend "Open"
  >~ [‘evalSem$evaluate _ _ [Assert _ _] = _’] >- suspend "Assert"
  >~ [‘evalSem$evaluate_match _ _ _ [] _ = _’] >- suspend "match_nil"
  >~ [‘evalSem$evaluate_match _ _ _ ((_,_)::_) _ = _’] >- suspend "match_cons"
  >~ [‘evalSem$evaluate_decs _ _ [] = _’] >- suspend "decs_nil"
  >~ [‘evalSem$evaluate_decs _ _ (_::_::_) = _’] >- suspend "decs_cons"
  >~ [‘evalSem$evaluate_decs _ _ [Dlet _ _ _] = _’] >- suspend "Dlet"
  >~ [‘evalSem$evaluate_decs _ _ [Dletrec _ _] = _’] >- suspend "Dletrec"
  >~ [‘evalSem$evaluate_decs _ _ [Dtype _ _] = _’] >- suspend "Dtype"
  >~ [‘evalSem$evaluate_decs _ _ [Dtabbrev _ _ _ _] = _’] >- suspend "Dtabbrev"
  >~ [‘evalSem$evaluate_decs _ _ [Denv _] = _’] >- suspend "Denv"
  >~ [‘evalSem$evaluate_decs _ _ [Dexn _ _ _] = _’] >- suspend "Dexn"
  >~ [‘evalSem$evaluate_decs _ _ [Dopen _ _] = _’] >- suspend "Dopen"
  >~ [‘evalSem$evaluate_decs _ _ [Dmod _ _] = _’] >- suspend "Dmod"
  >- suspend "Dlocal"
QED

Resume compile_evaluate_lemma[nil]:
  gvs [full_evaluate_def]
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def]
QED

Resume compile_evaluate_lemma[cons]:
  qpat_x_assum ‘evaluate _ _ _ = _ ∧ _’ strip_assume_tac
  \\ qpat_x_assum ‘evaluate _ _ (_::_::_) = _’
       (strip_assume_tac o SIMP_RULE (srw_ss()) [Once full_evaluate_def, AllCaseEqs()])
  \\ gvs []
  \\ first_x_assum drule_all \\ strip_tac
  >>~- ([‘evaluate s env [e1] = (_, Rerr err)’],
    qexistsl_tac [‘ck’,‘fr1’] \\ simp [full_evaluate_def]
    \\ Cases_on ‘err’ \\ gvs [])
  \\ ‘env_rel fr1 pe env env2’ by metis_tac [env_rel_SUBMAP]
  \\ first_x_assum drule_all \\ strip_tac
  \\ qpat_assum ‘evaluate (t with clock := _) env2 [_] = _’
       (mp_tac o MATCH_MP lift_exp)
  \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
  \\ qexistsl_tac [‘ck + ck'’,‘fr1'’]
  \\ gvs [full_evaluate_def]
  \\ imp_res_tac evaluate_sing \\ gvs []
  >- (conj_tac >- metis_tac [SUBMAP_TRANS] \\ metis_tac [v_rel_SUBMAP])
  \\ rename1 ‘Rerr err’ \\ Cases_on ‘err’ \\ gvs []
  \\ metis_tac [SUBMAP_TRANS]
QED

Resume compile_evaluate_lemma[Lit]:
  gvs [full_evaluate_def, compile_exp_def]
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def, v_rel_def]
QED

Resume compile_evaluate_lemma[Raise]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1’] \\ gvs [full_evaluate_def]
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ rename1 ‘Rerr err’ \\ Cases_on ‘err’ \\ gvs []
QED

Resume compile_evaluate_lemma[Handle]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ last_x_assum drule_all \\ strip_tac
  >~ [‘_ = (_,Rval _)’] >- (qexistsl_tac [‘ck’,‘fr1’] \\ simp [])
  >~ [‘_ = (_,Rerr (Rabort _))’] >- (qexistsl_tac [‘ck’,‘fr1’] \\ simp [])
  \\ ‘refs_rel fr1 pe st'.refs t1.refs ∧ env2.c = env.c’
    by gvs [state_rel_def, env_rel_def]
  \\ drule_all can_pmatch_all_rel \\ strip_tac
  \\ ‘env_rel fr1 pe env env2’ by metis_tac [env_rel_SUBMAP]
  \\ last_x_assum drule_all \\ strip_tac
  \\ qpat_assum ‘evaluate (t with clock := _) env2 [_] = _’
       (mp_tac o MATCH_MP lift_exp)
  \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
  \\ qexistsl_tac [‘ck + ck'’,‘fr1'’]
  \\ gvs [MAP_MAP_o, o_DEF, LAMBDA_PROD]
  \\ metis_tac [SUBMAP_TRANS]
QED

Resume compile_evaluate_lemma[Con]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1’]
  \\ ‘env2.c = env.c’ by gvs [env_rel_def]
  \\ gvs [full_evaluate_def, MAP_REVERSE]
  >- (
    ‘LIST_REL (v_rel fr1 pe) (REVERSE vs) (REVERSE y)’ by simp [EVERY2_REVERSE]
    \\ drule_all build_conv_rel \\ strip_tac \\ simp [])
  \\ qmatch_asmsub_rename_tac ‘(s1,Rerr err)’ \\ Cases_on ‘err’ \\ gvs []
QED

Resume compile_evaluate_lemma[Var]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ drule_all env_rel_lookup \\ strip_tac
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def]
QED

Resume compile_evaluate_lemma[Fun]:
  gvs [full_evaluate_def, compile_exp_def]
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def, v_rel_def]
QED

Resume compile_evaluate_lemma[App]:
  rpt (qpat_x_assum ‘_ ∧ _’ strip_assume_tac)
  \\ Cases_on ‘op = Eval ∧ ∃e. es = [e]’
  >- (
    gvs [compile_exp_def]
    \\ qpat_x_assum ‘evaluate _ _ [App _ _] = _’ mp_tac
    \\ simp [Once full_evaluate_def]
    \\ Cases_on ‘evaluate s env [e]’
    \\ rename1 ‘evaluate s env [e] = (st1,res1)’
    \\ strip_tac
    \\ ‘res1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
    \\ qpat_x_assum ‘∀s1 r. (st1,res1) = (s1,r) ∧ _ ⇒ _’
         (qspecl_then [‘st1’,‘res1’] mp_tac)
    \\ simp [] \\ disch_then drule_all \\ strip_tac
    \\ reverse (Cases_on ‘res1’) \\ gvs []
    >- (
      qexistsl_tac [‘ck’,‘fr1’] \\ simp [full_evaluate_def]
      \\ qmatch_asmsub_rename_tac ‘evaluate s env [e] = (_,Rerr err)’
      \\ Cases_on ‘err’ \\ gvs [])
    \\ imp_res_tac evaluate_sing \\ gvs []
    \\ rename1 ‘v_rel fr1 pe v1 w1’
    \\ qpat_assum ‘state_rel _ _ _ _ _ st1 _’
         (mp_then Any (qspec_then ‘[v1]’ mp_tac) state_rel_eval_arity)
    \\ simp [] \\ strip_tac
    \\ Cases_on ‘do_eval_init [v1] st1.eval_state (:'ffi)’ \\ gvs []
    \\ drule_all evaluate_init_body \\ strip_tac
    \\ qpat_assum ‘evaluate (t with clock := _) env2 _ = _’
         (mp_tac o MATCH_MP lift_exp)
    \\ simp [] \\ disch_then (qspec_then ‘1’ assume_tac)
    \\ ‘nsLookup env2.v (Short «$init») = SOME (Closure pe «x» init_body)’
      by gvs [env_rel_def]
    \\ qexistsl_tac [‘ck + 1’,‘fr1’]
    \\ gvs [full_evaluate_def, do_opapp_def, dec_clock_def, v_rel_def])
  \\ Cases_on ‘op = Eval ∧ ∃e1 e2. es = [e1; e2]’
  >- (
    gvs [compile_exp_def]
    \\ qpat_x_assum ‘evaluate _ _ [App _ _] = _’ mp_tac
    \\ simp [Once full_evaluate_def]
    \\ Cases_on ‘evaluate s env [e2; e1]’
    \\ rename1 ‘evaluate s env [e2; e1] = (st1,res1)’
    \\ strip_tac
    \\ ‘res1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
    \\ qpat_x_assum ‘∀s1 r. (st1,res1) = (s1,r) ∧ _ ⇒ _’
         (qspecl_then [‘st1’,‘res1’] mp_tac)
    \\ simp [] \\ disch_then drule_all \\ strip_tac
    \\ ‘nsLookup env2.v (Short «$eval») = SOME (Closure pe «x» eval_body) ∧
        env2.c = env.c’ by gvs [env_rel_def]
    \\ reverse (Cases_on ‘res1’) \\ gvs []
    >- (
      qexistsl_tac [‘ck’,‘fr1’]
      \\ simp [full_evaluate_def, do_con_check_def]
      \\ qmatch_asmsub_rename_tac ‘evaluate s env [e2; e1] = (_,Rerr err)’
      \\ Cases_on ‘err’ \\ gvs [])
    \\ imp_res_tac evaluate_length \\ gvs [LENGTH_EQ_NUM_compute]
    \\ rename1 ‘evaluate s env [e2; e1] = (st1,Rval [v2; v1])’
    \\ rename1 ‘v_rel fr1 pe v2 w2’ \\ rename1 ‘v_rel fr1 pe v1 w1’
    \\ qpat_assum ‘state_rel _ _ _ _ _ st1 _’
         (mp_then Any (qspec_then ‘[v1; v2]’ mp_tac) state_rel_eval_arity)
    \\ simp [] \\ strip_tac \\ gvs []
    \\ qpat_assum ‘state_rel _ _ _ _ _ st1 _’
         (strip_assume_tac o MATCH_MP state_rel_eval_state)
    \\ gvs [do_eval_res_def, do_eval_def, do_eval_fail_def]
    \\ qpat_assum ‘evaluate (t with clock := _) env2 _ = _’
         (mp_tac o MATCH_MP lift_exp)
    \\ simp [] \\ strip_tac
    >~ [‘EvalPending’] >- (
      drule_all evaluate_eval_body_pending
      \\ disch_then (qspecl_then [‘w2’,‘w1’] assume_tac)
      \\ qpat_x_assum ‘∀extra. evaluate (t with clock := _) env2 _ = _’
           (qspec_then ‘1’ assume_tac)
      \\ qexistsl_tac [‘ck + 1’,‘fr1’]
      \\ gvs [full_evaluate_def, do_con_check_def, build_conv_def, do_opapp_def,
              dec_clock_def, v_rel_data_v_refl, v_rel_def])
    \\ rename1 ‘st1.eval_state = SOME (EvalRun rr)’
    \\ ‘exp_sim F (:'ffi)’ by gvs [state_rel_def]
    \\ Cases_on ‘do_eval_run [v1; v2] rr’ \\ gvs []
    \\ rename1 ‘do_eval_run _ _ = SOME dr’ \\ Cases_on ‘dr’ \\ gvs []
    \\ gvs [do_eval_run_def, AllCaseEqs(), v_rel_def]
    \\ ‘w2 = v2’ by metis_tac [v_rel_data_v]
    \\ gvs []
    \\ drule_all evaluate_eval_body_run
    \\ disch_then (qspec_then ‘id’ mp_tac) \\ simp [] \\ strip_tac
    >~ [‘rr.compiler _ = NONE’] >- (
      ‘t1.clock = st1.clock’ by gvs [state_rel_def]
      \\ qpat_x_assum ‘∀extra. evaluate (t with clock := _) env2 _ = _’
           (qspec_then ‘ck' + 1’ assume_tac)
      \\ qpat_x_assum ‘∀k. evaluate (t1 with clock := _) _ _ = _’
           (qspec_then ‘st1.clock’ assume_tac)
      \\ qexistsl_tac [‘ck + (ck' + 1)’,‘fr1’]
      \\ gvs [full_evaluate_def, do_con_check_def, build_conv_def, do_opapp_def,
              dec_clock_def, v_rel_data_v_refl, v_rel_def])
    >~ [‘_ = (_,Rerr (Rabort Rtimeout_error)) ∧ _’] >- (
      ‘t1.clock = 0’ by gvs [state_rel_def]
      \\ qpat_x_assum ‘∀extra. evaluate (t with clock := _) env2 _ = _’
           (qspec_then ‘ck' + 1’ assume_tac)
      \\ qexistsl_tac [‘ck + (ck' + 1)’,‘fr1’]
      \\ gvs [full_evaluate_def, do_con_check_def, build_conv_def, do_opapp_def,
              dec_clock_def])
    \\ ‘t1.clock = st1.clock’ by gvs [state_rel_def]
    \\ ‘∃n. st1.clock = n + 1’ by (Cases_on ‘st1.clock’ \\ gvs [ADD1])
    \\ qpat_x_assum ‘state_rel _ _ _ _ _ _ (t1' with clock := _)’
         (mp_then Any (qspec_then ‘n’ assume_tac) state_rel_clock)
    \\ gvs [dec_clock_def]
    \\ first_x_assum drule_all \\ strip_tac
    \\ qpat_x_assum ‘∀extra. evaluate (t with clock := _) env2 _ = _’
         (qspec_then ‘ck' + ck'' + 1’ assume_tac)
    \\ qpat_x_assum ‘∀k. evaluate (t1 with clock := _) _ _ = _’
         (qspec_then ‘ck'' + n’ assume_tac)
    \\ ‘∃cl0. t1.eval_state =
            SOME (EvalDecs (adjust_decs inc_compile_decs C (rr with closure := cl0)))’
      by (gvs [state_rel_def, eval_rel_def] \\ metis_tac [])
    \\ pop_assum strip_assume_tac
    \\ qexistsl_tac [‘ck + (ck' + ck'' + 1)’,‘fr1'’]
    \\ gvs [full_evaluate_def, do_con_check_def, build_conv_def, do_opapp_def,
            dec_clock_def, eval_result_def]
    >~ [‘declare_env st2.eval_state _ = SOME _’] >- (
      ‘env_rel fr1' pe (env2' +++ env') (y +++ env2'')’
        by (irule env_rel_extend_dec_env \\ simp [] \\ metis_tac [env_rel_SUBMAP])
      \\ drule_all state_rel_declare_env \\ strip_tac \\ simp [v_rel_def]
      \\ qpat_assum ‘evaluate_decs _ env' decs = _’
           (strip_assume_tac o SIMP_RULE (srw_ss()) [] o
            MATCH_MP (CONJUNCT2 (CONJUNCT2 evaluate_EvalRun)))
      \\ ‘∃y2. es2 = SOME (EvalRun y2)’ by gvs [declare_env_def, AllCaseEqs()]
      \\ conj_tac >- metis_tac [SUBMAP_TRANS]
      \\ drule state_rel_reset_env_generation \\ simp []
      \\ disch_then (qspec_then ‘rr’ mp_tac) \\ simp [])
    >~ [‘_ = (_,Rerr (Rraise _))’] >- (
      conj_tac >- metis_tac [SUBMAP_TRANS]
      \\ qpat_assum ‘evaluate_decs _ env' decs = _’
           (strip_assume_tac o SIMP_RULE (srw_ss()) [] o
            MATCH_MP (CONJUNCT2 (CONJUNCT2 evaluate_EvalRun)))
      \\ drule_all state_rel_reset_env_generation
      \\ disch_then (qspec_then ‘rr’ mp_tac) \\ simp [])
    \\ metis_tac [SUBMAP_TRANS])
  \\ ‘compile_exp (App op es) = App op (MAP compile_exp es)’
    by (rw [compile_exp_def] \\ every_case_tac \\ gvs [])
  \\ qpat_x_assum ‘evaluate _ _ [App _ _] = _’ mp_tac
  \\ simp [Once full_evaluate_def]
  \\ Cases_on ‘evaluate s env (REVERSE es)’
  \\ rename1 ‘evaluate s env (REVERSE es) = (st1,res1)’
  \\ strip_tac
  \\ ‘res1 ≠ Rerr (Rabort Rtype_error)’ by (strip_tac \\ gvs [])
  \\ qpat_x_assum ‘∀s1 r. (st1,res1) = (s1,r) ∧ _ ⇒ _’
       (qspecl_then [‘st1’,‘res1’] mp_tac)
  \\ simp [] \\ disch_then drule_all \\ strip_tac
  \\ reverse (Cases_on ‘res1’) \\ gvs []
  >- (
    qexistsl_tac [‘ck’,‘fr1’] \\ simp [full_evaluate_def, MAP_REVERSE]
    \\ gvs [MAP_REVERSE] \\ Cases_on ‘e’ \\ gvs [])
  \\ rename1 ‘LIST_REL _ vs ws’
  \\ Cases_on ‘op = Opapp’ >- (
    gvs [AllCaseEqs(), MAP_REVERSE]
    \\ ‘LIST_REL (v_rel fr1 pe) (REVERSE vs) (REVERSE ws)’
      by simp [EVERY2_REVERSE]
    \\ drule_all do_opapp_rel \\ strip_tac
    >~ [‘Rtimeout_error’] >- (
      ‘t1.clock = 0’ by gvs [state_rel_def]
      \\ qexistsl_tac [‘ck’,‘fr1’] \\ simp [full_evaluate_def])
    \\ ‘t1.clock = st1.clock’ by gvs [state_rel_def]
    \\ ‘state_rel H G C fr1 pe (dec_clock st1) (dec_clock t1)’
      by (simp [dec_clock_def] \\ metis_tac [state_rel_clock])
    \\ last_x_assum drule_all \\ strip_tac
    \\ qpat_assum ‘evaluate (t with clock := _) env2 _ = _’
         (mp_tac o MATCH_MP lift_exp)
    \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
    \\ qexistsl_tac [‘ck + ck'’,‘fr1'’]
    \\ gvs [full_evaluate_def, dec_clock_def]
    \\ metis_tac [SUBMAP_TRANS])
  \\ Cases_on ‘op = ThunkOp ForceThunk’ >- (
    gvs [AllCaseEqs(), MAP_REVERSE]
    \\ ‘LIST_REL (v_rel fr1 pe) (REVERSE vs) (REVERSE ws)’
      by simp [EVERY2_REVERSE]
    \\ drule_all dest_thunk_rel
    \\ simp []
    \\ strip_tac
    >~ [‘IsThunk Evaluated _’] >- (
      qexistsl_tac [‘ck’,‘fr1’] \\ simp [full_evaluate_def])
    \\ rename1 ‘v_rel fr1 pe f g’
    \\ ‘LIST_REL (v_rel fr1 pe) [f; Conv NONE []] [g; Conv NONE []]’
      by simp [v_rel_def]
    \\ drule_all do_opapp_rel \\ strip_tac
    >~ [‘Rtimeout_error’] >- (
      ‘t1.clock = 0’ by gvs [state_rel_def]
      \\ qexistsl_tac [‘ck’,‘fr1’] \\ simp [full_evaluate_def])
    \\ ‘t1.clock = st1.clock’ by gvs [state_rel_def]
    \\ ‘state_rel H G C fr1 pe (dec_clock st1) (dec_clock t1)’
      by (simp [dec_clock_def] \\ metis_tac [state_rel_clock])
    \\ last_x_assum drule_all \\ strip_tac
    \\ qpat_assum ‘evaluate (t with clock := _) env2 _ = _’
         (mp_tac o MATCH_MP lift_exp)
    \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
    >~ [‘update_thunk’] >- (
      ‘LIST_REL (v_rel fr1' pe) (REVERSE vs) (REVERSE ws)’
        by metis_tac [LIST_REL_v_rel_SUBMAP]
      \\ drule_all state_rel_update_thunk \\ strip_tac
      \\ qexistsl_tac [‘ck + ck'’,‘fr1'’]
      \\ gvs [full_evaluate_def, dec_clock_def]
      \\ metis_tac [SUBMAP_TRANS])
    \\ qexistsl_tac [‘ck + ck'’,‘fr1'’]
    \\ gvs [full_evaluate_def, dec_clock_def]
    \\ Cases_on ‘e'’ \\ gvs []
    \\ metis_tac [SUBMAP_TRANS])
  \\ Cases_on ‘op = Eval’ >- (
    rpt (first_x_assum (kall_tac o assert (is_forall o concl)))
    \\ imp_res_tac evaluate_length
    \\ ‘LENGTH vs ≠ 1 ∧ LENGTH vs ≠ 2’
      by (rpt strip_tac \\ gvs [LENGTH_EQ_NUM_compute])
    \\ qpat_assum ‘state_rel _ _ _ _ _ st1 _’
         (mp_then Any (qspec_then ‘REVERSE vs’ mp_tac) state_rel_eval_arity)
    \\ simp [] \\ strip_tac \\ gvs [])
  \\ Cases_on ‘op = PtrEq’ >- (
    gvs [AllCaseEqs(), MAP_REVERSE, SWAP_REVERSE_SYM]
    \\ imp_res_tac state_rel_do_eq
    \\ ‘t1.ptr_eq_oracle = st1.ptr_eq_oracle’ by gvs [state_rel_def]
    \\ qexistsl_tac [‘ck’,‘fr1’] \\ simp [full_evaluate_def]
    \\ gvs [state_rel_stamps, v_rel_data_v_refl])
  \\ gvs [AllCaseEqs(), MAP_REVERSE]
  \\ ‘LIST_REL (v_rel fr1 pe) (REVERSE vs) (REVERSE ws)’
    by simp [EVERY2_REVERSE]
  \\ drule_all do_app_rel \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1'’] \\ simp [full_evaluate_def]
  \\ conj_tac >- metis_tac [SUBMAP_TRANS]
  \\ rename1 ‘res_rel _ _ r0 r2’
  \\ Cases_on ‘r0’ \\ gvs [evaluateTheory.list_result_def]
  \\ rename1 ‘res_rel _ _ (Rerr err) r2’
  \\ Cases_on ‘err’ \\ gvs [evaluateTheory.list_result_def]
QED

Resume compile_evaluate_lemma[Log]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ last_x_assum drule_all \\ strip_tac
  >~ [‘_ = (_,Rerr err)’] >- (
    qexistsl_tac [‘ck’,‘fr1’] \\ simp []
    \\ Cases_on ‘err’ \\ gvs [])
  \\ imp_res_tac evaluate_sing \\ gvs []
  >~ [‘SOME (Val _)’] >- (
    drule_all do_log_rel_Val \\ strip_tac
    \\ qexistsl_tac [‘ck’,‘fr1’] \\ gvs [])
  \\ drule_all do_log_rel_Exp \\ strip_tac
  \\ ‘env_rel fr1 pe env env2’ by metis_tac [env_rel_SUBMAP]
  \\ first_x_assum drule_all \\ strip_tac
  \\ qpat_assum ‘evaluate (t with clock := _) env2 [_] = _’
       (mp_tac o MATCH_MP lift_exp)
  \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
  \\ qexistsl_tac [‘ck + ck'’,‘fr1'’] \\ gvs []
  \\ metis_tac [SUBMAP_TRANS]
QED

Resume compile_evaluate_lemma[If]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ last_x_assum drule_all \\ strip_tac
  >~ [‘_ = (_,Rerr err)’] >- (
    qexistsl_tac [‘ck’,‘fr1’] \\ simp []
    \\ Cases_on ‘err’ \\ gvs [])
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ drule_all do_if_rel \\ strip_tac
  \\ ‘env_rel fr1 pe env env2’ by metis_tac [env_rel_SUBMAP]
  \\ first_x_assum drule_all \\ strip_tac
  \\ qpat_assum ‘evaluate (t with clock := _) env2 [_] = _’
       (mp_tac o MATCH_MP lift_exp)
  \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
  \\ qexistsl_tac [‘ck + ck'’,‘fr1'’] \\ gvs []
  \\ metis_tac [SUBMAP_TRANS]
QED

Resume compile_evaluate_lemma[Mat]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ last_x_assum drule_all \\ strip_tac
  >~ [‘_ = (_,Rerr err)’] >- (
    qexistsl_tac [‘ck’,‘fr1’] \\ simp []
    \\ Cases_on ‘err’ \\ gvs [])
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ ‘refs_rel fr1 pe st'.refs t1.refs ∧ env2.c = env.c’
    by gvs [state_rel_def, env_rel_def]
  \\ drule_all can_pmatch_all_rel \\ strip_tac
  \\ ‘env_rel fr1 pe env env2’ by metis_tac [env_rel_SUBMAP]
  \\ ‘v_rel fr1 pe bind_exn_v bind_exn_v’ by simp [v_rel_data_v_refl]
  \\ last_x_assum drule_all \\ strip_tac
  \\ qpat_assum ‘evaluate (t with clock := _) env2 [_] = _’
       (mp_tac o MATCH_MP lift_exp)
  \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
  \\ qexistsl_tac [‘ck + ck'’,‘fr1'’]
  \\ gvs [MAP_MAP_o, o_DEF, LAMBDA_PROD]
  \\ metis_tac [SUBMAP_TRANS]
QED

Resume compile_evaluate_lemma[Let]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ last_x_assum drule_all \\ strip_tac
  >~ [‘_ = (_,Rerr err)’] >- (
    qexistsl_tac [‘ck’,‘fr1’] \\ simp []
    \\ Cases_on ‘err’ \\ gvs [])
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ ‘env_rel fr1 pe env env2’ by metis_tac [env_rel_SUBMAP]
  \\ drule_all env_rel_nsOptBind \\ disch_then (qspec_then ‘xo’ assume_tac)
  \\ first_x_assum drule_all \\ strip_tac
  \\ qpat_assum ‘evaluate (t with clock := _) env2 [_] = _’
       (mp_tac o MATCH_MP lift_exp)
  \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
  \\ qexistsl_tac [‘ck + ck'’,‘fr1'’] \\ gvs []
  \\ metis_tac [SUBMAP_TRANS]
QED

Resume compile_evaluate_lemma[Letrec]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ ‘env_rel fr pe (env with v := build_rec_env funs env env.v)
        (env2 with v := build_rec_env (compile_funs funs) env2 env2.v)’
    by (irule env_rel_build_rec_env \\ simp [])
  \\ first_x_assum drule_all \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1’]
  \\ simp [full_evaluate_def, MAP_FST_compile_funs]
QED

Resume compile_evaluate_lemma[Tannot]:
  gvs [full_evaluate_def, compile_exp_def]
  \\ first_x_assum drule_all \\ strip_tac
  \\ first_x_assum (irule_at Any) \\ simp [full_evaluate_def]
QED

Resume compile_evaluate_lemma[Lannot]:
  gvs [full_evaluate_def, compile_exp_def]
  \\ first_x_assum drule_all \\ strip_tac
  \\ first_x_assum (irule_at Any) \\ simp [full_evaluate_def]
QED

Resume compile_evaluate_lemma[Open]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ drule_all env_rel_open_dec_env \\ strip_tac
  \\ drule_all env_rel_extend_dec_env \\ strip_tac
  \\ first_x_assum drule_all \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1’] \\ simp [full_evaluate_def]
QED

Resume compile_evaluate_lemma[Assert]:
  gvs [full_evaluate_def, compile_exp_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1’] \\ gvs []
  >- (
    imp_res_tac evaluate_sing \\ gvs [env_rel_def]
    \\ drule_all (cj 1 v_rel_check_shape) \\ simp [])
  \\ Cases_on ‘r1’ \\ gvs []
QED

Resume compile_evaluate_lemma[match_nil]:
  gvs [full_evaluate_def]
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def]
QED

Resume compile_evaluate_lemma[match_cons]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ ‘refs_rel fr pe s.refs t.refs ∧ env2.c = env.c’
    by gvs [state_rel_def, env_rel_def]
  \\ qspecl_then [‘env.c’,‘s.refs’,‘p’,‘v’,‘[]’,‘t.refs’,‘v2’,‘[]’] mp_tac
       (CONJUNCT1 pmatch_rel)
  \\ simp []
  \\ strip_tac
  \\ drule_all env_rel_alist_to_ns \\ strip_tac
  \\ first_x_assum drule_all \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1’] \\ simp []
QED

Resume compile_evaluate_lemma[decs_nil]:
  gvs [full_evaluate_def]
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def, nenv_rel_nsEmpty]
QED

Resume compile_evaluate_lemma[decs_cons]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ last_x_assum drule_all \\ strip_tac
  >~ [‘_ = (_,Rerr err)’] >- (
    qexistsl_tac [‘ck’,‘fr1’] \\ simp []
    \\ Cases_on ‘err’ \\ gvs [])
  \\ qmatch_asmsub_rename_tac ‘evaluate_decs st1 _ (d2::ds) = (s1,r2)’
  \\ ‘r2 ≠ Rerr (Rabort Rtype_error)’
    by (strip_tac \\ gvs [combine_dec_result_def])
  \\ ‘env_rel fr1 pe env env2’ by metis_tac [env_rel_SUBMAP]
  \\ drule_all env_rel_extend_dec_env \\ strip_tac
  \\ first_x_assum drule_all \\ strip_tac
  \\ qpat_assum ‘evaluate_decs (t with clock := _) env2 _ = _’
       (mp_tac o MATCH_MP lift_decs)
  \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
  \\ qexistsl_tac [‘ck + ck'’,‘fr1'’] \\ gvs []
  \\ conj_tac >- metis_tac [SUBMAP_TRANS]
  \\ Cases_on ‘r2’ \\ gvs [combine_dec_result_def]
  >- (
    irule (SIMP_RULE (srw_ss()) [extend_dec_env_def] nenv_rel_extend_dec_env)
    \\ simp [] \\ metis_tac [nenv_rel_SUBMAP])
  \\ rename1 ‘Rerr err’ \\ Cases_on ‘err’ \\ gvs []
QED

Resume compile_evaluate_lemma[Dlet]:
  gvs [full_evaluate_def, compile_dec_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1’]
  \\ ‘env2.c = env.c’ by gvs [env_rel_def]
  \\ gvs [full_evaluate_def]
  >~ [‘_ = (_,Rerr err)’] >- (Cases_on ‘err’ \\ gvs [])
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ ‘refs_rel fr1 pe s1.refs t1.refs’ by gvs [state_rel_def]
  \\ qmatch_asmsub_rename_tac ‘v_rel fr1 pe v1 v2’
  \\ qspecl_then [‘env.c’,‘s1.refs’,‘p’,‘v1’,‘[]’,‘t1.refs’,‘v2’,‘[]’] mp_tac
       (Q.INST [‘fr’ |-> ‘fr1’] (CONJUNCT1 pmatch_rel))
  \\ simp [] \\ strip_tac \\ simp [nenv_rel_alist_to_ns, v_rel_data_v_refl]
QED

Resume compile_evaluate_lemma[Dletrec]:
  gvs [full_evaluate_def, compile_dec_def, AllCaseEqs()]
  \\ qexistsl_tac [‘0’,‘fr’]
  \\ ‘env2.c = env.c’ by gvs [env_rel_def]
  \\ simp [full_evaluate_def, MAP_FST_compile_funs]
  \\ qexists_tac ‘Rval <|v := build_rec_env (compile_funs funs) env2 nsEmpty;
                         c := nsEmpty|>’
  \\ gvs [nenv_rel_build_rec_env, EVERY_MAP, LAMBDA_PROD]
QED

Resume compile_evaluate_lemma[Dtype]:
  gvs [full_evaluate_def, compile_dec_def, AllCaseEqs()]
  \\ qexistsl_tac [‘0’,‘fr’]
  \\ ‘t.next_type_stamp = s.next_type_stamp’ by gvs [state_rel_def]
  \\ simp [full_evaluate_def, nenv_rel_nsEmpty, state_rel_stamps]
QED

Resume compile_evaluate_lemma[Dtabbrev]:
  gvs [full_evaluate_def, compile_dec_def]
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def, nenv_rel_nsEmpty]
QED

Resume compile_evaluate_lemma[Denv]:
  gvs [full_evaluate_def, compile_dec_def, AllCaseEqs()]
  \\ drule_all state_rel_declare_env \\ strip_tac
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def, nenv_rel_nsSing]
QED

Resume compile_evaluate_lemma[Dexn]:
  gvs [full_evaluate_def, compile_dec_def, AllCaseEqs()]
  \\ qexistsl_tac [‘0’,‘fr’]
  \\ ‘t.next_exn_stamp = s.next_exn_stamp’ by gvs [state_rel_def]
  \\ simp [full_evaluate_def, nenv_rel_nsEmpty, state_rel_stamps]
QED

Resume compile_evaluate_lemma[Dopen]:
  gvs [full_evaluate_def, compile_dec_def, AllCaseEqs()]
  \\ drule_all env_rel_open_dec_env \\ strip_tac
  \\ qexistsl_tac [‘0’,‘fr’] \\ simp [full_evaluate_def]
QED

Resume compile_evaluate_lemma[Dmod]:
  gvs [full_evaluate_def, compile_dec_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ qexistsl_tac [‘ck’,‘fr1’] \\ gvs [full_evaluate_def]
  >~ [‘Rerr err’] >- (Cases_on ‘err’ \\ gvs [])
  \\ drule nenv_rel_nsLift \\ simp []
QED

Resume compile_evaluate_lemma[Dlocal]:
  gvs [full_evaluate_def, compile_dec_def, AllCaseEqs()]
  \\ last_x_assum drule_all \\ strip_tac
  >~ [‘_ = (_,Rerr err)’] >- (
    qexistsl_tac [‘ck’,‘fr1’] \\ simp []
    \\ Cases_on ‘err’ \\ gvs [])
  \\ ‘env_rel fr1 pe env env2’ by metis_tac [env_rel_SUBMAP]
  \\ drule_all env_rel_extend_dec_env \\ strip_tac
  \\ first_x_assum drule_all \\ strip_tac
  \\ qpat_assum ‘evaluate_decs (t with clock := _) env2 _ = _’
       (mp_tac o MATCH_MP lift_decs)
  \\ simp [] \\ disch_then (qspec_then ‘ck'’ assume_tac)
  \\ qexistsl_tac [‘ck + ck'’,‘fr1'’] \\ gvs []
  \\ metis_tac [SUBMAP_TRANS]
QED

Finalise compile_evaluate_lemma;

Theorem exp_sim_F:
  exp_sim F (:'ffi)
Proof
  rw [exp_sim_def]
  \\ drule (CONJUNCT1 (SIMP_RULE std_ss []
                         (Q.INST [‘H’ |-> ‘F’] compile_evaluate_lemma)))
  \\ disch_then drule_all \\ simp []
QED

(* the simulation for evaluate, evaluate_match and evaluate_decs *)
Theorem compile_evaluate =
  MP compile_evaluate_lemma (DISCH “H:bool” exp_sim_F);

(* ------------------------------------------------------------------ *
   Semantics
 * ------------------------------------------------------------------ *)

(* the eval state of the compiled program: EvalPending becomes EvalDecs,
   where the declarations are compiled by inc_compile_decs and C is the
   compiler minus that step *)
(* a variant of semantics_determ_clock_extra where the results of p' only
   need to agree with those of p on the ffi and on aborts *)
Theorem semantics_determ_clock_extra_rel[local]:
  ¬semantics_determ (s:'ffi evalSem$state) env p Fail ∧
  (∀k ffi r.
     evaluate_prog_with_clock s env k p = (ffi,r) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
     ∃ck r'.
       evaluate_prog_with_clock (s':'ffi evalSem$state) env' (k + ck) p' =
         (ffi,r') ∧
       ∀a. r' = Rerr (Rabort a) ⇔ r = Rerr (Rabort a)) ⇒
  semantics_determ s' env' p' = semantics_determ s env p
Proof
  strip_tac
  \\ ‘∀b. semantics_determ s env p b ⇒ semantics_determ s' env' p' b’
    suffices_by (
      rw [FUN_EQ_THM]
      \\ eq_tac
      >- (
        strip_tac
        \\ qspecl_then [‘s’,‘env’,‘p’] strip_assume_tac semantics_determ_total
        \\ metis_tac [semantics_determ_deterministic])
      \\ metis_tac [])
  \\ ‘∀k. SND (evaluate_prog_with_clock s env k p) ≠ Rerr (Rabort Rtype_error)’
    by (CCONTR_TAC \\ gvs [semantics_determ_def] \\ metis_tac [])
  \\ Cases
  >~ [‘semantics_determ _ _ _ Fail ⇒ _’] >- gvs []
  >~ [‘Terminate’] >- (
    rw [semantics_determ_def]
    \\ qpat_x_assum ‘∀k ffi r. _ ⇒ _’ drule \\ simp [] \\ strip_tac
    \\ qexists_tac ‘k + ck’ \\ simp []
    \\ ‘(∃a. r = Rerr (Rabort a) ∧ r' = r) ∨
        ((∀a. r ≠ Rerr (Rabort a)) ∧ (∀a. r' ≠ Rerr (Rabort a)))’
      by metis_tac []
    \\ gvs []
    \\ every_case_tac \\ gvs [])
  \\ rw [semantics_determ_def]
  >- (
    qpat_x_assum ‘∀k. ∃ffi. _’ (qspec_then ‘k’ strip_assume_tac)
    \\ qpat_x_assum ‘∀k ffi r. _ ⇒ _’ drule \\ simp [] \\ strip_tac
    \\ gvs [evaluate_prog_with_clock_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ CCONTR_TAC
    \\ qpat_x_assum ‘evaluate_decs (s' with clock := k) _ _ = _’ assume_tac
    \\ drule_then (qspec_then ‘ck’ mp_tac) evaluate_decs_add_to_clock
    \\ simp [] \\ metis_tac [])
  \\ irule lprefix_lub_new_chain
  \\ qpat_assum ‘lprefix_lub _ _’ $ irule_at Any
  \\ conj_tac >- simp [evaluate_prog_io_events_chain]
  \\ irule IMP_equiv_lprefix_chain
  \\ simp [evaluate_prog_io_events_chain, lprefix_rel_def, PULL_EXISTS]
  \\ conj_tac \\ gen_tac
  \\ Cases_on ‘evaluate_prog_with_clock s env k p’
  \\ qpat_x_assum ‘∀k ffi r. _ ⇒ _’ drule
  \\ (impl_tac >- metis_tac [SND])
  \\ strip_tac
  >- (qexists_tac ‘k + ck’ \\ simp [])
  \\ qexists_tac ‘k’
  \\ mp_tac (Q.SPECL [‘k’,‘k + ck’,‘s'’,‘env'’,‘p'’] evaluate_decs_ffi_mono_clock)
  \\ gvs [evaluate_prog_with_clock_def, LPREFIX_fromList, ELIM_UNCURRY,
          from_toList]
QED

Theorem check_exp_constructors_prelude[local]:
  check_exp_constructors envc (Con NONE [Fun «x» init_body; Fun «x» eval_body])
Proof
  simp [check_exp_constructors_def, init_body_def, eval_body_def,
        eval_fail_def, do_con_check_def]
QED

(* the prelude allocates its three references and binds $init and $eval
   to closures over an environment pe in which the references are
   visible *)
Theorem evaluate_prelude[local]:
  ∃pe.
    (∀c. evaluate_decs ((t:'ffi evalSem$state) with clock := c) env [prelude] =
           (t with <| clock := c;
                      refs := t.refs ++ [Refv (Litv (IntLit 1));
                                         Refv (Litv (IntLit 0));
                                         Refv (Litv (IntLit 0))] |>,
            Rval <| v := nsBind «$eval» (Closure pe «x» eval_body)
                           (nsBind «$init» (Closure pe «x» init_body) nsEmpty);
                    c := nsEmpty |>)) ∧
    nsLookup pe.v (Short «pending») = SOME (Loc T (LENGTH t.refs)) ∧
    nsLookup pe.v (Short «state») = SOME (Loc T (LENGTH t.refs + 1)) ∧
    nsLookup pe.v (Short «compiler») = SOME (Loc T (LENGTH t.refs + 2))
Proof
  simp [prelude_def, full_evaluate_def, do_app_def, store_alloc_def,
        pat_bindings_def, pmatch_def, nsOptBind_def, combine_dec_result_def,
        extend_dec_env_def, do_con_check_def, build_conv_def,
        check_exp_constructors_def, check_exp_constructors_prelude]
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
  \\ simp [PULL_EXISTS]
QED

(* after the prelude, the environment of the compiled program is related
   to the empty value environment of the input program *)
Theorem env_rel_prelude[local]:
  env.v = nsEmpty ⇒
  env_rel fr pe env
    (extend_dec_env
       <| v := nsBind «$eval» (Closure pe «x» eval_body)
                 (nsBind «$init» (Closure pe «x» init_body) nsEmpty);
          c := nsEmpty |> env)
Proof
  rw [env_rel_def, extend_dec_env_def, ns_rel_def]
  >- (
    Cases_on ‘p’
    \\ simp [namespaceTheory.nsLookupMod_def, namespaceTheory.nsBind_def,
             namespaceTheory.nsEmpty_def])
  \\ Cases_on ‘id’
  \\ gvs [namespaceTheory.nsLookup_def, namespaceTheory.nsBind_def,
          namespaceTheory.nsEmpty_def, AllCaseEqs()]
QED

Definition init_es_def:
  init_es C (EvalPending r) = EvalDecs (adjust_decs inc_compile_decs C r) ∧
  init_es C (EvalDecs r) = EvalDecs r ∧
  init_es C (EvalRun r) = EvalRun r ∧
  init_es C (EvalOracle x) = EvalOracle x
End

Definition init_factor_st_def:
  init_factor_st C (s:'ffi evalSem$state) ⇔
    case s.eval_state of
    | NONE => T
    | SOME (EvalPending r) => decs_factor inc_compile_decs C r
    | SOME _ => F
End

(* the compiled program starts with the prelude, after which the
   simulation compile_evaluate applies *)
(* the input program and the compiled program after the prelude *)
Theorem state_rel_prelude[local]:
  init_factor_st C (s:'ffi evalSem$state) ∧ s.refs = [] ∧
  nsLookup pe.v (Short «pending») = SOME (Loc T 0) ∧
  nsLookup pe.v (Short «state») = SOME (Loc T 1) ∧
  nsLookup pe.v (Short «compiler») = SOME (Loc T 2) ⇒
  state_rel (s.eval_state ≠ NONE)
    (OPTION_MAP (init_es C) s.eval_state,
     prelude_vals pe [Refv (Litv (IntLit 1)); Refv (Litv (IntLit 0));
                      Refv (Litv (IntLit 0))])
    C FEMPTY pe s
    (s with <| eval_state updated_by OPTION_MAP (init_es C);
               refs := [Refv (Litv (IntLit 1)); Refv (Litv (IntLit 0));
                        Refv (Litv (IntLit 0))] |>)
Proof
  simp [state_rel_def, refs_rel_def, prelude_ok_def, prelude_loc_def]
  \\ strip_tac
  \\ conj_tac >- (rw [] \\ simp [])
  \\ Cases_on ‘s.eval_state’ \\ simp []
  \\ gvs [init_factor_st_def]
  \\ Cases_on ‘x’ \\ gvs [eval_rel_def, init_es_def, prelude_loc_def]
QED

Theorem compile_semantics:
  init_factor_st C (s:'ffi evalSem$state) ∧ env.v = nsEmpty ∧ s.refs = [] ∧
  ¬semantics_determ s env prog Fail ∧
  semantics_determ s env prog outcome ⇒
  semantics_determ (s with eval_state updated_by OPTION_MAP (init_es C))
    env (compile_decs prog) outcome
Proof
  strip_tac
  \\ ‘semantics_determ (s with eval_state updated_by OPTION_MAP (init_es C))
        env (compile_decs prog) = semantics_determ s env prog’
    suffices_by simp []
  \\ irule semantics_determ_clock_extra_rel
  \\ rw [evaluate_prog_with_clock_def]
  \\ Cases_on ‘evaluate_decs (s with clock := k) env prog’ \\ gvs []
  \\ rename1 ‘evaluate_decs _ env prog = (st,r)’
  \\ qspecl_then [‘s with eval_state updated_by OPTION_MAP (init_es C)’,‘env’]
       strip_assume_tac (GEN_ALL evaluate_prelude)
  \\ qabbrev_tac ‘t1 = s with <| clock := k;
                                 eval_state updated_by OPTION_MAP (init_es C);
                                 refs := [Refv (Litv (IntLit 1));
                                          Refv (Litv (IntLit 0));
                                          Refv (Litv (IntLit 0))] |>’
  \\ ‘state_rel (s.eval_state ≠ NONE) (t1.eval_state,prelude_vals pe t1.refs)
        C FEMPTY pe (s with clock := k) t1’
    by (mp_tac (Q.INST [‘s’ |-> ‘s with clock := k’] state_rel_prelude)
        \\ gvs [Abbr ‘t1’, init_factor_st_def])
  \\ drule_then (drule_then drule) (CONJUNCT2 (CONJUNCT2 compile_evaluate))
  \\ disch_then (qspec_then ‘extend_dec_env
       <| v := nsBind «$eval» (Closure pe «x» eval_body)
                 (nsBind «$init» (Closure pe «x» init_body) nsEmpty);
          c := nsEmpty |> env’ mp_tac)
  \\ simp [env_rel_prelude]
  \\ strip_tac
  \\ qexists_tac ‘ck’
  \\ simp [compile_decs_def, Once evaluate_decs_cons]
  \\ ‘s with <| clock := ck + k;
                refs := [Refv (Litv (IntLit 1)); Refv (Litv (IntLit 0));
                         Refv (Litv (IntLit 0))];
                eval_state updated_by OPTION_MAP (init_es C) |> =
      t1 with clock := ck + t1.clock’
    by simp [Abbr ‘t1’, evalSemTheory.state_component_equality]
  \\ simp []
  \\ ‘t1'.ffi = st.ffi’ by gvs [state_rel_def]
  \\ simp []
  \\ Cases_on ‘r’ \\ Cases_on ‘r1’ \\ gvs [combine_dec_result_def]
  \\ rename1 ‘res_rel _ _ (Rerr e1) (Rerr e2)’
  \\ Cases_on ‘e1’ \\ Cases_on ‘e2’ \\ gvs []
QED
