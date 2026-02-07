(*
  Correctness proof for source_to_flat
*)
Theory source_to_flatProof
Ancestors
  source_to_flat flatProps namespaceProps semantics
  semanticPrimitivesProps ffi[qualified] lprefix_lub[qualified]
  backend_common[qualified] misc[qualified] backendProps
  source_evalProof
Ancestors[ignore_grammar]
  semanticPrimitives flatLang flatSem
  flat_elimProof[qualified] flat_patternProof[qualified]
Libs
  preamble experimentalLib

(* Set up ML bindings *)
open preamble semanticsTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     source_to_flatTheory flatLangTheory flatSemTheory flatPropsTheory
     backendPropsTheory experimentalLib source_evalProofTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj", "getOpClass_def"]
val _ = set_trace "BasicProvers.var_eq_old" 1

Theorem compile_exps_length[local]:
  LENGTH (compile_exps t m es) = LENGTH es
Proof
  induct_on `es` >>
  rw [compile_exp_def]
QED

Theorem mapi_map:
   !f g l. MAPi f (MAP g l) = MAPi (\i x. f i (g x)) l
Proof
  Induct_on `l` >>
  rw [combinTheory.o_DEF]
QED

Theorem fst_lem[local]:
  (λ(p1,p1',p2). p1) = FST
Proof
  rw [FUN_EQ_THM] >>
  pairarg_tac >>
  rw []
QED

Theorem funion_submap[local]:
  FUNION x y SUBMAP z ∧ DISJOINT (FDOM x) (FDOM y) ⇒ y SUBMAP z
Proof
  rw [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, FUNION_DEF] >>
  metis_tac []
QED

Theorem flookup_funion_submap[local]:
  (x ⊌ y) SUBMAP z ∧
   FLOOKUP (x ⊌ y) k = SOME v
   ⇒
   FLOOKUP z k = SOME v
Proof
  rw [SUBMAP_DEF, FLOOKUP_DEF] >>
  metis_tac []
QED

Theorem FILTER_MAPi_ID:
   ∀ls f. FILTER P (MAPi f ls) = MAPi f ls ⇔
   (∀n. n < LENGTH ls ⇒ P (f n (EL n ls)))
Proof
  Induct \\ reverse(rw[])
  >- (
    qmatch_goalsub_abbrev_tac`a ⇔ b`
    \\ `¬a`
    by (
      simp[Abbr`a`]
      \\ disch_then(mp_tac o Q.AP_TERM`LENGTH`)
      \\ rw[]
      \\ specl_args_of_then``FILTER``LENGTH_FILTER_LEQ mp_tac
      \\ simp[] )
    \\ simp[Abbr`b`]
    \\ qexists_tac`0`
    \\ simp[] )
  \\ simp[Once FORALL_NUM, SimpRHS]
QED

(* -- *)

(* value relation *)


(* bind locals with an arbitrary trace *)
Definition bind_locals_def:
  bind_locals ts locals comp_map =
    nsBindList (MAP2 (\t x. (x, Local t x)) ts locals) comp_map
End

Theorem nsAppend_bind_locals[local]:
  ∀funs.
  nsAppend (alist_to_ns (MAP (λx. (x,Local t x)) (MAP FST funs))) (bind_locals ts locals comp_map) =
  bind_locals (REPLICATE (LENGTH funs) t ++ ts) (MAP FST funs ++ locals) comp_map
Proof
  Induct_on`funs`>>fs[FORALL_PROD,bind_locals_def,namespaceTheory.nsBindList_def]
QED

Theorem nsBindList_pat_tups_bind_locals[local]:
  ∀ls.
  ∃tss.
  nsBindList (pat_tups t ls) (bind_locals ts locals comp_map) =
  bind_locals (tss ++ ts) (ls ++ locals) comp_map ∧
  LENGTH tss = LENGTH ls
Proof
  Induct>>rw[pat_tups_def,namespaceTheory.nsBindList_def,bind_locals_def]>>
  qexists_tac`(t § (LENGTH ls + 1))::tss`>>simp[]
QED

Datatype:
  global_env =
    <| v : flatSem$v option list; c : (ctor_id # type_id) # num |-> stamp;
        tys : num |-> (ctor_id # num) list |>
End

Theorem submap_distinct_fupdate_flookup:
  x ∉ FDOM f ==>
  (f |+ (x,y) ⊑ g <=> FLOOKUP g x = SOME y /\ f ⊑ g)
Proof
  rw [SUBMAP_FUPDATE, FLOOKUP_DEF]
  \\ EQ_TAC \\ rw []
  \\ fs [SUBMAP_DEF]
  \\ fs [DOMSUB_FAPPLY_THM]
  \\ metis_tac []
QED

Theorem submap_fupdate_flookup:
  (f |+ (x,y) ⊑ g <=> FLOOKUP g x = SOME y /\ f \\ x ⊑ g)
Proof
  rw [SUBMAP_FUPDATE, FLOOKUP_DEF]
  \\ EQ_TAC \\ rw []
  \\ fs [SUBMAP_DEF]
  \\ fs [DOMSUB_FAPPLY_THM]
QED

Definition has_bools_def:
  has_bools genv ⇔
    FLOOKUP genv ((true_tag, SOME bool_id), 0n) = SOME (TypeStamp «True» bool_type_num) ∧
    FLOOKUP genv ((false_tag, SOME bool_id), 0n) = SOME (TypeStamp «False» bool_type_num)
End

Definition has_lists_def:
  has_lists genv ⇔
    FLOOKUP genv ((cons_tag, SOME list_id), 2n) = SOME (TypeStamp «::» list_type_num) ∧
    FLOOKUP genv ((nil_tag, SOME list_id), 0n) = SOME (TypeStamp «[]» list_type_num)
End

Definition has_exns_def:
  has_exns genv ⇔
    FLOOKUP genv ((div_tag, NONE), 0n) = SOME div_stamp ∧
    FLOOKUP genv ((chr_tag, NONE), 0n) = SOME chr_stamp ∧
    FLOOKUP genv ((subscript_tag, NONE), 0n) = SOME subscript_stamp ∧
    FLOOKUP genv ((bind_tag, NONE), 0n) = SOME bind_stamp
End

Definition genv_c_ok_def:
  genv_c_ok genv_c ⇔
    has_bools genv_c ∧
    has_exns genv_c ∧
    has_lists genv_c ∧
    (!cn1 cn2 l1 l2 stamp1 stamp2.
      FLOOKUP genv_c (cn1,l1) = SOME stamp1 ∧
      FLOOKUP genv_c (cn2,l2) = SOME stamp2
      ⇒
      (ctor_same_type (SOME stamp1) (SOME stamp2) ⇔ ctor_same_type (SOME cn1) (SOME cn2))) ∧
    (!cn1 cn2 l1 l2 stamp.
      FLOOKUP genv_c (cn1,l1) = SOME stamp ∧
      FLOOKUP genv_c (cn2,l2) = SOME stamp
      ⇒
      cn1 = cn2 ∧ l1 = l2)
End

Definition genv_c_tys_ok_def:
  genv_c_tys_ok genv_c genv_tys ⇔
  !cn ty_id arity.
    ((cn, SOME ty_id), arity) IN FDOM genv_c ⇒
      ?ctors. FLOOKUP genv_tys ty_id = SOME ctors ∧
      MEM (cn, arity) ctors
End

Inductive v_rel:
  (!genv lit.
    v_rel genv ((Litv lit):semanticPrimitives$v) ((Litv lit):flatSem$v)) ∧
  (!genv cn cn' vs vs'.
    LIST_REL (v_rel genv) vs vs' ∧
    FLOOKUP genv.c (cn', LENGTH vs) = SOME cn
    ⇒
    v_rel genv (Conv (SOME cn) vs) (Conv (SOME cn') vs')) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    v_rel genv (Conv NONE vs) (Conv NONE vs')) ∧
  (!genv comp_map env env_v_local x e env_v_local' t ts.
    env_rel genv env_v_local env_v_local'.v ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local'.v)) env ∧
    LENGTH ts = LENGTH env_v_local'.v + 1
    ⇒
    v_rel genv
      (Closure (env with v := nsAppend env_v_local env.v) x e)
      (Closure env_v_local' x
        (compile_exp t
          (comp_map with v := bind_locals ts (x::MAP FST env_v_local'.v) comp_map.v)
          e))) ∧
  (* For expression level let recs *)
  (!genv comp_map env env_v_local funs x env_v_local' t ts.
    env_rel genv env_v_local env_v_local'.v ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local'.v)) env ∧
    LENGTH ts = LENGTH funs + LENGTH env_v_local'.v
    ⇒
    v_rel genv
      (Recclosure (env with v := nsAppend env_v_local env.v) funs x)
      (Recclosure env_v_local'
        (compile_funs t
          (comp_map with v := bind_locals ts (MAP FST funs++MAP FST env_v_local'.v) comp_map.v) funs)
          x)) ∧
  (* For top-level let recs *)
  (!genv comp_map env funs flat_env x y e new_vars t1 t2.
    MAP FST new_vars = MAP FST (REVERSE funs) ∧
    global_env_inv genv comp_map {} env ∧
    flat_env.v = [] ∧
    find_recfun x funs = SOME (y, e) ∧
    (* A syntactic way of relating the recursive function environment, rather
     * than saying that they build v_rel related environments, which looks to
     * require step-indexing *)
    (!x. x ∈ set (MAP FST funs) ⇒
       ?n y e t1 t2 t3.
         ALOOKUP new_vars x = SOME (Glob t1 n) ∧
         n < LENGTH genv.v ∧
         find_recfun x funs = SOME (y,e) ∧
         EL n genv.v =
           SOME (Closure flat_env y
                  (compile_exp t2 (comp_map with v := nsBindList ((y, Local t3 y)::new_vars) comp_map.v) e)))
    ⇒
    v_rel genv
      (Recclosure env funs x)
      (Closure flat_env y
        (compile_exp t1
          (comp_map with v := nsBindList ((y, Local t2 y)::new_vars) comp_map.v)
          e))) ∧
  (!genv loc b.
    v_rel genv (Loc b loc) (Loc b (loc + 1))) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    v_rel genv (Vectorv vs) (Vectorv vs')) ∧
  (!genv.
    env_rel genv nsEmpty []) ∧
  (!genv x v env env' v'.
    env_rel genv env env' ∧
    v_rel genv v v'
    ⇒
    env_rel genv (nsBind x v env) ((x,v')::env')) ∧
  (!genv comp_map shadowers env.
    (!x v.
       x ∉ IMAGE Short shadowers ∧
       nsLookup env.v x = SOME v
       ⇒
       ?n v' t.
         nsLookup comp_map.v x = SOME (Glob t n) ∧
         n < LENGTH genv.v ∧
         EL n genv.v = SOME v' ∧
         v_rel genv v v') ∧
    (!x arity stamp.
      nsLookup env.c x = SOME (arity, stamp) ⇒
      ∃cn ty_gp. nsLookup comp_map.c x = SOME (cn, ty_gp) ∧
        FLOOKUP genv.c ((cn, OPTION_MAP FST ty_gp), arity) = SOME stamp ∧
        (! ty_id ctors. ty_gp = SOME (ty_id, ctors) ⇒
            FLOOKUP genv.tys ty_id = SOME ctors)
    )
    ⇒
    global_env_inv genv comp_map shadowers env)
End

(*
Theorem v_rel_eqns:
   (!genv l v.
    v_rel genv (Litv l) v ⇔
      (v = Litv l)) ∧
   (!genv vs v.
    v_rel genv (Conv cn vs) v ⇔
      ?vs' cn'.
        LIST_REL (v_rel genv) vs vs' ∧
        v = Conv cn' vs' ∧
        case cn of
        | NONE => cn' = NONE
        | SOME cn =>
          ?cn2. cn' = SOME cn2 ∧ FLOOKUP genv.c (cn2, LENGTH vs) = SOME cn) ∧
   (!genv l v b.
    v_rel genv (Loc b l) v ⇔
      (v = Loc b l)) ∧
   (!genv vs v.
    v_rel genv (Vectorv vs) v ⇔
      ?vs'. LIST_REL (v_rel genv) vs vs' ∧ (v = Vectorv vs')) ∧
   (!genv fp v.
      v_rel genv (FP_WordTree fp) v <=>
      v = Litv (Word64 (compress_word fp))) /\
   (! genv fp v cn.
      v_rel genv (FP_BoolTree fp) v <=>
      FLOOKUP (genv.c) (((if (compress_bool fp) then true_tag else false_tag),SOME bool_id), 0) =
        SOME (TypeStamp (if (compress_bool fp) then «True» else «False») bool_type_num) /\
      v = Boolv (compress_bool fp)) /\
   (!genv env'.
    env_rel genv nsEmpty env' ⇔
      env' = []) ∧
   (!genv x v env env'.
    env_rel genv (nsBind x v env) env' ⇔
      ?v' env''. v_rel genv v v' ∧ env_rel genv env env'' ∧ env' = ((x,v')::env'')) ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env ⇔
      (!x v.
       x ∉ IMAGE Short shadowers ∧
       nsLookup env.v x = SOME v
       ⇒
       ?n v' t.
         nsLookup comp_map.v x = SOME (Glob t n) ∧
         n < LENGTH genv.v ∧
         EL n genv.v = SOME v' ∧
         v_rel genv v v') ∧
      (!x arity stamp.
        nsLookup env.c x = SOME (arity, stamp) ⇒
        ∃cn. nsLookup comp_map.c x = SOME cn ∧
          FLOOKUP genv.c (cn,arity) = SOME stamp))
Proof
  srw_tac[][semanticPrimitivesTheory.Boolv_def,flatSemTheory.Boolv_def] >>
  srw_tac[][Once v_rel_cases] >>
  srw_tac[][Q.SPECL[`genv`,`nsEmpty`](CONJUNCT1(CONJUNCT2 v_rel_cases))] >>
  srw_tac[][flatSemTheory.Boolv_def, semanticPrimitivesTheory.Boolv_def] >>
  every_case_tac >>
  fs [genv_c_ok_def, has_bools_def] >>
  TRY eq_tac >>
  rw [] >>
  metis_tac []
*)

Theorem v_rel_eqns[local] =
  [``v_rel genv (Litv l) v``, ``v_rel genv (Conv cn vs) v``,
    ``v_rel genv (Loc b l) v``, ``v_rel genv (Vectorv vs) v``,
    ``env_rel genv nsEmpty env'``, ``env_rel genv (nsBind x v env) env'``,
    ``v_rel genv (Env e id) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL
  |> LIST_CONJ

Theorem v_rel_more_eqns =
  [``v_rel genv (Closure env nm exp) v``,
    ``v_rel genv (Recclosure env funs x) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL
  |> LIST_CONJ
  |> CONJ v_rel_eqns

Theorem v_rel_global_eqn = SIMP_CONV (srw_ss ()) [Once v_rel_cases]
  ``global_env_inv genv comp_map shadowers env``

Theorem env_rel_LIST_REL:
  !xs ys. env_rel genv (alist_to_ns xs) ys <=>
  LIST_REL (\x y. FST x = FST y /\ v_rel genv (SND x) (SND y)) xs ys
Proof
  Induct \\ simp [Once v_rel_cases]
  \\ simp [FORALL_PROD, PULL_EXISTS]
  \\ rw []
  \\ EQ_TAC
  \\ simp [PULL_EXISTS, FORALL_PROD]
QED

Theorem env_rel_dom[local]:
  !genv env env'.
    env_rel genv env env'
    ⇒
    ?l. env = alist_to_ns l ∧ MAP FST l = MAP FST env'
Proof
  induct_on `env'` >>
  simp [Once v_rel_cases] >>
  rw [] >>
  first_x_assum drule >>
  rw [] >>
  rw_tac list_ss [GSYM alist_to_ns_cons] >>
  prove_tac [MAP, FST]
QED

Theorem env_rel_lookup[local]:
  !genv env x v env'.
    ALOOKUP env x = SOME v ∧
    env_rel genv (alist_to_ns env) env'
    ⇒
    ?v'.
      v_rel genv v v' ∧
      ALOOKUP env' x = SOME v'
Proof
  induct_on `env'` >>
  simp [] >>
  simp [Once v_rel_cases] >>
  rw [] >>
  rw [] >>
  fs [] >>
  rw [] >>
  Cases_on `env` >>
  TRY (PairCases_on `h`) >>
  fs [alist_to_ns_cons] >>
  rw [] >>
  metis_tac []
QED

Theorem env_rel_append[local]:
  !genv env1 env2 env1' env2'.
    env_rel genv env1 env1' ∧
    env_rel genv env2 env2'
    ⇒
    env_rel genv (nsAppend env1 env2) (env1'++env2')
Proof
  induct_on `env1'` >>
  rw []
  >- (
    `env1 = nsEmpty` by fs [Once v_rel_cases] >>
    rw []) >>
  qpat_x_assum `env_rel _ _ (_::_)` mp_tac >>
  simp [Once v_rel_cases] >>
  rw [] >>
  rw [] >>
  simp [Once v_rel_cases]
QED

Theorem env_rel_one[local]:
  env_rel genv (nsBind a b nsEmpty) xs <=>
  ?v. xs = [(a, v)] /\ v_rel genv b v
Proof
  simp [Once v_rel_cases]
  \\ Cases_on `xs` \\ simp []
  \\ simp [Once v_rel_cases]
  \\ metis_tac []
QED

Theorem env_rel_bind_one = env_rel_append
  |> Q.SPECL [`genv`, `nsBind a b nsEmpty`, `env2`, `[(c, d)]`]
  |> GEN_ALL
  |> SIMP_RULE (srw_ss ()) [env_rel_one]

Theorem env_rel_el[local]:
  !genv env env_i1.
    env_rel genv (alist_to_ns env) env_i1 ⇔
    LENGTH env = LENGTH env_i1 ∧
    !n. n < LENGTH env ⇒
        (FST (EL n env) = FST (EL n env_i1)) ∧
        v_rel genv (SND (EL n env)) (SND (EL n env_i1))
Proof
  induct_on `env` >>
  srw_tac[][v_rel_eqns] >>
  PairCases_on `h` >>
  srw_tac[][v_rel_eqns] >>
  eq_tac >>
  srw_tac[][] >>
  srw_tac[][]
  >- (cases_on `n` >>
      full_simp_tac(srw_ss())[])
  >- (cases_on `n` >>
      full_simp_tac(srw_ss())[])
  >- (cases_on `env_i1` >>
      full_simp_tac(srw_ss())[] >>
      FIRST_ASSUM (qspecl_then [`0`] mp_tac) >>
      SIMP_TAC (srw_ss()) [] >>
      srw_tac[][] >>
      qexists_tac `SND h` >>
      srw_tac[][] >>
      FIRST_X_ASSUM (qspecl_then [`SUC n`] mp_tac) >>
      srw_tac[][])
QED

Definition subglobals_def:
  subglobals g1 g2 ⇔
    LENGTH g1 ≤ LENGTH g2 ∧
    !n. n < LENGTH g1 ∧ IS_SOME (EL n g1) ⇒ EL n g1 = EL n g2
End

Theorem subglobals_refl[local]:
  !g. subglobals g g
Proof
  rw [subglobals_def]
QED

Theorem subglobals_trans[local]:
  !g1 g2 g3. subglobals g1 g2 ∧ subglobals g2 g3 ⇒ subglobals g1 g3
Proof
  rw [subglobals_def] >>
  res_tac >>
  fs []
QED

Theorem subglobals_refl_append[local]:
  !g1 g2 g3.
    subglobals (g1 ++ g2) (g1 ++ g3) = subglobals g2 g3 ∧
    (LENGTH g2 = LENGTH g3 ⇒ subglobals (g2 ++ g1) (g3 ++ g1) = subglobals g2 g3)
Proof
  rw [subglobals_def] >>
  eq_tac >>
  rw []
  >- (
    first_x_assum (qspec_then `n + LENGTH (g1:'a option list)` mp_tac) >>
    rw [EL_APPEND_EQN])
  >- (
    first_x_assum (qspec_then `n - LENGTH (g1:'a option list)` mp_tac) >>
    rw [EL_APPEND_EQN] >>
    fs [EL_APPEND_EQN])
  >- (
    first_x_assum (qspec_then `n` mp_tac) >>
    rw [EL_APPEND_EQN])
  >- (
    Cases_on `n < LENGTH g3` >>
    fs [EL_APPEND_EQN] >>
    rfs [] >>
    fs [])
QED

Theorem v_rel_weakening[local]:
  (!genv v v'.
    v_rel genv v v'
    ⇒
    !genv'. genv.c = genv'.c ∧ genv.tys = genv'.tys ∧
        subglobals genv.v genv'.v ⇒ v_rel genv' v v') ∧
   (!genv env env'.
    env_rel genv env env'
    ⇒
    !genv'. genv.c = genv'.c ∧ genv.tys = genv'.tys ∧
        subglobals genv.v genv'.v ⇒ env_rel genv' env env') ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env
    ⇒
    !genv'. genv.c = genv'.c ∧ genv.tys = genv'.tys ∧
        subglobals genv.v genv'.v ⇒ global_env_inv genv' comp_map shadowers env)
Proof
  ho_match_mp_tac v_rel_ind >>
  srw_tac[][v_rel_eqns, subglobals_def] >> fs[]
  >- fs [LIST_REL_EL_EQN]
  >- fs [LIST_REL_EL_EQN]
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `env`, `env'`, `t`, `ts`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `env`, `env'`, `t`,`ts`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `new_vars`, `t1`, `t2`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns, EL_APPEND1] >>
      srw_tac[][] >>
      res_tac >>
      qexists_tac `n` >>
      srw_tac[][EL_APPEND1] >>
      map_every qexists_tac [`t2`,`t3`] >>
      rw [] >>
      metis_tac [IS_SOME_DEF])
  >- fs [LIST_REL_EL_EQN]
  >- (
    rw [v_rel_global_eqn] >>
    res_tac >>
    rw [] >>
    res_tac >>
    rveq >> fs [] >>
    rveq >> fs [] >>
    rfs []
  )
QED

Theorem v_rel_weakening2[local]:
   (!genv v v'.
    v_rel genv v v'
    ⇒
    ∀gc. genv.c ⊑ genv'.c ∧ genv.tys ⊑ genv'.tys ∧ genv.v = genv'.v ⇒
    v_rel genv' v v') ∧
   (!genv env env'.
    env_rel genv env env'
    ⇒
    ∀gc. genv.c ⊑ genv'.c ∧ genv.tys ⊑ genv'.tys ∧ genv.v = genv'.v ⇒
    env_rel genv' env env') ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env
    ⇒
    ∀gc. genv.c ⊑ genv'.c ∧ genv.tys ⊑ genv'.tys ∧ genv.v = genv'.v ⇒
    global_env_inv genv' comp_map shadowers env)
Proof
  ho_match_mp_tac v_rel_ind >>
  srw_tac[][v_rel_eqns] >>
  fs [SUBMAP_FLOOKUP_EQN]
  >- fs [LIST_REL_EL_EQN]
  >- fs [LIST_REL_EL_EQN]
  >- (simp [Once v_rel_cases] >> metis_tac [])
  >- (simp [Once v_rel_cases] >> metis_tac [])
  >- (simp [Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`comp_map`, `new_vars`, `t1`, `t2`] >>
      simp []
  )
  >- fs [LIST_REL_EL_EQN]
  >- (
    fs [v_rel_global_eqn] >>
    rw [] >>
    res_tac >>
    fs [] >>
    metis_tac []
  )
QED

Theorem drestrict_lem[local]:
  f1 SUBMAP f2 ⇒ DRESTRICT f2 (COMPL (FDOM f1)) ⊌ f1 = f2
Proof
  rw [FLOOKUP_EXT, FUN_EQ_THM, FLOOKUP_FUNION] >>
  every_case_tac >>
  fs [FLOOKUP_DRESTRICT, SUBMAP_DEF,AllCaseEqs(),FLOOKUP_DEF]
QED

Theorem v_rel_weak:
   !genv v v' genv'.
   v_rel genv v v' ∧
   genv.c ⊑ genv'.c ∧
   genv.tys ⊑ genv'.tys ∧
   subglobals genv.v genv'.v
   ⇒
   v_rel genv' v v'
Proof
  rw [] >>
  FIRST (map drule (CONJUNCTS v_rel_weakening)) >>
  disch_then (qspec_then `genv with v := genv'.v` mp_tac) >>
  rw [] >>
  FIRST (map drule (CONJUNCTS v_rel_weakening2)) >>
  disch_then irule >>
  simp []
QED

Theorem env_rel_weak:
   !genv env env' genv'.
   env_rel genv env env' ∧
   genv.c ⊑ genv'.c ∧
   genv.tys ⊑ genv'.tys ∧
   subglobals genv.v genv'.v
   ⇒
   env_rel genv' env env'
Proof
  rw [] >>
  FIRST (map drule (CONJUNCTS v_rel_weakening)) >>
  disch_then (qspec_then `genv with v := genv'.v` mp_tac) >>
  rw [] >>
  FIRST (map drule (CONJUNCTS v_rel_weakening2)) >>
  disch_then irule >>
  simp []
QED

Theorem global_env_inv_weak:
   !genv comp_map shadowers env genv'.
   global_env_inv genv comp_map shadowers env ∧
   genv.c ⊑ genv'.c ∧
   genv.tys ⊑ genv'.tys ∧
   subglobals genv.v genv'.v
   ⇒
   global_env_inv genv' comp_map shadowers env
Proof
  rw [] >>
  FIRST (map drule (CONJUNCTS v_rel_weakening)) >>
  disch_then (qspec_then `genv with v := genv'.v` mp_tac) >>
  rw [] >>
  FIRST (map drule (CONJUNCTS v_rel_weakening2)) >>
  disch_then irule >>
  simp []
QED

Inductive result_rel:
  (∀genv v v'.
    f genv v v'
    ⇒
    result_rel f genv (Rval v) (Rval v')) ∧
  (∀genv v v'.
    v_rel genv v v'
    ⇒
    result_rel f genv (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
  (!genv a.
    result_rel f genv (Rerr (Rabort a)) (Rerr (Rabort a)))
End

Theorem result_rel_eqns[local]:
  (!genv v r.
    result_rel f genv (Rval v) r ⇔
      ?v'. f genv v v' ∧ r = Rval v') ∧
   (!genv v r.
    result_rel f genv (Rerr (Rraise v)) r ⇔
      ?v'. v_rel genv v v' ∧ r = Rerr (Rraise v')) ∧
   (!genv v r a.
    result_rel f genv (Rerr (Rabort a)) r ⇔
      r = Rerr (Rabort a))
Proof
  srw_tac[][result_rel_cases] >>
  metis_tac []
QED

Inductive sv_rel:
  (!genv v v'.
    v_rel genv v v'
    ⇒
    sv_rel genv (Refv v) (Refv v')) ∧
  (!genv w.
    sv_rel genv (W8array w) (W8array w)) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    sv_rel genv (Varray vs) (Varray vs')) ∧
  (!genv m v v'.
    v_rel genv v v'
    ⇒
    sv_rel genv (Thunk m v) (Thunk m v'))
End

Theorem sv_rel_weak[local]:
  !genv sv sv' genv'.
   sv_rel genv sv sv' ∧
   genv.c ⊑ genv'.c ∧
   genv.tys ⊑ genv'.tys ∧
   subglobals genv.v genv'.v
   ⇒
   sv_rel genv' sv sv'
Proof
  srw_tac[][sv_rel_cases] >>
  metis_tac [v_rel_weak, LIST_REL_EL_EQN]
QED

Inductive s_rel:
  (!genv s s'.
    ~ NULL s'.refs ∧
    LIST_REL (sv_rel genv) s.refs (TL s'.refs) ∧
    s.clock = s'.clock ∧
    s.ffi = s'.ffi
    ⇒
    s_rel genv s s')
End

Inductive env_all_rel:
  (!genv map env_v_local env env' locals.
    (?l. env_v_local = alist_to_ns l ∧ MAP FST l = locals) ∧
    global_env_inv genv map (set locals) env ∧
    env_rel genv env_v_local env'
    ⇒
    env_all_rel genv map
      <| c := env.c; v := nsAppend env_v_local env.v |>
      <| v := env' |>
      locals)
End

Theorem env_all_rel_weak[local]:
  !genv map locals env env' genv'.
   env_all_rel genv map env env' locals ∧
   genv.c ⊑ genv'.c ∧
   genv.tys ⊑ genv'.tys ∧
   subglobals genv.v genv'.v
   ⇒
   env_all_rel genv' map env env' locals
Proof
  rw [env_all_rel_cases] >>
  imp_res_tac env_rel_weak >>
  imp_res_tac global_env_inv_weak >>
  MAP_EVERY qexists_tac [`alist_to_ns l`, `env''`, `env'''`] >>
  rw [] >>
  metis_tac [SUBMAP_FDOM_SUBSET, SUBSET_TRANS]
QED

Definition match_result_rel_def:
  (match_result_rel genv env' (Match env) (Match env_i1) =
     ?env''. env = env'' ++ env' ∧ env_rel genv (alist_to_ns env'') env_i1) ∧
   (match_result_rel genv env' No_match No_match = T) ∧
   (match_result_rel genv env' Match_type_error _ = T) ∧
   (match_result_rel genv env' _ _ = F)
End

Theorem match_result_rel_imp:
  match_result_rel genv env m1 m2 ==>
  (m1 = Match_type_error \/ (m1 = No_match /\ m2 = No_match)
    \/ (?env1 env2. m1 = Match env1 /\ m2 = Match env2))
Proof
  Cases_on `m1` \\ Cases_on `m2` \\ simp [match_result_rel_def]
QED

(* semantic functions respect relation *)

Theorem do_eq[local]:
  !genv. genv_c_ok genv.c ⇒
   (!v1 v2 r v1_i1 v2_i1.
    do_eq v1 v2 = r ∧
    v_rel genv v1 v1_i1 ∧
    v_rel genv v2 v2_i1
    ⇒
    do_eq v1_i1 v2_i1 = r) ∧
   (!vs1 vs2 r vs1_i1 vs2_i1.
    do_eq_list vs1 vs2 = r ∧
    LIST_REL (v_rel genv) vs1 vs1_i1 ∧
    LIST_REL (v_rel genv) vs2 vs2_i1
    ⇒
    do_eq_list vs1_i1 vs2_i1 = r)
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac semanticPrimitivesTheory.do_eq_ind >>
  rpt strip_tac >>
  fs [Boolv_def, semanticPrimitivesTheory.do_eq_def, flatSemTheory.do_eq_def, v_rel_more_eqns] >>
  rveq >> fs [] >>
  rpt (irule COND_CONG >> rpt strip_tac) >>
  imp_res_tac LIST_REL_LENGTH >>
  fs [flatSemTheory.ctor_same_type_def,
      semanticPrimitivesTheory.ctor_same_type_def] >>
  TRY every_case_tac >>
  gs[lit_same_type_def] >>
  metis_tac [SOME_11, genv_c_ok_def
    |> SIMP_RULE (srw_ss()) [semanticPrimitivesTheory.ctor_same_type_def]]
QED

Theorem genv_lookup_nil:
  genv_c_ok genv_c ==>
  (FLOOKUP genv_c cn = SOME (TypeStamp «[]» list_type_num)
  <=> cn = ((nil_tag, SOME list_id), 0))
Proof
  Cases_on `cn`
  \\ simp [genv_c_ok_def, has_lists_def]
  \\ metis_tac []
QED

Theorem genv_lookup_cons:
  genv_c_ok genv_c ==>
  (FLOOKUP genv_c cn = SOME (TypeStamp «::» list_type_num)
  <=> cn = ((cons_tag, SOME list_id), 2))
Proof
  Cases_on `cn`
  \\ simp [genv_c_ok_def, has_lists_def]
  \\ metis_tac []
QED

Theorem v_to_char_list[local]:
  !genv. genv_c_ok genv.c ⇒
   !v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_char_list v1 = SOME vs1
    ⇒
    v_to_char_list v2 = SOME vs1
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac semanticPrimitivesTheory.v_to_char_list_ind >>
  srw_tac[][semanticPrimitivesTheory.v_to_char_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_more_eqns, flatSemTheory.v_to_char_list_def] >>
  imp_res_tac genv_lookup_nil >>
  imp_res_tac genv_lookup_cons >>
  fs [] >>
  rw [flatSemTheory.v_to_char_list_def]
QED

Theorem v_to_list[local]:
  !genv. genv_c_ok genv.c ⇒
   !v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_list v1 = SOME vs1
    ⇒
    ?vs2.
      v_to_list v2 = SOME vs2 ∧
      LIST_REL (v_rel genv) vs1 vs2
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac semanticPrimitivesTheory.v_to_list_ind >>
  srw_tac[][semanticPrimitivesTheory.v_to_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, flatSemTheory.v_to_list_def] >>
  srw_tac[][] >>
    imp_res_tac genv_lookup_nil >>
  imp_res_tac genv_lookup_cons >>
  fs [] >>
  rw [flatSemTheory.v_to_list_def] >>
  res_tac >>
  fs []
QED

Theorem vs_to_string[local]:
  ∀v1 v2 s.
    LIST_REL (v_rel genv) v1 v2 ⇒
    vs_to_string v1 = SOME s ⇒
    vs_to_string v2 = SOME s
Proof
  ho_match_mp_tac semanticPrimitivesTheory.vs_to_string_ind
  \\ rw[semanticPrimitivesTheory.vs_to_string_def,vs_to_string_def]
  \\ fs[v_rel_eqns]
  \\ pop_assum mp_tac
  \\ TOP_CASE_TAC \\ strip_tac \\ rveq \\ fs[]
  \\ rw[vs_to_string_def]
QED

Theorem v_rel_lems[local]:
  !genv. genv_c_ok genv.c ⇒
    (!b. v_rel genv (Boolv b) (Boolv b)) ∧
    v_rel genv div_exn_v div_exn_v ∧
    v_rel genv chr_exn_v chr_exn_v ∧
    v_rel genv bind_exn_v bind_exn_v ∧
    v_rel genv sub_exn_v subscript_exn_v
Proof
  rw [semanticPrimitivesTheory.div_exn_v_def, flatSemTheory.div_exn_v_def,
      semanticPrimitivesTheory.chr_exn_v_def, flatSemTheory.chr_exn_v_def,
      semanticPrimitivesTheory.bind_exn_v_def, flatSemTheory.bind_exn_v_def,
      semanticPrimitivesTheory.sub_exn_v_def, flatSemTheory.subscript_exn_v_def,
      v_rel_eqns, genv_c_ok_def, has_exns_def, has_bools_def,
      semanticPrimitivesTheory.Boolv_def, flatSemTheory.Boolv_def] >>
  every_case_tac >>
  simp [v_rel_eqns]
QED

Theorem list_to_v_v_rel:
   !xs ys.
     has_lists genv.c ∧ LIST_REL (v_rel genv) xs ys ⇒
       v_rel genv (list_to_v xs) (list_to_v ys)
Proof
  Induct >>
  rw [] >>
  fs [LIST_REL_EL_EQN, flatSemTheory.list_to_v_def, has_lists_def,
      v_rel_eqns, semanticPrimitivesTheory.list_to_v_def]
QED

Theorem LIST_REL_IMP_EL2: (* TODO: move *)
  !P xs ys. LIST_REL P xs ys ==> !i. i < LENGTH ys ==> P (EL i xs) (EL i ys)
Proof
  Induct_on `xs` \\ fs [PULL_EXISTS] \\ rw [] \\ Cases_on `i` \\ fs []
QED

Theorem LIST_REL_IMP_EL: (* TODO: move *)
  !P xs ys. LIST_REL P xs ys ==> !i. i < LENGTH xs ==> P (EL i xs) (EL i ys)
Proof
  Induct_on `xs` \\ fs [PULL_EXISTS] \\ rw [] \\ Cases_on `i` \\ fs []
QED

Theorem NOT_NULL_EQ[local]:
  (~ NULL xs) = (?y ys. xs = CONS y ys)
Proof
  Cases_on `xs` \\ simp []
QED

Theorem v_rel_check_type:
  v_rel genv v1 w1 ∧ genv_c_ok genv.c ∧ check_type ty v1 ⇒ check_type ty w1
Proof
  Cases_on ‘ty’ using prim_type_cases
  \\ rw [] \\ gvs [semanticPrimitivesTheory.check_type_def]
  \\ gvs [v_rel_eqns,semanticPrimitivesTheory.Boolv_def]
  \\ rw [] \\ gvs [flatSemTheory.check_type_def,Boolv_def]
  \\ gvs [genv_c_ok_def,has_bools_def] \\ res_tac \\ fs []
QED

Theorem do_test_lemma[local]:
  do_test test ty v1 v2 = Eq_val b ∧
  genv_c_ok genv.c ∧
  v_rel genv v1 w1 ∧ v_rel genv v2 w2 ⇒
  do_test test ty w1 w2 = Eq_val b
Proof
  strip_tac
  \\ gvs [oneline semanticPrimitivesTheory.do_test_def, AllCaseEqs()]
  \\ gvs [oneline flatSemTheory.do_test_def, AllCaseEqs()]
  >-
   (gvs [semanticPrimitivesTheory.check_type_def]
    \\ fs [Once v_rel_cases] \\ gvs []
    \\ fs [the_Litv_Float64_def]
    \\ fs [semanticPrimitivesTheory.the_Litv_Float64_def]
    \\ gvs [check_type_def])
  >-
   (drule_all (cj 1 do_eq) \\ simp []
    \\ imp_res_tac v_rel_check_type \\ fs [])
  \\ gvs [oneline semanticPrimitivesTheory.dest_Litv_def, AllCaseEqs()]
  \\ gvs [oneline flatSemTheory.dest_Litv_def, AllCaseEqs()]
  \\ gvs [v_rel_eqns]
QED

Theorem check_type_IMP_v_rel:
  check_type ty v ∧ genv_c_ok genv.c ⇒ v_rel genv v (v_to_flat v)
Proof
  Cases_on ‘ty’ using prim_type_cases
  \\ gvs [semanticPrimitivesTheory.check_type_def]
  \\ rw [] \\ gvs [v_to_flat_def]
  \\ EVAL_TAC \\ simp [Once v_rel_cases]
  \\ gvs [genv_c_ok_def,has_bools_def,EVAL “true_tag”,EVAL “false_tag”,EVAL “bool_id”]
  \\ EVAL_TAC
QED

Theorem check_type_v_rel_flat_to_v:
  check_type ty v ∧ v_rel genv v y ∧ genv_c_ok genv.c ⇒ flat_to_v y = v
Proof
  Cases_on ‘ty’ using prim_type_cases
  \\ gvs [semanticPrimitivesTheory.check_type_def] \\ rw []
  \\ fs [Once v_rel_cases,flat_to_v_def]
  \\ gvs [Boolv_def,semanticPrimitivesTheory.Boolv_def]
  \\ gvs [genv_c_ok_def,has_bools_def,EVAL “true_tag”,EVAL “false_tag”,EVAL “bool_id”]
  \\ rw [] \\ gvs [semanticPrimitivesTheory.ctor_same_type_def,FORALL_PROD]
  \\ Cases_on ‘cn'’ \\ gvs [] \\ res_tac
QED

Theorem check_type_v_rel_MAP_flat_to_v:
  ∀v y.
    EVERY (check_type ty) v ∧ LIST_REL (v_rel genv) v y ∧ genv_c_ok genv.c ⇒
    MAP flat_to_v y = v
Proof
  Induct \\ gvs [PULL_EXISTS] \\ rpt strip_tac
  \\ drule_all check_type_v_rel_flat_to_v \\ fs []
QED

Theorem do_arith_INL[local]:
  EVERY (check_type ty) vs ∧ genv_c_ok genv.c ∧
  LIST_REL (v_rel genv) vs vs_i1 ∧
  do_arith a ty vs = SOME (INL exn) ⇒
  exn = div_exn_v ∧
  EVERY (check_type ty) (MAP flat_to_v vs_i1) ∧
  ∃e. do_arith a ty (MAP flat_to_v vs_i1) = SOME (INL e)
Proof
  strip_tac
  \\ drule_all check_type_v_rel_MAP_flat_to_v
  \\ strip_tac \\ fs []
  \\ gvs [oneline do_arith_def,AllCaseEqs()]
QED

Theorem do_arith_INR[local]:
  EVERY (check_type ty) vs ∧ genv_c_ok genv.c ∧
  LIST_REL (v_rel genv) vs vs_i1 ∧
  do_arith a ty vs = SOME (INR r) ⇒
  EVERY (check_type ty) (MAP flat_to_v vs_i1) ∧
  ∃r'. do_arith a ty (MAP flat_to_v vs_i1) = SOME (INR r') ∧
       v_rel genv r (v_to_flat r')
Proof
  strip_tac
  \\ drule_all check_type_v_rel_MAP_flat_to_v
  \\ strip_tac \\ fs []
  \\ drule_all do_arith_check_type
  \\ rpt strip_tac
  \\ drule_all check_type_IMP_v_rel
  \\ simp []
QED

Theorem do_conversion_INL[local]:
  check_type ty1 v ∧ genv_c_ok genv.c ∧
  v_rel genv v v_i1 ∧
  do_conversion v ty1 ty2 = SOME (INL exn) ⇒
  exn = chr_exn_v ∧
  check_type ty1 (flat_to_v v_i1) ∧
  ∃e. do_conversion (flat_to_v v_i1) ty1 ty2 = SOME (INL e)
Proof
  strip_tac
  \\ drule_all check_type_v_rel_flat_to_v
  \\ strip_tac \\ fs []
  \\ gvs [oneline do_conversion_def,AllCaseEqs()]
QED

Theorem do_conversion_INR[local]:
  check_type ty1 v ∧ genv_c_ok genv.c ∧
  v_rel genv v v_i1 ∧
  do_conversion v ty1 ty2 = SOME (INR r) ⇒
  check_type ty1 (flat_to_v v_i1) ∧
  ∃r'. do_conversion (flat_to_v v_i1) ty1 ty2 = SOME (INR r') ∧
       v_rel genv r (v_to_flat r')
Proof
  strip_tac
  \\ drule_all check_type_v_rel_flat_to_v
  \\ strip_tac \\ fs []
  \\ drule_all do_conversion_check_type
  \\ rpt strip_tac
  \\ drule_all check_type_IMP_v_rel
  \\ simp []
QED

val s_i1 = ``s_i1 : ('f_orac_st, 'ffi) flatSem$state``;
val s1_i1 = mk_var ("s1_i1", type_of s_i1);

Theorem do_app[local]:
  ∀genv s1 s2 op vs r ^s1_i1 vs_i1.
    do_app s1 op vs = SOME (s2, r) ∧
    LIST_REL (sv_rel genv) (FST s1) (TL s1_i1.refs) ∧
    ~ NULL s1_i1.refs ∧
    LIST_REL (v_rel genv) vs vs_i1 ∧
    SND s1 = s1_i1.ffi ∧
    genv_c_ok genv.c ∧
    op ≠ AallocEmpty ∧
    op ≠ Env_id
    ⇒
     ∃r_i1 s2_i1.
       LIST_REL (sv_rel genv) (FST s2) (TL s2_i1.refs) ∧
       ~ NULL s2_i1.refs ∧
       SND s2 = s2_i1.ffi ∧
       s1_i1.globals = s2_i1.globals ∧
       TAKE 1 s1_i1.refs = TAKE 1 s2_i1.refs ∧
       result_rel v_rel genv r r_i1 ∧
       do_app s1_i1 (astOp_to_flatOp op) vs_i1 = SOME (s2_i1, r_i1)
Proof
  rpt gen_tac >>
  Cases_on `s1` >>
  Cases_on `s1_i1.refs` >> simp [] >>
  Cases_on `s1_i1` >>
  Cases_on `op = ConfigGC` >-
     (simp [astOp_to_flatOp_def] >>
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, Unitv_def]) >>
  pop_assum mp_tac >>
  Cases_on `op` >>
  simp [astOp_to_flatOp_def, astTheory.getOpClass_def]
  >~ [‘Shift’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases] >>
      full_simp_tac(srw_ss())[v_rel_eqns] >>
      fs[flatSemTheory.do_app_def] >>
      TRY (rename1 `shift8_lookup s11 w11 n11`) >>
      TRY (rename1 `shift64_lookup s11 w11 n11`) >>
      full_simp_tac(srw_ss())[v_rel_eqns]
      \\ Cases_on`w11` \\ Cases_on`s11` \\ fs[shift8_lookup_def,shift64_lookup_def, result_rel_cases, Once v_rel_eqns])
  >~ [‘Equality’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [Boolv_11, do_eq, eq_result_11, eq_result_distinct, v_rel_lems])
  >~ [‘Arith a ty’] >- (
      gvs [oneline semanticPrimitivesTheory.do_app_def,AllCaseEqs()]
      \\ gvs [oneline flatSemTheory.do_app_def,AllCaseEqs()]
      \\ reverse (rw []) \\ fs []
      \\ simp [result_rel_cases,PULL_EXISTS]
      >- (drule_all do_arith_INR \\ strip_tac \\ simp [])
      \\ drule_all do_arith_INL \\ strip_tac \\ gvs []
      \\ EVAL_TAC
      \\ simp [Once v_rel_cases]
      \\ gvs [genv_c_ok_def,has_exns_def,EVAL “div_tag”]
      \\ EVAL_TAC)
  >~ [‘FromTo ty1 ty2’] >- (
      gvs [oneline semanticPrimitivesTheory.do_app_def,AllCaseEqs()]
      \\ gvs [oneline flatSemTheory.do_app_def,AllCaseEqs()]
      \\ reverse (rw []) \\ fs []
      \\ simp [result_rel_cases,PULL_EXISTS]
      >- (drule_all do_conversion_INR \\ strip_tac \\ simp [])
      \\ drule_all do_conversion_INL \\ strip_tac \\ gvs []
      \\ imp_res_tac v_rel_lems \\ gvs [])
  >~ [‘Test test ty’] >- (
      gvs [oneline semanticPrimitivesTheory.do_app_def,AllCaseEqs()]
      \\ gvs [oneline flatSemTheory.do_app_def,AllCaseEqs()]
      \\ rw [PULL_EXISTS] \\ gvs []
      \\ drule_all do_test_lemma \\ fs []
      \\ full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >~ [‘Opapp’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >~ [‘Opassign’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_assign_def,store_v_same_type_def, Unitv_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[GSYM ADD1, LUPDATE_def] >-
      metis_tac [EVERY2_LUPDATE_same, sv_rel_rules] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN,sv_rel_cases] >>
      srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> res_tac >> full_simp_tac(srw_ss())[])
  >~ [‘Opref’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      full_simp_tac(srw_ss())[ADD1] >>
      metis_tac [LIST_REL_LENGTH])
  >~ [‘Opderef’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, ADD1] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases, REWRITE_RULE [ADD1] EL] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][])
  >~ [‘Aw8alloc’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      full_simp_tac(srw_ss())[store_lookup_def, ADD1, REWRITE_RULE [ADD1] EL] >>
      srw_tac[][sv_rel_cases, PULL_EXISTS, ADD1] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >~ [‘Aw8sub’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      full_simp_tac(srw_ss())[ADD1, REWRITE_RULE [ADD1] EL] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def, v_rel_lems])
  >~ [‘Aw8length’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      full_simp_tac(srw_ss())[ADD1, REWRITE_RULE [ADD1] EL] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def])
  >~ [‘Aw8update’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      full_simp_tac(srw_ss())[ADD1, REWRITE_RULE [ADD1] EL, REWRITE_RULE [ADD1] LUPDATE_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][Unitv_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      fsrw_tac[][] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][v_rel_lems])
  >~ [‘CopyStrStr’] >- (
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases]
    \\ simp[v_rel_lems,v_rel_eqns])
  >~ [‘CopyStrAw8’] >- (
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def,Unitv_def]
    \\ fs [REWRITE_RULE [ADD1] EL, ADD1]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns,ADD1]
    \\ simp[store_v_same_type_def, REWRITE_RULE [ADD1] LUPDATE_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >~ [‘CopyAw8Str’] >- (
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def,Unitv_def]
    \\ fs [REWRITE_RULE [ADD1] EL, ADD1]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns])
  >~ [‘CopyAw8Aw8’] >- (
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def,Unitv_def]
    \\ fs [REWRITE_RULE [ADD1] EL, ADD1]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns]
    \\ simp[store_v_same_type_def, REWRITE_RULE [ADD1] LUPDATE_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >~ [‘XorAw8Str_unsafe’] >- (
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def,Unitv_def]
    \\ fs [REWRITE_RULE [ADD1] EL, ADD1]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns]
    \\ simp[store_v_same_type_def, REWRITE_RULE [ADD1] LUPDATE_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >~ [‘Implode’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      imp_res_tac v_to_char_list >>
      srw_tac[][])
  >~ [‘Explode’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      imp_res_tac v_to_char_list >>
      srw_tac[][] >>
      namedCases_on ‘strng’ ["s"] >>
      fs [] >>
      Induct_on `s` >>
      fs [semanticPrimitivesTheory.list_to_v_def,flatSemTheory.list_to_v_def] >>
      simp [Once v_rel_cases] >>
      fs [genv_c_ok_def,has_lists_def] >>
      simp [Once v_rel_cases])
  >~ [‘Strsub’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_eqns] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[v_rel_lems]
      >> rename1 ‘explode strng’ >> Cases_on ‘strng’ >> fs [])
  >~ [‘Strlen’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >~ [‘Strcat’] >- (
    rw[semanticPrimitivesPropsTheory.do_app_cases,flatSemTheory.do_app_def]
    \\ fs[LIST_REL_def]
    \\ imp_res_tac v_to_list \\ fs[]
    \\ imp_res_tac vs_to_string \\ fs[result_rel_cases,v_rel_eqns] )
  >~ [‘VfromList’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_eqns] >>
      imp_res_tac v_to_list >>
      srw_tac[][])
  >~ [‘Vsub’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ, v_rel_lems])
  >~ [‘Vsub_unsafe’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ, v_rel_lems])
  >~ [‘Vlength’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][] >>
      metis_tac [LIST_REL_LENGTH])
  >~ [‘Aalloc’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases, LIST_REL_REPLICATE_same, ADD1] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >~ [‘AallocFixed’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases, LIST_REL_REPLICATE_same, ADD1] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >~ [‘Asub’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      fs [REWRITE_RULE [ADD1] EL, ADD1] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, v_rel_lems] >>
      decide_tac)
  >~ [‘Alength’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[store_lookup_def, sv_rel_cases] >>
      fs [REWRITE_RULE [ADD1] EL, ADD1] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      res_tac >>
      full_simp_tac(srw_ss())[sv_rel_cases] >>
      metis_tac [store_v_distinct, store_v_11, LIST_REL_LENGTH])
  >~ [‘Aupdate’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def,Unitv_def] >>
      fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, v_rel_lems] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][] >>
      decide_tac)
  >~ [‘Asub_unsafe’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, v_rel_lems] >>
      decide_tac)
  >~ [‘Aupdate_unsafe’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      drule_then drule LIST_REL_IMP_EL2 >>
      disch_tac >>
      every_case_tac >>
      full_simp_tac(srw_ss())[sv_rel_cases] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[Unitv_def] >>
      DEP_REWRITE_TAC [listTheory.EVERY2_LUPDATE_same] >>
      full_simp_tac(srw_ss())[Unitv_def, sv_rel_cases] >>
      DEP_REWRITE_TAC [listTheory.EVERY2_LUPDATE_same] >>
      gvs [] >>
      decide_tac)
  >~ [‘Aw8sub_unsafe’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      rfs[] >>
      srw_tac[][markerTheory.Abbrev_def, v_rel_lems])
  >~ [‘Aw8update_unsafe’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, Unitv_def, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      fsrw_tac[][] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][v_rel_lems] >> CCONTR_TAC >> rfs [] >> rveq >> fs [])
  >- ((* ThunkOp *)
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases,
              flatSemTheory.do_app_def, thunk_op_def] >>
    gvs[AllCaseEqs(), PULL_EXISTS]
    >- (
      ntac 2 (pairarg_tac >> gvs[]) >>
      gvs[store_alloc_def] >>
      srw_tac[][sv_rel_cases, result_rel_cases, v_rel_eqns] >>
      gvs[LIST_REL_EL_EQN])
    >- (
      gvs[store_assign_def, store_v_same_type_def] >>
      Cases_on `EL lnum q` >> gvs[] >> Cases_on `t'` >> gvs[] >>
      qpat_x_assum `v_rel _ (Loc _ _) y` mp_tac >> rw[Once v_rel_cases] >>
      gvs [LIST_REL_EL_EQN, REWRITE_RULE [ADD1] LUPDATE_def, EL_LUPDATE]
      >- (rw[] >> simp [Once sv_rel_cases])
      >- simp[Once result_rel_cases, Once v_rel_cases]
      >- (
        rw[REWRITE_RULE [ADD1] EL] >>
        first_x_assum drule >> gvs[] >>
        CASE_TAC >> rw[Once sv_rel_cases])))
  >~ [‘ListAppend’] >- (
    simp [semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
    rw [] >>
    fs [] >>
    rw [] >>
    imp_res_tac v_to_list >>
    fs [] >>
    rw [result_rel_cases] >>
    irule list_to_v_v_rel >>
    fs [genv_c_ok_def, LIST_REL_EL_EQN, EL_APPEND_EQN] >>
    rw [])
  >~ [‘FFI’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns,Unitv_def] \\ rw[] \\
      fs[store_lookup_def, LIST_REL_EL_EQN] \\ fs[] \\ rfs[] \\
      fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def] \\
      res_tac \\
      qpat_x_assum`EL _ _ = _`assume_tac \\ fs[] \\
      qhdtm_x_assum`sv_rel`mp_tac \\
      simp[Once sv_rel_cases] \\ rw[] \\
      fs[IMPLODE_EXPLODE_I,combinTheory.o_DEF] \\
      CASE_TAC \\ fs[store_assign_def,store_v_same_type_def,EL_LUPDATE] \\
      fs [REWRITE_RULE [ADD1] EL, ADD1, REWRITE_RULE [ADD1] LUPDATE_def]
      \\ rfs[] \\ rw[EL_LUPDATE]
      \\ rw[sv_rel_cases, result_rel_cases, v_rel_eqns])
  >~ [‘Eval’] >- (
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
  )
QED

Theorem find_recfun[local]:
  !x funs e comp_map y t.
    find_recfun x funs = SOME (y,e)
    ⇒
    find_recfun x (compile_funs t comp_map funs) =
      SOME (y, compile_exp (x::t) (comp_map with v := nsBind y (Local None y) comp_map.v) e)
Proof
  induct_on `funs` >>
   srw_tac[][Once find_recfun_def, compile_exp_def] >>
   PairCases_on `h` >>
   full_simp_tac(srw_ss())[] >>
   every_case_tac >>
   full_simp_tac(srw_ss())[Once find_recfun_def, compile_exp_def]
QED

Theorem do_app_rec_help[local]:
  !genv comp_map env_v_local env_v_local' env_v_top funs t.
    env_rel genv env_v_local env_v_local'.v ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local'.v)) env' ∧
    LENGTH ts = LENGTH funs' + LENGTH env_v_local'.v
    ⇒
     env_rel genv
       (alist_to_ns
          (MAP
             (λ(f,n,e).
                (f,
                 Recclosure
                   (env' with v := nsAppend env_v_local env'.v)
                   funs' f)) funs))
       (MAP
          (λ(fn,n,e).
             (fn,
              Recclosure env_v_local'
                (compile_funs t
                   (comp_map with v :=
                     (FOLDR (λ(x,v) e. nsBind x v e) comp_map.v
                      (MAP2 (λt x. (x,Local t x)) ts
                         (MAP FST funs' ++ MAP FST env_v_local'.v)))) funs')
                fn))
          (compile_funs t
             (comp_map with v :=
               (FOLDR (λ(x,v) e. nsBind x v e) comp_map.v
                (MAP2 (λt x. (x,Local t x)) ts
                   (MAP FST funs' ++ MAP FST env_v_local'.v)))) funs))
Proof
  induct_on `funs`
  >- srw_tac[][v_rel_eqns, compile_exp_def] >>
  rw [] >>
  PairCases_on`h`>>fs[compile_exp_def]>>
  simp[v_rel_eqns]>>
  simp [Once v_rel_cases] >>
  MAP_EVERY qexists_tac [`comp_map`, `env'`, `env_v_local`, `t`,`ts`] >>
  simp[compile_exp_def,bind_locals_def]>>
  simp_tac (std_ss) [GSYM APPEND, namespaceTheory.nsBindList_def]
QED

Theorem global_env_inv_add_locals[local]:
  !genv comp_map locals1 locals2 env.
    global_env_inv genv comp_map locals1 env
    ⇒
    global_env_inv genv comp_map (locals2 ∪ locals1) env
Proof
  srw_tac[][v_rel_global_eqn] >>
  metis_tac []
QED

Theorem global_env_inv_extend2[local]:
  !genv comp_map env new_vars env' locals env_c.
    set (MAP (Short o FST) new_vars) = nsDom env' ∧
    global_env_inv genv comp_map locals env ∧
    global_env_inv genv (comp_map with v := alist_to_ns new_vars) locals <| v := env'; c := env_c |>
    ⇒
    global_env_inv genv (comp_map with v := nsBindList new_vars comp_map.v) locals
        (env with v := nsAppend env' env.v)
Proof
  rw [v_rel_global_eqn, GSYM nsAppend_to_nsBindList] >>
  fs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_none, nsLookup_alist_to_ns_some] >>
  res_tac >>
  fs [] >>
  rw [] >>
  fs [] >> rveq >> fs [] >>
  goal_assum (first_assum o mp_then (Pat `EL _ _ = _`) mp_tac) >>
  simp [] >>
  Cases_on `x` >>
  fs [] >> rw []
  >- (
    `Short n' ∉ nsDom env'` by metis_tac [nsLookup_nsDom, NOT_SOME_NONE] >>
    qexists_tac`t` >>
    disj2_tac >>
    rw [ALOOKUP_NONE] >>
    qpat_x_assum `_ = nsDom _` (assume_tac o GSYM) >>
    fs [MEM_MAP] >>
    fs [namespaceTheory.id_to_mods_def])
  >- (
    fs [namespaceTheory.id_to_mods_def] >>
    Cases_on `p1` >>
    fs [] >>
    rw [])
QED

Theorem lookup_build_rec_env_lem[local]:
  !x cl_env funs' funs.
    ALOOKUP (MAP (λ(fn,n,e). (fn,Recclosure cl_env funs' fn)) funs) x = SOME v
    ⇒
    v = semanticPrimitives$Recclosure cl_env funs' x
Proof
  induct_on `funs` >>
  srw_tac[][] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[]
QED

Theorem sem_env_eq_lemma[local]:
  !(env:'a sem_env) x. (env with v := x) = <| v := x; c := env.c |>
Proof
  rw [] >>
  rw [sem_env_component_equality]
QED

Theorem do_opapp[local]:
  !genv vs vs_i1 env e.
    semanticPrimitives$do_opapp vs = SOME (env, e) ∧
    LIST_REL (v_rel genv) vs vs_i1
    ⇒
     ∃comp_map env_i1 locals t1 ts.
       env_all_rel genv comp_map env env_i1 locals ∧
       LENGTH ts = LENGTH locals ∧
       flatSem$do_opapp vs_i1 = SOME (env_i1, compile_exp t1 (comp_map with v := bind_locals ts locals comp_map.v) e)
Proof
  srw_tac[][do_opapp_cases, flatSemTheory.do_opapp_def] >>
   full_simp_tac(srw_ss())[LIST_REL_CONS1] >>
   srw_tac[][]
   >- (
       qpat_x_assum `v_rel genv (Closure _ _ _) _` mp_tac >>
       srw_tac[][Once v_rel_cases] >>
       srw_tac[][] >>
       rename [`v_rel _ v v'`, `env_rel _ envL env'.v`, `nsBind name _ _`] >>
       MAP_EVERY qexists_tac [`comp_map`, `name :: MAP FST env'.v`, `t`, `ts`] >>
       srw_tac[][bind_locals_def, env_all_rel_cases, namespaceTheory.nsBindList_def, FOLDR_MAP] >>
       fs[ADD1]>>
       MAP_EVERY qexists_tac [`nsBind name v envL`, `env`] >>
       simp [flatSemTheory.environment_component_equality,
         sem_env_component_equality] >>
       srw_tac[][v_rel_eqns]
       >- (
         drule env_rel_dom >>
         rw [MAP_o] >>
         rw_tac list_ss [GSYM alist_to_ns_cons] >>
         qexists_tac`(name,v)::l`>>simp[])>>
       full_simp_tac(srw_ss())[v_rel_eqns, v_rel_global_eqn] >>
       metis_tac [])
   >- (
     rename [`find_recfun name funs = SOME (arg, e)`,
             `v_rel _ (Recclosure env _ _) fun_v'`,
             `v_rel _ v v'`] >>
     qpat_x_assum `v_rel genv (Recclosure _ _ _) _` mp_tac >>
     srw_tac[][Once v_rel_cases] >>
     srw_tac[][] >>
     imp_res_tac find_recfun >>
     srw_tac[][]
     >- (
       MAP_EVERY qexists_tac [`comp_map`, `arg :: MAP FST funs ++ MAP FST env_v_local'.v`,`name::t`,`None::ts`] >>
       srw_tac[][bind_locals_def, env_all_rel_cases, namespaceTheory.nsBindList_def] >>
       srw_tac[][]>>fs[]
       >- (
         rw [sem_env_component_equality, flatSemTheory.environment_component_equality] >>
         MAP_EVERY qexists_tac [`nsBind arg v (build_rec_env funs (env' with v := nsAppend env_v_local env'.v) env_v_local)`, `env'`] >>
         srw_tac[][semanticPrimitivesPropsTheory.build_rec_env_merge, EXTENSION]
         >- (
           imp_res_tac env_rel_dom >>
           simp [] >>
           rw_tac list_ss [GSYM alist_to_ns_cons] >>
           simp [] >>
           simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
           rpt (pop_assum kall_tac) >>
           induct_on `funs` >>
           rw [] >>
           pairarg_tac >>
           rw [])
         >- metis_tac [INSERT_SING_UNION, global_env_inv_add_locals, UNION_COMM]
         >- (
           simp [v_rel_eqns, build_rec_env_merge] >>
           match_mp_tac env_rel_append >>
           simp [] >>
           metis_tac [do_app_rec_help]))
       >- (
         simp[compile_funs_map,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
         full_simp_tac(srw_ss())[FST_triple]))
     >- (
       MAP_EVERY qexists_tac [`comp_map with v := nsBindList new_vars comp_map.v`, `[arg]`, `t1`, `[t2]`] >>
       srw_tac[][env_all_rel_cases, namespaceTheory.nsBindList_def,bind_locals_def] >>
       rw [GSYM namespaceTheory.nsBindList_def] >>
       MAP_EVERY qexists_tac [`nsSing arg v`, `env with v := build_rec_env funs env env.v`] >>
       simp [semanticPrimitivesTheory.sem_env_component_equality,
             environment_component_equality] >>
       srw_tac[][semanticPrimitivesTheory.sem_env_component_equality,
             semanticPrimitivesPropsTheory.build_rec_env_merge, EXTENSION,
             environment_component_equality]
       >- (
         qexists_tac `[(arg,v)]` >>
         rw [namespaceTheory.nsSing_def, namespaceTheory.nsBind_def,
             namespaceTheory.nsEmpty_def])
       >- (
         irule global_env_inv_extend2 >>
         rw []
         >- (
           `MAP (Short:tvarN -> (tvarN, tvarN) id) (MAP FST new_vars) = MAP Short (MAP FST (REVERSE funs))` by metis_tac [] >>
           fs [MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
         >- metis_tac [global_env_inv_add_locals, UNION_EMPTY]
         >- (
           qexists_tac `env.c` >>
           srw_tac[][v_rel_eqns, v_rel_global_eqn] >>
           fs [nsLookup_alist_to_ns_some] >>
           rw []
           >- (
             `MEM x' (MAP FST funs)`
                     by (imp_res_tac ALOOKUP_MEM >>
                         full_simp_tac(srw_ss())[MEM_MAP] >>
                         PairCases_on `y` >>
                         srw_tac[][] >>
                         full_simp_tac(srw_ss())[] >>
                         metis_tac [FST, MEM_MAP, pair_CASES]) >>
             res_tac >>
             qexists_tac `n` >>
             srw_tac[][] >>
             drule lookup_build_rec_env_lem >>
             srw_tac[][Once v_rel_cases] >>
             MAP_EVERY qexists_tac [`comp_map`, `new_vars`, `t2`, `t3`] >>
             srw_tac[][find_recfun_ALOOKUP])
           >- fs [v_rel_eqns, v_rel_global_eqn]))
       >- (
         simp [Once v_rel_cases] >>
         qexists_tac `v` >>
         qexists_tac `nsEmpty` >>
         rw [namespaceTheory.nsSing_def, namespaceTheory.nsEmpty_def,
             namespaceTheory.nsBind_def] >>
         simp [Once v_rel_cases, namespaceTheory.nsEmpty_def])))
QED

Theorem pat_bindings_compile_pat[simp]:
 !comp_map (p:ast$pat) vars. pat_bindings (compile_pat comp_map p) vars = pat_bindings p vars
Proof
  ho_match_mp_tac compile_pat_ind >>
  simp [compile_pat_def, astTheory.pat_bindings_def, pat_bindings_def] >>
  induct_on `ps` >>
  rw [] >>
  fs [pat_bindings_def,astTheory.pat_bindings_def, PULL_FORALL]
QED

Theorem eta2[local]:
  !f x. (\y. f x y) = f x
Proof
  metis_tac []
QED

Theorem ctor_same_type_refl[local]:
  ctor_same_type x x
Proof
  Cases_on `x` >>
  rw [ctor_same_type_def] >>
  rename [`SOME x`] >>
  Cases_on `x` >>
  rw [ctor_same_type_def]
QED

Theorem ctor_same_type_SND[local]:
  ctor_same_type (SOME x) (SOME y) = (SND x = SND y)
Proof
  Cases_on `x` \\ Cases_on `y` \\ simp [ctor_same_type_def]
QED

Theorem genv_c_ok_pmatch_stamps_ok:
  s_rel genv s t /\
  nsLookup comp_map_c nm = SOME (flat_cn, ty_gp) /\
  same_type src_stamp src_stamp' /\
  genv_c_ok genv.c /\
  genv_c_tys_ok genv.c genv.tys /\
  FLOOKUP genv.c ((flat_cn, OPTION_MAP FST ty_gp), l) = SOME src_stamp /\
  FLOOKUP genv.c (flat_stamp', l') = SOME src_stamp' /\
  (!ty_id ctors. ty_gp = SOME (ty_id, ctors) ==>
    FLOOKUP genv.tys ty_id = SOME ctors)
  ==>
  pmatch_stamps_ok (SOME (flat_cn, ty_gp)) (SOME flat_stamp') l l'
Proof
  rw [genv_c_ok_def]
  \\ `ctor_same_type (SOME src_stamp) (SOME src_stamp')`
    by simp [semanticPrimitivesTheory.ctor_same_type_def]
  \\ `OPTION_MAP FST ty_gp = SND flat_stamp'`
    by metis_tac [ctor_same_type_SND, SND]
  \\ PairCases_on `flat_stamp'`
  \\ Cases_on `flat_stamp'1`
  >- (
    (* exceptions *)
    fs []
    \\ rw [pmatch_stamps_ok_cases]
    \\ fs [s_rel_cases, FDOM_FLOOKUP]
  )
  \\ fs [EXISTS_PROD]
  \\ simp [pmatch_stamps_ok_cases]
  \\ fs [s_rel_cases, FDOM_FLOOKUP]
  \\ imp_res_tac (REWRITE_RULE [FDOM_FLOOKUP] genv_c_tys_ok_def)
  \\ fs [] \\ rveq \\ fs []
QED

Theorem FST_PAIR_MAP_I[local]:
  FST ((I ## f) x) = FST x
Proof
  Cases_on `x` \\ simp []
QED

Theorem genv_c_ok_same_type_FST_eq_imp_same_ctor:
  genv_c_ok genv_c ∧
  FLOOKUP genv_c (cn1, l1) = SOME stamp1 ∧
  FLOOKUP genv_c (cn2, l2) = SOME stamp2 ∧
  same_type stamp1 stamp2 ∧
  FST cn1 = FST cn2 ∧ l1 = l2 ⇒
  same_ctor stamp1 stamp2
Proof
  Cases_on `cn1` \\ Cases_on `cn2`
  \\ fs [genv_c_ok_def, ctor_same_type_OPTREL, OPTREL_def,
            semanticPrimitivesTheory.ctor_same_type_def, same_ctor_def]
  \\ metis_tac [SND, SOME_11]
QED

Theorem pmatch[local]:
  (!cenv s p v env r env' env'' env_i1 ^s_i1 v_i1 st'.
   semanticPrimitives$pmatch cenv s p v env = r ∧
   s_rel genv st' s_i1 ∧
   global_env_inv genv comp_map2 shadowers senv ∧
   genv_c_ok genv.c ∧
   genv_c_tys_ok genv.c genv.tys ∧
   cenv = senv.c ∧
   comp_map2.c = comp_map.c ∧
   env = env' ++ env'' ∧
   s_i1.globals = genv.v ∧
   s = st'.refs ∧
   v_rel genv v v_i1 ∧
   env_rel genv (alist_to_ns env') env_i1
   ⇒
   ?r_i1.
     flatSem$pmatch s_i1 (compile_pat comp_map p) v_i1 env_i1 = r_i1 ∧
     match_result_rel genv env'' r r_i1) ∧
  (!cenv s ps vs env r env' env'' env_i1 ^s_i1 vs_i1 st'.
   pmatch_list cenv s ps vs env = r ∧
   global_env_inv genv comp_map2 shadowers senv ∧
   genv_c_ok genv.c ∧
   genv_c_tys_ok genv.c genv.tys ∧
   cenv = senv.c ∧
   comp_map2.c = comp_map.c ∧
   env = env' ++ env'' ∧
   s_i1.globals = genv.v ∧
   s_rel genv st' s_i1 ∧
   s = st'.refs ∧
   LIST_REL (v_rel genv) vs vs_i1 ∧
   env_rel genv (alist_to_ns env') env_i1
   ⇒
   ?r_i1.
     pmatch_list s_i1 (MAP (compile_pat comp_map) ps) vs_i1 env_i1 = r_i1 ∧
     match_result_rel genv env'' r r_i1)
Proof
  ho_match_mp_tac semanticPrimitivesTheory.pmatch_ind >>
  srw_tac[][semanticPrimitivesTheory.pmatch_def, flatSemTheory.pmatch_def, compile_pat_def] >>
  full_simp_tac(srw_ss())[match_result_rel_def, flatSemTheory.pmatch_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH
  >- (fs[compile_pat_def, v_rel_eqns] >> rveq >> fs[pmatch_def] >>
    TOP_CASE_TAC >- simp [match_result_rel_def] >>
    fs [] >>
    qmatch_assum_rename_tac `nsLookup _ _ = SOME p` >>
    `?l stamp. p = (l, stamp)` by metis_tac [pair_CASES] >> fs [] >>
    TOP_CASE_TAC >> simp [match_result_rel_def] >>
    fs [v_rel_global_eqn] >>
    last_assum (drule_then strip_assume_tac) >>
    rfs [eta2] >>
    drule_then (drule_then (fn t => CHANGED_TAC (DEP_REWRITE_TAC [t])))
        genv_c_ok_pmatch_stamps_ok >>
    simp [] >>
    TOP_CASE_TAC >> simp [match_result_rel_def]
    >- (
      (* same ctor *)
      TOP_CASE_TAC >> simp [match_result_rel_def] >>
      rw [] >>
      fs [semanticPrimitivesTheory.same_ctor_def, genv_c_ok_def] >>
      metis_tac [genv_c_ok_def, FST]
    )
    >- (
      (* diff ctor *)
      fs [] >>
      rw [match_result_rel_def] >>
      drule_then (drule_then (drule_then drule))
        genv_c_ok_same_type_FST_eq_imp_same_ctor >>
      simp []
    )
  )
  >- (simp [pmatch_stamps_ok_cases] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def, s_rel_cases] >>
      metis_tac [])
  >- (imp_res_tac s_rel_cases >>
      imp_res_tac NOT_NULL_EQ >>
      full_simp_tac(srw_ss())[store_lookup_def, ADD1, REWRITE_RULE [ADD1] EL] >>
      imp_res_tac LIST_REL_LENGTH >>
      rw [match_result_rel_def] >>
      fs [] >>
      imp_res_tac LIST_REL_IMP_EL2 >>
      fs [sv_rel_cases, match_result_rel_def]
  )
  >- (
    gvs []
    \\ ‘((i,v)::(env' ++ env'')) = ((i,v)::env') ++ env''’
      by gs []
    \\ pop_assum SUBST_ALL_TAC
    \\ first_x_assum irule \\ gs []
    \\ simp [env_rel_bind_one])
  >- (
      rfs [] >>
      first_x_assum (qsubterm_then
          `pmatch _ (compile_pat _ _) _ _` mp_tac) >>
      rpt (disch_then (first_assum o mp_then Any mp_tac)) >>
      rw [] >>
      imp_res_tac match_result_rel_imp >> fs [match_result_rel_def] >>
      rpt (first_x_assum (first_assum o mp_then Any strip_assume_tac)) >>
      fs [] >>
      imp_res_tac match_result_rel_imp >> fs [match_result_rel_def]
  )
QED

(* compiler correctness *)

Theorem opt_bind_lem[local]:
  opt_bind NONE = \x y.y
Proof
  rw [FUN_EQ_THM, miscTheory.opt_bind_def]
QED

Theorem env_updated_lem[local]:
  env with v updated_by (λy. y) = (env : 'a flatSem$environment)
Proof
  rw [environment_component_equality]
QED

Theorem evaluate_foldr_let_err[local]:
  !env s s' exps e x.
    flatSem$evaluate env s exps = (s', Rerr x)
    ⇒
    evaluate env s [FOLDR (Let t NONE) e exps] = (s', Rerr x)
Proof
  Induct_on `exps` >>
  rw [evaluate_def] >>
  fs [Once evaluate_cons] >>
  every_case_tac >>
  fs [evaluate_def] >>
  rw [] >>
  first_x_assum drule >>
  disch_then (qspec_then `e` mp_tac) >>
  rw [] >>
  every_case_tac >>
  fs [opt_bind_lem, env_updated_lem]
QED

Definition env_domain_eq_def:
  env_domain_eq (var_map : source_to_flat$environment) (env : 'a sem_env)⇔
    nsDom var_map.v = nsDom env.v ∧
    nsDomMod var_map.v = nsDomMod env.v ∧
    nsDom var_map.c = nsDom env.c ∧
    nsDomMod var_map.c = nsDomMod env.c
End

Theorem env_domain_eq_append[local]:
  env_domain_eq env1 env1' ∧
   env_domain_eq env2 env2'
   ⇒
   env_domain_eq (extend_env env1 env2) (extend_dec_env env1' env2')
Proof
  rw [env_domain_eq_def, extend_env_def, extend_dec_env_def,nsLookupMod_nsAppend_some,
      nsLookup_nsAppend_some, nsLookup_nsDom, namespaceTheory.nsDomMod_def,
      EXTENSION, GSPECIFICATION, EXISTS_PROD] >>
  metis_tac [option_nchotomy, NOT_SOME_NONE, pair_CASES]
QED

Theorem global_env_inv_append[local]:
  !genv var_map1 var_map2 env1 env2.
    env_domain_eq var_map1 env1 ∧
    global_env_inv genv var_map1 {} env1 ∧
    global_env_inv genv var_map2 {} env2
    ⇒
    global_env_inv genv (extend_env var_map1 var_map2) {} (extend_dec_env env1 env2)
Proof
  rw [env_domain_eq_def, v_rel_global_eqn, nsLookup_nsAppend_some,
    extend_env_def, extend_dec_env_def] >>
  first_x_assum drule >>
  rw [] >> rw []
  >- (
    goal_assum (first_assum o mp_then (Pat `EL _ _ = _`) mp_tac) >>
    rw [] >>
    fs [EXTENSION, namespacePropsTheory.nsLookup_nsDom,
        namespaceTheory.nsDomMod_def, GSPECIFICATION, EXISTS_PROD] >>
    metis_tac [NOT_SOME_NONE, option_nchotomy]
  )
  >- (
    qsuff_tac `nsLookup var_map1.c x = NONE`
    >- (
      fs [EXTENSION, namespacePropsTheory.nsLookup_nsDom,
          namespaceTheory.nsDomMod_def, GSPECIFICATION, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy]
    ) >>
    fs [EXTENSION, namespacePropsTheory.nsLookup_nsDom] >>
    metis_tac [NOT_SOME_NONE, option_nchotomy]
  )
QED

val result_rel_imp = hd (RES_CANON result_rel_cases);

Definition idx_prev_def:
  idx_prev idx idx2 <=>
  idx.vidx <= idx2.vidx /\ idx.tidx <= idx2.tidx /\ idx.eidx <= idx2.eidx
End

Theorem idx_prev_refl:
  idx_prev idx idx
Proof
  simp [idx_prev_def]
QED

Theorem idx_prev_trans:
  idx_prev idx idx2 /\ idx_prev idx2 idx3 ==> idx_prev idx idx3
Proof
  simp [idx_prev_def]
QED

Datatype:
  idx_types =
  Idx_Var | Idx_Type | Idx_Exn
End

Theorem idx_types_FORALL:
  (!x. P x) = (P Idx_Var ∧ P Idx_Type ∧ P Idx_Exn)
Proof
  EQ_TAC \\ rw []
  \\ Cases_on `x` \\ simp []
QED

Definition ALL_DISJOINT_DEF:
  ALL_DISJOINT xs ⇔
  ∀i j. i < LENGTH xs ∧ j < LENGTH xs ∧ i ≠ j ⇒ EL i xs ∩ EL j xs = ∅
End

Theorem ALL_DISJOINT_CONS:
  (ALL_DISJOINT [x] = T) ∧
  (ALL_DISJOINT (x :: y :: zs) = (DISJOINT x y ∧ ALL_DISJOINT (x ∪ y :: zs)))
Proof
  simp [ALL_DISJOINT_DEF, GSYM DISJOINT_DEF]
  \\ simp [arithmeticTheory.LT_SUC, satTheory.AND_IMP]
  \\ simp [DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM, PULL_EXISTS]
  \\ simp [LEFT_AND_OVER_OR]
  \\ simp [DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM, PULL_EXISTS]
  \\ metis_tac [DISJOINT_SYM]
QED

Definition idx_block_def:
  idx_block start_idx end_idx =
  {(i, Idx_Var) | start_idx.vidx ≤ i ∧ i < end_idx.vidx} ∪
  {(i, Idx_Type) | start_idx.tidx ≤ i ∧ i < end_idx.tidx} ∪
  {(i, Idx_Exn) | start_idx.eidx ≤ i ∧ i < end_idx.eidx}
End

Definition idx_final_block_def:
  idx_final_block start_idx =
  {(i, Idx_Var) | start_idx.vidx ≤ i} ∪
  {(i, Idx_Type) | start_idx.tidx ≤ i} ∪
  {(i, Idx_Exn) | start_idx.eidx ≤ i}
End

Definition genv_allocated_idxs_def:
  genv_allocated_idxs genv =
     {(i, Idx_Var) | i < LENGTH genv.v ∧ EL i genv.v <> NONE} ∪
        {(i, Idx_Type) | ?cn a. ((cn, SOME i), a) ∈ FDOM genv.c} ∪
        {(i, Idx_Type) | i ∈ FDOM genv.tys} ∪
        {(i, Idx_Exn) | ?a. ((i, NONE), a) ∈ FDOM genv.c}
End

(* simple invariants on env generations and stores: allocation from the
   next field will always be free *)
Definition env_gen_inv_def:
  env_gen_inv (e : environment_generation_store) =
    (domain e.envs ⊆ count e.next)
End

Definition env_store_inv_def:
  env_store_inv (e : environment_store) =
    (domain e.env_gens ⊆ count e.next)
End

Theorem inc_compile_prog_env_submap:
  inc_compile_prog env_id c p = (c', p') /\
  env_store_inv c.envs ==>
  env_store_inv c'.envs /\
  subspt c.envs.env_gens c'.envs.env_gens
Proof
  simp [inc_compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [env_store_inv_def]
  \\ fs []
  >- (
    drule_then irule SUBSET_TRANS
    \\ irule pred_setTheory.COUNT_MONO
    \\ simp []
  )
  >- (
    rw [subspt_def, lookup_insert]
    \\ imp_res_tac SUBSET_IMP
    \\ fs []
  )
QED

(* The source oracle states can always be decoded according to the
   optional decode function provided. The state
   part of the oracle sequence should be what is produced by repeatedly
   applying compile_prog *)
Definition src_orac_step_invs_def:
  src_orac_step_invs ci (g : ast$dec list -> ast$dec list) eval_state =
  (case (ci, eval_state) of
    | (NONE, NONE) => T
    | (SOME dec, SOME (EvalOracle s)) => (
    (!k env_id state_v decs. s.oracle k = (env_id, state_v, decs) ==>
        ?c x. dec state_v = SOME (c, x)) /\
    let c_orac = FST o THE o dec o FST o SND o s.oracle in
    (!k env_id state_v decs. s.oracle k = (env_id, state_v, decs) ==>
        c_orac (SUC k) = FST (inc_compile_prog env_id (c_orac k) (g decs))))
    | _ => F
  )
End

(* the flatLang oracle is derived from the source oracle by compile_prog,
   and the two compile oracles agree also *)
Definition orac_rel_inner_def:
  orac_rel_inner dec s (s_compiler : compiler_fun)
        (g : ast$dec list -> ast$dec list) c <=>
    !k env_id state_v decs. s.oracle k = (env_id, state_v, decs) ==>
        let x = THE (dec state_v) in
        let f_decs = SND (inc_compile_prog env_id (FST x) (g decs)) in
        c.compile_oracle k = (SND x, f_decs) /\
        (s_compiler (env_id, state_v, decs) <> NONE ==>
            ?bytes words f_st st_v2.
            c.compile (SND x) f_decs = SOME (bytes, words, f_st) /\
            s_compiler (env_id, state_v, decs) = SOME (st_v2, bytes, words) /\
            (!x2. dec st_v2 = SOME x2 ==> SND x2 = f_st))
End

Definition orac_rel_def:
  orac_rel interp g src_eval flat_eval <=> (case (interp, src_eval) of
    | (_, NONE) => T
    | (SOME dec, SOME (EvalOracle s)) => (
    ? s_compiler.
    s.custom_do_eval = source_evalProof$do_eval_oracle s_compiler g /\
    orac_rel_inner dec s s_compiler g flat_eval
      )
    | _ => F)
End

Theorem orac_rel_SOME_eval:
  orac_rel interp g (SOME eval_state) flat_eval ==>
  ? dec orac_st.
  interp = SOME dec /\ eval_state = EvalOracle orac_st
Proof
  simp [orac_rel_def] \\ every_case_tac \\ rw [] \\ fs []
QED

Definition src_orac_next_cfg_inner_def:
  src_orac_next_cfg_inner interp orac_0 = case (interp, orac_0) of
    | (SOME dec, (env_id, state_v, decs)) =>
      (case dec state_v of
        | SOME (c, x) => SOME c
        | _ => NONE
      )
    | _ => NONE
End

Definition src_orac_next_cfg_def:
  src_orac_next_cfg interp eval_state = case eval_state of
    | SOME (EvalOracle s) => src_orac_next_cfg_inner interp (s.oracle 0)
    | _ => NONE
End

(* every env stored in the eval state is related to a concrete env
   representation in the next oracle state *)
Definition src_orac_env_invs_def:
  src_orac_env_invs interp genv eval_state = (case eval_state of
    | NONE => T
    | SOME (EvalOracle s) =>
    (?c. src_orac_next_cfg interp eval_state = SOME c /\
      env_store_inv c.envs /\
      c.envs.next = LENGTH s.envs /\
      (!g_id id. g_id < LENGTH s.envs /\ id < LENGTH (EL g_id s.envs) ==>
        ?comp_map_gen comp_map.
        lookup g_id c.envs.env_gens = SOME comp_map_gen /\
        lookup id comp_map_gen = SOME comp_map /\
        global_env_inv genv comp_map {} (EL id (EL g_id s.envs))
    ))
    | _ => F
  )
End

Definition src_orac_gen_inv_def:
  src_orac_gen_inv eval_state = (case eval_state of
    | NONE => T
    | SOME (EvalOracle s) =>
    s.generation < LENGTH s.envs
  )
End

Definition src_orac_invs_def:
  src_orac_invs interp g genv eval_state <=>
  src_orac_step_invs interp g eval_state /\
  src_orac_env_invs interp genv eval_state /\
  src_orac_gen_inv eval_state
End

Theorem src_orac_invs_weak:
   src_orac_invs interp g genv src_eval ∧
   genv.c ⊑ genv'.c ∧
   genv.tys ⊑ genv'.tys ∧
   subglobals genv.v genv'.v
   ⇒
   src_orac_invs interp g genv' src_eval
Proof
  simp [src_orac_invs_def, src_orac_env_invs_def, src_orac_gen_inv_def]
  \\ every_case_tac \\ fs []
  \\ rw [] \\ fs []
  \\ metis_tac [global_env_inv_weak]
QED

(* the current generation of envs in the compiler state matches that
   generation in oracle state - this one is tricky, because it will stop
   being true for a while if some declaration are never executed because
   of an exception that is later handled *)
Definition env_gen_rel_def:
  env_gen_rel gen eval_state = (case eval_state of
    | NONE => T
    | SOME (EvalOracle s) =>
        gen.generation = s.generation ∧
        s.generation < LENGTH s.envs ∧
        gen.next = LENGTH (EL s.generation s.envs)
    | _ => F
  )
End

(* the oracle state is in the future, where this generation
   has already been compiled and its environments saved *)
Definition env_gen_future_rel_def:
  env_gen_future_rel interp gen eval_state =
    (case src_orac_next_cfg interp eval_state of
      | SOME c => ? gen_final.
        lookup gen.generation c.envs.env_gens = SOME gen_final /\
        subspt gen.envs gen_final
      | NONE => T)
End

(* indexes and ranges: the source-to-flat compiler allocates names in order.
   however, evaluation order is different to compile order. each block of
   decs is compiled together, but evaluated one at a time, and evaluation may
   call Eval and jump to the processing of another block.
   so, index parameters (idx, end_idx, others) and fin_idx:
     - idx .. end_idx are the indices used in this block
     - fin_idx is the final state after all completed compilation, so the
        indices after fin_idx are still available
       + fin_idx changes with each Eval, so we keep it out of the index tuple
         to make the invariant (and inductive hyps) easier to instantiate
     - other blocks may be on the stack of dec blocks being evaluated
   all of those blocks of indices are disjoint, and they are also disjoint
   from those indices that have actually been initialised. *)
Definition idx_range_rel_def:
  idx_range_rel interp genv s_n_ts s_n_en s_eval idxs ⇔
    ?idx end_idx fin_idx other_blocks.
    idxs = (idx, end_idx, other_blocks) ∧
    (case src_orac_next_cfg interp s_eval of NONE => T
        | SOME c => fin_idx = c.next) ∧
    idx_prev end_idx fin_idx ∧
    ALL_DISJOINT [idx_block idx end_idx; idx_final_block fin_idx; other_blocks;
        genv_allocated_idxs genv] ∧
    (!cn t. t ≥ s_n_ts ⇒ TypeStamp cn t ∉ FRANGE genv.c) ∧
    (!cn. cn ≥ s_n_en ⇒ ExnStamp cn ∉ FRANGE genv.c)
End

(* in eval mode, the length of the allocated globals space will end at the
   next vidx available for the next compilation. if no eval config, we've
   lost that information, but the prior end index will be before *)
Definition fin_idx_match_def:
  fin_idx_match len end_idx next_cfg = (case next_cfg of
    | NONE => end_idx.vidx <= len
    | SOME c => c.next.vidx = len)
End

Definition eval_ref_inv_def:
  eval_ref_inv first_global first_ref <=>
  first_global = [SOME (Loc T 0)] /\
  ?v. first_ref = [Refv v]
End

Definition invariant_def:
  invariant interp g gen genv idxs s s_i1 ⇔
    genv_c_ok genv.c ∧
    genv_c_tys_ok genv.c genv.tys ∧
    s_rel genv s s_i1 ∧
    idx_range_rel interp genv s.next_type_stamp
         s.next_exn_stamp s.eval_state idxs ∧
    src_orac_invs interp g genv s.eval_state ∧
    orac_rel interp g s.eval_state s_i1.eval_config ∧
    genv.v = s_i1.globals ∧
    eval_ref_inv (TAKE 1 s_i1.globals) (TAKE 1 s_i1.refs) ∧
    env_gen_inv gen ∧
    fin_idx_match (LENGTH s_i1.globals) (FST (SND idxs))
        (src_orac_next_cfg interp s.eval_state)
End

(* subsequent oracle config will still have the previous envs in store *)
Definition orac_config_envs_subspt_def:
  orac_config_envs_subspt interp es1 es2 ⇔
    OPTREL (\c c'.  subspt c.envs.env_gens c'.envs.env_gens)
    (src_orac_next_cfg interp es1)
    (src_orac_next_cfg interp es2)
End

Theorem orac_config_envs_subspt_trans:
  orac_config_envs_subspt interp es1 es2 ∧
  orac_config_envs_subspt interp es2 es3 ⇒
  orac_config_envs_subspt interp es1 es3
Proof
  simp [orac_config_envs_subspt_def, OPTREL_def]
  \\ rw [] \\ fs []
  \\ metis_tac [subspt_trans]
QED

Theorem orac_config_envs_subspt_refl:
  orac_config_envs_subspt interp es1 es1
Proof
  simp [orac_config_envs_subspt_def]
QED

(* this relation holds over any successful evaluate or evaluate_decs
   - the eval generation stack will be back to the same generation
*)
Definition eval_state_call_rel_def:
  eval_state_call_rel es1 es2 ⇔
    (case es1 of
      | SOME (EvalOracle s1) => ?s2. es2 = SOME (EvalOracle s2) /\
        s2.generation = s1.generation /\
        LENGTH s1.envs <= LENGTH s2.envs /\
        (!i. i < s1.generation ==> EL i s2.envs = EL i s1.envs)
      | _ => T)
End

Theorem eval_state_call_rel_trans:
  eval_state_call_rel es1 es2 /\ eval_state_call_rel es2 es3 ==>
  eval_state_call_rel es1 es3
Proof
  fs [eval_state_call_rel_def]
  \\ every_case_tac \\ fs []
  \\ rw []
QED

Theorem eval_state_call_rel_refl:
  eval_state_call_rel es1 es1
Proof
  fs [eval_state_call_rel_def]
  \\ every_case_tac \\ fs []
QED

Definition orac_forward_rel_def:
  orac_forward_rel interp es1 es2 <=>
  orac_config_envs_subspt interp es1 es2 /\
  eval_state_call_rel es1 es2
End

Theorem orac_forward_rel_trans:
  orac_forward_rel interp es1 es2 /\ orac_forward_rel interp es2 es3 ==>
  orac_forward_rel interp es1 es3
Proof
  metis_tac [orac_forward_rel_def, orac_config_envs_subspt_trans,
    eval_state_call_rel_trans]
QED

Theorem orac_forward_rel_refl[simp]:
  orac_forward_rel interp es1 es1
Proof
  fs [orac_forward_rel_def, orac_config_envs_subspt_refl,
    eval_state_call_rel_refl]
QED

Theorem can_pmatch_all_IMP_pmatch_rows:
  can_pmatch_all env.c st.refs (MAP FST pes) v /\
  invariant interp g gen genv idxs st s_i1 /\
  env_all_rel genv comp_map env env_i1 locals /\
  v_rel genv v v' ==>
  pmatch_rows
    (compile_pes t (comp_map with v := bind_locals ts locals comp_map.v) pes)
    s_i1 v' ≠ Match_type_error
Proof
  Induct_on `pes`
  \\ fs [pmatch_rows_def,compile_exp_def,FORALL_PROD]
  \\ rw []
  \\ fs [can_pmatch_all_def]
  \\ fs [invariant_def, env_all_rel_cases]
  \\ imp_res_tac (Q.prove (`x <> Match_type_error ==> (?y. x = y)`, simp []))
  \\ drule_then drule (pmatch |> CONJUNCT1)
  \\ rpt (disch_then drule)
  \\ disch_then (qsubterm_then `pmatch _ _ _ _` mp_tac)
  \\ simp [semanticPrimitivesTheory.state_component_equality, v_rel_rules]
  \\ rw []
  \\ imp_res_tac match_result_rel_imp \\ fs [match_result_rel_def]
  \\ TOP_CASE_TAC \\ fs []
QED

val s = mk_var("s",
  ``evaluate$evaluate`` |> type_of |> strip_fun |> #1 |> el 1
  |> type_subst[alpha |-> ``:'ffi``]);

Theorem invariant_globals:
  invariant interp g gen genv idxs s s_i1 ==> s_i1.globals = genv.v
Proof
  simp [invariant_def]
QED

Theorem invariant_genv_c_ok:
  invariant interp g gen genv idxs s s_i1 ==> genv_c_ok genv.c
Proof
  simp [invariant_def]
QED

Theorem invariant_change_clock:
   invariant interp g gen genv env st1 st2 ⇒
   invariant interp g gen genv env (st1 with clock := k) (st2 with clock := k)
Proof
  srw_tac[][invariant_def] >> full_simp_tac(srw_ss())[s_rel_cases]
QED

Theorem invariant_dec_clock:
   invariant interp g gen genv env st1 st2 ⇒
   st1.clock = st2.clock ∧
   invariant interp g gen genv env (dec_clock st1) (dec_clock st2)
Proof
  simp [invariant_def, dec_clock_def, evaluateTheory.dec_clock_def]
  \\ simp [s_rel_cases]
QED

Theorem v_rel_Bool_eqn:
  genv_c_ok genv.c ==> (v_rel genv (Boolv b) v <=> (v = Boolv b))
Proof
  rw [v_rel_eqns, Boolv_def, semanticPrimitivesTheory.Boolv_def, genv_c_ok_def,
    has_bools_def, PULL_EXISTS]
  \\ EQ_TAC \\ fs []
  \\ rw []
  \\ metis_tac []
QED

Theorem evaluate_Bool:
  s_rel genv s s' ∧ genv_c_ok genv.c ==>
  evaluate env s' [Bool t b] = (s', Rval [Boolv b])
Proof
  rw [s_rel_cases, Bool_def]
  \\ simp [evaluate_def]
  \\ fs [genv_c_ok_def, has_bools_def, FDOM_FLOOKUP]
  \\ simp [backend_commonTheory.bool_to_tag_def, Boolv_def]
  \\ every_case_tac
QED

Theorem Boolv_11:
  (Boolv b = Boolv b') = (b = b')
Proof
  simp [Boolv_def] \\ every_case_tac \\ EVAL_TAC
QED

Theorem opt_case_bool_eq[local]:
  option_CASE opt nc scc <=> (opt = NONE /\ nc) \/ (?x. opt = SOME x /\ scc x)
Proof
  Cases_on `opt` \\ simp []
QED

Theorem bind_locals_fold_nsBind:
  nsBind nm (Local t nm) (bind_locals ts locals v_map) =
  bind_locals (t :: ts) (nm :: locals) v_map
Proof
  simp [bind_locals_def, namespaceTheory.nsBindList_def]
QED

Theorem compile_decs_idx_prev:
  !t n next env envs ds n' next' env' envs' ds_i1.
    compile_decs t n next env envs ds = (n', next', env', envs', ds_i1)
    ⇒
    idx_prev next next'
Proof
  ho_match_mp_tac compile_decs_ind >>
  rw [compile_decs_def, idx_prev_def] >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs []
QED

Theorem inc_compile_prog_idx_prev:
  inc_compile_prog env_id c0 decs = (c1, fdecs) ==>
  idx_prev c0.next c1.next
Proof
  simp [inc_compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule compile_decs_idx_prev
  \\ rw []
  \\ simp []
QED

Theorem compile_decs_generation:
  !t n next env envs ds n' next' env' envs' ds_i1.
    compile_decs t n next env envs ds = (n', next', env', envs', ds_i1)
    ⇒
    envs'.generation = envs.generation
Proof
  ho_match_mp_tac compile_decs_ind >>
  rw [compile_decs_def, idx_prev_def] >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs []
QED

Theorem compile_decs_env_gen_inv:
  !t n next env envs ds n' next' env' envs' ds_i1.
    compile_decs t n next env envs ds = (n', next', env', envs', ds_i1) ∧
    env_gen_inv envs
    ⇒
    env_gen_inv envs' ∧
    subspt envs.envs envs'.envs
Proof
  ho_match_mp_tac compile_decs_ind >>
  rw [compile_decs_def, idx_prev_def] >>
  rw [] >>
  rpt (pairarg_tac >> fs []) >>
  fs [env_gen_inv_def] >>
  fsrw_tac [SATISFY_ss] [subspt_trans] >>
  rw [subspt_def, lookup_insert] >>
  imp_res_tac SUBSET_IMP >>
  fs [] >>
  drule_then irule SUBSET_TRANS >>
  irule pred_setTheory.COUNT_MONO >>
  fs []
QED

Theorem v_rel_eqns_non_global[local] =
  v_rel_eqns |> BODY_CONJUNCTS
    |> filter (null o find_terms (can (match_term ``global_env_inv``)) o concl)
    |> map GEN_ALL |> LIST_CONJ

Theorem ALL_DISJOINT_SUBSETS:
  !xs ys. ALL_DISJOINT xs ∧ LIST_REL (\x y. y ⊆ x) xs ys ⇒
  ALL_DISJOINT ys
Proof
  rw [ALL_DISJOINT_DEF, LIST_REL_EL_EQN]
  \\ fs [EXTENSION, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem ALL_DISJOINT_MOVE:
  ! i j mv_set xs ys. ALL_DISJOINT xs ∧
  ys = LUPDATE (EL i xs DIFF mv_set) i (LUPDATE (EL j xs UNION mv_set) j xs) ∧
  mv_set ⊆ EL i xs ∧
  i < LENGTH xs ∧
  j < LENGTH xs
  ⇒
  ALL_DISJOINT ys
Proof
  rw [ALL_DISJOINT_DEF, LIST_REL_EL_EQN, EL_LUPDATE]
  \\ rw []
  \\ fs [EXTENSION, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem idx_range_shrink:
  idx_range_rel i genv nts nes eval_config (l_idx, r_idx, etc) ∧
  idx_prev l_idx l_idx' ∧ idx_prev l_idx' r_idx
  ⇒
  idx_range_rel i genv nts nes eval_config (l_idx', r_idx, etc)
Proof
  rw [idx_range_rel_def]
  \\ TRY asm_exists_tac
  \\ simp []
  \\ drule_then irule ALL_DISJOINT_SUBSETS
  \\ simp [SUBSET_DEF]
  \\ simp [idx_block_def]
  \\ fs [idx_prev_def]
  \\ rw []
QED

Theorem invariant_idx_range_shrink:
  invariant interp g gen genv (l_idx, r_idx, etc) st st' ∧
  idx_prev l_idx l_idx' ∧ idx_prev l_idx' r_idx
  ⇒
  invariant interp g gen genv (l_idx', r_idx, etc) st st'
Proof
  simp [invariant_def]
  \\ metis_tac [idx_range_shrink]
QED

Theorem invariant_idx_range_shrink_gen:
  invariant interp g gen genv (l_idx, r_idx, etc) st st' ∧
  idx_prev l_idx l_idx' ∧ idx_prev l_idx' r_idx ∧
  (env_gen_inv gen ⇒ env_gen_inv gen')
  ⇒
  invariant interp g gen' genv (l_idx', r_idx, etc) st st'
Proof
  rw [invariant_def]
  \\ metis_tac [idx_range_shrink]
QED

Theorem pmatch_invariant:
  invariant interp g gen genv idxs st st' ∧
  env_all_rel genv comp_map2 env env' locals ∧
  comp_map2.c = comp_map.c ∧
  v_rel genv v v' ⇒
  match_result_rel genv [] (pmatch env.c st.refs p v [])
    (pmatch st' (compile_pat comp_map p) v' [])
Proof
  rw [invariant_def]
  \\ `?res. pmatch env.c st.refs p v [] = res` by simp []
  \\ drule_then drule (CONJUNCT1 pmatch)
  \\ simp [semanticPrimitivesTheory.state_component_equality]
  \\ disch_then irule
  \\ simp [v_rel_eqns]
  \\ fs [env_all_rel_cases]
  \\ metis_tac []
QED

Theorem evaluate_make_varls[local]:
  !n t idx vars g g' s env vals len.
    s.globals = g ++ REPLICATE len NONE ++ g' ∧
    LENGTH g = idx ∧
    LENGTH vals = LENGTH vars ∧
    len = LENGTH vars ∧
    (!n. n < LENGTH vals ⇒ ALOOKUP env.v (EL n vars) = SOME (EL n vals))
    ⇒
    flatSem$evaluate env s [make_varls n t idx vars] =
    (s with globals := g ++ MAP SOME vals ++ g', Rval [flatSem$Conv NONE []])
Proof
  ho_match_mp_tac make_varls_ind >>
  rw [make_varls_def, evaluate_def]
  >- fs [state_component_equality]
  >- (
    every_case_tac >>
    fs [] >>
    rfs [do_app_def, state_component_equality, ALOOKUP_NONE] >>
    rw []
    >- (
      imp_res_tac ALOOKUP_MEM >>
      fs [MEM_MAP] >>
      metis_tac [FST])
    >- (
      fs [EL_APPEND_EQN] >>
      `1 = SUC 0` by decide_tac >>
      full_simp_tac bool_ss [REPLICATE] >>
      fs []) >>
    `LENGTH g ≤ LENGTH g` by rw [] >>
    imp_res_tac LUPDATE_APPEND2 >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    `1 = SUC 0` by decide_tac >>
    full_simp_tac bool_ss [REPLICATE] >>
    fs [LUPDATE_compute] >>
    imp_res_tac ALOOKUP_MEM >>
    fs [] >>
    rw [] >>
    Cases_on `vals` >>
    fs [Unitv_def]) >>
  every_case_tac >>
  fs [] >>
  rfs [do_app_def, state_component_equality, ALOOKUP_NONE]
  >- (
    first_x_assum (qspec_then `0` mp_tac) >>
    simp [] >>
    CCONTR_TAC >>
    fs [] >>
    imp_res_tac ALOOKUP_MEM >>
    fs [MEM_MAP] >>
    metis_tac [FST])
  >- fs [EL_APPEND_EQN] >>
  `env with v updated_by opt_bind NONE v = env`
  by rw [environment_component_equality, miscTheory.opt_bind_def] >>
  rw [] >>
 `LENGTH g ≤ LENGTH g` by rw [] >>
  imp_res_tac LUPDATE_APPEND2 >>
  full_simp_tac std_ss [GSYM APPEND_ASSOC] >>
  fs [LUPDATE_compute] >>
  first_x_assum (qspecl_then [`g++[SOME x']`, `g'`, `q`, `env`, `TL vals`] mp_tac) >>
  simp [] >>
  Cases_on `vals` >>
  fs [] >>
  impl_tac
  >- (
    rw [] >>
    first_x_assum (qspec_then `n+1` mp_tac) >>
    simp [GSYM ADD1]) >>
  first_x_assum (qspec_then `0` mp_tac) >>
  rw [state_component_equality]
QED

Theorem EL_APPEND_IF:
  EL i (xs ++ ys) = if i < LENGTH xs then EL i xs else EL (i - LENGTH xs) ys
Proof
  rw [EL_APPEND1, EL_APPEND2]
QED

Theorem ALL_DISJOINT_elem:
  !x i. ALL_DISJOINT xs ∧
  i < LENGTH xs ∧
  x ∈ EL i xs ⇒
  EVERY I (MAPi (\j y. j = i ∨ x ∉ y) xs)
Proof
  simp [ALL_DISJOINT_DEF, EVERY_EL, EXTENSION]
  \\ metis_tac []
QED

Theorem subglobals_NONE:
  subglobals (REPLICATE n NONE) g <=> n <= LENGTH g
Proof
  csimp [subglobals_def, EL_REPLICATE]
QED

Theorem EL_add_SOME_SOME[local]:
  EL i (pre ++ MAP SOME xs ++ post) <> NONE <=>
  (EL i (pre ++ REPLICATE (LENGTH xs) NONE ++ post) <> NONE ∨
    (LENGTH pre <= i ∧ i < LENGTH pre + LENGTH xs))
Proof
  simp [EL_APPEND_IF]
  \\ rw []
  \\ fs [EL_MAP]
QED

Theorem ALOOKUP_alloc_defs_EL[local]:
  !funs l n m.
    ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
    n < LENGTH funs
    ⇒
    ∃tt.
    ALOOKUP (alloc_defs m l (MAP FST (REVERSE funs))) (EL n (MAP FST funs)) =
      SOME (Glob tt (l + LENGTH funs − (n + 1)))
Proof
  gen_tac >>
  Induct_on `LENGTH funs` >>
  rw [] >>
  Cases_on `REVERSE funs` >>
  fs [alloc_defs_def] >>
  rw []
  >- (
    `LENGTH funs = n + 1` suffices_by decide_tac >>
    rfs [EL_MAP] >>
    `funs = REVERSE (h::t)` by metis_tac [REVERSE_REVERSE] >>
    fs [] >>
    rw [] >>
    CCONTR_TAC >>
    fs [] >>
    `n < LENGTH t` by decide_tac >>
    fs [EL_APPEND1, FST_triple] >>
    fs [ALL_DISTINCT_APPEND, MEM_MAP, FORALL_PROD] >>
    fs [MEM_EL, EL_REVERSE] >>
    `PRE (LENGTH t - n) < LENGTH t` by decide_tac >>
    fs [METIS_PROVE [] ``~x ∨ y ⇔ x ⇒ y``] >>
    metis_tac [FST, pair_CASES, PAIR_EQ])
  >- (
    `funs = REVERSE (h::t)` by metis_tac [REVERSE_REVERSE] >>
    fs [] >>
    rw [] >>
    Cases_on `n = LENGTH t` >>
    fs [EL_APPEND2] >>
    `n < LENGTH t` by decide_tac >>
    fs [EL_APPEND1, ADD1] >>
    first_x_assum (qspec_then `REVERSE t` mp_tac) >>
    simp [] >>
    fs [ALL_DISTINCT_APPEND, ALL_DISTINCT_REVERSE, MAP_REVERSE]>>
    disch_then(qspec_then`l+1` assume_tac)>>fs[])
QED

Theorem ALOOKUP_alloc_defs[local]:
  !env x v l tt.
    ALOOKUP (REVERSE env) x = SOME v
    ⇒
    ∃n t.
      ALOOKUP (alloc_defs tt l (MAP FST (REVERSE env))) x = SOME (Glob t (l + n)) ∧
      n < LENGTH (MAP FST env) ∧
      EL n (REVERSE (MAP SOME (MAP SND env))) = SOME v
Proof
  Induct_on `env` >>
  rw [ALOOKUP_APPEND, alloc_defs_append] >>
  every_case_tac >>
  fs [alloc_defs_def]
  >- (
    PairCases_on `h` >>
    fs [EL_APPEND_EQN])
  >- (
    PairCases_on `h` >>
    fs [] >>
    first_x_assum drule >>
    disch_then (qspecl_then [`l`,`tt`] mp_tac) >>
    rw [])
  >- (
    PairCases_on `h` >>
    fs [] >>
    rw [] >>
    fs [ALOOKUP_NONE, MAP_REVERSE] >>
    drule ALOOKUP_MEM >>
    rw [] >>
    `MEM h0 (MAP FST (alloc_defs tt l (REVERSE (MAP FST env))))`
      by (rw [MEM_MAP] >> metis_tac [FST]) >>
    fs [fst_alloc_defs])
  >- (
    first_x_assum drule >>
    disch_then (qspecl_then [`l`,`tt`] mp_tac) >>
    rw [EL_APPEND_EQN])
QED

Theorem global_env_inv_extend[local]:
  !pat_env genv pat_env' tt g1 g2.
    env_rel genv (alist_to_ns pat_env) pat_env' ∧
    genv.v = g1 ⧺ MAP SOME (REVERSE (MAP SND pat_env')) ⧺ g2 ∧
    ALL_DISTINCT (MAP FST pat_env)
    ⇒
    global_env_inv genv
      <|c := nsEmpty;
        v := alist_to_ns (alloc_defs tt (LENGTH g1) (REVERSE (MAP FST pat_env')))|>
      ∅
      <|v := alist_to_ns pat_env; c := nsEmpty|>
Proof
  rw [v_rel_global_eqn, extend_dec_env_def, extend_env_def,
      nsLookup_nsAppend_some, nsLookup_alist_to_ns_some] >>
  rfs [Once (GSYM alookup_distinct_reverse)] >>
  drule ALOOKUP_alloc_defs >>
  disch_then (qspecl_then [`LENGTH g1`, `tt`] strip_assume_tac) >>
  drule env_rel_dom >>
  fs [env_rel_el] >>
  rw [] >>
  fs [MAP_REVERSE, PULL_EXISTS] >>
  rw [EL_APPEND_EQN] >>
  rw [EL_REVERSE, EL_MAP] >>
  irule v_rel_weak >>
  qexists_tac `genv` >>
  rw [subglobals_def] >>
  fs [EL_APPEND_EQN] >>
  rw [] >>
  fs [EL_REPLICATE] >>
  rfs [EL_REVERSE, EL_MAP] >>
  rw []
QED

Theorem LIST_REL_sv_rel_weak:
  LIST_REL (sv_rel genv) vs vs' ∧
  subglobals genv.v genv'.v ∧
  genv.c ⊑ genv'.c ∧
  genv.tys ⊑ genv'.tys ⇒
  LIST_REL (sv_rel genv') vs vs'
Proof
  rw []
  \\ irule LIST_REL_mono
  \\ simp [Once CONJ_COMM]
  \\ asm_exists_tac
  \\ rw []
  \\ drule_then irule sv_rel_weak
  \\ simp []
QED

Theorem idx_range_rel_v_REPLICATE_NONE:
  idx_range_rel interp genv nts nes eval_state (idx, end_idx, others) ∧
  fin_idx_match (LENGTH genv.v) end_idx
        (src_orac_next_cfg interp eval_state) ∧
  n + idx.vidx <= end_idx.vidx
  ==>
  ?pre post. genv.v = pre ++ REPLICATE n NONE ++ post ∧
    LENGTH pre = idx.vidx
Proof
  rw [idx_range_rel_def]
  \\ qexists_tac `TAKE idx.vidx genv.v`
  \\ qexists_tac `DROP (idx.vidx + n) genv.v`
  \\ fs [idx_prev_def]
  \\ `idx.vidx + n <= LENGTH genv.v`
    by (every_case_tac \\ fs [fin_idx_match_def])
  \\ qsuff_tac `!i. idx.vidx <= i /\ i < n + idx.vidx ==> EL i genv.v = NONE`
  >- (
    REWRITE_TAC [GSYM LIST_REL_eq, LIST_REL_EL_EQN]
    \\ simp [EL_APPEND_IF]
    \\ rw [] \\ rw []
    \\ simp [EL_TAKE, EL_REPLICATE, EL_DROP]
  )
  \\ rw []
  \\ qspecl_then [`(i, Idx_Var)`, `0`] drule ALL_DISJOINT_elem
  \\ simp [idx_block_def, genv_allocated_idxs_def, DISJ_EQ_IMP]
QED

Theorem invariant_make_varls:
  invariant interp g gen genv (idx, end_idx, others) st st' ∧
  idx.vidx = vidx ∧
  idx.vidx + LENGTH vars <= end_idx.vidx ∧
  vars = REVERSE (MAP FST env.v) ∧
  ALL_DISTINCT (MAP FST env.v)
  ⇒
  ?genv' st''.
  evaluate env st' [make_varls n t vidx vars] = (st'', Rval [Unitv]) ∧
  invariant interp g gen genv' (idx with vidx := idx.vidx + LENGTH vars, end_idx, others)
    st st'' ∧
  genv'.c = genv.c ∧
  genv'.tys = genv.tys ∧
  subglobals genv.v genv'.v ∧
  (!env1 tt. env_rel genv' (alist_to_ns env1) env.v ⇒
    global_env_inv genv'
      <|c := nsEmpty;
        v := alist_to_ns (alloc_defs tt vidx (REVERSE (MAP FST env.v)))|>
      ∅
      <|v := alist_to_ns env1; c := nsEmpty|>
  )
Proof
  rw []
  \\ Cases_on `env.v = []`
  >- (
    fs [make_varls_def, evaluate_def, Unitv_def]
    \\ simp [Q.prove (`n with vidx := n.vidx = n`,
        simp [next_indices_component_equality])]
    \\ asm_exists_tac
    \\ rw [subglobals_refl, alloc_defs_def]
    \\ fs [env_rel_LIST_REL]
    \\ simp [v_rel_global_eqn]
  )
  \\ fs [invariant_def]
  \\ drule idx_range_rel_v_REPLICATE_NONE
  \\ fs [LENGTH_REVERSE]
  \\ disch_then drule
  \\ rw []
  \\ drule_then drule evaluate_make_varls
  \\ disch_then (qsubterm_then `evaluate _ _ _ ` mp_tac)
  \\ disch_then (qspec_then `REVERSE (MAP SND env.v)` mp_tac)
  \\ simp []
  \\ impl_tac
  >- (
    rw []
    \\ simp [GSYM MAP_REVERSE, EL_MAP, EL_REVERSE]
    \\ simp [ALOOKUP_ALL_DISTINCT_EL]
  )
  \\ rw []
  \\ simp [Unitv_def]
  \\ qexists_tac `genv with v :=
    pre ++ MAP SOME (REVERSE (MAP SND env.v)) ++ post`
  \\ simp [subglobals_refl_append, subglobals_NONE]
  \\ rpt conj_tac
  >- (
    fs [s_rel_cases]
    \\ drule_then irule LIST_REL_sv_rel_weak
    \\ simp [subglobals_refl_append, subglobals_NONE]
  )
  >- (
    fs [idx_range_rel_def]
    \\ TRY asm_exists_tac
    \\ simp [genv_allocated_idxs_def, EL_add_SOME_SOME]
    \\ drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE)
    \\ simp []
    \\ qexists_tac `{(i, Idx_Var) | idx.vidx <= i /\ i < idx.vidx + LENGTH env.v}`
    \\ simp [LUPDATE_compute]
    \\ simp [EXTENSION, FORALL_PROD, idx_types_FORALL, idx_block_def,
        SUBSET_DEF, genv_allocated_idxs_def]
    \\ rw []
    \\ EQ_TAC \\ rw []
    \\ simp []
  )
  >- (
    drule_then irule src_orac_invs_weak
    \\ simp [subglobals_refl_append, subglobals_NONE]
  )
  >- (
    fs [TAKE_APPEND, eval_ref_inv_def]
    \\ Cases_on `pre` \\ fs []
    \\ fs [Q.ISPEC `0 : num` EQ_SYM_EQ]
    \\ Cases_on `env.v` \\ fs []
  )
  >- (
    fs [fin_idx_match_def]
  )
  >- (
    rw []
    \\ qpat_assum `LENGTH _ = _.vidx` (fn t => REWRITE_TAC [GSYM t])
    \\ irule global_env_inv_extend
    \\ imp_res_tac env_rel_dom
    \\ fs []
  )
QED

Theorem compile_funs_dom2:
  MAP FST (compile_funs t env funs) = MAP FST funs
Proof
  qspec_then `funs` mp_tac source_to_flatTheory.compile_funs_dom
  \\ simp [ELIM_UNCURRY, ETA_THM]
QED

Theorem genv_c_ok_extend:
  genv_c_ok c ∧
  (! cn arity stamp. FLOOKUP c_ext (cn, arity) = SOME stamp ⇒
    (same_type (ExnStamp 0) stamp <=> SND cn = NONE) ∧
    (! cn' arity' stamp'. FLOOKUP c_ext (cn', arity') = SOME stamp' ⇒
      (same_type stamp stamp' <=> ctor_same_type (SOME cn) (SOME cn')) ∧
      (stamp = stamp' ⇒ (cn = cn' ∧ arity = arity'))) ∧
    (! cn' arity' stamp'. FLOOKUP c (cn', arity') = SOME stamp' ⇒
      stamp <> stamp' ∧
      (SND cn <> NONE ⇒ SND cn <> SND cn') ∧
      (! s s' n. stamp = TypeStamp s n ⇒ stamp' <> TypeStamp s' n)))
  ⇒
  genv_c_ok (FUNION c c_ext)
Proof
  rw []
  \\ fs [genv_c_ok_def]
  \\ qsuff_tac `! cn arity stamp. FLOOKUP c (cn, arity) = SOME stamp ⇒
        (same_type (ExnStamp 0) stamp <=> SND cn = NONE)`
  \\ simp [FORALL_PROD]
  \\ rpt (disch_tac ORELSE conj_tac)
  >- fs [has_bools_def, FLOOKUP_FUNION]
  >- fs [has_exns_def, FLOOKUP_FUNION]
  >- fs [has_lists_def, FLOOKUP_FUNION]
  >- (
    (* ctor same type *)
    rw []
    \\ fs [FLOOKUP_FUNION, option_case_eq]
    \\ res_tac
    \\ fs [semanticPrimitivesTheory.ctor_same_type_def, same_type_def,
            ctor_same_type_def]
    \\ fs [ctor_same_type_refl]
    \\ Cases_on `stamp1` \\ Cases_on `stamp2`
    \\ fs [semanticPrimitivesTheory.ctor_same_type_def, same_type_def,
            ctor_same_type_def]
    \\ rfs []
  )
  >- (
    rpt (gen_tac ORELSE disch_tac)
    \\ fs [FLOOKUP_FUNION, option_case_eq]
    \\ res_tac
    \\ fs []
  )
  >- (
    fs [has_exns_def, FORALL_PROD]
    \\ rw []
    \\ last_x_assum drule
    \\ disch_then (qspec_then `div_tag` drule)
    \\ simp [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def]
    \\ Cases_on `stamp`
    \\ simp [semanticPrimitivesTheory.div_stamp_def, same_type_def]
  )
QED

Theorem genv_c_tys_ok_extend:
  genv_c_tys_ok c tys ∧
  genv_c_tys_ok c_ext tys_ext ∧
  DISJOINT (FDOM tys) (FDOM tys_ext)
  ⇒
  genv_c_tys_ok (FUNION c c_ext) (FUNION tys tys_ext)
Proof
  rw [genv_c_tys_ok_def]
  \\ res_tac
  \\ TRY (simp [FLOOKUP_FUNION] \\ NO_TAC)
  \\ drule_then (fn t => REWRITE_TAC [t]) FUNION_COMM
  \\ simp [FLOOKUP_FUNION]
QED

Theorem maybe_all_list_SOME:
  !xs ys. maybe_all_list xs = SOME ys ==> xs = MAP SOME ys
Proof
  Induct \\ simp [Once maybe_all_list_def]
  \\ rw []
  \\ every_case_tac
  \\ fs []
  \\ rveq \\ fs []
QED

Theorem some_f_inj_eq:
  INJ f UNIV UNIV /\ y = f x
  ==>
  (some x. y = f x) = SOME x
Proof
  DEEP_INTRO_TAC some_intro \\ fs[]
  \\ rw []
  \\ rfs [INJ_DEF]
QED

Theorem v_to_word8_list_rel:
  v_to_word8_list bytes_v = SOME bytes /\
  v_rel genv bytes_v v' /\
  genv_c_ok genv.c ==>
  v_to_bytes v' = SOME bytes
Proof
  rw [v_to_word8_list_def]
  \\ fs [case_eq_thms]
  \\ drule_then drule v_to_list
  \\ drule maybe_all_list_SOME
  \\ rw [v_to_bytes_def]
  \\ simp []
  \\ irule some_f_inj_eq
  \\ simp [INJ_DEF, INJ_MAP_EQ_IFF]
  \\ fs [LIST_REL_EL_EQN, LIST_EQ_REWRITE]
  \\ rfs []
  \\ rw []
  \\ rpt (first_x_assum drule)
  \\ simp [v_to_word8_def, EL_MAP]
  \\ every_case_tac \\ simp [v_rel_eqns]
QED

Theorem v_to_word64_list_rel:
  v_to_word64_list words_v = SOME words /\
  v_rel genv words_v v' /\
  genv_c_ok genv.c ==>
  v_to_words v' = SOME words
Proof
  rw [v_to_word64_list_def]
  \\ fs [case_eq_thms]
  \\ drule_then drule v_to_list
  \\ drule maybe_all_list_SOME
  \\ rw [v_to_words_def]
  \\ simp []
  \\ irule some_f_inj_eq
  \\ simp [INJ_DEF, INJ_MAP_EQ_IFF]
  \\ fs [LIST_REL_EL_EQN, LIST_EQ_REWRITE]
  \\ rfs []
  \\ rw []
  \\ rpt (first_x_assum drule)
  \\ simp [v_to_word64_def, EL_MAP]
  \\ every_case_tac \\ simp [v_rel_eqns]
QED

Theorem keep_glob_alloc:
  flat_elim$keep calc (glob_alloc next st)
Proof
  simp [glob_alloc_def, flat_elimTheory.keep_def, flat_elimTheory.is_pure_def]
QED

Theorem inc_compile_prog_nonempty:
  inc_compile_prog env_id st decs = (st', fdecs) ==> fdecs ≠ []
Proof
  rw [inc_compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
QED

Theorem src_orac_env_invs_lookup_env:
  lookup_env es env_id = SOME env /\
  src_orac_env_invs interp genv (SOME (EvalOracle es)) /\
  es.oracle 0 = (env_id,st_v,decs)
  ==>
  ? c x gen comp_map.
  (THE interp) st_v = SOME (c, x) /\
  lookup (FST env_id) c.envs.env_gens = SOME gen /\
  lookup (SND env_id) gen = SOME comp_map /\
  global_env_inv genv comp_map {} env
Proof
  PairCases_on `env_id`
  \\ rw [lookup_env_def, case_eq_thms]
  \\ fs [src_orac_invs_def, src_orac_env_invs_def, src_orac_next_cfg_def,
        src_orac_next_cfg_inner_def]
  \\ every_case_tac \\ fs []
  \\ rfs []
  \\ fs [oEL_THM]
  \\ rveq \\ fs []
  \\ first_x_assum (drule_then drule)
  \\ rw [] \\ simp []
QED

Theorem FST_SND_EQ_CASE[local]:
  FST = (\ (a, b). a) /\ SND = (\ (a, b). b)
Proof
  simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem step_1[local]:
  src_orac_step_invs interp g (SOME (EvalOracle es)) ==>
  ? i_f env_id0 st_v0 decs0 fdecs0 c0 x0 env_id1 st_v1 decs1 c1 x1.
  interp = SOME i_f /\
  es.oracle 0 = (env_id0, st_v0, decs0) /\
  es.oracle 1 = (env_id1, st_v1, decs1) /\
  i_f st_v0 = SOME (c0, x0) /\
  i_f st_v1 = SOME (c1, x1) /\
  inc_compile_prog env_id0 c0 (g decs0) = (c1, fdecs0) /\
  src_orac_next_cfg (SOME i_f) (SOME (EvalOracle es)) = SOME c0
Proof
  rw []
  \\ simp [PAIR_FST_SND_EQ, FST_SND_EQ_CASE]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ fs [src_orac_step_invs_def, EXISTS_PROD]
  \\ every_case_tac \\ fs []
  \\ res_tac
  \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rfs []
  \\ fs []
  \\ simp [src_orac_next_cfg_def, src_orac_next_cfg_inner_def]
QED

Theorem subglobals_add_NONE:
  subglobals gs (gs ++ REPLICATE n NONE)
Proof
  simp [subglobals_def, EL_APPEND_IF]
QED

Theorem do_eval:
  !vs'.
  do_eval vs s.eval_state = SOME (env, decs, eval_state) /\
  invariant interp g gen genv idxs s t /\
  LIST_REL (v_rel genv) vs vs'
  ==>
  ?genv' env_id c decs' eval_config' c' idx end_idx fin_idx other.
  idxs = (idx, end_idx, other) /\
  do_eval (DROP 4 vs') t.eval_config = SOME (decs', eval_config', Unitv) /\
  LENGTH vs' = 6 /\
  inc_compile_prog env_id c decs = (c', decs') /\
  decs' <> [] /\
  invariant interp g <|next := 0; generation := c.envs.next; envs := LN|> genv'
    (c.next, c'.next, idx_block idx end_idx ∪ other)
    (s with eval_state := eval_state) (t with <| eval_config := eval_config';
        globals := t.globals ++ REPLICATE (c'.next.vidx - c.next.vidx) NONE |>)
  /\
  env_gen_rel <|next := 0; generation := c.envs.next; envs := LN|> eval_state /\
  (let (_, _, _, gen, _) = compile_decs [] 1 c.next
    (lookup_env_id env_id c.envs)
    <|next := 0; generation := c.envs.next; envs := LN|> decs in
    env_gen_future_rel interp gen eval_state) /\
  global_env_inv genv' (lookup_env_id env_id c.envs) ∅ env /\
  src_orac_next_cfg interp eval_state = SOME c' /\
  idx_prev end_idx c'.next /\
  genv.c ⊑ genv'.c /\
  genv.tys ⊑ genv'.tys /\
  subglobals genv.v genv'.v /\
  orac_config_envs_subspt interp s.eval_state eval_state ∧
  (case s.eval_state of SOME (EvalOracle s) =>
    ?s'. eval_state = SOME (EvalOracle s') /\
    s'.envs = (add_env_generation s).envs /\
    s'.generation = (add_env_generation s).generation
    | _ => F
  )
Proof
  rw [semanticPrimitivesTheory.do_eval_def, do_eval_def]
  \\ fs [case_eq_thms, invariant_def]
  \\ rfs [CaseEq "eval_state"]
  \\ imp_res_tac orac_rel_SOME_eval
  \\ fs [orac_rel_def]
  \\ rveq \\ fs []
  \\ fs [source_evalProofTheory.do_eval_oracle_def]
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [case_eq_thms, pair_case_eq]
  \\ rveq \\ fs []
  \\ drule_then drule v_to_word64_list_rel
  \\ drule_then drule v_to_word8_list_rel
  \\ rw []
  \\ fs []
  \\ every_case_tac \\ fs []
  \\ PairCases_on `idxs` \\ fs []
  \\ imp_res_tac orac_rel_inner_def
  \\ fs [src_orac_invs_def]
  \\ drule step_1
  \\ rw []
  \\ fs [] \\ rfs []
  \\ drule inc_compile_prog_nonempty
  \\ rw []
  \\ goal_assum (first_assum o mp_then (Pat `inc_compile_prog _ _ _ = _`) mp_tac)
  \\ simp [EVAL ``(add_env_generation s).envs``,
        EVAL ``(add_env_generation s).generation``]
  \\ qmatch_goalsub_abbrev_tac `src_orac_next_cfg (SOME i_f) (SOME es2) = SOME c1`
  \\ `src_orac_next_cfg (SOME i_f) (SOME es2) = SOME c1`
    by (
    fs [src_orac_next_cfg_def, markerTheory.Abbrev_def, add_env_generation_def,
        src_orac_next_cfg_inner_def, shift_seq_def]
  )
  \\ fs []
  \\ imp_res_tac inc_compile_prog_idx_prev
  \\ fsrw_tac [SATISFY_ss] [idx_prev_trans]
  \\ qexists_tac `genv with
    <| v := genv.v ++ REPLICATE (c1.next.vidx - c0.next.vidx) NONE |>`
  \\ simp []
  \\ `subglobals t.globals (t.globals ++ REPLICATE (c1.next.vidx - c0.next.vidx) NONE)`
    by simp [subglobals_add_NONE]
  \\ simp [env_gen_inv_def]
  \\ rpt conj_tac
  >- (
    simp [shift_seq_def]
    \\ fs [orac_rel_inner_def]
    \\ first_x_assum (qspec_then `1` drule)
    \\ simp []
  )
  >- (
    fs [s_rel_cases]
    \\ drule_then irule LIST_REL_sv_rel_weak
    \\ simp []
  )
  >- (
    fs [idx_range_rel_def, genv_allocated_idxs_def,
        add_env_generation_def, idx_prev_refl]
    \\ qspecl_then [`0`, `2`] drule ALL_DISJOINT_MOVE
    \\ simp []
    \\ disch_then (qspec_then `idx_block idxs0 idxs1` mp_tac)
    \\ rw [LUPDATE_compute]
    \\ qspecl_then [`1`, `0`] drule ALL_DISJOINT_MOVE
    \\ disch_then (qspec_then `idx_block c0.next c1.next` mp_tac)
    \\ simp [LUPDATE_compute]
    \\ impl_tac
    >- (
      simp [idx_block_def, idx_final_block_def]
      \\ simp [SUBSET_DEF, PULL_EXISTS]
    )
    \\ rw []
    \\ csimp [EL_APPEND_IF, bool_case_eq, EL_REPLICATE]
    \\ drule_then irule ALL_DISJOINT_SUBSETS
    \\ simp [SUBSET_DEF, PULL_EXISTS, EL_APPEND_IF, bool_case_eq]
    \\ simp [idx_final_block_def, idx_block_def]
    \\ fs [idx_prev_def, idx_types_FORALL, FORALL_PROD]
  )
  >- (
    fs [markerTheory.Abbrev_def, add_env_generation_def]
    \\ fs [src_orac_step_invs_def, shift_seq_def]
    \\ rw []
    \\ res_tac
    \\ fs [GSYM SUC_ADD_SYM]
  )
  >- (
    fs [markerTheory.Abbrev_def, add_env_generation_def]
    \\ fs [src_orac_env_invs_def]
    \\ simp [src_orac_next_cfg_def, src_orac_next_cfg_inner_def, shift_seq_def]
    \\ imp_res_tac inc_compile_prog_env_submap
    \\ rfs []
    \\ rveq \\ fs []
    \\ rw [EL_APPEND_IF]
    >- (
      fs [inc_compile_prog_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
    )
    >- (
      res_tac
      \\ imp_res_tac subspt_lookup
      \\ fs []
      \\ drule_then irule global_env_inv_weak
      \\ simp []
    )
    >- (
      rfs [EL_CONS_IF]
    )
  )
  >- (
    fs [src_orac_gen_inv_def, markerTheory.Abbrev_def, add_env_generation_def]
  )
  >- (
    fs [markerTheory.Abbrev_def, add_env_generation_def, orac_rel_inner_def]
    \\ qexists_tac `s_compiler`
    \\ rw [shift_seq_def]
    \\ fsrw_tac [SATISFY_ss] []
  )
  >- (
    Cases_on `t.globals` \\ fs [eval_ref_inv_def]
  )
  >- (
    fs [fin_idx_match_def, idx_prev_def]
  )
  >- (
    fs [markerTheory.Abbrev_def, add_env_generation_def, env_gen_rel_def]
    \\ rveq \\ fs []
    \\ simp [EL_APPEND_IF]
    \\ fs [src_orac_env_invs_def]
  )
  >- (
    fs [inc_compile_prog_def, markerTheory.Abbrev_def, add_env_generation_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ simp [env_gen_future_rel_def, src_orac_next_cfg_def]
    \\ rfs [src_orac_next_cfg_def]
    \\ rveq \\ fs []
    \\ imp_res_tac compile_decs_generation
    \\ fs []
    \\ simp [subspt_def, lookup_insert, bool_case_eq]
    \\ imp_res_tac compile_decs_env_gen_inv
    \\ fs [env_gen_inv_def]
    \\ rw []
    \\ imp_res_tac SUBSET_IMP
    \\ fs []
  )
  >- (
    drule_then drule src_orac_env_invs_lookup_env
    \\ rw []
    \\ simp [lookup_env_id_def]
    \\ drule_then irule global_env_inv_weak
    \\ simp []
  )
  >- (
    fs [idx_range_rel_def]
    \\ fsrw_tac [SATISFY_ss] [idx_prev_trans]
  )
  >- (
    fs [markerTheory.Abbrev_def, add_env_generation_def]
    \\ fs [orac_config_envs_subspt_def, src_orac_next_cfg_def]
    \\ rfs [OPTREL_def]
    \\ drule inc_compile_prog_env_submap
    \\ fs [src_orac_env_invs_def, src_orac_next_cfg_def]
    \\ rfs []
    \\ fs []
  )
QED

Theorem invariant_end_eval:
  invariant interp g gen' genv (x, end_idx1, idx_block idx end_idx ∪ other) st st' ∧
  invariant interp g gen prev_genv (idx, end_idx, other) prev_st prev_st' ∧
  orac_forward_rel interp begin_eval_state st.eval_state ∧
  idx_prev end_idx end_idx1 ∧
  orac_config_envs_subspt interp prev_st.eval_state begin_eval_state ∧
  (case prev_st.eval_state of SOME (EvalOracle s) =>
    ?s'. begin_eval_state = SOME (EvalOracle s') ∧
    s'.envs = (add_env_generation s).envs ∧
    s'.generation = (add_env_generation s).generation
    | _ => F
  )
  ⇒
  invariant interp g gen genv (idx, end_idx, other) (st with
        eval_state := reset_env_generation prev_st.eval_state st.eval_state)
    st' ∧
  orac_forward_rel interp prev_st.eval_state
    (reset_env_generation prev_st.eval_state st.eval_state) ∧
  (env_gen_rel gen prev_st.eval_state ⇒
    env_gen_rel gen (reset_env_generation prev_st.eval_state st.eval_state))
Proof
  every_case_tac \\ fs []
  \\ rpt disch_tac
  \\ fs [invariant_def, src_orac_invs_def]
  \\ Cases_on `interp`
  >- (
    fs [src_orac_step_invs_def, orac_forward_rel_def] \\ rfs []
  )
  \\ fs [orac_forward_rel_def, eval_state_call_rel_def]
  \\ fs [reset_env_generation_def]
  \\ rfs [src_orac_next_cfg_def]
  \\ rw []
  \\ TRY (fs [src_orac_env_invs_def, src_orac_next_cfg_def, s_rel_cases, fin_idx_match_def]
    \\ NO_TAC)
  >- (
    fs [idx_range_rel_def, src_orac_next_cfg_def]
    \\ qexists_tac `fin_idx`
    \\ fsrw_tac [SATISFY_ss] [idx_prev_trans]
    \\ drule (Q.SPECL [`2`, `0`, `mv_set`, `[_; _; mv_set ∪ other; _]`]
          ALL_DISJOINT_MOVE)
    \\ rw [LUPDATE_compute]
    \\ drule_then irule ALL_DISJOINT_SUBSETS
    \\ simp [SUBSET_DEF, PULL_EXISTS]
    \\ imp_res_tac (Q.SPECL [`x`, `2`] ALL_DISJOINT_elem)
    \\ fs []
  )
  >- (
    fsrw_tac [SATISFY_ss] [src_orac_step_invs_def]
  )
  >- (
    fs [src_orac_gen_inv_def, add_env_generation_def]
  )
  >- (
    fs [orac_rel_def, orac_rel_inner_def]
    \\ qexists_tac `s_compiler`
    \\ fsrw_tac [SATISFY_ss] []
  )
  >- (
    fs [fin_idx_match_def]
    \\ imp_res_tac step_1 \\ fs []
    \\ every_case_tac \\ fs []
    \\ rfs [src_orac_next_cfg_def]
  )
  >- (
    drule_then irule orac_config_envs_subspt_trans
    \\ drule_then irule orac_config_envs_subspt_trans
    \\ simp [orac_config_envs_subspt_def, src_orac_next_cfg_def]
    \\ every_case_tac \\ simp []
  )
  >- (
    fs [add_env_generation_def]
  )
  >- (
    fs [add_env_generation_def, src_orac_gen_inv_def]
    \\ fs [EL_APPEND_IF]
  )
  >- (
    fs [env_gen_rel_def, add_env_generation_def, EL_APPEND_IF]
  )
QED

Theorem alloc_tags1_imp:
  ! ctors ns spt tag_list.
  alloc_tags1 ctors = (ns, spt, tag_list) ∧
  ALL_DISTINCT (MAP FST ctors) ==>
  ? cn_tags.
  ns = alist_to_ns (MAP (\ (cn, tag, arity). (cn, tag)) cn_tags) ∧
  set (MAP SND cn_tags) = {(tag, arity) |
    ∃max. lookup arity spt = SOME max ∧ tag < max} ∧
  tag_list = MAP SND cn_tags ∧
  ALL_DISTINCT tag_list ∧
  LIST_REL (\ (cn, ts) (cn', _, arity). cn = cn' ∧ arity = LENGTH ts)
    ctors cn_tags ∧
  MAP FST ctors = MAP FST cn_tags
Proof
  ho_match_mp_tac alloc_tags1_ind
  \\ simp [alloc_tags1_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ simp [PULL_EXISTS, EXISTS_PROD, lookup_def]
  \\ qexists_tac `cn_tags`
  \\ fs [lookup_inc_def, option_case_eq] \\ rveq \\ fs []
  \\ simp [EVERY_MEM, MEM_MAP, FORALL_PROD, EXISTS_PROD]
  \\ simp [lookup_insert, EXTENSION]
  \\ rw [] \\ EQ_TAC \\ rw []
  \\ rw [] \\ fs []
  \\ fs [bool_case_eq, Q.ISPEC `SOME v` EQ_SYM_EQ]
QED

(* FIXME also in flat_pattern *)
Theorem ALOOKUP_MAP_3:
  (!x. MEM x xs ==> FST (f x) = FST x) ==>
  ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x, y))) (ALOOKUP xs x)
Proof
  Induct_on `xs` \\ rw []
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM]
  \\ Cases_on `f h`
  \\ Cases_on `h`
  \\ rw []
  \\ fs []
QED

Theorem alloc_tags_invariant:
  alloc_tags idx.tidx (ctors : (mlstring # ast_t list) list) = (ns, cids) ∧
  invariant interp g gen genv (idx, end_idx, os) st st' ∧
  global_env_inv genv comp_map {} env ∧
  ALL_DISTINCT (MAP FST ctors) ∧
  idx.tidx + 1 <= end_idx.tidx
  ⇒
  ?genv'.
  genv.c ⊑ genv'.c ∧
  genv.tys ⊑ genv'.tys ∧
  genv'.v = genv.v ∧
  invariant interp g gen genv' (idx with tidx := idx.tidx + 1, end_idx, os)
    (st with next_type_stamp := st.next_type_stamp + 1) st' ∧
  (let build_env = <| c := alist_to_ns
        (REVERSE (build_constrs st.next_type_stamp ctors)); v := nsEmpty |> in
   global_env_inv genv' <| c := ns; v := nsEmpty |> {} build_env ∧
   env_domain_eq <|c := ns; v := nsEmpty|> build_env)
Proof
  rw [invariant_def]
  \\ fs [s_rel_cases]
  \\ fs [alloc_tags_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ Cases_on `ctors = []`
  >- (
    fs [alloc_tags1_def] \\ rveq \\ fs []
    \\ qexists_tac `genv`
    \\ simp [lookup_def, build_constrs_def, v_rel_cases, env_domain_eq_def]
    \\ fs [idx_range_rel_def]
    \\ asm_exists_tac
    \\ simp []
    \\ drule_then irule ALL_DISJOINT_SUBSETS
    \\ simp []
    \\ simp [SUBSET_DEF, idx_block_def]
    \\ rw []
  )
  \\ drule alloc_tags1_imp
  \\ rw [MAP_REVERSE]
  \\ `? r_ctors. ctors = REVERSE r_ctors`
    by metis_tac [REVERSE_REVERSE]
  \\ fs [MAP_REVERSE]
  \\ qexists_tac `genv with <| c := FUNION genv.c (alist_to_fmap
        (MAP (\(cn, tag, arity). (((tag, SOME idx.tidx), arity),
            TypeStamp cn st.next_type_stamp)) cn_tags));
        tys := FUNION genv.tys (alist_to_fmap [(idx.tidx, MAP SND (REVERSE cn_tags))])
    |>`
  \\ rw [SUBMAP_FUNION_ID]
  >- (
    drule_then irule genv_c_ok_extend
    \\ rw [FORALL_PROD]
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs [MEM_MAP, EXISTS_PROD] \\ rveq \\ fs []
    \\ simp [same_type_def, ctor_same_type_def]
    \\ rveq \\ fs []
    \\ imp_res_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM
    \\ fs []
    \\ TRY strip_tac
    \\ rveq \\ fs []
    \\ fs [idx_range_rel_def, genv_allocated_idxs_def]
    \\ rfs [FRANGE_FLOOKUP]
    \\ qspecl_then [`(i,Idx_Type)`, `0`] drule ALL_DISJOINT_elem
    \\ simp [idx_block_def]
    \\ qexists_tac `idx.tidx`
    \\ simp [FDOM_FLOOKUP]
    \\ metis_tac []
  )
  >- (
    irule genv_c_tys_ok_extend
    \\ simp [genv_c_tys_ok_def]
    \\ conj_tac
    >- (
      fs [idx_range_rel_def, genv_c_tys_ok_def, genv_allocated_idxs_def]
      \\ qspecl_then [`(i,Idx_Type)`, `0`] drule ALL_DISJOINT_elem
      \\ simp []
      \\ disch_then (qspec_then `idx.tidx` mp_tac)
      \\ simp [idx_block_def]
    )
    \\ simp [genv_c_tys_ok_def, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ simp [FLOOKUP_UPDATE, MEM_MAP, EXISTS_PROD]
    \\ metis_tac []
  )
  >- (
    drule_then irule LIST_REL_sv_rel_weak
    \\ simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    fs [idx_range_rel_def, genv_allocated_idxs_def]
    \\ asm_exists_tac
    \\ rw []
    \\ fs [FRANGE_FLOOKUP, FLOOKUP_FUNION, option_case_eq, FLOOKUP_UPDATE]
    \\ TRY (CCONTR_TAC \\ fs [] \\ imp_res_tac ALOOKUP_MEM
      \\ fs [MEM_MAP, EXISTS_PROD] \\ NO_TAC)
    \\ drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE)
    \\ simp [LUPDATE_compute]
    \\ qexists_tac `{(idx.tidx, Idx_Type)}`
    \\ simp [EXTENSION, FORALL_PROD, idx_types_FORALL, idx_block_def]
    \\ simp [MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ rw [] \\ EQ_TAC \\ rw []
    \\ fs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs [EXISTS_PROD]
    \\ metis_tac []
  )
  >- (
    drule_then irule src_orac_invs_weak
    \\ simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    simp [build_constrs_def, MAP_REVERSE]
    \\ simp [Once v_rel_cases]
    \\ rw [nsLookup_alist_to_ns_some]
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs [MEM_MAP, EXISTS_PROD] \\ rveq \\ fs []
    \\ simp [MAP_MAP_o, o_DEF, ELIM_UNCURRY]
    \\ drule_then drule LIST_REL_MEM_IMP
    \\ rw [EXISTS_PROD]
    \\ imp_res_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM
    \\ simp [ALOOKUP_MAP_3, FLOOKUP_FUNION]
    \\ simp [option_case_eq, ALOOKUP_MAP_3]
    \\ rfs [idx_range_rel_def, FLOOKUP_UPDATE, genv_allocated_idxs_def]
    \\ qspecl_then [`(i,Idx_Type)`, `0`] drule ALL_DISJOINT_elem
    \\ simp []
    \\ disch_then (qspec_then `idx.tidx` mp_tac)
    \\ simp [idx_block_def, flookup_thm]
    \\ rw []
    \\ irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM
    \\ simp [MEM_MAP, EXISTS_PROD]
    \\ simp [MAP_MAP_o, o_DEF]
    \\ simp [GSYM MAP_MAP_o |> REWRITE_RULE [o_DEF] |> Q.SPEC `f`
                |> Q.ISPEC `SND`]
    \\ irule ALL_DISTINCT_MAP_INJ
    \\ simp [FORALL_PROD]
  )
  >- (
    simp [env_domain_eq_def]
    \\ simp [MAP_MAP_o, o_DEF, build_constrs_def, MAP_REVERSE, ELIM_UNCURRY]
    \\ simp [GSYM MAP_MAP_o |> REWRITE_RULE [o_DEF] |> Q.SPEC `f`
                |> Q.ISPEC `FST`]
  )
QED

Theorem nsAppend_foldl'[local]:
  !l ns ns'.
   nsAppend (FOLDL (λns (l,cids). nsAppend l ns) ns' l) ns
   =
   FOLDL (λns (l,cids). nsAppend l ns) (nsAppend ns' ns) l
Proof
  Induct_on `l` >>
  rw [] >>
  PairCases_on `h` >>
  rw []
QED

Theorem nsAppend_foldl[local]:
  !l ns.
   FOLDL (λns (l,cids). nsAppend l ns) ns l
   =
   nsAppend (FOLDL (λns (l,cids). nsAppend l ns) nsEmpty l) ns
Proof
  metis_tac [nsAppend_foldl', nsAppend_nsEmpty]
QED

Theorem build_tdefs_no_mod[local]:
  !idx tdefs. nsDomMod (build_tdefs idx tdefs) = {[]}
Proof
  Induct_on `tdefs` >>
  rw [build_tdefs_def] >>
  PairCases_on `h` >>
  rw [build_tdefs_def] >>
  pop_assum (qspec_then `idx+1` mp_tac) >>
  rw [nsDomMod_nsAppend_flat]
QED

val extend_env_v_empty =
  ``extend_env <| c := c; v := nsEmpty |> <| c := c'; v := nsEmpty |>``
  |> SIMP_CONV (srw_ss ()) [extend_env_def];

val extend_dec_env_v_empty =
  ``extend_dec_env <| c := c; v := nsEmpty |> <| c := c'; v := nsEmpty |>``
  |> SIMP_CONV (srw_ss ()) [extend_dec_env_def];

Theorem nsLookup_nsBind_If:
  nsLookup (nsBind n v e) nm = (if nm = Short n then SOME v else nsLookup e nm)
Proof
  Cases_on `e`
  \\ Cases_on `nm`
  \\ simp [namespaceTheory.nsBind_def, namespaceTheory.nsLookup_def]
  \\ simp [EQ_SYM_EQ]
QED

Theorem invariant_IMP_s_rel:
  invariant interp g gen genv idx st st' ==> s_rel genv st st'
Proof
  simp [invariant_def]
QED

Definition abort_def:
  abort r <=> (case r of Rerr (Rabort a) => T
    | _ => F)
End

Theorem not_abort_IMP_cases[local]:
  (~ abort r ==> P) ==>
  ((?a. r = Rerr (Rabort a)) \/ (~ abort r /\ P))
Proof
  simp [abort_def] \\ every_case_tac \\ simp []
QED

Theorem abort_simps[simp]:
  abort (Rerr (Rabort a)) = T /\
  abort (Rerr (Rraise e)) = F /\
  abort (Rval v) = F
Proof
  simp [abort_def]
QED

val is_app_case = can markerSyntax.dest_Case

fun setup (q : term quotation, t : tactic) = let
    val the_concl = Parse.typedTerm q bool
    val t2 = (t \\ rpt (pop_assum mp_tac))
    val (goals, validation) = t2 ([], the_concl)
    fun get_goal q = first (can (rename [q])) goals |> snd
    fun init thms st = if null (fst st) andalso aconv (snd st) the_concl
      then ((K (goals, validation)) \\ TRY (MAP_FIRST ACCEPT_TAC thms)) st
      else failwith "setup tactic: mismatching starting state"
    val cases = map (find_terms is_app_case o snd) goals
  in {get_goal = get_goal, concl = fn () => the_concl,
    cases = cases, init = (init : thm list -> tactic),
    all_goals = fn () => map snd goals} end

val compile_correct_setup = setup (`
  (∀ ^s env es s' r genv comp_map env_i1 ^s_i1 es_i1 locals t ts gen idxs.
    evaluate$evaluate s env es = (s', r) ∧
    invariant interp g gen genv idxs s s_i1 ∧
    env_all_rel genv comp_map env env_i1 locals ∧
    LENGTH ts = LENGTH locals ∧
    env_gen_rel gen s.eval_state ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    es_i1 = compile_exps t (comp_map with v := bind_locals ts locals comp_map.v) es
    ⇒
    ?s'_i1 r_i1 genv'.
    flatSem$evaluate env_i1 s_i1 es_i1 = (s'_i1, r_i1) ∧
    result_rel (LIST_REL o v_rel) genv' r r_i1 ∧
    s_rel genv' s' s'_i1 ∧
    (~ abort r ⇒
      invariant interp g gen genv' idxs s' s'_i1 ∧
      env_gen_rel gen s'.eval_state ∧
      orac_forward_rel interp s.eval_state s'.eval_state ∧
      genv.c ⊑ genv'.c ∧
      genv.tys ⊑ genv'.tys ∧
      subglobals genv.v genv'.v)
  ) ∧
  (∀ ^s env v pes err_v genv comp_map s' r env_i1 ^s_i1 v_i1 pes_i1
         err_v_i1 locals t ts gen idxs.
    evaluate$evaluate_match s env v pes err_v = (s', r) ∧
    invariant interp g gen genv idxs s s_i1 ∧
    env_all_rel genv comp_map env env_i1 locals ∧
    v_rel genv v v_i1 ∧
    LENGTH ts = LENGTH locals ∧
    env_gen_rel gen s.eval_state ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    pes_i1 = compile_pes t (comp_map with v := bind_locals ts locals comp_map.v) pes ∧
    pmatch_rows pes_i1 s_i1 v_i1 <> Match_type_error ∧
    v_rel genv err_v err_v_i1
    ⇒
    ?s'_i1 r_i1 genv'.
    flatProps$evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 = (s'_i1, r_i1) ∧
    result_rel (LIST_REL o v_rel) genv' r r_i1 ∧
    s_rel genv' s' s'_i1 ∧
    (~ abort r ⇒
      invariant interp g gen genv' idxs s' s'_i1 ∧
      env_gen_rel gen s'.eval_state ∧
      orac_forward_rel interp s.eval_state s'.eval_state ∧
      genv.c ⊑ genv'.c ∧
      genv.tys ⊑ genv'.tys ∧
      subglobals genv.v genv'.v)
  ) ∧
  (∀ ^s env ds s' r path t idx end_idx os comp_map ^s_i1 idx'
        comp_map' ds_i1 t' genv gen gen'.
    evaluate$evaluate_decs s env ds = (s',r) ∧
    invariant interp g gen genv (idx, end_idx, os) s s_i1 ∧
    source_to_flat$compile_decs path t idx comp_map gen ds =
        (t', idx', comp_map', gen', ds_i1) ∧
    global_env_inv genv comp_map {} env ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    env_gen_rel gen s.eval_state ∧
    env_gen_future_rel interp gen' s.eval_state ∧
    idx_prev idx' end_idx
    ⇒
    ? ^s1_i1 genv' r_i1.
    flatSem$evaluate_decs s_i1 ds_i1 = (s1_i1,r_i1) ∧
    s_rel genv' s' s1_i1 ∧
    (~ abort r ⇒
      invariant interp g gen' genv' (idx', end_idx, os) s' s1_i1 ∧
      orac_forward_rel interp s.eval_state s'.eval_state ∧
      genv.c ⊑ genv'.c ∧
      genv.tys ⊑ genv'.tys ∧
      subglobals genv.v genv'.v
    ) ∧
    (!env'.
      r = Rval env'
      ⇒
      r_i1 = NONE ∧
      env_domain_eq comp_map' env' ∧
      env_gen_rel gen' s'.eval_state ∧
      global_env_inv genv' comp_map' {} env') ∧
    (!err.
      r = Rerr err
      ⇒
      ?err_i1.
        r_i1 = SOME err_i1 ∧
        result_rel (\a b (c:'a). T) genv' (Rerr err) (Rerr err_i1))
  )
  `,
  ho_match_mp_tac (name_ind_cases [] evaluateTheory.full_evaluate_ind)
  \\ rw [evaluateTheory.full_evaluate_def, flat_evaluate_def,
    compile_exp_def, compile_decs_def]
  \\ imp_res_tac invariant_IMP_s_rel
  \\ fs [result_rel_eqns, v_rel_eqns_non_global]
)

(*
  #all_goals compile_correct_setup ()
*)

val trans_thms = [SUBMAP_TRANS, SUBSET_TRANS,
    subglobals_trans, orac_forward_rel_trans];

Theorem compile_correct_seq[local]:
  ^(#get_goal compile_correct_setup `Case (_ :: _ :: _)`)
Proof
  rw []
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ reverse (fs [result_case_eq])
  >- (
    rw []
    \\ fs [result_rel_cases]
    \\ asm_exists_tac \\ simp []
  )
  \\ fs [pair_case_eq]
  \\ rveq \\ fs []
  \\ rw []
  \\ fs [result_rel_cases]
  \\ rveq \\ fs []
  \\ drule_then drule env_all_rel_weak
  \\ rw []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ impl_tac >- (CCONTR_TAC >> fs [])
  \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
  \\ rw [] \\ fs [] \\ rveq \\ fs []
  \\ metis_tac (v_rel_weak :: trans_thms)
QED

Theorem compile_correct_Raise[local]:
  ^(#get_goal compile_correct_setup `Case [Raise _]`)
Proof
  rw []
  \\ fs [pair_case_eq]
  \\ rveq \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ impl_tac >- (CCONTR_TAC \\ fs [])
  \\ rw []
  \\ fs [result_rel_cases] \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ imp_res_tac evaluatePropsTheory.evaluate_sing
  \\ imp_res_tac evaluate_sing
  \\ rveq \\ fs []
  \\ asm_exists_tac \\ simp []
QED

Theorem compile_correct_Handle[local]:
  ^(#get_goal compile_correct_setup `Case [Handle _ _]`)
Proof
  rw []
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ impl_tac >- (CCONTR_TAC \\ fs [])
  \\ rw []
  \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs []
  \\ TRY (asm_exists_tac \\ simp [])
  \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ drule_then drule env_all_rel_weak
  \\ rw []
  \\ first_x_assum (drule_then drule)
  \\ rpt (disch_then drule)
  \\ disch_then (first_assum o mp_then (Pat `v_rel`) mp_tac)
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ DEP_REWRITE_TAC [GEN_ALL can_pmatch_all_IMP_pmatch_rows]
  \\ rw [] \\ fs []
  \\ metis_tac trans_thms
QED

Theorem compile_correct_Con[local]:
  ^(#get_goal compile_correct_setup `Case [Con _ _]`)
Proof
  rw []
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ impl_tac >- (CCONTR_TAC \\ fs [])
  \\ rw []
  \\ fs [do_con_check_def, opt_case_bool_eq, EXISTS_PROD]
  >- (
    (* tuple *)
    rfs [build_conv_def, compile_exps_reverse, evaluate_def]
    \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
    \\ simp [v_rel_eqns]
    \\ goal_assum (first_assum o mp_then (Pat `s_rel`) mp_tac)
    \\ simp []
  )
  (* named constructor *)
  \\ rveq \\ fs [build_conv_def, compile_exps_reverse, evaluate_def]
  \\ fs [env_all_rel_cases] \\ rveq \\ fs []
  \\ fs [v_rel_global_eqn]
  \\ first_x_assum drule
  \\ rw [EXISTS_PROD]
  \\ simp [type_group_id_type_MAP, evaluate_def]
  \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
  \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
  \\ goal_assum (qsubterm_then `s_rel _ _ _` mp_tac)
  \\ simp [v_rel_eqns, result_rel_eqns]
  \\ imp_res_tac evaluatePropsTheory.evaluate_length
  \\ fs []
  \\ metis_tac [FLOOKUP_SUBMAP]
QED

Theorem compile_correct_Var[local]:
  ^(#get_goal compile_correct_setup `Case [Var _]`)
Proof
  rw []
  \\ fs [option_case_eq]
  \\ fs [env_all_rel_cases]
  \\ rveq \\ fs []
  \\ fs [nsLookup_nsAppend_some]
  >- ((* Local variable *)
    fs [nsLookup_alist_to_ns_some,bind_locals_def] >>
    rw [] >>
    drule env_rel_lookup >>
    disch_then drule >>
    rw [GSYM nsAppend_to_nsBindList] >>
    simp[MAP2_MAP]>>
    every_case_tac >>
    fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none, nsLookup_alist_to_ns_some,
        nsLookup_alist_to_ns_none,evaluate_def]>>
    fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
    `(λ(p1:tra,p2:tvarN). p2) = SND` by fs[FUN_EQ_THM,FORALL_PROD]>>
    fs[]>>rfs[MAP_ZIP]
    >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP, SUBMAP_REFL, subglobals_refl]
    >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP, SUBMAP_REFL, subglobals_refl]
    >- (
      drule ALOOKUP_MEM >>
      rw [MEM_MAP] >>
      pairarg_tac>>fs[compile_var_def]>>
      simp [evaluate_def, result_rel_cases] >>
      metis_tac [SUBMAP_REFL, subglobals_refl])
    >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP])
  >- ( (* top-level variable *)
    rw [GSYM nsAppend_to_nsBindList,bind_locals_def] >>
    fs [nsLookup_alist_to_ns_none] >>
    fs [v_rel_global_eqn, ALOOKUP_NONE, METIS_PROVE [] ``~x ∨ y ⇔ x ⇒ y``] >>
    first_x_assum drule >>
    rw [] >>
    simp[MAP2_MAP]>>
    every_case_tac >>
    fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none, nsLookup_alist_to_ns_some,
        nsLookup_alist_to_ns_none]>>
    fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]
    >- (Cases_on`p1`>>fs[])
    >- (
      drule ALOOKUP_MEM >>
      simp[MEM_MAP,MEM_ZIP,EXISTS_PROD]>>
      rw[]>>
      metis_tac[MEM_EL,LENGTH_MAP])
    >- (
      rfs [ALOOKUP_TABULATE] >>
      rw [] >>
      simp [evaluate_def, result_rel_cases,compile_var_def] >>
      simp [do_app_def] >>
      imp_res_tac invariant_globals >>
      fs [] >>
      metis_tac [subglobals_refl, SUBMAP_REFL]))
QED

Theorem compile_correct_Fun[local]:
  ^(#get_goal compile_correct_setup `Case [Fun _ _]`)
Proof
  rw [Once v_rel_cases] >>
  goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >>
  fs [env_all_rel_cases, subglobals_refl] >>
  srw_tac[][] >>
  rename [`global_env_inv genv comp_map (set (MAP FST locals)) env`] >>
  MAP_EVERY qexists_tac [`comp_map`, `env`, `alist_to_ns locals`,`t`,`None::ts`] >>
  imp_res_tac env_rel_dom >>
  srw_tac[][] >>
  simp [bind_locals_def, namespaceTheory.nsBindList_def] >>
  fs [ADD1]
  >- metis_tac [sem_env_eq_lemma]
  >- metis_tac[LENGTH_MAP]
QED

Theorem invariant_change_eval_ref:
  invariant interp g gen genv idxs st st'
  ==>
  invariant interp g gen genv idxs st
    (st' with refs := Refv y :: TL st'.refs)
Proof
  rw [invariant_def]
  \\ fs [s_rel_cases, eval_ref_inv_def]
QED

Theorem declare_env_store_env_id:
  declare_env st.eval_state env = SOME (x, es2) /\
  invariant interp g gen genv idxs st ^s_i1 /\
  env_gen_rel gen st.eval_state /\
  gen_id = gen.generation /\
  id = gen.next /\
  (case src_orac_next_cfg interp st.eval_state of
    | NONE => T
    | SOME c => (case lookup gen_id c.envs.env_gens of
      | NONE => F
      | SOME gen' => (case lookup id gen' of
        | NONE => F
        | SOME e => global_env_inv genv e {} env)))
  ==>
  ?y.
  evaluate_decs s_i1 [store_env_id gen_id id] =
    (s_i1 with refs := Refv y :: TL s_i1.refs, NONE) /\
  invariant interp g (gen with next := gen.next + 1) genv idxs
    (st with eval_state := es2) s_i1
  /\
  (?xs. s_i1.globals = SOME (Loc T 0) :: xs) /\
  v_rel genv x y /\
  orac_forward_rel interp st.eval_state es2
Proof
  fs [invariant_def, s_rel_cases]
  \\ rpt disch_tac
  \\ fs [NOT_NULL_EQ]
  \\ rfs []
  \\ Cases_on `s_i1.globals` \\ fs [eval_ref_inv_def]
  \\ simp [store_env_id_def, evaluate_def, do_app_def, env_id_tuple_def,
    miscTheory.opt_bind_def, store_assign_def]
  \\ rfs []
  \\ rveq \\ fs []
  \\ simp [store_v_same_type_def, LUPDATE_def]
  \\ fs [declare_env_def, option_case_eq, src_orac_invs_def]
  \\ every_case_tac \\ fs []
  \\ rveq \\ fs []
  \\ TRY (imp_res_tac step_1 \\ fs [env_gen_rel_def] \\ NO_TAC)
  \\ simp [v_rel_eqns, PULL_EXISTS, nat_to_v_def]
  \\ fs [oEL_THM]
  \\ simp [EL_LUPDATE]
  \\ fs [src_orac_next_cfg_def]
  \\ rw []
  \\ TRY (fs [src_orac_step_invs_def, env_gen_rel_def, orac_rel_def,
    orac_rel_inner_def, src_orac_gen_inv_def] \\ NO_TAC)
  >- (
    fs [idx_range_rel_def, src_orac_next_cfg_def]
    \\ asm_exists_tac
    \\ simp []
  )
  >- (
    fs [src_orac_env_invs_def, src_orac_next_cfg_def]
    \\ rw [EL_LUPDATE]
    \\ Cases_on `id = LENGTH (EL e.generation e.envs)` \\ fs []
    \\ rw [EL_APPEND_IF, EL_CONS_IF]
    \\ rfs [env_gen_rel_def, lookup_env_id_def]
  )
  >- (
    fs [env_gen_inv_def]
    \\ drule_then irule SUBSET_TRANS
    \\ irule pred_setTheory.COUNT_MONO
    \\ simp []
  )
  >- (
    fs [orac_forward_rel_def, eval_state_call_rel_def, EL_LUPDATE]
    \\ fs [orac_config_envs_subspt_def, src_orac_next_cfg_def]
  )
QED

Theorem pmatch_rows_drop_4[local]:
  LENGTH vs = 6 ==>
  pmatch_rows [(Pcon NONE [Pany; Pany; Pany; Pany; Pvar b; Pvar w], exp)]
    st (Conv NONE vs) =
  Match ([(w, LAST vs); (b, EL 4 vs)],
    Pcon NONE [Pany; Pany; Pany; Pany; Pvar b; Pvar w], exp)
Proof
  simp [pmatch_rows_def, pmatch_def, pmatch_stamps_ok_cases]
  \\ rpt (
    rename [`pmatch_list _ _ pm_vs _`]
    \\ Cases_on `pm_vs` \\ simp [pmatch_def, ADD1]
  )
QED

Theorem drop_4_via_el[local]:
  LENGTH vs = 6 ==> [EL 4 vs; LAST vs] = DROP 4 vs
Proof
  rw [LIST_EQ_REWRITE]
  \\ Cases_on `x` \\ fs [HD_DROP]
  \\ Cases_on `n` \\ fs [EL_DROP]
  \\ DEP_REWRITE_TAC [LAST_EL]
  \\ simp []
  \\ strip_tac
  \\ fs []
QED

Theorem compile_correct_App:
  ^(#get_goal compile_correct_setup `Case [App _ _]`)
Proof
  rpt disch_tac
  \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ (impl_tac >- (CCONTR_TAC \\ fs []))
  \\ Cases_on `op = AallocEmpty`
  >- (
    (* empty array creation *)
    rw []
    \\ fs [semanticPrimitivesTheory.do_app_def, astTheory.getOpClass_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    >- (
      drule (CONJUNCT1 evaluatePropsTheory.evaluate_length) >>
      rw [] >>
      fs [LENGTH_EQ_NUM_compute] >>
      rveq >> fs [] >>
      simp [compile_exp_def, evaluate_def] >>
      pairarg_tac >>
      fs [store_alloc_def, compile_exp_def] >>
      rpt var_eq_tac >>
      fs [result_rel_cases, Once v_rel_cases] >>
      simp [do_app_def] >>
      pairarg_tac >>
      fs [store_alloc_def] >>
      goal_assum (first_assum o mp_then (Pat `subglobals`) mp_tac) >>
      fs [invariant_def, s_rel_cases] >>
      imp_res_tac NOT_NULL_EQ >>
      rveq >> fs [ADD1] >>
      imp_res_tac LIST_REL_LENGTH >>
      simp [REPLICATE, sv_rel_cases])
    >- (
      rw []
      \\ fs [compile_exps_reverse]
      \\ fs [result_rel_cases] \\ rveq \\ fs []
      \\ drule_then (simp o single) evaluate_foldr_let_err
      \\ goal_assum (first_assum o mp_then (Pat `s_rel`) mp_tac)
      \\ simp []
      )
  )
  \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
  >- (
    (* Rerr *)
    rw [evaluate_def]
    \\ fs [compile_exps_reverse, result_rel_cases]
    \\ goal_assum (first_assum o mp_then (Pat `s_rel`) mp_tac)
    \\ simp []
    \\ rpt (CASE_TAC \\ fs [])
    \\ gvs [compile_exp_def, evaluate_def]
  )
  \\ Cases_on `op = Eval`
  >- (
    rw[]
    \\ fs [evaluateTheory.do_eval_res_def, astTheory.getOpClass_def]
    \\ fs [astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
        evaluate_decs_append, miscTheory.opt_bind_def]
    \\ fs [list_case_eq, option_case_eq, pair_case_eq]
    \\ rveq \\ fs []
    \\ imp_res_tac result_rel_imp \\ fs [result_rel_cases]
    \\ rveq \\ fs []
    \\ fs [compile_exps_reverse, pair_case_eq]
    \\ drule_then drule (Q.SPEC `REVERSE ys` do_eval)
    \\ simp []
    \\ disch_then drule
    \\ rw []
    \\ simp [pmatch_rows_drop_4, pat_bindings_def]
    \\ simp [evaluate_def, drop_4_via_el]
    \\ drule_then assume_tac invariant_dec_clock
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    >- (
      fs [invariant_def]
      \\ goal_assum (qsubterm_then `s_rel _ _` mp_tac)
      \\ fs [s_rel_cases]
    )
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq]
    \\ fs [inc_compile_prog_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ simp [glob_alloc_def, evaluate_def, do_app_def, Unitv_def]
    \\ first_x_assum (qsubterm_then `compile_decs _ _ _ _ _ _` mp_tac)
    \\ fs [dec_clock_def, evaluateTheory.dec_clock_def]
    \\ rfs []
    \\ disch_then drule
    \\ simp [idx_prev_refl]
    \\ impl_tac >- (
      rpt strip_tac \\ fs []
    )
    \\ rw []
    \\ fs [evaluate_decs_append]
    \\ reverse (fs [result_case_eq, error_result_case_eq])
    \\ rveq \\ fs [] \\ fsrw_tac [SATISFY_ss] []
    >- (
      rveq \\ fs []
      \\ drule_then (drule_then drule) invariant_end_eval
      \\ rw []
      \\ asm_exists_tac
      \\ imp_res_tac invariant_IMP_s_rel
      \\ simp []
      \\ metis_tac trans_thms
    )
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ drule_then drule declare_env_store_env_id
    \\ simp []
    \\ impl_tac >- (
      qpat_x_assum `orac_forward_rel _ _ _` mp_tac
      \\ rw [orac_forward_rel_def, orac_config_envs_subspt_def]
      \\ fs [OPTREL_SOME, subspt_lookup, lookup_insert]
      \\ imp_res_tac compile_decs_generation
      \\ fs []
      \\ first_x_assum (qsubterm_then `lookup _ _.envs.env_gens` mp_tac)
      \\ rw []
      \\ irule global_env_inv_append
      \\ simp []
      \\ drule_then irule global_env_inv_weak
      \\ fsrw_tac [SATISFY_ss] trans_thms
    )
    \\ rw []
    \\ simp [store_lookup_def]
    \\ drule_then drule invariant_end_eval
    \\ simp []
    \\ disch_then (qsubterm_then `orac_config_envs_subspt _ _ _` mp_tac)
    \\ impl_tac >- (
      simp []
      \\ drule_then irule orac_forward_rel_trans
      \\ simp []
    )
    \\ rw []
    \\ simp [miscTheory.opt_bind_def]
    \\ asm_exists_tac
    \\ simp []
    \\ drule_then (qsubterm_then `invariant _ _ _ _ _ _ _` mp_tac)
        invariant_change_eval_ref
    \\ simp []
    \\ metis_tac (invariant_IMP_s_rel :: trans_thms)
  )
  \\ Cases_on `op = Opapp`
  >- (
    (* Opapp *)
    fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq, option_case_eq, astTheory.getOpClass_def] >>
    rw [] >>
    rveq >> fs [] >>
    fs [astOp_to_flatOp_def, evaluate_def, compile_exps_reverse] >>
    fs [result_rel_eqns] >> rveq >> fs [] >>
    drule_then assume_tac EVERY2_REVERSE >>
    drule_then drule do_opapp >>
    rw [] >>
    imp_res_tac invariant_dec_clock >>
    rw []
    >- (
      (* out of clock *)
      fs [] >> rveq >> fs [] >>
      simp [result_rel_eqns] >>
      asm_exists_tac >>
      simp []
    ) >>
    fs [Q.ISPEC `(a, b)` EQ_SYM_EQ] >>
    first_x_assum (drule_then (drule_then drule)) >>
    simp [dec_clock_def] >>
    disch_then (qsubterm_then `evaluate _ _ _` mp_tac) >>
    rw [] >>
    fs [evaluateTheory.dec_clock_def, dec_clock_def] >>
    metis_tac (SUBSET_TRANS :: trans_thms)
  )
  \\ Cases_on `op = Env_id`
  >- (
    fs [option_case_eq, pair_case_eq, result_rel_eqns, astTheory.getOpClass_def]
    \\ rw []
    \\ fs [semanticPrimitivesTheory.do_app_def]
    \\ fs [case_eq_thms, semanticPrimitivesTheory.v_case_eq, pair_case_eq]
    \\ rveq \\ fs []
    \\ fs [v_rel_eqns]
    \\ rveq \\ fs []
    \\ imp_res_tac evaluate_length
    \\ fs [compile_exps_length]
    \\ fs [LENGTH_EQ_NUM_compute]
    \\ fs [compile_exp_def]
    \\ rw [result_rel_eqns, v_rel_eqns]
    \\ asm_exists_tac \\ fs []
    \\ fs [invariant_def, s_rel_cases]
  ) >>
  Cases_on ‘getOpClass op’ >> gs[]
  >- (
    Cases_on ‘op’ >> gs[astTheory.getOpClass_def] >>
    Cases_on ‘t'’ >> gvs[])
  >- (
    Cases_on ‘op’ >> gs[astTheory.getOpClass_def] >>
    Cases_on ‘t'’ >> gvs[])
  >~ [‘getOpClass op = Force’]
  >- (
    Cases_on ‘op’ >> gvs[astTheory.getOpClass_def] >>
    Cases_on ‘t'’ >> gvs[] >>
    gvs[AllCaseEqs(), evaluateTheory.dec_clock_def, flatSemTheory.dec_clock_def,
        PULL_EXISTS] >> rw[]
    >- (
      gvs[astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
          AllCaseEqs()] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >>
      rw[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.dest_thunk_def, AllCaseEqs()] >>
      rgs[Once v_rel_cases] >> gvs[] >>
      simp[dest_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[store_lookup_def, s_rel_cases, LIST_REL_EL_EQN] >>
      `∃v''. EL n (TL s'_i1.refs) = Thunk Evaluated v'' ∧
             v_rel genv' v v''` by (
        first_x_assum (qspec_then`n` mp_tac) >>
        gvs[] >> rw[Once sv_rel_cases]) >>
      simp[REWRITE_RULE [ADD1] EL, Once result_rel_cases] >>
      goal_assum drule >> rw[])
    >- (
      gvs[astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
          AllCaseEqs()] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >>
      rw[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.dest_thunk_def, AllCaseEqs()] >>
      rgs[Once v_rel_cases] >> gvs[] >>
      simp[dest_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[store_lookup_def, s_rel_cases, LIST_REL_EL_EQN] >>
      `∃v'. EL n (TL s'_i1.refs) = Thunk NotEvaluated v' ∧
             v_rel genv' v v'` by (
        first_x_assum (qspec_then`n` mp_tac) >>
        gvs[] >> rw[Once sv_rel_cases]) >>
      simp[REWRITE_RULE [ADD1] EL, Once result_rel_cases, PULL_EXISTS] >>
      simp[AppUnit_def, dec_clock_def] >>
      ntac 5 $ simp[Once evaluate_def] >>
      drule do_opapp >> simp[PULL_EXISTS] >>
      disch_then drule >> simp[Once v_rel_cases] >> strip_tac >> gvs[] >>
      goal_assum drule >> simp[]
      )
    >- (
      gvs[astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
          AllCaseEqs()] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >>
      rw[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.dest_thunk_def, AllCaseEqs()] >>
      rgs[Once v_rel_cases] >> gvs[] >>
      simp[dest_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[store_lookup_def, s_rel_cases, LIST_REL_EL_EQN] >>
      `∃v'. EL n (TL s'_i1.refs) = Thunk NotEvaluated v' ∧
             v_rel genv' v v'` by (
        first_x_assum (qspec_then`n` mp_tac) >>
        gvs[] >> rw[Once sv_rel_cases]) >>
      simp[REWRITE_RULE [ADD1] EL, Once result_rel_cases, PULL_EXISTS] >>
      simp[AppUnit_def, dec_clock_def] >>
      ntac 5 $ simp[Once evaluate_def] >>
      drule do_opapp >> simp[PULL_EXISTS] >>
      disch_then drule >> simp[Once v_rel_cases] >> strip_tac >> gvs[] >>
      dxrule invariant_dec_clock >> strip_tac >>
      gvs[evaluateTheory.dec_clock_def, flatSemTheory.dec_clock_def] >>
      last_x_assum drule_all >> disch_then $ qspec_then ‘t1’ assume_tac >> gvs[] >>
      gvs[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.update_thunk_def,
          oneline flatSemTheory.update_thunk_def, AllCaseEqs()] >>
      `dest_thunk [y] s'_i1'.refs = NotThunk` by (
        qpat_x_assum `v_rel _ v'3' y` mp_tac >>
        Cases_on `v'3'` >> Cases_on `y` >>
        rw[Once v_rel_cases, dest_thunk_def, Boolv_def] >>
        gvs[semanticPrimitivesTheory.dest_thunk_def, store_lookup_def] >>
        reverse $ rw []
        >- (Cases_on `s'_i1'.refs` >> gvs []) >>
        `n' < LENGTH s'_i1'.refs -1` by (Cases_on `s'_i1'.refs` >> gvs[]) >>
        gvs[] >>
        first_x_assum drule >> simp[REWRITE_RULE [ADD1] EL] >>
        Cases_on `EL n' st2.refs` >> Cases_on `EL n' (TL s'_i1'.refs)` >>
        rw[Once sv_rel_cases] >> gvs[] >> Cases_on `t'` >> gvs[]) >> gvs[] >>
      Cases_on `s'_i1'.refs` >> gvs[] >>
      qexists `genv'3'` >> gvs[] >>
      imp_res_tac SUBMAP_TRANS >> gvs[] >>
      imp_res_tac subglobals_trans >> gvs[] >>
      gvs[store_assign_def, store_v_same_type_def, REWRITE_RULE [ADD1] EL] >>
      rw[]
      >- (
        first_x_assum drule >>
        Cases_on `EL n st2.refs` >> Cases_on `EL n t'` >> gvs[] >>
        rw[Once sv_rel_cases])
      >- rw[REWRITE_RULE [ADD1] LUPDATE_def]
      >- (
        rw[REWRITE_RULE [ADD1] LUPDATE_def, EL_LUPDATE] >>
        simp[Once sv_rel_cases])
      >- (
        rw[REWRITE_RULE [ADD1] LUPDATE_def] >>
        gvs[invariant_def] >>
        rw[REWRITE_RULE [ADD1] LUPDATE_def] >>
        gvs[s_rel_cases, LIST_REL_EL_EQN] >>
        rw[EL_LUPDATE] >> simp[Once sv_rel_cases])
      >- (
        gvs[evaluateTheory.dec_clock_def] >>
        drule_then irule orac_forward_rel_trans >> gvs[])
      )
    >- (
      gvs[astOp_to_flatOp_def, evaluate_def, compile_exps_reverse,
          AllCaseEqs()] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >>
      rw[Once result_rel_cases] >>
      gvs[oneline semanticPrimitivesTheory.dest_thunk_def, AllCaseEqs()] >>
      rgs[Once v_rel_cases] >> gvs[] >>
      simp[dest_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[store_lookup_def, s_rel_cases, LIST_REL_EL_EQN] >>
      `∃v'. EL n (TL s'_i1.refs) = Thunk NotEvaluated v' ∧
             v_rel genv' v v'` by (
        first_x_assum (qspec_then`n` mp_tac) >>
        gvs[] >> rw[Once sv_rel_cases]) >>
      simp[REWRITE_RULE [ADD1] EL, Once result_rel_cases, PULL_EXISTS] >>
      simp[AppUnit_def, dec_clock_def] >>
      ntac 5 $ simp[Once evaluate_def] >>
      drule do_opapp >> simp[PULL_EXISTS] >>
      disch_then drule >> simp[Once v_rel_cases] >> strip_tac >> gvs[] >>
      dxrule invariant_dec_clock >> strip_tac >>
      gvs[evaluateTheory.dec_clock_def, flatSemTheory.dec_clock_def] >>
      last_x_assum drule_all >> disch_then $ qspec_then ‘t1’ assume_tac >> gvs[] >>
      qpat_x_assum `result_rel _ _ _ r_i1` mp_tac >> rw[Once result_rel_cases] >>
      goal_assum drule >> simp[] >>
      imp_res_tac SUBMAP_TRANS >> gvs[] >>
      imp_res_tac subglobals_trans >> gvs[] >>
      drule_then irule orac_forward_rel_trans >> gvs[]
      )) >>
  fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, option_case_eq, pair_case_eq] >>
  rw [] >>
  rveq >> fs [] >>
  fs [result_rel_eqns] >> rveq >> fs [] >>
  drule_then assume_tac EVERY2_REVERSE >>
  imp_res_tac s_rel_cases >>
  drule do_app >> simp [] >>
  rpt (disch_then drule) >>
  (impl_tac >- fs [invariant_def, s_rel_cases]) >>
  rw [] >>
  `astOp_to_flatOp op ≠ Opapp ∧ astOp_to_flatOp op ≠ Eval ∧
   astOp_to_flatOp op ≠ ThunkOp ForceThunk`
  by (
    rw [astOp_to_flatOp_def] >>
    Cases_on `op` >>
    simp [] >>
    fs [astTheory.getOpClass_def] >>
    Cases_on `t'` >> gvs []) >>
  fs [evaluate_def, compile_exps_reverse] >>
  imp_res_tac do_app_state_unchanged >>
  imp_res_tac do_app_const >>
  rename [`result_rel v_rel genv2`] >>
  qexists_tac `genv2` >>
  simp [] >>
  conj_tac >> TRY (fs [result_rel_cases] \\ NO_TAC) >>
  fs [invariant_def, s_rel_cases] >>
  rpt (TOP_CASE_TAC >> gs[result_rel_cases, semanticPrimitivesTheory.Boolv_def, Boolv_def, v_rel_eqns]) >>
  TRY COND_CASES_TAC >> gs[] >>
  simp[ Once v_rel_rules]
QED

Theorem compile_correct_Log[local]:
  ^(#get_goal compile_correct_setup `Case [Log _ _ _]`)
Proof
  rw [] >>
  fs [pair_case_eq] >> fs [] >>
  first_x_assum (drule_then (drule_then drule)) >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  simp [] >>
  impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
  rw [] >>
  reverse (fs [result_case_eq]) >> rveq >> fs []
  >- (
    goal_assum (qsubterm_then `invariant _ _ _ _` mp_tac) >>
    fs [result_rel_cases] >> rveq >> fs [] >>
    every_case_tac >>
    simp [evaluate_def]
  ) >>
  imp_res_tac evaluatePropsTheory.evaluate_sing >>
  reverse (fs [option_case_eq, exp_or_val_case_eq, result_rel_eqns])
  >- (
    rveq >> fs [] >>
    fs [evaluate_def, do_if_def, do_log_def, bool_case_eq] >> rveq >> fs [] >>
    goal_assum (qsubterm_then `invariant _ _ _ _` mp_tac) >>
    fs [invariant_def, v_rel_Bool_eqn, Boolv_11] >>
    drule_then (fn t => simp [t]) evaluate_Bool >>
    simp [result_rel_eqns, v_rel_Bool_eqn]
  ) >>
  fs [] >> rveq >> fs [] >>
  drule_then drule env_all_rel_weak >>
  rw [] >>
  first_x_assum (drule_then (drule_then drule)) >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  rw [] >>
  goal_assum (qsubterm_then `invariant _ _ _ _` mp_tac) >>
  fs [evaluate_def, do_if_def, do_log_def, bool_case_eq] >> rveq >> fs [] >>
  fs [invariant_def, v_rel_Bool_eqn, Boolv_11] >>
  metis_tac trans_thms
QED

Theorem compile_correct_If[local]:
  ^(#get_goal compile_correct_setup `Case [If _ _ _]`)
Proof
  rw [] >> fs [pair_case_eq] >> fs [] >>
  first_x_assum (drule_then (drule_then drule)) >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  simp [] >>
  (impl_tac >- (CCONTR_TAC >> fs [])) >>
  rw [] >>
  imp_res_tac result_rel_imp >> rveq >> fs [] >> rveq >> fs [result_rel_eqns] >>
  TRY (asm_exists_tac >> simp [] >> NO_TAC) >>
  fs [option_case_eq] >> fs [] >>
  drule_then drule env_all_rel_weak >>
  rw [] >>
  first_x_assum (drule_then (drule_then drule)) >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  rw [] >>
  imp_res_tac evaluatePropsTheory.evaluate_sing >>
  goal_assum (qsubterm_then `invariant _ _ _ _` mp_tac) >>
  fs [semanticPrimitivesTheory.do_if_def, bool_case_eq] >> rveq >> fs [] >>
  fs [invariant_def, do_if_def] >>
  rfs [v_rel_Bool_eqn, Boolv_11] >>
  metis_tac trans_thms
QED

Theorem compile_correct_Mat[local]:
  ^(#get_goal compile_correct_setup `Case [Mat _ _]`)
Proof
  rw [] \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ simp []
  \\ (impl_tac >- (CCONTR_TAC >> fs []))
  \\ rw []
  \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
  \\ TRY (asm_exists_tac \\ simp [])
  \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ imp_res_tac evaluatePropsTheory.evaluate_sing
  \\ fs [] \\ rveq \\ fs []
  \\ drule_then drule env_all_rel_weak
  \\ rw []
  \\ first_x_assum (drule_then (drule_then (drule_then drule)))
  \\ disch_then (qspec_then `bind_exn_v` mp_tac)
  \\ disch_then (qspec_then ‘t’ mp_tac)
  \\ DEP_REWRITE_TAC [GEN_ALL can_pmatch_all_IMP_pmatch_rows]
  \\ conj_tac >- metis_tac []
  \\ impl_tac >- (fs [invariant_def, v_rel_lems])
  \\ rw []
  \\ simp []
  \\ metis_tac trans_thms
QED

Theorem compile_correct_Let[local]:
  ^(#get_goal compile_correct_setup `Case [Let _ _ _]`)
Proof
  rw [] \\ fs [pair_case_eq] \\ fs []
  \\ first_x_assum (drule_then (drule_then drule))
  \\ simp [GSYM PULL_FORALL]
  \\ (impl_tac >- (CCONTR_TAC >> fs []))
  \\ rw []
  \\ rename [`Let opt_name _ _`]
  \\ Cases_on `opt_name`
  >- (
    (* anonymous bind *)
    pop_assum (qspec_then ‘t’ strip_assume_tac)
    \\ simp [compile_exp_def, evaluate_def]
    \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
    \\ TRY (asm_exists_tac \\ simp [])
    \\ fs [namespaceTheory.nsOptBind_def]
    \\ drule_then drule env_all_rel_weak
    \\ rw []
    \\ first_x_assum (drule_then (drule_then drule))
    \\ disch_then (qspec_then ‘t’ mp_tac)
    \\ rw []
    \\ simp [Q.prove (`env with v updated_by opt_bind NONE x = env`,
          simp [environment_component_equality,miscTheory.opt_bind_def] )]
    \\ metis_tac trans_thms
  )
  \\ pop_assum (qspec_then ‘x::t’ strip_assume_tac)
  \\ simp [compile_exp_def, evaluate_def]
  \\ imp_res_tac result_rel_imp \\ fs [] \\ rveq \\ fs [result_rel_eqns]
  \\ TRY (asm_exists_tac \\ simp [])
  \\ drule_then drule env_all_rel_weak
  \\ rw []
  \\ imp_res_tac evaluate_sing
  \\ fs [] \\ rveq \\ fs []
  \\ simp [bind_locals_fold_nsBind]
  \\ last_x_assum mp_tac
  \\ disch_then (qsubterm_then `evaluate _ _ _ ` mp_tac)
  \\ disch_then drule
  \\ impl_tac >- (
    fs [env_all_rel_cases]
    \\ fs [namespaceTheory.nsOptBind_def, miscTheory.opt_bind_def]
    \\ simp [PULL_EXISTS, listTheory.MAP_EQ_CONS, EXISTS_PROD]
    \\ metis_tac [env_rel_bind_one, pred_setTheory.INSERT_SING_UNION,
      global_env_inv_add_locals]
  )
  \\ rw []
  \\ simp []
  \\ metis_tac trans_thms
QED

Theorem compile_correct_Letrec[local]:
  ^(#get_goal compile_correct_setup `Case [Letrec _ _]`)
Proof
  rw [] >> fs [pair_case_eq] >>
  rw [evaluate_def] >>
  TRY (fs [compile_funs_map,MAP_MAP_o,o_DEF,UNCURRY] >>
       full_simp_tac(srw_ss())[FST_triple,ETA_AX] >>
       NO_TAC) >>
  fs [GSYM nsAppend_to_nsBindList] >>
  rw_tac std_ss [GSYM MAP_APPEND] >>
  simp[nsAppend_bind_locals]>>
  first_x_assum match_mp_tac >> simp[] >>
  full_simp_tac(srw_ss())[env_all_rel_cases] >>
  rw [] >>
  qexists_tac `build_rec_env funs <|v := nsAppend (alist_to_ns l) env'.v; c := env'.c|> (alist_to_ns l)` >>
  qexists_tac `env'` >>
  rw [semanticPrimitivesPropsTheory.build_rec_env_merge,build_rec_env_merge]
  >- (
    simp [MAP_MAP_o, UNCURRY, combinTheory.o_DEF] >>
    metis_tac [])
  >- metis_tac [global_env_inv_add_locals] >>
  rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
  match_mp_tac env_rel_append >>
  rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
  rw [env_rel_el, EL_MAP, UNCURRY] >>
  simp [Once v_rel_cases] >>
  qexists_tac `comp_map` >>
  qexists_tac `env'` >>
  qexists_tac `alist_to_ns l` >>
  qexists_tac `t` >>
  qexists_tac `REPLICATE (LENGTH funs) None ++ ts` >>
  drule env_rel_dom >>
  rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY,
      bind_locals_def, nsAppend_to_nsBindList] >>
  rw [sem_env_component_equality]
  >- metis_tac[]
  >- metis_tac [LENGTH_MAP]
QED

Theorem compile_correct_pattern[local]:
  ^(#get_goal compile_correct_setup `Case ((_, _) :: _)`)
Proof
  rw [] >> fs [pair_case_eq] >>
  drule_then drule pmatch_invariant >>
  disch_then (qsubterm_then `pmatch _ _ _ _` mp_tac) >>
  simp [] >>
  disch_then drule >>
  strip_tac >>
  imp_res_tac match_result_rel_imp >> fs []
  >- (
    last_x_assum (qsubterm_then `evaluate_match _ _ _ _ _` mp_tac) >>
    disch_then drule >>
    fs [pmatch_rows_def]
  ) >>
  qsubterm_then `nsBindList _ _` assume_tac
    (GEN_ALL nsBindList_pat_tups_bind_locals) >>
  fs [] >>
  last_x_assum (qsubterm_then `evaluate _ _ _` mp_tac) >>
  disch_then drule >>
  simp[]>>
  reverse IF_CASES_TAC THEN1 fs [pmatch_rows_def] >>
  impl_tac >> fs [] >>
  simp[s_rel_cases] >>
  fs [env_all_rel_cases, match_result_rel_def] >>
  rveq >> fs [] >>
  rw [environment_component_equality, sem_env_component_equality] >>
  qexists_tac `alist_to_ns (env1 ++ l)` >>
  qexists_tac`env'` >>
  rw []
  >- (
    drule (CONJUNCT1 pmatch_extend) >>
    drule env_rel_dom >>
    rw [])
  >- metis_tac [global_env_inv_add_locals]
  >- (
    rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
    match_mp_tac env_rel_append >>
    rw [])
QED

Theorem compile_correct_empty_decs[local]:
  ^(#get_goal compile_correct_setup `Case ([] : ast$dec list)`)
Proof
  (* no decs *)
  rw [] \\ asm_exists_tac \\ simp []
  \\ simp [v_rel_global_eqn, subglobals_refl,
      empty_env_def, env_domain_eq_def]
QED

Theorem abort_compile_dec_result[local]:
  abort (combine_dec_result env r) = abort r
Proof
  Cases_on `r` \\ simp [combine_dec_result_def]
QED

Theorem invariant_env_gen_inv[local]:
  invariant interp g gen genv (idx,end_idx,os) s s_i1
  ==>
  env_gen_inv gen
Proof
  simp [invariant_def]
QED

Theorem compile_decs_future_rel:
  compile_decs t n next env envs ds = (n2, next2, env2, envs2, ds2) /\
  env_gen_future_rel interp envs2 eval_state /\
  env_gen_inv envs ==>
  env_gen_future_rel interp envs eval_state
Proof
  rw []
  \\ imp_res_tac compile_decs_generation
  \\ imp_res_tac compile_decs_env_gen_inv
  \\ fs [env_gen_future_rel_def]
  \\ every_case_tac
  \\ fs []
  \\ metis_tac [subspt_trans]
QED

Theorem env_gen_future_rel_forward:
  env_gen_future_rel interp envs eval_state /\
  orac_forward_rel interp eval_state eval_state2 ==>
  env_gen_future_rel interp envs eval_state2
Proof
  rw []
  \\ fs [env_gen_future_rel_def, orac_forward_rel_def,
    orac_config_envs_subspt_def]
  \\ every_case_tac
  \\ fs [OPTREL_SOME]
  \\ imp_res_tac subspt_lookup
  \\ simp []
QED

Theorem compile_correct_cons_decs[local]:
  ^(#get_goal compile_correct_setup `Case ((_ :: _ :: _) : ast$dec list)`)
Proof
  (* sequence of decs *)
  rw [] \\ fs [pair_case_eq]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac compile_decs_idx_prev
  \\ first_x_assum (drule_then drule)
  \\ impl_tac >- (
    fs [invariant_def]
    \\ imp_res_tac compile_decs_env_gen_inv
    \\ imp_res_tac compile_decs_future_rel
    \\ rpt strip_tac \\ fs []
    \\ fsrw_tac [SATISFY_ss] [idx_prev_trans]
  )
  \\ rw []
  \\ simp [evaluate_decs_append]
  \\ reverse (fs [result_case_eq]) \\ rveq \\ fs [] \\ rveq \\ fs []
  >- (
    goal_assum (first_assum o mp_then (Pat `result_rel`) mp_tac)
    \\ rw []
    \\ fs []
    \\ drule_then irule invariant_idx_range_shrink_gen
    \\ imp_res_tac compile_decs_env_gen_inv
    \\ fs []
  )
  \\ fs [pair_case_eq] \\ fs []
  \\ drule_then drule global_env_inv_weak
  \\ rw []
  \\ first_x_assum (drule_then drule)
  \\ simp [global_env_inv_append]
  \\ imp_res_tac env_gen_future_rel_forward
  \\ (impl_tac >- (rpt strip_tac \\ fs [combine_dec_result_def]))
  \\ rw []
  \\ simp [abort_compile_dec_result]
  \\ simp [combine_dec_result_def, result_case_eq]
  \\ asm_exists_tac
  \\ rw [] \\ fs []
  \\ fsrw_tac [SATISFY_ss] trans_thms
  >- (
    imp_res_tac env_domain_eq_append
    \\ fs [extend_dec_env_def]
  )
  >- (
    mp_tac global_env_inv_append
    \\ simp [extend_dec_env_def]
    \\ disch_then irule
    \\ imp_res_tac global_env_inv_weak
    \\ simp []
  )
QED

Theorem compile_correct_Dlet[local]:
  ^(#get_goal compile_correct_setup `Case [Dlet _ _ _]`)
Proof
  rw [] >> fs [pair_case_eq] >> fs [] >>
  `env_all_rel genv comp_map env <|v := []|> []`
    by (simp [env_all_rel_cases] \\ simp [v_rel_rules]) >>
  first_x_assum (drule_then drule) >>
  simp [bind_locals_def, EVAL ``nsBindList [] ns``] >>
  simp [bind_locals_def] >>
  simp [Q.prove (`(x with v := x.v) = (x : source_to_flat$environment)`,
      simp [source_to_flatTheory.environment_component_equality])] >>
  disch_then (qsubterm_then `evaluate _ _ _` mp_tac) >>
  (impl_tac >- (CCONTR_TAC >> fs [])) >>
  rw [] >>
  simp [] >>
  imp_res_tac not_abort_IMP_cases >> fs [result_rel_eqns] >>
  rveq >> fs [] >>
  TRY (asm_exists_tac >> simp [result_rel_eqns]) >>
  fs [] >>
  drule invariant_idx_range_shrink >>
  disch_then (qsubterm_then `(_, _, _)` mp_tac) >>
  simp [] >>
  (impl_tac >- simp [idx_prev_def]) >>
  rw [] >>
  imp_res_tac result_rel_imp >> fs [] >> rveq >> fs [result_rel_eqns] >>
  TRY (asm_exists_tac >> simp []) >>
  imp_res_tac evaluate_sing >>
  fs [] >> rveq >> fs [pmatch_rows_def] >>
  drule_then drule env_all_rel_weak >>
  simp [] >> disch_tac >>
  drule pmatch_invariant >>
  disch_then (qsubterm_then `pmatch _ _ _ _ _` mp_tac) >>
  disch_then (qsubterm_then `flatSem$pmatch _ _ _` mp_tac) >>
  disch_then drule >>
  simp [] >> disch_tac >>
  imp_res_tac invariant_genv_c_ok >>
  imp_res_tac match_result_rel_imp >> fs [] >>
  TRY (asm_exists_tac >> simp [result_rel_eqns, v_rel_lems]) >>
  fs [match_result_rel_def] >>
  drule (CONJUNCT1 pmatch_bindings) >>
  rw [] >>
  qpat_x_assum `invariant _ _ _ _ (_ with vidx := _, _, _) _ _` kall_tac >>
  drule invariant_make_varls >>
  disch_then (qsubterm_then `evaluate _ _ _` mp_tac) >>
  simp [] >>
  (impl_tac >- fs [idx_prev_def]) >>
  rw [] >>
  simp [] >>
  imp_res_tac invariant_IMP_s_rel >>
  asm_exists_tac >> simp [] >>
  rw []
  >- (
    metis_tac [subglobals_trans]
  )
  >- (
    simp [env_domain_eq_def] >>
    simp [GSYM MAP_MAP_o, fst_alloc_defs, EXTENSION] >>
    rw [MEM_MAP] >>
    imp_res_tac env_rel_dom >>
    fs [] >>
    metis_tac [FST, MEM_MAP]
  )
  >- (
    first_x_assum irule >>
    metis_tac [env_rel_weak, SUBMAP_REFL]
  )
QED

Theorem compile_correct_Dletrec[local]:
  ^(#get_goal compile_correct_setup `Case [Dletrec _ _]`)
Proof
  rpt disch_tac \\ fs [ELIM_UNCURRY, Q.ISPEC `FST` ETA_THM]
  \\ simp [compile_funs_dom2]
  \\ drule invariant_make_varls
  \\ disch_then (qsubterm_then `evaluate _ _ _` mp_tac)
  \\ simp []
  \\ impl_tac
  >- (
    simp [build_rec_env_merge, MAP_MAP_o, o_DEF, ELIM_UNCURRY, ETA_THM]
    \\ simp [compile_funs_dom2]
    \\ fs [idx_prev_def]
  )
  \\ rw []
  \\ simp []
  \\ imp_res_tac invariant_IMP_s_rel
  \\ asm_exists_tac
  \\ fs [build_rec_env_merge, MAP_MAP_o, o_DEF]
  \\ conj_tac
  >- (
    simp [env_domain_eq_def]
    \\ simp [semanticPrimitivesPropsTheory.build_rec_env_merge]
    \\ simp [GSYM MAP_MAP_o, fst_alloc_defs]
    \\ simp [MAP_MAP_o, o_DEF, ELIM_UNCURRY, MAP_REVERSE]
  )
  \\ simp [semanticPrimitivesPropsTheory.build_rec_env_merge]
  \\ fs [MAP_MAP_o, o_DEF, ELIM_UNCURRY, Q.ISPEC `FST` ETA_THM]
  \\ fs [compile_funs_dom2]
  \\ first_x_assum irule
  \\ simp [source_to_flatTheory.compile_funs_map, MAP_MAP_o]
  \\ simp [env_rel_LIST_REL, EVERY2_MAP]
  \\ irule EVERY2_refl
  \\ simp [FORALL_PROD]
  \\ simp [Once v_rel_cases]
  \\ rw [source_to_flatTheory.compile_funs_map, MAP_EQ_f, FORALL_PROD]
  \\ qexistsl_tac [`comp_map`, `env`, `nsEmpty`, `path`, `MAP (K None) funs`]
  \\ simp []
  \\ drule_then (fn t => simp [t]) global_env_inv_weak
  \\ rw []
  \\ simp [bind_locals_def, MAP2_MAP, ZIP_MAP, MAP_MAP_o, o_DEF, v_rel_rules]
QED

Theorem compile_correct_Dtype[local]:
  ^(#get_goal compile_correct_setup `Case [Dtype _ _]`)
Proof
  simp [markerTheory.Case_def] >>
  MAP_EVERY qid_spec_tac [`genv`, `idx`, `comp_map`, `env`, `s`, `s_i1`] >>
  Induct_on `tds`
  >- ( (* No tds *)
    rw [evaluate_def] >>
    simp [build_tdefs_def, v_rel_global_eqn, env_domain_eq_def] >>
    qexists_tac `genv` >>
    simp [subglobals_refl] >>
    fs [invariant_def, s_rel_cases] >>
    simp [Q.prove (`(n with tidx := n.tidx) = n`,
      simp [next_indices_component_equality])]
  ) >>
  strip_tac >>
  rename [`EVERY check_dup_ctors (td::tds)`] >>
  `?tvs tn ctors. td = (tvs, tn ,ctors)` by metis_tac [pair_CASES] >>
  rw [evaluate_def] >>
  pairarg_tac >>
  fs [] >>
  simp [evaluate_def] >>
  drule_then (drule_then drule) alloc_tags_invariant >>
  impl_tac
  >- (
    fs [check_dup_ctors_thm] >>
    fs [idx_prev_def]
  ) >>
  rw [] >>
  drule_then drule global_env_inv_weak >>
  rw [subglobals_refl] >>
  first_x_assum (drule_then drule) >>
  imp_res_tac invariant_IMP_s_rel >>
  fs [ADD1] >>
  rw [] >>
  simp [o_DEF, ADD1] >>
  qexists_tac ‘genv''’ >>
  (* goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac) >> *)
  simp [build_tdefs_def, Once nsAppend_foldl] >>
  simp [GSYM extend_dec_env_v_empty, GSYM extend_env_v_empty] >>
  rw [] >> simp []
  >- (
    metis_tac [SUBMAP_TRANS]
  )
  >- (
    metis_tac [SUBMAP_TRANS]
  )
  >- (
    simp [build_tdefs_def, Once nsAppend_foldl] >>
    simp [GSYM extend_dec_env_v_empty, GSYM extend_env_v_empty] >>
    irule env_domain_eq_append >>
    simp []
  )
  >- (
    simp [build_tdefs_def, Once nsAppend_foldl] >>
    simp [GSYM extend_dec_env_v_empty, GSYM extend_env_v_empty] >>
    irule global_env_inv_append >>
    simp [] >>
    drule_then irule global_env_inv_weak >>
    simp []
  )
QED

Theorem compile_correct_Dtabbrev[local]:
  ^(#get_goal compile_correct_setup `Case [Dtabbrev _ _ _ _]`)
Proof
  rw [] >>
  asm_exists_tac >>
  fs [v_rel_global_eqn, empty_env_def, env_domain_eq_def, subglobals_refl]
QED

Theorem compile_correct_Denv[local]:
  ^(#get_goal compile_correct_setup `Case [Denv _]`)
Proof
  rw []
  \\ fs [option_case_eq, pair_case_eq]
  \\ fs [declare_env_def, option_case_eq, CaseEq "eval_state"]
  \\ rveq \\ fs []
  >- (
    (* incorrect eval state type *)
    fs [invariant_def, orac_rel_def]
    \\ rfs []
  )
  \\ simp [evaluate_def, do_app_def, env_id_tuple_def]
  \\ rfs [invariant_def, fin_idx_match_def, src_orac_invs_def]
  \\ drule_then strip_assume_tac step_1
  \\ fs []
  \\ `idx.vidx < LENGTH s_i1.globals ∧ EL idx.vidx s_i1.globals = NONE`
    by (
    fs [s_rel_cases, idx_range_rel_def, idx_prev_def, genv_allocated_idxs_def]
    \\ rveq \\ fs []
    \\ qspecl_then [`(i,Idx_Var)`, `0`] drule ALL_DISJOINT_elem
    \\ simp [idx_block_def]
  )
  \\ csimp [env_domain_eq_def]
  \\ qmatch_goalsub_abbrev_tac `LUPDATE (SOME v)`
  \\ qexists_tac `genv with <| v := LUPDATE (SOME v) idx.vidx genv.v |>`
  \\ `subglobals genv.v (LUPDATE (SOME v) idx.vidx genv.v)`
    by (
    rw [subglobals_def, EL_LUPDATE]
    \\ rw [] \\ fs [IS_SOME_EXISTS] \\ fs []
    \\ rfs [invariant_def, s_rel_cases]
  )
  \\ simp [src_orac_next_cfg_def]
  \\ fs [EL_LUPDATE, invariant_def, s_rel_cases]
  \\ rfs []
  \\ rw []
  \\ TRY (fs [src_orac_step_invs_def, orac_rel_def, src_orac_gen_inv_def,
        orac_rel_inner_def]
    \\ rfs [src_orac_next_cfg_def]
    \\ fsrw_tac [SATISFY_ss] [] \\ NO_TAC)
  >- (
    drule_then irule LIST_REL_sv_rel_weak
    \\ simp []
  )
  >- (
    fs [idx_range_rel_def, src_orac_next_cfg_def, genv_allocated_idxs_def]
    \\ rfs []
    \\ drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE)
    \\ simp [LUPDATE_compute]
    \\ qexists_tac `{(idx.vidx, Idx_Var)}`
    \\ simp [EXTENSION, idx_types_FORALL, FORALL_PROD]
    \\ fs [idx_block_def, EL_LUPDATE, bool_case_eq, idx_prev_def]
    \\ metis_tac []
  )
  >- (
    fs [src_orac_env_invs_def, env_gen_future_rel_def]
    \\ rfs [src_orac_next_cfg_def]
    \\ fs [env_gen_rel_def, oEL_THM]
    \\ rveq \\ fs []
    \\ fs [EL_LUPDATE, EL_APPEND_IF]
    \\ rw []
    \\ fs [EL_APPEND_IF]
    \\ rw []
    \\ TRY (res_tac \\ fs [] \\ drule_then irule global_env_inv_weak)
    \\ fs [subspt_lookup]
    \\ first_x_assum (qspec_then `id` mp_tac)
    \\ simp [lookup_insert]
    \\ rfs []
    \\ rw [miscTheory.EL_CONS_IF]
    \\ drule_then irule global_env_inv_weak
    \\ simp []
  )
  >- (
    fs [orac_rel_def]
    \\ qexists_tac `s_compiler`
    \\ fsrw_tac [SATISFY_ss] [orac_rel_inner_def]
  )
  >- (
    fs [eval_ref_inv_def]
    \\ Cases_on `s_i1.globals` \\ fs []
    \\ Cases_on `idx.vidx` \\ fs []
    \\ simp [LUPDATE_def]
  )
  >- (
    fs [env_gen_inv_def]
    \\ drule_then irule SUBSET_TRANS
    \\ simp [pred_setTheory.COUNT_MONO]
  )
  >- (
    simp [orac_forward_rel_def, eval_state_call_rel_def, EL_LUPDATE]
    \\ rfs [orac_config_envs_subspt_def, src_orac_next_cfg_def]
  )
  >- (
    fs [env_gen_rel_def, oEL_THM]
    \\ simp [EL_LUPDATE]
  )
  >- (
    simp [Once v_rel_cases]
    \\ fs [EL_LUPDATE, markerTheory.Abbrev_def, v_rel_eqns]
    \\ simp [nat_to_v_def, v_rel_eqns]
    \\ fs [oEL_THM]
    \\ rveq \\ fs []
    \\ fs [env_gen_rel_def]
  )
QED

Theorem compile_correct_Dexn[local]:
  ^(#get_goal compile_correct_setup `Case [Dexn _ _ _]`)
Proof
  reverse (rw [evaluate_def]) >>
  fs [v_rel_eqns, invariant_def, s_rel_cases] >>
  qexists_tac `genv with c := FUNION genv.c
      (FEMPTY |+ (((idx.eidx,NONE),LENGTH ts), ExnStamp s.next_exn_stamp))` >>
  rfs [SUBMAP_FUNION_ID, subglobals_refl, env_domain_eq_def, UNION_COMM] >>
  rw []
  >- (
    drule_then irule LIST_REL_sv_rel_weak
    \\ simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    drule_then irule genv_c_ok_extend >>
    simp [FLOOKUP_UPDATE] >>
    simp [semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
    simp [ctor_same_type_def] >>
    CCONTR_TAC >> fs [idx_range_rel_def] >>
    rfs [FRANGE_FLOOKUP]
  )
  >- (
    fs [genv_c_tys_ok_def]
  )
  >- (
    drule_then irule LIST_REL_sv_rel_weak
    \\ simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    fs [idx_range_rel_def, FRANGE_FUNION, genv_allocated_idxs_def] >>
    rw [] >>
    TRY asm_exists_tac >>
    fs [FRANGE_FLOOKUP, FLOOKUP_FUNION, option_case_eq, FLOOKUP_UPDATE] >>
    drule_then irule (Q.SPECL [`0`, `3`] ALL_DISJOINT_MOVE) >>
    simp [LUPDATE_compute] >>
    qexists_tac `{(idx.eidx, Idx_Exn)}` >>
    simp [EXTENSION, FORALL_PROD, idx_types_FORALL, idx_block_def] >>
    fs [idx_prev_def] >>
    metis_tac []
  )
  >- (
    drule_then irule src_orac_invs_weak
    \\ simp [subglobals_refl, SUBMAP_FUNION_ID]
  )
  >- (
    gvs [v_rel_global_eqn]
    \\ simp [FLOOKUP_FUNION, option_case_eq, FLOOKUP_UPDATE]
    \\ CCONTR_TAC
    \\ fs [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
    \\ rfs [FDOM_FLOOKUP]
    \\ res_tac >>
    rfs [] >>
    rveq >> fs [] >>
    fs [idx_range_rel_def, ALL_DISJOINT_DEF, genv_allocated_idxs_def] >>
    first_x_assum (qspecl_then [`0`, `3`] mp_tac) >>
    simp [EXTENSION] >>
    qexists_tac `(idx.eidx, Idx_Exn)` >>
    fs [idx_block_def, idx_prev_def] >>
    fs [FLOOKUP_DEF] >>
    asm_exists_tac >>
    simp []
  )
QED

Theorem compile_correct_Dmod[local]:
  ^(#get_goal compile_correct_setup `Case [Dmod _ _]`)
Proof
  rw [] >> fs [pair_case_eq] >> fs [] >>
  rpt (pairarg_tac >> fs []) >>
  rw [] >>
  first_x_assum drule >>
  disch_then drule >>
  simp [] >>
  (impl_tac >- (strip_tac >> fs [])) >>
  rw [] >>
  rw [] >>
  qexists_tac `genv'` >>
  simp [case_eq_thms, PULL_EXISTS] >>
  imp_res_tac not_abort_IMP_cases >> fs [result_rel_eqns] >>
  rw []
  >- (
    fs [env_domain_eq_def, lift_env_def] >>
    rw [nsDom_nsLift, nsDomMod_nsLift])
  >- (
    rw [] >>
    fs [v_rel_global_eqn] >>
    rw [lift_env_def, nsLookup_nsLift] >>
    CASE_TAC >>
    rw [] >>
    fs [])
QED

Theorem compile_correct_Dlocal[local]:
  ^(#get_goal compile_correct_setup `Case [Dlocal _ _]`)
Proof
  rw [] >> fs [pair_case_eq] >> fs [] >>
  rpt (pairarg_tac >> fs []) >>
  rveq >> fs [] >>
  imp_res_tac compile_decs_idx_prev >>
  first_x_assum (drule_then drule) >>
  simp [] >>
  impl_tac >- (
    fs [invariant_def]
    \\ imp_res_tac compile_decs_env_gen_inv
    \\ imp_res_tac compile_decs_future_rel
    \\ rpt strip_tac \\ fs []
    \\ fsrw_tac [SATISFY_ss] [idx_prev_trans]
  ) >>
  rw [evaluate_decs_append] >>
  reverse (fs [case_eq_thms])
  >- ( (* err case *)
    fs [] >>
    rw [] >>
    asm_exists_tac >>
    rw [] >>
    fs [] >>
    drule_then irule invariant_idx_range_shrink_gen >>
    imp_res_tac compile_decs_env_gen_inv >>
    simp []
  ) >>
  (* result case *)
  rveq >>
  fs [] >>
  first_x_assum (drule_then drule) >>
  imp_res_tac env_gen_future_rel_forward >>
  impl_tac
  >- metis_tac [global_env_inv_append, global_env_inv_weak] >>
  rw [] >>
  imp_res_tac evaluate_decs_append >>
  fs [] >>
  asm_exists_tac >>
  metis_tac trans_thms
QED

Theorem compile_correct:
  ^(#concl compile_correct_setup ())
Proof
  #init compile_correct_setup [
    compile_correct_seq, compile_correct_Raise, compile_correct_Handle,
    compile_correct_Con, compile_correct_Var, compile_correct_Fun,
    compile_correct_App, compile_correct_Log, compile_correct_If,
    compile_correct_Mat, compile_correct_Let, compile_correct_Letrec,
    compile_correct_pattern, compile_correct_empty_decs,
    compile_correct_cons_decs, compile_correct_Dlet, compile_correct_Dletrec,
    compile_correct_Dtype, compile_correct_Dtabbrev, compile_correct_Denv,
    compile_correct_Dexn, compile_correct_Dmod, compile_correct_Dlocal]
  (* trivial cases *)
  \\ TRY (
    rw []
    \\ goal_assum (first_assum o mp_then (Pat `invariant`) mp_tac)
    \\ simp [subglobals_refl]
    \\ NO_TAC
  )
  \\ TRY (Cases_on`l`>>fs[evaluate_def,compile_exp_def])
  \\ fs[s_rel_cases]
QED

Definition init_eval_state_ok_def:
  (init_eval_state_ok NONE = T) /\
  (init_eval_state_ok (SOME (EvalDecs _)) = F) /\
  (init_eval_state_ok (SOME (EvalOracle s)) <=>
    s.generation = 0 /\ s.envs = [[]])
End

Definition init_genv_ty_els_def:
  init_genv_ty_els = [
    (bool_id, [(false_tag, 0n, TypeStamp «False» bool_type_num);
        (true_tag, 0n, TypeStamp «True» bool_type_num)]);
    (list_id, REVERSE [(cons_tag, 2n, TypeStamp «::» list_type_num);
        (nil_tag, 0n, TypeStamp «[]» list_type_num)])]
End

Definition init_genv_els_def:
  init_genv_els = FLAT (MAP (\(id, xs).
        MAP (\(tag, arity, stamp). (((tag, SOME id), arity), stamp)) xs)
    init_genv_ty_els) ++ [
    (((div_tag, NONE), 0n), div_stamp);
    (((chr_tag, NONE), 0n), chr_stamp);
    (((subscript_tag, NONE), 0n), subscript_stamp);
    (((bind_tag, NONE), 0n), bind_stamp)]
End

Definition init_genv_def:
  init_genv = <| v := []; c := FEMPTY |++ init_genv_els;
    tys := FEMPTY |++ MAP (I ## MAP (I ## FST)) init_genv_ty_els |>
End

Theorem init_genv_ok:
  genv_c_ok init_genv.c
Proof
  simp [genv_c_ok_def]
  \\ rpt (conj_tac >- EVAL_TAC)
  \\ simp [init_genv_def, EVAL ``init_genv_els``, flookup_fupdate_list]
  \\ rw [] \\ full_simp_tac bool_ss []
  \\ TRY (simp_tac bool_ss [DISJ_EQ_IMP] \\ disch_tac \\ rw [])
  \\ EVAL_TAC
QED

Theorem init_genv_tys_ok:
  genv_c_tys_ok init_genv.c init_genv.tys
Proof
  EVAL_TAC \\ rw []
QED

Definition init_genv_next:
  init_genv_next = <|
    vidx := 0;
    tidx := SUC (MAX_LIST (MAP (\v. case SND v of TypeStamp _ i => i | _ => 0) init_genv_els));
    eidx := SUC (MAX_LIST (MAP (\v. case SND v of ExnStamp i => i | _ => 0) init_genv_els))
  |>
End

Definition init_global_env_inv_def:
  init_global_env_inv genv comp_map env <=>
  env.v = nsEmpty /\
  (case env.c of Bind ns ms => ms = [] /\
    EVERY (\(x, (arity, stamp)). case nsLookup comp_map.c (Short x) of
      NONE => F
    | SOME (cn, ty_gp) =>
        FLOOKUP genv.c ((cn, OPTION_MAP FST ty_gp), arity) = SOME stamp ∧
        (case ty_gp of NONE => T | SOME (ty_id, ctors) =>
            FLOOKUP genv.tys ty_id = SOME ctors)
    ) ns)
End

Theorem init_global_env_inv_imp:
  init_global_env_inv genv comp_map env ==>
  global_env_inv genv comp_map {} env
Proof
  rw [init_global_env_inv_def]
  \\ MAP_FIRST irule (CONJUNCTS v_rel_rules)
  \\ simp []
  \\ every_case_tac
  \\ Cases \\ simp [namespaceTheory.nsLookup_def]
  \\ rw []
  \\ imp_res_tac ALOOKUP_MEM
  \\ imp_res_tac EVERY_MEM
  \\ fs []
  \\ every_case_tac
  \\ fs []
QED

Definition precondition1_def:
  precondition1 interp g s1 env1 conf eval_conf prog ⇔
  src_orac_step_invs interp g s1.eval_state ∧
  orac_rel interp g s1.eval_state eval_conf ∧
  (case src_orac_next_cfg interp s1.eval_state of
    | NONE => T
    | SOME cfg => cfg = FST (compile_prog conf prog)) ∧
  conf.next.vidx = 0 ∧
  s1.refs = [] ∧
  init_global_env_inv init_genv conf.mod_env env1 ∧
  init_eval_state_ok s1.eval_state ∧
  idx_prev init_genv_next conf.next ∧
  EVERY (\(_, stamp). case stamp of TypeStamp cn t => t < s1.next_type_stamp
    | ExnStamp cn => cn < s1.next_exn_stamp) init_genv_els ∧
  conf.envs = empty_config.envs
End

Theorem precondition1_change_clock:
   precondition1 interp g s1 env1 conf eval_conf prog ⇒
   precondition1 interp g (s1 with clock := k) env1 conf eval_conf prog
Proof
  rw [precondition1_def]
QED

Theorem idx_block_union_final:
  idx_prev idx idx' ==>
  idx_block idx idx' ∪ idx_final_block idx' = idx_final_block idx
Proof
  simp [idx_prev_def, idx_block_def, idx_final_block_def, EXTENSION]
  \\ simp [FORALL_PROD, idx_types_FORALL]
QED

Theorem precondition_stamp_helper[local]:
  EVERY (\(_, stamp). case stamp of TypeStamp cn t => t < type_stamp
    | ExnStamp cn => cn < exn_stamp) init_genv_els ==>
  (∀cn t. t ≥ type_stamp ==> TypeStamp cn t ∉ FRANGE init_genv.c) ∧
  (∀cn. cn ≥ exn_stamp ==> ExnStamp cn ∉ FRANGE init_genv.c)
Proof
  rw [init_genv_def]
  \\ CCONTR_TAC
  \\ fs []
  \\ dxrule_then assume_tac (MATCH_MP SUBSET_IMP (SPEC_ALL FRANGE_FUPDATE_LIST_SUBSET))
  \\ fs [MEM_MAP, EXISTS_PROD, EVERY_MEM]
  \\ res_tac
  \\ fs []
QED

Theorem invariant_begin_alloc_blanks:
  precondition1 interp g s1 env1 cfg eval_conf prog /\
  cfg' = FST (compile_prog cfg prog) /\
  init_globs = SOME (Loc T 0) :: REPLICATE (cfg'.next.vidx - 1) NONE ==>
  invariant interp g
    <|next := 0; generation := cfg.envs.next; envs := LN|>
    (init_genv with v := init_globs)
    (cfg.next with vidx := 1, cfg'.next, {})
    s1
    (initial_state s1.ffi s1.clock eval_conf with
               <|refs := [Refv (Conv NONE [])]; globals := init_globs |>)
Proof
  rw []
  \\ fs [precondition1_def, invariant_def]
  \\ simp [init_genv_ok, init_genv_tys_ok]
  \\ fs [compile_prog_def]
  \\ rfs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp [EVAL ``(initial_state ffi clock ec).eval_config``,
    env_gen_inv_def, eval_ref_inv_def]
  \\ fs [empty_config_def]
  \\ imp_res_tac compile_decs_idx_prev
  \\ rw []
  >- (
    fs [s_rel_cases, initial_state_def]
  )
  >- (
    fs [idx_range_rel_def]
    \\ drule_then assume_tac precondition_stamp_helper
    \\ qexists_tac `next`
    \\ simp [idx_prev_refl]
    \\ conj_tac >- (
      every_case_tac \\ fs []
    )
    \\ Cases_on `next.vidx` \\ fs [idx_prev_def]
    \\ simp [init_genv_def]
    \\ fs [ALL_DISJOINT_CONS, idx_block_def, idx_final_block_def,
        genv_allocated_idxs_def]
    \\ fs [EVAL ``init_genv_els``, EVAL ``init_genv_ty_els``, FUPDATE_LIST_THM, DISJ_IMP_THM]
    \\ fs [DISJOINT_ALT, PULL_EXISTS, DISJ_IMP_THM, FORALL_AND_THM, EVAL ``init_genv_next``]
    \\ csimp [EL_CONS_IF, EL_REPLICATE]
  )
  >- (
    simp [src_orac_invs_def, src_orac_gen_inv_def, src_orac_env_invs_def]
    \\ every_case_tac \\ fs [init_eval_state_ok_def]
    \\ simp [env_store_inv_def]
    \\ imp_res_tac step_1 \\ fs []
  )
  >- (
    simp [fin_idx_match_def]
    \\ every_case_tac \\ fs []
    \\ imp_res_tac compile_decs_idx_prev
    \\ fs [idx_prev_def]
  )
QED

Theorem compile_prog_correct:
  precondition1 interp g s env cfg eval_conf ds ∧
  compile_prog cfg ds = (cfg', ds') ∧
  evaluate_decs s env ds = (s', r) ∧
  r <> Rerr (Rabort Rtype_error)
  ⇒
  ? s_i1 s_i1' genv' r_i1.
  s_i1 = initial_state s.ffi s.clock eval_conf ∧
  evaluate_decs s_i1 ds' = (s_i1', r_i1) ∧
  s_rel genv' s' s_i1' ∧
  (! res. r = Rval res ⇒ r_i1 = NONE) ∧
  (! err. r = Rerr err ⇒ ? err'. r_i1 = SOME err' ∧ err' <> Rabort Rtype_error
        ∧ result_rel (\a (b : unit) (c : unit). T) genv' (Rerr err) (Rerr err'))
Proof
  simp [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ fs [glob_alloc_def, alloc_env_ref_def, do_app_def, Unitv_def,
    evaluate_def, store_alloc_def]
  \\ fs [EVAL ``(initial_state _ _ _).globals``,
    EVAL ``(initial_state _ _ _).refs``]
  \\ drule invariant_begin_alloc_blanks
  \\ simp [compile_prog_def]
  \\ imp_res_tac compile_decs_idx_prev
  \\ fs [idx_prev_def, precondition1_def]
  \\ imp_res_tac init_global_env_inv_imp
  \\ Cases_on `next.vidx` \\ fs []
  \\ simp [LUPDATE_def]
  \\ rw []
  \\ drule_then drule (List.last (CONJUNCTS compile_correct))
  \\ rpt (disch_then drule)
  \\ simp [idx_prev_refl]
  \\ impl_tac >- (
    rw []
    >- (
      drule_then irule global_env_inv_weak
      \\ simp [subglobals_def, init_genv_def]
    )
    >- (
      simp [env_gen_rel_def]
      \\ every_case_tac \\ fs [init_eval_state_ok_def, empty_config_def]
    )
    >- (
      fs [env_gen_future_rel_def, init_eval_state_ok_def]
      \\ every_case_tac \\ fs []
      \\ simp [compile_prog_def]
      \\ imp_res_tac compile_decs_generation
      \\ fs []
    )
  )
  \\ rw []
  \\ simp []
  \\ asm_exists_tac
  \\ rw [] \\ fs []
  \\ fs [result_rel_cases]
  \\ rveq \\ fs []
QED

Theorem SND_eq[local]:
  SND x = y ⇔ ∃a. x = (a,y)
Proof
  Cases_on`x`\\rw[]
QED

Theorem compile_prog_semantics:
  precondition1 interp g s1 env1 conf eval_conf prog ⇒
   ¬semantics_prog s1 env1 prog Fail ⇒
   semantics_prog s1 env1 prog
      (semantics eval_conf s1.ffi
          (SND (compile_prog conf prog)))
Proof
  rw[semantics_prog_def,SND_eq]
  \\ fs []
  \\ simp[flatSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs[SND_eq]
  >- (
    fs[semantics_prog_def,SND_eq]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ fs [PAIR_FST_SND_EQ, FST_SND_EQ_CASE]
    \\ fs[evaluate_prog_with_clock_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ spose_not_then strip_assume_tac \\ fs[]
    \\ rveq \\ fs []
    \\ drule_then (qspec_then `k` assume_tac) precondition1_change_clock
    \\ drule compile_prog_correct
    \\ simp []
    \\ rename [`r <> Rerr _`]
    \\ Cases_on `r` \\ fs []
  )
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ conj_tac
  >- (
    rw[] \\ rw[semantics_prog_def]
    \\ fs[evaluate_prog_with_clock_def]
    \\ qexists_tac`k`
    \\ pairarg_tac \\ fs[]
    \\ rpt (first_x_assum (qspec_then `k` assume_tac))
    \\ drule_then (qspec_then `k` assume_tac) precondition1_change_clock
    \\ rfs []
    \\ drule compile_prog_correct
    \\ fs[FST_SND_EQ_CASE]
    \\ pairarg_tac \\ fs []
    \\ rw [] \\ fs []
    \\ TRY (fs [s_rel_cases] \\ NO_TAC)
    \\ every_case_tac \\ fs [result_rel_cases]
  )
  \\ rw[]
  \\ simp[semantics_prog_def]
  \\ conj_tac
  >- (
    rw[]
    \\ fs[evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs[]
    \\ imp_res_tac precondition1_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs [FST_SND_EQ_CASE]
    \\ rpt (pairarg_tac \\ fs [])
    \\ drule_then drule compile_prog_correct
    \\ rpt (disch_then drule)
    \\ impl_keep_tac
      >- (first_x_assum(qspecl_then[`k`,`st'.ffi`]strip_assume_tac)
          \\ rfs [])
    \\ fs [initial_state_clock]
    \\ strip_tac
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ rveq \\ fs[]
    \\ every_case_tac \\ fs[]
    \\ CCONTR_TAC \\ fs[]
    \\ rveq
    \\ fs[result_rel_cases]
    \\ Cases_on`r`\\fs[])
  \\ qmatch_abbrev_tac`lprefix_lub l1 (build_lprefix_lub l2)`
  \\ `l2 = l1`
  by (
    unabbrev_all_tac
    \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM]
    \\ fs[evaluate_prog_with_clock_def]
    \\ gen_tac
    \\ pairarg_tac \\ fs[]
    \\ AP_TERM_TAC
    \\ imp_res_tac precondition1_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs [FST_SND_EQ_CASE]
    \\ rpt (pairarg_tac \\ fs [])
    \\ drule_then drule compile_prog_correct
    \\ rpt (disch_then drule)
    \\ fs[]
    \\ `r ≠ Rerr (Rabort Rtype_error)`
       by (first_x_assum(qspecl_then[`k`,`st'.ffi`]strip_assume_tac)
          \\ rfs [])
    \\ fs [initial_state_clock]
    \\ strip_tac
    \\ fs[]
    \\ rfs[invariant_def,s_rel_cases,initial_state_def])
  \\ fs[Abbr`l1`,Abbr`l2`]
  \\ match_mp_tac build_lprefix_lub_thm
  \\ Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF]
  \\ REWRITE_TAC[IMAGE_COMPOSE]
  \\ match_mp_tac prefix_chain_lprefix_chain
  \\ simp[prefix_chain_def,PULL_EXISTS]
  \\ simp[evaluate_prog_with_clock_def]
  \\ qx_genl_tac[`k1`,`k2`]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ metis_tac[evaluatePropsTheory.evaluate_decs_ffi_mono_clock,
               evaluatePropsTheory.io_events_mono_def,
               LESS_EQ_CASES,FST]
QED

(* - connect semantics theorems of flat-to-flat passes --------------------- *)

Theorem compile_flat_correct:
   flat_patternProof$install_conf_rel cfg ec1 ec2 /\
   semantics ec1 ffi prog <> Fail
   ==>
   semantics ec1 ffi prog =
   semantics ec2 ffi (compile_flat cfg prog)
Proof
  rw [compile_flat_def]
  \\ metis_tac [flat_patternProofTheory.compile_decs_semantics,
        flat_elimProofTheory.flat_remove_semantics]
QED

Definition precondition_def:
  precondition interp s env cfg ec prog <=>
  ?ec1 g. precondition1 interp g s env cfg ec1 prog /\
    flat_patternProof$install_conf_rel cfg.pattern_cfg ec1 ec
End

Theorem compile_semantics:
   precondition interp s env cfg ec prog
 ⇒
   ¬semantics_prog s env prog Fail ⇒
   semantics_prog s env prog
      (semantics ec s.ffi (SND (compile cfg prog)))
Proof
  rw [compile_def]
  \\ pairarg_tac \\ fs []
  \\ fs [precondition_def]
  \\ imp_res_tac compile_prog_semantics \\ rfs []
  \\ DEP_REWRITE_TAC [GSYM compile_flat_correct]
  \\ simp []
  \\ fs [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ strip_tac \\ fs []
QED

(* - esgc_free theorems for compile_exp ------------------------------------ *)

Theorem op_gbag_astOp_to_flatOp:
  op_gbag (astOp_to_flatOp op) = {||}
Proof
  Cases_on `op` \\ simp [astOp_to_flatOp_def, op_gbag_def]
QED

Theorem compile_exp_esgc_free:
   (!tra env exp.
      esgc_free (compile_exp tra env exp) /\
      set_globals (compile_exp tra env exp) = {||}) /\
   (!tra env exps.
      EVERY esgc_free (compile_exps tra env exps) /\
      elist_globals (compile_exps tra env exps) = {||}) /\
   (!tra env pes.
      EVERY esgc_free (MAP SND (compile_pes tra env pes)) /\
      elist_globals (MAP SND (compile_pes tra env pes)) = {||}) /\
   (!tra env funs.
      EVERY esgc_free (MAP (SND o SND) (compile_funs tra env funs)) /\
      elist_globals (MAP (SND o SND) (compile_funs tra env funs)) = {||})
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ fs [compile_exp_def]
  \\ rpt (TOP_CASE_TAC \\ fs [])
  \\ fs [compile_exp_def]
  \\ simp [op_gbag_def, Bool_def, op_gbag_astOp_to_flatOp]
  >- (
   rename [`compile_var _ x`] \\ Cases_on `x` \\ fs [compile_var_def]
   \\ simp [op_gbag_def]
  )
  >- (
    fs [FOLDR_REVERSE, FOLDL_invariant, EVERY_MEM]
    \\ fs [flatPropsTheory.elist_globals_eq_empty]
    \\ DEEP_INTRO_TAC FOLDL_invariant
    \\ fs [op_gbag_def]
  )
QED

(* - esgc_free theorems for compile_decs ----------------------------------- *)

Theorem set_globals_make_varls:
   ∀a b c d. flatProps$set_globals (make_varls a b c d) =
             LIST_TO_BAG (MAP ((+)c) (COUNT_LIST (LENGTH d)))
Proof
  recInduct source_to_flatTheory.make_varls_ind
  \\ rw[source_to_flatTheory.make_varls_def]
  >- EVAL_TAC
  >- ( EVAL_TAC \\ rw[] \\ rw[EL_BAG] )
  \\ simp[COUNT_LIST_def, MAP_MAP_o, ADD1, o_DEF, LIST_TO_BAG_def]
  \\ EVAL_TAC
  \\ AP_THM_TAC
  \\ simp[FUN_EQ_THM]
  \\ simp[BAG_INSERT_UNION]
QED

Theorem make_varls_esgc_free:
   !n t idx xs.
     esgc_free (make_varls n t idx xs)
Proof
  ho_match_mp_tac make_varls_ind
  \\ rw [make_varls_def]
QED

Theorem nsAll_extend_env:
   nsAll P e1.v /\ nsAll P e2.v ==> nsAll P (extend_env e1 e2).v
Proof
  simp [extend_env_def, nsAll_nsAppend]
QED

Theorem compile_decs_esgc_free:
  !t n next env envs decs n' next' env' envs' decs'.
    compile_decs t n next env envs decs = (n', next', env', envs', decs')
     ==>
     EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet decs'))
Proof
  ho_match_mp_tac compile_decs_ind
  \\ rw [compile_decs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ fs [compile_exp_esgc_free, make_varls_esgc_free]
  \\ fs [EVERY_MAP, EVERY_FILTER, MAP_FILTER]
  \\ simp [EVERY_MEM, MEM_MAPi, PULL_EXISTS, UNCURRY, env_id_tuple_def]
QED

(* - the source_to_flat compiler produces things which are esgc_free ------- *)

Theorem compile_prog_esgc_free:
   compile_prog c p = (c1, p1)
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet p1))
Proof
  rw [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs [glob_alloc_def]
  \\ simp [alloc_env_ref_def]
  \\ metis_tac [compile_decs_esgc_free]
QED

Theorem compile_flat_esgc_free:
   compile_flat cfg ds = ds' /\
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds'))
Proof
  rw [compile_flat_def, compile_def]
  \\ irule flat_patternProofTheory.compile_decs_esgc_free
  \\ simp [flat_elimProofTheory.remove_flat_prog_esgc_free]
QED

Theorem compile_esgc_free:
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (SND (compile c p))))
Proof
  rw [compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ metis_tac [compile_prog_esgc_free, compile_flat_esgc_free]
QED

Theorem inc_compile_prog_esgc_free:
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (SND (inc_compile_prog env_id c p))))
Proof
  rw [inc_compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs [glob_alloc_def]
  \\ simp [store_env_id_def, env_id_tuple_def, FILTER_APPEND]
  \\ metis_tac [compile_decs_esgc_free]
QED

Theorem inc_compile_esgc_free:
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (SND (inc_compile env_id c p))))
Proof
  rw [inc_compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ irule flat_patternProofTheory.compile_decs_esgc_free
  \\ metis_tac [inc_compile_prog_esgc_free, SND]
QED

Theorem compile_no_Mat:
  no_Mat_decs (SND (compile c prog))
Proof
  fs [compile_def, compile_prog_def, compile_flat_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ irule flat_patternProofTheory.compile_decs_no_Mat
QED

Theorem inc_compile_no_Mat:
  no_Mat_decs (SND (inc_compile env_id c prog))
Proof
  fs [inc_compile_def, inc_compile_prog_def, compile_flat_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ irule flat_patternProofTheory.compile_decs_no_Mat
QED

Theorem mem_size_lemma[local]:
  list_size sz xs < N ==> (MEM x xs ⇒ sz x < N)
Proof
  Induct_on `xs` \\ rw [list_size_def] \\ fs []
QED

Definition num_bindings_def[simp]:
   (num_bindings (Dlet _ p _) = LENGTH (pat_bindings p [])) ∧
   (num_bindings (Dletrec _ f) = LENGTH f) ∧
   (num_bindings (Dmod _ ds) = SUM (MAP num_bindings ds)) ∧
   (num_bindings (Dlocal lds ds) = SUM (MAP num_bindings lds)
        + SUM (MAP num_bindings ds)) ∧
   (num_bindings (Denv _) = 1) ∧
   (num_bindings _ = 0)
Termination
  wf_rel_tac`measure dec_size`
End


Theorem compile_decs_num_bindings:
  !t n next env envs decs n' next' env' envs' decs'.
    compile_decs t n next env envs decs = (n', next', env', envs', decs') ⇒
     next.vidx ≤ next'.vidx ∧
     SUM (MAP num_bindings decs) = next'.vidx - next.vidx
Proof
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ simp [markerTheory.Abbrev_def]
  \\ rw[]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ fsrw_tac [ETA_ss] []
  \\ DECIDE_TAC
QED

val COUNT_LIST_ADD_SYM = COUNT_LIST_ADD
  |> CONV_RULE (SIMP_CONV bool_ss [Once ADD_SYM]);

Theorem MAPi_SNOC: (* TODO: move *)
  !xs x f. MAPi f (SNOC x xs) = SNOC (f (LENGTH xs) x) (MAPi f xs)
Proof
  Induct \\ fs [SNOC,SNOC_APPEND]
QED

Theorem compile_decs_elist_globals:
  !t n next env envs decs n' next' env' envs' decs'.
    compile_decs t n next env envs decs = (n', next', env', envs', decs') ⇒
    elist_globals (MAP dest_Dlet (FILTER is_Dlet decs')) =
      LIST_TO_BAG (MAP ((+) next.vidx) (COUNT_LIST (SUM (MAP num_bindings decs))))
Proof
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ rw[set_globals_make_varls]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw[compile_exp_esgc_free, EVAL ``COUNT_LIST 0``]
  \\ fs [FILTER_APPEND, Q.ISPEC `num_bindings` ETA_THM]
  \\ simp [op_gbag_def, env_id_tuple_def, EVAL ``COUNT_LIST 1``]
  >- (
    simp [flatPropsTheory.elist_globals_append, FILTER_APPEND]
    \\ drule compile_decs_esgc_free
    \\ rw []
    \\ imp_res_tac compile_decs_num_bindings
    \\ rw [COUNT_LIST_ADD_SYM]
    \\ srw_tac [ETA_ss] [LIST_TO_BAG_APPEND, MAP_MAP_o, o_DEF]
    \\ AP_TERM_TAC
    \\ simp [MAP_EQ_f]
  )
  >- (
    simp[flatPropsTheory.elist_globals_append, FILTER_APPEND]
    \\ drule compile_decs_esgc_free
    \\ rw[]
    \\ imp_res_tac compile_decs_num_bindings
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`a + (b + c)`
    \\ `a + (b + c) = b + (a + c)` by simp[]
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[Once COUNT_LIST_ADD,SimpRHS]
    \\ simp[LIST_TO_BAG_APPEND]
    \\ simp[MAP_MAP_o, o_DEF]
    \\ rw[]
    \\ AP_TERM_TAC
    \\ fs[MAP_EQ_f]
  )
QED

Theorem compile_flat_sub_bag:
  elist_globals (MAP dest_Dlet (FILTER is_Dlet (compile_flat cfg p))) <=
  elist_globals (MAP dest_Dlet (FILTER is_Dlet p))
Proof
  fs [source_to_flatTheory.compile_flat_def]
  \\ metis_tac [
       flat_elimProofTheory.remove_flat_prog_sub_bag,
       flat_patternProofTheory.compile_decs_elist_globals,
       SUB_BAG_TRANS]
QED

Theorem compile_flat_BAG_ALL_DISTINCT[local] = MATCH_MP
    ( BAG_ALL_DISTINCT_SUB_BAG |> REWRITE_RULE [GSYM AND_IMP_INTRO] )
    compile_flat_sub_bag

Theorem compile_globals_BAG_ALL_DISTINCT:
  BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet (SND (compile c prog)))))
Proof
  rw []
  \\ fs [compile_def, compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ irule compile_flat_BAG_ALL_DISTINCT
  \\ fs [glob_alloc_def, op_gbag_def, alloc_env_ref_def]
  \\ imp_res_tac compile_decs_elist_globals
  \\ simp [bagTheory.BAG_ALL_DISTINCT_BAG_UNION, bagTheory.BAG_DISJOINT_BAG_INSERT,
        containerTheory.IN_LIST_TO_BAG, MEM_MAP]
  \\ fs [LIST_TO_BAG_DISTINCT]
  \\ irule listTheory.ALL_DISTINCT_MAP_INJ
  \\ fs [all_distinct_count_list]
QED

Theorem inc_compile_globals_BAG_ALL_DISTINCT:
  BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet
    (SND (inc_compile env_id c prog)))))
Proof
  rw []
  \\ fs [inc_compile_def, inc_compile_prog_def]
  \\ rpt (pairarg_tac \\ full_simp_tac bool_ss [UNCURRY_DEF])
  \\ simp[]
  \\ match_mp_tac BAG_ALL_DISTINCT_SUB_BAG
  \\ (irule_at Any) flat_patternProofTheory.compile_decs_elist_globals
  \\ rw []
  \\ fs [glob_alloc_def, op_gbag_def, store_env_id_def, FILTER_APPEND,
        elist_globals_append, env_id_tuple_def]
  \\ imp_res_tac compile_decs_elist_globals
  \\ fs [LIST_TO_BAG_DISTINCT]
  \\ irule listTheory.ALL_DISTINCT_MAP_INJ
  \\ fs [all_distinct_count_list]
QED

Theorem SUB_BAG_IMP:
  (B1 <= B2) ==> x ⋲ B1 ==> x ⋲ B2
Proof
  rw []
  \\ imp_res_tac bagTheory.SUB_BAG_SET
  \\ imp_res_tac SUBSET_IMP
  \\ fs []
QED

(* not sure if this variant of the inc. compiler is the one we need *)
Theorem monotonic_globals_state_co_compile:
  compile conf prog = (conf',p) ∧ FST (FST (orac 0)) = conf' ∧
  is_state_oracle (\c (env_id, decs). inc_compile env_id c (f decs)) orac ⇒
  oracle_monotonic
    (IMAGE SUC ∘ SET_OF_BAG ∘ elist_globals ∘ MAP flatProps$dest_Dlet ∘
      FILTER flatProps$is_Dlet ∘ SND) $<
    (0 INSERT IMAGE SUC (SET_OF_BAG (elist_globals (MAP flatProps$dest_Dlet
                (FILTER flatProps$is_Dlet p)))))
    (state_co (\c (env_id, decs). inc_compile env_id c (f decs)) orac)
Proof
  rw []
  \\ irule (Q.ISPEC `\c. SUC c.next.vidx` oracle_monotonic_state)
  \\ fs [FORALL_PROD]
  \\ fs [compile_def, compile_prog_def, inc_compile_def, inc_compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ conj_tac
  \\ rpt (disch_tac ORELSE gen_tac)
  \\ TRY (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ simp[PULL_EXISTS,PULL_FORALL] \\ rpt strip_tac
  \\ TRY(drule_at Any (MATCH_MP SUB_BAG_IMP (SPEC_ALL flat_patternProofTheory.compile_decs_elist_globals)) \\ strip_tac)
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs[]
  \\ imp_res_tac compile_decs_elist_globals
  \\ imp_res_tac compile_decs_num_bindings
  \\ fs []
  \\ rpt (disch_tac ORELSE gen_tac)
  \\ fs [glob_alloc_def, alloc_env_ref_def, flatPropsTheory.op_gbag_def]
  \\ TRY (drule (MATCH_MP SUB_BAG_IMP (compile_flat_sub_bag)))
  \\ fs [FILTER_APPEND, store_env_id_def, elist_globals_append,
        env_id_tuple_def, op_gbag_def]
  \\ rfs []
  \\ fs [Q.ISPEC `FST (FST _)` (Q.SPEC `x` EQ_SYM_EQ)]
  \\ rw [] \\ fs []
  \\ fs [IN_LIST_TO_BAG, MEM_MAP, MEM_COUNT_LIST]
QED
