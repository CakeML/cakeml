(*
  Correctness proof for source_to_flat
*)

open preamble semanticsTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     source_to_flatTheory flatLangTheory flatSemTheory flatPropsTheory

val _ = new_theory "source_to_flatProof";

val grammar_ancestry =
  ["source_to_flat","flatProps","namespaceProps",
   "semantics","semanticPrimitivesProps","ffi","lprefix_lub",
   "backend_common","misc"];
val _ = set_grammar_ancestry grammar_ancestry;

(* TODO: move *)

val compile_exps_length = Q.prove (
  `LENGTH (compile_exps t m es) = LENGTH es`,
  induct_on `es` >>
  rw [compile_exp_def]);

Theorem mapi_map:
   !f g l. MAPi f (MAP g l) = MAPi (\i x. f i (g x)) l
Proof
  Induct_on `l` >>
  rw [combinTheory.o_DEF]
QED

val fst_lem = Q.prove (
  `(λ(p1,p1',p2). p1) = FST`,
  rw [FUN_EQ_THM] >>
  pairarg_tac >>
  rw []);

val funion_submap = Q.prove (
  `FUNION x y SUBMAP z ∧ DISJOINT (FDOM x) (FDOM y) ⇒ y SUBMAP z`,
  rw [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, FUNION_DEF] >>
  metis_tac []);

val flookup_funion_submap = Q.prove (
  `(x ⊌ y) SUBMAP z ∧
   FLOOKUP (x ⊌ y) k = SOME v
   ⇒
   FLOOKUP z k = SOME v`,
  rw [SUBMAP_DEF, FLOOKUP_DEF] >>
  metis_tac []);

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
val bind_locals_def = Define `
  bind_locals ts locals comp_map =
    nsBindList (MAP2 (\t x. (x, flatLang$Var_local t x)) ts locals) comp_map`;

val nsAppend_bind_locals = Q.prove(`
  ∀funs.
  nsAppend (alist_to_ns (MAP (λx. (x,Var_local t x)) (MAP FST funs))) (bind_locals ts locals comp_map) =
  bind_locals (REPLICATE (LENGTH funs) t ++ ts) (MAP FST funs ++ locals) comp_map`,
  Induct_on`funs`>>fs[FORALL_PROD,bind_locals_def,namespaceTheory.nsBindList_def]);

val nsBindList_pat_tups_bind_locals = Q.prove(`
  ∀ls.
  ∃tss.
  nsBindList (pat_tups t ls) (bind_locals ts locals comp_map) =
  bind_locals (tss ++ ts) (ls ++ locals) comp_map ∧
  LENGTH tss = LENGTH ls`,
  Induct>>rw[pat_tups_def,namespaceTheory.nsBindList_def,bind_locals_def]>>
  qexists_tac`(t § (LENGTH ls + 1))::tss`>>simp[]);

val _ = Datatype `
  global_env =
    <| v : flatSem$v option list; c : (ctor_id # type_id) # num |-> stamp |>`;

val has_bools_def = Define `
  has_bools genv ⇔
    FLOOKUP genv ((true_tag, SOME bool_id), 0n) = SOME (TypeStamp "True" bool_type_num) ∧
    FLOOKUP genv ((false_tag, SOME bool_id), 0n) = SOME (TypeStamp "False" bool_type_num)`;

val has_lists_def = Define `
  has_lists genv ⇔
    FLOOKUP genv ((cons_tag, SOME list_id), 2n) = SOME (TypeStamp "::" list_type_num) ∧
    FLOOKUP genv ((nil_tag, SOME list_id), 0n) = SOME (TypeStamp "[]" list_type_num)`;

val has_exns_def = Define `
  has_exns genv ⇔
    FLOOKUP genv ((div_tag, NONE), 0n) = SOME div_stamp ∧
    FLOOKUP genv ((chr_tag, NONE), 0n) = SOME chr_stamp ∧
    FLOOKUP genv ((subscript_tag, NONE), 0n) = SOME subscript_stamp ∧
    FLOOKUP genv ((bind_tag, NONE), 0n) = SOME bind_stamp`;

val genv_c_ok_def = Define `
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
      cn1 = cn2 ∧ l1 = l2)`;

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
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
    env_rel genv env_v_local env_v_local' ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local')) env ∧
    LENGTH ts = LENGTH env_v_local' + 1
    ⇒
    v_rel genv
      (Closure (env with v := nsAppend env_v_local env.v) x e)
      (Closure env_v_local' x
        (compile_exp t
          (comp_map with v := bind_locals ts (x::MAP FST env_v_local') comp_map.v)
          e))) ∧
  (* For expression level let recs *)
  (!genv comp_map env env_v_local funs x env_v_local' t ts.
    env_rel genv env_v_local env_v_local' ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local')) env ∧
    LENGTH ts = LENGTH funs + LENGTH env_v_local'
    ⇒
    v_rel genv
      (Recclosure (env with v := nsAppend env_v_local env.v) funs x)
      (Recclosure env_v_local'
        (compile_funs t
          (comp_map with v := bind_locals ts (MAP FST funs++MAP FST env_v_local') comp_map.v) funs)
          x)) ∧
  (* For top-level let recs *)
  (!genv comp_map env funs x y e new_vars t1 t2.
    MAP FST new_vars = MAP FST (REVERSE funs) ∧
    global_env_inv genv comp_map {} env ∧
    find_recfun x funs = SOME (y, e) ∧
    (* A syntactic way of relating the recursive function environment, rather
     * than saying that they build v_rel related environments, which looks to
     * require step-indexing *)
    (!x. x ∈ set (MAP FST funs) ⇒
       ?n y e t1 t2 t3.
         ALOOKUP new_vars x = SOME (App t1 (GlobalVarLookup n) []) ∧
         n < LENGTH genv.v ∧
         find_recfun x funs = SOME (y,e) ∧
         EL n genv.v =
           SOME (Closure [] y
                  (compile_exp t2 (comp_map with v := nsBindList ((y, Var_local t3 y)::new_vars) comp_map.v) e)))
    ⇒
    v_rel genv
      (Recclosure env funs x)
      (Closure [] y
        (compile_exp t1
          (comp_map with v := nsBindList ((y, Var_local t2 y)::new_vars) comp_map.v)
          e))) ∧
  (!genv loc.
    v_rel genv (Loc loc) (Loc loc)) ∧
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
         nsLookup comp_map.v x = SOME (App t (GlobalVarLookup n) []) ∧
         n < LENGTH genv.v ∧
         EL n genv.v = SOME v' ∧
         v_rel genv v v') ∧
    (!x arity stamp.
      nsLookup env.c x = SOME (arity, stamp) ⇒
      ∃cn. nsLookup comp_map.c x = SOME cn ∧
        FLOOKUP genv.c (cn,arity) = SOME stamp)
    ⇒
    global_env_inv genv comp_map shadowers env)`;

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
   (!genv l v.
    v_rel genv (Loc l) v ⇔
      (v = Loc l)) ∧
   (!genv vs v.
    v_rel genv (Vectorv vs) v ⇔
      ?vs'. LIST_REL (v_rel genv) vs vs' ∧ (v = Vectorv vs')) ∧
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
         nsLookup comp_map.v x = SOME (App t (GlobalVarLookup n) []) ∧
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
  every_case_tac >>
  fs [genv_c_ok_def, has_bools_def] >>
  TRY eq_tac >>
  rw [] >>
  metis_tac []
QED

val env_rel_dom = Q.prove (
  `!genv env env'.
    env_rel genv env env'
    ⇒
    ?l. env = alist_to_ns l ∧ MAP FST l = MAP FST env'`,
  induct_on `env'` >>
  simp [Once v_rel_cases] >>
  rw [] >>
  first_x_assum drule >>
  rw [] >>
  rw_tac list_ss [GSYM alist_to_ns_cons] >>
  prove_tac [MAP, FST]);

val env_rel_lookup = Q.prove (
  `!genv env x v env'.
    ALOOKUP env x = SOME v ∧
    env_rel genv (alist_to_ns env) env'
    ⇒
    ?v'.
      v_rel genv v v' ∧
      ALOOKUP env' x = SOME v'`,
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
  metis_tac []);

val env_rel_append = Q.prove (
  `!genv env1 env2 env1' env2'.
    env_rel genv env1 env1' ∧
    env_rel genv env2 env2'
    ⇒
    env_rel genv (nsAppend env1 env2) (env1'++env2')`,
  induct_on `env1'` >>
  rw []
  >- (
    `env1 = nsEmpty` by fs [Once v_rel_cases] >>
    rw []) >>
  qpat_x_assum `env_rel _ _ (_::_)` mp_tac >>
  simp [Once v_rel_cases] >>
  rw [] >>
  rw [] >>
  simp [Once v_rel_cases]);

val env_rel_el = Q.prove (
  `!genv env env_i1.
    env_rel genv (alist_to_ns env) env_i1 ⇔
    LENGTH env = LENGTH env_i1 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i1)) ∧ v_rel genv (SND (EL n env)) (SND (EL n env_i1))`,
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
      srw_tac[][]));

val subglobals_def = Define `
  subglobals g1 g2 ⇔
    LENGTH g1 ≤ LENGTH g2 ∧
    !n. n < LENGTH g1 ∧ IS_SOME (EL n g1) ⇒ EL n g1 = EL n g2`;

val subglobals_refl = Q.prove (
  `!g. subglobals g g`,
  rw [subglobals_def]);

val subglobals_trans = Q.prove (
  `!g1 g2 g3. subglobals g1 g2 ∧ subglobals g2 g3 ⇒ subglobals g1 g3`,
  rw [subglobals_def] >>
  res_tac >>
  fs []);

val subglobals_refl_append = Q.prove (
  `!g1 g2 g3.
    subglobals (g1 ++ g2) (g1 ++ g3) = subglobals g2 g3 ∧
    (LENGTH g2 = LENGTH g3 ⇒ subglobals (g2 ++ g1) (g3 ++ g1) = subglobals g2 g3)`,
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
    fs []));

val v_rel_weakening = Q.prove (
  `(!genv v v'.
    v_rel genv v v'
    ⇒
    !genv'. genv.c = genv'.c ∧ subglobals genv.v genv'.v ⇒ v_rel genv' v v') ∧
   (!genv env env'.
    env_rel genv env env'
    ⇒
    !genv'. genv.c = genv'.c ∧ subglobals genv.v genv'.v ⇒ env_rel genv' env env') ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env
    ⇒
    !genv'. genv.c = genv'.c ∧ subglobals genv.v genv'.v ⇒ global_env_inv genv' comp_map shadowers env)`,
  ho_match_mp_tac v_rel_ind >>
  srw_tac[][v_rel_eqns, subglobals_def]
  >- fs [LIST_REL_EL_EQN]
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
    res_tac >>
    rw [] >>
    metis_tac [IS_SOME_DEF])
  >- metis_tac [DECIDE ``x < y ⇒ x < y + l:num``, EL_APPEND1]);

val v_rel_weakening2 = Q.prove (
  `(!genv v v'.
    v_rel genv v v'
    ⇒
    ∀gc. DISJOINT (FDOM gc) (FDOM genv.c) ⇒ v_rel (genv with c := FUNION gc genv.c) v v') ∧
   (!genv env env'.
    env_rel genv env env'
    ⇒
    !gc. DISJOINT (FDOM gc) (FDOM genv.c) ⇒ env_rel (genv with c := FUNION gc genv.c) env env') ∧
   (!genv comp_map shadowers env.
    global_env_inv genv comp_map shadowers env
    ⇒
    !gc. DISJOINT (FDOM gc) (FDOM genv.c) ⇒ global_env_inv (genv with c := FUNION gc genv.c) comp_map shadowers env)`,
  ho_match_mp_tac v_rel_ind >>
  srw_tac[][v_rel_eqns]
  >- fs [LIST_REL_EL_EQN]
  >- (
    simp [FLOOKUP_FUNION] >>
    fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
    rw [] >>
    metis_tac [])
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
      decide_tac)
  >- fs [LIST_REL_EL_EQN]
  >- metis_tac [DECIDE ``x < y ⇒ x < y + l:num``, EL_APPEND1]
  >- (
    res_tac >>
    fs [] >>
    simp [FLOOKUP_FUNION] >>
    fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
    rw [] >>
    metis_tac []));

val drestrict_lem = Q.prove (
  `f1 SUBMAP f2 ⇒ DRESTRICT f2 (COMPL (FDOM f1)) ⊌ f1 = f2`,
  rw [FLOOKUP_EXT, FUN_EQ_THM, FLOOKUP_FUNION] >>
  every_case_tac >>
  fs [FLOOKUP_DRESTRICT, SUBMAP_DEF] >>
  fs [FLOOKUP_DEF] >>
  rw [] >>
  metis_tac []);

val v_rel_weak = Q.prove (
  `!genv v v' genv'.
   v_rel genv v v' ∧
   genv.c ⊑ genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   v_rel genv' v v'`,
  rw [] >>
  imp_res_tac v_rel_weakening2 >>
  fs [] >>
  rpt (first_x_assum (qspec_then `DRESTRICT genv'.c (COMPL (FDOM genv.c))` assume_tac)) >>
  rfs [drestrict_lem] >>
  fs [DISJOINT_DEF, EXTENSION, FDOM_DRESTRICT] >>
  fs [GSYM DISJ_ASSOC] >>
  imp_res_tac v_rel_weakening >>
  fs []);

val env_rel_weak = Q.prove (
  `!genv env env' genv'.
   env_rel genv env env' ∧
   genv.c ⊑ genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   env_rel genv' env env'`,
  rw [] >>
  imp_res_tac v_rel_weakening2 >>
  fs [] >>
  rpt (first_x_assum (qspec_then `DRESTRICT genv'.c (COMPL (FDOM genv.c))` assume_tac)) >>
  rfs [drestrict_lem] >>
  fs [DISJOINT_DEF, EXTENSION, FDOM_DRESTRICT] >>
  fs [GSYM DISJ_ASSOC] >>
  imp_res_tac v_rel_weakening >>
  fs []);

val global_env_inv_weak = Q.prove (
  `!genv comp_map shadowers env genv'.
   global_env_inv genv comp_map shadowers env ∧
   genv.c ⊑ genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   global_env_inv genv' comp_map shadowers env`,
  rw [] >>
  imp_res_tac v_rel_weakening2 >>
  fs [] >>
  rpt (first_x_assum (qspec_then `DRESTRICT genv'.c (COMPL (FDOM genv.c))` assume_tac)) >>
  rfs [drestrict_lem] >>
  fs [DISJOINT_DEF, EXTENSION, FDOM_DRESTRICT] >>
  fs [GSYM DISJ_ASSOC] >>
  imp_res_tac v_rel_weakening >>
  fs []);

val (result_rel_rules, result_rel_ind, result_rel_cases) = Hol_reln `
  (∀genv v v'.
    f genv v v'
    ⇒
    result_rel f genv (Rval v) (Rval v')) ∧
  (∀genv v v'.
    v_rel genv v v'
    ⇒
    result_rel f genv (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
  (!genv a.
    result_rel f genv (Rerr (Rabort a)) (Rerr (Rabort a)))`;

val result_rel_eqns = Q.prove (
  `(!genv v r.
    result_rel f genv (Rval v) r ⇔
      ?v'. f genv v v' ∧ r = Rval v') ∧
   (!genv v r.
    result_rel f genv (Rerr (Rraise v)) r ⇔
      ?v'. v_rel genv v v' ∧ r = Rerr (Rraise v')) ∧
   (!genv v r a.
    result_rel f genv (Rerr (Rabort a)) r ⇔
      r = Rerr (Rabort a))`,
  srw_tac[][result_rel_cases] >>
  metis_tac []);

val (sv_rel_rules, sv_rel_ind, sv_rel_cases) = Hol_reln `
  (!genv v v'.
    v_rel genv v v'
    ⇒
    sv_rel genv (Refv v) (Refv v')) ∧
  (!genv w.
    sv_rel genv (W8array w) (W8array w)) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    sv_rel genv (Varray vs) (Varray vs'))`;

val sv_rel_weak = Q.prove (
  `!genv sv sv' genv'.
   sv_rel genv sv sv' ∧
   genv.c ⊑ genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   sv_rel genv' sv sv'`,
  srw_tac[][sv_rel_cases] >>
  metis_tac [v_rel_weak, LIST_REL_EL_EQN]);

val (s_rel_rules, s_rel_ind, s_rel_cases) = Hol_reln `
  (!genv_c s s'.
    LIST_REL (sv_rel <| v := s'.globals; c := genv_c |>) s.refs s'.refs ∧
    s.clock = s'.clock ∧
    s.ffi = s'.ffi
    ⇒
    s_rel genv_c s s')`;

val s_rel_weak = Q.prove (
  `!genv_c s s' genv_c'.
   s_rel genv_c s s' ∧
   genv_c ⊑ genv_c'
   ⇒
   s_rel genv_c' s s'`,
  srw_tac[][s_rel_cases] >>
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  rfs [] >>
  res_tac >>
  imp_res_tac sv_rel_weak >>
  fs [] >>
  pop_assum (qspec_then `<|v := s'.globals; c := genv_c'|>` mp_tac) >>
  rw [] >>
  metis_tac [subglobals_refl]);

val (env_all_rel_rules, env_all_rel_ind, env_all_rel_cases) = Hol_reln `
  (!genv map env_v_local env env' locals.
    (?l. env_v_local = alist_to_ns l ∧ MAP FST l = locals) ∧
    global_env_inv genv map (set locals) env ∧
    env_rel genv env_v_local env'
    ⇒
    env_all_rel genv map
      <| c := env.c; v := nsAppend env_v_local env.v |>
      <| c := FDOM genv.c; v := env'; exh_pat := F; check_ctor := T |>
      locals)`;

val env_all_rel_weak = Q.prove (
  `!genv map locals env env' genv'.
   env_all_rel genv map env env' locals ∧
   genv.c = genv'.c ∧
   subglobals genv.v genv'.v
   ⇒
   env_all_rel genv' map env env' locals`,
  rw [env_all_rel_cases] >>
  imp_res_tac env_rel_weak >>
  imp_res_tac global_env_inv_weak >>
  MAP_EVERY qexists_tac [`alist_to_ns l`, `env''`, `env'''`] >>
  rw [] >>
  metis_tac [SUBMAP_FDOM_SUBSET, SUBSET_TRANS]);

val match_result_rel_def = Define
  `(match_result_rel genv env' (Match env) (Match env_i1) =
     ?env''. env = env'' ++ env' ∧ env_rel genv (alist_to_ns env'') env_i1) ∧
   (match_result_rel genv env' No_match No_match = T) ∧
   (match_result_rel genv env' Match_type_error _ = T) ∧
   (match_result_rel genv env' _ _ = F)`;

(* semantic functions respect relation *)

val do_eq = Q.prove (
  `!genv. genv_c_ok genv.c ⇒
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
    do_eq_list vs1_i1 vs2_i1 = r)`,
  ntac 2 strip_tac >>
  ho_match_mp_tac terminationTheory.do_eq_ind >>
  rw [terminationTheory.do_eq_def, flatSemTheory.do_eq_def, v_rel_eqns] >>
  rw [terminationTheory.do_eq_def, flatSemTheory.do_eq_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH >>
  rw [] >>
  fs [] >>
  TRY (
    rpt (qpat_x_assum `v_rel _ (Closure _ _ _) _` mp_tac >>
         simp [Once v_rel_cases]) >>
    rpt (qpat_x_assum `v_rel _ (Recclosure _ _ _) _` mp_tac >>
         simp [Once v_rel_cases]) >>
    rw [] >>
    rw [flatSemTheory.do_eq_def] >>
    NO_TAC) >>
  fs [flatSemTheory.ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  fs [genv_c_ok_def, flatSemTheory.ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def] >>
  metis_tac [eq_result_11, eq_result_distinct]);

val v_to_char_list = Q.prove (
  `!genv. genv_c_ok genv.c ⇒
   !v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_char_list v1 = SOME vs1
    ⇒
    v_to_char_list v2 = SOME vs1`,
  ntac 2 strip_tac >>
  ho_match_mp_tac terminationTheory.v_to_char_list_ind >>
  srw_tac[][terminationTheory.v_to_char_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, flatSemTheory.v_to_char_list_def,
                          genv_c_ok_def, has_lists_def] >>
  rw []
  >- (
    `cn2 = (nil_tag,SOME list_id)` by metis_tac [] >>
    rw [flatSemTheory.v_to_char_list_def])
  >- (
    `cn2 = (cons_tag,SOME list_id)` by metis_tac [] >>
    rw [flatSemTheory.v_to_char_list_def]));

val v_to_list = Q.prove (
  `!genv. genv_c_ok genv.c ⇒
   !v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_list v1 = SOME vs1
    ⇒
    ?vs2.
      v_to_list v2 = SOME vs2 ∧
      LIST_REL (v_rel genv) vs1 vs2`,
  ntac 2 strip_tac >>
  ho_match_mp_tac terminationTheory.v_to_list_ind >>
  srw_tac[][terminationTheory.v_to_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, flatSemTheory.v_to_list_def] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[has_lists_def, genv_c_ok_def, v_rel_eqns, flatSemTheory.v_to_list_def] >>
  srw_tac[][]
  >- (
    `cn2 = (nil_tag,SOME list_id)` by metis_tac [] >>
    rw [v_to_list_def])
  >- (
    `cn2 = (cons_tag,SOME list_id)` by metis_tac [] >>
    rw [v_to_list_def] >>
    every_case_tac >>
    metis_tac [NOT_SOME_NONE, SOME_11]));

val vs_to_string = Q.prove(
  `∀v1 v2 s.
    LIST_REL (v_rel genv) v1 v2 ⇒
    vs_to_string v1 = SOME s ⇒
    vs_to_string v2 = SOME s`,
  ho_match_mp_tac terminationTheory.vs_to_string_ind
  \\ rw[terminationTheory.vs_to_string_def,vs_to_string_def]
  \\ fs[v_rel_eqns]
  \\ pop_assum mp_tac
  \\ TOP_CASE_TAC \\ strip_tac \\ rveq \\ fs[]
  \\ rw[vs_to_string_def]);

val v_rel_lems = Q.prove (
  `!genv. genv_c_ok genv.c ⇒
    (!b. v_rel genv (Boolv b) (Boolv b)) ∧
    v_rel genv div_exn_v div_exn_v ∧
    v_rel genv chr_exn_v chr_exn_v ∧
    v_rel genv bind_exn_v bind_exn_v ∧
    v_rel genv sub_exn_v subscript_exn_v`,
  rw [semanticPrimitivesTheory.div_exn_v_def, flatSemTheory.div_exn_v_def,
      semanticPrimitivesTheory.chr_exn_v_def, flatSemTheory.chr_exn_v_def,
      semanticPrimitivesTheory.bind_exn_v_def, flatSemTheory.bind_exn_v_def,
      semanticPrimitivesTheory.sub_exn_v_def, flatSemTheory.subscript_exn_v_def,
      v_rel_eqns, genv_c_ok_def, has_exns_def, has_bools_def,
      semanticPrimitivesTheory.Boolv_def, flatSemTheory.Boolv_def] >>
  every_case_tac >>
  simp [v_rel_eqns]);

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

val do_app = Q.prove (
  `!genv s1 s2 op vs r s1_i1 vs_i1.
    do_app s1 op vs = SOME (s2, r) ∧
    LIST_REL (sv_rel genv) (FST s1) s1_i1.refs ∧
    SND s1 = s1_i1.ffi ∧
    LIST_REL (v_rel genv) vs vs_i1 ∧
    genv_c_ok genv.c ∧
    op ≠ AallocEmpty
    ⇒
     ∃r_i1 s2_i1.
       LIST_REL (sv_rel genv) (FST s2) s2_i1.refs ∧
       SND s2 = s2_i1.ffi ∧
       s1_i1.globals = s2_i1.globals ∧
       result_rel v_rel genv r r_i1 ∧
       do_app T s1_i1 (astOp_to_flatOp op) vs_i1 = SOME (s2_i1, r_i1)`,
  rpt gen_tac >>
  Cases_on `s1` >>
  Cases_on `s1_i1` >>
  Cases_on `op = ConfigGC` >-
     (simp [astOp_to_flatOp_def] >>
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases]) >>
  pop_assum mp_tac >>
  Cases_on `op` >>
  simp [astOp_to_flatOp_def]
  >- ((* Opn *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opb *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opw *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases,v_rel_lems]
      \\ Cases_on`o'` \\ fs[opw8_lookup_def,opw64_lookup_def])
  >- ((* Shift *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      TRY (rename1 `shift8_lookup s11 w11 n11`) >>
      TRY (rename1 `shift64_lookup s11 w11 n11`) >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems]
      \\ Cases_on`w11` \\ Cases_on`s11` \\ fs[shift8_lookup_def,shift64_lookup_def])
  >- ((* Equality *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [Boolv_11, do_eq, eq_result_11, eq_result_distinct, v_rel_lems])
  >- ( (*FP_cmp *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ( (*FP_uop *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ( (*FP_bop *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ( (*FP_top *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opapp *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opassign *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_assign_def,store_v_same_type_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >-
      metis_tac [EVERY2_LUPDATE_same, sv_rel_rules] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN,sv_rel_cases] >>
      srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> res_tac >> full_simp_tac(srw_ss())[])
  >- ((* Opref *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Opderef *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][])
  >- ((* Aw8alloc *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >- ((* Aw8sub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def, v_rel_lems])
  >- ((* Aw8length *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def])
  >- ((* Aw8update *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      fsrw_tac[][] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][v_rel_lems])
  >- ((* WordFromInt *)
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* WordToInt *)
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* CopyStrStr *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases]
    \\ simp[v_rel_lems,v_rel_eqns])
  >- ((* CopyStrAw8 *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns]
    \\ simp[store_v_same_type_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >- ((* CopyAw8Str *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns])
  >- ((* CopyAw8Aw8 *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns]
    \\ simp[store_v_same_type_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >- ((* Ord *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases,v_rel_lems])
  >- ((* Chr *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Chopb *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Implode *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      imp_res_tac v_to_char_list >>
      srw_tac[][])
  >- ((* Strsub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_eqns] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[stringTheory.IMPLODE_EXPLODE_I, v_rel_lems])
  >- ((* Strlen *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Strcat *)
    rw[semanticPrimitivesPropsTheory.do_app_cases,flatSemTheory.do_app_def]
    \\ fs[LIST_REL_def]
    \\ imp_res_tac v_to_list \\ fs[]
    \\ imp_res_tac vs_to_string \\ fs[result_rel_cases,v_rel_eqns] )
  >- ((* VfromList *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_eqns] >>
      imp_res_tac v_to_list >>
      srw_tac[][])
  >- ((* Vsub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ, v_rel_lems])
  >- ((* Vlength *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Aalloc *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases, LIST_REL_REPLICATE_same] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >- ((* Asub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
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
  >- ((* Alength *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[store_lookup_def, sv_rel_cases] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      res_tac >>
      full_simp_tac(srw_ss())[sv_rel_cases] >>
      metis_tac [store_v_distinct, store_v_11, LIST_REL_LENGTH])
  >- ((* Aupdate *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
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
  >- ((* ListAppend *)
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
  >- ((* FFI *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, flatSemTheory.do_app_def] >>
      fs[v_rel_eqns] \\ rw[] \\
      fs[store_lookup_def, LIST_REL_EL_EQN] \\ fs[] \\ rfs[] \\
      res_tac \\
      qpat_x_assum`EL _ _ = _`assume_tac \\ fs[] \\
      qhdtm_x_assum`sv_rel`mp_tac \\
      simp[Once sv_rel_cases] \\ rw[] \\
      fs[IMPLODE_EXPLODE_I] \\
      CASE_TAC \\ fs[store_assign_def,store_v_same_type_def,EL_LUPDATE] \\ rfs[] \\ rw[EL_LUPDATE]
      \\ rw[sv_rel_cases, result_rel_cases, v_rel_eqns]));

val find_recfun = Q.prove (
  `!x funs e comp_map y t.
    find_recfun x funs = SOME (y,e)
    ⇒
    find_recfun x (compile_funs t comp_map funs) =
      SOME (y, compile_exp t (comp_map with v := nsBind y (Var_local t y) comp_map.v) e)`,
   induct_on `funs` >>
   srw_tac[][Once find_recfun_def, compile_exp_def] >>
   PairCases_on `h` >>
   full_simp_tac(srw_ss())[] >>
   every_case_tac >>
   full_simp_tac(srw_ss())[Once find_recfun_def, compile_exp_def]);

val do_app_rec_help = Q.prove (
  `!genv comp_map env_v_local env_v_local' env_v_top funs t.
    env_rel genv env_v_local env_v_local' ∧
    global_env_inv genv comp_map (set (MAP FST env_v_local')) env' ∧
    LENGTH ts = LENGTH funs' + LENGTH env_v_local'
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
                      (MAP2 (λt x. (x,Var_local t x)) ts
                         (MAP FST funs' ++ MAP FST env_v_local')))) funs')
                fn))
          (compile_funs t
             (comp_map with v :=
               (FOLDR (λ(x,v) e. nsBind x v e) comp_map.v
                (MAP2 (λt x. (x,Var_local t x)) ts
                   (MAP FST funs' ++ MAP FST env_v_local')))) funs))`,
  induct_on `funs`
  >- srw_tac[][v_rel_eqns, compile_exp_def] >>
  rw [] >>
  PairCases_on`h`>>fs[compile_exp_def]>>
  simp[v_rel_eqns]>>
  simp [Once v_rel_cases] >>
  MAP_EVERY qexists_tac [`comp_map`, `env'`, `env_v_local`, `t`,`ts`] >>
  simp[compile_exp_def,bind_locals_def]>>
  simp_tac (std_ss) [GSYM APPEND, namespaceTheory.nsBindList_def]);

val global_env_inv_add_locals = Q.prove (
  `!genv comp_map locals1 locals2 env.
    global_env_inv genv comp_map locals1 env
    ⇒
    global_env_inv genv comp_map (locals2 ∪ locals1) env`,
  srw_tac[][v_rel_eqns] >>
  metis_tac []);

val global_env_inv_extend2 = Q.prove (
  `!genv comp_map env new_vars env' locals env_c.
    set (MAP (Short o FST) new_vars) = nsDom env' ∧
    global_env_inv genv comp_map locals env ∧
    global_env_inv genv (comp_map with v := alist_to_ns new_vars) locals <| v := env'; c := env_c |>
    ⇒
    global_env_inv genv (comp_map with v := nsBindList new_vars comp_map.v) locals
        (env with v := nsAppend env' env.v)`,
  srw_tac[][v_rel_eqns, GSYM nsAppend_to_nsBindList] >>
  fs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_none, nsLookup_alist_to_ns_some] >>
  res_tac >>
  fs [] >>
  rw [] >>
  qexists_tac `n` >>
  rw [] >>
  Cases_on `x` >>
  fs [] >>
  rw []
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
    rw []));

val lookup_build_rec_env_lem = Q.prove (
  `!x cl_env funs' funs.
    ALOOKUP (MAP (λ(fn,n,e). (fn,Recclosure cl_env funs' fn)) funs) x = SOME v
    ⇒
    v = semanticPrimitives$Recclosure cl_env funs' x`,
  induct_on `funs` >>
  srw_tac[][] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[]);

val sem_env_eq_lemma = Q.prove (
  `!(env:'a sem_env) x. (env with v := x) = <| v := x; c := env.c |>`,
  rw [] >>
  rw [sem_env_component_equality]);

val do_opapp = Q.prove (
  `!genv vs vs_i1 env e.
    semanticPrimitives$do_opapp vs = SOME (env, e) ∧
    LIST_REL (v_rel genv) vs vs_i1
    ⇒
     ∃comp_map env_i1 locals t1 ts.
       env_all_rel genv comp_map env <| c := FDOM genv.c; v := env_i1; exh_pat := F; check_ctor := T |> locals ∧
       LENGTH ts = LENGTH locals ∧
       flatSem$do_opapp vs_i1 = SOME (env_i1, compile_exp t1 (comp_map with v := bind_locals ts locals comp_map.v) e)`,
   srw_tac[][do_opapp_cases, flatSemTheory.do_opapp_def] >>
   full_simp_tac(srw_ss())[LIST_REL_CONS1] >>
   srw_tac[][]
   >- (qpat_x_assum `v_rel genv (Closure _ _ _) _` mp_tac >>
       srw_tac[][Once v_rel_cases] >>
       srw_tac[][] >>
       rename [`v_rel _ v v'`, `env_rel _ envL envL'`, `nsBind name _ _`] >>
       MAP_EVERY qexists_tac [`comp_map`, `name :: MAP FST envL'`, `t`, `ts`] >>
       srw_tac[][bind_locals_def, env_all_rel_cases, namespaceTheory.nsBindList_def, FOLDR_MAP] >>
       fs[ADD1]>>
       MAP_EVERY qexists_tac [`nsBind name v envL`, `env`] >>
       srw_tac[][v_rel_eqns]
       >- metis_tac [sem_env_eq_lemma]
       >- (
         drule env_rel_dom >>
         rw [MAP_o] >>
         rw_tac list_ss [GSYM alist_to_ns_cons] >>
         qexists_tac`(name,v)::l`>>simp[])>>
       full_simp_tac(srw_ss())[v_rel_eqns] >>
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
       MAP_EVERY qexists_tac [`comp_map`, `arg :: MAP FST funs ++ MAP FST env_v_local'`,`t`,`t::ts`] >>
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
           srw_tac[][v_rel_eqns] >>
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
           >- fs [v_rel_eqns]))
       >- (
         simp [Once v_rel_cases] >>
         qexists_tac `v` >>
         qexists_tac `nsEmpty` >>
         rw [namespaceTheory.nsSing_def, namespaceTheory.nsEmpty_def,
             namespaceTheory.nsBind_def] >>
         simp [Once v_rel_cases, namespaceTheory.nsEmpty_def]))));

Theorem pat_bindings_compile_pat[simp]:
 !comp_map (p:ast$pat) vars. pat_bindings (compile_pat comp_map p) vars = pat_bindings p vars
Proof
  ho_match_mp_tac compile_pat_ind >>
  simp [compile_pat_def, astTheory.pat_bindings_def, pat_bindings_def] >>
  induct_on `ps` >>
  rw [] >>
  fs [pat_bindings_def,astTheory.pat_bindings_def, PULL_FORALL]
QED

val eta2 = Q.prove (
  `!f x. (\y. f x y) = f x`,
  metis_tac []);

val ctor_same_type_refl = Q.prove (
  `ctor_same_type x x`,
  Cases_on `x` >>
  rw [ctor_same_type_def] >>
  rename [`SOME x`] >>
  Cases_on `x` >>
  rw [ctor_same_type_def]);

val pmatch = Q.prove (
  `(!cenv s p v env r env' env'' genv env_i1 s_i1 v_i1 comp_map genv_v.
    semanticPrimitives$pmatch cenv s p v env = r ∧
    genv_c_ok genv.c ∧
    (!x arity stamp.
      nsLookup cenv x = SOME (arity, stamp) ⇒
      ∃cn. nsLookup comp_map.c x = SOME cn ∧
        FLOOKUP genv.c (cn,arity) = SOME stamp) ∧
    env = env' ++ env'' ∧
    LIST_REL (sv_rel genv) s s_i1 ∧
    v_rel genv v v_i1 ∧
    env_rel genv (alist_to_ns env') env_i1
    ⇒
    ?r_i1.
      flatSem$pmatch <| v := genv_v; c := FDOM genv.c; exh_pat := F; check_ctor := T |> s_i1 (compile_pat comp_map p) v_i1 env_i1 = r_i1 ∧
      match_result_rel genv env'' r r_i1) ∧
   (!cenv s ps vs env r env' env'' genv env_i1 s_i1 vs_i1 comp_map genv_v.
    pmatch_list cenv s ps vs env = r ∧
    genv_c_ok genv.c ∧
    (!x arity stamp.
      nsLookup cenv x = SOME (arity, stamp) ⇒
      ∃cn. nsLookup comp_map.c x = SOME cn ∧
        FLOOKUP genv.c (cn,arity) = SOME stamp) ∧
    env = env' ++ env'' ∧
    LIST_REL (sv_rel genv) s s_i1 ∧
    LIST_REL (v_rel genv) vs vs_i1 ∧
    env_rel genv (alist_to_ns env') env_i1
    ⇒
    ?r_i1.
      pmatch_list <| v := genv_v; c := FDOM genv.c; exh_pat := F; check_ctor := T |> s_i1 (MAP (compile_pat comp_map) ps) vs_i1 env_i1 = r_i1 ∧
      match_result_rel genv env'' r r_i1)`,
  ho_match_mp_tac terminationTheory.pmatch_ind >>
  srw_tac[][terminationTheory.pmatch_def, flatSemTheory.pmatch_def, compile_pat_def] >>
  full_simp_tac(srw_ss())[match_result_rel_def, flatSemTheory.pmatch_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH
  >> TRY (full_simp_tac(srw_ss())[Once v_rel_cases] >>
          srw_tac[][flatSemTheory.pmatch_def, match_result_rel_def] >>
          FAIL_TAC "")
  >- (
    every_case_tac >>
    full_simp_tac(srw_ss())[match_result_rel_def] >>
    last_assum drule >>
    strip_tac >>
    rw [] >>
    rw [pmatch_def, eta2, match_result_rel_def] >>
    fs [same_ctor_def, semanticPrimitivesTheory.same_ctor_def,FDOM_FLOOKUP] >>
    rename [`same_type stamp1 stamp2`] >>
    `¬ctor_same_type (SOME stamp1) (SOME stamp2)` by metis_tac [genv_c_ok_def] >>
    fs [semanticPrimitivesTheory.ctor_same_type_def])
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      metis_tac [])
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def]
      >- (full_simp_tac(srw_ss())[store_lookup_def] >>
          metis_tac [])
      >- (FIRST_X_ASSUM match_mp_tac >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[store_lookup_def, LIST_REL_EL_EQN, sv_rel_cases] >>
          res_tac >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][])
      >> (full_simp_tac(srw_ss())[store_lookup_def, LIST_REL_EL_EQN] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[sv_rel_cases] >>
          res_tac >>
          full_simp_tac(srw_ss())[]))
  >- (CASE_TAC >>
      every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      srw_tac[][] >>
      pop_assum mp_tac >>
      pop_assum mp_tac >>
      res_tac >>
      srw_tac[][] >>
      CCONTR_TAC >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      metis_tac [match_result_rel_def, match_result_distinct])) ;

(* compiler correctness *)

val opt_bind_lem = Q.prove (
  `opt_bind NONE = \x y.y`,
  rw [FUN_EQ_THM, libTheory.opt_bind_def]);

val env_updated_lem = Q.prove (
  `env with v updated_by (λy. y) = (env : flatSem$environment)`,
  rw [environment_component_equality]);

val evaluate_foldr_let_err = Q.prove (
  `!env s s' exps e x.
    flatSem$evaluate env s exps = (s', Rerr x)
    ⇒
    evaluate env s [FOLDR (Let t NONE) e exps] = (s', Rerr x)`,
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
  fs [opt_bind_lem, env_updated_lem]);

val s = mk_var("s",
  ``evaluate$evaluate`` |> type_of |> strip_fun |> #1 |> el 1
  |> type_subst[alpha |-> ``:'ffi``]);

val s1 = mk_var("s",
  ``flatSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
  |> type_subst[alpha |-> ``:'ffi``]);

val compile_exp_correct' = Q.prove (
   `(∀^s env es res.
     evaluate$evaluate s env es = res ⇒
     SND res ≠ Rerr (Rabort Rtype_error) ⇒
     !genv comp_map s' r env_i1 s_i1 es_i1 locals t ts.
       res = (s',r) ∧
       genv_c_ok genv.c ∧
       env_all_rel genv comp_map env env_i1 locals ∧
       s_rel genv.c s s_i1 ∧
       LENGTH ts = LENGTH locals ∧
       es_i1 = compile_exps t (comp_map with v := bind_locals ts locals comp_map.v) es ∧
       genv.v = s_i1.globals
       ⇒
       ?s'_i1 r_i1.
         result_rel (LIST_REL o v_rel) (genv with v := s'_i1.globals) r r_i1 ∧
         s_rel genv.c s' s'_i1 ∧
         flatSem$evaluate env_i1 s_i1 es_i1 = (s'_i1, r_i1) ∧
         s_i1.globals = s'_i1.globals) ∧
   (∀^s env v pes err_v res.
     evaluate$evaluate_match s env v pes err_v = res ⇒
     SND res ≠ Rerr (Rabort Rtype_error) ⇒
     !genv comp_map s' r env_i1 s_i1 v_i1 pes_i1 err_v_i1 locals t ts.
       (res = (s',r)) ∧
       genv_c_ok genv.c ∧
       env_all_rel genv comp_map env env_i1 locals ∧
       s_rel genv.c s s_i1 ∧
       v_rel genv v v_i1 ∧
       LENGTH ts = LENGTH locals ∧
       pes_i1 = compile_pes t (comp_map with v := bind_locals ts locals comp_map.v) pes ∧
       v_rel genv err_v err_v_i1 ∧
       genv.v = s_i1.globals
       ⇒
       ?s'_i1 r_i1.
         result_rel (LIST_REL o v_rel) (genv with v := s'_i1.globals) r r_i1 ∧
         s_rel genv.c s' s'_i1 ∧
         flatSem$evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 = (s'_i1, r_i1) ∧
         s_i1.globals = s'_i1.globals)`,
  ho_match_mp_tac terminationTheory.evaluate_ind >>
  srw_tac[][terminationTheory.evaluate_def, flatSemTheory.evaluate_def,compile_exp_def] >>
  full_simp_tac(srw_ss())[result_rel_eqns, v_rel_eqns] >>
  rpt (split_pair_case_tac >> fs [])
  >- ( (* sequencing *)
    fs [GSYM compile_exp_def] >>
    rpt (pop_assum mp_tac) >>
    Q.SPEC_TAC (`e2::es`, `es`) >>
    rw [] >>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    rpt (disch_then drule >> simp[]) >>
    rename [`compile_exp trace _ _`] >>
    disch_then (qspecl_then[`trace`] strip_assume_tac)>>
    rfs[]>>
    rw [] >>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >>
      asm_exists_tac >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] ) >>
    strip_tac >>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    fs [] >>
    rename1 `evaluate _ _ [compile_exp _ _ _] = (s2, _)` >>
    disch_then (qspec_then `genv` mp_tac) >>
    fs [] >>
    disch_then drule >> simp[] >>
    disch_then drule >> simp[] >>
    disch_then drule >> simp[] >>
    disch_then (qspecl_then[`trace`] strip_assume_tac)>> rfs[]>>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[] >>
    irule v_rel_weak >>
    fs [] >>
    qexists_tac `genv with v := s2.globals` >>
    rw [])
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >>
    disch_then drule >> simp[] >>
    disch_then drule >> simp[] >>
    disch_then (qspecl_then[`t`,`ts`] strip_assume_tac)>> rfs[]>>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[])
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >>
    disch_then drule >> simp[] >>
    disch_then drule >> simp[] >>
    disch_then (qspecl_then[`t`,`ts`] strip_assume_tac)>> rfs[]>>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    rename1 `evaluate _ _ [compile_exp _ _ _] = (s2, _)` >>
    `env_all_rel (genv with v := s2.globals) comp_map env env_i1 locals`
    by (
      irule env_all_rel_weak >>
      qexists_tac `genv` >>
      rw [] >>
      metis_tac [subglobals_refl]) >>
    first_x_assum (qspec_then `genv with v := s2.globals` mp_tac) >>
    simp [])
  >- ( (* Constructors *)
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then drule >>
    disch_then drule >>
    simp [] >>
    disch_then (qspec_then `t` mp_tac) >>
    fs [do_con_check_def, build_conv_def] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    fs [evaluate_def, compile_exps_reverse]
    >- (
      fs [result_rel_cases, PULL_EXISTS] >>
      rw [v_rel_eqns, EVERY2_REVERSE] >>
      res_tac >>
      fs [EVERY2_REVERSE, env_all_rel_cases] >>
      rfs [])
    >- (
      every_case_tac >>
      fs [result_rel_cases] >>
      res_tac >>
      fs [env_all_rel_cases] >>
      rw [] >>
      rfs [])
    >- (
      fs [result_rel_cases, PULL_EXISTS] >>
      rw [v_rel_eqns] >>
      rename [`nsLookup comp_map.c x`] >>
      Cases_on `nsLookup comp_map.c x` >>
      fs [flatSemTheory.evaluate_def , result_rel_cases, env_all_rel_cases,
          v_rel_eqns] >>
      rw [] >>
      fs [FLOOKUP_DEF]
      >- metis_tac [NOT_SOME_NONE] >>
      res_tac >>
      fs [] >>
      rw [EVERY2_REVERSE]
      >- fs [compile_exps_length] >>
      metis_tac [evaluatePropsTheory.evaluate_length, LENGTH_REVERSE])
    >- (
      fs [result_rel_cases, env_all_rel_cases] >>
      rw [] >>
      fs [v_rel_eqns] >>
      res_tac >>
      fs [evaluate_def, FLOOKUP_DEF, compile_exps_length]))
  >- ((* Variable lookup *)
    Cases_on `nsLookup env.v n` >>
    fs [env_all_rel_cases] >>
    rw [] >>
    fs [nsLookup_nsAppend_some]
    >- ((* Local variable *)
      fs [nsLookup_alist_to_ns_some,bind_locals_def] >>
      rw [] >>
      drule env_rel_lookup >>
      disch_then drule >>
      rw [GSYM nsAppend_to_nsBindList] >>
      simp[MAP2_MAP]>>
      every_case_tac >>
      fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none, nsLookup_alist_to_ns_some,
          nsLookup_alist_to_ns_none]>>
      fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
      `(λ(p1:tra,p2:tvarN). p2) = SND` by fs[FUN_EQ_THM,FORALL_PROD]>>
      fs[]>>rfs[MAP_ZIP]
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP]
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP]
      >- (
        drule ALOOKUP_MEM >>
        rw [MEM_MAP] >>
        pairarg_tac>>fs[]>>
        simp [evaluate_def, result_rel_cases] >>
        irule v_rel_weak >>
        simp [] >>
        metis_tac [SUBMAP_REFL, subglobals_refl])
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP])
    >- ( (* top-level variable *)
      rw [GSYM nsAppend_to_nsBindList,bind_locals_def] >>
      fs [nsLookup_alist_to_ns_none] >>
      fs [v_rel_eqns, ALOOKUP_NONE, METIS_PROVE [] ``~x ∨ y ⇔ x ⇒ y``] >>
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
        simp [evaluate_def, result_rel_cases] >>
        simp [do_app_def] >>
        irule v_rel_weak >>
        simp [] >>
        metis_tac [SUBMAP_REFL, subglobals_refl])))
  >- (* Closure creation *)
     (srw_tac[][Once v_rel_cases] >>
      full_simp_tac(srw_ss())[env_all_rel_cases] >>
      srw_tac[][] >>
      rename [`global_env_inv genv comp_map (set (MAP FST locals)) env`] >>
      MAP_EVERY qexists_tac [`comp_map`, `env`, `alist_to_ns locals`,`t`,`(t§2)::ts`] >>
      imp_res_tac env_rel_dom >>
      srw_tac[][] >>
      simp [bind_locals_def, namespaceTheory.nsBindList_def] >>
      fs [ADD1]
      >- metis_tac [sem_env_eq_lemma]
      >- (
        irule env_rel_weak >>
        simp [] >>
        metis_tac [SUBMAP_REFL, subglobals_refl])
      >- (
        irule global_env_inv_weak >>
        simp [] >>
        metis_tac [SUBMAP_REFL, subglobals_refl])
      >- metis_tac[LENGTH_MAP])
  (* App *)
  >- (
    srw_tac [boolSimps.DNF_ss] [PULL_EXISTS]
    >- (
      (* empty array creation *)
      every_case_tac >>
      fs [semanticPrimitivesTheory.do_app_def] >>
      every_case_tac >>
      fs [] >>
      rw [evaluate_def, flatSemTheory.do_app_def] >>
      fs []
      >- (
        drule (CONJUNCT1 evaluatePropsTheory.evaluate_length) >>
        Cases_on `es` >>
        rw [LENGTH_NIL] >>
        fs [] >>
        simp [compile_exp_def, evaluate_def] >>
        pairarg_tac >>
        fs [store_alloc_def, compile_exp_def] >>
        rpt var_eq_tac >>
        first_x_assum drule >>
        disch_then drule >>
        disch_then drule >>
        disch_then(qspecl_then[`t`,`ts`] mp_tac)>>
        simp [] >>
        rw [result_rel_cases, Once v_rel_cases] >>
        simp [do_app_def] >>
        pairarg_tac >>
        fs [store_alloc_def] >>
        simp [Once v_rel_cases] >>
        fs [s_rel_cases] >>
        rw []
        >- metis_tac [LIST_REL_LENGTH] >>
        simp [REPLICATE, sv_rel_cases])
      >- (
        first_x_assum drule >>
        disch_then drule >>
        disch_then drule >>
        disch_then(qspecl_then[`t`,`ts`] mp_tac)>>
        rw [] >>
        qexists_tac `s'_i1` >>
        qexists_tac `r_i1` >>
        simp [] >>
        fs [compile_exps_reverse] >>
        `?e'. r_i1 = Rerr e'` by fs [result_rel_cases] >>
        rw [] >>
        metis_tac [evaluate_foldr_let_err])) >>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then drule >>
    disch_then drule >>
    disch_then(qspecl_then[`t`] strip_assume_tac)>> rfs[]>>
    full_simp_tac(srw_ss())[compile_exps_reverse] >>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC
    >- (
      rw [] >>
      first_x_assum (qspec_then `ts` mp_tac) >>
      rw [] >>
      rw [evaluate_def] >>
      fs [result_rel_cases]) >>
    BasicProvers.TOP_CASE_TAC
    >- (
      fs [] >>
      BasicProvers.TOP_CASE_TAC >>
      fs [] >>
      split_pair_case_tac >>
      fs [] >>
      drule do_opapp >>
      fs [] >>
      first_x_assum (qspec_then `ts` mp_tac) >>
      rw []
      >- (
        fs [result_rel_cases] >>
        qexists_tac `s'_i1` >>
        simp [evaluate_def, astOp_to_flatOp_def] >>
        fs [s_rel_cases] >>
        first_x_assum (qspecl_then [`genv with v := s'_i1.globals`, `REVERSE v'`] mp_tac) >>
        rw [EVERY2_REVERSE] >>
        rw [])
      >- (
        rw [evaluate_def, astOp_to_flatOp_def] >>
        fs [result_rel_cases] >>
        first_x_assum (qspecl_then [`genv with v := s'_i1.globals`, `REVERSE v'`] mp_tac) >>
        rw [EVERY2_REVERSE] >>
        rw []
        >- fs [s_rel_cases]
        >- fs [s_rel_cases] >>
        fs [] >>
        rename1 `LIST_REL (v_rel (_ with v := s2.globals))` >>
        rfs [] >>
        first_x_assum (qspec_then `genv with v := s2.globals` mp_tac) >>
        simp [] >>
        disch_then drule >>
        disch_then (qspec_then `dec_clock s2` mp_tac) >>
        fs [dec_clock_def, evaluateTheory.dec_clock_def] >>
        fs [s_rel_cases] >>
        disch_then (qspecl_then [`t1`, `ts'`] mp_tac) >>
        simp [] >>
        fs [env_all_rel_cases])) >>
    BasicProvers.TOP_CASE_TAC >>
    strip_tac >> rveq >>
    fs [] >>
    pop_assum mp_tac >>
    BasicProvers.TOP_CASE_TAC >>
    BasicProvers.TOP_CASE_TAC >>
    fs [] >>
    rw [] >>
    drule do_app >> full_simp_tac(srw_ss())[] >>
    first_x_assum (qspec_then `ts` mp_tac) >>
    rw [evaluate_def] >>
    fs [] >>
    rename1 `result_rel (LIST_REL o v_rel) (_ with v := s2.globals) _ _` >>
    first_x_assum (qspec_then `genv with v := s2.globals` mp_tac) >>
    simp [] >>
    disch_then (qspec_then `s2` mp_tac) >>
    fs [s_rel_cases] >>
    `<|v := s2.globals; c := genv.c|> = genv with v := s2.globals`
    by rw [theorem "global_env_component_equality"] >>
    fs [result_rel_cases] >>
    disch_then (qspec_then `REVERSE v'` mp_tac) >>
    simp [EVERY2_REVERSE] >>
    `astOp_to_flatOp op ≠ Opapp`
    by (
      rw [astOp_to_flatOp_def] >>
      Cases_on `op` >>
      simp [] >>
      fs []) >>
    `env_i1.check_ctor` by fs[env_all_rel_cases] \\ fs[] >>
    rw [] >>
    imp_res_tac do_app_const >>
    rw []
    >- (
      irule v_rel_weak >>
      qexists_tac `genv with v := s2.globals` >>
      rw [subglobals_refl])
    >- (
      fs [LIST_REL_EL_EQN] >>
      rw [] >>
      irule sv_rel_weak >>
      qexists_tac `genv with v := s2.globals` >>
      rw [])
    >- (
      irule v_rel_weak >>
      qexists_tac `genv with v := s2.globals` >>
      rw [subglobals_refl])
    >- (
      fs [LIST_REL_EL_EQN] >>
      rw [] >>
      irule sv_rel_weak >>
      qexists_tac `genv with v := s2.globals` >>
      rw [])
    >- (
      fs [LIST_REL_EL_EQN] >>
      rw [] >>
      irule sv_rel_weak >>
      qexists_tac `genv with v := s2.globals` >>
      rw []))
  >- ( (* logical operation *)
    fs[markerTheory.Abbrev_def]>>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then drule >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
      BasicProvers.TOP_CASE_TAC >> srw_tac[][evaluate_def] ) >>
    BasicProvers.TOP_CASE_TAC >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    imp_res_tac evaluatePropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> rveq >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[do_log_def] >> srw_tac[][] >>
      pop_assum mp_tac >>
      strip_tac >>
      qpat_x_assum `result_rel _ _ (Rval _) _` mp_tac >>
      simp [result_rel_cases] >>
      strip_tac >>
      fs [] >>
      rw [PULL_EXISTS] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      fs [v_rel_eqns, Boolv_def, semanticPrimitivesTheory.Boolv_def, PULL_EXISTS] >>
      rw [] >>
      asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      simp [evaluate_def, do_if_def, Boolv_def] >>
      rw [] >>
      fs [genv_c_ok_def, has_bools_def, Bool_def, evaluate_def, do_app_def,
          Boolv_def, opb_lookup_def, state_component_equality,
          backend_commonTheory.bool_to_tag_def ] >>
      rw [] >>
      fs [env_all_rel_cases] >>
      rw [] >>
      fs [FLOOKUP_DEF] >>
      metis_tac []) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    rename1 `evaluate _ _ [compile_exp _ _ _] = (s2, _)` >>
    first_x_assum (qspec_then `genv` mp_tac) >>
    fs [] >>
    disch_then drule >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    asm_exists_tac >> simp[] >>
    full_simp_tac(srw_ss())[do_log_def] >>
    qpat_x_assum`_ = SOME _`mp_tac >>
    srw_tac[][evaluate_def] >>
    srw_tac[][evaluate_def] >>
    fs [Boolv_def, semanticPrimitivesTheory.Boolv_def] >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[Once v_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
    srw_tac[][do_if_def] >>
    fs [genv_c_ok_def, has_bools_def, Boolv_def] >>
    rw [] >>
    fs [env_all_rel_cases] >>
    rw [] >>
    fs [FLOOKUP_DEF] >>
    metis_tac [])
  >- ( (* if *)
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then drule >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[] >>
    rename1 `evaluate _ _ [compile_exp _ _ _] = (s2, _)` >>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then (qspec_then `genv` mp_tac) >>
    fs [] >>
    disch_then drule >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    asm_exists_tac >> simp[] >>
    imp_res_tac evaluatePropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
    rename [`evaluate _ _ _ = (_, Rval v)`] >>
    Cases_on`v`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> rveq >>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.do_if_def] >>
    qpat_x_assum `result_rel _ _ (Rval _) _` mp_tac >>
    simp [result_rel_cases] >>
    rw [] >>
    rw [] >>
    fs [do_if_def] >>
    every_case_tac >>
    fs [Boolv_def, semanticPrimitivesTheory.Boolv_def] >>
    rw [] >>
    fs [v_rel_eqns] >>
    rw [] >>
    fs [genv_c_ok_def, has_bools_def] >>
    metis_tac [])
  >- ( (* match *)
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then drule >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    rename1 `evaluate _ _ [compile_exp _ _ _] = (s2, _)` >>
    `env_all_rel (genv with v := s2.globals) comp_map env env_i1 locals`
    by (
      irule env_all_rel_weak >>
      qexists_tac `genv` >>
      rw [subglobals_refl]) >>
    first_x_assum (qspec_then `genv with v := s2.globals` mp_tac) >>
    fs [] >>
    disch_then drule >>
    disch_then drule >>
    simp[] >> strip_tac >>
    qhdtm_x_assum`result_rel`mp_tac >>
    simp[Once result_rel_cases] >> strip_tac >>
    imp_res_tac evaluatePropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> rveq >>
    full_simp_tac(srw_ss())[] >>
    first_x_assum drule >>
    simp[bind_exn_v_def] >>
    disch_then irule >>
    rw [semanticPrimitivesTheory.bind_exn_v_def, v_rel_eqns] >>
    fs [genv_c_ok_def, has_exns_def])
  >- ( (* Let *)
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then drule >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      Cases_on`xo`>> srw_tac[][compile_exp_def,evaluate_def] >>
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    qhdtm_x_assum`result_rel`mp_tac >>
    simp[Once result_rel_cases] >> strip_tac >>
    fs [] >>
    rename1 `evaluate _ _ [compile_exp _ _ _] = (s2, _)` >>
    Cases_on`xo` >>
    fs [namespaceTheory.nsOptBind_def, libTheory.opt_bind_def] >>
    rw [compile_exp_def,evaluate_def]
    >- (
      first_x_assum (qspec_then `genv` mp_tac) >>
      qpat_abbrev_tac`env2 = env_i1 with v updated_by _` >>
      `env2 = env_i1` by (
        simp[environment_component_equality,Abbr`env2`,libTheory.opt_bind_def] ) >>
      simp []) >>
    qpat_abbrev_tac`env2 = env_i1 with v updated_by _` >>
    first_x_assum(qspecl_then[`genv with v := s2.globals`, `comp_map`,`env2`]mp_tac) >>
    simp[Abbr`env2`] >>
    disch_then(qspecl_then[`s2`,`x::locals`,`t`,`(t § 2)::ts`] mp_tac)>>
    impl_tac >- (
      full_simp_tac(srw_ss())[env_all_rel_cases] >>
      full_simp_tac(srw_ss())[namespaceTheory.nsOptBind_def,libTheory.opt_bind_def] >>
      srw_tac[QUANT_INST_ss[record_default_qp,pair_default_qp]][] >>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      simp[GSYM CONJ_ASSOC] >>
      drule global_env_inv_add_locals >>
      disch_then(qspec_then`{x}`strip_assume_tac) >>
      simp[Once INSERT_SING_UNION] >>
      qexists_tac `env'.v` >> simp [] >>
      qexists_tac `(x,HD a)::l` >>
      simp [] >>
      rw []
      >- (
        fs [v_rel_eqns] >>
        rw [] >>
        res_tac >>
        fs [] >>
        rw [] >>
        `genv with v := s2.globals = genv` by rw [theorem"global_env_component_equality"] >>
        metis_tac []) >>
      simp [v_rel_eqns] >>
      imp_res_tac evaluate_sing >>
      full_simp_tac(srw_ss())[] >>
      irule env_rel_weak >>
      simp [] >>
      metis_tac [SUBMAP_REFL, subglobals_refl]) >>
    strip_tac >>
    asm_exists_tac >> simp[] >>
    fs [GSYM nsAppend_to_nsBindList,bind_locals_def])
  >- ( (* let rec *)
    srw_tac[][markerTheory.Abbrev_def] >>
    srw_tac[][evaluate_def] >>
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
    qexists_tac `REPLICATE (LENGTH funs) t ++ ts` >>
    drule env_rel_dom >>
    rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY,
        bind_locals_def, nsAppend_to_nsBindList] >>
    rw [sem_env_component_equality]
    >- metis_tac[]
    >- metis_tac [LENGTH_MAP])
  >- (Cases_on`l`>>fs[evaluate_def,compile_exp_def])
  >- (
    fs [env_all_rel_cases] >>
    rw [] >>
    irule v_rel_weak >>
    fs [] >>
    metis_tac [SUBMAP_REFL, subglobals_refl])
  >- ( (* pattern/expression *)
    fs[markerTheory.Abbrev_def]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >- (
      rev_full_simp_tac(srw_ss())[] >>
      drule (CONJUNCT1 pmatch) >>
      `genv_c_ok <| v := s_i1.globals; c := genv.c |>.c` by rw [] >>
      disch_then drule >>
      simp[GSYM CONJ_ASSOC] >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      simp[GSYM CONJ_ASSOC] >>
      qhdtm_x_assum`s_rel`mp_tac >>
      simp[Once s_rel_cases] >> strip_tac >>
      disch_then drule >>
      `<|v := s_i1.globals; c := genv.c|> = genv`
      by rw [theorem"global_env_component_equality"] >>
      simp [] >>
      disch_then drule >>
      qhdtm_x_assum`env_all_rel`mp_tac >>
      simp[Once env_all_rel_cases] >> strip_tac >>
      simp [v_rel_eqns] >>
      disch_then (qspec_then `comp_map with v := bind_locals ts locals comp_map.v` mp_tac) >>
      disch_then (qspec_then `env''` mp_tac) >>
      impl_tac >- fs [v_rel_eqns] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`match_result_rel _ _ _ mm` >>
      Cases_on`mm`>>full_simp_tac(srw_ss())[match_result_rel_def] >>
      pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
      simp[evaluate_def]>>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      rw [GSYM CONJ_ASSOC] >>
      first_x_assum match_mp_tac >>
      simp[s_rel_cases] >>
      simp[env_all_rel_cases] >>
      metis_tac[] ) >>
    rfs [] >>
    drule (CONJUNCT1 pmatch) >>
    `genv_c_ok <| v := s_i1.globals; c := genv.c|>.c` by rw [] >>
    disch_then drule >>
    simp[GSYM CONJ_ASSOC] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    simp[GSYM CONJ_ASSOC] >>
    qhdtm_x_assum`s_rel`mp_tac >>
    simp[Once s_rel_cases] >> strip_tac >>
    disch_then drule >>
    `<|v := s_i1.globals; c := genv.c|> = genv`
    by rw [theorem"global_env_component_equality"] >>
    simp [] >>
    disch_then drule >>
    qhdtm_x_assum`env_all_rel`mp_tac >>
    simp[Once env_all_rel_cases] >> strip_tac >>
    simp [v_rel_eqns] >>
    disch_then (qspec_then `comp_map with v := bind_locals ts locals comp_map.v` mp_tac) >>
    disch_then (qspec_then `env''` mp_tac) >>
    impl_tac >- fs [v_rel_eqns] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`match_result_rel _ _ _ mm` >>
    Cases_on`mm`>>full_simp_tac(srw_ss())[match_result_rel_def] >>
    pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
    simp[evaluate_def]>>
    ONCE_REWRITE_TAC[CONJ_ASSOC] >>
    ONCE_REWRITE_TAC[CONJ_ASSOC] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    REWRITE_TAC [GSYM CONJ_ASSOC] >>
    qspecl_then [`comp_map.v`, `pat_bindings p []`] assume_tac (Q.GEN `comp_map` nsBindList_pat_tups_bind_locals|>INST_TYPE[alpha|->``:tvarN``])>>
    fs[]>>
    first_x_assum match_mp_tac >>
    simp[s_rel_cases] >>
    simp[env_all_rel_cases] >>
    qexists_tac `alist_to_ns (a ++ l)` >>
    qexists_tac`env'` >>
    rw []
    >- (
      drule (CONJUNCT1 pmatch_extend) >>
      rw [] >>
      drule env_rel_dom >>
      rw [])
    >- metis_tac [global_env_inv_add_locals]
    >- (
      rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
      match_mp_tac env_rel_append >>
      rw [])));

val compile_exp_correct = Q.prove (
  `∀s env es comp_map s' r s_i1 t genv_c.
    evaluate$evaluate s env es = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    genv_c_ok genv_c ∧
    global_env_inv <| v := s_i1.globals; c := genv_c |> comp_map {} env ∧
    s_rel genv_c s s_i1
    ⇒
    ?s'_i1 r_i1.
      result_rel (LIST_REL o v_rel) <| v := s'_i1.globals; c := genv_c |> r r_i1 ∧
      s_rel genv_c s' s'_i1 ∧
      flatSem$evaluate <|c := FDOM genv_c; v := []; exh_pat := F; check_ctor := T |>
        s_i1 (compile_exps t comp_map es) = (s'_i1, r_i1) ∧
        s_i1.globals = s'_i1.globals`,
  rw [] >>
  drule (GEN_ALL (CONJUNCT1 compile_exp_correct')) >>
  rfs [env_all_rel_cases, PULL_EXISTS] >>
  disch_then (qspecl_then [`<| v := s_i1.globals; c := genv_c |>`, `comp_map`, `s_i1`, `t`,`[]`] mp_tac) >>
  simp [PULL_EXISTS, sem_env_component_equality] >>
  disch_then (qspecl_then [`env`, `[]`] mp_tac) >>
  simp [] >>
  impl_tac
  >- simp [v_rel_eqns] >>
  simp [bind_locals_def,namespaceTheory.nsBindList_def] >>
  `comp_map with v := comp_map.v = comp_map`
  by rw [source_to_flatTheory.environment_component_equality] >>
  rw []);

val ALOOKUP_alloc_defs_EL = Q.prove (
  `!funs l n m.
    ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
    n < LENGTH funs
    ⇒
    ∃tt.
    ALOOKUP (alloc_defs m l (MAP FST (REVERSE funs))) (EL n (MAP FST funs)) =
      SOME (App tt (GlobalVarLookup (l + LENGTH funs − (n + 1))) [])`,
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
    disch_then(qspec_then`l+1` assume_tac)>>fs[]));

val compile_decs_num_bindings = Q.prove(
  `!n next env ds n' next' env' ds_i1.
    compile_decs n next env ds = (n', next',env',ds_i1)
    ⇒
    next.vidx ≤ next'.vidx ∧
    next.tidx ≤ next'.tidx ∧
    next.eidx ≤ next'.eidx`,
  ho_match_mp_tac compile_decs_ind >>
  rw [compile_decs_def] >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs []);

val env_domain_eq_def = Define `
  env_domain_eq (var_map : source_to_flat$environment) (env : 'a sem_env)⇔
    nsDom var_map.v = nsDom env.v ∧
    nsDomMod var_map.v = nsDomMod env.v ∧
    nsDom var_map.c = nsDom env.c ∧
    nsDomMod var_map.c = nsDomMod env.c`;

val env_domain_eq_append = Q.prove (
  `env_domain_eq env1 env1' ∧
   env_domain_eq env2 env2'
   ⇒
   env_domain_eq (extend_env env1 env2) (extend_dec_env env1' env2')`,
  rw [env_domain_eq_def, extend_env_def, extend_dec_env_def,nsLookupMod_nsAppend_some,
      nsLookup_nsAppend_some, nsLookup_nsDom, namespaceTheory.nsDomMod_def,
      EXTENSION, GSPECIFICATION, EXISTS_PROD] >>
  metis_tac [option_nchotomy, NOT_SOME_NONE, pair_CASES]);

val global_env_inv_append = Q.prove (
  `!genv var_map1 var_map2 env1 env2.
    env_domain_eq var_map1 env1 ∧
    global_env_inv genv var_map1 {} env1 ∧
    global_env_inv genv var_map2 {} env2
    ⇒
    global_env_inv genv (extend_env var_map1 var_map2) {} (extend_dec_env env1 env2)`,
  rw [env_domain_eq_def, v_rel_eqns, nsLookup_nsAppend_some, extend_env_def, extend_dec_env_def] >>
  first_x_assum drule >>
  rw []
  >- rw []
  >- (
    qexists_tac `n` >>
    qexists_tac `v'` >>
    qexists_tac `t` >>
    rw [] >>
    disj2_tac >>
    rw []
    >- (
      fs [EXTENSION, namespaceTheory.nsDom_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy])
    >- (
      fs [EXTENSION, namespaceTheory.nsDomMod_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy]))
  >- rw []
  >- (
    rw [] >>
    qexists_tac `cn` >>
    rw [] >>
    disj2_tac >>
    rw []
    >- (
      fs [EXTENSION, namespaceTheory.nsDom_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [pair_CASES, NOT_SOME_NONE, option_nchotomy])
    >- (
      fs [EXTENSION, namespaceTheory.nsDomMod_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy])));

val pmatch_lem =
  pmatch
  |> CONJUNCTS
  |> hd
  |> SIMP_RULE (srw_ss()) [];

val ALOOKUP_alloc_defs = Q.prove (
  `!env x v l tt.
    ALOOKUP (REVERSE env) x = SOME v
    ⇒
    ∃n t.
      ALOOKUP (alloc_defs tt l (MAP FST (REVERSE env))) x = SOME (App t (GlobalVarLookup (l + n)) [] )∧
      n < LENGTH (MAP FST env) ∧
      EL n (REVERSE (MAP SOME (MAP SND env))) = SOME v`,
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
    rw [EL_APPEND_EQN]));

fun spectv v tt = disch_then(qspec_then tt mp_tac o CONV_RULE (RESORT_FORALL_CONV(sort_vars[v])))
val spect = spectv "t"

val invariant_def = Define `
  invariant genv idx s s_i1 ⇔
    genv_c_ok genv.c ∧
    (!n. idx.vidx ≤ n ∧ n < LENGTH genv.v ⇒ EL n genv.v = NONE) ∧
    (!cn t. t ≥ s.next_type_stamp ⇒ TypeStamp cn t ∉ FRANGE genv.c) ∧
    (!cn. cn ≥ s.next_exn_stamp ⇒ ExnStamp cn ∉ FRANGE genv.c) ∧
    (!cn t a. t ≥ idx.tidx ⇒ ((cn,SOME t), a) ∉ FDOM genv.c) ∧
    (!cn a. cn ≥ idx.eidx ⇒ ((cn,NONE), a) ∉ FDOM genv.c) ∧
    genv.v = s_i1.globals ∧
    s_rel genv.c s s_i1`;

val global_env_inv_extend = Q.prove (
  `!pat_env genv pat_env' tt g1 g2.
    env_rel genv (alist_to_ns pat_env) pat_env' ∧
    genv.v = g1 ⧺ MAP SOME (REVERSE (MAP SND pat_env')) ⧺ g2 ∧
    ALL_DISTINCT (MAP FST pat_env)
    ⇒
    global_env_inv
      <|v := genv.v; c := genv.c|>
      <|c := nsEmpty;
        v := alist_to_ns (alloc_defs tt (LENGTH g1) (REVERSE (MAP FST pat_env')))|>
      ∅
      <|v := alist_to_ns pat_env; c := nsEmpty|>`,
  rw [v_rel_eqns, extend_dec_env_def, extend_env_def, nsLookup_nsAppend_some,
      nsLookup_alist_to_ns_some] >>
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
  rw []);

val env_c_update = Q.prove (
  `env with c updated_by $UNION {} = env`,
  rw [environment_component_equality]);

val evaluate_recfuns = Q.prove (
  `!env s funs idx t1 t2.
    (∀n. idx.vidx ≤ n ∧ n < LENGTH s.globals ⇒ EL n s.globals = NONE) ∧
    LENGTH funs + idx.vidx ≤ LENGTH s.globals ∧ env.check_ctor
    ⇒
    flatSem$evaluate_decs env s
      (MAPi (\i (f, x, e).
              Dlet (App t1 (GlobalVarInit (i + idx.vidx))
                     [Fun t2 x e]))
        funs)
    =
    (s with globals := TAKE idx.vidx s.globals ++
                       MAP (λ(f,x,e). SOME (Closure [] x e)) funs ++
                       DROP (idx.vidx + LENGTH funs) s.globals,
     {},
     NONE)`,
  Induct_on `funs` >>
  rw [evaluate_decs_def]
  >- rw [state_component_equality] >>
  pairarg_tac >>
  rw [evaluate_dec_def, evaluate_def, do_app_def] >>
  split_pair_case_tac >>
  simp [] >>
  fs [env_c_update] >>
  first_x_assum (qspecl_then [`env`,
      `s with globals := LUPDATE (SOME (Closure [] x e)) idx.vidx s.globals`,
      `idx with vidx := idx.vidx + 1`, `t1`, `t2`] mp_tac) >>
  simp [] >>
  impl_tac
  >- rw [EL_LUPDATE] >>
  simp [] >>
  strip_tac >>
  fs [combinTheory.o_DEF, ADD1, Unitv_def] >>
  rw [state_component_equality] >>
  qmatch_abbrev_tac `l1 = l2` >>
  `LENGTH l1 = LENGTH l2` by
  fs [Abbr`l1`, Abbr`l2`, LENGTH_TAKE, LENGTH_DROP, LENGTH_MAP, LENGTH_LUPDATE] >>
  unabbrev_all_tac >>
  irule LIST_EQ >>
  rw [EL_APPEND_EQN, EL_TAKE, EL_LUPDATE, EL_DROP] >>
  fs []);

val lookup_inc_lookup = Q.prove (
  `lookup_inc t new_cids = (tag,new_cids')
   ⇒
   lookup t new_cids' = SOME (tag+1)`,
  rw [lookup_inc_def] >>
  every_case_tac >>
  fs [] >>
  rw []);

val lookup_inc_lookup_unchanged = Q.prove (
  `!t1. lookup_inc t new_cids = (tag,new_cids') ∧
   t1 ≠ t
   ⇒
   lookup t1 new_cids = lookup t1 new_cids'`,
  rw [lookup_inc_def] >>
  every_case_tac >>
  fs [] >>
  rw [lookup_insert]);

val lookup_inc_lookup_new = Q.prove (
  `lookup_inc t new_cids = (tag,new_cids')
   ⇒
   lookup t new_cids = NONE ∧ tag = 0 ∨ lookup t new_cids = SOME tag`,
  rw [lookup_inc_def] >>
  every_case_tac >>
  fs [] >>
  rw []);

val alloc_tags_submap = Q.prove (
  `!idx new_cids ctors ns cids.
    alloc_tags idx new_cids ctors = (ns, cids)
    ⇒
    !arity max_tag. lookup arity new_cids = SOME max_tag ⇒
      ?max_tag'. lookup arity cids = SOME max_tag' ∧ max_tag ≤ max_tag'`,
  Induct_on `ctors` >>
  rw [alloc_tags_def] >>
  PairCases_on `h` >>
  fs [alloc_tags_def] >>
  rpt (pairarg_tac >> fs []) >>
  fs [lookup_inc_def] >>
  every_case_tac >>
  fs [] >>
  res_tac >>
  rw [] >>
  fs [lookup_insert]
  >- (
    first_x_assum irule >>
    rw [] >>
    fs []) >>
  Cases_on `LENGTH h1 = arity` >>
  fs [] >>
  pop_assum kall_tac >>
  rw [] >>
  pop_assum (qspecl_then [`max_tag + 1`, `arity`] mp_tac) >>
  rw [] >>
  rw []);

val evaluate_alloc_tags = Q.prove (
  `!idx (ctors :(tvarN, ast_t list) alist) ns cids genv s s' new_cids.
   invariant genv idx s s' ∧
   alloc_tags idx.tidx new_cids ctors = (ns, cids) ∧
   (!tag arity. ((tag,SOME idx.tidx),arity) ∈ FDOM genv.c ⇒
     (?max_tag. lookup arity new_cids = SOME max_tag ∧ tag < max_tag)) ∧
   ALL_DISTINCT (MAP FST ctors)
   ⇒
   ?genv_c.
     {((t,SOME idx.tidx),arity) | ?t'. lookup arity cids = SOME t' ∧ t < t' }
     DIFF
     {((t,SOME idx.tidx),arity) | ?t'. lookup arity new_cids = SOME t' ∧ t < t' } = FDOM genv_c ∧
     (!tag typ arity stamp.
       FLOOKUP genv_c ((tag,typ),arity) = SOME stamp ⇒
       typ = SOME idx.tidx ∧
       (lookup arity new_cids ≠ NONE ⇒
         ?max_tag. lookup arity new_cids = SOME max_tag ∧ tag ≥ max_tag) ∧
       ?cn. cn ∈ set (MAP FST ctors) ∧
         stamp = TypeStamp cn s.next_type_stamp) ∧
     nsDom ns = IMAGE Short (set (MAP FST ctors)) ∧
     nsDomMod ns = { [] } ∧
     invariant
       (genv with c := FUNION genv_c genv.c)
       (idx with tidx updated_by SUC)
       (s with next_type_stamp updated_by SUC)
       s' ∧
      global_env_inv (genv with c := FUNION genv_c genv.c)
        <| c := ns; v := nsEmpty |>
        {}
        <| v := nsEmpty; c := alist_to_ns (REVERSE (build_constrs s.next_type_stamp ctors)) |>`,
  Induct_on `ctors` >>
  rw [alloc_tags_def, build_constrs_def, extend_env_def, extend_dec_env_def] >>
  rw []
  >- (
    qexists_tac `FEMPTY` >>
    fs [invariant_def, v_rel_eqns, s_rel_cases] >>
    `genv with c := genv.c = genv` by rw [theorem "global_env_component_equality"] >>
    metis_tac []) >>
  rename [`alloc_tags _ _ (c::_) = _`] >>
  `?cn ts. c = (cn,ts)` by metis_tac [pair_CASES] >>
  fs [alloc_tags_def] >>
  rpt (pairarg_tac >> fs []) >>
  rw [] >>
  first_x_assum drule >>
  disch_then drule >>
  impl_keep_tac
  >- (
    rw [] >>
    res_tac >>
    fs [lookup_inc_def] >>
    every_case_tac >>
    fs [] >>
    rw [lookup_insert] >>
    fs []) >>
  simp [invariant_def, v_rel_eqns, s_rel_cases, extend_env_def, extend_dec_env_def] >>
  rw [] >>
  qexists_tac `genv_c |+ (((tag, SOME idx.tidx), LENGTH ts),
                          TypeStamp cn s.next_type_stamp)` >>
  `((tag, SOME idx.tidx), LENGTH ts) ∉ FDOM (FUNION genv_c genv.c)`
  by (
    CCONTR_TAC >>
    fs [FLOOKUP_DEF] >>
    res_tac >>
    fs [lookup_inc_def] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    fs [lookup_insert]) >>
  rw []
  >- (
    qpat_x_assum `_ DIFF _ = FDOM _` (assume_tac o GSYM) >>
    rw [] >>
    qmatch_goalsub_abbrev_tac `S1 DIFF S2 = x INSERT _ DIFF S3` >>
    `x ∈ S1`
    by (
      simp [Abbr`x`, Abbr`S1`] >>
      drule alloc_tags_submap >>
      disch_then (qspecl_then [`LENGTH ts`, `tag + 1`] mp_tac) >>
      simp [DECIDE ``!x:num y. x +1 ≤ y ⇔ x < y``] >>
      disch_then irule >>
      metis_tac [lookup_inc_lookup]) >>
    `x ∉ S2`
    by (
      simp [Abbr`x`, Abbr`S2`] >>
      drule lookup_inc_lookup_new >>
      rw [] >>
      rw []) >>
    `S3 = x INSERT S2`
    by (
      simp [Abbr`x`, Abbr`S2`, Abbr`S3`] >>
      rw [EXTENSION] >>
      eq_tac >>
      rw []
      >- (
        rw [PROVE [] ``!x y. x ∨ y ⇔ ~x ⇒ y``] >>
        drule lookup_inc_lookup_new >>
        drule lookup_inc_lookup >>
        drule lookup_inc_lookup_unchanged >>
        rw [] >>
        fs [] >>
        Cases_on `arity = LENGTH ts` >>
        fs [])
      >- (
        drule lookup_inc_lookup >>
        rw [])
      >- (
        Cases_on `arity = LENGTH ts` >>
        fs [] >>
        drule lookup_inc_lookup_unchanged >>
        rw [] >>
        metis_tac [])) >>
    rw [EXTENSION] >>
    eq_tac >>
    rw [] >>
    CCONTR_TAC >>
    fs [SUBSET_DEF])
  >- (
    fs [FLOOKUP_UPDATE] >>
    every_case_tac >>
    fs [] >>
    metis_tac [])
  >- (
    fs [FLOOKUP_UPDATE] >>
    every_case_tac >>
    fs []
    >- (
      rw [] >>
      fs [lookup_inc_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_insert])
    >- (
      res_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_inc_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_insert]
      >- metis_tac [] >>
      every_case_tac >>
      fs [])
    >- metis_tac []
    >- (
      res_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_inc_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      fs [lookup_insert]
      >- metis_tac [] >>
      every_case_tac >>
      fs []))
  >- (
    fs [FLOOKUP_UPDATE] >>
    every_case_tac >>
    fs [] >>
    metis_tac [])
  >- (
    simp [FUNION_FUPDATE_1] >>
    simp [genv_c_ok_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- (
      fs [has_bools_def, invariant_def, genv_c_ok_def] >>
      simp [FLOOKUP_UPDATE] >>
      fs [FLOOKUP_DEF] >>
      metis_tac [DECIDE ``x ≥ x : num``]) >>
    conj_tac
    >- (
      fs [has_exns_def, invariant_def, genv_c_ok_def] >>
      simp [FLOOKUP_UPDATE] >>
      fs [FLOOKUP_DEF] >>
      metis_tac [DECIDE ``x ≥ x : num``]) >>
    conj_tac
    >- (
      fs [has_lists_def, invariant_def, genv_c_ok_def] >>
      simp [FLOOKUP_UPDATE] >>
      fs [FLOOKUP_DEF] >>
      metis_tac [DECIDE ``x ≥ x : num``]) >>
    conj_tac
    >- (
      rw []
      >- fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def]
      >- (
        pop_assum mp_tac >>
        simp [FLOOKUP_FUNION] >>
        every_case_tac >>
        rw [] >>
        PairCases_on `cn2`
        >- (
          Cases_on `stamp2` >>
          fs [invariant_def] >>
          fs [FLOOKUP_DEF] >>
          `cn21 ≠ SOME idx.tidx` by metis_tac [PAIR_EQ, DECIDE ``x ≥ x : num``] >>
          rw [] >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
          fs [FRANGE_DEF] >>
          metis_tac [DECIDE ``!x:num. x ≥ x``])
        >- (
          Cases_on `stamp2` >>
          res_tac >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
          res_tac >>
          fs [invariant_def, FLOOKUP_DEF, genv_c_ok_def]))
      >- (
        pop_assum mp_tac >>
        simp [FLOOKUP_FUNION] >>
        every_case_tac >>
        rw [] >>
        PairCases_on `cn1`
        >- (
          Cases_on `stamp1` >>
          fs [invariant_def] >>
          fs [FLOOKUP_DEF] >>
          `cn11 ≠ SOME idx.tidx` by metis_tac [PAIR_EQ, DECIDE ``x ≥ x : num``] >>
          rw [] >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
          fs [FRANGE_DEF] >>
          metis_tac [DECIDE ``!x:num. x ≥ x``])
        >- (
          Cases_on `stamp1` >>
          res_tac >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
          res_tac >>
          fs [invariant_def, FLOOKUP_DEF, genv_c_ok_def]))
      >- metis_tac [genv_c_ok_def])
    >- (
      rpt gen_tac >>
      strip_tac >>
      every_case_tac
      >- (
        fs [FLOOKUP_FUNION] >>
        every_case_tac >>
        fs [invariant_def, FLOOKUP_DEF, FRANGE_DEF] >>
        rw [] >>
        metis_tac [DECIDE ``x ≥ x : num``, stamp_11, pair_CASES])
      >- (
        fs [FLOOKUP_FUNION] >>
        every_case_tac >>
        fs [invariant_def, FLOOKUP_DEF, FRANGE_DEF] >>
        rw [] >>
        metis_tac [DECIDE ``x ≥ x : num``, stamp_11, pair_CASES])
      >- metis_tac [genv_c_ok_def]))
  >- (
    simp [FRANGE_FUPDATE, FUNION_FUPDATE_1] >>
    fs [] >>
    res_tac >>
    fs [IN_FRANGE, FDOM_DRESTRICT] >>
    rw [DRESTRICT_DEF] >>
    metis_tac [])
  >- (
    simp [Once FUPDATE_EQ_FUNION] >>
    fs [s_rel_cases] >>
    res_tac >>
    simp [GSYM FUNION_ASSOC] >>
    qabbrev_tac `g = genv_c ⊌ genv.c` >>
    fs [IN_FRANGE] >>
    rw [] >>
    CCONTR_TAC >>
    fs [] >>
    rfs [FAPPLY_FUPDATE, FUNION_DEF] >>
    every_case_tac >>
    fs [] >>
    metis_tac [])
  >- (
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    simp [Once FUPDATE_EQ_FUNION] >>
    simp [GSYM FUNION_ASSOC] >>
    rfs [] >>
    res_tac >>
    irule sv_rel_weak >>
    simp [] >>
    qexists_tac `<|v := s'.globals; c := genv_c ⊌ genv.c|>` >>
    rw [SUBMAP_DEF, FAPPLY_FUPDATE, FUNION_DEF, subglobals_refl] >>
    rw [] >>
    metis_tac [])
  >- (
    pop_assum mp_tac >>
    rw [nsLookup_alist_to_ns_some]
    >- (
       fs [ALOOKUP_APPEND, nsLookup_nsAppend_some, nsLookup_alist_to_ns_some] >>
       every_case_tac >>
       fs [] >>
       rw [] >>
       fs [FLOOKUP_UPDATE, FUNION_FUPDATE_1]
       >- (
         drule ALOOKUP_MEM >>
         simp [MEM_MAP, EXISTS_PROD] >>
         rw [] >>
         fs [MEM_MAP] >>
         metis_tac [FST]) >>
       rw [nsLookup_nsAppend_some] >>
       first_x_assum (qspecl_then [`Short x'`, `arity`, `stamp`] mp_tac) >>
       rw [build_constrs_def] >>
       rw [] >>
       fs [FLOOKUP_DEF] >>
       fs [])));

val nsAppend_foldl' = Q.prove (
  `!l ns ns'.
   nsAppend (FOLDL (λns (l,cids). nsAppend l ns) ns' l) ns
   =
   FOLDL (λns (l,cids). nsAppend l ns) (nsAppend ns' ns) l`,
  Induct_on `l` >>
  rw [] >>
  PairCases_on `h` >>
  rw []);

val nsAppend_foldl = Q.prove (
  `!l ns.
   FOLDL (λns (l,cids). nsAppend l ns) ns l
   =
   nsAppend (FOLDL (λns (l,cids). nsAppend l ns) nsEmpty l) ns`,
  metis_tac [nsAppend_foldl', nsAppend_nsEmpty]);

val evaluate_make_varls = Q.prove (
  `!n t idx vars g g' s env vals.
    LENGTH g = idx ∧
    s.globals = g ++ REPLICATE (LENGTH vars) NONE ++ g' ∧
    LENGTH vals = LENGTH vars ∧
    (!n. n < LENGTH vals ⇒ ALOOKUP env.v (EL n vars) = SOME (EL n vals)) ∧
    env.check_ctor
    ⇒
    flatSem$evaluate env s [make_varls n t idx vars] =
    (s with globals := g ++ MAP SOME vals ++ g', Rval [flatSem$Conv NONE []])`,
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
    fs []) >>
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
  by rw [environment_component_equality, libTheory.opt_bind_def] >>
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
  rw [state_component_equality]);

val build_tdefs_no_mod = Q.prove (
  `!idx tdefs. nsDomMod (build_tdefs idx tdefs) = {[]}`,
  Induct_on `tdefs` >>
  rw [build_tdefs_def] >>
  PairCases_on `h` >>
  rw [build_tdefs_def] >>
  pop_assum (qspec_then `idx+1` mp_tac) >>
  rw [nsDomMod_nsAppend_flat]);

val compile_decs_correct' = Q.prove (
  `!s env ds s' r comp_map s_i1 idx idx' comp_map' ds_i1 t t' genv.
    evaluate$evaluate_decs s env ds = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    invariant genv idx s s_i1 ∧
    global_env_inv genv comp_map {} env ∧
    source_to_flat$compile_decs t idx comp_map ds = (t', idx', comp_map', ds_i1) ∧
    idx'.vidx ≤ LENGTH genv.v
    ⇒
    ?(s'_i1:'a flatSem$state) genv' cenv' r_i1.
      flatSem$evaluate_decs <| c := FDOM genv.c; v := []; exh_pat := F; check_ctor := T |> s_i1 ds_i1 = (s'_i1,cenv',r_i1) ∧
      genv.c SUBMAP genv'.c ∧
      subglobals genv.v genv'.v ∧
      FDOM genv'.c = cenv' ∪ FDOM genv.c ∧
      invariant genv' idx' s' s'_i1 ∧
      (!env'.
        r = Rval env'
        ⇒
        r_i1 = NONE ∧
        env_domain_eq comp_map' env' ∧
        global_env_inv genv' comp_map' {} env') ∧
      (!err.
        r = Rerr err
        ⇒
        ?err_i1.
          r_i1 = SOME err_i1 ∧
          result_rel (\a b (c:'a). T) genv' (Rerr err) (Rerr err_i1))`,
  ho_match_mp_tac terminationTheory.evaluate_decs_ind >>
  simp [terminationTheory.evaluate_decs_def] >>
  conj_tac
  >- (
    rw [compile_decs_def, evaluate_decs_def, v_rel_eqns, invariant_def, env_domain_eq_def] >>
    rw [extend_dec_env_def, evaluate_decs_def, extend_env_def, empty_env_def] >>
    qexists_tac `genv` >>
    metis_tac [SUBMAP_REFL, subglobals_refl]) >>
  conj_tac
  >- (
    rpt gen_tac >>
    simp [compile_decs_def] >>
    qspec_tac (`d2::ds`, `ds`) >>
    rw [] >>
    ntac 2 (pairarg_tac \\ fs[])
    \\ rveq
    \\ qpat_x_assum`_ = (_,r)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw [] >>
      fs [] >>
      first_x_assum drule >>
      disch_then drule >>
      disch_then drule >>
      impl_tac
      >- (
        imp_res_tac compile_decs_num_bindings >>
        rw []) >>
      rw [] >>
      simp [PULL_EXISTS] >>
      MAP_EVERY qexists_tac [`s'_i1`, `genv'`, `cenv'`, `err_i1`] >>
      rw [] >>
      fs [invariant_def]
      >- metis_tac [evaluate_decs_append_err] >>
      drule compile_decs_num_bindings >>
      fs [] >>
      rw [] >>
      rfs [] >>
      metis_tac [GREATER_EQ]) >>
    BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rw[] >>
    first_x_assum drule >>
    disch_then drule >>
    disch_then drule >>
    impl_tac
    >- (
      imp_res_tac compile_decs_num_bindings >>
      rw []) >>
    rw [] >>
    `r' ≠ Rerr (Rabort Rtype_error)`
    by (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs []) >>
    fs [] >>
    first_x_assum drule >>
    `global_env_inv genv' (extend_env new_env1 comp_map) {} (extend_dec_env a env)`
    by metis_tac [global_env_inv_append, global_env_inv_weak] >>
    disch_then drule >>
    disch_then drule >>
    impl_tac
    >- (
      imp_res_tac compile_decs_num_bindings >>
      fs [subglobals_def]) >>
    rw [] >>
    rename1 `evaluate_decs <|v := []; c := cenv1 ∪ FDOM genv.c; exh_pat := F; check_ctor := T |> s1 ds2 = (s2, cenv2, r2)` >>
    MAP_EVERY qexists_tac [`s2`, `genv''`, `cenv2 ∪ cenv1`, `r2`] >>
    rw [UNION_ASSOC]
    >- (
      irule evaluate_decs_append >>
      rw [])
    >- metis_tac [SUBMAP_TRANS]
    >- metis_tac [subglobals_trans]
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [])
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      rw [] >>
      fs [] >>
      imp_res_tac env_domain_eq_append >>
      fs [extend_dec_env_def])
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      imp_res_tac global_env_inv_weak >>
      drule global_env_inv_append >>
      fs [extend_dec_env_def])
    >- (
      fs [combine_dec_result_def] >>
      every_case_tac >>
      fs [] >>
      rw [] >>
      MAP_EVERY qexists_tac [`small_idx`] >>
      fs [])) >>
  rw [compile_decs_def]
  >- ( (* Let *)
    split_pair_case_tac >>
    fs [] >>
    qmatch_assum_rename_tac `evaluate _ _ _ = (st', res)` >>
    drule compile_exp_correct >>
    `res ≠ Rerr (Rabort Rtype_error)`
    by (Cases_on `res` >> rfs [] >> rw []) >>
    rveq >>
    fs [invariant_def] >>
    disch_then drule >>
    disch_then (qspecl_then [`comp_map`, `s_i1`] mp_tac) >>
    spect`(om_tra ▷ t)`>>
    `<|v := s_i1.globals; c := genv.c|> = genv` by rw [theorem "global_env_component_equality"] >>
    simp [] >>
    rw [flatSemTheory.evaluate_decs_def, flatSemTheory.evaluate_dec_def,
        flatSemTheory.evaluate_def, compile_exp_def, result_rel_cases] >>
    rw [] >>
    fs [] >>
    rw []
    >- ( (* Expression evaluates *)
      qmatch_assum_rename_tac `evaluate _ _ [e] = (st', Rval answer')` >>
      `?answer. answer' = [answer]`
      by (
        imp_res_tac evaluate_sing >>
        fs []) >>
      fs [] >>
      rpt var_eq_tac >>
      qmatch_assum_rename_tac `evaluate _ _ [compile_exp _ comp_map e] = (st1', Rval [answer1])` >>
      `match_result_rel genv [] (pmatch env.c st'.refs p answer ([]++[]))
             (pmatch <| v := []; c := FDOM genv.c; exh_pat := F; check_ctor := T |> st1'.refs (compile_pat comp_map p) answer1 [])`
      by (
        match_mp_tac pmatch_lem >>
        simp [] >>
        fs [s_rel_cases] >>
        fs [v_rel_eqns] >>
        metis_tac []) >>
      Cases_on `pmatch env.c st'.refs p answer [] ` >>
      fs []
      >- ( (* No match *)
        rw [PULL_EXISTS] >>
        every_case_tac >>
        fs [match_result_rel_def] >>
        qexists_tac `genv` >>
        rw [subglobals_refl] >>
        rw [v_rel_lems, extend_env_def, extend_dec_env_def] >>
        fs [v_rel_eqns] >>
        fs [s_rel_cases] >>
        imp_res_tac evaluatePropsTheory.evaluate_state_unchanged >>
        metis_tac [])
      >- ( (* Match *)
        qmatch_asmsub_abbrev_tac `match_result_rel _ _ (Match _) r` >>
        Cases_on `r` >>
        fs [match_result_rel_def] >>
        rename [`evaluate <| v := env; c := _; exh_pat := _; check_ctor := _ |>
                   s [make_varls _ _ _ _]`] >>
        `?g1 g2.
          LENGTH g1 = idx.vidx ∧
          s.globals = g1++REPLICATE (LENGTH (REVERSE (pat_bindings p []))) NONE++g2`
        by (
          qexists_tac `TAKE idx.vidx s.globals` >>
          qexists_tac `DROP (idx.vidx + LENGTH (pat_bindings p [])) s.globals` >>
          simp [] >>
          `idx.vidx ≤ LENGTH genv.v` by decide_tac >>
          rw [] >>
          rfs [] >>
          irule LIST_EQ >>
          rw [EL_APPEND_EQN, EL_TAKE, EL_REPLICATE, EL_DROP]) >>
        drule evaluate_make_varls >>
        disch_then drule >>
        disch_then (qspecl_then [`0`, `om_tra ▷ t + 3`,
           `<|v := env; c := FDOM genv.c; exh_pat := F; check_ctor := T|>`,
           `MAP SND (REVERSE env)`] mp_tac) >>
        fs [markerTheory.Abbrev_def] >>
        qpat_x_assum `Match _ = pmatch _ _ _ _ _` (assume_tac o GSYM) >>
        drule (CONJUNCT1 pmatch_bindings) >>
        simp [] >>
        strip_tac >>
        impl_tac
        >- metis_tac [EL_MAP, alookup_distinct_reverse, ALOOKUP_ALL_DISTINCT_EL,
                      LENGTH_MAP, LENGTH_REVERSE, MAP_REVERSE,
                      ALL_DISTINCT_REVERSE] >>
        rw [] >>
        qexists_tac `<| v := g1 ⧺ MAP SOME (MAP SND (REVERSE env)) ⧺ g2;
                        c := genv.c |>` >>
        conj_tac
        >- simp [] >>
        conj_asm1_tac
        >- (
          rw [] >>
          simp_tac std_ss [subglobals_refl_append, GSYM APPEND_ASSOC] >>
          `LENGTH (REPLICATE (LENGTH (pat_bindings p [])) (NONE:flatSem$v option)) =
           LENGTH (MAP SOME (MAP SND (REVERSE env)))`
          by (
            rw [LENGTH_REPLICATE] >>
            metis_tac [LENGTH_MAP]) >>
          imp_res_tac subglobals_refl_append >>
          rw [] >>
          rw [subglobals_def] >>
          `n < LENGTH (pat_bindings p [])` by metis_tac [LENGTH_MAP] >>
          fs [EL_REPLICATE]) >>
        rw []
        >- (
          `LENGTH (pat_bindings p []) = LENGTH env` by metis_tac [LENGTH_MAP] >>
          rw [EL_APPEND_EQN] >>
          last_x_assum (qspec_then `n` mp_tac) >>
          simp [EL_APPEND_EQN])
        >- metis_tac [evaluatePropsTheory.evaluate_state_unchanged, s_rel_cases]
        >- metis_tac [evaluatePropsTheory.evaluate_state_unchanged, s_rel_cases]
        (*
        >- metis_tac [evaluatePropsTheory.evaluate_state_unchanged, s_rel_cases]
        >- metis_tac [evaluatePropsTheory.evaluate_state_unchanged, s_rel_cases]
        *)
        >- (
          fs [s_rel_cases] >>
          irule LIST_REL_mono >>
          qexists_tac `sv_rel <|v := s_i1.globals; c := genv.c|>` >>
          rw []
          >- (
            irule sv_rel_weak >>
            qexists_tac `genv` >>
            rw []) >>
          metis_tac [])
        >- (
          fs [env_domain_eq_def] >>
          drule (CONJUNCT1 pmatch_bindings) >>
          simp [GSYM MAP_MAP_o, fst_alloc_defs, EXTENSION] >>
          rw [MEM_MAP] >>
          imp_res_tac env_rel_dom >>
          fs [] >>
          metis_tac [FST, MEM_MAP])
        >- (
          fs [] >>
          qspecl_then [`a`, `<|v := g1 ⧺ MAP SOME (MAP SND (REVERSE env)) ⧺ g2; c := genv.c|>`,
                       `env`, `t+4`, `g1`, `g2`] mp_tac global_env_inv_extend >>
          simp [MAP_REVERSE] >>
          impl_tac
          >- (
            imp_res_tac env_rel_dom >>
            fs [] >>
            irule env_rel_weak >>
            qexists_tac `genv` >>
            rw [] >>
            simp [subglobals_def] >>
            rw [EL_APPEND_EQN] >>
            rfs [EL_REPLICATE] >>
            metis_tac [LENGTH_MAP, LESS_EQ_REFL, ADD_COMM, ADD_ASSOC]) >>
          simp [])))
    >- ( (* Expression exception *)
      qexists_tac `genv` >>
      rw [] >>
      simp [subglobals_refl, extend_env_def, extend_dec_env_def] >>
      fs [v_rel_eqns] >>
      metis_tac [s_rel_cases, evaluatePropsTheory.evaluate_state_unchanged])
    >- ( (* Expression abort *)
      qexists_tac `genv` >>
      rw [] >>
      simp [subglobals_refl, extend_env_def, extend_dec_env_def] >>
      metis_tac [s_rel_cases, evaluatePropsTheory.evaluate_state_unchanged]))
  >- ( (* Letrec *)
    `funs = [] ∨ (?f x e. funs = [(f,x,e)]) ∨ ?f1 f2 fs. funs = f1::f2::fs`
    by metis_tac [list_CASES, pair_CASES]
    >- ( (* No functions *)
      fs [compile_decs_def] >>
      rw [evaluate_decs_def, compile_exp_def, evaluate_dec_def, alloc_defs_def,
          extend_env_def, extend_dec_env_def,
          semanticPrimitivesTheory.build_rec_env_def] >>
      qexists_tac `genv` >>
      rw [] >>
      fs [invariant_def, v_rel_eqns, s_rel_cases, env_domain_eq_def] >>
      metis_tac [subglobals_refl])
    >- ( (* One function *)
      fs [compile_decs_def] >>
      reverse (
        rw [evaluate_decs_def, evaluate_dec_def, compile_exp_def, evaluate_def,
            namespaceTheory.nsBindList_def, namespaceTheory.mk_id_def,
            nsLookup_nsBind, build_rec_env_def, do_app_def]) >>
      fs [invariant_def] >>
      `idx.vidx < LENGTH genv.v` by decide_tac >>
      fs [] >>
      rfs []
      >- (
        res_tac >>
        fs []) >>
      rw [] >>
      qmatch_goalsub_abbrev_tac `_ = LUPDATE (SOME cl) _ _` >>
      qexists_tac `<| v := LUPDATE (SOME cl) idx.vidx s_i1.globals; c := genv.c |>` >>
      rw []
      >- (
        rw [subglobals_def, EL_LUPDATE] >>
        rw [] >>
        res_tac >>
        fs [])
      >- (
        rw [subglobals_def, EL_LUPDATE] >>
        rw [] >>
        res_tac >>
        fs [])
      >- (
        fs [s_rel_cases] >>
        irule LIST_REL_mono >>
        qexists_tac `sv_rel <|v := s_i1.globals; c := genv.c|>` >>
        rw [] >>
        irule sv_rel_weak >>
        rw [] >>
        qexists_tac `<|v := s_i1.globals; c := genv.c|>` >>
        rw [subglobals_def] >>
        rw [subglobals_def, EL_LUPDATE] >>
        rw [] >>
        res_tac >>
        fs [])
      >- rw [env_domain_eq_def, semanticPrimitivesTheory.build_rec_env_def,
             alloc_defs_def]
      >- (
        rw [v_rel_eqns, nsLookup_alist_to_ns_some,
            semanticPrimitivesTheory.build_rec_env_def, EL_LUPDATE] >>
        simp [alloc_defs_def] >>
        fs [nsLookup_nsBind] >>
        Cases_on `x'` >>
        fs [] >>
        Cases_on `n = f` >>
        fs [nsLookup_nsBind] >>
        irule v_rel_weak >>
        qexists_tac `genv` >>
        rw []
        >- (
          rw [subglobals_def, EL_LUPDATE] >>
          rw [] >>
          res_tac >>
          fs []) >>
        rw [Abbr`cl`] >>
        simp [Once v_rel_cases] >>
        rw [compile_exp_def, bind_locals_def] >>
        rw [namespaceTheory.nsBindList_def] >>
        MAP_EVERY qexists_tac [`comp_map`, `env`, `nsEmpty`, `om_tra ▷t`, `[om_tra ▷t]`] >>
        simp [v_rel_eqns]))
    >- ( (* Multiple functions *)
      full_simp_tac std_ss [compile_decs_def] >>
      `LENGTH funs > 1` by rw [] >>
      qpat_x_assum `_ = _::_::_` (assume_tac o GSYM) >>
      full_simp_tac std_ss [] >>
      pop_assum kall_tac >>
      fs [] >>
      rw [mapi_map, extend_env_def] >>
      fs [invariant_def] >>
      rfs [] >>
      fs [] >>
      qmatch_goalsub_abbrev_tac `evaluate_decs env1 s1 (MAPi _ cfuns)` >>
      `LENGTH funs = LENGTH cfuns`
      by rw [Abbr`cfuns`, compile_funs_map] >>
      fs [] >>
      `env1.check_ctor` by fs[Abbr`env1`] >>
      imp_res_tac evaluate_recfuns >>
      fs [] >>
      qmatch_assum_abbrev_tac `∀t2 t1.
         evaluate_decs env1 _
           (MAPi
              (λi (f,x,e).
                 Dlet
                   (App t1 (GlobalVarInit (i + idx.vidx)) [Fun t2 x e]))
              cfuns) =
         (s2,_, _)` >>
      qexists_tac `<| v := s2.globals; c := genv.c |>` >>
      rw []
      >- (
        rw [subglobals_def, Abbr `s2`, EL_APPEND_EQN] >>
        rw [EL_TAKE, EL_DROP] >>
        fs [] >>
        `idx.vidx ≤ n` by decide_tac >>
        res_tac >>
        fs [])
      >- (
        fs [Abbr `s2`, EL_APPEND_EQN] >>
        `n < LENGTH s1.globals` by rfs [LENGTH_TAKE] >>
        rw [EL_DROP])
      >- fs [Abbr `s2`]
      >- (
        fs [s_rel_cases, Abbr `s2`] >>
        irule LIST_REL_mono >>
        qexists_tac `sv_rel <|v := s1.globals; c := genv.c|>` >>
        rw [] >>
        drule sv_rel_weak >>
        disch_then irule >>
        rw [subglobals_def, EL_APPEND_EQN] >>
        rw [EL_TAKE, EL_MAP, EL_DROP] >>
        res_tac >>
        fs [])
      >- (
        rw [env_domain_eq_def, semanticPrimitivesPropsTheory.build_rec_env_merge] >>
        rw [EXTENSION, GSYM MAP_MAP_o, fst_alloc_defs] >>
        rw [MEM_MAP, EXISTS_PROD])
      >- (
        fs [Abbr`s2`, semanticPrimitivesPropsTheory.build_rec_env_merge] >>
        qmatch_abbrev_tac `global_env_inv <| v := g1++middle++g2; c := _ |> _ _ <| v := alist_to_ns pat_env; c := _ |>` >>
        qspecl_then [`pat_env`,
                     `<| v := g1 ⧺ middle ⧺ g2;
                         c := genv.c|>`,
                     `REVERSE (MAP (λ(f,x,e). (f, Closure [] x e)) cfuns)`,
                     `t`, `g1`, `g2`]
                    mp_tac global_env_inv_extend >>
        simp [Abbr`pat_env`, Abbr`middle`, MAP_REVERSE, MAP_MAP_o, o_DEF,
              LAMBDA_PROD, fst_lem] >>
        `LENGTH g1 = idx.vidx` by rw [Abbr`g1`, LENGTH_TAKE] >>
        simp [] >>
        `MAP FST cfuns = REVERSE (MAP FST funs)`
        by (
          rw [Abbr`cfuns`] >>
          metis_tac [compile_funs_dom, MAP_REVERSE, GSYM fst_lem]) >>
        simp [] >>
        disch_then irule >>
        fs [fst_lem] >>
        rw [env_rel_el]
        >- (
          simp [Abbr`cfuns`, GSYM MAP_REVERSE, compile_funs_map, MAP_MAP_o,
                o_DEF, LAMBDA_PROD] >>
          simp [EL_MAP] >>
          pairarg_tac >>
          rw []) >>
        simp [Abbr`cfuns`, Once compile_funs_map] >>
        fs [compile_funs_map] >>
        simp [GSYM MAP_REVERSE, MAP_MAP_o, o_DEF, LAMBDA_PROD, EL_MAP] >>
        pairarg_tac >>
        simp [] >>
        simp [Once v_rel_cases] >>
        MAP_EVERY qexists_tac [`comp_map`, `e`, `alloc_defs t (LENGTH g1) (MAP FST (REVERSE funs))`, `om_tra ▷ t + 1`, `om_tra ▷ t + 1`] >>
        rw []
        >- (
          rw [nsAppend_to_nsBindList] >>
          rw [namespaceTheory.nsBindList_def] >>
          irule (PROVE [] ``!f a b x y z. x = y ⇒ f a x z = f a y z``) >>
          rw [source_to_flatTheory.environment_component_equality])
        >- simp [fst_alloc_defs]
        >- (
          irule global_env_inv_weak >>
          qexists_tac `genv` >>
          rw [subglobals_def,EL_APPEND_EQN, EL_TAKE]
          >- rw [Abbr `g1`, Abbr`g2`] >>
          rw [EL_TAKE, Abbr`g1`, TAKE_LENGTH_ID]
          >- (
            res_tac >>
            fs []) >>
          fs [Abbr`g2`] >>
          res_tac >>
          `idx.vidx ≤ n''` by decide_tac >>
          fs [])
        >- (
          irule find_recfun_el >>
          rw [fst_lem] >>
          metis_tac [])
        >- (
          fs [MEM_MAP] >>
          rw [] >>
          rename [`MEM fun funs`] >>
          `?f1 x1 e1. fun = (f1,x1,e1)` by metis_tac [pair_CASES] >>
          fs [] >>
          imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
          `ALOOKUP (REVERSE funs) f1 = SOME (x1,e1)`
          by metis_tac [alookup_distinct_reverse] >>
          drule ALOOKUP_alloc_defs >>
          disch_then (qspecl_then [`idx.vidx`, `t`] mp_tac) >>
          rw [] >>
          rw [] >>
          rw [EL_APPEND_EQN, EL_MAP, find_recfun_ALOOKUP,
              nsAppend_to_nsBindList, namespaceTheory.nsBindList_def] >>
          rfs [GSYM MAP_REVERSE, EL_MAP] >>
          pairarg_tac >>
          rw [] >>
          fs [] >>
          qexists_tac `om_tra ▷ t + 1` >>
          qexists_tac `om_tra ▷ t + 1` >>
          irule (PROVE [] ``!f a b x y z. x = y ⇒ f a x z = f a y z``) >>
          rw [source_to_flatTheory.environment_component_equality]))))
  >- ( (* Type definition *)
    rpt (pop_assum mp_tac) >>
    MAP_EVERY qspec_tac [(`genv`,`genv`), (`idx`,`idx`), (`comp_map`,`comp_map`), (`env`,`env`), (`s`,`s`), (`s_i1`, `s_i1`)] >>
    Induct_on `tds`
    >- ( (* No tds *)
      rw [evaluate_decs_def] >>
      simp [extend_env_def, extend_dec_env_def, build_tdefs_def] >>
      fs [invariant_def] >>
      qexists_tac `genv` >>
      simp [] >>
      fs [v_rel_eqns, s_rel_cases] >>
      rw [env_domain_eq_def, subglobals_refl]) >>
    strip_tac >>
    rename [`EVERY check_dup_ctors (td::tds)`] >>
    `?tvs tn ctors. td = (tvs, tn ,ctors)` by metis_tac [pair_CASES] >>
    rw [evaluate_decs_def] >>
    pairarg_tac >>
    fs [] >>
    simp [evaluate_dec_def] >>
    drule evaluate_alloc_tags >>
    disch_then drule >>
    simp [lookup_def] >>
    impl_tac
    >- (
      fs [terminationTheory.check_dup_ctors_thm] >>
      fs [invariant_def]) >>
    reverse (rw [])
    >- (
      fs [is_fresh_type_def, invariant_def] >>
      rw [] >>
      metis_tac [DECIDE ``!x:num. x ≥ x``]) >>
    first_x_assum drule >>
    disch_then drule >>
    rw [] >>
    qpat_x_assum `_ = FDOM _` (mp_tac o GSYM) >>
    rw [] >>
    fs [combinTheory.o_DEF, LAMBDA_PROD] >>
    fs [] >>
    `!x y. SUC x + y = x + SUC y` by decide_tac >>
    asm_simp_tac std_ss [] >>
    rw [] >>
    qexists_tac `genv'` >>
    rw []
    >- (
      irule funion_submap >>
      qexists_tac `genv_c` >>
      rw [DISJOINT_DEF, EXTENSION] >>
      CCONTR_TAC >>
      fs [] >>
      rw [] >>
      fs [FLOOKUP_DEF, invariant_def] >>
      metis_tac [DECIDE ``!x. x ≥ x:num``])
    >- metis_tac [UNION_ASSOC]
    >- (
      fs [env_domain_eq_def, build_tdefs_def, ADD1] >>
      ONCE_REWRITE_TAC [nsAppend_foldl] >>
      rw [build_tdefs_no_mod, nsDom_nsAppend_flat, nsDomMod_nsAppend_flat,
          o_DEF, build_constrs_def, MAP_REVERSE, MAP_MAP_o, EXTENSION] >>
      eq_tac >>
      rw [MEM_MAP, EXISTS_PROD] >>
      metis_tac [FST])
    >- (
      fs [build_tdefs_def, v_rel_eqns] >>
      rw [] >>
      fs [nsLookup_nsAppend_some, ADD1]
      >- (
        res_tac >>
        qexists_tac `cn` >>
        rw [Once nsAppend_foldl] >>
        rw [nsLookup_nsAppend_some])
      >- (
        fs [build_constrs_def, nsLookup_alist_to_ns_some, env_domain_eq_def] >>
        rw [Once nsAppend_foldl] >>
        rw [nsLookup_nsAppend_some] >>
        qmatch_goalsub_abbrev_tac `nsLookup rest _ = SOME _` >>
        `nsLookup rest (Short x') = NONE`
        by (
          fs [nsLookup_nsDom, EXTENSION] >>
          metis_tac [NOT_SOME_NONE, option_nchotomy]) >>
        simp [] >>
        res_tac >>
        fs [namespaceTheory.id_to_mods_def] >>
        metis_tac [flookup_funion_submap])))
  >- ( (* type abbreviation *)
    fs [evaluate_decs_def, evaluate_dec_def] >>
    qexists_tac `genv` >>
    fs [invariant_def, s_rel_cases, v_rel_eqns, extend_dec_env_def, extend_env_def,
        empty_env_def, env_domain_eq_def] >>
    metis_tac [subglobals_refl])
  >- ( (* exceptions *)
    reverse (rw [evaluate_decs_def, evaluate_dec_def]) >>
    fs [invariant_def, s_rel_cases, v_rel_eqns]
    >- (
      fs [is_fresh_exn_def] >>
      rw [] >>
      metis_tac [DECIDE ``!x:num.x ≥ x``]) >>
    qexists_tac `genv with c := genv.c |+ (((idx.eidx,NONE),LENGTH ts), ExnStamp s.next_exn_stamp)` >>
    rw []
    >- metis_tac [subglobals_refl]
    >- simp [EXTENSION]
    >- (
      fs [genv_c_ok_def] >>
      rw []
      >- fs [has_bools_def, FLOOKUP_UPDATE]
      >- (
        fs [has_exns_def, FLOOKUP_UPDATE] >>
        rw [] >>
        fs [FLOOKUP_DEF, is_fresh_exn_def])
      >- fs [has_lists_def, FLOOKUP_UPDATE]
      >- (
        fs [FLOOKUP_UPDATE] >>
        every_case_tac >>
        rw []
        >- rw [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def]
        >- (
          fs [has_exns_def, div_stamp_def] >>
          res_tac >>
          Cases_on `stamp1` >>
          Cases_on `cn1` >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def])
        >- (
          fs [has_exns_def, div_stamp_def] >>
          res_tac >>
          Cases_on `stamp2` >>
          Cases_on `cn2` >>
          fs [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def])
        >- metis_tac [])
      >- (
        fs [FLOOKUP_UPDATE] >>
        every_case_tac >>
        fs [FLOOKUP_DEF, FRANGE_DEF, s_rel_cases] >>
        rw [] >>
        metis_tac [DECIDE ``!x.x≥x:num``])
      >- (
        fs [FLOOKUP_UPDATE] >>
        every_case_tac >>
        fs [FLOOKUP_DEF, FRANGE_DEF, s_rel_cases] >>
        rw [] >>
        metis_tac [DECIDE ``!x.x≥x:num``]))
    >- metis_tac [DECIDE ``x ≤ x:num``]
    >- (
      fs [IN_FRANGE] >>
      rw [DOMSUB_FAPPLY_THM])
    >- (
      fs [IN_FRANGE] >>
      rw [DOMSUB_FAPPLY_THM])
    >- (
      irule LIST_REL_mono >>
      qexists_tac `sv_rel <|v := s_i1.globals; c := genv.c|>` >>
      rw [] >>
      irule sv_rel_weak >>
      rw [] >>
      qexists_tac `genv` >>
      rw [subglobals_refl] >>
      `genv = <|v := s_i1.globals; c := genv.c|>` by rw [theorem "global_env_component_equality"] >>
      metis_tac [])
    >- rw [env_domain_eq_def]
    >- rw [FLOOKUP_DEF])
  >- ( (* Module *)
    pairarg_tac >>
    fs [] >>
    rw [] >>
    split_pair_case_tac >>
    fs [] >>
    rw [] >>
    rename [`evaluate_decs _ _ _ = (s1, r1)`] >>
    `r1 ≠ Rerr (Rabort Rtype_error)` by (every_case_tac >> fs []) >>
    fs [] >>
    first_x_assum drule >>
    disch_then drule >>
    disch_then drule >>
    rw [] >>
    rw [] >>
    qexists_tac `genv'` >>
    rw [] >>
    every_case_tac >>
    fs []
    >- (
      fs [env_domain_eq_def, lift_env_def] >>
      rw [nsDom_nsLift, nsDomMod_nsLift])
    >- (
      rw [] >>
      fs [v_rel_eqns] >>
      rw [lift_env_def, nsLookup_nsLift] >>
      CASE_TAC >>
      rw [] >>
      fs [])
    >- rw [])
  >- ( (* local *)
    pairarg_tac >>
    fs [] >>
    pairarg_tac >>
    fs [] >>
    rveq >>
    imp_res_tac compile_decs_num_bindings >>
    split_pair_case_tac >>
    rename [`evaluate_decs _ _ _ = (s1, r1)`] >>
    fs [] >>
    Cases_on `r1 = Rerr (Rabort Rtype_error)` >> rw [] >> fs [] >>
    first_x_assum drule >>
    disch_then drule >>
    disch_then drule >>
    rw [] >>
    reverse (Cases_on `r1`)
    >- ( (* err case *)
      fs [] >>
      rveq >>
      drule evaluate_decs_append_err >>
      rw [] >>
      rpt (CHANGED_TAC asm_exists_tac) >>
      fs [] >>
      fs [invariant_def]
    ) >>
    (* result case *)
    fs [] >>
    first_x_assum drule >>
    `global_env_inv genv' (extend_env new_env1 comp_map) {} (extend_dec_env a env)`
    by metis_tac [global_env_inv_append, global_env_inv_weak] >>
    disch_then drule >>
    disch_then drule >>
    fs [] >>
    (impl_tac >- fs [subglobals_def]) >>
    rw [] >>
    imp_res_tac evaluate_decs_append >>
    fs [] >>
    first_x_assum drule >>
    fs [] >>
    rw [] >>
    qexists_tac `genv''` >>
    fs [UNION_ASSOC] >>
    metis_tac [SUBMAP_TRANS, subglobals_trans]
  ));

Theorem compile_decs_correct:
   !s env ds s' r comp_map s_i1 idx ds_i1 next' genv.
    evaluate$evaluate_decs s env ds = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    invariant genv idx s s_i1 ∧
    global_env_inv genv comp_map {} env ∧
    source_to_flat$compile_prog <| next := idx; mod_env := comp_map |> ds = (next', ds_i1) ∧
    idx.vidx ≤ LENGTH genv.v
    ⇒
    ?(s'_i1:'a flatSem$state) genv' cenv' r_i1.
      flatSem$evaluate_decs <| c := FDOM genv.c; v := []; exh_pat := F; check_ctor := T |> s_i1 ds_i1 = (s'_i1,cenv',r_i1) ∧
      genv.c SUBMAP genv'.c ∧
      subglobals genv.v genv'.v ∧
      FDOM genv'.c = cenv' ∪ FDOM genv.c ∧
      invariant genv' next'.next s' s'_i1 ∧
      (!env'.
        r = Rval env'
        ⇒
        r_i1 = NONE ∧
        env_domain_eq next'.mod_env env' ∧
        global_env_inv genv' next'.mod_env {} env') ∧
      (!err.
        r = Rerr err
        ⇒
        ?err_i1.
          r_i1 = SOME err_i1 ∧
          result_rel (\a b (c:'a). T) genv' (Rerr err) (Rerr err_i1))
Proof
  rw [compile_prog_def, glob_alloc_def] >>
  pairarg_tac >>
  fs [] >>
  rw [evaluate_decs_def, evaluate_dec_def, evaluate_def, do_app_def] >>
  drule compile_decs_correct' >>
  simp [] >>
  qabbrev_tac `ext_glob = s_i1.globals ⧺ REPLICATE (next.vidx − idx.vidx) NONE` >>
  `invariant (genv with v := ext_glob) idx s (s_i1 with globals := ext_glob)`
  by (
    fs [invariant_def, Abbr`ext_glob`] >>
    rw [EL_APPEND_EQN] >>
    fs []
    >- rw [EL_REPLICATE] >>
    fs [s_rel_cases] >>
    irule LIST_REL_mono >>
    qexists_tac `sv_rel <|v := s_i1.globals; c := genv.c|>` >>
    rw [] >>
    irule sv_rel_weak >>
    rw [] >>
    qexists_tac `<|v := s_i1.globals; c := genv.c|>` >>
    rw [subglobals_def, EL_APPEND_EQN]) >>
  `global_env_inv (genv with v := ext_glob) comp_map {} env`
  by (
    irule global_env_inv_weak >>
    simp [] >>
    qexists_tac `genv` >>
    fs [invariant_def] >>
    rw [Abbr `ext_glob`, subglobals_def, EL_APPEND_EQN] >>
    rw []) >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  impl_tac
  >- (
    rw [Abbr`ext_glob`] >>
    fs [invariant_def] >>
    rfs []) >>
  rw [] >>
  rw [] >>
  qexists_tac `genv''` >>
  rw [Abbr`ext_glob`] >>
  fs [invariant_def] >>
  qpat_x_assum `subglobals _ _` mp_tac >>
  simp [subglobals_def, PULL_FORALL] >>
  strip_tac >>
  disch_then (qspec_then `n` mp_tac) >>
  simp [EL_APPEND_EQN] >>
  rw []
QED

Theorem invariant_change_clock:
   invariant genv env st1 st2 ⇒
   invariant genv env (st1 with clock := k) (st2 with clock := k)
Proof
  srw_tac[][invariant_def] >> full_simp_tac(srw_ss())[s_rel_cases]
QED

(* TODO initial_ctors ⊆ FDOM genv.c could do and that follows
   from genv_c_ok *)
val precondition_def = Define`
  precondition s1 env1 conf  ⇔
    ?genv.
      invariant genv conf.next s1 (initial_state s1.ffi s1.clock) ∧
      global_env_inv genv conf.mod_env {} env1 ∧
      conf.next.vidx ≤ LENGTH genv.v ∧
      FDOM genv.c = initial_ctors`;

val SND_eq = Q.prove(
  `SND x = y ⇔ ∃a. x = (a,y)`,
  Cases_on`x`\\rw[]);

Theorem compile_prog_correct:
   precondition s1 env1 c ⇒
   ¬semantics_prog s1 env1 prog Fail ⇒
   semantics_prog s1 env1 prog (semantics F T s1.ffi (SND (compile_prog c prog)))
Proof
  rw[semantics_prog_def,SND_eq,precondition_def]
  \\ simp[flatSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs[SND_eq]
  >- (
    fs[semantics_prog_def,SND_eq]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ simp[]
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) \\ fs[]
    \\ spose_not_then strip_assume_tac \\ fs[]
    \\ fs[evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs[] \\ rw[]
    \\ drule (GEN_ALL compile_decs_correct)
    \\ imp_res_tac  invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ asm_exists_tac \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`flatSem$evaluate_decs env2'`
    \\ `env2' = initial_env F T`
       by (rw[environment_component_equality,initial_env_def,Abbr `env2'`])
    \\ fs[]
    \\ asm_exists_tac
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `compile_prog e _ = _`
    \\ qexists_tac `SND (compile_prog e prog)`
    \\ qexists_tac `FST (compile_prog e prog)`
    \\ rw []
    \\ `c = e` by (UNABBREV_ALL_TAC >> rw [config_component_equality])
    \\ fs []
    \\ CCONTR_TAC
    \\ Cases_on`r`
    \\ fs[result_rel_cases,initial_state_def]
    \\ rw [])
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ conj_tac
  >- (
    rw[] \\ rw[semantics_prog_def]
    \\ fs[evaluate_prog_with_clock_def]
    \\ qexists_tac`k`
    \\ pairarg_tac \\ fs[]
    \\ `r' ≠ Rerr (Rabort Rtype_error)`
       by (first_x_assum(qspecl_then[`k`,`st'.ffi`]strip_assume_tac)
          \\ rfs [])
    \\ drule (GEN_ALL compile_decs_correct)
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ simp []
    \\ disch_then drule \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `compile_prog e _ = _`
    \\ disch_then (qspecl_then [ `SND (compile_prog e prog)`
                               , `FST (compile_prog e prog)`] mp_tac)
    \\ impl_tac >- (UNABBREV_ALL_TAC >> fs[])
    \\ qmatch_goalsub_abbrev_tac`flatSem$evaluate_decs env2'`
    \\ `env2' = initial_env F T`
       by (rw[environment_component_equality,initial_env_def,Abbr `env2'`])
    \\ strip_tac
    \\ fs[invariant_def,s_rel_cases]
    \\ rveq \\ fs[]
    \\ `e = c` by (UNABBREV_ALL_TAC >> rw [config_component_equality])
    \\ fs [initial_state_def] \\ rfs []
    \\ every_case_tac \\ fs[]
    \\ rw[]
    \\ fs[result_rel_cases]
    \\ Cases_on `r' = Rerr (Rabort Rtimeout_error)`
    \\ fs [])
  \\ rw[]
  \\ simp[semantics_prog_def]
  \\ conj_tac
  >- (
    rw[]
    \\ fs[evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs[]
    \\ drule (GEN_ALL compile_decs_correct)
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ `r ≠ Rerr (Rabort Rtype_error)`
       by (first_x_assum(qspecl_then[`k`,`st'.ffi`]strip_assume_tac)
          \\ rfs [])
    \\ disch_then drule \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `compile_prog e _ = _`
    \\ disch_then (qspecl_then [ `SND (compile_prog e prog)`
                               , `FST (compile_prog e prog)`] mp_tac)
    \\ impl_tac >- (UNABBREV_ALL_TAC >> fs[])
    \\ qmatch_goalsub_abbrev_tac`flatSem$evaluate_decs env2'`
    \\ `env2' = initial_env F T`
    by ( unabbrev_all_tac \\ rw[environment_component_equality,initial_env_def])
    \\ strip_tac
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ rveq \\ fs[]
    \\ `e = c`  by (UNABBREV_ALL_TAC >> rw [config_component_equality])
    \\ fs [initial_state_def] \\ rfs []
    \\ every_case_tac \\ fs[]
    \\ CCONTR_TAC \\ fs[]
    \\ rveq
    \\ fs[result_rel_cases]
    \\ fs[s_rel_cases]
    \\ last_x_assum(qspec_then`k`mp_tac)
    \\ simp[]
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
    \\ drule (GEN_ALL compile_decs_correct)
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ `r ≠ Rerr (Rabort Rtype_error)`
       by (first_x_assum(qspecl_then[`k`,`st'.ffi`]strip_assume_tac)
          \\ rfs [])
    \\ disch_then drule \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `compile_prog e _ = _`
    \\ disch_then (qspecl_then [ `SND (compile_prog e prog)`
                               , `FST (compile_prog e prog)`] mp_tac)
    \\ impl_tac >- (UNABBREV_ALL_TAC >> fs[])
    \\ `e = c`  by (UNABBREV_ALL_TAC >> rw [config_component_equality])
    \\ fs [initial_state_def] \\ rfs []
    \\ qmatch_goalsub_abbrev_tac`flatSem$evaluate_decs env2'`
    \\ `env2' = initial_env F T`
    by ( unabbrev_all_tac \\ rw[environment_component_equality,initial_env_def])
    \\ rveq
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

open flat_uncheck_ctorsProofTheory flat_elimProofTheory
     flat_exh_matchProofTheory flat_reorder_matchProofTheory

val _ = set_grammar_ancestry
  (["flat_uncheck_ctorsProof", "flat_elimProof",
    "flat_exh_matchProof", "flat_reorder_matchProof"]
   @ grammar_ancestry);

Theorem compile_decs_tidx_thm:
   !n1 next1 env1 ds1 n2 next2 env2 ds2.
   compile_decs n1 next1 env1 ds1 = (n2, next2, env2, ds2)
   ==>
   ALL_DISTINCT (get_tdecs ds2) /\
   EVERY (\d. !t s. d = Dtype t s ==> next1.tidx <= t /\ t < next2.tidx) ds2 /\
   (next1.tidx = next2.tidx <=> get_tdecs ds2 = [])
Proof
  ho_match_mp_tac compile_decs_ind
  \\ rw [compile_decs_def] \\ fs [get_tdecs_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [FILTER_APPEND, ALL_DISTINCT_APPEND, compile_exp_def,
         MAPi_enumerate_MAP, FILTER_MAP, MAP_MAP_o, o_DEF, UNCURRY,
         EVERY_MEM, MEM_MAPi] \\ rw []
  \\ fs [MAP_enumerate_MAPi, LAMBDA_PROD]
  >-
   (rename1 `_ + x`
    \\ map_every qid_spec_tac [`x`,`type_def`]
    \\ Induct \\ rw [MEM_MAPi]
    \\ fs [ELIM_UNCURRY, o_DEF, ADD1]
    \\ first_x_assum (qspec_then `x + 1` assume_tac)
    \\ once_rewrite_tac [DECIDE ``x + (n + 1) = n + (x + 1n)``] \\ fs [])
  >-
   (rename1 `_ + x`
    \\ map_every qid_spec_tac [`x`,`type_def`]
    \\ Induct \\ rw [miscTheory.enumerate_def])
  \\ fs [GSYM get_tdecs_def]
  \\ imp_res_tac get_tdecs_MEM \\ fs []
  \\ res_tac \\ fs []
  \\ imp_res_tac compile_decs_num_bindings \\ fs []
  \\ TRY (eq_tac \\ rw [] \\ fs [])
  \\
   (strip_tac
    \\ imp_res_tac get_tdecs_MEM \\ fs []
    \\ res_tac \\ fs [])
QED

Theorem compile_flat_correct:
   EVERY (is_new_type init_ctors) prog /\
   ALL_DISTINCT (get_tdecs prog) /\
   semantics F T ffi prog <> Fail
   ==>
   semantics F T ffi prog = semantics T F ffi (compile_flat prog)
Proof
  rw [compile_flat_def]
  \\ metis_tac [flat_uncheck_ctorsProofTheory.compile_decs_semantics,
                flat_elimProofTheory.flat_remove_semantics,
                flat_reorder_matchProofTheory.compile_decs_semantics,
                flat_exh_matchProofTheory.compile_decs_semantics]
QED

Theorem compile_semantics:
   source_to_flatProof$precondition s env c ⇒
   ¬semantics_prog s env prog Fail ⇒
   semantics_prog s env prog (semantics T F s.ffi (SND (compile c prog)))
Proof
  rw [compile_def] \\ pairarg_tac \\ fs []
  \\ imp_res_tac compile_prog_correct \\ rfs []
  \\ `semantics F T s.ffi p' <> Fail` by (CCONTR_TAC \\ fs [])
  \\ `semantics F T s.ffi p' = semantics T F s.ffi (compile_flat p')`
    suffices_by (rw []\\ fs [])
  \\ match_mp_tac compile_flat_correct \\ fs []
  \\ fs [compile_prog_def]
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ imp_res_tac compile_decs_tidx_thm
  \\ fs [glob_alloc_def, get_tdecs_def]
  \\ fs [GSYM glob_alloc_def, GSYM get_tdecs_def]
  \\ rw [EVERY_MEM, is_new_type_def]
  \\ strip_tac
  \\ `tid <> 0 ==> tid = 1`
    by fs [flat_exh_matchTheory.init_ctors_def, FDOM_FUPDATE_LIST]
  \\ `c.next.tidx > 1`
    by (fs [precondition_def, invariant_def]
        \\ qhdtm_x_assum `source_to_flatProof$genv_c_ok` mp_tac
        \\ qpat_x_assum `!x.!y.!z._ ==> _` mp_tac
        \\ qpat_x_assum `FDOM _ = _` mp_tac
        \\ EVAL_TAC \\ fs [flookup_thm] \\ rw []
        \\ CCONTR_TAC \\ fs [])
  \\ fs [glob_alloc_def, EVERY_MEM]
  \\ res_tac \\ fs []
QED

(* - esgc_free theorems for compile_exp ------------------------------------ *)

Theorem compile_exp_esgc_free:
   (!tra env exp.
      nsAll (\_ v. esgc_free v /\ set_globals v = {||}) env.v
      ==>
      esgc_free (compile_exp tra env exp) /\
      set_globals (compile_exp tra env exp) = {||}) /\
   (!tra env exps.
      nsAll (\_ v. esgc_free v /\ set_globals v = {||}) env.v
      ==>
      EVERY esgc_free (compile_exps tra env exps) /\
      elist_globals (compile_exps tra env exps) = {||}) /\
   (!tra env pes.
      nsAll (\_ v. esgc_free v /\ set_globals v = {||}) env.v
      ==>
      EVERY esgc_free (MAP SND (compile_pes tra env pes)) /\
      elist_globals (MAP SND (compile_pes tra env pes)) = {||}) /\
   (!tra env funs.
      nsAll (\_ v. esgc_free v /\ set_globals v = {||}) env.v
      ==>
      EVERY esgc_free (MAP (SND o SND) (compile_funs tra env funs)) /\
      elist_globals (MAP (SND o SND) (compile_funs tra env funs)) = {||})
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ fs [compile_exp_def]
  >-
   (PURE_FULL_CASE_TAC \\ fs []
    \\ imp_res_tac nsLookup_nsAll \\ fs [])
  \\ fs [nsAll_nsBind]
  >-
   (IF_CASES_TAC \\ fs []
    \\ fs [elist_globals_eq_empty, EVERY_MEM]
    \\ fs [FOLDR_REVERSE, FOLDL_invariant, EVERY_MEM]
    >-
     (FOLDL_invariant |> Q.ISPECL [`\x. set_globals x = {||}`]
      |> BETA_RULE |> match_mp_tac
      \\ fs [op_gbag_def])
    \\ Cases_on `op` \\ fs [op_gbag_def, astOp_to_flatOp_def])
  >-
   (Cases_on `lop` \\ fs []
    \\ res_tac \\ fs []
    \\ EVAL_TAC)
  >-
   (rfs []
    \\ last_x_assum mp_tac \\ impl_tac \\ rw []
    \\ last_x_assum mp_tac \\ impl_tac \\ rw []
    \\ qhdtm_x_assum `nsAll` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ EVAL_TAC
    \\ rename1 `FOLDR _ b (MAP _ xs)`
    \\ qid_spec_tac `b`
    \\ Induct_on `xs` \\ rw []
    \\ Cases_on `id` \\ Cases_on `h = n`
    \\ fs [nsLookup_nsBind] \\ rw []
    \\ metis_tac [])
  \\ last_x_assum irule
  \\ pop_assum mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ qid_spec_tac `env`
  \\ rename1 `pat_tups tra ps`
  \\ qid_spec_tac `ps`
  \\ Induct \\ rw [pat_tups_def, namespaceTheory.nsBindList_def]
  \\ last_x_assum drule
  \\ fs [namespaceTheory.nsBindList_def, nsAll_nsBind]
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

Theorem alloc_defs_set_globals:
   !xs n next. elist_globals (MAP SND (alloc_defs n next xs)) = {||}
Proof
  Induct \\ rw [alloc_defs_def, op_gbag_def]
QED

Theorem alloc_defs_esgc_free:
   !xs n next. EVERY esgc_free (MAP SND (alloc_defs n next xs))
Proof
  Induct \\ rw [alloc_defs_def, op_gbag_def]
QED

Theorem nsAll_extend_env:
   nsAll P e1.v /\ nsAll P e2.v ==> nsAll P (extend_env e1 e2).v
Proof
  simp [extend_env_def, nsAll_nsAppend]
QED

Theorem compile_decs_esgc_free:
   !n next env decs n1 next1 env1 decs1.
     nsAll (\_ v. esgc_free v /\ set_globals v = {||}) env.v /\
     compile_decs n next env decs = (n1, next1, env1, decs1)
     ==>
     EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet decs1)) /\
     nsAll (\_ v. esgc_free v /\ set_globals v = {||}) env1.v
Proof
  ho_match_mp_tac compile_decs_ind
  \\ rw [compile_decs_def]
  \\ fs [compile_exp_esgc_free, make_varls_esgc_free]
  \\ fs [EVERY_MAP, EVERY_FILTER, MAP_FILTER]
  \\ simp [EVERY_MEM, MEM_MAPi, PULL_EXISTS, UNCURRY]
  \\ TRY
   (irule nsAll_alist_to_ns
    \\ fs [ELIM_UNCURRY]
    \\ ho_match_mp_tac
      (EVERY_CONJ |> REWRITE_RULE [EQ_IMP_THM] |> SPEC_ALL |> CONJUNCT2)
    \\ conj_tac
    >- simp [GSYM EVERY_MAP, alloc_defs_esgc_free]
    \\ qmatch_goalsub_abbrev_tac `EVERY _ xs`
    \\ `EVERY (\x. set_globals x = {||}) (MAP SND xs)`
        suffices_by rw [EVERY_MAP]
    \\ simp [EVERY_MEM, GSYM elist_globals_eq_empty, Abbr`xs`,
             alloc_defs_set_globals]
    \\ NO_TAC)
  >- fs [compile_exp_def]
  >-
   (ho_match_mp_tac (EVERY_EL |> REWRITE_RULE [EQ_IMP_THM]
                     |> SPEC_ALL |> CONJUNCT1)
    \\ qmatch_goalsub_abbrev_tac `extend_env env2`
    \\ qmatch_asmsub_abbrev_tac `nsAll P`
    \\ `nsAll P (extend_env env2 env).v`
      by (irule nsAll_extend_env
          \\ fs [Abbr `env2`, Abbr `P`]
          \\ irule nsAll_alist_to_ns
          \\ fs [alloc_defs_append]
          \\ simp [EVERY_CONJ, ELIM_UNCURRY]
          \\ simp [GSYM EVERY_MAP]
          \\ fs [alloc_defs_esgc_free]
          \\ conj_tac
          \\ qmatch_goalsub_abbrev_tac `EVERY _ xs`
          \\ `EVERY (\x. set_globals x = {||}) (MAP SND xs)`
              suffices_by rw [EVERY_MAP]
          \\ simp [EVERY_MEM, GSYM elist_globals_eq_empty, Abbr`xs`,
                   alloc_defs_set_globals])
    \\ simp [EVERY_MEM]
    \\ simp [compile_funs_map]
    \\ rw [MEM_MAP, PULL_EXISTS, UNCURRY]
    \\ qmatch_goalsub_abbrev_tac `compile_exp _ env3`
    \\ `nsAll P env3.v` by fs [Abbr `P`, Abbr `env3`, nsAll_nsBind]
    \\ fs [compile_exp_esgc_free])
  \\ fs [empty_env_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [EVERY_MEM, lift_env_def]
  \\ last_x_assum mp_tac
  \\ impl_tac \\ rw []
  \\ irule nsAll_extend_env \\ fs []
QED

(* - the source_to_flat compiler produces things which are esgc_free ------- *)

Theorem compile_prog_esgc_free:
   nsAll (\_ v. esgc_free v /\ set_globals v = {||}) c.mod_env.v /\
   compile_prog c p = (c1, p1)
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet p1))
Proof
  rw [compile_prog_def]
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ fs [glob_alloc_def]
  \\ metis_tac [compile_decs_esgc_free]
QED

Theorem compile_flat_esgc_free:
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (compile_flat ds)))
Proof
  rw [compile_flat_def, flat_exh_matchTheory.compile_def]
  \\ drule flat_exh_matchProofTheory.compile_decs_esgc_free
  \\ disch_then (qspec_then `init_ctors` mp_tac) \\ rw []
  \\ drule flat_elimProofTheory.remove_flat_prog_esgc_free \\ rw []
  \\ rename1 `compile_decs (compile_decs ds1)`
  \\ irule flat_reorder_matchProofTheory.compile_decs_esgc_free
  \\ irule flat_uncheck_ctorsProofTheory.compile_decs_esgc_free
  \\ rw[]
QED

Theorem compile_esgc_free:
   nsAll (\_ v. esgc_free v /\ set_globals v = {||}) c.mod_env.v /\
   compile c p = (c1, p1)
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet p1))
Proof
  rw [compile_def]
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ metis_tac [compile_prog_esgc_free, compile_flat_esgc_free]
QED

val mem_size_lemma = Q.prove ( `list_size sz xs < N ==> (MEM x xs ⇒ sz x < N)`,
  Induct_on `xs` \\ rw [list_size_def] \\ fs []);

val num_bindings_def = tDefine"num_bindings"
  `(num_bindings (Dlet _ p _) = LENGTH (pat_bindings p [])) ∧
   (num_bindings (Dletrec _ f) = LENGTH f) ∧
   (num_bindings (Dmod _ ds) = SUM (MAP num_bindings ds)) ∧
   (num_bindings (Dlocal lds ds) = SUM (MAP num_bindings lds)
        + SUM (MAP num_bindings ds)) ∧
   (num_bindings _ = 0)`
(wf_rel_tac`measure dec_size`
  \\ fs [terminationTheory.dec1_size_eq]
  \\ rpt (match_mp_tac mem_size_lemma ORELSE strip_tac)
  \\ fs []);

val _ = export_rewrites["num_bindings_def"];

Theorem compile_decs_num_bindings:
   ∀n next env ds e f g p. compile_decs n next env ds = (e,f,g,p) ⇒
   next.vidx ≤ f.vidx ∧
   SUM (MAP num_bindings ds) = f.vidx - next.vidx
Proof
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ rw[]
  \\ pairarg_tac \\ fsrw_tac[ETA_ss][]
  \\ pairarg_tac \\ fs[] \\ rw[]
QED

val COUNT_LIST_ADD_SYM = COUNT_LIST_ADD
  |> CONV_RULE (SIMP_CONV bool_ss [Once ADD_SYM]);

Theorem compile_decs_elist_globals:
   ∀n next env ds e f g p.
   compile_decs n next env ds = (e,f,g,p) ∧
   nsAll (λ_ v. esgc_free v ∧ set_globals v = {||}) env.v ⇒
   elist_globals (MAP dest_Dlet (FILTER is_Dlet p)) =
     LIST_TO_BAG (MAP ((+) next.vidx) (COUNT_LIST (SUM (MAP num_bindings ds))))
Proof
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ rw[set_globals_make_varls]
  \\ rw[compile_exp_esgc_free]
  \\ TRY ( EVAL_TAC \\ rw [EL_BAG] \\ NO_TAC )
  >- (
    qmatch_goalsub_abbrev_tac`FILTER P (MAPi f ls)`
    \\ qmatch_asmsub_abbrev_tac`compile_funs _ _ ll`
    \\ Q.ISPECL_THEN[`P`,`ls`,`f`]mp_tac(Q.GEN`P` FILTER_MAPi_ID)
    \\ simp[Abbr`P`, Abbr`f`, UNCURRY]
    \\ disch_then kall_tac
    \\ simp[o_DEF, UNCURRY]
    \\ qmatch_goalsub_abbrev_tac`COUNT_LIST l`
    \\ `l = LENGTH ls` by simp[Abbr`ls`, Abbr`l`,source_to_flatTheory.compile_funs_map,Abbr`ll`]
    \\ qmatch_goalsub_abbrev_tac`MAPi f ls`
    \\ `∀n. n < LENGTH ls ⇒ set_globals (EL n (MAPi f ls)) = {|next.vidx + n|}`
    by (
      simp[Abbr`f`, EL_MAPi]
      \\ EVAL_TAC
      \\ qx_gen_tac`m`
      \\ strip_tac
      \\ `set_globals (SND(SND(EL m ls))) = {||}` suffices_by simp[]
      \\ fs[Abbr`ls`, source_to_flatTheory.compile_funs_map]
      \\ simp[EL_MAP]
      \\ simp[UNCURRY]
      \\ qmatch_goalsub_abbrev_tac`compile_exp tra venv exp`
      \\ qspecl_then[`tra`,`venv`,`exp`]mp_tac (CONJUNCT1 compile_exp_esgc_free)
      \\ impl_tac
      >- (
        rw[Abbr`venv`]
        \\ irule namespacePropsTheory.nsAll_nsBind
        \\ rw[source_to_flatTheory.extend_env_def]
        \\ irule namespacePropsTheory.nsAll_nsAppend
        \\ rw[]
        \\ irule namespacePropsTheory.nsAll_alist_to_ns
        \\ simp[UNCURRY]
        \\ qmatch_goalsub_abbrev_tac`alloc_defs n v l`
        \\ Q.ISPECL_THEN[`l`,`n`,`v`] mp_tac alloc_defs_set_globals
        \\ simp[flatPropsTheory.elist_globals_eq_empty]
        \\ simp[EVERY_MEM, UNCURRY]
        \\ simp[MEM_MAP, PULL_EXISTS]
        \\ Q.ISPECL_THEN[`l`,`n`,`v`] mp_tac alloc_defs_esgc_free
        \\ simp[EVERY_MEM, UNCURRY]
        \\ simp[MEM_MAP, PULL_EXISTS] )
      \\ rw[] )
    \\ qhdtm_x_assum`Abbrev`kall_tac
    \\ qhdtm_x_assum`Abbrev`kall_tac
    \\ rw[]
    \\ pop_assum mp_tac
    \\ `LENGTH (MAPi f ls) = LENGTH ls` by simp[]
    \\ pop_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qspec_tac(`next.vidx`,`b`)
    \\ qspec_tac(`MAPi f ls`,`l1`)
    \\ Induct_on`ls` \\ simp[]
    >- (EVAL_TAC \\ rw[])
    \\ simp[o_DEF] \\ rw[ADD1]
    \\ Cases_on`l1` \\ fs[]
    \\ last_x_assum(qspecl_then[`t`,`b+1`]mp_tac)
    \\ impl_tac >- ( fs[ADD1] )
    \\ impl_tac >- (
      rw[]
      \\ first_x_assum(qspec_then`SUC n`mp_tac)
      \\ rw[] )
    \\ rw[COUNT_LIST_ADD_SYM]
    \\ simp[MAP_MAP_o, o_DEF]
    \\ rw[LIST_TO_BAG_APPEND]
    \\ simp[EVAL``COUNT_LIST 1``]
    \\ rw[LIST_TO_BAG_def]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ rw[]
    \\ AP_TERM_TAC
    \\ simp[MAP_EQ_f])
  >- (
    simp[MAPi_enumerate_MAP, FILTER_MAP, o_DEF, UNCURRY]
    \\ EVAL_TAC )
  >- (
    pairarg_tac \\ fs[] \\ rveq
    \\ srw_tac[ETA_ss][] )
  >- (
    pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ rveq
    \\ simp [flatPropsTheory.elist_globals_append, FILTER_APPEND]
    \\ drule compile_decs_esgc_free
    \\ disch_then drule
    \\ strip_tac
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac
    >- (
      simp[extend_env_def]
      \\ irule namespacePropsTheory.nsAll_nsAppend
      \\ simp[] )
    \\ rw []
    \\ imp_res_tac compile_decs_num_bindings
    \\ rw [COUNT_LIST_ADD_SYM]
    \\ srw_tac [ETA_ss] [LIST_TO_BAG_APPEND, MAP_MAP_o, o_DEF]
    \\ AP_TERM_TAC
    \\ simp [MAP_EQ_f]
  )
  >- (
    pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ rveq
    \\ simp[flatPropsTheory.elist_globals_append, FILTER_APPEND]
    \\ drule compile_decs_esgc_free
    \\ disch_then drule
    \\ strip_tac
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac
    >- (
      simp[extend_env_def]
      \\ irule namespacePropsTheory.nsAll_nsAppend
      \\ simp[] )
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

val _ = export_theory ();
