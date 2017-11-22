open preamble;
open namespacePropsTheory semanticPrimitivesTheory semanticPrimitivesPropsTheory;
open source_to_modTheory modLangTheory modSemTheory modPropsTheory;

val _ = new_theory "source_to_modProof";

val compile_exps_length = Q.prove (
  `LENGTH (compile_exps t m es) = LENGTH es`,
  induct_on `es` >>
  rw [compile_exp_def]);

val mapi_map = Q.store_thm ("mapi_map",
  `!f g l. MAPi f (MAP g l) = MAPi (\i x. f i (g x)) l`,
  Induct_on `l` >>
  rw [combinTheory.o_DEF]);

(* value relation *)


(* bind locals with an arbitrary trace *)
val bind_locals_def = Define `
  bind_locals ts locals comp_map =
    nsBindList (MAP2 (\t x. (x, modLang$Var_local t x)) ts locals) comp_map`;

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
    <| v : modSem$v option list; c : (ctor_id # type_id) # num |-> stamp |>`;

val has_bools_def = Define `
  has_bools genv ⇔
    FLOOKUP genv ((1n, SOME bool_id), 0n) = SOME (TypeStamp "true" bool_type_num) ∧
    FLOOKUP genv ((0, SOME bool_id), 0n) = SOME (TypeStamp "false" bool_type_num)`;

val has_lists_def = Define `
  has_lists genv ⇔
    FLOOKUP genv ((cons_id, SOME list_id), 2n) = SOME (TypeStamp "::" list_type_num) ∧
    FLOOKUP genv ((nil_id, SOME list_id), 0n) = SOME (TypeStamp "nil" list_type_num)`;

val has_exns_def = Define `
  has_exns genv ⇔
    FLOOKUP genv ((div_id, NONE), 0n) = SOME div_stamp ∧
    FLOOKUP genv ((chr_id, NONE), 0n) = SOME chr_stamp ∧
    FLOOKUP genv ((subscript_id, NONE), 0n) = SOME subscript_stamp ∧
    FLOOKUP genv ((bind_id, NONE), 0n) = SOME bind_stamp`;

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
    v_rel genv ((Litv lit):semanticPrimitives$v) ((Litv lit):modSem$v)) ∧
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

val v_rel_eqns = Q.store_thm ("v_rel_eqns",
  `(!genv l v.
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
          FLOOKUP genv.c (cn,arity) = SOME stamp))`,
  srw_tac[][semanticPrimitivesTheory.Boolv_def,modSemTheory.Boolv_def] >>
  srw_tac[][Once v_rel_cases] >>
  srw_tac[][Q.SPECL[`genv`,`nsEmpty`](CONJUNCT1(CONJUNCT2 v_rel_cases))] >>
  every_case_tac >>
  fs [genv_c_ok_def, has_bools_def] >>
  TRY eq_tac >>
  rw [] >>
  metis_tac []);

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
    s.next_type_stamp = s'.next_type_id ∧
    s.next_exn_stamp = s'.next_exn_id ∧
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
  rw [terminationTheory.do_eq_def, modSemTheory.do_eq_def, v_rel_eqns] >>
  rw [terminationTheory.do_eq_def, modSemTheory.do_eq_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH >>
  rw [] >>
  fs [] >>
  TRY (
    rpt (qpat_x_assum `v_rel _ (Closure _ _ _) _` mp_tac >>
         simp [Once v_rel_cases]) >>
    rpt (qpat_x_assum `v_rel _ (Recclosure _ _ _) _` mp_tac >>
         simp [Once v_rel_cases]) >>
    rw [] >>
    rw [modSemTheory.do_eq_def] >>
    NO_TAC) >>
  fs [modSemTheory.ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  fs [genv_c_ok_def, modSemTheory.ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def] >>
  metis_tac [eq_result_11, eq_result_distinct]);

  (*
val do_con_check = Q.prove (
  `!genv comp_map env cn es env_i1 locals t1 ts.
    do_con_check env.c cn (LENGTH es) ∧
    env_all_rel genv comp_map env env_i1 locals
    ⇒
    do_con_check env_i1.c cn (LENGTH (compile_exps t1 (bind_locals ts locals comp_map) es))`,
  srw_tac[][do_con_check_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[env_all_rel_cases] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  ntac 3 (pop_assum (fn _ => all_tac)) >>
  induct_on `es` >>
  srw_tac[][compile_exp_def]);
  *)

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
  full_simp_tac(srw_ss())[v_rel_eqns, modSemTheory.v_to_char_list_def,
                          genv_c_ok_def, has_lists_def] >>
  rw []
  >- (
    `cn2 = (nil_id,SOME list_id)` by metis_tac [] >>
    rw [modSemTheory.v_to_char_list_def])
  >- (
    `cn2 = (cons_id,SOME list_id)` by metis_tac [] >>
    rw [modSemTheory.v_to_char_list_def]));

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
  full_simp_tac(srw_ss())[v_rel_eqns, modSemTheory.v_to_list_def] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[has_lists_def, genv_c_ok_def, v_rel_eqns, modSemTheory.v_to_list_def] >>
  srw_tac[][]
  >- (
    `cn2 = (nil_id,SOME list_id)` by metis_tac [] >>
    rw [v_to_list_def])
  >- (
    `cn2 = (cons_id,SOME list_id)` by metis_tac [] >>
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
  rw [semanticPrimitivesTheory.div_exn_v_def, modSemTheory.div_exn_v_def,
      semanticPrimitivesTheory.chr_exn_v_def, modSemTheory.chr_exn_v_def,
      semanticPrimitivesTheory.bind_exn_v_def, modSemTheory.bind_exn_v_def,
      semanticPrimitivesTheory.sub_exn_v_def, modSemTheory.subscript_exn_v_def,
      v_rel_eqns, genv_c_ok_def, has_exns_def, has_bools_def,
      semanticPrimitivesTheory.Boolv_def, modSemTheory.Boolv_def] >>
  every_case_tac >>
  simp [v_rel_eqns]);

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
       do_app s1_i1 (astOp_to_modOp op) vs_i1 = SOME (s2_i1, r_i1)`,
  rpt gen_tac >>
  Cases_on `s1` >>
  Cases_on `s1_i1` >>
  Cases_on `op = ConfigGC` >-
     (simp [astOp_to_modOp_def] >>
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases]) >>
  pop_assum mp_tac >>
  Cases_on `op` >>
  simp [astOp_to_modOp_def]
  >- ((* Opn *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opb *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opw *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases,v_rel_lems]
      \\ Cases_on`o'` \\ fs[opw8_lookup_def,opw64_lookup_def])
  >- ((* Shift *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      TRY (rename1 `shift8_lookup s11 w11 n11`) >>
      TRY (rename1 `shift64_lookup s11 w11 n11`) >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems]
      \\ Cases_on`w11` \\ Cases_on`s11` \\ fs[shift8_lookup_def,shift64_lookup_def])
  >- ((* Equality *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [Boolv_11, do_eq, eq_result_11, eq_result_distinct, v_rel_lems])
  >- ( (*FP_cmp *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ( (*FP_uop *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ( (*FP_bop *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      fs[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opapp *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Opassign *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_assign_def,store_v_same_type_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >-
      metis_tac [EVERY2_LUPDATE_same, sv_rel_rules] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN,sv_rel_cases] >>
      srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> res_tac >> full_simp_tac(srw_ss())[])
  >- ((* Opref *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Opderef *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
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
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >- ((* Aw8sub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
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
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
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
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
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
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* WordToInt *)
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* CopyStrStr *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases]
    \\ simp[v_rel_lems,v_rel_eqns])
  >- ((* CopyStrAw8 *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
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
    rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,v_rel_lems,v_rel_eqns])
  >- ((* CopyAw8Aw8 *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
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
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases,v_rel_lems])
  >- ((* Chr *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Chopb *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Implode *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      imp_res_tac v_to_char_list >>
      srw_tac[][])
  >- ((* Strsub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_eqns] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[stringTheory.IMPLODE_EXPLODE_I, v_rel_lems])
  >- ((* Strlen *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems])
  >- ((* Strcat *)
    rw[semanticPrimitivesPropsTheory.do_app_cases,modSemTheory.do_app_def]
    \\ fs[LIST_REL_def]
    \\ imp_res_tac v_to_list \\ fs[]
    \\ imp_res_tac vs_to_string \\ fs[result_rel_cases,v_rel_eqns] )
  >- ((* VfromList *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_eqns] >>
      imp_res_tac v_to_list >>
      srw_tac[][])
  >- ((* Vsub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ, v_rel_lems])
  >- ((* Vlength *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Aalloc *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases, LIST_REL_REPLICATE_same] >>
      metis_tac [LIST_REL_LENGTH, v_rel_lems])
  >- ((* Asub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
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
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[store_lookup_def, sv_rel_cases] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      res_tac >>
      full_simp_tac(srw_ss())[sv_rel_cases] >>
      metis_tac [store_v_distinct, store_v_11, LIST_REL_LENGTH])
  >- ((* Aupdate *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
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
  >- ((* FFI *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, v_rel_lems] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def, IMPLODE_EXPLODE_I] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[]));

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
       modSem$do_opapp vs_i1 = SOME (env_i1, compile_exp t1 (comp_map with v := bind_locals ts locals comp_map.v) e)`,
   srw_tac[][do_opapp_cases, modSemTheory.do_opapp_def] >>
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
         rw [sem_env_component_equality, modSemTheory.environment_component_equality] >>
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

             (*
val build_conv = Q.prove (
  `!genv comp_map env cn vs v vs' env_i1 locals.
    build_conv env.c cn vs = SOME v ∧
    env_all_rel genv comp_map env env_i1 locals ∧
    LIST_REL (v_rel genv) vs vs'
    ⇒
    ∃v'.
      v_rel genv v v' ∧
      build_conv env_i1.c cn vs' = SOME v'`,
  srw_tac[][semanticPrimitivesTheory.build_conv_def, modSemTheory.build_conv_def] >>
  every_case_tac >>
  srw_tac[][Once v_rel_cases] >>
  full_simp_tac(srw_ss())[env_all_rel_cases] >> rev_full_simp_tac(srw_ss())[]);
  *)

val pat_bindings_compile_pat = Q.store_thm ("pat_bindings_compile_pat[simp]",
`!comp_map (p:ast$pat) vars. pat_bindings (compile_pat comp_map p) vars = pat_bindings p vars`,
  ho_match_mp_tac compile_pat_ind >>
  simp [compile_pat_def, astTheory.pat_bindings_def, pat_bindings_def] >>
  induct_on `ps` >>
  rw [] >>
  fs [pat_bindings_def,astTheory.pat_bindings_def, PULL_FORALL]);

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
      modSem$pmatch <| v := genv_v; c := FDOM genv.c; exh_pat := F; check_ctor := T |> s_i1 (compile_pat comp_map p) v_i1 env_i1 = r_i1 ∧
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
  srw_tac[][terminationTheory.pmatch_def, modSemTheory.pmatch_def, compile_pat_def] >>
  full_simp_tac(srw_ss())[match_result_rel_def, modSemTheory.pmatch_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH
  >> TRY (full_simp_tac(srw_ss())[Once v_rel_cases] >>
          srw_tac[][modSemTheory.pmatch_def, match_result_rel_def] >>
          FAIL_TAC "")
  >- (
    every_case_tac >>
    full_simp_tac(srw_ss())[match_result_rel_def] >>
    last_assum drule >>
    strip_tac >>
    rw [] >>
    rw [pmatch_def, eta2, match_result_rel_def] >>
    fs [semanticPrimitivesTheory.same_ctor_def,FDOM_FLOOKUP] >>
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
  `env with v updated_by (λy. y) = (env : modSem$environment)`,
  rw [environment_component_equality]);

val evaluate_foldr_let_err = Q.prove (
  `!env s s' exps e x.
    modSem$evaluate env s exps = (s', Rerr x)
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
  ``modSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
  |> type_subst[alpha |-> ``:'ffi``]);

  (*
val do_app_subglobals = Q.prove (
  `!s op vs s' r.
    modSem$do_app s op vs = SOME (s',r)
    ⇒
    subglobals s.globals s'.globals`,
  cheat);

val evaluate_subglobals = Q.prove (
  `(∀env ^s1 es res.
    modSem$evaluate env s es = res ⇒
    !s' r.
      res = (s',r) ⇒ subglobals s.globals s'.globals) ∧
   (∀env ^s1 v pes err_v res.
    modSem$evaluate_match env s v pes err_v = res ⇒
    !s' r.
      res = (s',r) ⇒ subglobals s.globals s'.globals)`,
  ho_match_mp_tac evaluate_ind >>
  rw [evaluate_def] >>
  rw [subglobals_refl] >>
  every_case_tac >>
  fs [subglobals_def] >>
  rfs []
  >- metis_tac [LESS_LESS_EQ_TRANS]
  >- metis_tac [LESS_LESS_EQ_TRANS]
  >- metis_tac [LESS_LESS_EQ_TRANS]
  >- (
    fs [do_opapp_def, dec_clock_def] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    metis_tac [LESS_LESS_EQ_TRANS])
  >- (
    imp_res_tac do_app_subglobals >>
    fs [subglobals_def] >>
    metis_tac [LESS_LESS_EQ_TRANS]) >>
  metis_tac [LESS_LESS_EQ_TRANS]);
  *)

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
         modSem$evaluate env_i1 s_i1 es_i1 = (s'_i1, r_i1) ∧
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
         modSem$evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 = (s'_i1, r_i1) ∧
         s_i1.globals = s'_i1.globals)`,
  ho_match_mp_tac terminationTheory.evaluate_ind >>
  srw_tac[][terminationTheory.evaluate_def, modSemTheory.evaluate_def,compile_exp_def] >>
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
      fs [EVERY2_REVERSE])
    >- (
      every_case_tac >>
      fs [result_rel_cases] >>
      res_tac >>
      fs [] >>
      rw [])
    >- (
      fs [result_rel_cases, PULL_EXISTS] >>
      rw [v_rel_eqns] >>
      rename [`nsLookup comp_map.c x`] >>
      Cases_on `nsLookup comp_map.c x` >>
      fs [modSemTheory.evaluate_def , result_rel_cases, env_all_rel_cases,
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
      rw [evaluate_def, modSemTheory.do_app_def] >>
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
        simp [evaluate_def, astOp_to_modOp_def] >>
        fs [s_rel_cases] >>
        first_x_assum (qspecl_then [`genv with v := s'_i1.globals`, `REVERSE v'`] mp_tac) >>
        rw [EVERY2_REVERSE] >>
        rw [])
      >- (
        rw [evaluate_def, astOp_to_modOp_def] >>
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
    `astOp_to_modOp op ≠ Opapp`
    by (
      rw [astOp_to_modOp_def] >>
      Cases_on `op` >>
      simp [] >>
      fs []) >>
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
          Boolv_def, opb_lookup_def, state_component_equality] >>
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
        `<|v := env'.v; c := env'.c|> = env'` by rw [sem_env_component_equality] >>
        cheat) >>
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
      modSem$evaluate <|c := FDOM genv_c; v := []; exh_pat := F; check_ctor := T |>
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
  by rw [source_to_modTheory.environment_component_equality] >>
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

    (*
val letrec_global_env_lem3 = Q.prove (
  `!funs x genv cenv var_map t tt.
    ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
    MEM x (MAP FST funs)
    ⇒
    ∃n y e' t0 t2 t3.
      ALOOKUP (alloc_defs t (LENGTH genv) (MAP FST (REVERSE funs))) x = SOME (Var_global t0 n) ∧
      n < LENGTH genv + LENGTH funs ∧
      find_recfun x funs = SOME (y,e') ∧
      EL n (genv ++ MAP (λ(p1,p1',p2). SOME (Closure (cenv,[]) p1' (compile_exp tt (nsBind p1' (Var_local tt p1') (nsAppend (alist_to_ns (alloc_defs t (LENGTH genv) (MAP FST (REVERSE funs)))) var_map)) p2))) (REVERSE funs)) = SOME (Closure (cenv,[]) y
                (compile_exp t2 (nsBindList ((y,Var_local t3 y)::alloc_defs t (LENGTH genv) (MAP FST (REVERSE funs))) var_map) e'))`,
  srw_tac[][] >>
  full_simp_tac(srw_ss())[MEM_EL] >>
  srw_tac[][] >>
  MAP_EVERY qexists_tac [`LENGTH genv + LENGTH funs - (n + 1)`, `FST (SND (EL n funs))`, `SND (SND (EL n funs))`]>>
  CONV_TAC (RESORT_EXISTS_CONV (List.rev))>>
  qexists_tac`tt`>>qexists_tac`tt`>>
  simp[GSYM PULL_EXISTS]>>
  rw[EL_APPEND2]
  >- metis_tac [ALOOKUP_alloc_defs_EL]
  >- (srw_tac[][find_recfun_ALOOKUP] >>
      rpt (pop_assum mp_tac) >>
      Q.SPEC_TAC (`n`, `n`) >>
      induct_on `funs` >>
      srw_tac[][] >>
      cases_on `0 < n` >>
      srw_tac[][EL_CONS] >>
      PairCases_on `h` >>
      full_simp_tac(srw_ss())[]
      >- (every_case_tac >>
          full_simp_tac(srw_ss())[] >>
          `PRE n < LENGTH funs` by decide_tac
          >- (full_simp_tac(srw_ss())[MEM_MAP, FST_triple] >>
              FIRST_X_ASSUM (qspecl_then [`EL (PRE n) funs`] mp_tac) >>
              srw_tac[][EL_MAP, EL_MEM])
          >- metis_tac []))
  >- (`LENGTH funs - (n + 1) < LENGTH funs` by decide_tac >>
      `LENGTH funs - (n + 1) < LENGTH (REVERSE funs)` by metis_tac [LENGTH_REVERSE] >>
      srw_tac [ARITH_ss] [EL_MAP, EL_REVERSE] >>
      `PRE (n + 1) = n` by decide_tac >>
      full_simp_tac(srw_ss())[] >>
      `?f x e. EL n funs = (f,x,e)` by metis_tac [pair_CASES] >>
      srw_tac[][] >>
      simp [nsAppend_to_nsBindList] >>
      simp [namespaceTheory.nsBindList_def, MAP_REVERSE]));

val compile_dec_num_bindings = Q.prove(
  `!next mn mods tops d next' tops' d_i1.
    compile_dec next mn mods tops d = (next',tops',d_i1)
    ⇒
    next' = next + dec_to_dummy_env d_i1`,
  srw_tac[][compile_dec_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM] >>
  srw_tac[][dec_to_dummy_env_def, compile_funs_map] >>
  metis_tac []);
  *)

val compile_decs_num_bindings = Q.prove(
  `!n next env ds n' next' env' ds_i1.
    compile_decs n next env ds = (n', next',env',ds_i1)
    ⇒
    next.vidx ≤ next'.vidx ∧
    next.tidx ≤ next'.tidx`,
  ho_match_mp_tac compile_decs_ind >>
  rw [compile_decs_def] >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs []);

val env_domain_eq_def = Define `
  env_domain_eq (var_map : source_to_mod$environment) (env : 'a sem_env)⇔
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

    (*
val make_varls_trace_exists = Q.prove(`
  ∀ls n t.
  ∃tt.
  LENGTH tt = LENGTH ls ∧
  make_varls n t ls = bind_locals_list tt ls`,
  Induct>>fs[bind_locals_list_def,make_varls_def]>>rw[]>>
  pop_assum(qspecl_then[`n+1`,`t`] strip_assume_tac)>>fs[]>>
  qexists_tac`(t ▷ n) :: tt`>>fs[]);
  *)

val reverse_bind_locals_list = Q.prove(`
  ∀ls tt.
  LENGTH ls = LENGTH tt ⇒
  REVERSE (bind_locals_list tt (REVERSE ls)) =
  bind_locals_list (REVERSE tt) ls`,
  simp[bind_locals_list_def,MAP2_MAP,GSYM MAP_REVERSE,REVERSE_ZIP]);

fun spectv v tt = disch_then(qspec_then tt mp_tac o CONV_RULE (RESORT_FORALL_CONV(sort_vars[v])))
val spect = spectv "t"

val invariant_def = Define `
  invariant genv idx s s_i1 ⇔
    genv_c_ok genv.c ∧
    (!n. idx.vidx ≤ n ∧ n < LENGTH genv.v ⇒ EL n genv.v = NONE) ∧
    (!cn t a. t ≥ idx.tidx ⇒ ((cn,SOME t), a) ∉ FDOM genv.c) ∧
    (!cn t. t ≥ s.next_type_stamp ⇒ TypeStamp cn t ∉ FRANGE genv.c) ∧
    genv.v = s_i1.globals ∧
    s_rel genv.c s s_i1`;

val global_env_inv_extend = Q.prove (
  `!pat_env genv pat_env' tt g1 g2.
    env_rel genv (alist_to_ns pat_env) pat_env' ∧
    genv.v = g1 ⧺ REPLICATE (LENGTH (MAP FST pat_env)) NONE ⧺ g2 ∧
    ALL_DISTINCT (MAP FST pat_env)
    ⇒
    global_env_inv
      <|v := g1 ⧺ MAP SOME (REVERSE (MAP SND pat_env')) ++ g2; c := genv.c|>
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

    (*
val alloc_tags_submap = Q.prove (
  `!idx new_cids ctors ns cids.
    alloc_tags idx new_cids ctors = (ns, cids)
    ⇒
    !arity max_tag. lookup arity new_cids = SOME max_tag ⇒
      ?max_tag'. lookup arity cids = SOME max_tag' ∧ max_tag' ≥ max_tag`,
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
  `!idx (ctors :(tvarN, ast_t list) alist) ns cids genv comp_map env s s' new_cids.
   invariant genv idx comp_map env s s' ∧
   alloc_tags idx.tidx new_cids ctors = (ns, cids) ∧
   (!tag arity. ((tag,SOME idx.tidx),arity) ∈ FDOM genv.c ⇒
     (?max_tag. lookup arity new_cids = SOME max_tag ∧ tag < max_tag)) ∧
   ALL_DISTINCT (MAP FST ctors)
   ⇒
   ?genv_c.
     {((idx,SOME s'.next_type_id),arity) |
       arity < LENGTH (toList cids) ∧
       idx < EL arity (toList cids)}
     DIFF
     {((idx,SOME s'.next_type_id),arity) |
       arity < LENGTH (toList new_cids) ∧
       idx < EL arity (toList new_cids)} = FDOM genv_c ∧
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
       (extend_env <| c := ns; v := nsEmpty |> comp_map)
       (extend_dec_env <| v := nsEmpty; c := alist_to_ns (REVERSE (build_constrs s.next_type_stamp ctors)) |> env)
       (s with next_type_stamp updated_by SUC)
       (s' with next_type_id updated_by SUC)`,
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
  >- cheat
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
          `s'.next_type_id ≥ s'.next_type_id` by decide_tac >>
          metis_tac [])
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
          `s'.next_type_id ≥ s'.next_type_id` by decide_tac >>
          metis_tac [])
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
    res_tac >>
    fs [] >>
    rfs [] >>
    simp [GSYM FUNION_ASSOC] >>
    drule (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] (CONJUNCT1 v_rel_weakening2)) >>
    simp [])
  >- (
    pop_assum mp_tac >>
    rw [nsLookup_nsAppend_some]
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
       fs [])
    >- (
      fs [nsLookup_alist_to_ns_none, ALOOKUP_NONE] >>
      Cases_on `x = Short cn` >>
      fs [] >>
      `x ∉ nsDom ns'`
      by (
        simp [] >>
        rw [] >>
        CCONTR_TAC >>
        fs [] >>
        fs [MEM_MAP, FORALL_PROD] >>
        rw [] >>
        metis_tac [FST, pair_CASES]) >>
      simp [nsLookup_nsAppend_some] >>
      fs [nsLookup_nsDom, invariant_def, v_rel_eqns] >>
      last_x_assum (qspecl_then [`x`, `arity`, `stamp`] mp_tac) >>
      rw [] >>
      rw []
      >- metis_tac [option_nchotomy]
      >- (
        fs [namespaceTheory.nsDomMod_def, EXTENSION, GSPECIFICATION] >>
        fs [EXISTS_PROD] >>
        metis_tac [option_nchotomy]) >>
      rename1 `FLOOKUP genv.c (cn1,_) = SOME _` >>
      `?tag1 typ1. cn1 = (tag1,typ1)` by metis_tac [pair_CASES] >>
      simp [FLOOKUP_UPDATE, FUNION_FUPDATE_1] >>
      rw []
      >- fs [FLOOKUP_DEF] >>
      simp [FLOOKUP_FUNION] >>
      every_case_tac >>
      rw [] >>
      res_tac >>
      fs [FLOOKUP_DEF] >>
      fs [] >>
      `~(idx.tidx ≥ idx.tidx)` by metis_tac [] >>
      fs []))
  >- (
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    simp [Once FUPDATE_EQ_FUNION] >>
    simp [GSYM FUNION_ASSOC] >>
    res_tac >>
    irule sv_rel_weakening2 >>
    simp []));

val nsAppend_foldl = Q.prove (
  `!l ns ns'.
   nsAppend (FOLDL (λns (l,cids). nsAppend l ns) ns' l) ns
   =
   FOLDL (λns (l,cids). nsAppend l ns) (nsAppend ns' ns) l`,
  Induct_on `l` >>
  rw [] >>
  PairCases_on `h` >>
  rw []);
  *)

val evaluate_make_varls = Q.prove (
  `!n t idx vars g g' s env vals.
    LENGTH g = idx ∧
    s.globals = g ++ REPLICATE (LENGTH vars) NONE ++ g' ∧
    LENGTH vals = LENGTH vars ∧
    (!n. n < LENGTH vals ⇒ ALOOKUP env.v (EL n vars) = SOME (EL n vals))
    ⇒
    modSem$evaluate env s [make_varls n t idx vars] =
    (s with globals := g ++ MAP SOME vals ++ g', Rval [modSem$Conv NONE []])`,
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

val compile_decs_correct' = Q.prove (
  `!s env ds s' r comp_map s_i1 idx idx' comp_map' ds_i1 t t' genv.
    evaluate$evaluate_decs s env ds = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    invariant genv idx s s_i1 ∧
    global_env_inv genv comp_map {} env ∧
    source_to_mod$compile_decs t idx comp_map ds = (t', idx', comp_map', ds_i1) ∧
    idx'.vidx ≤ LENGTH genv.v
    ⇒
    ?(s'_i1:'a modSem$state) genv' cenv' r_i1.
      modSem$evaluate_decs <| c := FDOM genv.c; v := []; exh_pat := F; check_ctor := T |> s_i1 ds_i1 = (s'_i1,cenv',r_i1) ∧
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
      rfs []) >>
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
    rw [modSemTheory.evaluate_decs_def, modSemTheory.evaluate_dec_def,
        modSemTheory.evaluate_def, compile_exp_def, result_rel_cases] >>
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
        imp_res_tac evaluate_state_const >>
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
          `LENGTH (REPLICATE (LENGTH (pat_bindings p [])) (NONE:modSem$v option)) =
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
        >- metis_tac [evaluate_state_const, s_rel_cases]
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
          drule global_env_inv_extend >>
          simp [] >>
          disch_then (qspecl_then [`t+4`, `g1`, `g2`] mp_tac) >>
          simp [] >>
          imp_res_tac env_rel_dom >>
          fs [] >>
          impl_tac
          >- metis_tac [LENGTH_MAP] >>
          rw [MAP_REVERSE])))
    >- ( (* Expression exception *)
      qexists_tac `genv` >>
      rw [] >>
      simp [subglobals_refl, extend_env_def, extend_dec_env_def] >>
      fs [v_rel_eqns] >>
      metis_tac [s_rel_cases, evaluate_state_const])
    >- ( (* Expression abort *)
      qexists_tac `genv` >>
      rw [] >>
      simp [subglobals_refl, extend_env_def, extend_dec_env_def] >>
      metis_tac [s_rel_cases, evaluate_state_const]))


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
      rw [mapi_map, compile_funs_map, LAMBDA_PROD]

      rw [evaluate_decs_def, evaluate_dec_def, compile_funs_map,
          semanticPrimitivesTheory.build_rec_env_def] >>

      qmatch_goalsub_abbrev_tac `_ with globals updated_by (\g. g ++ MAP SOME cls)` >>

      qmatch_goalsub_abbrev_tac `_ with globals updated_by (\g. g ++ MAP SOME cls)` >>
      qexists_tac `<| v := genv.v ++ MAP SOME cls; c := genv.c |>` >>
      fs [invariant_def] >>
      rw []
      >- (
        drule global_env_inv_extend >>
        full_simp_tac std_ss [semanticPrimitivesPropsTheory.build_rec_env_merge,
                              nsAppend_nsEmpty] >>
        qmatch_goalsub_abbrev_tac `extend_dec_env <| v := alist_to_ns pat_env; c := _ |>` >>
        disch_then (qspecl_then [`pat_env`, `ZIP (MAP FST funs, REVERSE cls)`, `t`] mp_tac) >>
        `LENGTH funs = LENGTH cls`
        by simp [compile_funs_map, Abbr `cls`, Abbr `pat_env`] >>
        simp [MAP_ZIP] >>
        disch_then irule >>
        rw []
        >- (
          simp [Abbr `pat_env`, MAP_MAP_o, combinTheory.o_DEF] >>
          simp [LAMBDA_PROD]) >>
        rw [env_rel_el]
        >- simp [Abbr `pat_env`] >>
        simp [ZIP_MAP, Abbr `pat_env`] >>
        `n < LENGTH funs` by fs [] >>
        simp [EL_MAP] >>
        simp [EL_ZIP] >>
        `∃f x e. EL n funs = (f,x,e)` by metis_tac [pair_CASES] >>
        simp [LAMBDA_PROD] >>
        simp [Abbr `cls`, MAP_REVERSE, compile_funs_map,
              MAP_MAP_o, combinTheory.o_DEF] >>
        simp [EL_MAP] >>
        simp [Once v_rel_cases] >>
        rw [] >>
        cheat)
      >- (
        fs [s_rel_cases] >>
        irule LIST_REL_mono >>
        qexists_tac `sv_rel <|v := s_i1.globals; c := genv.c|>` >>
        rw [] >>
        drule sv_rel_weakening >>
        rw [])
      >- fs [Abbr `cls`, compile_funs_map]))

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
      metis_tac []) >>
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
    rw [] >>
    first_x_assum drule >>
    rw [] >>
    fs [toList_def, toListA_def] >>
    qpat_x_assum `_ = FDOM _` (mp_tac o GSYM) >>
    rw [] >>
    fs [combinTheory.o_DEF, LAMBDA_PROD] >>
    `s_i1 with
        <|next_type_id := s_i1.next_type_id + 1;
          globals updated_by (λg. g)|> =
        (s_i1 with next_type_id updated_by SUC)`
    by rw [state_component_equality] >>
    fs [] >>
    `!x y. SUC x + y = x + SUC y` by decide_tac >>
    asm_simp_tac std_ss [] >>
    rw [] >>
    qexists_tac `genv'` >>
    rw []
    >- metis_tac [UNION_ASSOC] >>
    fs [extend_env_def, extend_dec_env_def, build_tdefs_def, ADD1, nsAppend_foldl])

  >- ( (* type abbreviation *)
    fs [evaluate_decs_def, evaluate_dec_def] >>
    qexists_tac `genv` >>
    fs [invariant_def, s_rel_cases, v_rel_eqns, extend_dec_env_def, extend_env_def,
        empty_env_def] >>
    metis_tac [])

  >- ( (* exceptions *)
    rw [evaluate_decs_def, evaluate_dec_def] >>
    fs [invariant_def, s_rel_cases, v_rel_eqns, extend_dec_env_def, extend_env_def] >>
    qexists_tac `genv with c := genv.c |+ (((s_i1.next_exn_id,NONE),LENGTH ts), ExnStamp ARB)` >>
    rw []
    >- simp [EXTENSION]
    >- (
      fs [genv_c_ok_def] >>
      rw []
      >- fs [has_bools_def, FLOOKUP_UPDATE]
      >- (
        fs [has_exns_def, FLOOKUP_UPDATE] >>
        cheat)
      >- fs [has_lists_def, FLOOKUP_UPDATE]
      >- (
        fs [FLOOKUP_UPDATE] >>
        every_case_tac >>
        fs [] >>
        rw [ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def, same_type_def] >>
        cheat)
      >- cheat
      >- cheat)
    >- cheat
    >- cheat
    >- cheat
    >- cheat)
  >- ( (* Module *)
    cheat));

    (*
val global_env_inv_extend_mod = Q.prove (
  `!genv new_genv mods tops tops' menv new_env env mn.
    global_env_inv genv mods tops menv ∅ env ∧
    global_env_inv (genv ++ MAP SOME (MAP SND new_genv)) FEMPTY (FEMPTY |++ tops') [] ∅ new_env
    ⇒
    global_env_inv (genv ++ MAP SOME (MAP SND new_genv)) (mods |+ (mn,FEMPTY |++ tops')) tops ((mn,new_env)::menv) ∅ env`,
  srw_tac[][last (CONJUNCTS v_rel_eqns)]
  >- metis_tac [v_rel_weakening] >>
  every_case_tac >>
  srw_tac[][FLOOKUP_UPDATE] >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  res_tac >>
  qexists_tac `map'` >>
  srw_tac[][] >>
  res_tac  >>
  qexists_tac `n` >>
  qexists_tac `v_i1` >>
  srw_tac[][]
  >- decide_tac >>
  metis_tac [v_rel_weakening, EL_APPEND1]);

val global_env_inv_extend_mod_err = Q.prove (
  `!genv new_genv mods tops tops' menv new_env env mn new_genv'.
    mn ∉ set (MAP FST menv) ∧
    global_env_inv genv mods tops menv ∅ env
    ⇒
    global_env_inv (genv ++ MAP SOME (MAP SND new_genv) ++ new_genv')
                   (mods |+ (mn,FEMPTY |++ tops')) tops menv ∅ env`,
  srw_tac[][last (CONJUNCTS v_rel_eqns)]
  >- metis_tac [v_rel_weakening] >>
  srw_tac[][FLOOKUP_UPDATE]
  >- metis_tac [ALOOKUP_MEM, MEM_MAP, pair_CASES, FST] >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  srw_tac[][] >>
  res_tac >>
  srw_tac[][] >>
  res_tac  >>
  qexists_tac `n` >>
  qexists_tac `v_i1` >>
  srw_tac[][]
  >- decide_tac >>
  metis_tac [v_rel_weakening, EL_APPEND1, APPEND_ASSOC]);


val prompt_mods_ok_dec = Q.prove (
  `!l mn var_map d l' var_map' d_i1 t t'.
    compile_dec t l [] var_map d = (t',l',var_map',d_i1)
    ⇒
    prompt_mods_ok NONE [d_i1]`,
  srw_tac[][LET_THM, prompt_mods_ok_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[compile_dec_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM]);

val prompt_mods_ok = Q.prove (
  `!l mn var_map ds l' var_map' ds_i1 t t'.
    compile_decs t l [mn] var_map ds = (t',l',var_map',ds_i1)
    ⇒
    prompt_mods_ok (SOME mn) ds_i1`,
  induct_on `ds` >>
  srw_tac[][LET_THM, compile_decs_def, prompt_mods_ok_def] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[prompt_mods_ok_def] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  srw_tac[][]
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[compile_dec_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LET_THM])
  >- metis_tac []);

val no_dup_types_helper = Q.prove (
  `!next mn  env ds next' env' ds_i1 t t'.
    compile_decs t next mn env ds = (t',next',env',ds_i1) ⇒
    FLAT (MAP (\d. case d of Dtype _ tds => MAP (\(tvs,tn,ctors). tn) tds | _ => []) ds)
    =
    FLAT (MAP (\d. case d of Dtype mn tds => MAP (\(tvs,tn,ctors). tn) tds | _ => []) ds_i1)`,
  induct_on `ds` >>
  srw_tac[][compile_decs_def] >>
  srw_tac[][] >>
  fs [LET_THM] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[compile_dec_def, LET_THM] >>
  srw_tac[][] >>
  metis_tac []);

val no_dup_types = Q.prove(
  `!next mn env ds next' env' ds_i1 t t'.
    compile_decs t next mn env ds = (t',next',env',ds_i1) ∧
    no_dup_types ds
    ⇒
    no_dup_types ds_i1`,
  induct_on `ds` >>
  srw_tac[][compile_decs_def]
  >- full_simp_tac(srw_ss())[semanticPrimitivesTheory.no_dup_types_def, modSemTheory.no_dup_types_def, modSemTheory.decs_to_types_def] >>
  fs [LET_THM] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  srw_tac[][] >>
  res_tac >>
  cases_on `h` >>
  full_simp_tac(srw_ss())[compile_dec_def, LET_THM] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.decs_to_types_def, semanticPrimitivesTheory.no_dup_types_def,
      modSemTheory.decs_to_types_def, modSemTheory.no_dup_types_def, ALL_DISTINCT_APPEND] >>
  srw_tac[][] >>
  metis_tac [no_dup_types_helper]);

val no_dup_types_dec = Q.prove (
  `!next mn env d next' env' d_i1 t t'.
    compile_dec t next mn env d = (t',next',env',d_i1) ∧
    no_dup_types [d]
    ⇒
    no_dup_types [d_i1]`,
  rw [] >>
  irule no_dup_types >>
  qexists_tac `[d]` >>
  rw [compile_decs_def] >>
  qexists_tac `env` >>
  qexists_tac `env'` >>
  qexists_tac `mn` >>
  qexists_tac `next` >>
  qexists_tac `next'` >>
  qexists_tac `t` >>
  simp []);

val compile_decs_dec = Q.prove(
  `compile_dec t next mn env d = (t',x,y,z) ⇒
   compile_decs t next mn env [d] = (t',x,y,[z])`,
  rw[compile_decs_def]);

val compile_top_decs = Q.store_thm("compile_top_decs",
  `compile_top t n env top =
   let (mno,ds) = case top of Tmod mn _ ds => (SOME mn,ds) | Tdec d => (NONE,[d]) in
   let (t',next,new_env,ds) = compile_decs t n (option_fold CONS [] mno) env ds in
   let env = case top of Tmod mn _ _ => nsAppend (nsLift mn new_env) env | _ => nsAppend new_env env in
   (t',next,env,Prompt mno ds)`,
  rw[compile_top_def]
  \\ every_case_tac \\ fs[option_fold_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[Q.ISPECL[`FST`,`SND`]FOLDL_FUPDATE_LIST |> SIMP_RULE(srw_ss())[LAMBDA_PROD]]
  \\ fs[Q.ISPEC`I:α#β -> α#β`LAMBDA_PROD |> GSYM |> SIMP_RULE (srw_ss())[]]
  \\ imp_res_tac compile_decs_dec \\ fs[]);

val global_env_inv_lift = Q.prove (
  `!mn var_map env.
    global_env_inv genv var_map {} env
    ⇒
    global_env_inv genv (nsLift mn var_map) {} (nsLift mn env)`,
  rw [v_rel_eqns, nsLookup_nsLift] >>
  every_case_tac >>
  fs []);

val invariant_def = Define `
  invariant var_map env s s_i1 ⇔
    global_env_inv s_i1.globals var_map {} env ∧
    s_rel s s_i1 ∧
    (!x. x ∈ s.defined_mods ⇒ LENGTH x = 1)`;

val invariant_change_clock = Q.store_thm("invariant_change_clock",
  `invariant menv env st1 st2 ⇒
   invariant menv env (st1 with clock := k) (st2 with clock := k)`,
  srw_tac[][invariant_def] >> full_simp_tac(srw_ss())[s_rel_cases])

val invariant_defined_mods = Q.prove(
  `invariant c d e f ⇒ f.defined_mods = IMAGE HD e.defined_mods`,
  rw[invariant_def,s_rel_cases]);

val invariant_defined_types = Q.prove(
  `invariant c d e f ⇒ e.defined_types = f.defined_types`,
  rw[invariant_def,s_rel_cases]);

val compile_prog_correct = Q.store_thm ("compile_prog_correct",
  `!s env prog var_map  s' r s_i1 next' var_map' prog_i1 t.
    evaluate$evaluate_tops s env prog = (s',r) ∧
    invariant var_map env.v s s_i1 ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    source_to_mod$compile_prog t (LENGTH s_i1.globals) var_map prog = (next',var_map',prog_i1)
    ⇒
    ∃(s'_i1:'a modSem$state) new_genv cenv' r_i1.
     modSem$evaluate_prompts <|c := env.c; v := []; exh_pat := F |> s_i1 prog_i1 =
       (s'_i1,cenv',new_genv,r_i1) ∧
     (!new_env.
       r = Rval new_env
       ⇒
       next' = LENGTH (s_i1.globals ++ new_genv) ∧
       r_i1 = NONE ∧
       cenv' = new_env.c ∧
       invariant var_map' (nsAppend new_env.v env.v) s' s'_i1) ∧
     (!err.
       r = Rerr err
       ⇒
       ?err_i1.
         r_i1 = SOME err_i1 ∧ s_rel s' s'_i1 ∧
         result_rel (\a b (c:'a). T) (s_i1.globals ++ new_genv) r (Rerr err_i1))`,
  ho_match_mp_tac evaluateTheory.evaluate_tops_ind >>
  conj_tac
  (* Empty prog *)
  >- rw [compile_prog_def, evaluate_prompts_def] >>
  conj_tac
  (* Cons case *)
  >- (
    rpt gen_tac >>
    qspec_tac (`top2::tops`, `tops`) >>
    rw [] >>
    qpat_x_assum `evaluate_tops _ _ (_::_) = _` mp_tac >>
    simp [Once evaluatePropsTheory.evaluate_tops_cons] >>
    fs [compile_prog_def] >>
    pairarg_tac >>
    fs [] >>
    pairarg_tac >>
    fs [] >>
    rveq >>
    split_pair_case_tac >>
    fs [] >>
    reverse CASE_TAC
    (* Error case *)
    >- (
      rw [] >>
      pop_assum drule>> simp[]>>
      spectv "t'"`t`>>simp[]>>
      rw [] >>
      qpat_x_assum `evaluate_prompts _ _ [_] = _` mp_tac >>
      simp [evaluate_prompts_def] >>
      split_pair_case_tac >>
      simp [] >>
      CASE_TAC >>
      rw []) >>
    rfs [] >>
    first_x_assum drule >>
    rw [] >>
    split_pair_case_tac >>
    fs [] >>
    rveq >>
    fs [extend_dec_env_def] >>
    qpat_x_assum`!x. P x` mp_tac>>
    spectv "t'" `t`>>simp[]>> strip_tac>>
    qpat_x_assum `evaluate_prompts _ _ [_] = _` mp_tac >>
    simp [evaluate_prompts_def] >>
    split_pair_case_tac >>
    simp [] >>
    CASE_TAC >>
    rw [] >>
    first_x_assum drule >>
    spect `n'`>>
    simp [] >>
    qmatch_assum_rename_tac `combine_dec_result _ final_res ≠ _` >>
    `final_res ≠ Rerr (Rabort Rtype_error)`
      by (
        Cases_on `final_res` >>
        fs [combine_dec_result_def]) >>
    rw [] >>
    Cases_on `final_res` >>
    fs [combine_dec_result_def] >>
    fs [result_rel_cases]) >>
  conj_tac
  (* Declarations case *)
  >- (
    rw [compile_prog_def, evaluateTheory.evaluate_tops_def] >>
    pairarg_tac >>
    fs [compile_top_def] >>
    pairarg_tac >>
    fs [compile_decs_def] >>
    rw [] >>
    drule compile_decs_correct >>
    fs [invariant_def] >>
    disch_then drule >>
    spectv "t'" `t`>>
    simp [compile_decs_def, evaluate_prompts_def, evaluate_prompt_def] >>
    strip_tac >>
    drule prompt_mods_ok_dec >>
    drule no_dup_types_dec >>
    impl_tac
    >- (
      Cases_on `d` >>
      fs [evaluate_decs_def, semanticPrimitivesTheory.no_dup_types_def,
          semanticPrimitivesTheory.decs_to_types_def] >>
      fs [evaluateTheory.evaluate_decs_def] >>
      every_case_tac >>
      fs []) >>
    simp [] >>
    rename1 `evaluate_decs [] _ _ [_] = (s', final_result)` >>
    Cases_on `final_result` >>
    fs []
    >- (
      rw [option_fold_def]
      >- (
        irule global_env_inv_append >>
        rw [] >>
        metis_tac [v_rel_weakening])
      >- (
        fs [s_rel_cases, update_mod_state_def] >>
        drule evaluate_decs_globals >>
        rw [] >>
        fs [])
      >- (
        drule evaluatePropsTheory.evaluate_decs_state_unchanged >>
        simp [] >>
        metis_tac []))
    >- (
      fs [s_rel_cases, update_mod_state_def, result_rel_cases] >>
      metis_tac [v_rel_weakening]))
  (* Module case *)
  >- (
    rw [compile_prog_def, evaluateTheory.evaluate_tops_def] >>
    pairarg_tac >>
    fs [compile_top_def] >>
    pairarg_tac >>
    fs [] >>
    rw [] >>
    split_pair_case_tac >>
    fs [] >>
    rename1 `evaluate_decs [_] _ _ _ = (st1, result)` >>
    `result ≠ Rerr (Rabort Rtype_error)`
      by (
        every_case_tac >> rw []) >>
    drule compile_decs_correct >>
    fs [invariant_def] >>
    disch_then drule >>
    spectv "t'" `t`>>
    simp [evaluate_prompts_def, evaluate_prompt_def] >>
    strip_tac >>
    drule prompt_mods_ok >>
    drule no_dup_types >>
    `mn ∉ s_i1.defined_mods`
    by (
      fs [s_rel_cases] >>
      rw [] >>
      Cases_on `x` >>
      fs [] >>
      CCONTR_TAC >>
      fs [] >>
      res_tac >>
      fs [LENGTH_EQ_NUM]) >>
    simp [] >>
    Cases_on `result` >>
    fs [] >>
    rw [] >>
    rw []
    >- simp [option_fold_def]
    >- (
      irule global_env_inv_append >>
      rw [nsDom_nsLift, nsDomMod_nsLift]
      >- metis_tac [global_env_inv_lift]
      >- metis_tac [v_rel_weakening])
    >- (
      fs [s_rel_cases, update_mod_state_def] >>
      drule evaluate_decs_globals >>
      rw [] >>
      fs [GSYM INSERT_SING_UNION])
    >- metis_tac [evaluatePropsTheory.evaluate_decs_state_unchanged]
    >- fs [s_rel_cases, update_mod_state_def, GSYM INSERT_SING_UNION]
    >- (
      fs [s_rel_cases, update_mod_state_def, result_rel_cases] >>
      metis_tac [v_rel_weakening])));

val inj_hd_sing = Q.prove (
  `EVERY (\mn. LENGTH mn = 1) l
   ⇒
   !x y. MEM x l ∧ MEM y l ∧ HD x = HD y ⇒ x = y`,
  induct_on `l` >>
  rw [] >>
  fs [EVERY_MEM] >>
  res_tac >>
  fs [] >>
  `!lst. LENGTH lst = 1 ⇔ ?x. lst = [x]`
  by (rw [] >> Cases_on `lst` >> rw [LENGTH_NIL]) >>
  fs [] >>
  rw [] >>
  fs []);

val compile_prog_mods_ok = Q.prove (
  `!l var_map prog l' var_map' prog_i1 n.
    compile_prog n l var_map prog = (l',var_map',prog_i1)
    ⇒
    EVERY (λp. case p of Prompt mn ds => prompt_mods_ok mn ds) prog_i1`,
  induct_on `prog` >>
  srw_tac[][compile_prog_def, LET_THM] >>
  srw_tac[][] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  first_x_assum drule >>
  rw [] >>
  every_case_tac >>
  fs [compile_top_def] >>
  every_case_tac >>
  pairarg_tac >>
  fs [] >>
  rw [] >>
  metis_tac [prompt_mods_ok_dec, prompt_mods_ok]);

val whole_compile_prog_correct = Q.store_thm ("whole_compile_prog_correct",
  `evaluate_prog s env prog = (s',r) ∧
   invariant var_map env.v s s_i1 ∧
   compile_prog n (LENGTH s_i1.globals) var_map prog = (next',var_map',prog_i1) ∧
   r ≠ Rerr (Rabort Rtype_error)
   ⇒
    ∃(s'_i1:'a modSem$state) r_i1.
     evaluate_prog <| c := env.c; v := []; exh_pat := F |> s_i1 prog_i1 = (s'_i1,r_i1) ∧
     s_rel s' s'_i1 ∧
     (∀v. r = Rval v ⇒ r_i1 = NONE) ∧
     (∀err. r = Rerr err ⇒ ∃err_i1. r_i1 = SOME err_i1 ∧
       ∃new_genv.
         result_rel (\a b (c:'a). T) (s_i1.globals ++ new_genv) r (Rerr err_i1))`,
  rw [modSemTheory.evaluate_prog_def, evaluateTheory.evaluate_prog_def]
  \\ imp_res_tac compile_prog_mods_ok
  \\ imp_res_tac invariant_defined_mods
  \\ imp_res_tac invariant_defined_types
  \\ fs[semanticPrimitivesTheory.no_dup_mods_def,
        semanticPrimitivesTheory.no_dup_top_types_def]
  >- (
    fs[EVERY_MEM,EXISTS_MEM]
    \\ res_tac
    \\ drule compile_prog_correct
    \\ disch_then drule
    \\ spect`n`
    \\ rw[] \\ fs[LIST_TO_SET_MAP]
    \\ TRY (Cases_on`r`\\fs[invariant_def])
    \\ rw []
    \\ metis_tac[PAIR, ALL_DISTINCT_MAP, typeSoundTheory.disjoint_image]));

open semanticsTheory

val precondition_def = Define`
  precondition s1 env1 conf s2 env2 ⇔
    invariant conf.mod_env env1.v s1 s2 ∧
    env2.c = env1.c ∧
    env2.v = [] ∧
    env2.exh_pat = F ∧
    conf.next_global = LENGTH s2.globals`;

val SND_eq = Q.prove(
  `SND x = y ⇔ ∃a. x = (a,y)`,
  Cases_on`x`\\rw[]);

val compile_correct = Q.store_thm("compile_correct",
  `precondition s1 env1 c s2 env2 ⇒
   ¬semantics_prog s1 env1 prog Fail ⇒
   semantics_prog s1 env1 prog (semantics env2 s2 (SND (compile c prog)))`,
  rw[semantics_prog_def,SND_eq,precondition_def,compile_def]
  \\ pairarg_tac \\ fs[]
  \\ simp[modSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs[SND_eq]
  >- (
    fs[semantics_prog_def,SND_eq]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ simp[]
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) \\ fs[]
    \\ spose_not_then strip_assume_tac \\ fs[]
    \\ fs[evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs[] \\ rw[]
    \\ drule (GEN_ALL whole_compile_prog_correct)
    \\ spectv "n" `1`
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ asm_exists_tac \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`modSem$evaluate_prog env2'`
    \\ `env2' = env2`
    by ( unabbrev_all_tac \\ rw[environment_component_equality])
    \\ fs[]
    \\ Cases_on`r`\\fs[result_rel_cases] )
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ conj_tac
  >- (
    rw[] \\ rw[semantics_prog_def]
    \\ fs[evaluate_prog_with_clock_def]
    \\ qexists_tac`k`
    \\ pairarg_tac \\ fs[]
    \\ drule (GEN_ALL whole_compile_prog_correct)
    \\ spectv "n" `1`
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ impl_tac
    >- ( rpt(first_x_assum(qspec_then`k`mp_tac))\\fs[] )
    \\ qmatch_goalsub_abbrev_tac`modSem$evaluate_prog env2'`
    \\ `env2' = env2`
    by ( unabbrev_all_tac \\ rw[environment_component_equality])
    \\ strip_tac
    \\ fs[invariant_def,s_rel_cases]
    \\ rveq \\ fs[]
    \\ every_case_tac \\ fs[]
    \\ rw[]
    \\ strip_tac \\ fs[result_rel_cases] )
  \\ rw[]
  \\ simp[semantics_prog_def]
  \\ conj_tac
  >- (
    rw[]
    \\ fs[evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs[]
    \\ drule (GEN_ALL whole_compile_prog_correct)
    \\ spectv "n" `1`
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ impl_tac
    >- ( rpt(first_x_assum(qspec_then`k`mp_tac))\\fs[] )
    \\ qmatch_goalsub_abbrev_tac`modSem$evaluate_prog env2'`
    \\ `env2' = env2`
    by ( unabbrev_all_tac \\ rw[environment_component_equality])
    \\ strip_tac
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ rveq \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ fs[]
    \\ rveq
    \\ fs[result_rel_cases]
    \\ fs[s_rel_cases]
    \\ last_x_assum(qspec_then`k`mp_tac)
    \\ simp[]
    \\ Cases_on`r`\\fs[]
    \\ Cases_on`a`\\fs[])
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
    \\ drule (GEN_ALL whole_compile_prog_correct)
    \\ spectv "n" `1`
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ impl_tac
    >- ( rpt(first_x_assum(qspec_then`k`mp_tac))\\fs[] )
    \\ qmatch_goalsub_abbrev_tac`modSem$evaluate_prog env2'`
    \\ `env2' = env2`
    by ( unabbrev_all_tac \\ rw[environment_component_equality])
    \\ rveq
    \\ strip_tac
    \\ fs[]
    \\ fs[s_rel_cases] )
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
  \\ metis_tac[evaluatePropsTheory.evaluate_prog_ffi_mono_clock,
               evaluatePropsTheory.io_events_mono_def,
               LESS_EQ_CASES,FST]);

               *)

val _ = export_theory ();
