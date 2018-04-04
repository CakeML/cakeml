open preamble backendComputeLib sptreeTheory flatLangTheory reachabilityTheory flat_elimTheory flatSemTheory flatPropsTheory

val m = Hol_pp.print_apropos;
val f = print_find;

val _ = new_theory "flat_elimProof";


(******************************************************** STATE_REL *********************************************************)

(**************************** FIND GLOBALS *****************************)

val v_size_map_snd = Q.store_thm("exp_size_map_snd",
    `∀ vvs . v3_size (MAP SND vvs) ≤ v1_size vvs`,
    Induct >> rw[v_size_def] >> 
    Cases_on `v3_size (MAP SND vvs) = v1_size vvs` >> 
    `v_size (SND h) ≤ v2_size h` by (Cases_on `h` >> rw[v_size_def]) >> rw[]
);

(******** FINDALLGLOBALS, FINDVGLOBALS, FINDREFSGLOBALS ********)

val findAllGlobals_def = Define `
    (findAllGlobals e = union (findLookups e) (findLoc e)) ∧ 
    (findAllGlobalsL [] = LN) ∧
    (findAllGlobalsL (h::t) = union (findAllGlobals h) (findAllGlobalsL t))
`

val findAllGlobals_ind = theorem "findAllGlobals_ind";

val findVglobals_def = tDefine "findVglobals" `
    (findVglobals (Conv _ vl) = findVglobalsL vl) ∧
    (findVglobals (Closure vvs _ e) = 
        union (findVglobalsL (MAP SND vvs)) (findAllGlobals e)) ∧  
    (findVglobals (Recclosure vvs vves _) = 
        union (findVglobalsL (MAP SND vvs)) (findAllGlobalsL (MAP (SND o SND) vves))) ∧ 
    (findVglobals (Vectorv vl) = findVglobalsL vl) ∧
    (findVglobals _ = LN) ∧
    (findVglobalsL [] = LN) ∧ 
    (findVglobalsL (h::t) = union (findVglobals h) (findVglobalsL t)) 
`
(
    WF_REL_TAC `measure (λ e . case e of 
            | INL x => v_size x 
            | INR y => v3_size y)` >> 
    rw[v_size_def] >> qspec_then `vvs` mp_tac v_size_map_snd >>
    Cases_on `v3_size(MAP SND vvs) = v1_size vvs` >> rw[]
);

val findVglobals_ind = theorem "findVglobals_ind";

val findRefsGlobals_def = Define `
    (findRefsGlobals (Refv a::t) = union (findVglobals a) (findRefsGlobals t)) ∧ 
    (findRefsGlobals (Varray l::t) = union (findVglobalsL l) (findRefsGlobals t)) ∧
    (findRefsGlobals _ = LN)
`

val findRefsGlobals_ind = theorem "findRefsGlobals_ind";

(******** FINDENVGLOBALS, FINDRESULTGLOBALS ********)

val findEnvGlobals_def = Define `
    findEnvGlobals env = findVglobalsL (MAP SND env.v)
`

val findResultGlobals_def = Define `
    (findResultGlobals (SOME (Rraise v)) = findVglobals v) ∧ 
    (findResultGlobals _ = LN)
`

val findResultGlobals_ind = theorem "findResultGlobals_ind";

val findSemPrimResGlobals_def = Define `
    (findSemPrimResGlobals (Rerr e : (flatSem$v list, flatSem$v) semanticPrimitives$result) =
       findResultGlobals (SOME e)) ∧
    (findSemPrimResGlobals (Rval e) = findVglobalsL e)
`

(**************************** GLOBALS_REL *****************************)

(* s = state, t = removed state *)
val globals_rel_def = Define `
    globals_rel (reachable : num_set) (s : 'ffi flatSem$state) (t : 'ffi flatSem$state) ⇔ 
        LENGTH s.globals = LENGTH t.globals ∧ 
        (∀ n . n ∈ domain reachable ∧ n < LENGTH t.globals
        ⇒ EL n s.globals = EL n t.globals)
`

val globals_rel_refl = Q.store_thm("globals_rel_refl",
    `∀ reachable s . globals_rel reachable s s`,
    rw[globals_rel_def]
);

val globals_rel_trans = Q.store_thm("globals_rel_trans",
    `∀ reachable s1 s2 s3 . 
        globals_rel reachable s1 s2 ∧ globals_rel reachable s2 s3
        ⇒ globals_rel reachable s1 s3`,
    rw[globals_rel_def]
);

val globals_rel_sym = Q.store_thm("globals_rel_sym",
    `∀ reachable s1 s2 . 
        globals_rel reachable s1 s2 ⇔ globals_rel reachable s2 s1`,
    rw[] >> EQ_TAC >> rw[globals_rel_def]
);

val globals_rel_equivalence = Q.store_thm("globals_rel_equivalence",
    `∀ reachable . equivalence (globals_rel reachable)`,
    rw[equivalence_def, reflexive_def, symmetric_def, transitive_def] >>
    fs[globals_rel_sym, globals_rel_refl] >>
    metis_tac[globals_rel_trans]
);

(**************************** DECSCLOSED *****************************)

val decsClosed_def = Define `
    decsClosed (reachable : num_set) decs ⇔  ∀ r t . analyseCode decs = (r,t)
    ⇒ domain r ⊆ domain reachable ∧
      (∀ n m . n ∈ domain reachable ∧ isReachable (mk_wf_set_tree t) n m 
      ⇒ m ∈ domain reachable)
`
(*** TO MOVE TO REACHABILITY THEORY ***)
val union_num_set_sym = Q.store_thm ("union_num_set_sym",
    `∀ t1:num_set t2 . union t1 t2 = union t2 t1`,
    Induct >> fs[union_def] >> rw[] >> CASE_TAC >> fs[union_def]
);

val lookup_mk_wf_set_tree = Q.store_thm("lookup_mk_wf_set_tree",
    `∀ n tree x . lookup n tree = SOME x ⇒ ∃ y . lookup n (mk_wf_set_tree tree) = SOME y ∧ domain x = domain y`,
    rw[flat_elimTheory.mk_wf_set_tree_def] >> rw[lookup_map] >> rw[lookup_union]
);

val num_set_tree_union_sym = Q.store_thm("num_set_tree_union_sym",
    `∀ (t1 : num_set num_map) t2 . num_set_tree_union t1 t2 = num_set_tree_union t2 t1`,
    Induct >> rw[num_set_tree_union_def] >> Cases_on `t2` >> fs[num_set_tree_union_def] >>
    fs[union_num_set_sym]
);

val lookup_domain_num_set_tree_union = Q.store_thm("lookup_domain_num_set_tree_union",
    `∀ n (t1:num_set num_map) t2 x . lookup n t1 = SOME x 
    ⇒ ∃ y . lookup n (num_set_tree_union t1 t2) = SOME y ∧ domain x ⊆ domain y`,
    Induct_on `t1` >> rw[] 
    >- fs[lookup_def]
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >> fs[lookup_def, domain_union])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >> fs[lookup_def, domain_union] >>
        Cases_on `EVEN n` >> fs[])
    >- (fs[lookup_def, num_set_tree_union_def] >> CASE_TAC >> fs[lookup_def, domain_union] >>
        Cases_on `n = 0` >> fs[domain_union] >> Cases_on `EVEN n` >> fs[])
);

val lookup_NONE_num_set_tree_union = Q.store_thm ("lookup_NONE_num_set_tree_union",
    `∀ n (t1:num_set num_map) t2 . lookup n t1 = NONE
    ⇒ lookup n (num_set_tree_union t1 t2) = lookup n t2`,
    Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >> Cases_on `n = 0` >> fs[] >>
    Cases_on `EVEN n` >> fs[]
);

val lookup_SOME_SOME_num_set_tree_union = Q.store_thm ("lookup_SOME_SOME_num_set_tree_union",
    `∀ n (t1:num_set num_map) x1 t2 x2 . lookup n t1 = SOME x1 ∧ lookup n t2 = SOME x2
    ⇒ lookup n (num_set_tree_union t1 t2) = SOME (union x1 x2)`,
    Induct_on `t1` >> rw[] >> fs[lookup_def, num_set_tree_union_def] >>
    Cases_on `t2` >> fs[lookup_def] >>
    Cases_on `EVEN n` >> fs[] >>
    Cases_on `n = 0` >> fs[]
);

val lookup_num_set_tree_union = Q.store_thm("lookup_num_set_tree_union",
    `∀ (t1 : num_set num_map) t2 n . 
        lookup n (num_set_tree_union t1 t2) = case (lookup n t1) of
            | NONE => lookup n t2
            | SOME s1 => case (lookup n t2) of 
                | NONE => SOME s1 
                | SOME s2 => SOME (union s1 s2)`,
    rw[] >> Cases_on `lookup n t1` >> fs[]
    >-  fs[lookup_NONE_num_set_tree_union] 
    >- (Cases_on `lookup n t2` >> fs[]
        >- (fs[lookup_NONE_num_set_tree_union, num_set_tree_union_sym] >>
            imp_res_tac lookup_NONE_num_set_tree_union >>
            pop_assum (qspec_then `t1` mp_tac) >> rw[] >>
            fs[num_set_tree_union_sym])
        >-  fs[lookup_SOME_SOME_num_set_tree_union])
);
                
val isAdjacent_num_set_tree_union = Q.store_thm("isAdjacent_num_set_tree_union",
    `∀ t1 t2 n m . 
        isAdjacent t1 n m ⇒ isAdjacent (num_set_tree_union t1 t2) n m`,
    rw[isAdjacent_def] >> imp_res_tac lookup_domain_num_set_tree_union >>
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >> 
    first_x_assum (qspec_then `t2` mp_tac) >> rw[] >>
    fs[SUBSET_DEF, domain_lookup]
);

val lookup_domain_mk_wf_set_tree = Q.store_thm("lookup_domain_mk_wf_set_tree",
    `∀ n t x y . lookup n (mk_wf_set_tree t) = SOME x ⇒
        lookup n t = SOME y ⇒ domain y = domain x`,
    rw[flat_elimTheory.mk_wf_set_tree_def] >> fs[lookup_map, lookup_union] >>
    metis_tac[domain_mk_wf]
);

val superdomain_inverse_thm = Q.store_thm("superdomain_inverse_thm",
    `∀ n tree . n ∈ domain (superdomain tree) 
    ⇒ ∃ k aSet . lookup k tree = SOME aSet ∧ n ∈ domain aSet`,
    Induct_on `tree` >> rw[superdomain_def] >> fs[lookup_def, domain_union] >> res_tac
    >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
    >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
    >- (qexists_tac `0` >> fs[])
    >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])
);

val superdomain_not_in_thm = Q.store_thm("superdomain_not_in_thm",
    `∀ n tree . n ∉ domain (superdomain tree) ⇒ ∀ k aSet . lookup k tree = SOME aSet ⇒ n ∉ domain aSet`,
    Induct_on `tree` >> rw[superdomain_def] >> fs[lookup_def, domain_union] >> res_tac >>
    Cases_on `k = 0` >> Cases_on `EVEN k` >> fs[] >> metis_tac[]
);

val domain_superdomain_num_set_tree_union = Q.store_thm("domain_superdomain_num_set_tree_union",
    `∀ t1 t2 . domain (superdomain t1) ⊆ domain (superdomain (num_set_tree_union t1 t2))`,
    fs[SUBSET_DEF] >> rw[] >> imp_res_tac superdomain_inverse_thm >> 
    imp_res_tac lookup_domain_num_set_tree_union >> pop_assum (qspec_then `t2` mp_tac) >>
    rw[] >> imp_res_tac superdomain_thm >> metis_tac[SUBSET_DEF]
);

val isAdjacent_wf_set_tree_num_set_tree_union = Q.store_thm ("isAdjacent_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 n m . 
        isAdjacent (mk_wf_set_tree t1) n m 
        ⇒ isAdjacent (mk_wf_set_tree (num_set_tree_union t1 t2)) n m`,
    rw[isAdjacent_def] >> fs[mk_wf_set_tree_def] >> fs[lookup_map] >> 
    fs[lookup_union] >> fs[lookup_map] >> fs[PULL_EXISTS] >> fs[lookup_num_set_tree_union] >>
    Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[] >>
    rveq >> fs[lookup_def, mk_wf_def, lookup_union] >> EVERY_CASE_TAC >> fs[] >>
    qspecl_then [`t1`, `t2`] mp_tac domain_superdomain_num_set_tree_union >>
    rw[SUBSET_DEF, domain_lookup]
);

(*
val mk_wf_set_tree_num_set_tree_union = Q.store_thm("mk_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 . mk_wf_set_tree (num_set_tree_union t1 t2) = 
        num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2)`,
    rw[] >>
    `wf (mk_wf_set_tree (num_set_tree_union t1 t2))` by metis_tac[mk_wf_set_tree_thm, wf_set_tree_def] >>
    `wf (num_set_tree_union (mk_wf_set_tree t1) (mk_wf_set_tree t2))` by 
        metis_tac[mk_wf_set_tree_thm, wf_set_tree_def, wf_num_set_tree_union] >> 
    rw[spt_eq_thm] >>
    simp[mk_wf_set_tree_def] >>
    fs[lookup_map] >> fs[lookup_union] >> fs[lookup_map] >>
    fs[lookup_num_set_tree_union] >>
    fs[lookup_map] >> fs[lookup_union] >>
    fs[lookup_map] >> fs[OPTION_MAP_COMPOSE, mk_wf_def] >>
    Cases_on `lookup n t1` >> Cases_on `lookup n t2` >> fs[] >>
    EVERY_CASE_TAC >> fs[mk_wf_def, union_def] >>
    
    `lookup n (num_set_tree_union t1 t2) = NONE` by fs[lookup_num_set_tree_union] >>

cheat (* TODO - not necessary for now, but a useful result *)
);
*)

val isReachable_wf_set_tree_num_set_tree_union = Q.store_thm ("isReachable_wf_set_tree_num_set_tree_union",
    `∀ t1 t2 n m . 
        isReachable (mk_wf_set_tree t1) n m ⇒ isReachable (mk_wf_set_tree (num_set_tree_union t1 t2)) n m`,
    simp[isReachable_def] >> strip_tac >> strip_tac >> 
    ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] >>
    simp[Once RTC_CASES2] >> disj2_tac >> qexists_tac `m` >> fs[] >> 
    imp_res_tac isAdjacent_wf_set_tree_num_set_tree_union >> fs[]
); 

val decsClosed_reduce = Q.store_thm ("decsClosed_reduce",
    `∀ reachable h t . decsClosed reachable (h::t) ⇒ decsClosed reachable t`,
    fs[decsClosed_def] >> rw[] >> Cases_on `h` >> fs[analyseCode_def] 
    >- (Cases_on `analyseExp e` >> fs[codeAnalysis_union_def, domain_union])
    >- (Cases_on `analyseExp e` >> fs[codeAnalysis_union_def, domain_union] >>
        first_x_assum drule >> rw[] >> pop_assum match_mp_tac >>
        assume_tac isReachable_wf_set_tree_num_set_tree_union >> fs[] >>
        fs[Once num_set_tree_union_sym])
    >> metis_tac[] 
);


(**************************** FLAT_STATE_REL *****************************)

(* s = state, t = removed state *)
val flat_state_rel_def = Define `
    flat_state_rel reachable s t ⇔ s.clock = t.clock ∧ s.refs = t.refs ∧
    s.ffi = t.ffi ∧ globals_rel reachable s t ∧ 
    domain (findRefsGlobals s.refs) ⊆ domain reachable
`

val flat_state_rel_trans = Q.store_thm("flat_state_rel_trans",
    `∀ reachable s1 s2 s3 . flat_state_rel reachable s1 s2 ∧ flat_state_rel reachable s2 s3 
    ⇒ flat_state_rel reachable s1 s3`,
    rw[flat_state_rel_def, globals_rel_def]
);

val flat_state_rel_triangle = Q.store_thm("flat_state_rel_triangle",
    `∀ reachable s1 s2 s3 . flat_state_rel reachable s1 s2 ∧ flat_state_rel reachable s1 s3 
    ⇒ flat_state_rel reachable s2 s3`,
    rw[flat_state_rel_def, globals_rel_def] >> metis_tac[]
);

(******************************************************** OTHER LEMMAS *********************************************************)

(**************************** IMPLEMENTATION LEMMAS *****************************)

val keep_Dlet = Q.store_thm("keep_Dlet",
    `∀ (reachable:num_set) h . ¬ keep reachable h ⇒ ∃ x . h = Dlet x`,
   Cases_on `h` >> rw[keep_def]
);
          

(******************************************************** MAIN PROOFS *********************************************************)

val evaluate_sing_keep_flat_state_rel_eq = Q.store_thm("evaluate_sing_keep_flat_state_rel_eq",
    `(∀ env (state:'ffi flatSem$state) exprL new_state result expr reachable removed_state . 
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧ exprL = [expr] ∧ 
        keep reachable (Dlet expr) ∧ 
        flat_state_rel reachable state removed_state ∧ 
        domain (findEnvGlobals env) ⊆ domain reachable ∧  
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state . 
        evaluate (env with v := []) removed_state exprL = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧ 
        domain (findSemPrimResGlobals result) ⊆ domain reachable)
  ∧ 
    (∀ env (state:'ffi flatSem$state) v patExp_list err_v new_state result reachable removed_state .
        evaluate_match (env with v := []) state v patExp_list err_v = (new_state, result) ∧
        flat_state_rel reachable new_state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧ 
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate_match (env with v := []) removed_state v patExp_list err_v = (new_removed_state, result) ∧ 
        flat_state_rel reachable new_state new_removed_state ∧ 
        domain (findSemPrimResGlobals result) ⊆ domain reachable)`
  ,
    ho_match_mp_tac evaluate_ind >> rw[] >>
    qpat_assum `flat_state_rel _ _ _` mp_tac >> 
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac
    (* 14 subgoals *)
    >| [
        qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
        simp[flatSemTheory.evaluate_def] >> 
        rw[] >> fs[findSemPrimResGlobals_def, findVglobals_def]
      , 
        qpat_x_assum `evaluate _ _ _ = _` mp_tac >> simp[flatSemTheory.evaluate_def] >>
        Cases_on `evaluate (env with v:=[]) state' [e]` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        rw[] >> fs[keep_def] >> qpat_x_assum `inter _ _ ≠ _` mp_tac >> 
        simp[Once findLoc_def] >> strip_tac >> fs[] >> rfs[] >>
        `r ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
        fs[] >> Cases_on `r` >> fs[] >> rveq >> 
        fs[findSemPrimResGlobals_def, findResultGlobals_def] >>
        `LENGTH a = 1` by (imp_res_tac evaluate_length >> fs[LENGTH]) >>
        Cases_on `a` >> fs[findVglobals_def]
      ,
        qpat_x_assum `evaluate _ _ _ = _` mp_tac >> simp[flatSemTheory.evaluate_def] >>
        Cases_on `evaluate (env with v:=[]) state' [e]` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        rw[] >> fs[keep_def] >> qpat_x_assum `inter _ _ ≠ _` mp_tac >> 
        simp[Once findLoc_def] >> strip_tac >> fs[] >> rfs[] >>
        `inter (findLoc e) reachable ≠ LN` by cheat (* TODO *) >> 
        `r ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
        fs[] >> rfs[] >>
        Cases_on `r` >> fs[] >> rveq >>
        Cases_on `e'` >> fs[] >>
        cheat (* TODO *)
      ,
      cheat,
      cheat,
      cheat,
      cheat,
      cheat,
      cheat,
      cheat,
      cheat,
      cheat,
      cheat,
      cheat

    ]    
);

val evaluate_dec_flat_state_rel = Q.store_thm("evaluate_dec_state_rel",
    `∀ env (state:'ffi flatSem$state) dec new_state new_ctors result reachable removed_state . 
        evaluate_dec env state dec = (new_state, new_ctors, result) ∧ 
        flat_state_rel reachable state removed_state ∧ keep reachable dec ∧
        result ≠ SOME (Rabort Rtype_error) ∧ 
        domain (findEnvGlobals env) ⊆ domain reachable
    ⇒ ∃ new_removed_state . 
        evaluate_dec env removed_state dec = (new_removed_state, new_ctors, result) ∧ 
        flat_state_rel reachable new_state new_removed_state ∧ 
        domain (findResultGlobals result) ⊆ domain reachable`
      ,
        rw[] >> qpat_x_assum `evaluate_dec _ _ _ = _` mp_tac >> 
        reverse(Induct_on `dec`) >> fs[evaluate_dec_def] >> strip_tac >> strip_tac >>
        fs[keep_def] 
        >- (reverse(Cases_on `env.check_ctor`) >> fs[is_fresh_exn_def] >>
            rw[] >> fs[findResultGlobals_def])
        >- (reverse(Cases_on `env.check_ctor`) >> fs[is_fresh_exn_def] >>
            rw[] >> fs[findResultGlobals_def])
        >- (assume_tac evaluate_sing_keep_flat_state_rel_eq >> fs[] >>
            pop_assum kall_tac >>
            Cases_on `evaluate (env with v := []) state' [e]` >> fs[] >>
            first_x_assum (qspecl_then [`env`, `state'`, `q`, `r`, `e`, 
                `reachable`, `removed_state`] mp_tac) >> strip_tac >>
            fs[keep_def] >> rfs[] >>
            strip_tac >>
            `r ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
            qpat_x_assum `_ = (_,_,_) ` mp_tac >> fs[] >>
            EVERY_CASE_TAC >> fs[] >> rw[] >> fs[findResultGlobals_def, findSemPrimResGlobals_def])
);

val evaluate_sing_notKeep_flat_state_rel = Q.store_thm("evaluate_sing_notKeep_state_rel",
    `(∀ env (state:'ffi flatSem$state) exprL new_state result expr reachable removed_state . 
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧ exprL = [expr] ∧ 
        ¬keep reachable (Dlet expr) ∧ 
        flat_state_rel reachable state removed_state ∧ 
        domain (findEnvGlobals env) ⊆ domain reachable ∧  
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧ ∃ value : flatSem$v . result = Rval [value] ∧
      domain (findVglobals value) ⊆ domain reachable)
  ∧ 
    (∀ env (state:'ffi flatSem$state) v patExp_list err_v new_state result reachable removed_state .
        evaluate_match (env with v := []) state v patExp_list err_v = (new_state, result) ∧
        (*¬ keep reachable (Dlet XXXXX) ∧*)
        flat_state_rel reachable new_state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧ 
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧ ∃ value : flatSem$v . result = Rval [value] ∧ 
      domain (findVglobals value) ⊆ domain reachable)`
,
    ho_match_mp_tac evaluate_ind >> rw[] >>
    qpat_assum `flat_state_rel _ _ _` mp_tac >> 
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac
    
    (* 26 subgoals - 13 flatLang expressions, two conjuncts in goal for each *)
    >| [
        qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
        simp[flatSemTheory.evaluate_def] >> rw[] >> fs[]
    ,
        qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
        simp[flatSemTheory.evaluate_def] >> rw[] >> fs[findVglobals_def]
    ,
        qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
        simp[flatSemTheory.evaluate_def] >>
        Cases_on `evaluate (env with v := []) state' [e]` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[keep_def, Once findLoc_def] >> rw[] >>
        `r ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
        fs[] >> Cases_on `r` >> fs[]
    ,   
        qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
        simp[flatSemTheory.evaluate_def] >>
        Cases_on `evaluate (env with v := []) state' [e]` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        rw[] >>
        fs[keep_def, Once findLoc_def] >> rw[] >>
        Cases_on `r` >> fs[] >>
        rveq >> fs[] >>
        cheat (* TODO - DOESN'T SEEM TO BE TRUE *)
    ,
        qpat_x_assum `evaluate _ _ _ = _` mp_tac >> simp[flatSemTheory.evaluate_def] >>
        Cases_on `evaluate (env with v := []) state' [e]` >> fs[] >>
        cheat (* TODO *)
    ,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat,
        cheat
    ]
);



(**************************** FLAT_DECS_REMOVAL LEMMA *****************************)

val flat_decs_removal_lemma = Q.store_thm ("flat_decs_removal_lemma",
    `∀ env (state:'ffi flatSem$state) decs new_state new_ctors result reachable removed_decs removed_state . 
        evaluate_decs env state decs = (new_state, new_ctors, result) ∧ 
        result ≠ SOME (Rabort Rtype_error) ∧ 
        removeUnreachable reachable decs = removed_decs ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        decsClosed reachable decs
    ⇒ ∃ new_removed_state . 
        evaluate_decs env removed_state removed_decs = (new_removed_state, new_ctors, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧ 
        domain (findResultGlobals result) ⊆ domain reachable`
  ,
    Induct_on `decs` 
    >- (rw[evaluate_decs_def, removeUnreachable_def] >> fs[evaluate_decs_def, findResultGlobals_def])
    >>  fs[evaluate_decs_def, removeUnreachable_def] >> rw[] >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >> SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac
        >- (fs[evaluate_decs_def] >> `∃ r . evaluate_dec env state' h = r` by simp[] >> 
            PairCases_on `r` >> fs[] >> `r2 ≠ SOME (Rabort Rtype_error)` by (CCONTR_TAC >> fs[]) >> 
            drule evaluate_dec_flat_state_rel >> rpt (disch_then drule) >> rw[] >> fs[] >> 
            Cases_on `r2` >> fs[] >> rw[] >> EVERY_CASE_TAC >> first_x_assum drule >> fs[] >> 
            rveq >> disch_then drule >> reverse(impl_tac) >- rw[] >> fs[findEnvGlobals_def] >>
            imp_res_tac decsClosed_reduce)
       >>   reverse(EVERY_CASE_TAC) >> fs[] >> rveq >> rename1 `_ _ decs = (n_state, ctors, res)` >>
            imp_res_tac keep_Dlet >> rveq >> fs[Once evaluate_dec_def] >> EVERY_CASE_TAC >> fs[] >> 
            rveq >> rw[UNION_EMPTY] >> 
            `env with c updated_by $UNION {} = env` by fs[environment_component_equality] >> fs[]
            >- (assume_tac evaluate_sing_notKeep_flat_state_rel >> fs[] >> pop_assum kall_tac >>
                pop_assum (qspecl_then [`env`, `state'`, `new_state`, `Rerr e`, `x'`, 
                    `reachable`, `removed_state`] mp_tac) >> rpt(disch_then drule) >> fs[]) 
            >>  first_x_assum match_mp_tac >> fs[] >> asm_exists_tac >> fs[] >> 
                imp_res_tac decsClosed_reduce >> fs[] >> assume_tac evaluate_sing_notKeep_flat_state_rel >> 
                fs[] >> pop_assum kall_tac >>
                pop_assum (qspecl_then [`env`, `state'`, `q`, `Rval [Conv NONE []]`, `x`, 
                    `reachable`, `removed_state`] mp_tac) >> rpt(disch_then drule) >> fs[]


);


(* in code, you can say get global -> in flatLang you have code in closures, which can get globals therefore
    -> therefore anything in which you can say "get global" must be in reachable set -> have to scan all closures and recclosures *)

(* implementation-wise, be conservative - look for patterns of code that point into closures 
    -> look at source_to_flatTheory, look at patterns of code that it generates and then shape isHidden function to match this *)

(* what you want to get out of the matcher isHidden -
    isHidden should be of type : (num # exp) list option, where num is a global and exp is the corresponding code that gets
    unconditionally stored in the closure *)

(* pattern matcher should handle things like val (x, y, z) = someBigThing, or more generally val (Branch v1 v2 v3) = foo -
    there is only ever one pattern to match to usually *)

(* also check how mutually recursive functions turn out *)

(* if isHidden matcher gives out NONE, then make sure that everything is deemed reachable and the optimisation is therefore safe *)
    
(* TODO - make state_rel more like word_state_rel *)

(* TODO - upload to github on deadcode_elim branch *)






val _ = export_theory();






(* OLD *****************************************************************************************************************)
(*
(**************************** STATE_REL *****************************)
val state_rel_def = Define `
    state_rel (reachable:num_set) (s:'ffi flatSem$state) t ⇔ s.clock = t.clock ∧ s.refs = t.refs ∧ 
    s.ffi = t.ffi ∧ LENGTH s.globals = LENGTH t.globals ∧ 
    ∀ n . n ∈ domain reachable ∧ n < LENGTH s.globals 
        ⇒  EL n s.globals = EL n t.globals
`

val evaluate_dec_state_rel = Q.store_thm("evaluate_dec_state_rel",
    `∀ env s h t s1 new_ctors result reachable. 
        evaluate_dec env s h = (s1, new_ctors, result) ∧ 
        state_rel reachable s t ∧ keep reachable h ∧
        result ≠ SOME (Rabort Rtype_error)
    ⇒ ∃ t1 . evaluate_dec env t h = (t1, new_ctors, result) ∧ 
        state_rel reachable s1 t1`,
    cheat
);



(************************* LEMMAS *****************************)
(*val keep_new_ctors = Q.store_thm("keep_new_ctors",
    `∀ (reachable:num_set) h env state h1 new_ctors result . 
    ¬keep reachable h ∧ evaluate_dec env state h = (h1, new_ctors, result) ⇒ new_ctors = {}`,
    Cases_on `h` >> rw[keep_def] >> EVERY_CASE_TAC >> fs[] >>
    cheat
);

*)
(* by running x, we don't do anything observable, so we can delete it 
    in particular can't write to any globals we care about
*)

val not_keep_subterm = Q.store_thm("not_keep_subterm",
    `∀ reachable:num_set x y t . ¬keep reachable (Dlet x) ∧ 
        (x = Raise t y) ==> ¬keep reachable (Dlet y)`,
    cheat
);



val keep_state_rel_thm = Q.store_thm("keep_state_rel_thm",
    `(∀ env (s:'ffi flatSem$state) x s1 r reachable t . evaluate (env with v := []) s [x] = (s1, r) ∧ 
        ¬keep reachable (Dlet x) ∧ state_rel reachable s t    
    ⇒ state_rel reachable s1 t ∧ ∃ v . r = Rval [v])`, 
    cheat
); 


(***************************** REMOVAL *************************)
        
(* add assumption - if there is a get global in upcoming state, it is in reachable *)

val removal_thm = Q.store_thm ("removal_thm",
    `∀ env s ds s1 new_ctors result ds1 t (reachable:num_set).
        flatSem$evaluate_decs env s ds = (s1, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧
        removeUnreachable reachable ds = ds1 ∧ state_rel reachable s t 
    ⇒ ∃ t1 . 
        flatSem$evaluate_decs env t ds1 = (t1, new_ctors, result) ∧
        state_rel reachable s1 t1`,
    Induct_on `ds` 
    >- (rw[evaluate_decs_def, removeUnreachable_def] >> fs[evaluate_decs_def])
    >> fs[evaluate_decs_def, removeUnreachable_def] >> rw[]
        >- (fs[evaluate_decs_def] >> `∃ r . evaluate_dec env s h = r` by simp[] >> PairCases_on `r` >>
            fs[] >> `r2 ≠ SOME (Rabort Rtype_error)` by (CCONTR_TAC >> fs[]) >> 
            drule evaluate_dec_state_rel >> rpt (disch_then drule) >> rw[] >> fs[] >> Cases_on `r2` >> 
            fs[] >> rw[] >> EVERY_CASE_TAC >> first_x_assum drule >> fs[] >> rveq >> disch_then drule >>
            strip_tac >> fs[] >> rveq >> simp[]) 
        >> reverse(EVERY_CASE_TAC) >> fs[] >> rveq >>
           rename1 `_ = (s1, tn1, _)` >> rename1 `_ s1 ds = (s2, tn2, res)` >>
           imp_res_tac keep_Dlet >> rveq
            >- (fs[Once evaluate_dec_def] >> EVERY_CASE_TAC >> fs[] >> rveq >> rw[UNION_EMPTY] >>
                drule keep_state_rel_thm >> disch_then drule >> disch_then drule >> fs[]) 
            >> fs[Once evaluate_dec_def] >> EVERY_CASE_TAC >> fs[] >> rveq >> rw[UNION_EMPTY] >>
               first_x_assum match_mp_tac >> qmatch_assum_abbrev_tac `evaluate_decs env2 _ _ = _` >>
               `env2 = env` by (fs[flatSemTheory.environment_component_equality, Abbr `env2`]) >>
               fs[] >> asm_exists_tac >> fs[] >> drule keep_state_rel_thm >> disch_then drule >>
               disch_then drule >> fs[]
);
*)

(**************************** DLETS ******************************)

(*
val count_GlobalVarInits_def = tDefine "count_GlobalVarInits" `
    (count_GlobalVarInits (Raise _ er) = (count_GlobalVarInits er)) ∧ 
    (count_GlobalVarInits (Handle _ eh p_es) =
                (count_GlobalVarInits eh) + (count_GlobalVarInitsL (MAP SND p_es))) ∧ 
    (count_GlobalVarInits (Lit _ _) = 0n) ∧ 
    (count_GlobalVarInits (Con _ _ es) = count_GlobalVarInitsL es) ∧ 
    (count_GlobalVarInits (Var_local _ _) = 0n) ∧ 
    (count_GlobalVarInits (Fun _ _ ef) = count_GlobalVarInits ef) ∧ 
    (count_GlobalVarInits (App _ op es) = (case (dest_GlobalVarInit op) of
        | SOME n => 1n + (count_GlobalVarInitsL es)
        | NONE => count_GlobalVarInitsL es)) ∧ 
    (count_GlobalVarInits (If _ ei1 ei2 ei3) = 
        (count_GlobalVarInits ei1) + (count_GlobalVarInits ei2) + (count_GlobalVarInits ei3)) ∧ 
    (count_GlobalVarInits (Mat _ em p_es) =
        (count_GlobalVarInits em) + (count_GlobalVarInitsL (MAP SND p_es))) ∧ 
    (count_GlobalVarInits (Let _ _ el1 el2) = (count_GlobalVarInits el1) + (count_GlobalVarInits el2)) ∧ 
    (count_GlobalVarInits (Letrec _ vv_es elr1) = 
        (count_GlobalVarInitsL (MAP (SND o SND) vv_es)) + (count_GlobalVarInits elr1)) ∧
    (count_GlobalVarInitsL [] = 0n) ∧
    (count_GlobalVarInitsL (e::es) = count_GlobalVarInits e + count_GlobalVarInitsL es)
`
    (
        WF_REL_TAC `measure (λ e . case e of 
            | INL x => exp_size x 
            | INR (y:flatLang$exp list) => flatLang$exp6_size y)` >> rw[exp_size_def]
        >- (qspec_then `vv_es` mp_tac exp_size_map_snd_snd >>
            Cases_on `exp6_size(MAP (λ x . SND (SND x)) vv_es) = exp1_size vv_es` >>
            rw[])
        >> (qspec_then `p_es` mp_tac exp_size_map_snd >>
            Cases_on `exp6_size(MAP SND p_es) = exp3_size p_es` >>
            rw[])
    );

val count_GlobalVarInits_ind = theorem "count_GlobalVarInits_ind";

val count_GlobalVarInits_Dlet_def = Define `
    (count_GlobalVarInits_Dlet (d:flatLang$dec) = case d of
        | Dlet e => count_GlobalVarInits e
        | _ => 0n)
`
*)
(* THIS IS NOT TRUE
val one_Dlet_thm = Q.store_thm("one_Dlet_thm",
    `∀ e c p c1 ds d. source_to_flat$compile c p = (c1, ds) ∧ MEM d ds ∧ d = Dlet e 
    ⇒ count_GlobalVarInits e ≤ 1`,
    Induct_on `p`
    >-(rw[source_to_flatTheory.compile_def] >> fs[source_to_flatTheory.compile_decs_def] >>
       rw[] >> fs[] >> rw[count_GlobalVarInits_def] >> rw[dest_GlobalVarInit_def])
    >> cheat
);
*)
