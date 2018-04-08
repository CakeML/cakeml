open preamble backendComputeLib sptreeTheory flatLangTheory reachabilityTheory flat_elimTheory flatSemTheory flatPropsTheory

val m = Hol_pp.print_apropos;
val f = print_find;

val _ = new_theory "flat_elimProof";

val union_num_set_sym = Q.store_thm ("union_num_set_sym",
    `∀ t1:num_set t2 . union t1 t2 = union t2 t1`,
    Induct >> fs[union_def] >> rw[] >> CASE_TAC >> fs[union_def]
);

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
(* OLD VERSION 
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
*)

(* NEW DEFINITION - TODO - check changes to Closure/Recclosure are OK *)
val findVglobals_def = tDefine "findVglobals" `
    (findVglobals (Conv _ vl) = (findVglobalsL vl):num_set) ∧
    (findVglobals (Closure vvs _ e) = 
        findVglobalsL (MAP SND vvs)) ∧  
    (findVglobals (Recclosure vvs vves _) = 
        findVglobalsL (MAP SND vvs))  ∧ 
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

val findVglobalsL_APPEND = Q.store_thm("findVglobalsL_APPEND",
    `∀ l1 l2 . findVglobalsL (l1 ++ l2) = union (findVglobalsL l1) (findVglobalsL l2)`,
    Induct >> fs[findVglobals_def] >> fs[union_assoc]
);

val findVglobalsL_REVERSE = Q.store_thm("findVglobals_REVERSE",
    `∀ l . findVglobalsL l = findVglobalsL (REVERSE l)`,
    Induct >> fs[findVglobals_def] >> 
    fs[findVglobalsL_APPEND, union_num_set_sym, findVglobals_def]
);

val findVglobalsL_domain_MEM = Q.store_thm("findVglobalsL_MEM",
    `∀ k v vs . MEM (k, v) vs ⇒ domain (findVglobals v) ⊆ domain (findVglobalsL (MAP SND vs))`,
    Induct_on `vs` >> rw[] >> fs[findVglobals_def, domain_union] >> res_tac >> fs[SUBSET_DEF]
);

val findVglobals_MAP_Recclosure = Q.store_thm("findVglobals_MAP_Recclosure",
    `∀ (funs:(tvarN,tvarN # flatLang$exp) alist) v l . 
        domain (findVglobalsL (MAP (λ (f,x,e). Recclosure v l f) funs)) ⊆
        domain (findVglobalsL (MAP SND v))`,
    Induct >> fs[findVglobals_def] >> rw[domain_union] >> 
    PairCases_on `h` >> fs[findVglobals_def]
);

val findRefsGlobals_def = Define `
    (findRefsGlobals (Refv a::t) = union (findVglobals a) (findRefsGlobals t)) ∧ 
    (findRefsGlobals (Varray l::t) = union (findVglobalsL l) (findRefsGlobals t)) ∧
    (findRefsGlobals (_::t) = findRefsGlobals t) ∧
    (findRefsGlobals [] = LN)
`

val findRefsGlobals_ind = theorem "findRefsGlobals_ind";

val findRefsGlobals_EL = Q.store_thm("findRefsGlobals_EL",
    `∀ n l . n < LENGTH l ⇒
        (∀ a . EL n l = Refv a ⇒ domain (findVglobals a) ⊆ domain (findRefsGlobals l)) ∧
        (∀ vs . EL n l = Varray vs ⇒ domain (findVglobalsL vs) ⊆ domain (findRefsGlobals l))`,
    Induct >> rw[] 
    >- (Cases_on `l` >> fs[findRefsGlobals_def, domain_union])
    >- (Cases_on `l` >> fs[findRefsGlobals_def, domain_union])
    >> fs[EL] >> first_x_assum (qspec_then `TL l` mp_tac) >> rw[] >>
       `n < LENGTH (TL l)` by fs[LENGTH_TL] >> fs[] >> 
       Cases_on `l` >> fs[] >> 
       Cases_on `h` >> fs[findRefsGlobals_def, domain_union, SUBSET_DEF]
);

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
    globals_rel (reachable : num_set) (s : 'a flatSem$state) (t : 'a flatSem$state) ⇔ 
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
(*** TODO - MOVE TO REACHABILITY THEORY ***)

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

(* TODO - check if findAllGlobals or just findLookups necessary - may not care about initialisations *)

(* s = state, t = removed state *)
val flat_state_rel_def = Define `
    flat_state_rel reachable s t ⇔ s.clock = t.clock ∧ s.refs = t.refs ∧
    s.ffi = t.ffi ∧ globals_rel reachable s t ∧ 
    domain (findRefsGlobals s.refs) ⊆ domain reachable
`
val flat_state_rel_sym = Q.store_thm("flat_state_rel_sym",
    `∀ reachable s t . flat_state_rel reachable s t ⇔ flat_state_rel reachable t s`,
    rw[flat_state_rel_def] >> EQ_TAC >> rw[] >> rfs[] >> fs[globals_rel_sym]
);

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

val pmatch_Match_reachable = Q.store_thm ("pmatch_Match_reachable",
    `(∀ env refs p v l a reachable:num_set . pmatch env refs p v l = Match a ∧
        domain (findVglobalsL (MAP SND env.v)) ⊆ domain reachable ∧ 
        domain (findVglobals v) ⊆ domain reachable ∧ 
        domain (findVglobalsL (MAP SND l)) ⊆ domain reachable ∧ 
        domain (findRefsGlobals refs) ⊆ domain reachable
    ⇒ domain (findVglobalsL (MAP SND a)) ⊆ domain reachable)
  ∧ 
    (∀ env refs p vs l a reachable:num_set . pmatch_list env refs p vs l = Match a ∧
        domain (findVglobalsL (MAP SND env.v)) ⊆ domain reachable ∧ 
        domain (findVglobalsL vs) ⊆ domain reachable ∧ 
        domain (findVglobalsL (MAP SND l)) ⊆ domain reachable ∧ 
        domain (findRefsGlobals refs) ⊆ domain reachable
    ⇒ domain (findVglobalsL (MAP SND a)) ⊆ domain reachable)`
  ,
    ho_match_mp_tac pmatch_ind >> rw[pmatch_def] >> fs[findVglobals_def, domain_union]
    >- (Cases_on `store_lookup lnum refs` >> fs[] >> Cases_on `x` >> fs[] >>
        fs[semanticPrimitivesTheory.store_lookup_def] >>
        first_x_assum (qspec_then `reachable` match_mp_tac) >> rw[] >>
        imp_res_tac findRefsGlobals_EL >> metis_tac[SUBSET_TRANS])
    >- (Cases_on `pmatch env refs p v l` >> fs[domain_union])
);


(******************************************************** OTHER LEMMAS *********************************************************)

(**************************** IMPLEMENTATION LEMMAS *****************************)

val keep_Dlet = Q.store_thm("keep_Dlet",
    `∀ (reachable:num_set) h . ¬ keep reachable h ⇒ ∃ x . h = Dlet x`,
   Cases_on `h` >> rw[keep_def]
);
          

(******************************************************** MAIN PROOFS *********************************************************)

val findRefsGlobals_LUPDATE = Q.store_thm ("findRefsGlobals_LUPDATE",
    `∀ reachable:num_set refs n . n < LENGTH refs ∧ domain (findRefsGlobals refs) ⊆ domain reachable ⇒ 
    (∀ a . domain (findVglobals a) ⊆ domain reachable 
        ⇒ domain (findRefsGlobals (LUPDATE (Refv a) n refs)) ⊆ domain reachable) ∧
    (∀ vs . domain (findVglobalsL vs) ⊆ domain reachable 
        ⇒ domain (findRefsGlobals (LUPDATE (Varray vs) n  refs)) ⊆ domain reachable) ∧ 
    (∀ ws.  domain (findRefsGlobals (LUPDATE (W8array ws) n  refs)) ⊆ domain reachable)`,
    Induct_on `refs` >>  
    rw[] >>
    Cases_on `h` >> fs[findRefsGlobals_def, domain_union] >>
    Cases_on `n = 0` >> fs[LUPDATE_def, findRefsGlobals_def, domain_union] >>

    fs[domain_union, LUPDATE_def] >>
    
    
    (*
    MEM_LUPDATE_E
    MEM_LUPDATE
    LUPDATE_SEM
    lupdate_append
    lupdate_append2
    EL_UPDATE
    findRefsGlobals_EL 
    *)

cheat (* TODO *)
);

val findRefsGlobals_APPEND = Q.store_thm ("findRefsGlobals_APPEND",
    `∀ refs new .
        findRefsGlobals (refs ++ new) = union (findRefsGlobals refs) (findRefsGlobals new)`,
    Induct >> rw[] >> fs[findRefsGlobals_def] >> 
    Cases_on `h` >> fs[findRefsGlobals_def] >> fs[union_assoc]
    
);

val findVglobalsL_REPLICATE = Q.store_thm ("findVglobalsL_REPLICATE",
    `∀ n v vs . domain (findVglobalsL (REPLICATE n v)) ⊆  domain (findVglobals v)`,
    Induct >> fs[REPLICATE, findVglobals_def, domain_union]
);

val do_app_SOME_flat_state_rel = Q.store_thm("do_app_SOME_flat_state_rel",
    `∀ reachable state removed_state op l new_state result new_removed_state. 
        flat_state_rel reachable state removed_state ∧ op ≠ Opapp ∧ domain(findVglobalsL l) ⊆ domain reachable 
        ⇒ do_app state op l = SOME (new_state, result) 
            ⇒ ∃ new_removed_state . flat_state_rel reachable new_state new_removed_state ∧ 
                do_app removed_state op l = SOME (new_removed_state, result)`
  ,
    rw[] >> qpat_x_assum `flat_state_rel _ _ _` mp_tac >> simp[Once flat_state_rel_def] >> strip_tac >>
    Cases_on `op` >> fs[do_app_cases] >> rveq >> fs[] >> rw[] >> 
    fs[semanticPrimitivesTheory.store_assign_def, semanticPrimitivesTheory.store_v_same_type_def] >>
    fs[semanticPrimitivesTheory.store_alloc_def, semanticPrimitivesTheory.store_lookup_def] >>
    fs[flat_state_rel_def, globals_rel_def, findVglobals_def, domain_union, findRefsGlobals_def] >> rveq
    (* 19 subgoals *)
    >-  metis_tac[findRefsGlobals_LUPDATE]
    >- (fs[findRefsGlobals_APPEND, domain_union,findRefsGlobals_def, findVglobals_def] >> metis_tac[])
    >- (fs[findRefsGlobals_APPEND, domain_union,findRefsGlobals_def, findVglobals_def] >> metis_tac[])
    >- (qexists_tac `removed_state` >> fs[])
    >-  metis_tac[findRefsGlobals_LUPDATE]
    >- (qexists_tac `removed_state` >> fs[])
    >-  metis_tac[findRefsGlobals_LUPDATE]
    >-  metis_tac[findRefsGlobals_LUPDATE]
    >- (qexists_tac `removed_state` >> fs[])
    >- (qexists_tac `removed_state` >> fs[])
    >- (fs[findRefsGlobals_APPEND, domain_union,findRefsGlobals_def, findVglobals_def] >> 
        metis_tac[findVglobalsL_REPLICATE, SUBSET_DEF])
    >- (qexists_tac `removed_state` >> fs[])
    >- (
    
        cheat (* TODO, marginally more tricky than some other cases *))
    >- (qexists_tac `removed_state` >> fs[])
    >-  metis_tac[findRefsGlobals_LUPDATE]
    >- (reverse(rw[]) >- metis_tac[] >> Cases_on `n' < LENGTH removed_state.globals` >> 
        rveq >> fs[] >- fs[EL_APPEND1] >- fs[EL_APPEND2])
    >- (qexists_tac `removed_state with globals := LUPDATE (SOME v''''''') n removed_state.globals` >> fs[] >> 
        rw[] >- (fs[LUPDATE_SEM] >> metis_tac[]) >- metis_tac[]
        >- cheat (* TODO - this looks like a serious problem *))
    >- (fs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE])
    >- (
        qexists_tac `removed_state` >> fs[] >>
        rw[] >>
        cheat (* TODO - again, looks like a problem *)
        
        )

(* TODO - it seems for op = GlobalVarInit n/GlobalVarLookup n, we have problems 
    -> need an assumption that n is in reachable, which can only come from adding an assumption
        to evaluate_sing_keep_flat_state_rel_eq_lemma
    HOWEVER this requires all inits/lookups to be in the reachable set, which is not guaranteed
    by keep_def, which would generate such a constraint

    -> The only way to prove this seems to be to adjust the implementation so that 
        keep = T ⇒ ALL global vars are in the reachable set
        keep = F ⇒ NONE of the global vars are in the reachable set 
        so that we can assume findLoc e ⊆ reachable in evaluate_sing_keep_flat_state_rel_eq_lemma
        *)
);


val evaluate_sing_keep_flat_state_rel_eq_lemma = Q.store_thm("evaluate_sing_keep_flat_state_rel_eq_lemma",
    `(∀ env (state:'a flatSem$state) exprL new_state result reachable:num_set removed_state . 
        flatSem$evaluate env state exprL = (new_state, result) ∧ 
        (*EVERY (λ e. (inter (findLoc e) reachable) = LN ⇒ ¬isPure e) exprL ∧ *)env.exh_pat ∧ 
        flat_state_rel reachable state removed_state ∧ 
        domain (findEnvGlobals env) ⊆ domain reachable ∧  
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate env removed_state exprL = (new_removed_state, result) ∧ 
        flat_state_rel reachable new_state new_removed_state ∧ 
        domain (findSemPrimResGlobals result) ⊆ domain reachable)
   ∧ 
    (∀ env (state:'a flatSem$state) v patExp_list err_v new_state result reachable:num_set removed_state .
        evaluate_match env state v patExp_list err_v = (new_state, result) ∧
        (*EVERY (λ e. (inter (findLoc e) reachable) = LN ⇒ ¬isPure e) (MAP SND patExp_list) ∧*) env.exh_pat ∧ 
        domain (findVglobals v) ⊆ domain reachable ∧ 
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧ 
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state . 
        evaluate_match env removed_state v patExp_list err_v = (new_removed_state, result) ∧ 
        flat_state_rel reachable new_state new_removed_state ∧
        domain (findSemPrimResGlobals result) ⊆ domain reachable)`
      ,
        ho_match_mp_tac evaluate_ind >> rpt CONJ_TAC >> rpt GEN_TAC >> strip_tac 
        (* EVALUATE CASES *)
            (* EMPTY LIST CASE *)
        >- (fs[evaluate_def] >> rveq >> fs[findSemPrimResGlobals_def, findVglobals_def])
            (* NON_EMPTY, NON-SINGLETON LIST CASE *)
        >- (rpt gen_tac >> strip_tac >> qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> Cases_on `evaluate env state' [e1]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >> 
            Cases_on `evaluate env q (e2::es)` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `new_removed_state`] mp_tac) >> fs[] >>
            reverse(Cases_on `r` >> fs[]) >- (rw[] >> fs[])
            >- (strip_tac >> rw[] >> fs[findSemPrimResGlobals_def, findVglobals_def, domain_union] >>
                imp_res_tac evaluate_sing >> rveq >> rveq >> fs[findVglobals_def]))
    
        (* SINGLETON LIST CASES *)
            (* Lit - DONE!!! *)
        >- (fs[evaluate_def] >> rveq >> fs[] >> fs[findSemPrimResGlobals_def, findVglobals_def])
            (* Raise *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >> strip_tac >> 
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >>
            `r ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
            fs[] >>
            Cases_on `r` >> fs[] >>
            rveq >> fs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def, findResultGlobals_def] >>
            imp_res_tac evaluate_sing >> rveq >> rveq >> fs[findVglobals_def])
            (* Handle - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >>
            Cases_on `r` >> rw[] >> rfs[] >> 
            Cases_on `e'` >> rw[] >> rfs[] >> rveq >> rfs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] match_mp_tac) >> 
            fs[findSemPrimResGlobals_def, findResultGlobals_def])
            (* Con NONE - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `env.check_ctor` >> fs[] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def] >> simp[Once findVglobalsL_REVERSE])
            (* Con SOME - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            Cases_on `env.check_ctor ∧ (cn, LENGTH es) ∉ env.c` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def] >> simp[Once findVglobalsL_REVERSE])
            (* Var_local - DONE!!! *)
        >- (qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> strip_tac >> rveq >>
            Cases_on `ALOOKUP env.v n` >> fs[findSemPrimResGlobals_def, findVglobals_def] >>
            imp_res_tac ALOOKUP_MEM >> imp_res_tac findVglobalsL_domain_MEM >>
            fs[findEnvGlobals_def] >> fs[SUBSET_DEF])
            (* Fun - DONE!!! *)
        >- (qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> strip_tac >> rveq >>
            fs[findSemPrimResGlobals_def, findEnvGlobals_def, findVglobals_def])
            (* App *) 
        >- (
            rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> 
            Cases_on `r` >> fs[] >> strip_tac >> rveq >> rfs[] >>
            Cases_on `op = Opapp` >> fs[]
            >- (Cases_on `do_opapp (REVERSE a)` >> fs[] >>
                Cases_on `x` >> fs[] >>
                Cases_on `q.clock = 0` >> fs[]
                >- (rveq >> qpat_x_assum `flat_state_rel reachable new_state _` mp_tac >>
                    simp[Once flat_state_rel_def] >> strip_tac >> rveq >> 
                    fs[flat_state_rel_def, findSemPrimResGlobals_def, findResultGlobals_def])
                >- (first_x_assum (qspecl_then [`reachable`, `dec_clock new_removed_state`] mp_tac) >> fs[] >>
                    qpat_x_assum `flat_state_rel reachable q _` mp_tac >> simp[Once flat_state_rel_def] >>
                    strip_tac >> strip_tac >> qpat_x_assum `_ ⇒ _` match_mp_tac  >>
                    fs[flat_state_rel_def, globals_rel_def, dec_clock_def, findEnvGlobals_def] >> rfs[] >> rveq >> 
                    fs[] >> fs[do_opapp_def] >> EVERY_CASE_TAC >> fs[] >> rveq >> fs[findSemPrimResGlobals_def] >> 
                    fs[SWAP_REVERSE_SYM] >> fs[findVglobals_def, domain_union] >> fs[build_rec_env_def] >> 
                    fs[FOLDR_CONS_triple] >> fs[findVglobalsL_APPEND, domain_union] >> fs[MAP_MAP_o] >>
                    `MAP (SND o (λ (f,x,e). (f, Recclosure l l0 f))) l0 = 
                        MAP (λ (f,x,e). (Recclosure l l0 f)) l0` by (rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]) >>
                    fs[] >> metis_tac[findVglobals_MAP_Recclosure, SUBSET_TRANS]))
            >- ( 
                Cases_on `do_app q op (REVERSE a)` >> fs[] >>
                PairCases_on `x` >>
                fs[] >> rveq >>
                cheat (* TODO - this looks tricky *)
            )
        )


            (* If - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e1]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> strip_tac >> fs[] >>
            `r ≠ Rerr(Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
            Cases_on `r` >> fs[] >>
            Cases_on `do_if (HD a) e2 e3` >> fs[])
            (* Mat - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> strip_tac >> 
            `r ≠ Rerr(Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
            Cases_on `r` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `new_removed_state`] match_mp_tac) >> fs[] >>
            fs[findSemPrimResGlobals_def] >>
            imp_res_tac evaluate_sing >> rveq >> fs[] >> rveq >> fs[findVglobals_def])
            (* Let - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e1]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> strip_tac >>
            `r ≠ Rerr(Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
            Cases_on `r` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `new_removed_state`] match_mp_tac) >> fs[] >>
            fs[findEnvGlobals_def, libTheory.opt_bind_def] >>
            Cases_on `n` >> fs[] >>
            fs[findVglobals_def, domain_union] >>
            fs[findSemPrimResGlobals_def] >> imp_res_tac evaluate_sing >> 
            rveq >> fs[] >> rveq >> fs[findVglobals_def])
            (* Letrec *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
            strip_tac >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] match_mp_tac) >> fs[] >>
            fs[findEnvGlobals_def, build_rec_env_def] >>
            fs[FOLDR_CONS_triple] >> fs[findVglobalsL_APPEND, domain_union] >> fs[MAP_MAP_o] >>
            `MAP (SND o (λ (f,x,e). (f, Recclosure env.v funs f))) funs = 
                MAP (λ (f,x,e). (Recclosure env.v funs f)) funs` by (rw[MAP_EQ_f] >> PairCases_on `e'` >> fs[]) >>
            fs[] >> metis_tac[findVglobals_MAP_Recclosure, SUBSET_TRANS])
        
        (* EVALUATE_MATCH CASES *)
            (* EMPTY LIST CASE - DONE!!! *)
        >- (fs[evaluate_def])
            (* NON-EMPTY LIST CASE - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate_match _ _ _ _ _ =  _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `ALL_DISTINCT (pat_bindings p [])` >> fs[] >>
            strip_tac >> 
            `state'.refs = removed_state.refs` by fs[flat_state_rel_def] >> fs[] >> 
            Cases_on `pmatch env removed_state.refs p v []` >> fs[] >> 
            first_x_assum (qspecl_then [`reachable`, `removed_state`] match_mp_tac) >> fs[] >>
            fs[findEnvGlobals_def, findVglobalsL_APPEND, domain_union] >>
            drule (CONJUNCT1 pmatch_Match_reachable) >> disch_then drule >> 
            disch_then match_mp_tac >> fs[findVglobals_def] >> rw[] >> fs[flat_state_rel_def])
);

val evaluate_sing_keep_flat_state_rel_eq = Q.store_thm("evaluate_sing_keep_flat_state_rel_eq",
    `(∀ env (state:'a flatSem$state) exprL new_state result expr reachable removed_state . 
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧ exprL = [expr] ∧ 
        keep reachable (Dlet expr) ∧ env.exh_pat ∧ 
        flat_state_rel reachable state removed_state ∧ 
        domain (findEnvGlobals env) ⊆ domain reachable ∧  
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state . 
        evaluate (env with v := []) removed_state exprL = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧ 
        domain (findSemPrimResGlobals result) ⊆ domain reachable)`
      ,
        rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >> 
        drule (CONJUNCT1 evaluate_sing_keep_flat_state_rel_eq_lemma) >> fs[] >>
        strip_tac >> pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
        impl_tac >> fs[] >> fs[findEnvGlobals_def, findVglobals_def] >> metis_tac[]
);

val evaluate_dec_flat_state_rel = Q.store_thm("evaluate_dec_state_rel",
    `∀ env (state:'a flatSem$state) dec new_state new_ctors result reachable removed_state . 
        evaluate_dec env state dec = (new_state, new_ctors, result) ∧
        env.exh_pat ∧ (* TODO - new assumption, check if OK *)
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
            Cases_on `evaluate (env with v := []) state' [e]` >> fs[] >>
            first_x_assum (qspecl_then [`env`, `state'`, `q`, `r`, `e`, 
                `reachable`, `removed_state`] mp_tac) >> strip_tac >>
            fs[keep_def] >> rfs[] >> strip_tac >>
            `r ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
            qpat_x_assum `_ = (_,_,_) ` mp_tac >> fs[] >>
            EVERY_CASE_TAC >> fs[] >> rw[] >> fs[findResultGlobals_def, findSemPrimResGlobals_def])
);




(******************************************************)


val inter_union_empty = Q.store_thm("inter_union",
    `∀ a b c . isEmpty (inter (union a b) c) ⇔ isEmpty (inter a c) ∧ isEmpty (inter b c)`,
    rw[] >> EQ_TAC >> rw[] >> `wf (inter (union a b) c) ∧ wf (inter a c)` by metis_tac[wf_inter] >>
    fs[domain_empty] >> fs[EXTENSION] >> rw[] >> pop_assum (qspec_then `x` mp_tac) >> fs[domain_lookup] >>
    rw[] >> fs[lookup_inter, lookup_union] >> TRY(first_x_assum (qspec_then `x` mp_tac)) >> rw[] >>
    fs[lookup_inter, lookup_union] >> EVERY_CASE_TAC >> fs[]
);

val inter_insert_empty = Q.store_thm("inter_insert_empty",
    `∀ n t1 t2 . isEmpty (inter (insert n () t1) t2) ⇒ n ∉ domain t2 ∧ isEmpty(inter t1 t2)`,
    rw[] >> `∀ k . lookup k (inter (insert n () t1) t2) = NONE` by fs[lookup_def] 
    >- (fs[domain_lookup] >> rw[] >> fs[lookup_inter] >> pop_assum (qspec_then `n` mp_tac) >> 
        rw[] >> fs[] >> EVERY_CASE_TAC >> fs[])
    >- (`wf (inter t1 t2)` by metis_tac[wf_inter] >> fs[domain_empty] >> fs[EXTENSION] >> rw[] >> 
        pop_assum (qspec_then `x` mp_tac) >> rw[] >> first_x_assum (qspec_then `x` mp_tac) >> rw[] >>
        fs[domain_lookup, lookup_inter, lookup_insert] >> Cases_on `x = n` >> fs[] >> 
        Cases_on `lookup n t2` >> fs[] >> CASE_TAC)
);

val findLoc_EVERY_isEmpty = Q.store_thm("findLoc_EVERY_isEmpty",
    `∀ l reachable:num_set . EVERY (λ e . isEmpty (inter (findLoc e) reachable)) l ⇔ isEmpty (inter (findLocL l) reachable)`,
    Induct >- fs[Once findLoc_def, inter_def] >> fs[EVERY_DEF] >> rw[] >> EQ_TAC >> rw[] >> 
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >> fs[inter_union_empty]
);


val evaluate_flat_state_rel_lemma = Q.store_thm ("evaluate_flat_state_rel_lemma",
`(∀ env (state:'a flatSem$state) exprL new_state result reachable removed_state . 
        flatSem$evaluate env state exprL = (new_state, result) ∧ 
        EVERY isPure exprL ∧  
        EVERY (λ e. isEmpty (inter (findLoc e) reachable)) exprL ∧ env.exh_pat ∧ (* TODO - new assumptions, check if OK *)
        flat_state_rel reachable state removed_state ∧ 
        domain (findEnvGlobals env) ⊆ domain reachable ∧  
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧ ∃ values : flatSem$v list . result = Rval values ∧
      domain (findVglobalsL values) ⊆ domain reachable)
   ∧ 
    (∀ env (state:'a flatSem$state) v patExp_list err_v new_state result reachable removed_state .
        evaluate_match env state v patExp_list err_v = (new_state, result) ∧
        EVERY isPure (MAP SND patExp_list) ∧ 
        EVERY (λ e. isEmpty (inter (findLoc e) reachable)) (MAP SND patExp_list) ∧ env.exh_pat ∧ 
        domain (findVglobals v) ⊆ domain reachable ∧ (* TODO - new assumptions, check if OK *)
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧ 
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧ ∃ values : flatSem$v list . result = Rval values ∧ 
      domain (findVglobalsL values) ⊆ domain reachable)`
  , 
    ho_match_mp_tac evaluate_ind >> rpt CONJ_TAC >> rpt GEN_TAC >> strip_tac
    >| [
        (* EVALUATE_DECS_CASES *)
        
        (* EMPTY LIST CASE - DONE!!! *)
        fs[evaluate_def] >> rveq >> fs[findVglobals_def]
      ,
        (* NON-EMPTY, NON-SINGLETON LIST CASE - DONE!!! *) 
        rpt gen_tac >> strip_tac >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >> 
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e1]` >> fs[] >>
        Cases_on `r` >> fs[] 
        >- (Cases_on `evaluate env q (e2 :: es)` >> fs[] >> 
            first_x_assum drule >> disch_then drule >> 
            fs[] >> Cases_on `r` >> fs[]
            >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
                rw[] >> fs[findVglobals_def, domain_union] >>
                `LENGTH a = 1` by (imp_res_tac evaluate_sing >> fs[]) >>
                Cases_on `a` >> fs[findVglobals_def, domain_union])
            >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> 
                fs[] >> rw[] >> fs[] >> qpat_x_assum `EXISTS _ _` mp_tac >>
                once_rewrite_tac [GSYM NOT_EVERY] >> strip_tac))
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >> 
            rw[] >> fs[])

      , (* SINGLETON LIST CASES *)
    
        (* Lit - DONE!!! *)
        fs[evaluate_def] >> rveq >> fs[findVglobals_def]
      ,
        (* Raise - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >> 
        fs[evaluate_def] >> Cases_on `evaluate env state' [e]` >> fs[] >>
        Cases_on `r` >> fs[] >> 
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[isPure_def]
      ,
        (* Handle - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >> 
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e]` >> fs[] >>
        Cases_on `r` >> fs[]
        >- (rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> 
            fs[isPure_def] >> strip_tac >>
            qpat_x_assum `isEmpty _` mp_tac >>
            simp[Once findLoc_def] >>
            strip_tac >>
            qpat_x_assum `isEmpty _ ⇒ _` match_mp_tac >> fs[] >>
            imp_res_tac inter_union_empty)         
        >- (fs[isPure_def] >> qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >> 
            strip_tac >>
            `isEmpty(inter (findLocL (MAP SND patExp_list)) reachable) ∧ 
            isEmpty (inter (findLoc e) reachable)` by metis_tac[inter_union_empty] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> 
            fs[] >> strip_tac >> fs[])
      ,
        (* Con NONE - DONE!!! *) 
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        reverse(Cases_on `env.check_ctor`) >> fs[] >> fs[evaluate_def] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
        Cases_on `r` >> fs[]  
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> rveq >> 
            fs[isPure_def, findVglobals_def] >> fs[EVERY_REVERSE] >>
            simp[Once findVglobalsL_REVERSE] >> fs[isPure_EVERY_aconv] >> rfs[] >>
            qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
            strip_tac >> 
            fs[findLoc_EVERY_isEmpty])
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            rveq >> fs[isPure_def] >> fs[EVERY_REVERSE, isPure_EVERY_aconv] >>
            once_rewrite_tac [(GSYM NOT_EXISTS)] >> once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
            qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
            fs[findLoc_EVERY_isEmpty])
      ,
        (* Con SOME - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >> fs[evaluate_def] >> 
        Cases_on `env.check_ctor ∧ (cn, LENGTH es) ∉ env.c` >> fs[] >> fs[] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >> Cases_on `r` >> fs[] >>
        fs[isPure_def, isPure_EVERY_aconv, EVERY_REVERSE] >> rveq >> fs[findLoc_EVERY_isEmpty] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >> strip_tac
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> fs[findVglobals_def] >> simp[Once findVglobalsL_REVERSE])
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[EVERY_REVERSE, isPure_EVERY_aconv] >> once_rewrite_tac [(GSYM NOT_EXISTS)] >> 
            once_rewrite_tac [GSYM NOT_EVERY] >> fs[findLoc_EVERY_isEmpty])
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> fs[findVglobals_def] >> simp[Once findVglobalsL_REVERSE])
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
            fs[EVERY_REVERSE, isPure_EVERY_aconv] >> once_rewrite_tac [(GSYM NOT_EXISTS)] >> 
            once_rewrite_tac [GSYM NOT_EVERY] >> fs[findLoc_EVERY_isEmpty])
      ,
        (* Var_local - DONE!!! *)
        fs[evaluate_def] >> Cases_on `ALOOKUP env.v n` >> fs[] >> rveq >> fs[] >>
        fs[findVglobals_def, findEnvGlobals_def] >> imp_res_tac ALOOKUP_MEM >>
        imp_res_tac findVglobalsL_domain_MEM >> imp_res_tac SUBSET_TRANS
      ,
        (* Fun - DONE!!! *)
        qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >> fs[evaluate_def] >>
        rveq >> fs[findVglobals_def, domain_union, findEnvGlobals_def, findAllGlobals_def, isPure_def]
      ,
        (* App - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
        fs[isPure_def] >> qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
        strip_tac >> fs[] >> fs[EVERY_REVERSE] >> fs[findLoc_EVERY_isEmpty] >>
        Cases_on `r` >> fs[] 
        >- (Cases_on `op = Opapp` >> fs[isPure_def, dest_GlobalVarInit_def] >> 
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> strip_tac >> 
            Cases_on `op` >> fs[isPure_def, dest_GlobalVarInit_def, do_app_def] >>
            EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >>
            fs[isPure_EVERY_aconv] >> 
            imp_res_tac inter_insert_empty >>
            fs[] >> rfs[] >>
            fs[findVglobals_def, flat_state_rel_def] >> rw[] >> fs[] >>
            fs[globals_rel_def] >> rw[] >>
            fs[LUPDATE_SEM] >>
            Cases_on `n' = n` >> fs[])
        >- (rveq >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            once_rewrite_tac [(GSYM NOT_EXISTS)] >> once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
            Cases_on `op` >> fs[isPure_def, isPure_EVERY_aconv, dest_GlobalVarInit_def] >>
            imp_res_tac inter_insert_empty)
      ,
        (* If - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `evaluate env state' [e1]` >> fs[] >>
        fs[isPure_def] >> qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >>
        strip_tac >> 
        `isEmpty (inter (findLoc e1) reachable) ∧  isEmpty (inter (findLoc e2) reachable) ∧ 
            isEmpty (inter (findLoc e3) reachable)` by metis_tac[inter_union_empty] >>
        Cases_on `r` >> fs[] 
        >- (fs[do_if_def, Boolv_def] >> Cases_on `HD a` >> fs[] >> EVERY_CASE_TAC >> fs[] >> 
            rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[])
        >- (rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[])
      ,
        (* Mat - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e]` >> fs[] >> fs[isPure_def] >> 
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >> strip_tac >> 
        `isEmpty (inter (findLocL (MAP SND patExp_list)) reachable) ∧ 
            isEmpty (inter (findLoc e) reachable)` by metis_tac[inter_union_empty] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
        strip_tac >> Cases_on `r` >> fs[] >>  
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
        strip_tac >> fs[isPure_EVERY_aconv, findLoc_EVERY_isEmpty] >> rfs[] >>
        imp_res_tac evaluate_sing >> rveq >> fs[findVglobals_def]
      ,
        (* Let - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >>
        Cases_on `evaluate env state' [e1]` >> fs[isPure_def] >>
        fs[isPure_def] >> qpat_x_assum `isEmpty _ ` mp_tac >> simp[Once findLoc_def] >>
        strip_tac >> imp_res_tac inter_union_empty >>
        Cases_on `r` >> fs[]
        >- (first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> strip_tac >>
            fs[findEnvGlobals_def] >>
            qpat_x_assum `domain _ ⊆ domain _ ⇒ _` match_mp_tac >>
            fs[libTheory.opt_bind_def] >>
            Cases_on `n` >> fs[] >>
            fs[findVglobals_def, domain_union] >>
            imp_res_tac evaluate_sing >> rveq >> fs[findVglobals_def])
        >- (rveq >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[])
      ,
        (* Letrec - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
        strip_tac >> fs[isPure_def] >> rfs[] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >> strip_tac >>
        `isEmpty (inter (findLocL (MAP (SND o SND) funs)) reachable) ∧ 
            isEmpty (inter (findLoc e) reachable)` by metis_tac[inter_union_empty] >>
        fs[] >> qpat_x_assum `domain _ ⊆ domain _ ⇒ _` match_mp_tac >>
        fs[findEnvGlobals_def, build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
        fs[findVglobalsL_APPEND, domain_union] >> fs[MAP_MAP_o] >>
        `MAP (SND o (λ (f,x,e). (f, Recclosure env.v funs f))) funs = 
            MAP (λ (f,x,e). (Recclosure env.v funs f)) funs` by (rw[MAP_EQ_f] >> PairCases_on `e'` >> fs[]) >>
        fs[] >> metis_tac[findVglobals_MAP_Recclosure, SUBSET_TRANS] 

      , (* EVALUATE_MATCH CASES *)
    
        (* EMPTY LIST CASE - DONE!!! *)
        fs[evaluate_def]
      ,
        (* NON-EMPTY LIST CASE - DONE!!! *)
        rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >> 
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
        fs[evaluate_def] >> Cases_on `ALL_DISTINCT (pat_bindings p [])` >> fs[] >>
        Cases_on `pmatch env removed_state.refs p v []` >> fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
        impl_tac >> fs[] >> fs[findEnvGlobals_def, findVglobalsL_APPEND, domain_union] >>
        drule (CONJUNCT1 pmatch_Match_reachable) >> disch_then drule >> disch_then match_mp_tac >>
        fs[findVglobals_def] >> rw[] >> metis_tac[]
    ]
);


val evaluate_sing_notKeep_flat_state_rel = Q.store_thm("evaluate_sing_notKeep_state_rel",
    `(∀ env (state:'a flatSem$state) exprL new_state result expr reachable removed_state . 
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧ exprL = [expr] ∧ 
        ¬keep reachable (Dlet expr) ∧
        
        env.exh_pat ∧ (* TODO - new assumption, check if OK *)

        flat_state_rel reachable state removed_state ∧ 
        domain (findEnvGlobals env) ⊆ domain reachable ∧  
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧ ∃ value : flatSem$v . result = Rval [value] ∧
      domain (findVglobals value) ⊆ domain reachable)`
  ,
    rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >> 
    drule (CONJUNCT1 evaluate_flat_state_rel_lemma) >> fs[] >> disch_then drule >> disch_then drule >> fs[] >> 
    impl_tac >- EVAL_TAC
    >> fs[] >> rw[] >> imp_res_tac evaluate_sing >> fs[] >> fs[findVglobals_def]
); 




(**************************** FLAT_DECS_REMOVAL LEMMA *****************************)

val flat_decs_removal_lemma = Q.store_thm ("flat_decs_removal_lemma",
    `∀ env (state:'a flatSem$state) decs new_state new_ctors result reachable removed_decs removed_state . 
        evaluate_decs env state decs = (new_state, new_ctors, result) ∧ 
        result ≠ SOME (Rabort Rtype_error) ∧

        env.exh_pat ∧ (* TODO - new assumption, check if OK *)

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
        >- (
            fs[evaluate_decs_def] >> `∃ r . evaluate_dec env state' h = r` by simp[] >> 
            PairCases_on `r` >> fs[] >> `r2 ≠ SOME (Rabort Rtype_error)` by (CCONTR_TAC >> fs[]) >>
            drule evaluate_dec_flat_state_rel >> rpt (disch_then drule) >> rw[] >> fs[] >> 
            Cases_on `r2` >> fs[] >> rw[] >> EVERY_CASE_TAC >> first_x_assum drule >> fs[] >> 
            rveq >> disch_then drule >> reverse(impl_tac) >- rw[] >> fs[findEnvGlobals_def] >>
            imp_res_tac decsClosed_reduce)
       >>   reverse(EVERY_CASE_TAC) >> fs[] >> rveq >> rename1 `_ _ decs = (n_state, ctors, res)` >>
            imp_res_tac keep_Dlet >> rveq >> 
            fs[Once evaluate_dec_def] >> EVERY_CASE_TAC >> fs[] >> 
            rveq >> rw[UNION_EMPTY] >> 
            `env with c updated_by $UNION {} = env` by fs[environment_component_equality] >> fs[]
            >- (drule evaluate_sing_notKeep_flat_state_rel >> fs[] >> strip_tac >> 
                pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
                strip_tac >> fs[])
            >>  first_x_assum match_mp_tac >> fs[] >> asm_exists_tac >> fs[] >> 
                imp_res_tac decsClosed_reduce >> fs[] >> 
                drule evaluate_sing_notKeep_flat_state_rel >> fs[]
);

val flat_removal_thm = Q.store_thm ("flat_removal_thm",
    `∀ env (state:'a flatSem$state) decs new_state new_ctors result roots tree reachable removed_decs . 
        evaluate_decs env state decs = (new_state, new_ctors, result) ∧ 
        result ≠ SOME (Rabort Rtype_error) ∧
        env.exh_pat ∧ 
        (roots, tree) = analyseCode decs ∧
        reachable = closure_spt roots (mk_wf_set_tree tree) ∧ 
        removeUnreachable reachable decs = removed_decs ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧ 
        domain (findRefsGlobals state.refs) ⊆ domain reachable
    ⇒ ∃ s . 
        evaluate_decs env state removed_decs = (s, new_ctors, result)`
  ,
    rpt strip_tac >> drule flat_decs_removal_lemma >> rpt (disch_then drule) >> strip_tac >>
    pop_assum (qspec_then `state'` mp_tac) >> fs[] >> reverse(impl_tac) >- (rw[] >> fs[])
    >>  qspecl_then [`decs`, `roots`, `mk_wf_set_tree tree`, `tree`] mp_tac analysis_reachable_thm >>
        impl_tac >> rw[]
        >- fs[flat_state_rel_def, globals_rel_refl]
        >- (fs[decsClosed_def] >> rw[] >> `(r,t) = (roots, tree)` by metis_tac[] >> fs[] >> rveq 
            >- (rw[SUBSET_DEF] >> qexists_tac `x` >> fs[isReachable_def])
            >- (qexists_tac `n'` >> fs[isReachable_def] >> metis_tac[transitive_RTC, transitive_def]))
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

val _ = export_theory();

