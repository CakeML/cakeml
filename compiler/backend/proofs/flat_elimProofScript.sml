open preamble sptreeTheory flatLangTheory reachabilityTheory flat_elimTheory
     flatSemTheory flatPropsTheory

val _ = new_theory "flat_elimProof";

val grammar_ancestry =
  ["flat_elim", "reachability", "flatSem", "flatLang", "flatProps",
    "misc", "ffi", "sptree"];
val _ = set_grammar_ancestry grammar_ancestry;


(******************************************************** STATE RELATION *********************************************************)

(**************************** FIND GLOBALS *****************************)

val v_size_map_snd = Q.store_thm("exp_size_map_snd",
    `∀ vvs . v3_size (MAP SND vvs) ≤ v1_size vvs`,
    Induct >> rw[v_size_def] >>
    Cases_on `v3_size (MAP SND vvs) = v1_size vvs` >>
    `v_size (SND h) ≤ v2_size h` by (Cases_on `h` >> rw[v_size_def]) >> rw[]
);


val findVglobals_def = tDefine "findVglobals" `
    (findVglobals (Conv _ vl) = (findVglobalsL vl):num_set) ∧
    (findVglobals (Closure vvs _ e) =
        union (findVglobalsL (MAP SND vvs)) (findLookups e)) ∧
    (findVglobals (Recclosure vvs vves _) =
        union (findVglobalsL (MAP SND vvs)) (findLookupsL (MAP (SND o SND) vves))) ∧
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

(*** THEOREMS ***)

val findVglobalsL_APPEND = Q.store_thm("findVglobalsL_APPEND",
    `∀ l1 l2 . findVglobalsL (l1 ++ l2) = union (findVglobalsL l1) (findVglobalsL l2)`,
    Induct >> fs[findVglobals_def] >> fs[union_assoc]
);

val findVglobalsL_REVERSE = Q.store_thm("findVglobalsL_REVERSE",
    `∀ l . findVglobalsL l = findVglobalsL (REVERSE l)`,
    Induct >> fs[findVglobals_def] >>
    fs[findVglobalsL_APPEND, union_num_set_sym, findVglobals_def]
);

val findVglobalsL_MEM = Q.store_thm("findVglobalsL_MEM",
    `∀ k v vs . MEM (k, v) vs ⇒ domain (findVglobals v) ⊆ domain (findVglobalsL (MAP SND vs))`,
    Induct_on `vs` >> rw[] >> fs[findVglobals_def, domain_union] >> res_tac >> fs[SUBSET_DEF]
);

val findVglobalsL_EL = Q.store_thm("findVglobalsL_EL",
    `∀ n vs . n < LENGTH vs ⇒
    domain (findVglobals (EL n vs)) ⊆ domain(findVglobalsL vs)`,
    Induct >> fs[EL] >> rw[] >> Cases_on `vs` >> fs[findVglobals_def, domain_union] >>
    Cases_on `n = 0` >> fs[] >>  fs[EXTENSION, SUBSET_DEF]
);

val findVglobals_MAP_Recclosure = Q.store_thm("findVglobals_MAP_Recclosure",
    `∀ (funs:(tvarN,tvarN # flatLang$exp) alist) v l .
        domain (findVglobalsL (MAP (λ (f,x,e). Recclosure v l f) funs)) ⊆
        domain (findVglobalsL (MAP SND v)) ∪ domain (findLookupsL (MAP (SND o SND) l))`,
    Induct >> fs[findVglobals_def] >> rw[domain_union] >>
    PairCases_on `h` >> fs[findVglobals_def, domain_union]
);

val findVglobalsL_REPLICATE = Q.store_thm ("findVglobalsL_REPLICATE",
    `∀ n v vs . domain (findVglobalsL (REPLICATE n v)) ⊆  domain (findVglobals v)`,
    Induct >> fs[REPLICATE, findVglobals_def, domain_union]
);

val findVglobalsL_LUPDATE = Q.store_thm ("findVglobalsL_LUPDATE",
    `∀ n vs (reachable:num_set) v . n < LENGTH vs ∧
    domain (findVglobalsL vs) ⊆ domain reachable ∧ domain (findVglobals v) ⊆ domain reachable
    ⇒ domain (findVglobalsL (LUPDATE v n vs)) ⊆ domain reachable`,
    Induct_on `vs` >> rw[] >> Cases_on `n` >> fs[LUPDATE_def] >> fs[findVglobals_def, domain_union]
);

val findVglobals_v_to_list = Q.store_thm("findVglobals_v_to_list",
    `∀ x reachable xs .
        domain (findVglobals x) ⊆ domain reachable ∧ v_to_list x = SOME xs
    ⇒ domain (findVglobalsL xs) ⊆ domain reachable`,
    recInduct v_to_list_ind >> fs[v_to_list_def, findVglobals_def, domain_union] >> rw[] >>
    Cases_on `v_to_list v2` >> fs[] >> rveq >>
    fs[findVglobals_def, domain_union] >> metis_tac[]
);

val findVglobals_list_to_v = Q.store_thm("findVglobals_list_to_v",
    `∀ xs reachable x .
        domain (findVglobalsL xs) ⊆ domain reachable ∧ list_to_v xs = x
    ⇒ domain (findVglobals x) ⊆ domain reachable`,
    Induct >> fs[list_to_v_def, findVglobals_def, domain_union]
);

(******** FINDREFSGLOBALS ********)

val findRefsGlobals_def = Define `
    (findRefsGlobals (Refv a::t) = union (findVglobals a) (findRefsGlobals t)) ∧
    (findRefsGlobals (Varray l::t) = union (findVglobalsL l) (findRefsGlobals t)) ∧
    (findRefsGlobals (_::t) = findRefsGlobals t) ∧
    (findRefsGlobals [] = LN)
`

val findRefsGlobals_ind = theorem "findRefsGlobals_ind";

(*** THEOREMS ***)

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

val findRefsGlobals_MEM = Q.store_thm("findRefsGlobals_MEM",
    `∀ refs reachable:num_set . domain (findRefsGlobals refs) ⊆ domain reachable ⇒
        (∀ a . MEM (Refv a) refs ⇒ domain (findVglobals a) ⊆ domain reachable) ∧
        (∀ vs . MEM (Varray vs) refs ⇒ domain (findVglobalsL vs) ⊆ domain reachable)`,
    Induct >> rw[] >> fs[findRefsGlobals_def, domain_union] >>
    Cases_on `h` >> fs[findRefsGlobals_def, domain_union]
);

val findRefsGlobals_LUPDATE = Q.store_thm ("findRefsGlobals_LUPDATE",
    `∀ reachable:num_set refs n . n < LENGTH refs ∧ domain (findRefsGlobals refs) ⊆ domain reachable ⇒
    (∀ a . domain (findVglobals a) ⊆ domain reachable
        ⇒ domain (findRefsGlobals (LUPDATE (Refv a) n refs)) ⊆ domain reachable) ∧
    (∀ vs . domain (findVglobalsL vs) ⊆ domain reachable
        ⇒ domain (findRefsGlobals (LUPDATE (Varray vs) n  refs)) ⊆ domain reachable) ∧
    (∀ ws.  domain (findRefsGlobals (LUPDATE (W8array ws) n  refs)) ⊆ domain reachable)`,
    Induct_on `refs` >> rw[] >> Cases_on `h` >> fs[findRefsGlobals_def, domain_union] >>
    Cases_on `n = 0` >> fs[LUPDATE_def, findRefsGlobals_def, domain_union] >>
    fs[domain_union, LUPDATE_def] >> Cases_on `n` >> fs[] >>
    fs[LUPDATE_def, findRefsGlobals_def, domain_union]
);

val findRefsGlobals_APPEND = Q.store_thm ("findRefsGlobals_APPEND",
    `∀ refs new .
        findRefsGlobals (refs ++ new) = union (findRefsGlobals refs) (findRefsGlobals new)`,
    Induct >> rw[] >> fs[findRefsGlobals_def] >>
    Cases_on `h` >> fs[findRefsGlobals_def] >> fs[union_assoc]

);

(******** FINDENVGLOBALS ********)

val findEnvGlobals_def = Define `
    findEnvGlobals env = findVglobalsL (MAP SND env.v)
`

(******** FINDRESULTGLOBALS ********)

val findResultGlobals_def = Define `
    (findResultGlobals (SOME (Rraise v)) = findVglobals v) ∧
    (findResultGlobals _ = LN)
`

val findResultGlobals_ind = theorem "findResultGlobals_ind";

(******** FINDSEMPRIMRESGLOBALS ********)

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
        ⇒ EL n s.globals = EL n t.globals) ∧
        (∀ n x . n < LENGTH t.globals ∧ EL n t.globals = SOME x ⇒ EL n s.globals = SOME x) ∧
        (∀ n . n < LENGTH t.globals ∧ EL n s.globals = NONE ⇒ EL n t.globals = NONE)

     ∧    (∀ n x . n ∈ domain reachable ∧ n < LENGTH t.globals ∧ EL n t.globals = SOME x ⇒
            domain (findVglobals x) ⊆ domain reachable)
`
val globals_rel_trans = Q.store_thm("globals_rel_trans",
    `∀ reachable s1 s2 s3 .
        globals_rel reachable s1 s2 ∧ globals_rel reachable s2 s3
        ⇒ globals_rel reachable s1 s3`,
    rw[globals_rel_def]
);

(**************************** DECSCLOSED *****************************)

val decsClosed_def = Define `
    decsClosed (reachable : num_set) decs ⇔  ∀ r t . analyseCode decs = (r,t)
    ⇒ domain r ⊆ domain reachable ∧
      (∀ n m . n ∈ domain reachable ∧ isReachable (mk_wf_set_tree t) n m
      ⇒ m ∈ domain reachable)
`

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

val decsClosed_reduce_HD = Q.store_thm("decsClosed_reduce_HD",
    `∀ reachable h t . decsClosed reachable (h::t) ⇒ decsClosed reachable [h]`,
    fs[decsClosed_def] >> rw[] >> Cases_on `h` >> fs[analyseCode_def] >> Cases_on `analyseExp e` >>
    fs[codeAnalysis_union_def, domain_union] >> rveq >> fs[domain_def]
    >- (Cases_on `analyseCode t` >> fs[codeAnalysis_union_def, domain_union])
    >- (fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
        Cases_on `analyseCode t` >> fs[codeAnalysis_union_def, domain_union] >>
        imp_res_tac isReachable_wf_set_tree_num_set_tree_union >>
        pop_assum (qspec_then `r` mp_tac) >> strip_tac >> res_tac)
    >- (fs[EVAL ``mk_wf_set_tree LN``] >> imp_res_tac reachable_domain >> fs[domain_def])
    >- (fs[EVAL ``mk_wf_set_tree LN``] >> imp_res_tac reachable_domain >> fs[domain_def])
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


(******************************************************** OTHER LEMMAS *********************************************************)

(**************************** FLATLANG LEMMAS *****************************)

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


val findVglobals_list_to_v_APPEND = Q.store_thm("findVglobals_list_to_v_APPEND",
    `∀ xs reachable ys .
        domain (findVglobalsL xs) ⊆ domain reachable ∧ domain(findVglobalsL ys) ⊆ domain reachable
    ⇒ domain (findVglobals (list_to_v (xs ++ ys))) ⊆ domain reachable`,
    Induct >> fs[list_to_v_def, findVglobals_def, domain_union] >>
    metis_tac[findVglobals_list_to_v]
);

val findVglobals_Unitv = Q.store_thm("findVglobals_Unitv[simp]",
  `findVglobals (Unitv cc) = LN`,
  EVAL_TAC);

val do_app_SOME_flat_state_rel = Q.store_thm("do_app_SOME_flat_state_rel",
    `∀ reachable state removed_state op l new_state result new_removed_state.
        flat_state_rel reachable state removed_state ∧ op ≠ Opapp ∧
        domain(findVglobalsL l) ⊆ domain reachable ∧ domain (findLookups (App tra op [])) ⊆ domain reachable
        ⇒ do_app cc state op l = SOME (new_state, result) ∧ result ≠ Rerr (Rabort Rtype_error)
            ⇒ ∃ new_removed_state . flat_state_rel reachable new_state new_removed_state ∧
                do_app cc removed_state op l = SOME (new_removed_state, result) ∧
                domain (findSemPrimResGlobals (list_result result)) ⊆ domain reachable`,

    rw[] >> qpat_x_assum `flat_state_rel _ _ _` mp_tac >> simp[Once flat_state_rel_def] >> strip_tac >>
    `∃ this_case . this_case op` by (qexists_tac `K T` >> simp[]) >>
    reverse (Cases_on `op`) >> fs[]
    >- (fs[do_app_def] >> Cases_on `l` >> fs[findVglobals_def] >>
        rveq >> fs[flat_state_rel_def] >>
        fs[findLookups_def, dest_GlobalVarLookup_def, findSemPrimResGlobals_def] >>
        Cases_on `EL n new_state.globals` >> fs[] >> res_tac >>
        Cases_on `EL n removed_state.globals` >> fs[findVglobals_def] >>
        fs[globals_rel_def] >> res_tac >> fs[] >> rveq >> metis_tac[])
    >- (fs[do_app_def] >> Cases_on `l` >> fs[findVglobals_def] >>
        Cases_on `t` >> fs[] >>
        rveq >> fs[flat_state_rel_def, globals_rel_def] >> rfs[] >>
        fs[EL_LUPDATE] >> rw[] >>
        fs[findSemPrimResGlobals_def, findVglobals_def] >>
        metis_tac[]) >>
    fs[do_app_cases] >> rveq >> fs[] >> rw[] >>
    fs[findSemPrimResGlobals_def, findVglobals_def, findResultGlobals_def] >>
    fs[semanticPrimitivesTheory.store_assign_def, semanticPrimitivesTheory.store_v_same_type_def, subscript_exn_v_def] >>
    fs[semanticPrimitivesTheory.store_alloc_def, semanticPrimitivesTheory.store_lookup_def, chr_exn_v_def, Boolv_def, div_exn_v_def] >>
    fs[flat_state_rel_def, findVglobals_def, domain_union, findRefsGlobals_def] >> rveq >> rfs[globals_rel_def]
    (* 21 subgoals *)
    >- (rw[] >> Cases_on `n' < LENGTH removed_state.globals` >> rveq >> fs[]
        >- fs[EL_APPEND1] >- fs[EL_APPEND2] >- fs[EL_APPEND1] >- fs[EL_APPEND2] >- metis_tac[EL_APPEND1]
        >- (fs[EL_APPEND2] >> `n' - LENGTH removed_state.globals < n` by fs[] >> metis_tac[EL_REPLICATE])
        >- (fs[EL_APPEND1] >> metis_tac[])
        >- (fs[EL_APPEND2] >> `n' - LENGTH removed_state.globals < n` by fs[] >> fs[EL_REPLICATE]))
    >-  metis_tac[findRefsGlobals_LUPDATE]
    >-  metis_tac[findVglobals_v_to_list, findVglobals_list_to_v_APPEND]
    >- (qsuff_tac `domain (findVglobalsL (LUPDATE v'''''' (Num (ABS i''''''')) vs)) ⊆ domain reachable`
        >-  metis_tac[findRefsGlobals_LUPDATE]
        >>  match_mp_tac findVglobalsL_LUPDATE >> fs[] >> imp_res_tac EL_MEM >> rfs[] >>
            fs[findRefsGlobals_def] >> metis_tac[findRefsGlobals_MEM])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (imp_res_tac findRefsGlobals_EL >>
        `domain (findVglobals (EL (Num (ABS i'''''')) vs)) ⊆ domain (findVglobalsL vs)` by
            (match_mp_tac findVglobalsL_EL >> decide_tac) >> metis_tac[SUBSET_TRANS])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (rw[] >- metis_tac[] >> fs[findRefsGlobals_APPEND, domain_union, findRefsGlobals_def] >>
        metis_tac[findVglobalsL_REPLICATE, SUBSET_DEF])
    >- (`Num (ABS i''''') < LENGTH vs'` by fs[] >>  metis_tac[findVglobalsL_EL, SUBSET_DEF])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (metis_tac[findVglobals_v_to_list, SUBSET_DEF])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (rw[] >> metis_tac[findRefsGlobals_LUPDATE])
    >- (rw[] >> metis_tac[findRefsGlobals_LUPDATE])
    >- (rw[] >> metis_tac[findRefsGlobals_LUPDATE])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (qexists_tac `removed_state` >> fs[] >> fs[])
    >- (fs[findRefsGlobals_APPEND, domain_union, findRefsGlobals_def] >> metis_tac[])
    >- (metis_tac[findRefsGlobals_EL, SUBSET_DEF])
    >- (rw[] >> fs[findRefsGlobals_APPEND, findRefsGlobals_def, findVglobals_def, domain_union] >> res_tac)
    >- (rw[] >> metis_tac[findRefsGlobals_LUPDATE])
);

(******************************************************** MAIN LEMMAS *********************************************************)

(**************************** CASE: keep reachable h *****************************)

(******** EVALUATE MUTUAL INDUCTION ********)

val evaluate_sing_keep_flat_state_rel_eq_lemma = Q.store_thm("evaluate_sing_keep_flat_state_rel_eq_lemma",
    `(∀ env (state:'a flatSem$state) exprL new_state result reachable:num_set removed_state .
        flatSem$evaluate env state exprL = (new_state, result) ∧
        domain (findLookupsL exprL) ⊆ domain reachable ∧
        env.exh_pat ∧
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
        domain (findLookupsL (MAP SND patExp_list)) ⊆ domain reachable ∧
        env.exh_pat ∧
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
            simp[evaluate_def] >> Cases_on `evaluate env state' [e1]` >> fs[findLookups_def, domain_union] >>
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
        >- (rpt gen_tac >> strip_tac >> fs[findLookups_def] >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >> strip_tac >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >>
            `r ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
            fs[] >> Cases_on `r` >> fs[] >> rveq >> fs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def, findResultGlobals_def] >>
            imp_res_tac evaluate_sing >> rveq >> rveq >> fs[findVglobals_def])
            (* Handle - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >>
            Cases_on `evaluate env state' [e]` >> fs[] >>
            fs[findLookups_def, domain_union] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >>
            Cases_on `r` >> rw[] >> rfs[] >>
            Cases_on `e'` >> rw[] >> rfs[] >> rveq >> rfs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] match_mp_tac) >>
            fs[findSemPrimResGlobals_def, findResultGlobals_def])
            (* Con NONE - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def] >>
            Cases_on `env.check_ctor` >> fs[] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> simp[Once findLookupsL_REVERSE] >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def] >> simp[Once findVglobalsL_REVERSE])
            (* Con SOME - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            Cases_on `env.check_ctor ∧ (cn, LENGTH es) ∉ env.c` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> simp[Once findLookupsL_REVERSE] >> fs[] >>
            strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
            fs[findSemPrimResGlobals_def, findVglobals_def] >> simp[Once findVglobalsL_REVERSE])
            (* Var_local - DONE!!! *)
        >- (qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> strip_tac >> rveq >> fs[findLookups_def] >>
            Cases_on `ALOOKUP env.v n` >> fs[findSemPrimResGlobals_def, findVglobals_def] >>
            imp_res_tac ALOOKUP_MEM >> imp_res_tac findVglobalsL_MEM >>
            fs[findEnvGlobals_def] >> fs[SUBSET_DEF])
            (* Fun - DONE!!! *)
        >- (qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> strip_tac >> rveq >>
            fs[findSemPrimResGlobals_def, findEnvGlobals_def, findVglobals_def] >>
            fs[domain_union, findLookups_def])
            (* App *)
        >- (
            rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def] >>
            Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> simp[Once findLookupsL_REVERSE] >> fs[] >>
            strip_tac >> fs[] >>
            `domain (findLookupsL es) ⊆ domain reachable` by (Cases_on `op` >> fs[dest_GlobalVarLookup_def] >> fs[domain_insert]) >>
            fs[] >>
            Cases_on `r` >> fs[] >> strip_tac >> rveq >> fs[] >> rfs[] >>
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
                    fs[do_opapp_def] >> EVERY_CASE_TAC >> fs[] >> rveq >> fs[findSemPrimResGlobals_def] >>
                    fs[SWAP_REVERSE_SYM, findVglobals_def, domain_union] >> rw[]
                    >- (fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
                        imp_res_tac ALOOKUP_MEM >>
                        `MEM r (MAP (SND o SND) l0)` by (fs[MEM_MAP] >> qexists_tac `(s,q'',r)` >> fs[]) >>
                        imp_res_tac findLookupsL_MEM >> rw[] >>
                        metis_tac[SUBSET_TRANS])
                    >- (fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >> fs[findVglobalsL_APPEND, domain_union] >>
                        fs[MAP_MAP_o] >>
                        `MAP (SND o (λ (f,x,e). (f, Recclosure l l0 f))) l0 =
                        MAP (λ (f,x,e). (Recclosure l l0 f)) l0` by (rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]) >> fs[] >>
                        `domain (findVglobalsL (MAP (λ(f,x,e). Recclosure l l0 f) l0)) ⊆ domain(findVglobalsL (MAP SND l)) ∪
                        domain (findLookupsL (MAP (SND o SND) l0))` by metis_tac[findVglobals_MAP_Recclosure] >>
                        fs[SUBSET_DEF, EXTENSION] >> metis_tac[])
                    >- (fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
                        imp_res_tac ALOOKUP_MEM >>
                        `MEM r (MAP (SND o SND) l0)` by (fs[MEM_MAP] >> qexists_tac `(s,q'',r)` >> fs[]) >>
                        imp_res_tac findLookupsL_MEM >> rw[] >>
                        metis_tac[SUBSET_TRANS])
                    >- (fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >> fs[findVglobalsL_APPEND, domain_union] >>
                        fs[MAP_MAP_o] >>
                        `MAP (SND o (λ (f,x,e). (f, Recclosure l l0 f))) l0 =
                        MAP (λ (f,x,e). (Recclosure l l0 f)) l0` by (rw[MAP_EQ_f] >> PairCases_on `e` >> fs[]) >> fs[] >>
                        `domain (findVglobalsL (MAP (λ(f,x,e). Recclosure l l0 f) l0)) ⊆ domain(findVglobalsL (MAP SND l)) ∪
                        domain (findLookupsL (MAP (SND o SND) l0))` by metis_tac[findVglobals_MAP_Recclosure] >>
                        fs[SUBSET_DEF, EXTENSION] >> metis_tac[]))
                )
            >- (Cases_on `do_app env.check_ctor q op (REVERSE a)` >> fs[] >> PairCases_on `x` >> fs[] >> rveq >>
                drule (GEN_ALL do_app_SOME_flat_state_rel) >>  fs[findLookups_def] >> disch_then drule >> strip_tac >>
                pop_assum (qspecl_then [`env.check_ctor`, `REVERSE a`, `new_state`, `x1`] mp_tac) >> simp[Once findVglobalsL_REVERSE] >>
                fs[] >> strip_tac >>
                `domain (case dest_GlobalVarLookup op of NONE => LN | SOME n => insert n () LN) ⊆ domain reachable`
                    by (Cases_on `dest_GlobalVarLookup op` >> fs[]) >> fs[findSemPrimResGlobals_def] >> rfs[]))
            (* If - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
            Cases_on `evaluate env state' [e1]` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            strip_tac >> strip_tac >> fs[] >>
            `r ≠ Rerr(Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
            Cases_on `r` >> fs[] >>
            Cases_on `do_if (HD a) e2 e3` >> fs[] >>
            fs[do_if_def] >> EVERY_CASE_TAC >> fs[])
            (* Mat - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
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
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
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
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
            Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
            strip_tac >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] match_mp_tac) >> fs[] >>
            fs[findEnvGlobals_def, build_rec_env_def] >>
            fs[FOLDR_CONS_triple] >> fs[findVglobalsL_APPEND, domain_union] >> fs[MAP_MAP_o] >>
            `MAP (SND o (λ (f,x,e). (f, Recclosure env.v funs f))) funs =
                MAP (λ (f,x,e). (Recclosure env.v funs f)) funs` by (rw[MAP_EQ_f] >> PairCases_on `e'` >> fs[]) >>
            `domain (findVglobalsL (MAP (SND o (λ(f,x,e). (f, Recclosure env.v funs f))) funs)) ⊆ domain (findVglobalsL (MAP SND env.v)) ∪
                domain (findLookupsL (MAP (SND o SND) funs))` by metis_tac[findVglobals_MAP_Recclosure] >>
            fs[SUBSET_DEF] >> metis_tac[])
        (* EVALUATE_MATCH CASES *)
            (* EMPTY LIST CASE - DONE!!! *)
        >- (fs[evaluate_def])
            (* NON-EMPTY LIST CASE - DONE!!! *)
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `evaluate_match _ _ _ _ _ =  _` mp_tac >>
            simp[evaluate_def] >> fs[findLookups_def, domain_union] >>
            Cases_on `ALL_DISTINCT (pat_bindings p [])` >> fs[] >>
            strip_tac >>
            `state'.refs = removed_state.refs` by fs[flat_state_rel_def] >> fs[] >>
            Cases_on `pmatch env removed_state.refs p v []` >> fs[] >>
            first_x_assum (qspecl_then [`reachable`, `removed_state`] match_mp_tac) >> fs[] >>
            fs[findEnvGlobals_def, findVglobalsL_APPEND, domain_union] >>
            drule (CONJUNCT1 pmatch_Match_reachable) >> disch_then drule >>
            disch_then match_mp_tac >> fs[findVglobals_def] >> rw[] >> fs[flat_state_rel_def])
);

(******** EVALUATE SPECIALISATION ********)

val evaluate_sing_keep_flat_state_rel_eq = Q.store_thm("evaluate_sing_keep_flat_state_rel_eq",
    `∀ env (state:'a flatSem$state) exprL new_state result expr reachable removed_state .
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧ exprL = [expr] ∧
        keep reachable (Dlet expr) ∧ env.exh_pat ∧
        domain(findLookups expr) ⊆ domain reachable ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate (env with v := []) removed_state exprL = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state`
      ,
        rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
        drule (CONJUNCT1 evaluate_sing_keep_flat_state_rel_eq_lemma) >> fs[] >>
        strip_tac >> pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
        impl_tac >> fs[] >> simp[findEnvGlobals_def, findVglobals_def, Once findLookups_def] >>
        simp[EVAL ``findLookupsL []``] >> rw[] >> fs[]
);

(******** EVALUATE_DEC ********)

val evaluate_dec_flat_state_rel = Q.store_thm("evaluate_dec_flat_state_rel",
    `∀ env (state:'a flatSem$state) dec new_state new_ctors result reachable removed_state .
        evaluate_dec env state dec = (new_state, new_ctors, result) ∧
        env.exh_pat ∧
        decsClosed reachable [dec] ∧
        flat_state_rel reachable state removed_state ∧ keep reachable dec ∧
        result ≠ SOME (Rabort Rtype_error) ∧
        domain (findEnvGlobals env) ⊆ domain reachable
    ⇒ ∃ new_removed_state .
        evaluate_dec env removed_state dec = (new_removed_state, new_ctors, result) ∧
        flat_state_rel reachable new_state new_removed_state`
      ,
        rw[] >> qpat_x_assum `evaluate_dec _ _ _ = _` mp_tac >>
        reverse(Induct_on `dec`) >> fs[evaluate_dec_def] >> strip_tac >> strip_tac >>
        fs[keep_def]
        >- (reverse(Cases_on `env.check_ctor`) >> fs[is_fresh_exn_def] >>
            rw[] >> fs[findResultGlobals_def])
        >- (reverse(Cases_on `env.check_ctor`) >> fs[is_fresh_exn_def] >>
            rw[] >> fs[findResultGlobals_def]) >>
        strip_tac >> strip_tac >> assume_tac evaluate_sing_keep_flat_state_rel_eq >> fs[] >>
        Cases_on `evaluate (env with v := []) state' [e]` >> fs[] >>
        first_x_assum (qspecl_then [`env`, `state'`, `q`, `r`, `e`,
            `reachable`, `removed_state`] mp_tac) >> strip_tac >>
        fs[keep_def] >> rfs[] >> fs[] >>
        `domain (findLookups e) ⊆ domain reachable` by (
            fs[decsClosed_def] >> fs[analyseCode_def] >> fs[analyseExp_def] >>
            reverse(Cases_on `isPure e`) >> fs[] >- (fs[codeAnalysis_union_def] >> fs[domain_union]) >>
            reverse(Cases_on `isHidden e`) >> fs[] >> fs[codeAnalysis_union_def, domain_union] >>
            fs[Once num_set_tree_union_sym, num_set_tree_union_def] >> simp[SUBSET_DEF] >>
            rw[] >> first_x_assum match_mp_tac >> fs[spt_eq_thm, wf_inter, wf_def] >> fs[lookup_inter_alt] >>
            fs[lookup_def] >> Cases_on `lookup n (findLoc e)` >> fs[] >> fs[domain_lookup] >>
            asm_exists_tac >> fs[] >> fs[isReachable_def] >> match_mp_tac RTC_SINGLE >> fs[isAdjacent_def] >>
            `(lookup n (map (K (findLookups e)) (findLoc e))) = SOME (findLookups e)` by fs[lookup_map] >>
            imp_res_tac lookup_mk_wf_set_tree >> fs[] >>
            `wf_set_tree (mk_wf_set_tree (map (K (findLookups e)) (findLoc e)))` by metis_tac[mk_wf_set_tree_thm] >>
            fs[wf_set_tree_def] >> res_tac >> `y = findLookups e` by metis_tac[wf_findLookups, num_set_domain_eq] >>
            rveq >> fs[] >> fs[SUBSET_DEF, domain_lookup]) >>
        fs[] >> `r ≠ Rerr (Rabort Rtype_error)` by (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
        qpat_x_assum `_ = (_,_,_) ` mp_tac >> fs[] >>
        EVERY_CASE_TAC >> fs[] >> rw[] >> fs[findResultGlobals_def, findSemPrimResGlobals_def]
);




(**************************** CASE: *NOT* keep reachable h *****************************)

(******** EVALUATE MUTUAL INDUCTION ********)

val evaluate_flat_state_rel_lemma = Q.store_thm ("evaluate_flat_state_rel_lemma",
    `(∀ env (state:'a flatSem$state) exprL new_state result reachable removed_state .
        flatSem$evaluate env state exprL = (new_state, result) ∧
        EVERY isPure exprL ∧
        EVERY (λ e. isEmpty (inter (findLoc e) reachable)) exprL ∧ env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧ ∃ values : flatSem$v list . result = Rval values)
   ∧
    (∀ env (state:'a flatSem$state) v patExp_list err_v new_state result reachable removed_state .
        evaluate_match env state v patExp_list err_v = (new_state, result) ∧
        EVERY isPure (MAP SND patExp_list) ∧
        EVERY (λ e. isEmpty (inter (findLoc e) reachable)) (MAP SND patExp_list) ∧ env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧ ∃ values : flatSem$v list . result = Rval values)`
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
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once findLoc_def] >> strip_tac >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[EVERY_REVERSE, isPure_EVERY_aconv] >>
        once_rewrite_tac [(GSYM NOT_EXISTS)] >>
        once_rewrite_tac [GSYM NOT_EVERY] >> fs[findLoc_EVERY_isEmpty]
      ,
        (* Var_local - DONE!!! *)
        fs[evaluate_def] >> Cases_on `ALOOKUP env.v n` >> fs[] >> rveq >> fs[] >>
        fs[findVglobals_def, findEnvGlobals_def] >> imp_res_tac ALOOKUP_MEM >>
        imp_res_tac findVglobalsL_MEM >> imp_res_tac SUBSET_TRANS
      ,
        (* Fun - DONE!!! *)
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >> fs[evaluate_def] >>
        rveq >> fs[findVglobals_def, domain_union, findEnvGlobals_def, isPure_def] >>
        fs[findLoc_def]
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
            fs[isPure_EVERY_aconv] >> imp_res_tac inter_insert_empty >>
            EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >>
            fs[findVglobals_def, flat_state_rel_def] >> rw[] >> fs[] >> rfs[] >>
            fs[globals_rel_def] >>
            fs[LUPDATE_SEM] >>
            reverse(rw[]) >- metis_tac[] >>
            Cases_on `n = n'` >> fs[] >>
            qpat_x_assum `∀ n . _ ∧ _ ⇒ _` match_mp_tac >>
            fs[EL_LUPDATE])
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
        fs[]
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

(******** EVALUATE SPECIALISATION ********)


val evaluate_sing_notKeep_flat_state_rel = Q.store_thm("evaluate_sing_notKeep_flat_state_rel",
    `∀ env (state:'a flatSem$state) exprL new_state result expr reachable removed_state .
        flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧ exprL = [expr] ∧
        ¬keep reachable (Dlet expr) ∧ env.exh_pat ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ flat_state_rel reachable new_state removed_state ∧ ∃ value : flatSem$v . result = Rval [value]`
  ,
    rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
    drule (CONJUNCT1 evaluate_flat_state_rel_lemma) >> fs[] >> disch_then drule >> disch_then drule >> fs[] >>
    rw[] >> imp_res_tac evaluate_sing >> fs[] >> fs[findVglobals_def]
);

(******************************************************** MAIN PROOFS *********************************************************)

(**************************** FLATLANG DECS REMOVAL LEMMA *****************************)

val flat_decs_removal_lemma = Q.store_thm ("flat_decs_removal_lemma",
    `∀ env (state:'a flatSem$state) decs new_state new_ctors result reachable removed_decs removed_state .
        evaluate_decs env state decs = (new_state, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧ env.exh_pat ∧
        removeUnreachable reachable decs = removed_decs ∧
        flat_state_rel reachable state removed_state ∧
        domain (findEnvGlobals env) ⊆ domain reachable ∧
        decsClosed reachable decs
    ⇒ ∃ new_removed_state .
        new_removed_state.ffi = new_state.ffi /\
        evaluate_decs env removed_state removed_decs = (new_removed_state, new_ctors, result)`,
    Induct_on `decs`
    >- (rw[evaluate_decs_def, removeUnreachable_def] >>
        fs[evaluate_decs_def, findResultGlobals_def, flat_state_rel_def])
    >>  fs[evaluate_decs_def, removeUnreachable_def] >> rw[] >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >> SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac
        >- (fs[evaluate_decs_def] >> `∃ r . evaluate_dec env state' h = r` by simp[] >>
            PairCases_on `r` >> fs[] >> `r2 ≠ SOME (Rabort Rtype_error)` by (CCONTR_TAC >> fs[]) >>
            drule evaluate_dec_flat_state_rel >> rpt (disch_then drule) >> rw[] >> fs[] >>
            pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
            `decsClosed reachable [h]` by imp_res_tac decsClosed_reduce_HD >> fs[] >>
            reverse(Cases_on `r2` >> fs[] >> rw[] >> rveq >> EVERY_CASE_TAC) >- fs[flat_state_rel_def] >>
            fs[] >> first_x_assum drule >> fs[] >> rveq >> strip_tac >>
            pop_assum (qspecl_then [`reachable`, `new_removed_state`] mp_tac) >> fs[] >>
            reverse(impl_tac) >- rw[] >> fs[findEnvGlobals_def] >> imp_res_tac decsClosed_reduce)
        >>  reverse(EVERY_CASE_TAC) >> fs[] >> rveq >> rename1 `_ _ decs = (n_state, ctors, res)` >>
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

(**************************** FLATLANG REMOVAL THEOREM *****************************)

val flat_removal_thm = Q.store_thm ("flat_removal_thm",
    `∀ exh_pat check_ctor ffi k decs new_state new_ctors result roots tree reachable removed_decs .
        evaluate_decs (initial_env exh_pat check_ctor) (initial_state ffi k) decs = (new_state, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧ exh_pat ∧
        (roots, tree) = analyseCode decs ∧
        reachable = closure_spt roots (mk_wf_set_tree tree) ∧
        removeUnreachable reachable decs = removed_decs
    ⇒ ∃ s .
        s.ffi = new_state.ffi /\
        evaluate_decs (initial_env exh_pat check_ctor) (initial_state ffi k) removed_decs = (s, new_ctors, result)`
  ,
    rpt strip_tac >> drule flat_decs_removal_lemma >> rpt (disch_then drule) >> strip_tac >>
    pop_assum (qspecl_then [`reachable`, `removed_decs`, `initial_state ffi k`] mp_tac) >> fs[] >>
    reverse(impl_tac) >- (rw[] >> fs[])
    >>  qspecl_then [`decs`, `roots`, `mk_wf_set_tree tree`, `tree`] mp_tac analysis_reachable_thm >>
        impl_tac >> rw[initial_env_def, initial_state_def]
        >- (fs[flat_state_rel_def, globals_rel_def] >> fs[findRefsGlobals_def])
        >- (fs[findEnvGlobals_def, findVglobals_def])
        >- (fs[decsClosed_def] >> rw[] >> `(r,t) = (roots, tree)` by metis_tac[] >> fs[] >> rveq
            >- (rw[SUBSET_DEF] >> qexists_tac `x` >> fs[isReachable_def])
            >- (qexists_tac `n'` >> fs[isReachable_def] >> metis_tac[transitive_RTC, transitive_def]))
);

val flat_remove_eval_sim = Q.store_thm("flat_remove_eval_sim",
  `eval_sim ffi T T ds1 T T (removeFlatProg ds1)
                            (\d1 d2. d2 = removeFlatProg d1) F`,
  rw [eval_sim_def] \\ qexists_tac `0` \\ fs [removeFlatProg_def]
  \\ pairarg_tac \\ fs []
  \\ drule flat_removal_thm \\ rw [] \\ fs []);

val flat_remove_semantics = save_thm ("flat_remove_semantics",
  MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] IMP_semantics_eq)
           flat_remove_eval_sim |> SIMP_RULE (srw_ss()) []);

(* syntactic results *)

val elist_globals_filter = Q.prove (
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds))) = {||}`,
  Induct_on `ds` \\ rw [] \\ fs [SUB_BAG_UNION]);

val esgc_free_filter = Q.prove (
  `EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds)))`,
  Induct_on `ds` \\ rw []);

val elist_globals_filter_SUB_BAG = Q.prove (
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))`,
  Induct_on `ds` \\ rw [] \\ fs [SUB_BAG_UNION]);

val removeFlatProg_elist_globals_eq_empty = Q.store_thm (
  "removeFlatProg_elist_globals_eq_empty",
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (removeFlatProg ds))) = {||}`,
  simp [removeFlatProg_def, removeUnreachable_def, UNCURRY]
  \\ metis_tac [elist_globals_filter]);

val removeFlatProg_esgc_free = Q.store_thm ("removeFlatProg_esgc_free",
  `EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (removeFlatProg ds)))`,
  simp [removeFlatProg_def, removeUnreachable_def, UNCURRY]
  \\ metis_tac [esgc_free_filter]);

val removeFlatProg_sub_bag = Q.store_thm ("removeFlatProg_sub_bag",
  `elist_globals (MAP dest_Dlet (FILTER is_Dlet (removeFlatProg ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))`,
  simp [removeFlatProg_def, removeUnreachable_def, UNCURRY]
  \\ metis_tac [elist_globals_filter_SUB_BAG]);

val removeFlatProg_distinct_globals = Q.store_thm (
  "removeFlatProg_distinct_globals",
  `BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)))
   ==>
   BAG_ALL_DISTINCT (elist_globals
     (MAP dest_Dlet (FILTER is_Dlet (removeFlatProg ds))))`,
  metis_tac [removeFlatProg_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]);

val _ = export_theory();

