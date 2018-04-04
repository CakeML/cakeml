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

(**************************** GLOBALS_REL *****************************)

(* s = state, t = removed state *)
val globals_rel_def = Define `
    globals_rel (reachable : num_set) (s : 'ffi flatSem$state) (t : 'ffi flatSem$state) ⇔ 
        LENGTH s.globals = LENGTH t.globals ∧ 
        (∀ n . n ∈ domain reachable ∧ n < LENGTH t.globals
        ⇒ EL n s.globals = EL n t.globals)
`

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
    >- (
        Cases_on `analyseExp e` >> fs[codeAnalysis_union_def, domain_union] >>
        first_x_assum drule >> rw[] >>
        pop_assum match_mp_tac >>
        fs[isReachable_def] >>
        cheat (* TODO *)
    )
    >> metis_tac[] 
);


(**************************** FLAT_STATE_REL *****************************)

(* s = state, t = removed state *)
val flat_state_rel_def = Define `
    flat_state_rel reachable s t ⇔ s.clock = t.clock ∧ s.refs = t.refs ∧
    s.ffi = t.ffi ∧ globals_rel reachable s t ∧ 
    domain (findRefsGlobals s.refs) ⊆ domain reachable
`


(******************************************************** OTHER LEMMAS *********************************************************)

(**************************** IMPLEMENTATION LEMMAS *****************************)

val keep_Dlet = Q.store_thm("keep_Dlet",
    `∀ (reachable:num_set) h . ¬ keep reachable h ⇒ ∃ x . h = Dlet x`,
   Cases_on `h` >> rw[keep_def]
);
          

(******************************************************** MAIN PROOFS *********************************************************)

(**************************** FLAT_DECS_REMOVAL LEMMA *****************************)

val flat_decs_removal_lemma = Q.store_thm ("flat_decs_removal_lemma",
    `∀ env state decs new_state new_ctors result reachable removed_decs removed_state . 
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
,cheat); (* 
    Induct_on `decs` 
    >- (rw[evaluate_decs_def, removeUnreachable_def] >> fs[evaluate_decs_def, findResultGlobals_def])
    >> fs[evaluate_decs_def, removeUnreachable_def] >> reverse(rw[])

        >- (
            imp_res_tac keep_Dlet >> rveq >> fs[evaluate_dec_def] >>
            Cases_on `evaluate (env with v :=[] ) state' [x]` >> fs[] >>
            Cases_on `r` >> fs[] >>

                EVERY_CASE_TAC >> fs[] >> rveq >>
                `env with c updated_by $UNION {} = env` by fs[environment_component_equality] >>
                fs[UNION_EMPTY] >>
                first_x_assum match_mp_tac >> 
                qexists_tac `q` >> fs[] >>
                fs[flat_state_rel_def] >>
                   
                
            
            )
        )

        >- (fs[evaluate_decs_def] >> `∃ r . evaluate_dec env removed_state h = r` by simp[] >> PairCases_on `r` >>
            fs[] >> 
            `r2 ≠ SOME (Rabort Rtype_error)` by (EVERY_CASE_TAC >> rveq >> fs[]
            CCONTR_TAC >> fs[]) >> 
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
*)
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
    state_rel (reachable:num_set) s t ⇔ s.clock = t.clock ∧ s.refs = t.refs ∧ 
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
        rw[] >> 
        Cases_on `h` >> fs[evaluate_dec_def] >>

    (* TODO *)
    
    cheat
);



(************************* LEMMAS *****************************)
(*val keep_new_ctors = Q.store_thm("keep_new_ctors",
    `∀ (reachable:num_set) h env state h1 new_ctors result . 
    ¬keep reachable h ∧ evaluate_dec env state h = (h1, new_ctors, result) ⇒ new_ctors = {}`,
    Cases_on `h` >> rw[keep_def] >> EVERY_CASE_TAC >> fs[] >>
    cheat
    (* TODO *)
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
    `(∀ env (s:'ffi state) x s1 r reachable t . evaluate (env with v := []) s [x] = (s1, r) ∧ 
        ¬keep reachable (Dlet x) ∧ state_rel reachable s t
    
    ⇒ state_rel reachable s1 t ∧ ∃ v . r = Rval [v]) ∧ 
    
`(∀env (s:'ffi flatSem$state) ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
         (∀env (s:'ffi flatSem$state) v pes ev s' vs.
               evaluate_match env s v pes ev = (s', Rval vs) ⇒ LENGTH vs = 1)`,
    



cheat);
rw[]

Induct >> fs[evaluate_def] >> rw[]



imp_res_tac evaluate_sing
evaluate_cons

EVERY_CASE_TAC >>


            rw[] >> qspecl_then [`reachable`, `(Raise t x)`, `x`, `t`] mp_tac not_keep_subterm >>
            EVERY_CASE_TAC >> 
            first_assum (qspecl_then [`t'`, `s1`, `s`, `reachable`, `env`, `r`] mp_tac) >> rw[] >>
            first_assum (qspecl_then [`t'`, `q`, `s`, `reachable`, `env`, `Rval a`] mp_tac) >> rw[]
             

                  

>>    cheat
);


(***************************** REMOVAL *************************)
        
        (* TODO - add assumption - if there is a get global in upcoming state, it is in reachable *)

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


      `(∀env (s:'ffi flatSem$state) ls s' vs.
            evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
    
    `∀ env s ds s1 new_ctors result ds1 t (reachable:num_set).
        flatSem$evaluate_decs env s ds = (s1, new_ctors, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧
        removeUnreachable reachable ds = ds1 ∧ state_rel reachable s t 
    ⇒ ∃ t1 . 
        flatSem$evaluate_decs env t ds1 = (t1, new_ctors, result) ∧
        state_rel reachable s1 t1`,
    
    ho_match_mp_tac evaluate_ind
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
    (* TODO *)
    Induct_on `p`
    >-(rw[source_to_flatTheory.compile_def] >> fs[source_to_flatTheory.compile_decs_def] >>
       rw[] >> fs[] >> rw[count_GlobalVarInits_def] >> rw[dest_GlobalVarInit_def])
    
    
    
    >> rw[source_to_flatTheory.compile_def] >>
    fs[source_to_flatTheory.compile_decs_def] >>
    Cases_on `p` >>
    >-(

    Cases_on `h` >>
    fs[source_to_flatTheory.compile_decs_def] >>
    rw[] >> fs[] >>
    rw[count_GlobalVarInits_def] >>
    rw[dest_GlobalVarInit_def] >>


    )
   
    rw[] >> fs[] >>
    rw[Once count_GlobalVarInits_def] >>
    rw[dest_GlobalVarInit_def] >>
   
    cheat
);
*)
