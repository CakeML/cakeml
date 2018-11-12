open preamble sptreeTheory flatLangTheory

val _ = new_theory "flat_elim";


(**************************** ANALYSIS FUNCTIONS *****************************)

(* isHidden exp = T means there is no direct execution of GlobalVarLookup *)
val isHidden_def = tDefine "isHidden" `
    (isHidden (Raise t e) = isHidden e) ∧
        (* raise exception *)
    (isHidden (Handle t e pes) = F) ∧
        (* exception handler *)
    (isHidden (Lit t l) = T) ∧
        (* literal *)
    (isHidden (Con t id_option es) = EVERY isHidden es) ∧
        (* constructor *)
    (isHidden (Var_local t str) = T) ∧
        (* local var *)
    (isHidden (Fun t name body) = T) ∧
        (* function abstraction *)
    (isHidden (App t Opapp l) = F) ∧
        (* function application *)
    (isHidden (App t (GlobalVarInit g) [e]) = isHidden e) ∧
        (* GlobalVarInit *)
    (isHidden (App t (GlobalVarLookup g) [e]) = F) ∧
        (* GlobalVarLookup *)
    (isHidden (If t e1 e2 e3) = (isHidden e1 ∧ isHidden e2 ∧ isHidden e3)) ∧
        (* if expression *)
    (isHidden (Mat t e1 [p,e2]) = (isHidden e1 ∧ isHidden e2)) ∧
        (* SINGLE pattern match *)
    (isHidden (Let t opt e1 e2) = (isHidden e1 ∧ isHidden e2)) ∧
        (* let-expression *)
    (isHidden (Letrec t funs e) = isHidden e) ∧
        (* local def of mutually recursive funs *)
    (isHidden _ = F)
`
    (
        WF_REL_TAC `measure (λ e . exp_size e)` >> rw[exp_size_def] >>
        Induct_on `es` >> rw[exp_size_def] >> fs[]
    );

val isHidden_ind = theorem "isHidden_ind";

(* check if expression is pure in that it does not make any visible changes
    (other than writing to globals) *)
val isPure_def = tDefine "isPure" `
    (isPure (Handle t e pes) = isPure e) ∧
    (isPure (Lit t l) = T) ∧
    (isPure (Con t id_option es) = EVERY isPure es) ∧
    (isPure (Var_local t str) = T) ∧
    (isPure (Fun t name body) = T) ∧
    (isPure (App t (GlobalVarInit g) es) = EVERY isPure es) ∧
    (isPure (If t e1 e2 e3) = (isPure e1 ∧ isPure e2 ∧ isPure e3)) ∧
    (isPure (Mat t e1 pes) = (isPure e1 ∧ EVERY isPure (MAP SND pes))) ∧
    (isPure (Let t opt e1 e2) = (isPure e1 ∧ isPure e2)) ∧
    (isPure (Letrec t funs e) = isPure e) ∧
    (isPure _ = F)
`
    (
        WF_REL_TAC `measure (λ e . exp_size e)` >> rw[exp_size_def] >> fs[] >>
        TRY (Induct_on `es` >> rw[exp_size_def] >> fs[])
        >- (Induct_on `pes` >> rw[exp_size_def] >> fs[] >>
            Cases_on `h` >> fs[exp_size_def])
    );

val isPure_ind = theorem "isPure_ind";

val dest_GlobalVarInit_def = Define `
    dest_GlobalVarInit (GlobalVarInit n) = SOME n ∧
    dest_GlobalVarInit _ = NONE
`

val dest_GlobalVarLookup_def = Define `
    dest_GlobalVarLookup (GlobalVarLookup n) = SOME n ∧
    dest_GlobalVarLookup _ = NONE
`

val exp_size_map_snd = Q.store_thm("exp_size_map_snd",
    `∀ p_es . exp6_size (MAP SND p_es) ≤ exp3_size p_es`,
    Induct >> rw[exp_size_def] >>
    Cases_on `exp6_size (MAP SND p_es) = exp3_size p_es` >>
    `exp_size (SND h) ≤ exp5_size h` by (Cases_on `h` >> rw[exp_size_def]) >>
    rw[]
);

val exp_size_map_snd_snd = Q.store_thm("exp_size_map_snd_snd",
    `∀ vv_es . exp6_size (MAP (λ x . SND (SND x)) vv_es) ≤ exp1_size vv_es`,
    Induct >> rw[exp_size_def] >>
    Cases_on `exp6_size (MAP (λ x . SND (SND x)) vv_es) = exp1_size vv_es` >>
    `exp_size (SND (SND h)) ≤ exp2_size h` by
        (Cases_on `h` >> Cases_on `r` >> rw[exp_size_def]) >> rw[]
);

val findLoc_def = tDefine "findLoc" `
    (findLoc ((Raise _ er):flatLang$exp) = findLoc er) ∧
    (findLoc (Handle _ eh p_es) =
        union (findLoc eh) (findLocL (MAP SND p_es))) ∧
    (findLoc (Lit _ _) = LN:num_set) ∧
    (findLoc (Con _ _ es) = findLocL es) ∧
    (findLoc (Var_local _ _) = LN) ∧
    (findLoc (Fun _ _ ef) = findLoc ef) ∧
    (findLoc (App _ op es) = (case (dest_GlobalVarInit op) of
        | SOME n => (insert n () (findLocL es))
        | NONE => findLocL es)) ∧
    (findLoc (If _ ei1 ei2 ei3) =
        union (findLoc ei1) (union (findLoc ei2) (findLoc ei3))) ∧
    (findLoc (Mat _ em p_es) = union (findLoc em) (findLocL (MAP SND p_es))) ∧
    (findLoc (Let _ _ el1 el2) = union (findLoc el1) (findLoc el2)) ∧
    (findLoc (Letrec _ vv_es elr1) =
        union (findLocL (MAP (SND o SND) vv_es)) (findLoc elr1)) ∧
    (findLocL [] = LN) ∧
    (findLocL (e::es) = union (findLoc e) (findLocL es))`
    (
        WF_REL_TAC `measure (λ e . case e of
            | INL x => exp_size x
            | INR y => exp6_size y)` >>
        rw[exp_size_def]
        >- (qspec_then `vv_es` mp_tac exp_size_map_snd_snd >>
            Cases_on
                `exp6_size(MAP (λ x . SND (SND x)) vv_es) = exp1_size vv_es` >>
            rw[])
        >- (qspec_then `p_es` mp_tac exp_size_map_snd >>
            Cases_on `flatLang$exp6_size(MAP SND p_es) = exp3_size p_es` >>
            rw[])
        >- (qspec_then `p_es` mp_tac exp_size_map_snd >>
            Cases_on `exp6_size(MAP SND p_es') = exp3_size p_es` >>
            rw[])
    );

val findLoc_ind = theorem "findLoc_ind";

val findLookups_def = tDefine "findLookups" `
    (findLookups (Raise _ er) = findLookups er) ∧
    (findLookups (Handle _ eh p_es) =
        union (findLookups eh) (findLookupsL (MAP SND p_es))) ∧
    (findLookups (Lit _ _) = LN) ∧
    (findLookups (Con _ _ es) = findLookupsL es) ∧
    (findLookups (Var_local _ _) = LN) ∧
    (findLookups (Fun _ _ ef) = findLookups ef) ∧
    (findLookups (App _ op es) = (case (dest_GlobalVarLookup op) of
        | SOME n => (insert n () (findLookupsL es))
        | NONE => findLookupsL es)) ∧
    (findLookups (If _ ei1 ei2 ei3) =
        union (findLookups ei1) (union (findLookups ei2) (findLookups ei3))) ∧
    (findLookups (Mat _ em p_es) =
        union (findLookups em) (findLookupsL (MAP SND p_es))) ∧
    (findLookups (Let _ _ el1 el2) =
        union (findLookups el1) (findLookups el2)) ∧
    (findLookups (Letrec _ vv_es elr1) =
        union (findLookupsL (MAP (SND o SND) vv_es)) (findLookups elr1)) ∧
    (findLookupsL [] = LN) ∧
    (findLookupsL (e::es) = union (findLookups e) (findLookupsL es))
`
    (
        WF_REL_TAC `measure (λ e . case e of
                | INL x => exp_size x
                | INR (y:flatLang$exp list) =>
                    flatLang$exp6_size y)` >> rw[exp_size_def]
        >- (qspec_then `vv_es` mp_tac exp_size_map_snd_snd >>
            Cases_on
                `exp6_size(MAP (λ x . SND (SND x)) vv_es) = exp1_size vv_es` >>
            rw[])
        >- (qspec_then `p_es` mp_tac exp_size_map_snd >>
            Cases_on `exp6_size(MAP SND p_es) = exp3_size p_es` >>
            rw[])
        >- (qspec_then `p_es` mp_tac exp_size_map_snd >>
            Cases_on `exp6_size(MAP SND p_es) = exp3_size p_es` >>
            rw[])
    );

val findLookups_ind = theorem "findLookups_ind";

val analyseExp_def = Define `
    analyseExp e = let locs = (findLoc e) in let lookups = (findLookups e) in
        if isPure e then (
            if (isHidden e) then (LN, map (K lookups) locs)
            else (locs, map (K lookups) locs)
        ) else (
            (union locs lookups, (map (K LN) (union locs lookups)))
        )
`

val num_set_tree_union_def = Define `
    (num_set_tree_union (LN:num_set num_map) t2 = t2) ∧
    (num_set_tree_union (LS a) t =
     case t of
       | LN => LS a
       | LS b => LS (union a b)
       | BN t1 t2 => BS t1 a t2
       | BS t1 b t2 => BS t1 (union a b) t2) ∧
  (num_set_tree_union (BN t1 t2) t =
     case t of
       | LN => BN t1 t2
       | LS a => BS t1 a t2
       | BN t1' t2' =>
            BN (num_set_tree_union t1 t1') (num_set_tree_union t2 t2')
       | BS t1' a t2' =>
        BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')) ∧
  (num_set_tree_union (BS t1 a t2) t =
     case t of
       | LN => BS t1 a t2
       | LS b => BS t1 (union a b) t2
       | BN t1' t2' =>
            BS (num_set_tree_union t1 t1') a (num_set_tree_union t2 t2')
       | BS t1' b t2' =>
            BS (num_set_tree_union t1 t1') (union a b)
                (num_set_tree_union t2 t2'))
`;

val codeAnalysis_union_def = Define `
    codeAnalysis_union (r1, t1) (r2, t2) =
        ((union r1 r2), (num_set_tree_union t1 t2))
`

val analyseCode_def = Define `
    analyseCode [] = (LN, LN) ∧
    analyseCode ((Dlet e)::cs) =
        codeAnalysis_union (analyseExp e) (analyseCode cs) ∧
    analyseCode (_::cs) = analyseCode cs
`



(**************************** REACHABILITY FUNS *****************************)


val superdomain_def = Define `
    superdomain LN = LN ∧
    superdomain (LS (t:num_set)) = t ∧
    superdomain (BN t1 t2) = union (superdomain t1) (superdomain t2) ∧
    superdomain (BS t1 a t2) =
        union (superdomain t1) (union a (superdomain t2))
`

(* TODO - USE THIS FOLD DEFINITION OF SUPERDOMAIN

val sd_def = Define `
    sd (t:num_set num_map) = (foldi (λ k v a . union v a) 0 LN) t
`
);

*)

val mk_wf_set_tree_def = Define `
    mk_wf_set_tree t =
        let t' = union t (map (K LN) (superdomain t)) in mk_wf (map (mk_wf) t')
`

val close_spt_def = tDefine "close_spt" `
    close_spt (reachable :num_set) (seen :num_set) (tree :num_set spt) =
        let to_look = difference seen reachable in
        let new_sets = inter tree to_look in
            if new_sets = LN then reachable else
                let new_set = spt_fold union LN new_sets in
                    close_spt (union reachable to_look) (union seen new_set)
                        tree
    `
    (
        WF_REL_TAC `measure (λ (r, _, t) . size (difference t r))` >>
        rw[] >>
        match_mp_tac size_diff_less >>
        fs[domain_union, domain_difference] >>
        fs[inter_eq_LN, IN_DISJOINT, domain_difference] >>
        qexists_tac `x` >>
        fs[]
    )

val close_spt_ind = theorem "close_spt_ind";

val closure_spt_def = Define
    `closure_spt start tree = close_spt LN start tree`;

(**************************** REMOVAL FUNCTIONS *****************************)

val keep_def = Define `
    (keep reachable (Dlet e) =
        (* if none of the global variables that e may assign to are in
           the reachable set, then e is candidate for removal
           -> if any are in, then keep e
           -> however if e is not pure (can have side-effects),
              then it must be kept *)
        if isEmpty (inter (findLoc e) reachable) then (¬ (isPure e)) else T) ∧
    (keep reachable _ = T) (* not a Dlet, will be Dtype/Dexn so keep *)
`

val keep_ind = theorem "keep_ind";

val removeUnreachable_def = Define `
    removeUnreachable reachable l = FILTER (keep reachable) l
`

val removeFlatProg_def = Define `
    removeFlatProg code =
        let (r, t) = analyseCode code in
        let reachable = closure_spt r (mk_wf_set_tree t) in
        removeUnreachable reachable code
`


val _ = export_theory();
