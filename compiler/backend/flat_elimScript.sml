(*
  Implementation for flatLang dead-code elimination.

  Analyses code to give a next-step function as a num_set num_map.
  Closes this next-step function to give a set of reachable globals.
  Removes unreachable globals from the code.
*)

open preamble sptreeTheory flatLangTheory

val _ = new_theory "flat_elim";


(**************************** ANALYSIS FUNCTIONS *****************************)

(* is_hidden exp = T means there is no direct execution of GlobalVarLookup *)
val is_hidden_def = tDefine "is_hidden" `
    (is_hidden (Raise t e) = is_hidden e) ∧
        (* raise exception *)
    (is_hidden (Handle t e pes) = F) ∧
        (* exception handler *)
    (is_hidden (Lit t l) = T) ∧
        (* literal *)
    (is_hidden (Con t id_option es) = EVERY is_hidden es) ∧
        (* constructor *)
    (is_hidden (Var_local t str) = T) ∧
        (* local var *)
    (is_hidden (Fun t name body) = T) ∧
        (* function abstraction *)
    (is_hidden (App t Opapp l) = F) ∧
        (* function application *)
    (is_hidden (App t (GlobalVarInit g) [e]) = is_hidden e) ∧
        (* GlobalVarInit *)
    (is_hidden (App t (GlobalVarLookup g) [e]) = F) ∧
        (* GlobalVarLookup *)
    (is_hidden (If t e1 e2 e3) = (is_hidden e1 ∧ is_hidden e2 ∧ is_hidden e3)) ∧
        (* if expression *)
    (is_hidden (Mat t e1 [p,e2]) = (is_hidden e1 ∧ is_hidden e2)) ∧
        (* SINGLE pattern match *)
    (is_hidden (Let t opt e1 e2) = (is_hidden e1 ∧ is_hidden e2)) ∧
        (* let-expression *)
    (is_hidden (Letrec t funs e) = is_hidden e) ∧
        (* local def of mutually recursive funs *)
    (is_hidden _ = F)
`
    (
        WF_REL_TAC `measure (λ e . exp_size e)` >> rw[exp_size_def] >>
        Induct_on `es` >> rw[exp_size_def] >> fs[]
    );

val is_hidden_ind = theorem "is_hidden_ind";

(* check if expression is pure in that it does not make any visible changes
    (other than writing to globals) *)
val is_pure_def = tDefine "is_pure" `
    (is_pure (Handle t e pes) = is_pure e) ∧
    (is_pure (Lit t l) = T) ∧
    (is_pure (Con t id_option es) = EVERY is_pure es) ∧
    (is_pure (Var_local t str) = T) ∧
    (is_pure (Fun t name body) = T) ∧
    (is_pure (App t (GlobalVarInit g) es) = EVERY is_pure es) ∧
    (is_pure (If t e1 e2 e3) = (is_pure e1 ∧ is_pure e2 ∧ is_pure e3)) ∧
    (is_pure (Mat t e1 pes) = (is_pure e1 ∧ EVERY is_pure (MAP SND pes))) ∧
    (is_pure (Let t opt e1 e2) = (is_pure e1 ∧ is_pure e2)) ∧
    (is_pure (Letrec t funs e) = is_pure e) ∧
    (is_pure _ = F)
`
    (
        WF_REL_TAC `measure (λ e . exp_size e)` >> rw[exp_size_def] >> fs[] >>
        TRY (Induct_on `es` >> rw[exp_size_def] >> fs[])
        >- (Induct_on `pes` >> rw[exp_size_def] >> fs[] >>
            Cases_on `h` >> fs[exp_size_def])
    );

val is_pure_ind = theorem "is_pure_ind";

val dest_GlobalVarInit_def = Define `
    dest_GlobalVarInit (GlobalVarInit n) = SOME n ∧
    dest_GlobalVarInit _ = NONE
`

val dest_GlobalVarLookup_def = Define `
    dest_GlobalVarLookup (GlobalVarLookup n) = SOME n ∧
    dest_GlobalVarLookup _ = NONE
`

Theorem exp_size_map_snd:
     ∀ p_es . exp6_size (MAP SND p_es) ≤ exp3_size p_es
Proof
    Induct >> rw[exp_size_def] >>
    Cases_on `exp6_size (MAP SND p_es) = exp3_size p_es` >>
    `exp_size (SND h) ≤ exp5_size h` by (Cases_on `h` >> rw[exp_size_def]) >>
    rw[]
QED

Theorem exp_size_map_snd_snd:
     ∀ vv_es . exp6_size (MAP (λ x . SND (SND x)) vv_es) ≤ exp1_size vv_es
Proof
    Induct >> rw[exp_size_def] >>
    Cases_on `exp6_size (MAP (λ x . SND (SND x)) vv_es) = exp1_size vv_es` >>
    `exp_size (SND (SND h)) ≤ exp2_size h` by
        (Cases_on `h` >> Cases_on `r` >> rw[exp_size_def]) >> rw[]
QED

val find_loc_def = tDefine "find_loc" `
    (find_loc ((Raise _ er):flatLang$exp) = find_loc er) ∧
    (find_loc (Handle _ eh p_es) =
        union (find_loc eh) (find_locL (MAP SND p_es))) ∧
    (find_loc (Lit _ _) = LN:num_set) ∧
    (find_loc (Con _ _ es) = find_locL es) ∧
    (find_loc (Var_local _ _) = LN) ∧
    (find_loc (Fun _ _ ef) = find_loc ef) ∧
    (find_loc (App _ op es) = (case (dest_GlobalVarInit op) of
        | SOME n => (insert n () (find_locL es))
        | NONE => find_locL es)) ∧
    (find_loc (If _ ei1 ei2 ei3) =
        union (find_loc ei1) (union (find_loc ei2) (find_loc ei3))) ∧
    (find_loc (Mat _ em p_es) =
        union (find_loc em) (find_locL (MAP SND p_es))) ∧
    (find_loc (Let _ _ el1 el2) = union (find_loc el1) (find_loc el2)) ∧
    (find_loc (Letrec _ vv_es elr1) =
        union (find_locL (MAP (SND o SND) vv_es)) (find_loc elr1)) ∧
    (find_locL [] = LN) ∧
    (find_locL (e::es) = union (find_loc e) (find_locL es))`
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

val find_loc_ind = theorem "find_loc_ind";

val find_lookups_def = tDefine "find_lookups" `
    (find_lookups (Raise _ er) = find_lookups er) ∧
    (find_lookups (Handle _ eh p_es) =
        union (find_lookups eh) (find_lookupsL (MAP SND p_es))) ∧
    (find_lookups (Lit _ _) = LN) ∧
    (find_lookups (Con _ _ es) = find_lookupsL es) ∧
    (find_lookups (Var_local _ _) = LN) ∧
    (find_lookups (Fun _ _ ef) = find_lookups ef) ∧
    (find_lookups (App _ op es) = (case (dest_GlobalVarLookup op) of
        | SOME n => (insert n () (find_lookupsL es))
        | NONE => find_lookupsL es)) ∧
    (find_lookups (If _ ei1 ei2 ei3) =
        union (find_lookups ei1)
            (union (find_lookups ei2) (find_lookups ei3))) ∧
    (find_lookups (Mat _ em p_es) =
        union (find_lookups em) (find_lookupsL (MAP SND p_es))) ∧
    (find_lookups (Let _ _ el1 el2) =
        union (find_lookups el1) (find_lookups el2)) ∧
    (find_lookups (Letrec _ vv_es elr1) =
        union (find_lookupsL (MAP (SND o SND) vv_es)) (find_lookups elr1)) ∧
    (find_lookupsL [] = LN) ∧
    (find_lookupsL (e::es) = union (find_lookups e) (find_lookupsL es))
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

val find_lookups_ind = theorem "find_lookups_ind";

val analyse_exp_def = Define `
    analyse_exp e = let locs = (find_loc e) in let lookups = (find_lookups e) in
        if is_pure e then (
            if (is_hidden e) then (LN, map (K lookups) locs)
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

val code_analysis_union_def = Define `
    code_analysis_union (r1, t1) (r2, t2) =
        ((union r1 r2), (num_set_tree_union t1 t2))
`

val analyse_code_def = Define `
    analyse_code [] = (LN, LN) ∧
    analyse_code ((Dlet e)::cs) =
        code_analysis_union (analyse_exp e) (analyse_code cs) ∧
    analyse_code (_::cs) = analyse_code cs
`



(**************************** REACHABILITY FUNS *****************************)


val superdomain_def = Define `
    superdomain (t:num_set num_map) = spt_fold union LN t
`

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
        if isEmpty (inter (find_loc e) reachable) then (¬ (is_pure e)) else T) ∧
    (keep reachable _ = T) (* not a Dlet, will be Dtype/Dexn so keep *)
`

val keep_ind = theorem "keep_ind";

val remove_unreachable_def = Define `
    remove_unreachable reachable l = FILTER (keep reachable) l
`

val remove_flat_prog_def = Define `
    remove_flat_prog code =
        let (r, t) = analyse_code code in
        let reachable = closure_spt r (mk_wf_set_tree t) in
        remove_unreachable reachable code
`


val _ = export_theory();
