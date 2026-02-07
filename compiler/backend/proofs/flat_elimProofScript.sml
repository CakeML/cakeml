(*
  Correctness proof for flatLang dead code elimination
*)
Theory flat_elimProof
Ancestors
  flat_elim flatSem flatLang flatProps spt_closure ast
  misc[qualified] ffi[qualified] sptree
Libs
  preamble

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(************************** LEMMAS ***************************)

(*
Theorem wf_find_loc_wf_find_locL:
     (∀ e locs . find_loc  e = locs ⇒ wf locs) ∧
    (∀ l locs . find_locL l = locs ⇒ wf locs)
Proof
    ho_match_mp_tac find_loc_ind >> rw[find_loc_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarInit op` >> fs[wf_insert]
QED

Theorem wf_find_locL:
     ∀ l . wf(find_locL l)
Proof
    metis_tac[wf_find_loc_wf_find_locL]
QED

Theorem wf_find_loc:
     ∀ e . wf(find_loc e)
Proof
    metis_tac[wf_find_loc_wf_find_locL]
QED

Theorem wf_find_lookups_wf_find_lookupsL:
     (∀ e lookups . find_lookups e = lookups ⇒ wf lookups) ∧
    (∀ l lookups . find_lookupsL l = lookups ⇒ wf lookups)
Proof
    ho_match_mp_tac find_lookups_ind >>
    rw[find_lookups_def, wf_union] >> rw[wf_def] >>
    Cases_on `dest_GlobalVarLookup op` >> fs[wf_insert]
QED

Theorem wf_find_lookupsL:
     ∀ l . wf(find_lookupsL l)
Proof
    metis_tac[wf_find_lookups_wf_find_lookupsL]
QED

Theorem wf_find_lookups:
     ∀ e . wf(find_lookups e)
Proof
    metis_tac[wf_find_lookups_wf_find_lookupsL]
QED
*)

Theorem is_pure_EVERY_aconv:
     ∀ es . EVERY (λ a . is_pure a) es = EVERY is_pure es
Proof
    Induct >> fs[]
QED

Theorem find_lookupsL_MEM:
     ∀ e es . MEM e es ⇒ domain (find_lookups e) ⊆ domain (find_lookupsL es)
Proof
    Induct_on `es` >> rw[] >> fs[find_lookups_def, domain_union] >>
    res_tac >> fs[SUBSET_DEF]
QED

Theorem find_lookupsL_APPEND:
     ∀ l1 l2 . find_lookupsL (l1 ++ l2) =
        union (find_lookupsL l1) (find_lookupsL l2)
Proof
    Induct >> fs[find_lookups_def] >> fs[union_assoc]
QED

Theorem find_lookupsL_REVERSE:
     ∀ l . find_lookupsL l = find_lookupsL (REVERSE l)
Proof
    Induct >> fs[find_lookups_def] >>
    fs[find_lookupsL_APPEND, find_lookups_def, union_num_set_sym]
QED

Theorem find_loc_EVERY_isEmpty:
     ∀ l reachable:num_set .
        EVERY (λ e . isEmpty (inter (find_loc e) reachable)) l
      ⇔ isEmpty (inter (find_locL l) reachable)
Proof
    Induct >- fs[Once find_loc_def, inter_def]
    >> fs[EVERY_DEF] >> rw[] >> EQ_TAC >> rw[] >>
       qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
       fs[inter_union_empty]
QED


(************************** DEFINITIONS ***************************)

Theorem SUM_MAP_v3_size:
  !xs. SUM (MAP v3_size xs) = LENGTH xs +
    SUM (MAP (mlstring_size ∘ FST) xs) +
    SUM (MAP (v_size ∘ SND) xs)
Proof
  Induct \\ simp [FORALL_PROD, v_size_def]
QED

Definition find_v_globals_def:
    (find_v_globals (Conv _ vl) = (find_v_globalsL vl):num_set) ∧
    (find_v_globals (Closure env _ e) =
        union (find_v_globalsL (MAP SND env.v)) (find_lookups e)) ∧
    (find_v_globals (Recclosure env vves _) =
        union (find_v_globalsL (MAP SND env.v))
            (find_lookupsL (MAP (SND o SND) vves))) ∧
    (find_v_globals (Vectorv vl) = find_v_globalsL vl) ∧
    (find_v_globals _ = LN) ∧
    (find_v_globalsL [] = LN) ∧
    (find_v_globalsL (h::t) = union (find_v_globals h) (find_v_globalsL t))
Termination
    WF_REL_TAC `measure (λ e . case e of
            | INL x => v_size x
            | INR y => list_size v_size y)`
    \\ rw [list_size_pair_size_MAP_FST_SND]
    \\ Cases_on ‘env’
    \\ gvs [environment_size_def]
    \\ gvs [list_size_pair_size_MAP_FST_SND]
End

val find_v_globals_ind = theorem "find_v_globals_ind";

Theorem find_v_globalsL_APPEND:
     ∀ l1 l2 . find_v_globalsL (l1 ++ l2) =
        union (find_v_globalsL l1) (find_v_globalsL l2)
Proof
    Induct >> fs[find_v_globals_def] >> fs[union_assoc]
QED

Theorem find_v_globalsL_REVERSE:
     ∀ l . find_v_globalsL l = find_v_globalsL (REVERSE l)
Proof
    Induct >> fs[find_v_globals_def] >>
    fs[find_v_globalsL_APPEND, union_num_set_sym, find_v_globals_def]
QED

Theorem find_v_globalsL_MEM:
     ∀ k v vs . MEM (k, v) vs
  ⇒ domain (find_v_globals v) ⊆ domain (find_v_globalsL (MAP SND vs))
Proof
    Induct_on `vs` >> rw[] >> fs[find_v_globals_def, domain_union] >>
    res_tac >> fs[SUBSET_DEF]
QED

Theorem find_v_globalsL_EL:
     ∀ n vs . n < LENGTH vs ⇒
    domain (find_v_globals (EL n vs)) ⊆ domain(find_v_globalsL vs)
Proof
    Induct >> fs[EL] >> rw[] >> Cases_on `vs` >>
    fs[find_v_globals_def, domain_union] >>
    Cases_on `n = 0` >> fs[] >>  fs[EXTENSION, SUBSET_DEF]
QED

Theorem find_v_globalsL_EL_trans[local]:
    n < LENGTH vs ∧ domain(find_v_globalsL vs) ⊆ R ⇒
    domain (find_v_globals (EL n vs)) ⊆ R
Proof
    metis_tac [find_v_globalsL_EL, SUBSET_TRANS]
QED

Theorem find_v_globals_MAP_Recclosure:
    ∀ funs v l.
    domain (find_v_globalsL (MAP (λx. Recclosure env l (f x)) funs)) =
    (if NULL funs then {}
        else domain (find_v_globalsL (MAP SND env.v)) ∪
            domain (find_lookupsL (MAP (SND o SND) l)))
Proof
    Induct >> fs[find_v_globals_def] >> rw[domain_union]
QED

Theorem find_v_globalsL_REPLICATE:
     ∀ n v vs . domain (find_v_globalsL (REPLICATE n v)) ⊆
        domain (find_v_globals v)
Proof
    Induct >> fs[REPLICATE, find_v_globals_def, domain_union]
QED

Theorem find_v_globalsL_LUPDATE:
     ∀ n vs (reachable:num_set) v . n < LENGTH vs ∧
    domain (find_v_globalsL vs) ⊆ domain reachable ∧
    domain (find_v_globals v) ⊆ domain reachable
  ⇒ domain (find_v_globalsL (LUPDATE v n vs)) ⊆ domain reachable
Proof
    Induct_on `vs` >> rw[] >> Cases_on `n` >> fs[LUPDATE_def] >>
    fs[find_v_globals_def, domain_union]
QED

Theorem find_v_globals_v_to_list:
     ∀ x (reachable:num_set) xs .
        domain (find_v_globals x) ⊆ domain reachable ∧ v_to_list x = SOME xs
    ⇒ domain (find_v_globalsL xs) ⊆ domain reachable
Proof
    recInduct v_to_list_ind >>
    fs[v_to_list_def, find_v_globals_def, domain_union] >> rw[] >>
    Cases_on `v_to_list v2` >> fs[] >> rveq >>
    fs[find_v_globals_def, domain_union] >> metis_tac[]
QED

Theorem find_v_globals_list_to_v:
     ∀ xs (reachable:num_set) x .
        domain (find_v_globalsL xs) ⊆ domain reachable ∧ list_to_v xs = x
    ⇒ domain (find_v_globals x) ⊆ domain reachable
Proof
    Induct >> fs[list_to_v_def, find_v_globals_def, domain_union]
QED

Definition find_refs_globals_def:
    (find_refs_globals (Refv a::t) =
        union (find_v_globals a) (find_refs_globals t)) ∧
    (find_refs_globals (Varray l::t) =
        union (find_v_globalsL l) (find_refs_globals t)) ∧
    (find_refs_globals (Thunk _ a::t) =
        union (find_v_globals a) (find_refs_globals t)) ∧
    (find_refs_globals (_::t) = find_refs_globals t) ∧
    (find_refs_globals [] = LN)
End

val find_refs_globals_ind = theorem "find_refs_globals_ind";

Theorem find_refs_globals_MEM:
     ∀ refs reachable:num_set .
        domain (find_refs_globals refs) ⊆ R
      ⇒ (∀ a . MEM (Refv a) refs
            ⇒ domain (find_v_globals a) ⊆ R) ∧
        (∀ vs . MEM (Varray vs) refs
            ⇒ domain (find_v_globalsL vs) ⊆ R) ∧
        (∀ m a . MEM (Thunk m a) refs
            ⇒ domain (find_v_globals a) ⊆ R)
Proof
    Induct >> rw[] >> fs[find_refs_globals_def, domain_union] >>
    Cases_on `h` >> fs[find_refs_globals_def, domain_union] >>
    first_x_assum drule >> gvs []
QED

Theorem find_refs_globals_EL:
  n < LENGTH refs ∧ domain (find_refs_globals refs) ⊆ R ⇒
    (∀ a . EL n refs = Refv a
            ⇒ domain (find_v_globals a) ⊆ R) ∧
    (∀ vs . EL n refs = Varray vs
            ⇒ domain (find_v_globalsL vs) ⊆ R) ∧
    (∀ m a . EL n refs = Thunk m a
            ⇒ domain (find_v_globals a) ⊆ R)
Proof
  metis_tac [EL_MEM, find_refs_globals_MEM]
QED

Theorem find_refs_globals_LUPDATE:
     ∀ reachable:num_set refs n .
        n < LENGTH refs ∧ domain (find_refs_globals refs) ⊆ domain reachable
      ⇒
        (∀ a . domain (find_v_globals a) ⊆ domain reachable
            ⇒ domain (find_refs_globals (LUPDATE (Refv a) n refs))
                ⊆ domain reachable) ∧
    (∀ vs . domain (find_v_globalsL vs) ⊆ domain reachable
        ⇒ domain (find_refs_globals (LUPDATE (Varray vs) n  refs))
            ⊆ domain reachable) ∧
    (∀ ws. domain (find_refs_globals (LUPDATE (W8array ws) n refs))
        ⊆ domain reachable) ∧
    (∀ m a. domain (find_v_globals a) ⊆ domain reachable
        ⇒ domain (find_refs_globals (LUPDATE (Thunk m a) n refs))
            ⊆ domain reachable)
Proof
    Induct_on `refs` >> rw[] >> Cases_on `h` >>
    fs[find_refs_globals_def, domain_union] >>
    Cases_on `n = 0` >> fs[LUPDATE_def, find_refs_globals_def, domain_union] >>
    fs[domain_union, LUPDATE_def] >> Cases_on `n` >> fs[] >>
    fs[LUPDATE_def, find_refs_globals_def, domain_union]
QED

Theorem find_refs_globals_APPEND:
     ∀ refs new . find_refs_globals (refs ++ new) =
        union (find_refs_globals refs) (find_refs_globals new)
Proof
    Induct >> rw[] >> fs[find_refs_globals_def] >>
    Cases_on `h` >> fs[find_refs_globals_def] >> fs[union_assoc]
QED

Definition find_env_globals_def:
    find_env_globals env = find_v_globalsL (MAP SND env.v)
End

Definition find_result_globals_def:
    (find_result_globals (SOME (Rraise v)) = find_v_globals v) ∧
    (find_result_globals _ = LN)
End

val find_result_globals_ind = theorem "find_result_globals_ind";

Definition find_sem_prim_res_globals_def:
    (find_sem_prim_res_globals (Rerr e :
        (flatSem$v list, flatSem$v) semanticPrimitives$result) =
        find_result_globals (SOME e)) ∧
    (find_sem_prim_res_globals (Rval e) = find_v_globalsL e)
End

val s =  ``s:('c,'ffi) state``
val t = mk_var ("t", type_of s)
val new_state = mk_var ("new_state", type_of s);
val state = mk_var ("state", type_of s);

Definition v_has_Eval_def1:
  (v_has_Eval (Closure env _ e) = (has_Eval e ∨
    EXISTS v_has_Eval (MAP SND env.v))) ∧
  (v_has_Eval (Conv _ vl) = EXISTS v_has_Eval vl) ∧
  (v_has_Eval (Recclosure env nm_es _) =
    (EXISTS v_has_Eval (MAP SND env.v) ∨
      EXISTS has_Eval (MAP (SND o SND) nm_es))) ∧
  (v_has_Eval (Vectorv vl) = EXISTS v_has_Eval vl) ∧
  (v_has_Eval _ = F)
Termination
  WF_REL_TAC `measure v_size`
  \\ gvs [list_size_pair_size_MAP_FST_SND] \\ rw []
  \\ Cases_on ‘env’ \\ gvs [environment_size_def]
  \\ imp_res_tac MEM_list_size
  \\ pop_assum $ qspec_then ‘v_size’ mp_tac
  \\ gvs [list_size_pair_size_MAP_FST_SND]
End

Theorem v_has_Eval_def = CONV_RULE (DEPTH_CONV ETA_CONV) v_has_Eval_def1

(* s_g = state globals, t_g = removed state globals *)
Definition globals_rel_def:
    globals_rel
      (reachable : num_set) s_g t_g ⇔
        LENGTH s_g = LENGTH t_g ∧
        (∀ n . n ∈ domain reachable ∧ n < LENGTH t_g
          ⇒ EL n s_g = EL n t_g) ∧
        (∀ n x . n < LENGTH t_g ∧ EL n t_g = SOME x
          ⇒ EL n s_g = SOME x) ∧
        (∀ n . n < LENGTH t_g ∧ EL n s_g = NONE
          ⇒ EL n t_g = NONE) ∧
        (∀ n x . n ∈ domain reachable ∧ n < LENGTH t_g ∧
          EL n t_g = SOME x
            ⇒ ~ v_has_Eval x ∧ domain (find_v_globals x) ⊆ domain reachable)
End

Theorem globals_rel_trans:
     ∀ reachable s1 s2 s3 .
        globals_rel reachable s1 s2 ∧ globals_rel reachable s2 s3
        ⇒ globals_rel reachable s1 s3
Proof
    rw[globals_rel_def]
QED

Definition decs_closed_def:
    decs_closed (reachable : num_set) decs ⇔  ∀ r t . analyse_code decs = (r,t)
    ⇒ domain r ⊆ domain reachable ∧
      (∀ n m . n ∈ domain reachable ∧ is_reachable t n m
      ⇒ m ∈ domain reachable)
End

Theorem decs_closed_reduce:
     ∀ reachable h t . decs_closed reachable (h::t) ⇒ decs_closed reachable t
Proof
    fs[decs_closed_def] >> rw[] >> Cases_on `h` >> fs[analyse_code_def]
    >- (Cases_on `analyse_exp e` >> fs[code_analysis_union_def, domain_union])
    >- (
        Cases_on `analyse_exp e` >> fs[code_analysis_union_def, domain_union] >>
        first_x_assum drule >> rw[] >> pop_assum match_mp_tac >>
        fs[Once num_set_tree_union_sym] >>
        irule is_reachable_num_set_tree_union >> simp[]
        )
    >> metis_tac[]
QED

Theorem decs_closed_reduce_HD:
     ∀ reachable h t .
        decs_closed reachable (h::t) ⇒ decs_closed reachable [h]
Proof
    fs[decs_closed_def] >> rw[] >> Cases_on `h` >> fs[analyse_code_def] >>
    Cases_on `analyse_exp e` >>
    fs[code_analysis_union_def, domain_union] >> rveq >> fs[domain_def]
    >- (Cases_on `analyse_code t` >> fs[code_analysis_union_def, domain_union])
    >- (fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
        Cases_on `analyse_code t` >>
        fs[code_analysis_union_def, domain_union] >>
        first_x_assum irule >> goal_assum drule >>
        irule is_reachable_num_set_tree_union >> simp[]
        )
    >> imp_res_tac reachable_domain >> gvs[]
QED

(* s = state, t = removed state *)
Definition flat_state_rel_def:
    flat_state_rel reachable ^s ^t ⇔
      s.clock = t.clock ∧ s.refs = t.refs ∧
      s.ffi = t.ffi ∧ globals_rel reachable s.globals t.globals ∧
      domain (find_refs_globals s.refs) ⊆ domain reachable ∧
      EVERY (EVERY ($~ ∘ v_has_Eval) ∘ store_v_vs) s.refs
End

Theorem flat_state_rel_trans:
  ∀ reachable s1 s2 s3 .
    flat_state_rel reachable s1 s2 ∧
    flat_state_rel reachable s2 s3
  ⇒ flat_state_rel reachable s1 s3
Proof
  rw[flat_state_rel_def, globals_rel_def]
QED

(**************************** FLATLANG LEMMAS *****************************)

Theorem pmatch_Match_reachable:
     (∀ ^s p v l a reachable:num_set . pmatch s p v l = Match a ∧
        domain (find_v_globals v) ⊆ domain reachable ∧
        domain (find_v_globalsL (MAP SND l)) ⊆ domain reachable ∧
        domain (find_refs_globals s.refs) ⊆ domain reachable
    ⇒ domain (find_v_globalsL (MAP SND a)) ⊆ domain reachable)
  ∧
    (∀ ^s p vs l a reachable:num_set .
        pmatch_list s p vs l = Match a ∧
        domain (find_v_globalsL vs) ⊆ domain reachable ∧
        domain (find_v_globalsL (MAP SND l)) ⊆ domain reachable ∧
        domain (find_refs_globals s.refs) ⊆ domain reachable
    ⇒ sptree$domain (find_v_globalsL (MAP SND a)) ⊆ domain reachable)
Proof
    ho_match_mp_tac pmatch_ind >> rw[pmatch_def] >>
    fs[find_v_globals_def, domain_union] >>
    rfs[]
    >- (Cases_on `store_lookup lnum s.refs` >> fs[] >> Cases_on `x` >> fs[] >>
        fs[semanticPrimitivesTheory.store_lookup_def] >>
        first_x_assum (qspec_then `reachable` match_mp_tac) >> rw[] >>
        imp_res_tac find_refs_globals_EL >> metis_tac[SUBSET_TRANS]) >>
    Cases_on `pmatch s p v l` >> fs[domain_union,CaseEq"match_result"]
QED

Theorem find_v_globals_list_to_v_APPEND:
     ∀ xs (reachable:num_set) ys .
        domain (find_v_globalsL xs) ⊆ sptree$domain reachable ∧
        domain(find_v_globalsL ys) ⊆ domain reachable
    ⇒ domain (find_v_globals (list_to_v (xs ++ ys))) ⊆ domain reachable
Proof
    Induct >> fs[list_to_v_def, find_v_globals_def, domain_union] >>
    metis_tac[find_v_globals_list_to_v]
QED

Theorem find_v_globals_Unitv[simp]:
   find_v_globals Unitv = LN
Proof
  EVAL_TAC
QED

Theorem EVERY_EL_IMP:
  EVERY P xs /\ n < LENGTH xs ==> P (EL n xs)
Proof
  simp [EVERY_EL]
QED

Theorem not_v_has_Eval_EVERY_EL[local]:
  EVERY ($~ ∘ v_has_Eval) xs /\ i < LENGTH xs ==> ~ v_has_Eval (EL i xs)
Proof
  simp [EVERY_EL]
QED

val v_has_Eval_Unitv = EVAL ``v_has_Eval Unitv``;

Theorem v_has_Eval_list_to_v:
  v_has_Eval (list_to_v xs) = EXISTS v_has_Eval xs
Proof
  Induct_on `xs` \\ fs [list_to_v_def, v_has_Eval_def]
QED

Theorem v_has_Eval_v_to_list:
  !v xs. v_to_list v = SOME xs ==> v_has_Eval v = EXISTS v_has_Eval xs
Proof
  ho_match_mp_tac v_to_list_ind
  \\ simp [v_to_list_def, v_has_Eval_def]
  \\ rw [option_case_eq, PULL_EXISTS]
  \\ rfs []
QED

fun qif_pat_tac qpat (tac : tactic) goal = if can (rename [qpat]) goal
  then tac goal
  else ALL_TAC goal

fun conseq xs = ConseqConv.CONSEQ_REWRITE_TAC (xs, [], [])

Theorem fvg_map_char_empty[local]:
  find_v_globals (list_to_v (MAP (λc. Litv (Char c)) ss)) = LN
Proof
  Induct_on `ss` \\ simp [find_v_globals_def, list_to_v_def]
QED

Theorem not_LE_LESS_IMP[local]:
  (~ (x >= y)) ==> ((x : num) < y)
Proof
  simp []
QED

Theorem EL_REP_NONE_SOME_trivia[local]:
  n < LENGTH xs + i ==>
  (EL n (xs ++ REPLICATE i NONE) = SOME y <=>
    n < LENGTH xs /\ EL n xs = SOME y)
Proof
  rw [EL_APPEND_EQN]
  \\ simp [EL_REPLICATE]
QED

Theorem pair_case_eq[local]:
  pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v
Proof
  Cases_on `x` >>
 srw_tac[][]
QED

Theorem pair_lam_lem[local]:
  !f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)
Proof
  srw_tac[][]
QED

val eqs = flatSemTheory.case_eq_thms;

Theorem do_app_cases =
  ``do_app st op vs = SOME (st',v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem, CaseEq "thunk_op"] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs])

Theorem do_app_SOME_flat_state_rel:
     ∀ reachable state removed_state op l new_state result new_removed_state.
        flat_state_rel reachable state removed_state ∧ op ≠ Opapp ∧
        domain(find_v_globalsL l) ⊆ domain reachable ∧
        domain (find_lookups (App tra op [])) ⊆ domain reachable ∧
        EVERY ($~ ∘ v_has_Eval) l
          ⇒ do_app state op l = SOME (new_state, result) ∧
            result ≠ Rerr (Rabort Rtype_error)
            ⇒ ∃ new_removed_state .
                flat_state_rel reachable new_state new_removed_state ∧
                do_app removed_state op l =
                    SOME (new_removed_state, result) ∧
                domain (find_sem_prim_res_globals (evaluate$list_result result)) ⊆
                    domain reachable ∧
                EVERY ($~ ∘ v_has_Eval) (result_vs (evaluate$list_result result))
Proof
  rw []
  \\ qpat_assum `flat_state_rel _ _ _` (mp_tac o REWRITE_RULE [flat_state_rel_def])
  \\ rw []
  \\ `∃ this_case . this_case op` by (qexists_tac `K T` >> simp[])
  \\ Cases_on ‘∃a ty. op = Arith a ty’ >- (
    fs [do_app_def]
    \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ gvs [semanticPrimitivesTheory.do_arith_def, AllCaseEqs()]
    \\ simp [do_app_def, semanticPrimitivesTheory.do_arith_def,
              find_sem_prim_res_globals_def, find_result_globals_def,
              find_v_globals_def, v_has_Eval_def, div_exn_v_def, v_to_flat_def]
    \\ rw [find_v_globals_def, v_has_Eval_def,
           semanticPrimitivesTheory.Boolv_def, v_to_flat_def, Boolv_def])
  \\ Cases_on ‘∃ty1 ty2. op = FromTo ty1 ty2’ >- (
    fs [do_app_def]
    \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘ty1’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ Cases_on ‘ty2’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ gvs [semanticPrimitivesTheory.do_conversion_def, AllCaseEqs()]
    \\ simp [do_app_def, semanticPrimitivesTheory.do_conversion_def,
              find_sem_prim_res_globals_def, find_result_globals_def,
              find_v_globals_def, v_has_Eval_def, v_to_flat_def, chr_exn_v_def])
  \\ qpat_x_assum `do_app _ _ _ = SOME _`
      (strip_assume_tac o REWRITE_RULE [do_app_cases])
  \\ rw []
  \\ fs [v_has_Eval_def]
  \\ simp [do_app_def]
  \\ fs [find_sem_prim_res_globals_def, find_v_globals_def,
        find_result_globals_def, chr_exn_v_def, Boolv_def, div_exn_v_def,
        v_has_Eval_def, subscript_exn_v_def, Unitv_def, find_lookups_def,
        dest_GlobalVarLookup_def]
  \\ rfs []
  \\ imp_res_tac not_LE_LESS_IMP
  \\ qif_pat_tac `store_assign _ _ _ = SOME _` (
    fs [semanticPrimitivesTheory.store_assign_def]
    \\ rw []
    \\ simp [flat_state_rel_def, listTheory.IMP_EVERY_LUPDATE,
            find_refs_globals_LUPDATE]
  )
  \\ qif_pat_tac `store_alloc _ _ = _` (
    fs [semanticPrimitivesTheory.store_alloc_def]
    \\ rw []
    \\ simp [flat_state_rel_def,find_refs_globals_APPEND,
            find_refs_globals_def,domain_union]
  )
  \\ qif_pat_tac `this_case (El _)` (
    fs [semanticPrimitivesTheory.store_lookup_def]
    \\ fs [Q.ISPEC `EL _ _` EQ_SYM_EQ |> Q.SPEC `HD _`]
    \\ fs [rich_listTheory.LENGTH_NOT_NULL]
    \\ TRY (rename [`~ NULL xs`] \\ Cases_on `xs` \\ fs [])
    \\ fs [find_v_globals_def, domain_union]
    \\ imp_res_tac EVERY_EL_IMP
    \\ imp_res_tac find_refs_globals_EL
    \\ rfs []
    \\ DEP_REWRITE_TAC [find_v_globalsL_EL_trans]
    \\ simp []
  )
  >- (
    qpat_assum `this_case Explode` kall_tac
    \\ simp [v_has_Eval_list_to_v, EVERY_MAP, v_has_Eval_def,
            fvg_map_char_empty]
  )
  >- (
    drule_then drule find_v_globals_v_to_list
    \\ imp_res_tac v_has_Eval_v_to_list
    \\ fs []
  )
  >- (
    qpat_assum `this_case Vsub` kall_tac
    \\ simp [find_v_globalsL_EL_trans]
    \\ fs [EVERY_EL]
  )
  >- (
    qpat_assum `this_case Vsub_unsafe` kall_tac
    \\ simp [find_v_globalsL_EL_trans]
    \\ fs [EVERY_EL]
  )
  >- metis_tac[find_v_globalsL_REPLICATE,SUBSET_TRANS]
  >- (
    qpat_assum `this_case Asub` kall_tac
    \\ fs [semanticPrimitivesTheory.store_lookup_def]
    \\ DEP_REWRITE_TAC [find_v_globalsL_EL_trans, not_v_has_Eval_EVERY_EL]
    \\ imp_res_tac find_refs_globals_EL
    \\ imp_res_tac EVERY_EL_IMP
    \\ rfs []
  )
  >- (
    qpat_assum `this_case Aupdate` kall_tac
    \\ fs [semanticPrimitivesTheory.store_lookup_def]
    \\ DEP_REWRITE_TAC (listTheory.IMP_EVERY_LUPDATE
        :: RES_CANON find_refs_globals_LUPDATE)
    \\ simp []
    \\ DEP_REWRITE_TAC [find_v_globalsL_LUPDATE, listTheory.IMP_EVERY_LUPDATE]
    \\ simp []
    \\ imp_res_tac find_refs_globals_EL
    \\ imp_res_tac EVERY_EL_IMP
    \\ rfs []
  )
  >- (
    qpat_assum `this_case Asub_unsafe` kall_tac
    \\ fs [semanticPrimitivesTheory.store_lookup_def]
    \\ DEP_REWRITE_TAC [find_v_globalsL_EL_trans, not_v_has_Eval_EVERY_EL]
    \\ imp_res_tac find_refs_globals_EL
    \\ imp_res_tac EVERY_EL_IMP
    \\ rfs []
  )
  >- (
    qpat_assum `this_case Aupdate_unsafe` kall_tac
    \\ fs [semanticPrimitivesTheory.store_lookup_def]
    \\ DEP_REWRITE_TAC (listTheory.IMP_EVERY_LUPDATE
        :: RES_CANON find_refs_globals_LUPDATE)
    \\ simp []
    \\ DEP_REWRITE_TAC [find_v_globalsL_LUPDATE, listTheory.IMP_EVERY_LUPDATE]
    \\ simp []
    \\ imp_res_tac find_refs_globals_EL
    \\ imp_res_tac EVERY_EL_IMP
    \\ rfs []
  )
  >- (
    qpat_assum `this_case ListAppend` kall_tac
    \\ imp_res_tac v_has_Eval_v_to_list
    \\ rfs [v_has_Eval_list_to_v, domain_union]
    \\ metis_tac[find_v_globals_v_to_list, find_v_globals_list_to_v_APPEND]
  )
  >- (
    qpat_assum `this_case (GlobalVarAlloc _)` kall_tac
    \\ fs [flat_state_rel_def, globals_rel_def]
    \\ simp [listTheory.EL_APPEND_EQN, EL_REPLICATE, bool_case_eq]
    \\ csimp [EL_REPLICATE]
    \\ metis_tac []
  )
  >- (
    qpat_assum `this_case (GlobalVarInit _)` kall_tac
    \\ fs [flat_state_rel_def, globals_rel_def]
    \\ simp [EL_LUPDATE, bool_case_eq]
    \\ metis_tac []
  )
  >- (
    qpat_assum `this_case (GlobalVarLookup _)` kall_tac
    \\ fs [flat_state_rel_def, globals_rel_def, IS_SOME_EXISTS]
    \\ rfs []
    \\ metis_tac []
  )
QED


(**************************** MAIN LEMMAS *****************************)

Theorem flat_state_rel_pmatch:
  (! ^new_state p a env.
    flat_state_rel reachable new_state new_removed_state ==>
    pmatch new_removed_state p a env =
    pmatch new_state p a env) /\
  (! ^new_state p a env.
    flat_state_rel reachable new_state new_removed_state ==>
    pmatch_list new_removed_state p a env =
    pmatch_list new_state p a env)
Proof
  ho_match_mp_tac pmatch_ind \\ rw []
  \\ fs [pmatch_def,flat_state_rel_def]
  \\ rw [] \\ fs [] \\ rpt (CASE_TAC \\ fs [])
QED

Theorem flat_state_rel_pmatch_rows:
  flat_state_rel reachable new_state new_removed_state ==>
  pmatch_rows (pes: (pat # exp) list) new_removed_state a =
  pmatch_rows pes new_state a
Proof
  Induct_on `pes` \\ fs [pmatch_rows_def,FORALL_PROD]
  \\ rw [] \\ fs []
  \\ drule (CONJUNCT1 flat_state_rel_pmatch) \\ fs []
QED

Theorem pmatch_rows_find_lookups:
  pmatch_rows pes q a = Match (env',p',e') /\
  domain (find_lookupsL (MAP SND pes)) ⊆ domain reachable ==>
  domain (find_lookups e') ⊆ sptree$domain reachable
Proof
  Induct_on `pes` \\ fs [pmatch_rows_def,FORALL_PROD]
  \\ fs [CaseEq"match_result"] \\ rw []
  \\ fs [find_lookups_def,domain_union]
QED

Theorem pmatch_not_has_Eval:
  (
  ! ^s p v bindings env.
  pmatch s p v bindings = Match env /\ ~ v_has_Eval v /\
  EVERY (EVERY ($~ ∘ v_has_Eval) ∘ store_v_vs) s.refs /\
  EVERY ($~ ∘ v_has_Eval ∘ SND) bindings ==>
  EVERY ($~ ∘ v_has_Eval ∘ SND) env
  ) /\ (
  ! ^s ps vs bindings env.
  pmatch_list s ps vs bindings = Match env /\
  EVERY ($~ ∘ v_has_Eval) vs /\
  EVERY (EVERY ($~ ∘ v_has_Eval) ∘ store_v_vs) s.refs /\
  EVERY ($~ ∘ v_has_Eval ∘ SND) bindings ==>
  EVERY ($~ ∘ v_has_Eval ∘ SND) env
  )
Proof
  ho_match_mp_tac pmatch_ind
  \\ simp [pmatch_def]
  \\ rw []
  \\ simp []
  \\ fs [v_has_Eval_def, option_case_eq, case_eq_thms]
  \\ rfs []
  >- (
    fs [semanticPrimitivesTheory.store_lookup_def]
    \\ drule_then drule EVERY_EL_IMP
    \\ simp []
  )
  \\ fs [CaseEq "match_result"]
  \\ fs []
QED

Theorem has_Eval_def[local]:
  (has_Eval (Handle _ e pes) = (has_Eval e ∨ EXISTS has_Eval (MAP SND pes))) ∧
  (has_Eval (Con _ _ es) = EXISTS has_Eval es) ∧
  (has_Eval (Fun _ _ e) = has_Eval e) ∧
  (has_Eval (App t op es) = (op = Eval ∨ EXISTS has_Eval es)) ∧
  (has_Eval (If t e1 e2 e3) = (has_Eval e1 ∨ has_Eval e2 ∨ has_Eval e3)) ∧
  (has_Eval (Mat t e pes) = (has_Eval e ∨ EXISTS has_Eval (MAP SND pes))) ∧
  (has_Eval (Let _ opt e1 e2) = (has_Eval e1 ∨ has_Eval e2)) ∧
  (has_Eval (Letrec _ funs e) = (has_Eval e ∨ EXISTS has_Eval (MAP (SND o SND) funs))) ∧
  (has_Eval (Raise _ e) = has_Eval e) ∧
  (has_Eval (Var_local _ _) = F) ∧
  (has_Eval (Lit _ v) = F)
Proof
  ‘∀es. has_Eval_list es <=> EXISTS has_Eval es’ by
     (Induct \\ fs [flat_elimTheory.has_Eval_def])
  \\ ‘∀pes. has_Eval_pats pes <=> EXISTS has_Eval (MAP SND pes)’ by
     (Induct \\ fs [flat_elimTheory.has_Eval_def,FORALL_PROD])
  \\ ‘∀pes. has_Eval_funs pes <=> EXISTS has_Eval (MAP (SND o SND) pes)’ by
     (Induct \\ fs [flat_elimTheory.has_Eval_def,FORALL_PROD])
  \\ rw [] \\ simp [Once flat_elimTheory.has_Eval_def]
QED

(******** EVALUATE INDUCTION ********)

val evaluate_exp_ind = evaluate_ind
  |> Q.SPECL [`P`, `\_ _. T`, `\_ _. T`]
  |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
  |> Q.GEN `P`

Theorem evaluate_keep_flat_state_rel_eq_lemma:
    (∀ env ^state exprL new_state
        result reachable:num_set removed_state .
        flatSem$evaluate env state exprL = (new_state, result) ∧
        domain (find_lookupsL exprL) ⊆ domain reachable ∧
        flat_state_rel reachable state removed_state ∧
        domain (find_env_globals env) ⊆ domain reachable ∧
        EVERY (($~) ∘ v_has_Eval ∘ SND) env.v ∧
        EVERY (($~) ∘ has_Eval) exprL ∧
        result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate env removed_state exprL = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state ∧
        domain (find_sem_prim_res_globals result) ⊆ domain reachable ∧
        EVERY (($~) ∘ v_has_Eval) (result_vs result))
Proof
  ho_match_mp_tac evaluate_exp_ind >> rpt CONJ_TAC >> rpt GEN_TAC >>
  TRY strip_tac >>
  TRY (simp [] >> NO_TAC)
  (* EVALUATE CASES *)
  >- ( (* EMPTY LIST CASE *)
    fs[evaluate_def] >> rveq >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def]
    )
  >- ( (* NON_EMPTY, NON-SINGLETON LIST CASE *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> Cases_on `evaluate env state' [e1]` >>
    fs[find_lookups_def, domain_union] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
    strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
    Cases_on `evaluate env q (e2::es)` >> fs[] >>
    first_x_assum (
        qspecl_then [`reachable`, `new_removed_state`] mp_tac) >>
    fs[] >>
    reverse(Cases_on `r` >> fs[])
    >- (
      rw[] >> fs[]
    )
    >- (
      strip_tac >> rw[] >>
      fs[find_sem_prim_res_globals_def,
          find_v_globals_def, domain_union] >>
      imp_res_tac evaluate_sing >> rveq >> rveq >>
      fs[find_v_globals_def]
      )
    )
  (* SINGLETON LIST CASES *)
  >- ( (* Lit *)
    fs[evaluate_def] >> rveq >> fs[] >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def, v_has_Eval_def]
    )
  >- ( (* Raise *)
    rpt gen_tac >> strip_tac >> fs[find_lookups_def, has_Eval_def] >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def, pair_case_eq] >>
    strip_tac >> fs [] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
    impl_tac >- (CCONTR_TAC >> fs[]) >>
    strip_tac >>
    fs[case_eq_thms] >> rveq >> fs[] >>
    fs[find_sem_prim_res_globals_def,
        find_v_globals_def, find_result_globals_def] >>
    imp_res_tac evaluate_sing >> rveq >> rveq >> fs[find_v_globals_def]
    )
  >- ( (* Handle *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >>
    Cases_on `evaluate env state' [e]` >> fs[] >>
    fs[find_lookups_def, domain_union, has_Eval_def] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >> fs[] >>
    strip_tac >>
    Cases_on `r` >> rw[] >> rfs[] >>
    Cases_on `e'` >> rw[] >> rfs[] >> rveq >> rfs[] >>
    fs [CaseEq"match_result",pair_case_eq,CaseEq"bool"] >> rveq >> fs [] >>
    drule flat_state_rel_pmatch_rows >> fs [] >>
    rfs [] >> strip_tac >> first_x_assum match_mp_tac >> fs [] >>
    conj_tac THEN1 metis_tac [pmatch_rows_find_lookups] >>
    fs [find_env_globals_def] >>
    fs[find_env_globals_def, find_v_globalsL_APPEND, domain_union] >>
    imp_res_tac pmatch_rows_IMP_pmatch >>
    drule (CONJUNCT1 pmatch_not_has_Eval) >>
    fs [flat_state_rel_def] >>
    fs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    res_tac >>
    fs [] >>
    rw [] >>
    drule_then irule (CONJUNCT1 pmatch_Match_reachable) >>
    fs[find_v_globals_def] >>
    fs [find_sem_prim_res_globals_def,find_result_globals_def]
    )
  >- ( (* Con NONE *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, has_Eval_def, EVERY_REVERSE] >>
    fs[] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    simp[Once find_lookupsL_REVERSE] >> fs[] >>
    strip_tac >>
    Cases_on `r` >>
    rw[] >> rfs[] >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def,
        v_has_Eval_def, EVERY_REVERSE] >>
    simp[Once find_v_globalsL_REVERSE]
    )
  >- ( (* Con SOME *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, has_Eval_def, EVERY_REVERSE] >>
    fs[] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    simp[Once find_lookupsL_REVERSE] >> fs[] >>
    strip_tac >> Cases_on `r` >> rw[] >> rfs[] >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def,
        v_has_Eval_def, EVERY_REVERSE] >>
    simp[Once find_v_globalsL_REVERSE]
    )
  >- ( (* Var_local *)
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> strip_tac >> rveq >> fs[find_lookups_def] >>
    Cases_on `ALOOKUP env.v n` >>
    fs[find_sem_prim_res_globals_def, find_v_globals_def] >>
    imp_res_tac ALOOKUP_MEM >> imp_res_tac find_v_globalsL_MEM >>
    fs[find_env_globals_def] >> fs[SUBSET_DEF] >>
    fs[EVERY_MEM] >> res_tac >> fs []
    )
  >- ( (* Fun *)
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> strip_tac >> rveq >>
    fs[find_sem_prim_res_globals_def,
        find_env_globals_def, find_v_globals_def] >>
    fs[domain_union, find_lookups_def] >>
    fs[v_has_Eval_def, has_Eval_def, EVERY_MAP, o_DEF]
    )
  >- ( (* App *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, has_Eval_def, EVERY_REVERSE] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    first_x_assum (
        qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    simp[Once find_lookupsL_REVERSE] >> fs[] >>
    strip_tac >> fs[] >>
    `domain (find_lookupsL es) ⊆ domain reachable` by (
        Cases_on `op` >> fs[dest_GlobalVarLookup_def] >>
        fs[domain_insert]) >>
    fs[] >>
    Cases_on `r` >> fs[] >> strip_tac >> rveq >> fs[] >> rfs[] >>
    Cases_on `op = Opapp` >> fs[]
    >- (
      Cases_on `do_opapp (REVERSE a)` >> fs[] >>
      Cases_on `x` >> fs[] >>
      Cases_on `q.clock = 0` >> fs[]
      >- (
        rveq >>
        qpat_x_assum
            `flat_state_rel reachable new_state _` mp_tac >>
        simp[Once flat_state_rel_def] >> strip_tac >> rveq >>
        fs[flat_state_rel_def,
            find_sem_prim_res_globals_def, find_result_globals_def]
        )
      >- (
        first_x_assum (qspecl_then
            [`reachable`, `dec_clock new_removed_state`] mp_tac) >>
        fs[] >>
        qpat_x_assum `flat_state_rel reachable q _` mp_tac >>
        simp[Once flat_state_rel_def] >>
        strip_tac >> strip_tac >>
        qpat_x_assum `_ ⇒ _` match_mp_tac  >>
        fs[flat_state_rel_def, globals_rel_def,
            dec_clock_def, find_env_globals_def] >> rfs[] >> rveq >>
        asm_rewrite_tac [] >>
        fs[do_opapp_def] >> EVERY_CASE_TAC >> fs[] >> rveq >>
        fs[find_sem_prim_res_globals_def] >>
        fs[SWAP_REVERSE_SYM, find_v_globals_def, domain_union, v_has_Eval_def,
            o_DEF, EVERY_MAP] >>
        rw[]
        >- (
          fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
          imp_res_tac ALOOKUP_MEM >>
          fs [MEM_SPLIT] >>
          fs [find_lookupsL_APPEND, domain_union, find_lookups_def]
          )
        >- (
          fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
          fs[find_v_globalsL_APPEND, domain_union] >>
          fs[MAP_MAP_o] >>
          simp [ELIM_UNCURRY, o_DEF, find_v_globals_MAP_Recclosure] >>
          rw []
          )
        >- (
          fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
          fs[EVERY_MAP, ELIM_UNCURRY, v_has_Eval_def]
          )
        >- (
          fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
          imp_res_tac ALOOKUP_MEM >>
          fs [EVERY_MEM] >> res_tac >> fs []
          )
        >- (
          fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
          imp_res_tac ALOOKUP_MEM >>
          fs [MEM_SPLIT] >>
          fs [find_lookupsL_APPEND, domain_union, find_lookups_def]
          )
        >- (
          fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
          fs[find_v_globalsL_APPEND, domain_union] >>
          fs[MAP_MAP_o] >>
          simp [ELIM_UNCURRY, o_DEF, find_v_globals_MAP_Recclosure] >>
          rw []
          )
        >- (
          fs[build_rec_env_def] >> fs[FOLDR_CONS_triple] >>
          fs [EVERY_MAP, ELIM_UNCURRY, v_has_Eval_def]
          )
       >- (
          fs[semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
          imp_res_tac ALOOKUP_MEM >>
          fs [EVERY_MEM] >> res_tac >> fs []
          )
        )
      )
    >- (
      Cases_on `op = ThunkOp ForceThunk` >> gvs []
      >- (
        gvs [AllCaseEqs(), dec_clock_def, dest_GlobalVarLookup_def, PULL_EXISTS]
        >- (
          gvs [oneline dest_thunk_def, AllCaseEqs(),
               semanticPrimitivesTheory.store_lookup_def, flat_state_rel_def,
               EVERY_EL] >>
          first_x_assum drule >> gvs [] >> rw [] >>
          gvs [find_sem_prim_res_globals_def, find_v_globals_def] >>
          drule_all find_refs_globals_EL >> rw [])
        >- (
          gvs [oneline dest_thunk_def, AllCaseEqs(),
               semanticPrimitivesTheory.store_lookup_def, flat_state_rel_def] >>
          simp [PULL_EXISTS] >>
          last_x_assum $ qspecl_then
            [`reachable`, `new_removed_state`] mp_tac >>
          impl_tac
          >- (
            gvs [AppUnit_def, find_lookups_def, dest_GlobalVarLookup_def,
                 find_env_globals_def, find_v_globals_def, has_Eval_def,
                 EVERY_EL] >>
            first_x_assum drule >> rw [] >>
            drule_all find_refs_globals_EL >> rw []) >>
          rw [] >>
          goal_assum drule >> simp [] >>
          gvs [oneline update_thunk_def, AllCaseEqs(),
               semanticPrimitivesTheory.store_assign_def,
               find_sem_prim_res_globals_def, find_v_globals_def] >>
          rw []
          >- (drule_all find_refs_globals_LUPDATE >> gvs []) >>
          gvs [EVERY_EL, EL_LUPDATE] >> rw [])
        >- (
          gvs [oneline dest_thunk_def, AllCaseEqs(),
               semanticPrimitivesTheory.store_lookup_def, flat_state_rel_def] >>
          last_x_assum $ qspecl_then
            [`reachable`, `new_removed_state`] mp_tac >>
          impl_tac
          >- (
            gvs [AppUnit_def, find_lookups_def, dest_GlobalVarLookup_def,
                 find_env_globals_def, find_v_globals_def, has_Eval_def,
                 EVERY_EL] >>
            first_x_assum drule >> rw [] >>
            drule_all find_refs_globals_EL >> rw []) >>
          rw [] >>
          goal_assum drule >> simp [])) >>
      Cases_on `do_app q op (REVERSE a)` >> fs[] >>
      PairCases_on `x` >> fs[] >> rveq >>
      drule (GEN_ALL do_app_SOME_flat_state_rel) >>
      fs[find_lookups_def] >> disch_then drule >> strip_tac >>
      pop_assum (qspecl_then [
          `REVERSE a`, `new_state`, `x1`] mp_tac) >>
          simp[Once find_v_globalsL_REVERSE] >>
      fs[EVERY_REVERSE] >> strip_tac >>
      `domain (case dest_GlobalVarLookup op of
          NONE => LN | SOME n => insert n () LN) ⊆ domain reachable`
              by (Cases_on `dest_GlobalVarLookup op` >> fs[]) >>
      fs[find_sem_prim_res_globals_def] >> rfs[] >>
      fs[]
      )
    )
  >- ( (* If *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
    Cases_on `evaluate env state' [e1]` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[has_Eval_def] >>
    strip_tac >> strip_tac >> fs[] >>
    `r ≠ Rerr(Rabort Rtype_error)` by
        (CCONTR_TAC >> Cases_on `r` >> fs[]) >>
    fs[] >>
    Cases_on `r` >> fs[] >>
    Cases_on `do_if (HD a) e2 e3` >> fs[] >>
    fs[do_if_def] >>
    first_x_assum match_mp_tac >>
    fs[] >>
    fs[flat_state_rel_def] >>
    EVERY_CASE_TAC >> fs[]
    )
  >- ( (* Mat *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
    Cases_on `evaluate env state' [e]` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[has_Eval_def] >>
    strip_tac >> strip_tac >>
    `r ≠ Rerr(Rabort Rtype_error)` by
        (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
    Cases_on `r` >> fs[] >>
    fs [CaseEq"match_result",pair_case_eq,CaseEq"bool"] >> rveq >> fs [] >>
    drule flat_state_rel_pmatch_rows >> fs [] THEN1 EVAL_TAC >>
    rfs [] >> strip_tac >> first_x_assum match_mp_tac >> fs [] >>
    conj_tac THEN1 metis_tac [pmatch_rows_find_lookups] >>
    fs [find_env_globals_def] >>
    imp_res_tac evaluate_sing >> rveq >> fs [] >>
    fs[find_env_globals_def, find_v_globalsL_APPEND, domain_union] >>
    imp_res_tac pmatch_rows_IMP_pmatch >>
    drule (CONJUNCT1 pmatch_not_has_Eval) >>
    fs [flat_state_rel_def] >>
    fs [EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    res_tac >>
    fs [] >>
    rw [] >>
    drule (CONJUNCT1 pmatch_Match_reachable) >>
    disch_then match_mp_tac >>
    fs[find_v_globals_def] >>
    fs [find_sem_prim_res_globals_def,find_result_globals_def] >>
    fs [flat_state_rel_def,find_v_globals_def]
    )
  >- ( (* Let *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
    Cases_on `evaluate env state' [e1]` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[has_Eval_def] >>
    strip_tac >> strip_tac >>
    `r ≠ Rerr(Rabort Rtype_error)` by
        (CCONTR_TAC >> Cases_on `r` >> fs[]) >> fs[] >>
    Cases_on `r` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `new_removed_state`]
        match_mp_tac) >> fs[] >>
    fs[find_env_globals_def, miscTheory.opt_bind_def] >>
    Cases_on `n` >> fs[] >>
    fs[find_v_globals_def, domain_union] >>
    fs[find_sem_prim_res_globals_def] >> imp_res_tac evaluate_sing >>
    rveq >> fs[] >> rveq >> fs[find_v_globals_def]
    )
  >- ( (* Letrec *)
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `evaluate _ _ _ = _` mp_tac >>
    simp[evaluate_def] >> fs[find_lookups_def, domain_union] >>
    Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
    strip_tac >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`]
        match_mp_tac) >> fs[] >>
    fs[find_env_globals_def, build_rec_env_def, has_Eval_def] >>
    fs[FOLDR_CONS_triple] >> fs[find_v_globalsL_APPEND, domain_union] >>
    fs[MAP_MAP_o, EVERY_MAP] >>
    fs [ELIM_UNCURRY, o_DEF, v_has_Eval_def, EVERY_MAP] >>
    simp [find_v_globals_MAP_Recclosure] >>
    rw [o_DEF]
  )
QED

(******** EVALUATE SPECIALISATION ********)

Theorem evaluate_sing_keep_flat_state_rel_eq:
    ∀ env ^state exprL new_state result expr
      reachable removed_state .
      flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧
      flat_state_rel reachable state removed_state ∧
      exprL = [expr] ∧
      keep reachable (Dlet expr) ∧
      domain(find_lookups expr) ⊆ domain reachable ∧
      ~ has_Eval expr ∧
      result ≠ Rerr (Rabort Rtype_error)
    ⇒ ∃ new_removed_state .
        evaluate (env with v := []) removed_state exprL
            = (new_removed_state, result) ∧
        flat_state_rel reachable new_state new_removed_state
Proof
  rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
  drule evaluate_keep_flat_state_rel_eq_lemma >> fs[] >>
  strip_tac >> pop_assum (qspecl_then [`reachable`, `removed_state`]
      mp_tac) >> fs[] >>
  impl_tac >> fs[] >>
  simp[find_env_globals_def, find_v_globals_def, Once find_lookups_def] >>
  simp[EVAL ``find_lookupsL []``] >> rw[] >> fs[]
QED

(******** EVALUATE_DEC ********)

Theorem evaluate_dec_flat_state_rel:
  ∀ ^state dec new_state result
    reachable removed_state .
    evaluate_dec state dec = (new_state, result) ∧
    decs_closed reachable [dec] ∧
    flat_state_rel reachable state removed_state ∧ keep reachable dec ∧
    ~ has_Eval_dec dec ∧
    result ≠ SOME (Rabort Rtype_error)
  ⇒ ∃ new_removed_state .
      evaluate_dec removed_state dec =
          (new_removed_state, result) ∧
      flat_state_rel reachable new_state new_removed_state
Proof
  rw[] >> qpat_x_assum `evaluate_dec _ _ = _` mp_tac >>
  reverse(Induct_on `dec`) >> fs[evaluate_def] >> strip_tac >>
  strip_tac >>
  fs[keep_def] >>
  rpt strip_tac >>
  fs [pair_case_eq] >>
  drule_then drule evaluate_sing_keep_flat_state_rel_eq >>
  fs [keep_def, has_Eval_dec_def] >>
  `domain (find_lookups e) ⊆ domain reachable` by (
    fs[decs_closed_def] >> fs[analyse_code_def] >>
    fs[analyse_exp_def] >>
    reverse(Cases_on `is_pure e`) >> fs[]
    >- (fs[code_analysis_union_def] >> fs[domain_union]) >>
    reverse(Cases_on `is_hidden e`) >> fs[] >>
    fs[code_analysis_union_def, domain_union] >>
    fs[Once num_set_tree_union_sym, num_set_tree_union_def] >>
    simp[SUBSET_DEF] >>
    rw[] >> first_x_assum match_mp_tac >>
    fs[spt_eq_thm, lookup_inter_alt] >>
    fs[lookup_def] >> Cases_on `lookup n (find_loc e)` >> fs[] >>
    fs[domain_lookup] >>
    asm_exists_tac >> fs[] >> fs[is_reachable_def] >>
    match_mp_tac RTC_SINGLE >> fs[is_adjacent_def] >>
    fs[lookup_map]
  ) >>
  simp [] >>
  impl_tac >- (CCONTR_TAC >> fs []) >>
  EVERY_CASE_TAC >> fs[] >> rw[] >>
  fs[flat_state_rel_def]
QED

Theorem total_pat_IMP:
  (! ^s p v env res.
     pmatch s p v env = res /\ total_pat p ==> res <> No_match) /\
  (! ^s ps vs env res.
     LENGTH ps = LENGTH vs /\
     pmatch_list s ps vs env = res /\
     total_pat_list ps ==> res <> No_match)
Proof
  ho_match_mp_tac pmatch_ind \\ rw []
  \\ fs [pmatch_def,CaseEq"bool",total_pat_def]
  \\ CCONTR_TAC \\ fs []
  \\ fs [pmatch_stamps_ok_cases]
  \\ rveq
  \\ fs [total_pat_def]
  \\ fs [CaseEq"match_result"] \\ fs []
QED

Theorem EXISTS_total_pat:
  EXISTS total_pat (MAP FST pes) ==>
  pmatch_rows pes new_state v <> No_match
Proof
  Induct_on `pes` \\ fs [pmatch_rows_def,FORALL_PROD]
  \\ strip_tac
  \\ reverse (Cases_on `EXISTS total_pat (MAP FST pes)`)
  \\ full_simp_tac std_ss [] THEN1
   (rw [] \\ Cases_on `pmatch new_state p_1 v []` \\ fs []
    \\ drule (CONJUNCT1 total_pat_IMP) \\ fs [] \\ fs [CaseEq"match_result"])
  \\ Cases_on `pmatch_rows pes new_state v` \\ fs []
  \\ fs [CaseEq"match_result"]
QED


(********************** CASE: *NOT* keep reachable h ***********************)

(******** EVALUATE MUTUAL INDUCTION ********)

Theorem evaluate_flat_state_rel_lemma:
  (∀ env ^state exprL new_state result
      reachable removed_state .
      flatSem$evaluate env state exprL = (new_state, result) ∧
      EVERY is_pure exprL ∧
      EVERY (($~) ∘ v_has_Eval ∘ SND) env.v ∧
      EVERY (($~) ∘ has_Eval) exprL ∧
      EVERY (λ e. isEmpty (inter (find_loc e) reachable)) exprL ∧
      flat_state_rel reachable state removed_state ∧
      result ≠ Rerr (Rabort Rtype_error)
  ⇒ ?values. flat_state_rel reachable new_state removed_state ∧
      result = Rval values ∧
      EVERY (($~) ∘ v_has_Eval) values)
Proof
  ho_match_mp_tac evaluate_exp_ind >> rpt CONJ_TAC >> rpt GEN_TAC
  >> TRY (simp [] >> NO_TAC) >> strip_tac
  (* EVALUATE_DECS_CASES *)
  >- ( (* EMPTY LIST CASE *)
      fs[evaluate_def] >> rveq >> fs[find_v_globals_def]
      )
  >- ( (* NON-EMPTY, NON-SINGLETON LIST CASE *)
    rpt gen_tac >> strip_tac >>
    qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >>
    Cases_on `evaluate env state' [e1]` >> fs[] >>
    Cases_on `r` >> fs[]
    >- (
      Cases_on `evaluate env q (e2 :: es)` >> fs[] >>
      first_x_assum drule >> disch_then drule >>
      fs[] >> Cases_on `r` >> fs[]
      >- (
        first_x_assum (qspecl_then [`reachable`, `removed_state`]
            mp_tac) >> fs[] >>
        rw[] >> fs[find_v_globals_def, domain_union] >>
        imp_res_tac evaluate_sing >>
        fs [] >>
        first_x_assum match_mp_tac >>
        fs[]
        )
      >- (
        rveq >>
        fs[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >> rw[] >> fs[] >>
        qpat_x_assum `EXISTS _ _` mp_tac >>
        once_rewrite_tac [GSYM NOT_EVERY] >> strip_tac
        )
      )
    >- (
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[] >> rw[] >> fs[]
      )
    )
      (* SINGLETON LIST CASES *)
  >- ( (* Lit *)
    fs[evaluate_def] >> rveq >> fs[find_v_globals_def, v_has_Eval_def]
    )
  >- ((* Raise *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >> Cases_on `evaluate env state' [e]` >> fs[] >>
    Cases_on `r` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[is_pure_def1]
    )
  >- ( (* Handle *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def, has_Eval_def] >>
    Cases_on `evaluate env state' [e]` >> fs[] >>
    Cases_on `r` >> fs[]
    >- (rveq >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[is_pure_def1] >> strip_tac >>
        qpat_x_assum `isEmpty _` mp_tac >>
        simp[Once find_loc_def] >>
        strip_tac >>
        qpat_x_assum `isEmpty _ ⇒ _` match_mp_tac >> fs[] >>
        imp_res_tac inter_union_empty)
    >- (fs[is_pure_def1] >>
        qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
        strip_tac >>
        `isEmpty(inter (find_locL (MAP SND pes)) reachable) ∧
        isEmpty (inter (find_loc e) reachable)` by
            metis_tac[inter_union_empty] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        fs[] >> strip_tac >> fs[])
    )
  >- ( (* Con NONE *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def, has_Eval_def] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    Cases_on `r` >> fs[]
    >- (
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[] >>
      strip_tac >> rveq >>
      fs[is_pure_def1, find_v_globals_def] >> fs[EVERY_REVERSE] >>
      simp[Once find_v_globalsL_REVERSE] >> fs[] >>
      rfs[v_has_Eval_def, EVERY_REVERSE] >>
      qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
      strip_tac >>
      fs[find_loc_EVERY_isEmpty]
      )
    >- (
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[] >>
      rveq >> fs[is_pure_def1] >> fs[EVERY_REVERSE] >>
      once_rewrite_tac [(GSYM NOT_EXISTS)] >>
      once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
      qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
      fs[find_loc_EVERY_isEmpty]
      )
    )
  >- ( (* Con SOME *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >>
    strip_tac >> fs[evaluate_def] >>
    fs [bool_case_eq] >>
    rfs[] >> fs[] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    Cases_on `r` >>
    fs[has_Eval_def] >>
    fs[is_pure_def1, EVERY_REVERSE] >> rveq >>
    fs[find_loc_EVERY_isEmpty, v_has_Eval_def, EVERY_REVERSE] >>
    qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
    strip_tac >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[EVERY_REVERSE] >>
    once_rewrite_tac [(GSYM NOT_EXISTS)] >>
    once_rewrite_tac [GSYM NOT_EVERY] >>
    fs[find_loc_EVERY_isEmpty]
    )
  >- ( (* Var_local *)
    fs[evaluate_def] >> Cases_on `ALOOKUP env.v n` >> fs[] >>
    rveq >> fs[] >>
    fs[find_v_globals_def, find_env_globals_def, EVERY_MEM] >>
    imp_res_tac ALOOKUP_MEM >>
    res_tac >> fs [] >>
    imp_res_tac find_v_globalsL_MEM >> imp_res_tac SUBSET_TRANS
    )
  >- ( (* Fun *)
    qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >>
    strip_tac >> fs[evaluate_def] >>
    rveq >>
    fs[find_v_globals_def, domain_union,
        find_env_globals_def, is_pure_def1, v_has_Eval_def, has_Eval_def] >>
    fs[find_loc_def, EVERY_MAP, o_DEF]
    )
  >- ( (* App *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >>
    Cases_on `evaluate env state' (REVERSE es)` >> fs[] >>
    fs[is_pure_def1] >> qpat_x_assum `isEmpty _` mp_tac >>
    simp[Once find_loc_def] >>
    strip_tac >> fs[] >> fs[EVERY_REVERSE] >> fs[find_loc_EVERY_isEmpty] >>
    Cases_on `r` >> fs[]
    >- (
      Cases_on `op = Opapp` >> fs[is_pure_def1, dest_GlobalVarInit_def] >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      strip_tac >>
      Cases_on `op` >>
      fs[is_pure_def1, dest_GlobalVarInit_def, do_app_def] >>
      rfs [has_Eval_def] >>
      fs[] >> imp_res_tac inter_insert_empty >>
      EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >>
      simp[v_has_Eval_Unitv] >>
      fs[find_v_globals_def, flat_state_rel_def] >> rw[] >>
      fs[] >> rfs[] >>
      fs[globals_rel_def] >>
      fs[LUPDATE_SEM] >>
      simp [EL_LUPDATE, bool_case_eq] >>
      metis_tac []
      )
    >- (
      rveq >> fs[] >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[has_Eval_def] >>
      once_rewrite_tac [(GSYM NOT_EXISTS)] >>
      once_rewrite_tac [GSYM NOT_EVERY] >> fs[] >>
      Cases_on `op` >>
      fs[is_pure_def1, dest_GlobalVarInit_def] >>
      imp_res_tac inter_insert_empty
      )
    )
  >- ( (* If *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >> Cases_on `evaluate env state' [e1]` >> fs[] >>
    fs[is_pure_def1, has_Eval_def] >>
    qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
    strip_tac >>
    `isEmpty (inter (find_loc e1) reachable) ∧
        isEmpty (inter (find_loc e2) reachable) ∧
        isEmpty (inter (find_loc e3) reachable)` by
            metis_tac[inter_union_empty] >>
    Cases_on `r` >> fs[]
    >- (
      fs[do_if_def, Boolv_def] >> Cases_on `HD a` >> fs[] >>
      EVERY_CASE_TAC >> fs[] >>
      rveq >> first_x_assum (qspecl_then [`reachable`, `removed_state`]
          mp_tac) >> fs[] >>
      strip_tac >> rfs[] >>
      first_x_assum (drule_then drule) >>
      fs[]
      )
    >- (
      rveq >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[]
      )
    )
  >- ( (* Mat *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >>
    Cases_on `evaluate env state' [e]` >> fs[] >>
    fs[is_pure_def1, has_Eval_def] >>
    qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
    strip_tac >>
    `isEmpty (inter (find_locL (MAP SND pes)) reachable) ∧
        isEmpty (inter (find_loc e) reachable)` by
            metis_tac[inter_union_empty] >>
    reverse (Cases_on `r`) >> fs[]
    THEN1 (rveq \\ fs [] \\ metis_tac [])
    \\ fs [CaseEq"match_result",pair_case_eq,CaseEq"bool"] \\ rveq \\ fs []
    \\ imp_res_tac EXISTS_total_pat \\ fs []
    \\ last_x_assum match_mp_tac \\ first_x_assum drule
    \\ disch_then drule \\ fs [] \\ strip_tac
    \\ drule pmatch_rows_IMP_pmatch \\ strip_tac
    \\ fs [GSYM find_loc_EVERY_isEmpty]
    \\ drule (CONJUNCT1 pmatch_not_has_Eval)
    \\ imp_res_tac evaluate_sing
    \\ fs [flat_state_rel_def]
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ res_tac \\ fs []
    \\ fs [flat_state_rel_def]
    )
  >- ( (* Let *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >>
    Cases_on `evaluate env state' [e1]` >> fs[is_pure_def1, has_Eval_def] >>
    fs[is_pure_def1] >> qpat_x_assum `isEmpty _ ` mp_tac >>
    simp[Once find_loc_def] >>
    strip_tac >>
    fs[inter_union_empty] >>
    Cases_on `r` >> fs[]
    >- (
      first_x_assum drule >>
      disch_then drule >>
      strip_tac >>
      fs[] >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[] >>
      impl_tac >> fs[] >>
      imp_res_tac evaluate_sing >>
      fs[miscTheory.opt_bind_def] >>
      every_case_tac >> simp []
      )
    >- (
      rveq >> fs[] >>
      first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
      fs[]
      )
    )
  >- ( (* Letrec *)
    rpt gen_tac >> strip_tac >> qpat_assum `flat_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac >>
    fs[evaluate_def] >> Cases_on `ALL_DISTINCT (MAP FST funs)` >> fs[] >>
    first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
    fs[] >>
    strip_tac >> fs[is_pure_def1, has_Eval_def] >> rfs[] >>
    qpat_x_assum `isEmpty _` mp_tac >> simp[Once find_loc_def] >>
    strip_tac >>
    first_x_assum irule >>
    `isEmpty (inter (find_locL (MAP (SND o SND) funs)) reachable) ∧
        isEmpty (inter (find_loc e) reachable)` by
            metis_tac[inter_union_empty] >>
    fs[find_env_globals_def, build_rec_env_def] >>
    fs[FOLDR_CONS_triple, EVERY_MAP, o_DEF] >>
    fs[ELIM_UNCURRY, v_has_Eval_def, EVERY_MAP, o_DEF]
    )
QED

(******** EVALUATE SPECIALISATION ********)

Theorem evaluate_sing_notKeep_flat_state_rel:
  ∀ env state exprL new_state result expr
      reachable removed_state .
      flatSem$evaluate (env with v := []) state exprL = (new_state, result) ∧
      exprL = [expr] ∧
      ~ has_Eval expr ∧
      ¬keep reachable (Dlet expr) ∧
      flat_state_rel reachable state removed_state ∧
      result ≠ Rerr (Rabort Rtype_error)
  ⇒ flat_state_rel reachable new_state removed_state ∧
      ∃ value : flatSem$v . result = Rval [value]
Proof
  rpt gen_tac >> strip_tac >> fs[keep_def] >> rveq >>
  drule evaluate_flat_state_rel_lemma >> fs[] >>
  disch_then drule >> disch_then drule >> fs[] >>
  rw[] >> imp_res_tac evaluate_sing >> fs[] >> fs[find_v_globals_def]
QED



(******************************* MAIN PROOFS ******************************)

Theorem keep_Dlet:
     ∀ (reachable:num_set) h . ¬ keep reachable h ⇒ ∃ x . h = Dlet x
Proof
   Cases_on `h` >> rw[keep_def]
QED

Theorem flat_decs_removal_lemma:
     ∀ ^state decs new_state result
        reachable removed_decs removed_state .
        evaluate_decs state decs = (new_state, result) ∧
        result ≠ SOME (Rabort Rtype_error) ∧
        remove_unreachable reachable decs = removed_decs ∧
        flat_state_rel reachable state removed_state ∧
        EVERY ($~ ∘ has_Eval_dec) decs ∧
        decs_closed reachable decs
    ⇒ ∃ new_removed_state .
        new_removed_state.ffi = new_state.ffi /\
        evaluate_decs removed_state removed_decs =
            (new_removed_state, result)
Proof
    Induct_on `decs`
    >- (rw[evaluate_def, remove_unreachable_def] >>
        fs[evaluate_def, find_result_globals_def, flat_state_rel_def])
    >>  fs[evaluate_def, remove_unreachable_def] >> rw[] >>
        qpat_assum `flat_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once flat_state_rel_def] >> strip_tac
        >- (
          fs[evaluate_def] >>
          fs [pair_case_eq] >>
          rveq >> fs [] >>
          rename [`evaluate_dec _ _ = (_, r1)`] >>
          `r1 ≠ SOME (Rabort Rtype_error)` by (CCONTR_TAC >> fs[]) >>
          drule evaluate_dec_flat_state_rel >> rpt (disch_then drule) >>
          rw[] >> fs[] >>
          pop_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
          fs[] >>
          `decs_closed reachable [h]` by imp_res_tac decs_closed_reduce_HD >>
          fs[] >>
          reverse(Cases_on `r1` >> fs[] >> rw[] >> rveq >> EVERY_CASE_TAC)
          >- fs[flat_state_rel_def] >>
          fs[] >> first_x_assum drule >> fs[] >> rveq >> strip_tac >>
          pop_assum (qspecl_then [`reachable`, `new_removed_state`] mp_tac) >>
          fs[] >>
          reverse(impl_tac) >- rw[] >> fs[find_env_globals_def] >>
          imp_res_tac decs_closed_reduce >> fs[]
          )
        >>  reverse(EVERY_CASE_TAC) >> fs[] >> rveq >>
            imp_res_tac keep_Dlet >> rveq >>
            fs[Once evaluate_def] >> EVERY_CASE_TAC >> fs[] >>
            rveq >> rw[UNION_EMPTY]
            >- (
                drule evaluate_sing_notKeep_flat_state_rel >> fs[] >>
                strip_tac >>
                rfs [has_Eval_dec_def] >>
                metis_tac [])
            >>  first_x_assum match_mp_tac >>
                fs[] >> asm_exists_tac >> fs[] >>
                imp_res_tac decs_closed_reduce >> fs[] >>
                drule evaluate_sing_notKeep_flat_state_rel >> fs[] >>
                fs [has_Eval_dec_def]
QED

Theorem flat_removal_thm:
  ∀ ffi k decs new_state result roots tree
      reachable removed_decs .
      evaluate_decs (initial_state ffi k ec) decs = (new_state, result) ∧
      result ≠ SOME (Rabort Rtype_error) ∧
      (roots, tree) = analyse_code decs ∧
      reachable = closure_spt roots tree ∧
      ~ EXISTS has_Eval_dec decs ∧
      remove_unreachable reachable decs = removed_decs
  ⇒ ∃ s .
      s.ffi = new_state.ffi /\
      evaluate_decs (initial_state ffi k ec) removed_decs = (s, result)
Proof
  rpt strip_tac >> drule flat_decs_removal_lemma >>
  rpt (disch_then drule) >> strip_tac >>
  pop_assum (qspec_then `initial_state ffi k ec` mp_tac) >>
  impl_tac >> gvs[] >>
  qspecl_then [`tree`,`roots`] mp_tac closure_spt_thm >> strip_tac >>
  rw[initial_state_def]
  >- (
    fs[flat_state_rel_def, globals_rel_def] >>
    fs[find_refs_globals_def]
    )
  >- (
    fs[decs_closed_def] >> rw[] >> gvs[]
    >- (rw[SUBSET_DEF] >> qexists_tac `x` >> fs[is_reachable_def])
    >- (
      qexists_tac `n'` >> fs[is_reachable_def] >>
      metis_tac[transitive_RTC, transitive_def]
      )
    )
QED

Theorem flat_remove_eval_sim:
   eval_sim ffi ds1 (remove_flat_prog ds1) ec ec
                    (\d1 d2. d2 = remove_flat_prog d1) F
Proof
  rw [eval_sim_def] \\ qexists_tac `0` \\ fs [remove_flat_prog_def]
  \\ pairarg_tac \\ fs []
  \\ drule flat_removal_thm \\ rw [] \\ fs []
  \\ rfs []
QED

Theorem flat_remove_semantics =
  MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] IMP_semantics_eq)
           flat_remove_eval_sim |> SIMP_RULE (srw_ss()) []

(* syntactic results *)

Theorem elist_globals_filter[local]:
  elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds))) = {||}
Proof
  Induct_on `ds` \\ rw [] \\ fs [SUB_BAG_UNION]
QED

Theorem esgc_free_filter[local]:
  EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds)))
Proof
  Induct_on `ds` \\ rw []
QED

Theorem elist_globals_filter_SUB_BAG[local]:
  elist_globals (MAP dest_Dlet (FILTER is_Dlet (FILTER P ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))
Proof
  Induct_on `ds` \\ rw [] \\ fs [SUB_BAG_UNION]
QED

Theorem remove_flat_prog_elist_globals_eq_empty:
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
   ==>
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))) = {||}
Proof
  simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ metis_tac [elist_globals_filter]
QED

Theorem remove_flat_prog_esgc_free:
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
   ==>
   EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds)))
Proof
  simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ metis_tac [esgc_free_filter]
QED

Theorem remove_flat_prog_sub_bag:
   elist_globals (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))) <=
   elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))
Proof
  simp [remove_flat_prog_def, remove_unreachable_def, UNCURRY]
  \\ rw []
  \\ metis_tac [elist_globals_filter_SUB_BAG]
QED

Theorem remove_flat_prog_distinct_globals:
   BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)))
   ==>
   BAG_ALL_DISTINCT (elist_globals
     (MAP dest_Dlet (FILTER is_Dlet (remove_flat_prog ds))))
Proof
  metis_tac [remove_flat_prog_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]
QED
