(*
  Prove completeness of the type inferencer for the expression-level.
*)
Theory infer_eComplete
Ancestors
  typeSystem ast semanticPrimitives infer unify infer_t
  typeSysProps inferProps namespace namespaceProps envRel
Libs
  preamble

(*Useful lemmas about pure add constraints, some of these imply the others*)
Theorem pure_add_constraints_success:
 !s constraints s'.
t_wfs s ∧
pure_add_constraints s constraints s'
⇒
s SUBMAP s' ∧
FDOM s ⊆ FDOM s' ∧
t_compat s s' ∧
t_wfs s'
Proof
  ho_match_mp_tac pure_add_constraints_ind>>
  fs[pure_add_constraints_def,t_compat_refl]>>
  ntac 7 strip_tac>>
  imp_res_tac t_unify_unifier>>
  res_tac>>fs[]>>CONJ_ASM1_TAC>>
  metis_tac[SUBMAP_DEF,SUBSET_DEF,SUBMAP_t_compat,SUBMAP_TRANS]
QED

(*t_compat is preserved over certain types of pure_add_constraints*)
Theorem t_compat_pure_add_constraints_1:
 !ls s sx.
  t_compat s sx ∧ EVERY (\x,y. t_walkstar sx x = t_walkstar sx y) ls
  ⇒
  ?si. pure_add_constraints s ls si ∧ t_compat si sx
Proof
  Induct>>fs[pure_add_constraints_def]>>rw[]>>
  Cases_on`h`>>fs[]>>
  simp[pure_add_constraints_def]>>
  imp_res_tac t_compat_eqs_t_unify>>
  fs[]
QED

(*If pure add constraints succeeds then the constraints all unify*)
Theorem t_compat_pure_add_constraints_2:
 !ls s sx.
  t_wfs s ∧
  pure_add_constraints s ls sx
  ⇒
  EVERY (\x,y. t_walkstar sx x = t_walkstar sx y) ls
Proof
  Induct>>rw[]>>
  Cases_on`h`>>fs[pure_add_constraints_def]
  >-
    (imp_res_tac t_unify_unifier>>
    imp_res_tac pure_add_constraints_success>>
    fs[t_compat_def]>>
    first_x_assum(qspec_then `r` assume_tac)>>rfs[]>>
    `t_walkstar sx (t_walkstar s2 r) = t_walkstar sx q` by
      metis_tac[t_walkstar_SUBMAP]>>
    fs[])
  >>
    metis_tac[t_unify_wfs]
QED

(*behaves like a function if the first 2 arguments are equal*)
Theorem pure_add_constraints_functional:
  !constraints s s' s''.
   t_wfs s ∧
   pure_add_constraints s constraints s' ∧
   pure_add_constraints s constraints s'' ⇒ s' = s''
Proof
   Induct>>
   rw[]>>
   fs[pure_add_constraints_def]>>
   Cases_on`h`>>
   fs[pure_add_constraints_def]>>
   fs[t_unify_eqn]>>
   imp_res_tac t_unify_wfs>>
   metis_tac[]
QED

(*1 direction is sufficient to imply the other*)
Theorem pure_add_constraints_swap_lemma[local]:
  t_wfs s ∧
  pure_add_constraints s (a++b) sx
  ⇒
  ?si. pure_add_constraints s (b++a) si ∧
       t_compat si sx
Proof
  rw[]>>
  imp_res_tac t_compat_pure_add_constraints_2>>
  fs[pure_add_constraints_append]>>
  imp_res_tac t_compat_pure_add_constraints_2>>
  imp_res_tac pure_add_constraints_success>>fs[]>>
  `t_compat s sx` by metis_tac[t_compat_trans]>>
  fs[PULL_EXISTS,Once SWAP_EXISTS_THM]>>
  Q.SPECL_THEN [`b`,`s`,`sx`] assume_tac t_compat_pure_add_constraints_1>>
  rfs[]>>
  HINT_EXISTS_TAC>>
  Q.SPECL_THEN [`a`,`si`,`sx`] assume_tac t_compat_pure_add_constraints_1>>
  rfs[]>>
  HINT_EXISTS_TAC>>fs[]
QED

Theorem pure_add_constraints_swap:
 t_wfs s ∧
  pure_add_constraints s (a++b) sx
  ⇒
  ?si. pure_add_constraints s (b++a) si ∧
       t_compat si sx ∧
       t_compat sx si
Proof
  rw[]>>
  assume_tac pure_add_constraints_swap_lemma>>rfs[]>>
  HINT_EXISTS_TAC>>fs[]>>
  imp_res_tac pure_add_constraints_swap_lemma>>
  imp_res_tac pure_add_constraints_functional>>
  fs[t_compat_trans]
QED

val pure_add_constraints_swap = GEN_ALL pure_add_constraints_swap;

(*End pure_add_constraints stuff*)

Theorem extend_t_vR_WF[local]:
   (check_t lim {} (n) ∧
   WF (t_vR s) )⇒
   WF (t_vR (s |+ (uvar,n)))
Proof
  fs[WF_DEF]>>rw[]>>
  first_x_assum(qspec_then `B` assume_tac)>>fs[]>>
  Cases_on `?w. B w`>> fs[]>>
  Q.EXISTS_TAC `min` >>
  fs[t_vR_eqn,FLOOKUP_UPDATE]>>
  IF_CASES_TAC>>rw[]>>
  imp_res_tac check_t_t_vars>>
  fs[FLOOKUP_DEF]
QED

Theorem not_t_oc[local]:
  (!t s v lim. t_wfs s ∧ check_t lim {} t ⇒ ¬ t_oc s t v) ∧
  (!ts s t v lim. t_wfs s ∧ EVERY (check_t lim {}) ts ⇒ ~ EXISTS (\t. t_oc s t v) ts)
Proof
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def]>>
  TRY (res_tac>>metis_tac[])>>
  SPOSE_NOT_THEN assume_tac>>
  Q.ISPEC_THEN `s` assume_tac t_oc_eqn>>
  rfs[]>> res_tac>>
  fs[t_walk_eqn]>>
  fs[EVERY_MEM,EXISTS_MEM]>>
  res_tac
QED

Theorem FDOM_extend[local]:
  FDOM s = count next_uvar ⇒
   FDOM (s |+ (next_uvar, n)) = count (SUC next_uvar)
Proof
  fs[FDOM_FUPDATE,count_def,INSERT_DEF,SET_EQ_SUBSET,SUBSET_DEF]>>
   rw[]>- DECIDE_TAC>-
   (res_tac>>DECIDE_TAC)>>
   Cases_on`x=next_uvar`>>fs[]>>
   `x<next_uvar` by DECIDE_TAC>>fs[]
QED

Theorem pure_add_constraints_exists:
 !s ts next_uvar lim.
  t_wfs s ∧
  FDOM s = count next_uvar ∧
  EVERY (check_freevars lim []) ts
  ⇒
  let tys = MAP ( λn. (next_uvar+n)) (COUNT_LIST (LENGTH ts)) in
  let targs = MAP unconvert_t ts in
  let constraints = ZIP ((MAP Infer_Tuvar tys),targs) in
  let extension = ZIP (tys,targs) in
  pure_add_constraints s constraints (s|++extension)
Proof
  induct_on`ts`>>
  srw_tac[][] >>unabbrev_all_tac>>
  srw_tac[] [COUNT_LIST_def, pure_add_constraints_def]>-rw[FUPDATE_LIST]>>
  fsrw_tac[][LET_THM,MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = (SUC x) + y``] >>
  fsrw_tac[][t_unify_eqn]>>
  fsrw_tac[][t_walk_eqn,Once t_vwalk_eqn] >>
  `FLOOKUP s next_uvar = NONE ` by
    (fs[FLOOKUP_DEF,count_def,SUBSET_DEF]>>
    first_x_assum (qspec_then `next_uvar` mp_tac)>>DECIDE_TAC)>>
  fsrw_tac[][t_ext_s_check_eqn]>>
  imp_res_tac check_freevars_to_check_t>>
  Cases_on`unconvert_t h`>>
  fsrw_tac[][t_walk_eqn]>>
  imp_res_tac not_t_oc
  >-
    (`t_wfs (s |+ (next_uvar,Infer_Tvar_db n))` by
      metis_tac[t_wfs_eqn,extend_t_vR_WF]>>
      imp_res_tac FDOM_extend>>
      simp[]>>
      pop_assum (qspec_then `Infer_Tvar_db n` assume_tac)>>
      res_tac>>
      fsrw_tac[][FUPDATE_LIST_THM,DECIDE ``SUC x + n = n + SUC x``])
  >-
    (`t_wfs (s |+ (next_uvar,Infer_Tapp l n))` by metis_tac[t_wfs_eqn,extend_t_vR_WF]>>
    imp_res_tac FDOM_extend>>simp[]>>
    pop_assum(qspec_then `Infer_Tapp l n` assume_tac)>>
    res_tac>>
    fs[FUPDATE_LIST_THM])
  >-
    fs[check_t_def]
QED

(*Can't find a version of this in the right direction*)
Theorem check_t_t_walkstar[local]:
   t_wfs s ⇒
  !tvs (uvars:num ->bool) t. check_t tvs {} (t_walkstar s t) ⇒ check_t tvs (FDOM s) t
Proof
  strip_tac>>ho_match_mp_tac check_t_ind>>
  rw[]
  >-
    (Cases_on`tvs' ∈ FDOM s`>>fs[check_t_def]>>
    qpat_x_assum `check_t A B C` mp_tac>>
    fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
    `FLOOKUP s tvs' = NONE` by fs[flookup_thm]>>simp[check_t_def])
  >-
    (pop_assum mp_tac>>
    fs[check_t_def,t_walkstar_eqn,t_walk_eqn])
  >>
    pop_assum mp_tac>>
    fs[check_t_def,t_walkstar_eqn,t_walk_eqn]>>
    fs[EVERY_MEM]>>rw[]>>
    res_tac>>
    metis_tac[MEM_MAP]
QED

(*Ignore increment on deBrujin vars*)
Theorem t_walkstar_ignore_inc[local]:
  t_wfs s ⇒
(!t.(!uv. uv ∈ FDOM s ⇒ check_t 0 {} (t_walkstar s (Infer_Tuvar uv)))
⇒
t_walkstar (infer_deBruijn_inc tvs o_f s) t = t_walkstar s t) ∧
(!ts. (!t.(!uv. uv ∈ FDOM s ⇒ check_t 0 {} (t_walkstar s (Infer_Tuvar uv)))
⇒
EVERY (\t. t_walkstar (infer_deBruijn_inc tvs o_f s) t = t_walkstar s t) ts))
Proof
  strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[]>>
  imp_res_tac inc_wfs>>
  fs[t_walkstar_eqn1]
  >-
    fs[MAP_EQ_f,EVERY_MEM]
  >>
  assume_tac walkstar_inc>>
  pop_assum(qspecl_then [`tvs`,`s`,`Infer_Tuvar n`] assume_tac)>>rfs[]>>
  fs[infer_deBruijn_inc_def]>>
  Cases_on`n ∈ FDOM s`
  >-
  (res_tac>>
  match_mp_tac check_t_deBruijn_inc>>
  fs[check_t_more])
  >>
  fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
  simp[EQ_SYM_EQ,Once t_vwalk_eqn]>>
  `FLOOKUP s n = NONE` by fs[flookup_thm]>>
  fs[infer_deBruijn_inc_def]
QED

(*Adding a list of keys that did not already exist is safe*)
Theorem SUBMAP_FUPDATE_LIST_NON_EXIST[local]:
  set (MAP FST ls) ∩ (FDOM s) = {}
  ⇒
  s SUBMAP (s|++ls)
Proof
  Induct_on`ls`>>fs[FUPDATE_LIST_THM]>>
  rw[]>>
  Cases_on`h`>>
  fs[INSERT_INTER]>>
  `q ∉ FDOM s` by
    (SPOSE_NOT_THEN assume_tac>>fs[])>>
  fs[]>>
  `s|++ls SUBMAP s|+(q,r)|++ls` by
    (Cases_on`MEM q (MAP FST ls)`
    >-
      fs[FUPDATE_FUPDATE_LIST_MEM]
    >>
      fs[FUPDATE_FUPDATE_LIST_COMMUTES]>>DISJ1_TAC>>
      fs[FDOM_FUPDATE_LIST])>>
  metis_tac[SUBMAP_TRANS]
QED

Theorem t_vwalk_o_f_id[local]:
  t_wfs s ⇒
  !t. t_vwalk (infer_deBruijn_inc 0 o_f s) t = t_vwalk s t
Proof
  strip_tac>>
  ho_match_mp_tac (Q.INST[`s`|->`s`]t_vwalk_ind)>>
  rw[]>>
  fs[Once t_vwalk_eqn]>>
  imp_res_tac inc_wfs>>
  simp[Once t_vwalk_eqn]>>
  fs[FLOOKUP_o_f]>>
  every_case_tac>>
  fs[FLOOKUP_o_f,infer_deBruijn_inc0]>>
  metis_tac[]
QED

Theorem t_walkstar_o_f_id[local]:
  t_wfs s ⇒
  !t. t_walkstar ((infer_deBruijn_inc 0) o_f s) t  = t_walkstar s t
Proof
  rw[]>>
  imp_res_tac t_walkstar_ind>>
  Q.SPEC_TAC (`t`, `t`) >>
  pop_assum ho_match_mp_tac >>
  Cases>>
  rw[]>>
  imp_res_tac inc_wfs>>
  fs[t_walkstar_eqn,t_walk_eqn]>>
  imp_res_tac t_vwalk_o_f_id>>fs[]
  >>
  every_case_tac>>
  fs[MAP_EQ_f]>>rw[]>>res_tac>>
  fs[t_walkstar_eqn]
QED

Theorem deBruijn_subst_id[local]:
  (!t. deBruijn_subst 0 [] t = t) ∧
  (!ts. MAP (deBruijn_subst 0 []) ts = ts)
Proof
  Induct>>rw[]>>fs[deBruijn_subst_def,MAP_EQ_ID]
QED

Theorem tscheme_approx_weakening2[local]:
  tscheme_approx tvs s t1 t2 ∧ t_compat s s' ∧ FDOM s ⊆ FDOM s' ⇒
  tscheme_approx tvs s' t1 t2
Proof
  Cases_on`t1`>>Cases_on`t2`>>rw[tscheme_approx_def]>>
  qexists_tac`subst'`>>fs[]>>
  rw[]
  >-
    (fs[EVERY_MEM]>>rw[]>>
    metis_tac[check_t_more5])
  >>
  first_x_assum(qspec_then`subst` assume_tac)>>rfs[]>>
  fs[t_compat_def]>>metis_tac[]
QED

Theorem env_rel_complete_t_compat[local]:
  t_compat s s' ∧
  FDOM s ⊆ FDOM s' ∧
  t_wfs s' ∧
  env_rel_complete s ienv tenv tenvE ⇒
  env_rel_complete s' ienv tenv tenvE
Proof
  rw[env_rel_complete_def]
  >-
    metis_tac[]
  >>
  res_tac>>
  metis_tac[tscheme_approx_weakening2]
QED

Theorem NOT_SOME_NONE[local]:
  (!x. A ≠ SOME x) ⇒ A = NONE
Proof
  metis_tac[optionTheory.option_nchotomy]
QED

Theorem t_walk_submap_walkstar[local]:
  !s s'. s SUBMAP s' ∧ t_wfs s ∧ t_wfs s'
⇒
(!h. t_walk s (t_walkstar s' h) = t_walkstar s' h) ∧
(!hs. MAP ((t_walk s) o t_walkstar s') hs = MAP (t_walkstar s') hs)
Proof
  ntac 3 strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>rw[]>>
  fs[t_walkstar_eqn,t_walk_eqn,MAP_MAP_o]>>
  Cases_on`t_vwalk s' n`>>fs[t_walk_eqn]>>
  imp_res_tac t_vwalk_to_var>>
  fs[Once t_vwalk_eqn]>>
  `n' ∉ FDOM s` by
    metis_tac[SUBMAP_DEF]>>
  imp_res_tac flookup_thm>>
  fs[]
QED

Theorem t_unify_to_pure_add_constraints[local]:
  !s s' h t constraints s''.
pure_add_constraints s (constraints ++ [h,t]) s'' ⇒
(?s'. pure_add_constraints s constraints s' ∧
t_unify s' h t = SOME s'')
Proof
  rw[pure_add_constraints_append]>>
  Q.EXISTS_TAC`s2`>>fs[]>>
  fs[pure_add_constraints_def]
QED

Theorem add_constraint_success2[local]:
  !l t1 t2 st st' x.
  add_constraint l t1 t2 st = (Success x, st') ⇔
  x = () ∧
  pure_add_constraints st.subst [t1,t2] st'.subst ∧
  st'.next_uvar = st.next_uvar ∧
  st'.next_id = st.next_id
Proof
  rw[add_constraint_success,pure_add_constraints_def,EQ_IMP_THM]>>
  rw[infer_st_rewrs,infer_st_component_equality]
QED

Theorem pure_add_constraints_combine[local]:
  (?st'. (pure_add_constraints st.subst ls st'.subst ∧ st'.next_uvar = x1 ∧ st'.next_id = x2) ∧
(pure_add_constraints st'.subst ls' st''.subst ∧ y1 = st'.next_uvar ∧ y2 = st'.next_id))
⇔
pure_add_constraints st.subst (ls++ls') st''.subst ∧ y1 = x1 ∧ y2 = x2
Proof
  fs[pure_add_constraints_def,EQ_IMP_THM]>>rw[]
>-
  metis_tac[pure_add_constraints_append]
>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<| subst:= s2 ; next_uvar := x1 ; next_id:=x2|>`>>fs[]
QED

Theorem t_unify_ignore[local]:
  (!s t t'.
  t_wfs s ⇒
  t_walkstar s t = t_walkstar s t' ⇒
  t_unify s t t' = SOME s) ∧
  (!s ts ts'.
  t_wfs s ⇒
  MAP (t_walkstar s) ts = MAP (t_walkstar s) ts' ⇒
  ts_unify s ts ts' = SOME s)
Proof
  ho_match_mp_tac t_unify_strongind>>rw[]>>
  fs[t_unify_eqn]>-
  (full_case_tac>>
  imp_res_tac t_walk_submap_walkstar>>fs[]>>
  qpat_x_assum `t_walkstar s t = X` mp_tac>>
  fs[t_walkstar_eqn]>>every_case_tac>>fs[]>>
  metis_tac[])>>
  Cases_on`ts`>>Cases_on`ts'`>>
  fs[ts_unify_def]
QED

Theorem pure_add_constraints_ignore:
 !s ls. t_wfs s ∧ EVERY (λx,y. t_walkstar s x = t_walkstar s y) ls
  ⇒ pure_add_constraints s ls s
Proof
  strip_tac>>Induct>>
  fs[pure_add_constraints_def]>>
  rw[]>>
  Cases_on`h` >>rw[pure_add_constraints_def]>>
  fs[]>>imp_res_tac t_unify_ignore>>
  metis_tac[]
QED

(*t_compat preserves all grounded (no unification variable after walk) terms*)
Theorem t_compat_ground[local]:
  t_compat a b
  ⇒
  ∀uv. uv ∈ FDOM a ∧
       check_t tvs {} (t_walkstar a (Infer_Tuvar uv))
       ⇒ uv ∈ FDOM b ∧
         check_t tvs {} (t_walkstar b (Infer_Tuvar uv))
Proof
  rw[t_compat_def]>>
  first_x_assum (qspec_then `Infer_Tuvar uv` assume_tac)>>
  imp_res_tac t_walkstar_no_vars>>
  fs[check_t_def]>>
  metis_tac[t_walkstar_tuvar_props]
QED

Theorem t_walkstar_tuvar_props2[local]:
  t_wfs s ∧ t_walkstar s x = Infer_Tuvar uv
  ⇒
  ?k. x = Infer_Tuvar k ∧
      (k = uv ⇒ k ∉ FDOM s) ∧
      (k ≠ uv ⇒ k ∈ FDOM s)
Proof
  rw[]>>
  Cases_on`x`>>
  TRY
  (pop_assum mp_tac>>
  simp[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>NO_TAC)>>
  Q.EXISTS_TAC `n`>>fs[]>>
  Cases_on`n=uv`>-
  fs[t_walkstar_tuvar_props]>>
  SPOSE_NOT_THEN assume_tac>>
  imp_res_tac t_walkstar_tuvar_props>>
  fs[]
QED

(*Remove every uvar in the FDOM if we walkstar using a completed map*)
Theorem check_t_less:
   (!t.
  t_wfs s ∧
  (!uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  check_t 0 uvars t
  ⇒
  check_t n (uvars ∩ (COMPL (FDOM s))) (t_walkstar s t)) ∧
  (!ts.
  t_wfs s ∧
  (!uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  EVERY (check_t 0 uvars) ts
  ⇒
  EVERY (check_t n (uvars ∩ (COMPL (FDOM s)))) (MAP (t_walkstar s) ts))
Proof
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[]
  >- fs[t_walkstar_eqn,t_walk_eqn,check_t_def]
  >-
    fs[t_walkstar_eqn,t_walk_eqn,check_t_def,EVERY_MEM,MEM_MAP]
  >>
  Cases_on`n' ∈ FDOM s`
  >-
    (res_tac>>fs[check_t_more])
  >>
    imp_res_tac t_walkstar_tuvar_props>>
    fs[check_t_def]
QED

(*Double sided t_compat thm*)
Theorem t_compat_bi_ground:
 (!uv. uv ∈ FDOM a ⇒ check_t n {} (t_walkstar a (Infer_Tuvar uv))) ∧
  t_compat a b ∧
  t_compat b a
  ⇒
  (!uv. uv ∈ FDOM b ⇒ check_t n {} (t_walkstar b (Infer_Tuvar uv))) ∧
  FDOM a = FDOM b ∧
  ((!t. t_walkstar a t= t_walkstar b t) ∧
  (!ts. MAP (t_walkstar a) ts = MAP (t_walkstar b) ts))
Proof
  strip_tac>>
  CONJ_ASM1_TAC
  >-
  (fs[t_compat_def]>>
    rw[]>>
    Cases_on`uv ∈ FDOM a`
    >-
      (res_tac>>
      last_x_assum(qspec_then `Infer_Tuvar uv` assume_tac)>>
      metis_tac[t_walkstar_no_vars])
    >>
      first_x_assum(qspec_then `Infer_Tuvar uv` assume_tac)>>
      imp_res_tac t_walkstar_tuvar_props>>
      fs[]>>
      imp_res_tac t_walkstar_tuvar_props2>>
      Cases_on`k''''=uv` >>fs[]>>
      res_tac>>
      `t_walkstar a (Infer_Tuvar k'''') = Infer_Tuvar k` by fs[]>>
      fs[check_t_def])
  >>
  CONJ_ASM1_TAC
  >-
    (fs[EXTENSION]>>
    rw[EQ_IMP_THM]>>
    imp_res_tac t_compat_ground>>
    res_tac>> metis_tac[])
  >>
    ho_match_mp_tac infer_tTheory.infer_t_induction>>rw[]>>
    fs[t_compat_def]>>
    TRY(fs[t_walkstar_eqn,t_walk_eqn]>>NO_TAC)>>
    Cases_on`n' ∈ FDOM a`
    >-
      metis_tac[t_walkstar_no_vars]
    >>
      metis_tac[t_walkstar_tuvar_props]
QED

(*Free properties when extending the completed map with uvar->ground var*)
Theorem extend_one_props[local]:
  t_wfs st.subst ∧
  t_wfs s ∧
  pure_add_constraints st.subst constraints s ∧
  (∀uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  check_freevars n [] t ∧
  FDOM s = count st.next_uvar ⇒
  let s' = s|++[(st.next_uvar,unconvert_t t)] in
  t_wfs s' ∧
  pure_add_constraints s [Infer_Tuvar st.next_uvar,unconvert_t t] s' ∧
  s SUBMAP s' ∧
  st.subst SUBMAP s' ∧
  pure_add_constraints st.subst
    (constraints ++ [(Infer_Tuvar st.next_uvar,unconvert_t t)]) s' ∧
  FDOM s' = count (st.next_uvar +1) ∧
  t_walkstar s' (Infer_Tuvar st.next_uvar) = unconvert_t t ∧
  ∀uv. uv ∈ FDOM s' ⇒ check_t n {} (t_walkstar s' (Infer_Tuvar uv))
Proof
  strip_tac>>
  fs[LET_THM]>>
  imp_res_tac check_freevars_to_check_t>>
  Q.ABBREV_TAC `constraints' = constraints++[Infer_Tuvar st.next_uvar,unconvert_t t]`>>
  Q.SPECL_THEN [`s`,`[t]`,`st.next_uvar`,`n`] mp_tac pure_add_constraints_exists>>
  impl_tac >-
     (fs[check_t_def]>>
     imp_res_tac check_t_to_check_freevars>>
     rfs[check_freevars_def])>>
  fs[LET_THM,EVAL``COUNT_LIST 1``]>>
  qpat_abbrev_tac `s' = s|++ A`>>strip_tac>>
  CONJ_ASM1_TAC>-
    metis_tac[pure_add_constraints_wfs]>>
  CONJ_ASM1_TAC>-
    metis_tac[pure_add_constraints_success]>>
  CONJ_ASM1_TAC>-
    metis_tac[SUBMAP_TRANS,pure_add_constraints_success]>>
  CONJ_ASM1_TAC>-
    metis_tac[Abbr`constraints'`,pure_add_constraints_append]>>
  CONJ_ASM1_TAC>-
  (fs[Abbr`s'`,FDOM_FUPDATE_LIST,count_def,EXTENSION]>>
     rw[]>>DECIDE_TAC)>>
  CONJ_ASM1_TAC >-
  (fs[t_walkstar_eqn,Abbr`s'`,t_walk_eqn,Once t_vwalk_eqn]>>
     fs[flookup_fupdate_list]>>
     Cases_on`unconvert_t t`
     >- fs[check_t_def]
     >-
       (fs[MAP_EQ_ID,check_t_def,EVERY_MEM]>>rw[]>>
       res_tac>>metis_tac[t_walkstar_no_vars])
    >- fs[check_t_def])>>
  rw[]>>Cases_on`uv = st.next_uvar`
     >-
       fs[check_t_def]
     >>
       `uv <st.next_uvar` by DECIDE_TAC>>
       imp_res_tac t_walkstar_SUBMAP>>
       metis_tac[pure_add_constraints_success,t_walkstar_no_vars]
QED

(*This occurs when looking up a list updated fmap*)
val ALOOKUP_lemma = GEN_ALL (prove(
``
  n<LENGTH ls ⇒
  ALOOKUP (REVERSE (ZIP ((MAP (\n. offset + n) (COUNT_LIST (LENGTH ls))),ls))) (offset+n)
  = SOME (EL n ls)``,
  rw[]>>
  qmatch_abbrev_tac `ALOOKUP (REVERSE L) k = SOME Y`>>
  Q.ISPECL_THEN [`L`,`k`] mp_tac alookup_distinct_reverse>>
  impl_keep_tac>-
    (rw[Abbr`L`,MAP_ZIP,LENGTH_COUNT_LIST]>>
    match_mp_tac ALL_DISTINCT_MAP_INJ>>
    fs[all_distinct_count_list])>>
  rw[]>>
  unabbrev_all_tac>>
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>fs[]>>
  fs[MEM_ZIP,LENGTH_COUNT_LIST]>>HINT_EXISTS_TAC>>
  fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]));

Theorem submap_t_walkstar_replace[local]:
  t_wfs s' ∧
  s SUBMAP s' ∧
  check_t n {} (t_walkstar s h)
  ⇒
  t_walkstar s h = t_walkstar s' h
Proof
  rw[]>>
  imp_res_tac t_walkstar_SUBMAP>>
  metis_tac[t_walkstar_no_vars]
QED

Theorem extend_multi_props:
 !st constraints s ts n.
  t_wfs st.subst ∧
  t_wfs s ∧
  pure_add_constraints st.subst constraints s ∧
  (∀uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  EVERY (check_freevars n []) ts ∧
  FDOM s = count st.next_uvar ⇒
  let tys = MAP ( λn. (st.next_uvar+n)) (COUNT_LIST (LENGTH ts)) in
  let targs = MAP unconvert_t ts in
  let new_constraints = ZIP ((MAP Infer_Tuvar tys),targs) in
  let extension = ZIP (tys,targs) in
  let s' = s|++extension in
  pure_add_constraints s new_constraints s' ∧
  pure_add_constraints st.subst (constraints++new_constraints) s' ∧
  t_wfs s' ∧
  s SUBMAP s' ∧
  st.subst SUBMAP s' ∧
  FDOM s' = count (st.next_uvar +LENGTH ts) ∧
  (∀n. n<LENGTH ts ⇒
  t_walkstar s' (Infer_Tuvar (st.next_uvar+n)) = EL n targs) ∧
  ∀uv. uv ∈ FDOM s' ⇒ check_t n {} (t_walkstar s' (Infer_Tuvar uv))
Proof
  rpt strip_tac>>
  fsrw_tac[][LET_THM]>>CONJ_ASM1_TAC>-
    (imp_res_tac pure_add_constraints_exists>>
    fs[LET_THM])>>
  CONJ_ASM1_TAC>-
    metis_tac[pure_add_constraints_append]>>
  CONJ_ASM1_TAC>-
    metis_tac[pure_add_constraints_success]>>
  CONJ_ASM1_TAC>-
    metis_tac[pure_add_constraints_success]>>
  CONJ_ASM1_TAC>-
    metis_tac[pure_add_constraints_success]>>
  CONJ_ASM1_TAC>-
    (fsrw_tac[][FDOM_FUPDATE_LIST,count_def,EXTENSION]>>srw_tac[][]>>
    qpat_abbrev_tac `ls1 = MAP (\n.st.next_uvar+n) A`>>
    qpat_abbrev_tac `ls2 = MAP unconvert_t ts`>>
    `LENGTH ls1 = LENGTH ls2` by metis_tac[LENGTH_MAP,LENGTH_COUNT_LIST]>>
    rw[EQ_IMP_THM]
    >-
      DECIDE_TAC
    >-
      (pop_assum mp_tac>>
      fs[MAP_ZIP,Abbr`ls1`]>>
      fs[MEM_MAP,MEM_COUNT_LIST]>>rw[]>>DECIDE_TAC)
    >>
      Cases_on`x < st.next_uvar` >>
      fs[MAP_ZIP,Abbr`ls1`]>>fs[MEM_MAP,MEM_COUNT_LIST]>>
      imp_res_tac arithmeticTheory.LESS_ADD >>
      Q.EXISTS_TAC`LENGTH ts -p`>>
      DECIDE_TAC)>>
  CONJ_ASM1_TAC>-
    (srw_tac[][]>>
    fsrw_tac[][t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
    qpat_abbrev_tac `s' = s|++A`>>
    `FLOOKUP s' (st.next_uvar+n') = SOME (EL n' (MAP unconvert_t ts))` by
      (fs[Abbr`s'`,flookup_update_list_some]>>
      DISJ1_TAC>>
      Q.ISPECL_THEN [`st.next_uvar`,`n'`,`MAP unconvert_t ts`] mp_tac ALOOKUP_lemma>>
      impl_keep_tac>- metis_tac[LENGTH_MAP]>>
      rw[])>>
    simp[]>>
    `check_t n {} (EL n' (MAP unconvert_t ts))` by
      metis_tac[check_freevars_to_check_t,EL_MAP,EVERY_MEM,MEM_EL]>>
    every_case_tac>>fsrw_tac[][check_t_def]>>
    fsrw_tac[][MAP_EQ_ID]>>srw_tac[][]>>metis_tac[EVERY_MEM,t_walkstar_no_vars])>>
  srw_tac[][]>>Cases_on`uv ∈ FDOM s`
      >-
        (rfs[]>>
        res_tac>>
        metis_tac[submap_t_walkstar_replace])
      >>
        rfs[]>>
        `uv - st.next_uvar < LENGTH ts` by DECIDE_TAC>>
        first_x_assum(qspec_then `uv-st.next_uvar` assume_tac)>>rfs[]>>
        `st.next_uvar + (uv - st.next_uvar) = uv` by DECIDE_TAC>>fs[]>>
        fs[EVERY_EL,EL_MAP]>>
        first_x_assum(qspec_then `uv-st.next_uvar` mp_tac)>>
        impl_tac>- DECIDE_TAC>>
        metis_tac[check_freevars_to_check_t]
QED

(*Useful tactics, mainly for constrain_op*)

val unconversion_tac =
  rpt (qpat_x_assum `convert_t A = B` (assume_tac o (Q.AP_TERM `unconvert_t`)))>>
  imp_res_tac check_t_empty_unconvert_convert_id>>
  fs[unconvert_t_def];

fun pure_add_constraints_combine_tac ls =
  case ls of [st,constraints,s]
  =>
    (`pure_add_constraints ^(st).subst (^(constraints) ++ ls) ^(s)` by
      (fs[pure_add_constraints_append]>>
      Q.EXISTS_TAC`^(s)`>>fs[])>>
      Q.SPECL_THEN [`^(s)`,`^(st).subst`,`ls`,`^(constraints)`] assume_tac
        pure_add_constraints_swap>>
      rfs[])
  | _ => ALL_TAC;

fun pure_add_constraints_rest_tac ls =
  case ls of [constraints,s]
  =>
  (Q.EXISTS_TAC`si`>>
  Q.EXISTS_TAC`^(constraints)`>>
  Q.SPECL_THEN [`n`,`si`,`^(s)`] assume_tac (GEN_ALL t_compat_bi_ground)>>
  rfs[]>>
  rw[]
  >-
    metis_tac[pure_add_constraints_success]
  >>
    TRY(`t_wfs si` by metis_tac[pure_add_constraints_wfs]>>
    fs[pure_add_constraints_wfs,convert_t_def,t_walkstar_eqn,t_walk_eqn]>>NO_TAC))
  | _ => ALL_TAC;

fun pure_add_constraints_ignore_tac s =
     byA(`pure_add_constraints ^(s) ls ^(s)`,
      (match_mp_tac pure_add_constraints_ignore >>
      fs[Abbr`ls`,t_walkstar_eqn,t_walk_eqn]))

(* copied from src/1/Tactical *)
fun parse_with_goal t (asms, g) =
   let
      val ctxt = free_varsl (g :: asms)
   in
      Parse.parse_in_context ctxt t
   end

val Q_TAC = fn tac => fn t => fn g => tac (parse_with_goal t g) g

(* Q_TAC except the argument is a list of terms *)
val list_Q_TAC = fn tac => fn ts => fn g => tac (map (fn t=> parse_with_goal t g) ts) g

val pure_add_constraints_ignore_tac = Q_TAC pure_add_constraints_ignore_tac
val pure_add_constraints_combine_tac = list_Q_TAC pure_add_constraints_combine_tac
val pure_add_constraints_rest_tac = list_Q_TAC pure_add_constraints_rest_tac

(*For grounded ones*)
val pac_tac =
  pure_add_constraints_ignore_tac `s`>>
  pure_add_constraints_combine_tac [`st`,`constraints`,`s`]>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st.next_uvar; next_id := st.next_id |>` >>fs[]>>
  pure_add_constraints_rest_tac [`constraints`,`s`];

fun flip_converts th =
  let
    val (l,r) = dest_eq (concl th)
  in
    if same_const (rator r) ``convert_t`` then
      CONV_RULE (REWR_CONV EQ_SYM_EQ) th
    else th
  end handle HOL_ERR _ => th

fun extend_uvar_tac t=
  `check_freevars n [] ^(t)` by
  (imp_res_tac check_t_to_check_freevars>>
  rfs[check_freevars_def])>>
  Q.SPECL_THEN [`^(t)`,`st`,`s`,`n`,`constraints`] mp_tac (GEN_ALL extend_one_props)>>
  impl_tac>- fs[]>>
  qpat_abbrev_tac `s' = s|++A`>>
  Q.ABBREV_TAC `constraints' = constraints++[Infer_Tuvar st.next_uvar,unconvert_t ^(t)]`>>
  rfs[LET_THM]>>
  imp_res_tac pure_add_constraints_success>>
  unconversion_tac>>
  rw[];

val replace_uvar_tac =
  rpt (qpat_x_assum `t_walkstar s A = B` (fn th =>
  (((Q.SUBGOAL_THEN `t_walkstar s' h = ^(th|>concl|>rhs)` assume_tac))>-
  (metis_tac[check_t_def,submap_t_walkstar_replace,th]))) )

val rest_uvar_tac =
  pure_add_constraints_ignore_tac `s'`>>
  pure_add_constraints_combine_tac [`st`,`constraints'`,`s'`]>>
  `t_compat s si` by metis_tac[t_compat_trans]>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st.next_uvar+1 ; next_id := st.next_id|>` >>fs[]>>
  pure_add_constraints_rest_tac [`constraints'`,`s'`]>>
  TRY(metis_tac[check_freevars_empty_convert_unconvert_id]);

val extend_uvar_tac = Q_TAC extend_uvar_tac;

fun TRY1 tac = TRY (tac >> NO_TAC)

Theorem constrain_op_complete_simple_helper[local]:
  !n.
    sub_completion n st.next_uvar st.subst constraints s ∧
    type_op op ts t ∧
    MAP (convert_t o (t_walkstar s)) ts' = ts ∧
    FST (op_simple_constraints op) ∧
    FDOM st.subst ⊆ count st.next_uvar ∧
    FDOM s = count st.next_uvar ∧
    t_wfs st.subst ∧
    EVERY (check_t n {}) (MAP (t_walkstar s) ts') ∧
    check_freevars n [] t
    ⇒
    ?st' xs t'.
    t = convert_t (t_walkstar s t') ∧
    pure_add_constraints s xs s ∧
    (!l st'.
      st'.next_uvar = st.next_uvar ∧
      st'.next_id = st.next_id ∧
      pure_add_constraints st.subst xs st'.subst ==>
      constrain_op l op ts' st = (Success t',st'))
Proof
  rw []
  \\ imp_res_tac sub_completion_wfs
  \\ `?is_case. is_case op` by (qexists_tac `\x. T` \\ simp [])
  \\ fs [op_simple_constraints_def, type_op_cases]
  \\ rfs [MAP_EQ_CONS]
  \\ rw []
  \\ RULE_ASSUM_TAC flip_converts
  \\ simp [constrain_op_def, op_simple_constraints_def]
  \\ simp [success_eqns]
  \\ qmatch_goalsub_abbrev_tac `_ ==> pure_add_constraints _ xs _ /\ t' = _`
  \\ qexists_tac `xs`
  \\ qexists_tac `t'`
  \\ fs [markerTheory.Abbrev_def, t_walkstar_eqn1, convert_t_def, word_tc_def]
  \\ rpt conj_tac
  \\ TRY $ irule pure_add_constraints_ignore
  \\ simp [t_walkstar_eqn1]
  \\ TRY (rename [‘t_num_of ty’] \\ Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases \\ gvs [])
  \\ unconversion_tac
  \\ gvs[LENGTH_EQ_NUM_compute, REPLICATE_compute,CaseEq"bool"]
  \\ unconversion_tac
  \\ gvs[t_walkstar_eqn1]
QED

Theorem constrain_op_complete[local]:
  !n.
type_op op ts t ∧
sub_completion n st.next_uvar st.subst constraints s ∧
FDOM st.subst ⊆ count st.next_uvar ∧
FDOM s = count st.next_uvar ∧
t_wfs st.subst ∧
MAP (convert_t o (t_walkstar s)) ts' = ts ∧
EVERY (check_t n {}) (MAP (t_walkstar s) ts') ∧
check_freevars n [] t
⇒
?t' st' s' constraints'.
constrain_op l op ts' st = (Success t',st') ∧
sub_completion n st'.next_uvar st'.subst constraints' s' ∧
t_compat s s' ∧
FDOM st'.subst ⊆ count st'.next_uvar ∧
FDOM s' = count st'.next_uvar ∧
t = convert_t (t_walkstar s' t')
Proof
  strip_tac>>
  `?is_case. is_case op` by (qexists_tac `\x. T` >> simp [])>>
  strip_tac>>
  `?simple argc retc. op_simple_constraints op = (simple, argc, retc)`
    by (metis_tac [pair_CASES])>>
  Cases_on `simple`>-(
    drule constrain_op_complete_simple_helper
    \\ rpt (disch_then drule)
    \\ rw []
    \\ imp_res_tac sub_completion_wfs
    \\ fs [sub_completion_def]
    \\ `∃s3. pure_add_constraints st.subst (xs ++ constraints) s3 ∧
         t_compat s3 s ∧ t_compat s s3`
        by (metis_tac [pure_add_constraints_append, pure_add_constraints_swap])
    \\ qspecl_then [`n`,`s3`,`s`] mp_tac (GEN_ALL t_compat_bi_ground)
    \\ rw []
    \\ fs [pure_add_constraints_append]
    \\ first_x_assum (qspecl_then [`l`, `st with subst := s2`] mp_tac)
    \\ rw []
    \\ asm_exists_tac
    \\ simp []
    \\ imp_res_tac pure_add_constraints_success
  )>>
  fs[sub_completion_def]>>
  rw[]>>
  rfs[]>>
  imp_res_tac pure_add_constraints_wfs>>
  fs[type_op_cases]>>
  rfs [op_simple_constraints_def]>>
  simp [constrain_op_case_def, op_simple_constraints_def]>>
  every_case_tac>>
  ntac 2 (fs[unconvert_t_def,MAP]>>rw[])>>
  fs[add_constraint_success2,success_eqns,sub_completion_def,Tword64_def,word_tc_def]>>
  Q.SPECL_THEN [`st.subst`,`constraints`,`s`] mp_tac pure_add_constraints_success>>
  impl_tac>>rw[] >> RULE_ASSUM_TAC flip_converts
  >> TRY1
    (qpat_x_assum `_ <> SND (op_to_string _)` mp_tac>>
      simp [op_to_string_def])
  >> TRY1
    (* ... -> t->int*)
    (unconversion_tac>>
    Q.EXISTS_TAC `Infer_Tapp [] Tint_num`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac)
  >> TRY1 (* ... -> t ->bool*)
    (unconversion_tac>>
    Q.EXISTS_TAC`Infer_Tapp [] Tbool_num`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac)
  >> TRY1
    (* ... ->t->word8*)
    (unconversion_tac>>
    Q.EXISTS_TAC`Infer_Tapp [] Tword8_num`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac)
  >> TRY1 (* ... -> t->double*)
    (unconversion_tac>>
    Q.EXISTS_TAC `Infer_Tapp [] Tdouble_num`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac)
  >> TRY1 (* ... -> t->word64*)
    (unconversion_tac>>
    Q.EXISTS_TAC `Infer_Tapp [] Tword64_num`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac)
  >> TRY1 (*simple t->t'*)
    (unconversion_tac>>
    qpat_abbrev_tac `ls = [(h,B)]`>>
    pac_tac)
  >> TRY1 (*Opapp --> Example with fresh unification variable*)
    ((*First find the extension to s and prove every property of s is carried over*)
    extend_uvar_tac `t`>>
    qpat_abbrev_tac`ls = [(h,Infer_Tapp B C)]`>>
    `t_walkstar s' h' = t_walkstar s h'` by
      metis_tac[submap_t_walkstar_replace]>>
    `t_walkstar s' h = t_walkstar s h` by
      metis_tac[submap_t_walkstar_replace]>>
    rest_uvar_tac)
  >> TRY1 (* 'a -> 'a ref Opref *)
    (Q.EXISTS_TAC`s`>>Q.EXISTS_TAC`constraints`>>
    fs[t_compat_refl]>>
    fs[convert_t_def,Once t_walkstar_eqn,Once t_walk_eqn,SimpRHS])
  >> TRY1 (* 'a ref -> 'a Opderef *)
    (extend_uvar_tac `t`>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    rename1 `[(h, Infer_Tapp _ _)]` >>
    replace_uvar_tac>>
    rest_uvar_tac)
  >> TRY1 (* ... ->  word8array *)
    (unconversion_tac>>
    Q.EXISTS_TAC`Infer_Tapp [] Tword8array_num`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac)
  >> TRY1 (* ... -> t -> tup *)
    (unconversion_tac >>
    qexists_tac`Infer_Tapp [] Ttup_num` >>
    fs[pure_add_constraints_combine] >>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac )
  >> TRY1 ( (* ... -> string *)
    unconversion_tac >>
    qexists_tac`Infer_Tapp [] Tstring_num` >>
    fs[pure_add_constraints_combine] >>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac )
  >> TRY1 ( (* ... -> char *)
    unconversion_tac >>
    qexists_tac`Infer_Tapp [] Tchar_num` >>
    fs[pure_add_constraints_combine] >>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    pac_tac )
  >> TRY1 (* list -> vector *)
    (rename1`Tapp [t2] Tvector_num` >>
    extend_uvar_tac `t2`>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    rename1 `[(h,Infer_Tapp _ _)]` >>
    replace_uvar_tac>>
    rest_uvar_tac>>
    `t_wfs si` by metis_tac[pure_add_constraints_wfs]>>
    fs[convert_t_def,t_walkstar_eqn,t_walk_eqn]>>
    metis_tac[check_freevars_empty_convert_unconvert_id])
  >> TRY1
    (* ... ->list*)
    (
    qexists_tac`Infer_Tapp [Infer_Tuvar st.next_uvar] Tlist_num` >>
    fs[pure_add_constraints_combine]>>
    rename1`Tapp [t1] Tlist_num` >>
    extend_uvar_tac`t1`>>
    qpat_abbrev_tac `ls = (h,_)::_` >>
    `pure_add_constraints s' ls s'` by
      (match_mp_tac pure_add_constraints_ignore >>
      fs[Abbr`ls`]>>
      simp[t_walkstar_eqn1]>>
      metis_tac[t_walkstar_no_vars,t_walkstar_SUBMAP])>>
    pure_add_constraints_combine_tac [`st`,`constraints'`,`s'`]>>
    fs[pure_add_constraints_append]>>
    Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st.next_uvar+1; next_id := st.next_id |>` >>fs[]>>
    Q.EXISTS_TAC`si`>>
    Q.EXISTS_TAC`constraints'`>>
    Q.SPECL_THEN [`n`,`si`,`s'`] assume_tac (GEN_ALL t_compat_bi_ground)>>
    rfs[]>>
    rw[]
    >-
      metis_tac[t_compat_trans]
    >-
      metis_tac[pure_add_constraints_success]
    >>
      `t_wfs si` by metis_tac[pure_add_constraints_wfs]>>
      fs[t_walkstar_eqn,t_walk_eqn,convert_t_def]>>
      metis_tac[check_freevars_empty_convert_unconvert_id])
  >> TRY1
    (rename1`Tapp [t1] Tvector_num` >>
    extend_uvar_tac `t1`>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    rename1 `[(h, Infer_Tapp _ _)]` >>
    replace_uvar_tac>>
    rest_uvar_tac)
  >> TRY1
    (rename1`Tapp [t1] Tarray_num` >>
    extend_uvar_tac `t1`>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    rename1 `[(h, Infer_Tapp _ _)]` >>
    replace_uvar_tac>>
    rest_uvar_tac>>
    `t_wfs si` by metis_tac[pure_add_constraints_wfs]>>
    fs[convert_t_def,t_walkstar_eqn,t_walk_eqn]>>
    metis_tac[check_freevars_empty_convert_unconvert_id])
  >> TRY1
    (Q.EXISTS_TAC `Infer_Tuvar st.next_uvar`>>
    fs[pure_add_constraints_combine]>>
    extend_uvar_tac `t`>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B);C]`>>
    rename1 `[(h,Infer_Tapp _ _); _]` >>
    replace_uvar_tac>>
    `t_walkstar s' h' = Infer_Tapp [] Tint_num` by
      metis_tac[submap_t_walkstar_replace]>>
    rest_uvar_tac)
QED

Definition simp_tenv_invC_def:
  simp_tenv_invC s tvs tenv tenvE ⇔
  (!n t. ALOOKUP tenvE n = SOME t
  ⇒
  check_freevars tvs [] t ∧
  ?t'. ALOOKUP tenv n = SOME t' ∧
       unconvert_t t = t_walkstar s t') ∧
  !n t'. ALOOKUP tenv n = SOME t' ⇒
  ?t. ALOOKUP tenvE n = SOME t
End

Theorem simp_tenv_invC_empty[local]:
  simp_tenv_invC s n [] []
Proof
  rw[simp_tenv_invC_def]
QED

Theorem simp_tenv_invC_more[local]:
  simp_tenv_invC s tvs tenv tenvE ∧
  t_compat s s' ⇒
  simp_tenv_invC s' tvs tenv tenvE
Proof
  rw[simp_tenv_invC_def]>>
  res_tac>>
  fs[t_compat_def]>>
  metis_tac[check_freevars_to_check_t,t_walkstar_no_vars]
QED

Theorem simp_tenv_invC_append[local]:
  simp_tenv_invC s'' tvs tenv tenvE ∧
  simp_tenv_invC s'' tvs tenv' tenvE'
  ⇒
  simp_tenv_invC s'' tvs (tenv'++tenv) (tenvE' ++ tenvE)
Proof
  rw[simp_tenv_invC_def]>>
  fs[ALOOKUP_APPEND]>>
  every_case_tac>>res_tac>>fs[]>>metis_tac[]
QED

(*convert on both sides of eqn*)
Theorem convert_bi_remove:
 convert_t A = convert_t B ∧
  check_t n {} A ∧
  check_t m {} B
  ⇒
  A = B
Proof
  rw[]>>
  last_x_assum (assume_tac o (Q.AP_TERM `unconvert_t`))>>
  metis_tac[check_t_empty_unconvert_convert_id]
QED

(*Substituting every tvs away with something that has no tvs leaves none left*)
Theorem infer_type_subst_check_t_less[local]:
  LENGTH ls = LENGTH tvs ∧
  EVERY (check_t n {}) ls ⇒
  (!t.
  check_freevars n tvs t
  ⇒
  check_t n {} (infer_type_subst (ZIP (tvs,ls)) t)) ∧
  (!ts.
  EVERY (check_freevars n tvs) ts
  ⇒
  EVERY (check_t n {}) (MAP (infer_type_subst (ZIP(tvs,ls))) ts))
Proof
  strip_tac>>
  Induct>>rw[]
  >-
    (rename1 ‘Tvar s’>>
     fs[check_freevars_def,infer_type_subst_alt]>>
    `?x. ALOOKUP (ZIP(tvs,ls)) s = SOME x` by
      (SPOSE_NOT_THEN assume_tac>>
      imp_res_tac NOT_SOME_NONE>>
      fs[ALOOKUP_NONE]>>
      metis_tac[MAP_ZIP])>>
    imp_res_tac ALOOKUP_MEM>>
    Q.ISPECL_THEN [`tvs`,`ls`,`s,x`] assume_tac MEM_ZIP>> rfs[]>>
    metis_tac[EVERY_EL])
  >>
    fs[infer_type_subst_alt,check_t_def,check_freevars_def]>>
    fs[EVERY_MAP]>>metis_tac[]
QED

Theorem infer_p_complete:
  (!tvs tenv p t tenvE.
  type_p tvs tenv p t tenvE
  ⇒
  !l s ienv st constraints.
  tenv_ctor_ok tenv.c ∧
  ienv.inf_c = tenv.c ∧
  ienv.inf_t = tenv.t ∧
  tenv_abbrev_ok tenv.t ∧
  t_wfs st.subst ∧
  sub_completion tvs st.next_uvar st.subst constraints s ∧
  FDOM st.subst ⊆ count st.next_uvar ∧
  FDOM s = count st.next_uvar
  ⇒
  ?t' new_bindings st' s' constraints'.
    infer_p l ienv p st  = (Success (t',new_bindings),st') ∧
    sub_completion tvs st'.next_uvar st'.subst constraints' s' ∧
    FDOM st'.subst ⊆ count st'.next_uvar ∧
    FDOM s' = count st'.next_uvar ∧
    t_compat s s' ∧
    simp_tenv_invC s' tvs new_bindings tenvE ∧
    t = convert_t (t_walkstar s' t')) ∧
  (!tvs tenv ps ts tenvE.
  type_ps tvs tenv ps ts tenvE
  ⇒
  !l s ienv st constraints.
  tenv_ctor_ok tenv.c ∧
  ienv.inf_c = tenv.c ∧
  ienv.inf_t = tenv.t ∧
  tenv_abbrev_ok tenv.t ∧
  t_wfs st.subst ∧
  sub_completion tvs st.next_uvar st.subst constraints s ∧
  FDOM st.subst ⊆ count st.next_uvar ∧
  FDOM s = count st.next_uvar
  ⇒
  ?ts' new_bindings st' s' constraints'.
    infer_ps l ienv ps st = (Success (ts',new_bindings),st') ∧
    sub_completion tvs st'.next_uvar st'.subst constraints' s' ∧
    FDOM st'.subst ⊆ count st'.next_uvar ∧
    FDOM s' = count st'.next_uvar ∧
    t_compat s s' ∧
    simp_tenv_invC s' tvs new_bindings tenvE ∧
    ts = MAP (convert_t o t_walkstar s') ts')
Proof
  ho_match_mp_tac type_p_strongind>>
  rw[UNCURRY,success_eqns,infer_p_def]
  >- (
    Q.SPECL_THEN [`t`,`st`,`s`,`tvs`,`constraints`]
      mp_tac (GEN_ALL extend_one_props)>>
    `t_wfs s` by metis_tac[sub_completion_wfs]>>
    impl_tac >> fs[LET_THM,sub_completion_def]>>
    qpat_abbrev_tac `s' = s|++A`>>
    qpat_abbrev_tac `constraints' = constraints ++ B`>> rw[]>>
    ntac 2 HINT_EXISTS_TAC>>rw[]
    >-
      (fs[SUBSET_DEF,count_def]>>rw[]>>res_tac>>DECIDE_TAC)
    >-
      metis_tac[SUBMAP_t_compat]
    >>
      fs[simp_tenv_invC_def]>>
      metis_tac[check_freevars_empty_convert_unconvert_id])
  >- (
    Q.SPECL_THEN [`t`,`st`,`s`,`tvs`,`constraints`]
      mp_tac (GEN_ALL extend_one_props)>>
    `t_wfs s` by metis_tac[sub_completion_wfs]>>
    impl_tac >> fs[LET_THM,sub_completion_def]>>
    qpat_abbrev_tac `s' = s|++A`>>
    qpat_abbrev_tac `constraints' = constraints ++ B`>> rw[]>>
    ntac 2 HINT_EXISTS_TAC>>rw[]
    >-
      (fs[SUBSET_DEF,count_def]>>rw[]>>res_tac>>DECIDE_TAC)
    >-
      metis_tac[SUBMAP_t_compat]
    >>
      fs[simp_tenv_invC_def]>>
      metis_tac[check_freevars_empty_convert_unconvert_id])
  >> TRY(ntac 2 HINT_EXISTS_TAC >>
    imp_res_tac sub_completion_wfs>>
    fs[t_walkstar_eqn,convert_t_def,t_walk_eqn,Tchar_def]>>
    metis_tac[t_compat_refl,simp_tenv_invC_empty])
  >- (
    first_x_assum(qspecl_then [`l`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>rfs[]>>
    imp_res_tac tenv_ctor_ok_lookup>>
    Q.SPECL_THEN [`st'`,`constraints'`,`s'`,`ts'`,`tvs`] mp_tac extend_multi_props>>
    impl_keep_tac >-
    (fs[t_compat_def,sub_completion_def]>>
      metis_tac[infer_p_wfs])>>
    fs[LET_THM]>>
    qpat_abbrev_tac `s'' = s'|++A`>>
    qpat_abbrev_tac `ls = ZIP (MAP Infer_Tuvar A,MAP unconvert_t ts')`>>
    Q.ABBREV_TAC `constraints'' = constraints' ++ls`>>
    rw[Abbr`ls`]>>
    fs[sub_completion_def]>>
    (*Prove properties about the new completed map*)
    (*Most difficult would be the walkstar property*)
    qpat_abbrev_tac `ls = ZIP(ts'',MAP (infer_type_subst A) B)`>>
    `LENGTH ts'' = LENGTH ts` by
      metis_tac[LENGTH_MAP]>>
    Q.ABBREV_TAC `unconv_ts' = MAP unconvert_t ts'`>>
    `pure_add_constraints s'' ls s''` by
      (match_mp_tac pure_add_constraints_ignore>>
      fs[Abbr`ls`,EVERY_MEM]>>rw[]>>
      fs[MAP_EQ_EVERY2,LIST_REL_EL_EQN]>>
      rfs[LENGTH_MAP,MEM_ZIP]>>
      res_tac>> fs[EL_MAP]>>
      Q.SPECL_THEN [`EL n ts`,`tvs'`,`unconv_ts'`] mp_tac(fst(CONJ_PAIR convert_t_subst))>>
      impl_keep_tac
      >-
        (fs[MEM_EL,Abbr`unconv_ts'`,LENGTH_MAP]>>metis_tac[])
      >>
      strip_tac>>
      `MAP convert_t unconv_ts' = ts'` by
        (fs[Abbr`unconv_ts'`,MAP_EQ_ID,MAP_MAP_o,EVERY_MEM]>>
        rw[]>>res_tac>>metis_tac[check_freevars_empty_convert_unconvert_id])>>
      pop_assum SUBST_ALL_TAC>>
      pop_assum (SUBST_ALL_TAC o SYM)>>
      imp_res_tac convert_bi_remove>>
      pop_assum (Q.SPEC_THEN `tvs` mp_tac)>>
      impl_keep_tac>-
        (imp_res_tac infer_p_check_t>>
        fs[EVERY_EL]>>
        pop_assum(qspec_then `n` mp_tac)>>impl_tac>-metis_tac[]>>
        assume_tac (GEN_ALL check_t_less)>>
        pop_assum(qspecl_then [`count st'.next_uvar`,`s'`,`tvs`] assume_tac)>>
        rw[]>>
        first_x_assum(qspec_then `EL n ts''` mp_tac)>>
        impl_tac>>fs[])>>
      strip_tac>>
      pop_assum (qspec_then `tvs` mp_tac)>>impl_tac
      >-
        (assume_tac (GEN_ALL infer_type_subst_check_t_less)>>
        pop_assum(qspecl_then [`tvs'`,`tvs`,`unconv_ts'`] mp_tac)>>
        impl_tac>-
          (fs[EVERY_MEM,Abbr`unconv_ts'`]>>rw[MEM_MAP]>>res_tac>>
          fs[check_freevars_to_check_t])>>
        rw[]>>
        first_x_assum(qspec_then `EL n ts` mp_tac)>>
        impl_tac>-
          (imp_res_tac check_freevars_add>>
          pop_assum (qspec_then `tvs` assume_tac)>>rfs[])>>
        rw[])>>
      rw[]>>
      imp_res_tac submap_t_walkstar_replace>>
      ntac 7 (pop_assum kall_tac)>>
      pop_assum (SUBST1_TAC o SYM)>>
      qpat_x_assum `C = t_walkstar A B` (SUBST1_TAC o SYM)>>
      Q.SPECL_THEN [`EL n ts`,`tvs'`,`s''`,`st'.next_uvar`] mp_tac
         (fst (CONJ_PAIR subst_infer_subst_swap))>>
      impl_tac>-metis_tac[pure_add_constraints_success]>>
      rw[]>>fs[]>>
      AP_THM_TAC>>
      ntac 3 AP_TERM_TAC>>
      match_mp_tac LIST_EQ>> CONJ_ASM1_TAC
      >>
        fs[LENGTH_MAP,LENGTH_COUNT_LIST]
      >>
        rw[Abbr`s''`]>>
        simp[LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST])>>
    pure_add_constraints_combine_tac [`st'`,`constraints''`,`s''`]>>
    imp_res_tac infer_p_wfs>>fs[pure_add_constraints_append]>>
    Q.EXISTS_TAC `<|subst:=s2';next_uvar:=st'.next_uvar+LENGTH tvs';next_id:=st'.next_id|>`>>
    fs[]>>
    Q.LIST_EXISTS_TAC [`si`,`constraints''`]>>fs[]>>
    Q.SPECL_THEN [`tvs`,`si`,`s''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
    rfs[]>>
    rw[simp_tenv_invC_def]
    >-
      metis_tac[pure_add_constraints_success]
    >-
      metis_tac[t_compat_trans,SUBMAP_t_compat]
    >-
      metis_tac[simp_tenv_invC_def]
    >-
      (fs[simp_tenv_invC_def]>>res_tac>>
      imp_res_tac check_freevars_to_check_t>>
      `t_walkstar s' t' = t_walkstar s'' t'` by
        (match_mp_tac (GEN_ALL submap_t_walkstar_replace)>>
        metis_tac[check_freevars_to_check_t])>>
      fs[t_compat_def])
    >-
      metis_tac[simp_tenv_invC_def]
    >>
      fs[t_compat_def]>>
      simp[Once convert_t_def,Once t_walk_eqn,Once t_walkstar_eqn]>>
      fs[MAP_MAP_o]>>
      match_mp_tac LIST_EQ>>rw[]
      >-
        fs[LENGTH_COUNT_LIST]
      >>
        res_tac>>
        fs[LENGTH_COUNT_LIST,EL_COUNT_LIST,Abbr`unconv_ts'`,EL_MAP]>>
        pop_assum (assume_tac o Q.AP_TERM `convert_t`)>>
        `convert_t (EL x (MAP unconvert_t ts')) = EL x ts'` by
          (fs[EL_MAP]>>
          metis_tac[EVERY_EL,check_freevars_empty_convert_unconvert_id])>>
        fs[]>>
        first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)>>
        rpt AP_TERM_TAC>>
        match_mp_tac EQ_SYM >>
        match_mp_tac (GEN_ALL check_t_empty_unconvert_convert_id) >>
        simp[EL_MAP] >>
        qexists_tac`tvs` >>
        match_mp_tac check_freevars_to_check_t >>
        fs[EVERY_MEM,MEM_EL,PULL_EXISTS])
  >- (
    first_x_assum(qspecl_then [`l`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    ntac 2 HINT_EXISTS_TAC>>fs[]>>
    imp_res_tac infer_p_wfs>>
    imp_res_tac sub_completion_wfs>>
    fs[Once t_walkstar_eqn,Once t_walk_eqn,convert_t_def,MAP_MAP_o]>>
    fs[MAP_EQ_f])
  >- (
    first_x_assum(qspecl_then [`l`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    ntac 2 HINT_EXISTS_TAC>>fs[]>>
    imp_res_tac infer_p_wfs>>
    imp_res_tac sub_completion_wfs>>
    fs[Once t_walkstar_eqn,Once t_walk_eqn,SimpRHS,convert_t_def])
  >- ( (* Pany case *)
    first_x_assum drule>> simp[]>>
    rpt(disch_then drule)>>
    disch_then(qspec_then`l` assume_tac)>>fs[]>>
    asm_exists_tac>>simp[]>>
    match_mp_tac simp_tenv_invC_append>>simp[simp_tenv_invC_def]>>
    DEP_REWRITE_TAC[check_t_to_check_freevars]>>
    CONJ_ASM1_TAC >- (
      imp_res_tac infer_p_check_t>>simp[]>>
      imp_res_tac(CONJUNCT1 check_t_less)>>
      rfs[]>>
      pop_assum(qspec_then`s'` mp_tac)>>
      disch_then(qspec_then`tvs` mp_tac)>>simp[]>>
      fs[t_compat_def]>>
      fs[sub_completion_def])>>
    metis_tac[check_t_empty_unconvert_convert_id])
  >- (
    simp [type_name_check_subst_comp_thm] >>
    first_x_assum(qspecl_then [`l`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    qmatch_goalsub_abbrev_tac`t_unify _ _ A`>>
    qabbrev_tac`ls = [(t',A)]`>>
    imp_res_tac infer_p_wfs>>
    `pure_add_constraints s' ls s'` by
      (match_mp_tac pure_add_constraints_ignore>>
      fs[Abbr`A`,Abbr`ls`]>>
      CONJ_ASM1_TAC
      >-
        metis_tac[sub_completion_wfs]
      >>
      fs[sub_completion_def]>>
      imp_res_tac infer_p_check_t>>
      imp_res_tac(CONJUNCT1 check_t_less)>>
      rfs[]>>
      imp_res_tac check_t_to_check_freevars>>
      metis_tac[infer_type_subst_nil,check_t_empty_unconvert_convert_id,t_walkstar_idempotent])>>
    `pure_add_constraints st'.subst (constraints'++ls) s'` by
      metis_tac[pure_add_constraints_append,sub_completion_def]>>
    imp_res_tac pure_add_constraints_swap>>
    fs[pure_add_constraints_append,Abbr`ls`,pure_add_constraints_def,sub_completion_def]>>
    map_every qexists_tac [`si'`,`constraints'`]>>fs[]>>
    drule (GEN_ALL t_compat_bi_ground)>>
    disch_then(qspec_then`si'` assume_tac)>>rfs[]>>
    fs[simp_tenv_invC_def]>>
    metis_tac[t_compat_trans,t_unify_wfs,pure_add_constraints_success])
  >- (
    last_x_assum(qspecl_then [`l`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    first_x_assum(qspecl_then [`l`, `s'`,`ienv`,`st'`,`constraints'`] mp_tac)>>
    impl_tac>>fs[]
    >- metis_tac[infer_p_wfs]
    >>
    rw[]>>fs[]>>
    ntac 2 HINT_EXISTS_TAC>>fs[]>>
    rw[]
    >- metis_tac[t_compat_trans]
    >- metis_tac[simp_tenv_invC_more,simp_tenv_invC_append]
    >>
       imp_res_tac infer_p_check_t>>
       assume_tac (GEN_ALL check_t_less)>>
       fs[sub_completion_def]>>
       pop_assum (qspecl_then [`count st'.next_uvar`,`s'`,`tvs`] assume_tac)>>
       rfs[]>>
       first_x_assum(qspec_then `t'` mp_tac)>>
       impl_tac>-
         metis_tac[t_compat_def]>>
       rw[]>>AP_TERM_TAC>>
       fs[t_compat_def]>>
       metis_tac[t_walkstar_no_vars])
QED

(*Specialize check_t_less a bit since we use this form a lot*)
Theorem sub_completion_completes:
 t_wfs s ∧
  check_t 0 (count n) t ∧
  FDOM s = count n ∧
  (!uv. uv < n ⇒
    check_t tvs {} (t_walkstar s (Infer_Tuvar uv)))
  ⇒
  check_t tvs {} (t_walkstar s t)
Proof
  assume_tac (GEN_ALL (CONJUNCT1 check_t_less))>>
  rw[]>>
  first_x_assum(qspecl_then[`count n`,`s`,`tvs`,`t`] mp_tac)>>
  impl_tac>>fs[]
QED

Theorem lookup_var_bind_var_list[local]:
  !bindings.
  lookup_var x (bind_var_list 0 bindings tenvE) tenv =
  case x of
  Short id =>
    (case ALOOKUP bindings id of
      SOME t => SOME (0,t)
    | NONE => lookup_var x tenvE tenv)
  | _ => lookup_var x tenvE tenv
Proof
  Induct>>rw[bind_var_list_def]>>Cases_on`x`>>
  fs[lookup_var_def,lookup_varE_def]>>
  fs[tveLookup_bvl,deBruijn_inc0]>>
  every_case_tac>>fs[]
QED

(*This should be general enough to prove both Mat and Handle cases*)
Theorem infer_pes_complete[local]:
  ∀pes st' constraints' s'.
  pes ≠ [] ∧
  ienv_ok (count uvar) ienv ∧
  uvar ≤ st'.next_uvar ∧
  t_wfs st'.subst ∧
  env_rel_complete s' ienv tenv tenvE ∧
  (∀x::set pes.
    ∃bindings.
      ALL_DISTINCT (pat_bindings (FST x) []) ∧
      type_p (num_tvs tenvE) tenv (FST x) t1 bindings ∧
      type_e tenv (bind_var_list 0 bindings tenvE) (SND x) t2 ∧
      ∀l s'' ienv' st'' constraints''.
        ienv_ok (count st''.next_uvar) ienv' ∧ t_wfs st''.subst ∧
        FDOM st''.subst ⊆ count st''.next_uvar ∧
        sub_completion (num_tvs (bind_var_list 0 bindings tenvE)) st''.next_uvar st''.subst constraints'' s'' ∧
        FDOM s'' = count st''.next_uvar ∧
        env_rel_complete s'' ienv' tenv (bind_var_list 0 bindings tenvE) ⇒
        ∃t'' st''' s''' constraints'''.
          infer_e l ienv' (SND x) st'' = (Success t'',st''') ∧
          sub_completion (num_tvs tenvE) st'''.next_uvar st'''.subst constraints''' s''' ∧
          FDOM st'''.subst ⊆ count st'''.next_uvar ∧
          FDOM s''' = count st'''.next_uvar ∧ t_compat s'' s''' ∧
          t2 = convert_t (t_walkstar s''' t'')) ∧
  sub_completion (num_tvs tenvE) st'.next_uvar st'.subst constraints' s' ∧
  FDOM st'.subst ⊆ count st'.next_uvar ∧
  FDOM s' = count st'.next_uvar ∧
  unconvert_t t1 = t_walkstar s' t1' ∧
  unconvert_t t2 = t_walkstar s' t2'
  ⇒
  ?st'' s'' constraints''.
  infer_pes l ienv pes t1' t2' st' = (Success (), st'') ∧
  sub_completion (num_tvs tenvE) st''.next_uvar st''.subst constraints'' s'' ∧
  FDOM st''.subst ⊆ count st''.next_uvar ∧
  FDOM s'' = count st''.next_uvar ∧
  t_compat s' s''
Proof
  Induct>- rw[]>>
  rpt GEN_TAC>>
  strip_tac>>
  Cases_on`h`>>
  simp[add_constraint_success2,infer_e_def,success_eqns,UNCURRY]>>
  fs[RES_FORALL]>>
  first_x_assum(qspec_then `q,r` assume_tac)>>rfs[]>>
  Q.SPECL_THEN [`num_tvs tenvE`,`tenv`,`q`,`t1`,`bindings`] assume_tac
    (fst (CONJ_PAIR infer_p_complete))>>rfs[]>>
  fs[ienv_ok_def,env_rel_complete_def]>>
  pop_assum(qspecl_then [`l`, `s'`,`ienv`,`st'`,`constraints'`] assume_tac)>>rfs[]>>
  imp_res_tac infer_p_bindings>>
  pop_assum(qspec_then `[]` assume_tac)>>fs[]>>
  qpat_abbrev_tac`ls = [(t1',t')]`>>
  `check_t (num_tvs tenvE) {} (t_walkstar s'' t')` by
    (`t_wfs s''` by metis_tac[sub_completion_wfs,infer_p_wfs]>>
    imp_res_tac infer_p_check_t>>
    rfs[sub_completion_def]>>
    metis_tac[sub_completion_completes])>>
  imp_res_tac check_t_empty_unconvert_convert_id>>
  fs[]>>
  pure_add_constraints_ignore_tac `s''`>-
    (CONJ_TAC>-metis_tac[t_compat_def,t_walkstar_SUBMAP,SUBMAP_DEF]>>
    metis_tac[t_compat_def,t_walkstar_no_vars])>>
  fs[sub_completion_def]>>
  pure_add_constraints_combine_tac [`st''`,`constraints''`,`s''`]>>
  `t_wfs st''.subst` by metis_tac[infer_p_wfs]>>fs[]>>
  Q.SPECL_THEN [`num_tvs tenvE`,`si`,`s''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
  rfs[]>>
  fs[pure_add_constraints_append]>>
  fs[Once PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
  Q.ABBREV_TAC `nst = <|next_uvar:=st''.next_uvar;subst:=s2';next_id:=st''.next_id|>`>>
  qexists_tac `nst`>>fs[]>>
  qpat_abbrev_tac `ntenv = nsAppend A B`>>
  first_x_assum(qspecl_then [`l`, `si`,`ienv with inf_v := ntenv`,`nst`,`constraints''`] mp_tac)>>
  impl_keep_tac
  >-
    (fs[Abbr`nst`]>>rw[]
    >-
      (fs[Abbr`ntenv`,ienv_val_ok_def]>>
      match_mp_tac nsAll_nsAppend>>
      fs[nsAll_def,nsLookup_alist_to_ns_some,FORALL_PROD]>>rw[]
      >-
        (fs[ALOOKUP_MAP] >> imp_res_tac ALOOKUP_MEM>>
        imp_res_tac infer_p_check_t>>
        fs[EVERY_MEM]>>
        first_x_assum(qspec_then `(x',p_2)` assume_tac)>>
        rfs[])
      >>
        first_x_assum(qspecl_then[`x`,`p_1`,`p_2`] assume_tac)>>rfs[]>>
        `uvar ≤ st''.next_uvar` by
          (imp_res_tac infer_p_next_uvar_mono>>fs[])>>
        metis_tac[check_t_more4])
     >- metis_tac[pure_add_constraints_wfs]
     >- metis_tac[pure_add_constraints_success]
     >-
       (fs[Abbr`ntenv`,simp_tenv_invC_def,lookup_var_bind_var_list,alist_to_ns_def,nsLookup_nsAppend_some]>>
       Cases_on`x`>>fs[nsLookup_def]
       >-
         (pop_assum mp_tac>>TOP_CASE_TAC>>rw[]
         >-
           (fs[ALOOKUP_MAP]>>
           Cases_on`ALOOKUP new_bindings n`
           >-
             (first_x_assum(qspecl_then [`Short n`,`tvs`,`t`] assume_tac)>>
             rfs[]>>
             qexists_tac`n'`>>fs[id_to_mods_def]>>
             match_mp_tac (GEN_ALL tscheme_approx_weakening2)>>fs[]>>
             qexists_tac`s'`>>
             imp_res_tac infer_p_next_uvar_mono>>
             fs[SUBSET_DEF,EQ_SYM_EQ]>>
             metis_tac[t_compat_trans])
           >>
           metis_tac[option_CLAUSES])
         >>
           first_x_assum(qspecl_then[`n`,`t`] assume_tac)>>rfs[]>>
           HINT_EXISTS_TAC>>fs[ALOOKUP_MAP]>>
           simp[tscheme_approx_def,LENGTH_NIL,infer_deBruijn_subst_id]>>
           metis_tac[t_walkstar_idempotent,t_compat_def])
       >>
       first_x_assum(qspecl_then [`Long m i`,`tvs`,`t`] assume_tac)>>rfs[]>>
       qexists_tac`n`>>rw[]
       >-
         (fs[id_to_mods_def]>>Cases_on`p1`>>fs[nsLookupMod_def])
       >>
         match_mp_tac (GEN_ALL tscheme_approx_weakening2)>>fs[]>>
         qexists_tac`s'`>>
         imp_res_tac infer_p_next_uvar_mono>>
         fs[SUBSET_DEF,EQ_SYM_EQ]>>
         metis_tac[t_compat_trans]))
  >- (
  rw[]>>
  `t_wfs st''''.subst` by metis_tac[infer_e_wfs]>>
  fs[Abbr`nst`]>>
  qunabbrev_tac`ls`>>
  qpat_abbrev_tac `ls = ([t2',t''])`>>
  imp_res_tac infer_e_check_t>>fs[]>>rfs[]>>
  `check_t (num_tvs tenvE) {} (t_walkstar s'''' t'')` by
      (`t_wfs s''''` by metis_tac[infer_e_wfs,pure_add_constraints_wfs]>>
      rfs[num_tvs_bind_var_list]>>
       metis_tac[sub_completion_completes])>>
  pure_add_constraints_ignore_tac `s''''`>-
    (CONJ_TAC>-metis_tac[pure_add_constraints_success]>>
    imp_res_tac check_t_empty_unconvert_convert_id>>
    pop_assum SUBST_ALL_TAC>>
    rfs[]>>
    `t_compat s' s''''` by metis_tac[t_compat_trans]>>
    fs[t_compat_def]>>
    metis_tac[t_walkstar_no_vars])>>
  pure_add_constraints_combine_tac [`st''''`,`constraints''''`,`s''''`]>>
  Q.SPECL_THEN [`num_tvs tenvE`,`si'`,`s''''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
  rfs[]>>
  fs[pure_add_constraints_append]>>
  fs[Once PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
  Q.ABBREV_TAC `nst = <|next_uvar:=st''''.next_uvar;subst:=s2''';next_id:=st''''.next_id|>`>>
  qexists_tac `nst`>>fs[num_tvs_bind_var_list]>>
  (*Unroll infer_pes 1 step*)
  Cases_on`pes`
  >-
    (fs[infer_e_def,success_eqns,Abbr`nst`]>>
    Q.LIST_EXISTS_TAC [`si'`,`constraints''''`]>>
    fs[pure_add_constraints_success]>>
    CONJ_TAC>>metis_tac[pure_add_constraints_success,t_compat_trans])
  >>
    last_x_assum(qspecl_then[`nst`,`constraints''''`,`si'`] mp_tac)>>
    impl_tac>-
      (fs[Abbr`nst`,pure_add_constraints_success]>>rw[]
      >-
        (imp_res_tac infer_p_next_uvar_mono>>fs[]>>
        imp_res_tac infer_e_next_uvar_mono>>fs[])
      >- metis_tac[pure_add_constraints_wfs]
      >-
        (last_x_assum(qspecl_then[`x`,`tvs`,`t`] assume_tac)>>
        rfs[]>>HINT_EXISTS_TAC>>fs[]>>
        match_mp_tac (GEN_ALL tscheme_approx_weakening2)>>
        HINT_EXISTS_TAC>>fs[]>>
        imp_res_tac infer_p_next_uvar_mono>>
        imp_res_tac infer_e_next_uvar_mono>>fs[EQ_SYM_EQ,SUBSET_DEF]>>
        metis_tac[t_compat_trans])
      >- metis_tac[pure_add_constraints_success]
      >>
        `t_compat s' si'` by metis_tac[t_compat_trans]>>
        `t_wfs si'` by metis_tac[pure_add_constraints_wfs]>>
        fs[t_compat_def]>>
        metis_tac[t_walkstar_no_vars,check_t_empty_unconvert_convert_id])>>
    rw[]>>
    fs[Abbr`nst`]>>
    qexists_tac`s'''''`>>qexists_tac`constraints'''''`>>fs[]>>
    metis_tac[t_compat_trans])
QED

Theorem deBrujin_subst_excess[local]:
  (∀n targs t t'.
  check_freevars (LENGTH targs) [] t ∧
  deBruijn_subst n targs t = t'
  ⇒
  ∀ls.
  deBruijn_subst n (targs++ls) t = t')
Proof
  ho_match_mp_tac deBruijn_subst_ind>>
  fs[deBruijn_subst_def]>>rw[]
  >-
    (`n' < LENGTH targs + LENGTH ls +n` by DECIDE_TAC>>fs[]>>
    match_mp_tac EL_APPEND1>>
    DECIDE_TAC)
  >-
    (fs[check_freevars_def]>>
    `n' < LENGTH targs +n` by DECIDE_TAC>>fs[])
  >>
  fs[MAP_EQ_f,check_freevars_def,EVERY_MEM]
QED

Theorem convert_infer_deBruijn_subst[local]:
  ∀subst t.
  check_t (LENGTH subst) {} t ⇒
  convert_t (infer_deBruijn_subst subst t) =
  deBruijn_subst 0 (MAP convert_t subst) (convert_t t)
Proof
  gen_tac \\ ho_match_mp_tac infer_t_ind >>
  rw[infer_deBruijn_subst_alt]>>
  EVAL_TAC>>simp[EL_MAP]>>rw[]>>fs[check_t_def]>>
  fs[MAP_MAP_o,MAP_EQ_f]>>rw[]>>
  first_assum (match_mp_tac o MP_CANON)>>
  fs[EVERY_MEM]
QED

Theorem t_walkstar_infer_db_subst[local]:
  ∀s s' uvars subst tvs.
  s SUBMAP s' ∧ t_wfs s' ∧
  FDOM s = count uvars ∧
  (∀n. n < uvars ⇒ check_t tvs {} (t_walkstar s (Infer_Tuvar n))) ∧
  (∀n. n < LENGTH subst ⇒ t_walkstar s' (Infer_Tuvar (n + uvars)) = t_walkstar s (EL n subst))
  ⇒
  (∀t.
  check_t (LENGTH subst) (count uvars) t ⇒
  t_walkstar s (infer_deBruijn_subst subst t) =
  t_walkstar s' (infer_deBruijn_subst (MAP (λn. Infer_Tuvar (n + uvars)) (COUNT_LIST (LENGTH subst))) t)) ∧
  ∀ts.
  EVERY (check_t (LENGTH subst) (count uvars)) ts ⇒
  MAP (t_walkstar s o infer_deBruijn_subst subst) ts =
  MAP (t_walkstar s' o infer_deBruijn_subst (MAP (λn. Infer_Tuvar (n + uvars)) (COUNT_LIST (LENGTH subst)))) ts
Proof
  ntac 6 strip_tac>>
  imp_res_tac t_wfs_SUBMAP>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[]>>
  fs[infer_deBruijn_subst_alt]
  >-
    (IF_CASES_TAC>>fs[LENGTH_COUNT_LIST,EL_MAP,check_t_def,EL_COUNT_LIST])
  >-
    (fs[t_walkstar_eqn1,check_t_def]>>
    metis_tac[MAP_MAP_o])
  >>
    fs[check_t_def]>>res_tac>>
    imp_res_tac t_walkstar_no_vars>>
    metis_tac[t_walkstar_SUBMAP]
QED

Theorem ienv_val_ok_more[local]:
  (ienv_val_ok cuvs env ∧ cuvs ⊆ cuvs' ⇒
  ienv_val_ok cuvs' env) ∧
  (ienv_val_ok (count uvs) env ∧ uvs ≤ uvs' ⇒
  ienv_val_ok (count uvs') env)
Proof
  rw[ienv_val_ok_def,FORALL_PROD,nsAll_def]>>
  res_tac>>fs[]>>
  metis_tac[check_t_more4,check_t_more5]
QED

Theorem infer_e_complete:
  (!tenv tenvE e t.
   type_e tenv tenvE e t
   ⇒
   !loc s ienv st constraints.
     (*Invariants on the typing and inferencer envs*)
     (*check_menv ienv.inf_m ∧
     menv_alpha ienv.inf_m tenv.m ∧*)
     ienv_ok (count st.next_uvar) ienv ∧
     (*Invariants on inferencer state*)
     t_wfs st.subst ∧
     FDOM st.subst ⊆ count st.next_uvar ∧
     (*Subcompletion*)
     sub_completion (num_tvs tenvE) st.next_uvar st.subst constraints s ∧
     FDOM s = count st.next_uvar ∧
     env_rel_complete s ienv tenv tenvE
     ⇒
     ?t' st' s' constraints'.
       infer_e loc ienv e st = (Success t', st') ∧
       sub_completion (num_tvs tenvE) st'.next_uvar st'.subst constraints' s' ∧
       FDOM st'.subst ⊆  count st'.next_uvar ∧
       FDOM s' = count st'.next_uvar ∧
       t_compat s s' ∧
       t = convert_t (t_walkstar s' t')) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts
   ⇒
   !loc s ienv st constraints.
     (*check_menv ienv.inf_m ∧
     menv_alpha ienv.inf_m tenv.m ∧*)
     ienv_ok (count st.next_uvar) ienv ∧
     t_wfs st.subst ∧
     FDOM st.subst ⊆ count st.next_uvar ∧
     sub_completion (num_tvs tenvE) st.next_uvar st.subst constraints s ∧
     FDOM s = count st.next_uvar ∧
     env_rel_complete s ienv tenv tenvE
     ⇒
     ?ts' st' s' constraints'.
       infer_es loc ienv es st = (Success ts', st') ∧
       sub_completion (num_tvs tenvE) st'.next_uvar st'.subst constraints' s' ∧
       FDOM st'.subst ⊆ count st'.next_uvar ∧
       FDOM s' = count st'.next_uvar ∧
       t_compat s s' ∧
       ts = MAP (convert_t o t_walkstar s') ts') ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env
   ⇒
   !loc s ienv st constraints.
     (*check_menv ienv.inf_m ∧
     menv_alpha ienv.inf_m tenv.m ∧*)
     ienv_ok (count st.next_uvar) ienv ∧
     t_wfs st.subst ∧
     FDOM st.subst ⊆ count st.next_uvar ∧
     sub_completion (num_tvs tenvE) st.next_uvar st.subst constraints s ∧
     FDOM s = count st.next_uvar ∧
     env_rel_complete s ienv tenv tenvE
     ⇒
     ?env' st' s' constraints'.
       infer_funs loc ienv funs st = (Success env', st') ∧
       sub_completion (num_tvs tenvE) st'.next_uvar st'.subst constraints' s' ∧
       FDOM st'.subst ⊆ count st'.next_uvar ∧
       FDOM s' = count st'.next_uvar ∧
       t_compat s s' ∧
       MAP SND env = MAP (convert_t o t_walkstar s') env')
Proof
  ho_match_mp_tac type_e_strongind >>
  rw [add_constraint_success2,success_eqns,infer_e_def]
  (*Easy cases*) >~
  [‘Tapp [] Tint_num = _’]
  >- (qexists_tac `s` >>
      imp_res_tac sub_completion_wfs >>
      rw [t_walkstar_eqn1, convert_t_def] >>
      metis_tac [t_compat_refl]) >~
  [‘Tapp [] Tchar_num = _’]
  >- (qexists_tac `s` >>
      imp_res_tac sub_completion_wfs >>
      rw [t_walkstar_eqn1, convert_t_def, Tchar_def] >>
      metis_tac [t_compat_refl]) >~
  [‘Tapp [] Tstring_num = _’]
  >- (qexists_tac `s'` >>
      imp_res_tac sub_completion_wfs >>
      rw [t_walkstar_eqn1, convert_t_def] >>
      metis_tac [t_compat_refl]) >~
  [‘Tapp [] Tword8_num = _’]
  >- (qexists_tac `s` >>
      imp_res_tac sub_completion_wfs >>
      rw [t_walkstar_eqn1, convert_t_def] >>
      metis_tac [t_compat_refl]) >~
  [‘Tapp [] Tword64_num = _’]
  >- (qexists_tac `s` >>
      imp_res_tac sub_completion_wfs >>
      rw [t_walkstar_eqn1, convert_t_def] >>
      metis_tac [t_compat_refl]) >~
  [‘Tapp [] Tdouble_num = _’]
  >- (qexists_tac `s` >>
      imp_res_tac sub_completion_wfs >>
      rw [t_walkstar_eqn1, convert_t_def] >>
      metis_tac [t_compat_refl])
  >-
    (*Raise*)
    (rfs[ienv_ok_def]>>
    imp_res_tac check_freevars_to_check_t>>
    first_x_assum(qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    `t_wfs st'.subst ∧ t_wfs s'` by
      (CONJ_ASM1_TAC>> metis_tac[infer_e_wfs,sub_completion_wfs])>>
    Q.SPECL_THEN [`t`,`st'`,`s'`,`num_tvs tenvE`,`constraints'`]
      mp_tac (GEN_ALL extend_one_props)>>
    impl_tac >> fs[LET_THM,sub_completion_def]>>
    qpat_abbrev_tac `fin_s = s'|++A`>>
    qpat_abbrev_tac `fin_c = constraints' ++ B`>> rw[]>>
    Q.EXISTS_TAC `Infer_Tuvar st'.next_uvar`>>fs[]>>
    imp_res_tac infer_e_check_t>>
    assume_tac (GEN_ALL check_t_less)>>
    first_x_assum(qspecl_then [`count st'.next_uvar`,`s'`,`num_tvs tenvE`] assume_tac)>>
    fs[]>>
    first_x_assum(qspec_then `t'` mp_tac)>>
    impl_tac>>fs[]>>strip_tac>>
    `t_walkstar fin_s t' = Infer_Tapp [] Texn_num` by
      (qpat_x_assum `A = convert_t B` (assume_tac o SYM o (Q.AP_TERM`unconvert_t`))>>
      fs[unconvert_t_def]>>
      metis_tac[pure_add_constraints_success,submap_t_walkstar_replace
               ,check_t_empty_unconvert_convert_id])>>
    qpat_abbrev_tac `ls = [(t',Infer_Tapp A B)]`>>
    pure_add_constraints_ignore_tac `fin_s`>>
    pure_add_constraints_combine_tac [`st'`,`fin_c`,`fin_s`]>>
    fs[pure_add_constraints_append]>>
    fs[PULL_EXISTS]>>
    Q.LIST_EXISTS_TAC [`si`,`fin_c`,`<|subst:=s2' ; next_uvar := st'.next_uvar; next_id := st'.next_id |>`]>>
    Q.SPECL_THEN [`num_tvs tenvE`,`si`,`fin_s`] assume_tac (GEN_ALL t_compat_bi_ground)>>
    rfs[]>>
    metis_tac[pure_add_constraints_success,t_compat_trans
             ,check_freevars_empty_convert_unconvert_id])
  >- (*Handler*)
    (last_x_assum (qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>rfs[]>>
    fs[UNCURRY]>>
    imp_res_tac infer_e_wfs>>
    drule (GEN_ALL infer_pes_complete)>>
    fs[sub_completion_def]>>
    fs[ienv_ok_def]>>
    imp_res_tac infer_e_check_t>>
    rfs[]>>
    imp_res_tac pure_add_constraints_wfs>>
    `check_t (num_tvs tenvE) {} (t_walkstar s' t')` by
      metis_tac[sub_completion_completes]>>
    fs[]>>
    disch_then (qspecl_then [`st.next_uvar`,`tenvE`,`tenv`,`t'`,`t`,`Infer_Tapp [] Texn_num`,`Tapp [] Texn_num`,`loc`,`ienv`,`st'`,`constraints'`,`s'`] mp_tac)>>
    impl_keep_tac >-
      (fs[env_rel_complete_def]>>rw[]
      >-
        metis_tac[infer_e_next_uvar_mono]
      >-
        metis_tac[]
      >-
        (res_tac>>fs[]>>
        match_mp_tac tscheme_approx_weakening2>>fs[]>>
        imp_res_tac infer_e_next_uvar_mono>>fs[SUBSET_DEF])
      >-
        (EVAL_TAC>>
        match_mp_tac (GSYM t_walkstar_no_vars)>>
        EVAL_TAC>>fs[])>>
      metis_tac[check_t_empty_unconvert_convert_id])
    >>
    rw[]>>
    map_every qexists_tac [`st'''`,`s'''`,`constraints'''`]>>fs[]>>rw[]
    >-
      metis_tac[t_compat_trans]>>
    AP_TERM_TAC>>
    fs[t_compat_def]>>
    metis_tac[t_walkstar_no_vars])
  >- (* Con *)
    (first_x_assum(qspecl_then[`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[sub_completion_def,ienv_ok_def]>>fs[env_rel_complete_def]>>
    fs[success_eqns]>>
    qspecl_then [`st'`,`constraints'`,`s'`,`ts'`,`num_tvs tenvE`]
      mp_tac extend_multi_props>>
    impl_keep_tac>-
      (fs[]>>metis_tac[infer_e_wfs,pure_add_constraints_wfs])>>
    imp_res_tac tenv_ctor_ok_lookup>>
    fs[LET_THM]>>
    qpat_abbrev_tac `s'' = s'|++A`>>
    qpat_abbrev_tac `ls = ZIP (MAP Infer_Tuvar A,MAP unconvert_t ts')`>>
    Q.ABBREV_TAC `constraints'' = constraints' ++ls`>>
    rw[Abbr`ls`]>>
    qpat_abbrev_tac `ls = ZIP(ts'',MAP (infer_type_subst A) B)`>>
    `LENGTH ts'' = LENGTH ts` by metis_tac[LENGTH_MAP]>>
    Q.ABBREV_TAC `unconv_ts' = MAP unconvert_t ts'`>>
    (*pretty much same as infer_p's pcons*)
    `pure_add_constraints s'' ls s''` by
       (match_mp_tac pure_add_constraints_ignore>>
       fs[Abbr`ls`,EVERY_MEM]>>rw[]>>
       fs[MAP_EQ_EVERY2,LIST_REL_EL_EQN]>>
       rfs[LENGTH_MAP,MEM_ZIP]>>
       res_tac>> fs[EL_MAP]>>
       Q.SPECL_THEN [`EL n ts`,`tvs`,`unconv_ts'`] mp_tac(fst(CONJ_PAIR convert_t_subst))>>
       impl_keep_tac
       >-
         (fs[MEM_EL,Abbr`unconv_ts'`,LENGTH_MAP]>>metis_tac[])
       >>
       strip_tac>>
       `MAP convert_t unconv_ts' = ts'` by
         (fs[Abbr`unconv_ts'`,MAP_EQ_ID,MAP_MAP_o,EVERY_MEM]>>
         rw[]>>res_tac>>metis_tac[check_freevars_empty_convert_unconvert_id])>>
       pop_assum SUBST_ALL_TAC>>
       pop_assum (SUBST_ALL_TAC o SYM)>>
       imp_res_tac convert_bi_remove>>
       pop_assum (Q.SPEC_THEN `num_tvs tenvE` mp_tac)>>
       impl_keep_tac>-
         (imp_res_tac infer_e_check_t>>
         fs[EVERY_EL]>>
         first_x_assum(qspec_then `n` mp_tac)>>impl_tac>-metis_tac[]>>
         assume_tac (GEN_ALL check_t_less)>>
         pop_assum(qspecl_then [`count st'.next_uvar`,`s'`
                               ,`num_tvs tenvE`] assume_tac)>>
         rw[]>>
         first_x_assum(qspec_then `EL n ts''` mp_tac)>>
         impl_tac>>fs[])>>
       strip_tac>>
       pop_assum (qspec_then `num_tvs tenvE` mp_tac)>>impl_tac
       >-
         (assume_tac (GEN_ALL infer_type_subst_check_t_less)>>
         pop_assum(qspecl_then [`tvs`,`num_tvs tenvE`
                               ,`unconv_ts'`] mp_tac)>>
         impl_tac>-
           (fs[EVERY_MEM,Abbr`unconv_ts'`]>>rw[MEM_MAP]>>res_tac>>
           fs[check_freevars_to_check_t])>>
         rw[]>>
         first_x_assum(qspec_then `EL n ts` mp_tac)>>
         impl_tac>-
           (imp_res_tac check_freevars_add>>
           pop_assum (qspec_then `num_tvs tenvE` assume_tac)>>rfs[])>>
         rw[])>>
       rw[]>>
       imp_res_tac submap_t_walkstar_replace>>
       ntac 7 (pop_assum kall_tac)>>
       pop_assum (SUBST1_TAC o SYM)>>
       qpat_x_assum `C = t_walkstar A B` (SUBST1_TAC o SYM)>>
       Q.SPECL_THEN [`EL n ts`,`tvs`,`s''`,`st'.next_uvar`] mp_tac
          (fst (CONJ_PAIR subst_infer_subst_swap))>>
       impl_tac>-metis_tac[pure_add_constraints_success]>>
       rw[]>>fs[]>>
       `LENGTH ts' = LENGTH unconv_ts'` by fs[Abbr`unconv_ts'`]>>
       fs[]>>
       AP_THM_TAC>>
       ntac 3 AP_TERM_TAC>>
       match_mp_tac LIST_EQ>> CONJ_ASM1_TAC
       >>
         fs[LENGTH_MAP,LENGTH_COUNT_LIST]
       >>
         rw[Abbr`s''`]>>
         simp[LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST])>>
    pure_add_constraints_combine_tac [`st'`,`constraints''`,`s''`]>>
    imp_res_tac infer_e_wfs>>fs[pure_add_constraints_append]>>
    Q.EXISTS_TAC `<|subst:=s2';next_uvar:=st'.next_uvar+LENGTH ts';next_id:=st'.next_id|>`>>fs[]>>
    Q.LIST_EXISTS_TAC [`si`,`constraints''`]>>fs[]>>
    Q.SPECL_THEN [`num_tvs tenvE`,`si`,`s''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
    rfs[]>>
    rw[]
    >-
      metis_tac[pure_add_constraints_success]
    >-
      metis_tac[t_compat_trans,SUBMAP_t_compat]
    >>
      fs[t_compat_def]>>
      simp[Once t_walkstar_eqn,Once t_walk_eqn,convert_t_def]>>
      fs[MAP_MAP_o]>>
      match_mp_tac LIST_EQ>>rw[]
      >-
        fs[LENGTH_COUNT_LIST]
      >>
        fs[LENGTH_COUNT_LIST,EL_COUNT_LIST,Abbr`unconv_ts'`,EL_MAP]>>
        ntac 2 (last_x_assum(qspec_then `x` kall_tac))>>
        last_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
        `st'.next_uvar + x = x+st'.next_uvar` by DECIDE_TAC>>
        fs[]>>
        metis_tac[check_freevars_empty_convert_unconvert_id,EVERY_EL])
  >- (*Con NONE*)
     (first_x_assum(qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
     rfs[]>>
     ntac 2 HINT_EXISTS_TAC>>
     fs[t_compat_def]>>
     simp[SimpRHS,Once t_walkstar_eqn,t_walk_eqn,convert_t_def,MAP_MAP_o]>>
     fs[MAP_EQ_f])
  >- (* Var *)
    (fs[env_rel_complete_def]>>pop_assum drule>>rw[]>>
    `t_wfs s` by metis_tac[sub_completion_wfs]>>
    drule tscheme_approx_thm>>
    disch_then drule>>
    strip_tac>>
    qpat_x_assum `t_wfs s` mp_tac>>
    strip_tac>>
    qpat_x_assum `tscheme_approx _ _ _ _` kall_tac >>
    fs[success_eqns]>>
    (* The unconversion of the deBruijn specs *)
    qabbrev_tac`unargs = MAP unconvert_t targs`>>
    first_x_assum (qspec_then`unargs` mp_tac)>>
    impl_tac>-
      (fs[Abbr`unargs`,EVERY_MAP,EVERY_MEM]>>rw[]>>
      metis_tac[check_freevars_to_check_t])>>
    rw[]>>fs[sub_completion_def]>>
    drule (GSYM db_subst_infer_subst_swap3)>>
    disch_then drule>>
    disch_then (qspecl_then[`unargs`] assume_tac)>>
    `MAP (convert_t o t_walkstar s) unargs = targs` by
      (match_mp_tac LIST_EQ>>fs[Abbr`unargs`,EL_MAP]>>rw[]>>
      fs[EVERY_EL]>>res_tac>>
      metis_tac[t_walkstar_no_vars,check_freevars_empty_convert_unconvert_id,check_freevars_to_check_t])>>
    fs[]>>
    Q.SPECL_THEN [`st`,`constraints`,`s`,`MAP convert_t (MAP (t_walkstar s) subst')`,`num_tvs tenvE`] mp_tac extend_multi_props>>
    impl_tac>-
      (fs[EVERY_MEM,MEM_MAP]>>
      rw[]>>
      match_mp_tac check_t_to_check_freevars>>fs[]>>
      res_tac>>
      match_mp_tac (CONJUNCT1 check_t_walkstar)>>
      fs[])>>
    LET_ELIM_TAC>>
    simp[Once SWAP_EXISTS_THM]>>
    qexists_tac`constraints++new_constraints`>>
    qexists_tac`s'`>>simp[]>>
    fs[ienv_ok_def,ienv_val_ok_def,nsAll_def]>>
    res_tac>>
    fs[SUBMAP_t_compat]>>rw[]
    >- (fs[SUBSET_DEF]>>rw[]>>res_tac>>fs[])
    >>
    AP_TERM_TAC>>
    Q.ISPECL_THEN [`s`,`s'`,`st.next_uvar`,`subst'`,`num_tvs tenvE`] mp_tac t_walkstar_infer_db_subst>> fs[]>>
    impl_tac>-
      (fs[Abbr`targs'`,EL_MAP]>>rw[]>>
      match_mp_tac check_t_empty_unconvert_convert_id>>
      fs[EVERY_EL]>>res_tac>>fs[]>>
      Q.SPECL_THEN [`EL n'' subst'`,`num_tvs tenvE`,`s`] mp_tac (CONJUNCT1 check_t_walkstar)>>
      fs[]>>metis_tac[])>>
    metis_tac[])
  >- (*Fun*)
    (imp_res_tac check_freevars_to_check_t>>
    fs[sub_completion_def]>>
    imp_res_tac pure_add_constraints_success>>
    Q.SPECL_THEN [`t1`,`st`,`s`,`num_tvs tenvE`,`constraints`]
      mp_tac (GEN_ALL extend_one_props)>>
    impl_tac>>
    fs[LET_THM]>>
    qpat_abbrev_tac `constraints' = constraints ++A`>>
    qpat_abbrev_tac `s' = s|++B`>>
    strip_tac>>
    qmatch_goalsub_abbrev_tac`infer_e _ A _ B`>>
    first_x_assum(qspecl_then[`loc`, `s'`,`A`,`B`,`constraints'`] mp_tac)>>
    impl_tac>>fs[num_tvs_def,Abbr`A`,Abbr`B`]
    >-
      (fs[ienv_ok_def,ienv_val_ok_def]>>rw[]
      >-
        (fs[nsAll_def]>>Cases>>rw[]>>fs[nsLookup_nsBind]>>
        Cases_on`Short n' = Short n`>>fs[nsLookup_nsBind]>>
        rveq>>fs[check_t_def]>>res_tac>>
        pairarg_tac>>fs[check_t_more3])
      >-
        (fs[SUBSET_DEF]>>rw[]>>res_tac>>DECIDE_TAC)
      >>
        fs[env_rel_complete_def,lookup_var_def,lookup_varE_def]>>
        ntac 3 strip_tac>>
        first_x_assum(qspecl_then[`x`,`tvs`,`t'`] mp_tac)>>fs[]>>
        FULL_CASE_TAC>>fs[]
        >-
          (fs[tveLookup_def]>>IF_CASES_TAC
          >-
          (fs[deBruijn_inc0]>>rw[]>- metis_tac[check_t_to_check_freevars]>>
          fs[tscheme_approx_def,LENGTH_NIL,infer_deBruijn_subst_id]>>
          metis_tac[t_walkstar_no_vars])
          >>
          FULL_CASE_TAC>>fs[]>>rw[]>>fs[]>>
          match_mp_tac tscheme_approx_weakening>>
          first_assum (match_exists_tac o concl)>>fs[])
        >>
          rw[]>>fs[]>>
          match_mp_tac tscheme_approx_weakening>>
          first_assum (match_exists_tac o concl)>>fs[])
    >>
    strip_tac>>rw[success_eqns]>>
    HINT_EXISTS_TAC>>HINT_EXISTS_TAC>>
    fs[]>> CONJ_TAC
    >-
      (`t_compat s s'` by fs[SUBMAP_t_compat]>>
      metis_tac[t_compat_trans])
    >>
      `t_wfs st''.subst` by (imp_res_tac infer_e_wfs>>rfs[])>>
      `t_wfs s''` by
        metis_tac[pure_add_constraints_success]>>
     fs[t_compat_def]>>
     first_x_assum(qspec_then `Infer_Tuvar st.next_uvar` assume_tac)>>rfs[]>>
     fs[convert_t_def,Once t_walkstar_eqn,Once t_walk_eqn,SimpRHS]>>
     metis_tac[check_freevars_empty_convert_unconvert_id,t_walkstar_no_vars])
  >- (*App*)
    (first_x_assum(qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>rfs[ienv_ok_def]>>
    `MAP (convert_t o (t_walkstar s')) ts' = ts ∧
     EVERY (check_t (num_tvs tenvE) {}) (MAP (t_walkstar s') ts')` by
      (imp_res_tac infer_e_check_t>>
      CONJ_ASM2_TAC>>
      fs[MAP,MAP_MAP_o,MAP_EQ_f,EVERY_MEM,MEM_MAP]>>rw[]
      >>
      assume_tac (GEN_ALL check_t_less)>>
      first_x_assum(qspecl_then [`count st'.next_uvar`,`s'`,`num_tvs tenvE`] assume_tac)>>
      rfs[sub_completion_def]>>
      first_x_assum match_mp_tac>>fs[]>>
      metis_tac[infer_e_wfs,pure_add_constraints_wfs])>>
    Q.SPECL_THEN [`ts'`,`ts`,`t`,`st'`,`s'`,`op`,`loc`,`constraints'`,`num_tvs tenvE`] mp_tac
      (GEN_ALL constrain_op_complete)>>
    impl_keep_tac>- (fs[]>>metis_tac[infer_e_wfs])>>
    fs[]>>metis_tac[t_compat_trans])
  >- (*Log*)
   (last_x_assum(qspecl_then
      [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>rfs[]>>
    first_x_assum(qspecl_then
      [`loc`, `s'`,`ienv`,`st'`,`constraints'`] mp_tac)>>
    fs[ienv_ok_def]>>
    impl_keep_tac
    >-
      (imp_res_tac infer_e_next_uvar_mono>>fs[]>>reverse(rw[])
      >-
        (match_mp_tac env_rel_complete_t_compat>>
        fs[t_compat_def,SUBSET_DEF])
      >>
        metis_tac[ienv_val_ok_more,infer_e_wfs,sub_completion_wfs])
    >>
    rw[]>>simp[]>>
    qexists_tac `Infer_Tapp [] Tbool_num`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = [(t,Infer_Tapp [] X);(t'',B)]`>>
    Q.SPECL_THEN [`s''`,`ls`] mp_tac pure_add_constraints_ignore>>
    impl_keep_tac
    >-
      (fs[Abbr`ls`,sub_completion_def,t_compat_def]>>
      imp_res_tac infer_e_check_t>>CONJ_TAC
      >-
        (qpat_x_assum `Tapp [] TC_bool =A` (SUBST_ALL_TAC o SYM)>>
        qpat_x_assum`convert_t A =B` (assume_tac o (Q.AP_TERM `unconvert_t`))>>
        first_x_assum(qspec_then `t'` (SUBST1_TAC o SYM))>>
        fs[]>>rfs[]>>
        imp_res_tac sub_completion_completes>>
        imp_res_tac check_t_empty_unconvert_convert_id>>
        fs[unconvert_t_def])
      >>
        simp[Once t_walkstar_eqn,Once t_walk_eqn,SimpRHS]>>
        imp_res_tac sub_completion_completes>>
        qpat_x_assum `Tapp [] TC_bool = A`
          (assume_tac o (Q.AP_TERM `unconvert_t`))>>
        imp_res_tac check_t_empty_unconvert_convert_id>>
        fs[unconvert_t_def]>>metis_tac[])>>
   rw[]>>
   fs[sub_completion_def]>>
   pure_add_constraints_combine_tac [`st''`,`constraints''`,`s''`]>>
   imp_res_tac infer_e_wfs>>
   fs[pure_add_constraints_append]>>
   Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st''.next_uvar;next_id:=st''.next_id |>` >>fs[]>>
   Q.LIST_EXISTS_TAC [`si`,`constraints''`]>>fs[]>>
   Q.SPECL_THEN [`num_tvs tenvE`,`si`,`s''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
   rfs[]>>
   rw[]
   >-
     metis_tac[pure_add_constraints_success]
   >-
     metis_tac[t_compat_trans]
   >>
     AP_TERM_TAC>>
     fs[Abbr`ls`])
  >- (*If *)
    (last_x_assum (qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[ienv_ok_def]>>
    qpat_abbrev_tac `ls = [t',Infer_Tapp [] B]`>>
    pure_add_constraints_ignore_tac `s'`>-
      (fs[t_compat_def,sub_completion_def]>>
      imp_res_tac infer_e_check_t>>
      rfs[]>>
      imp_res_tac sub_completion_completes>>
      qpat_x_assum `A = convert_t B`
        (assume_tac o (Q.AP_TERM `unconvert_t`))>>
      fs[unconvert_t_def]>>
      metis_tac[t_walkstar_no_vars,check_t_empty_unconvert_convert_id])>>
    fs[sub_completion_def]>>
    pure_add_constraints_combine_tac [`st'`,`constraints'`,`s'`]>>
    imp_res_tac infer_e_wfs>>fs[]>>
    fs[pure_add_constraints_append]>>
    Q.SPECL_THEN [`num_tvs tenvE`,`si`,`s'`] assume_tac (GEN_ALL t_compat_bi_ground)>>
    rfs[Once PULL_EXISTS]>>
    CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
    qabbrev_tac `nst = <|next_uvar:=st'.next_uvar;subst:=s2';next_id:=st'.next_id|>`>>
    qexists_tac `nst`>>
    last_x_assum(qspecl_then [`loc`, `si`,`ienv`,`nst`,`constraints'`]
      mp_tac)>>
    impl_keep_tac>>fs[Abbr`nst`]
    >-
      (imp_res_tac infer_e_next_uvar_mono>>fs[]>>reverse (rw[])
      >-
        (match_mp_tac env_rel_complete_t_compat>>
        fs[EQ_SYM_EQ]>>
        fs[t_compat_def,SUBSET_DEF])
      >>
        metis_tac[pure_add_constraints_success,ienv_val_ok_more])
    >>
    rw[]>>fs[PULL_EXISTS]>>
    last_x_assum(qspecl_then [`loc`, `s'''`,`ienv`,`st'''`
                             ,`constraints'''`] mp_tac)>>
    impl_keep_tac
    >-
      (`st.next_uvar ≤ st'''.next_uvar` by
        (imp_res_tac infer_e_next_uvar_mono>>fs[]>>DECIDE_TAC)>>
      imp_res_tac infer_e_wfs>>
      imp_res_tac infer_e_next_uvar_mono>>
      fs[]>>rw[]
      >-
        metis_tac[ienv_val_ok_more]
      >>
      match_mp_tac env_rel_complete_t_compat>>fs[SUBSET_DEF]>>
      metis_tac[t_compat_trans,t_compat_def])
    >>
    rw[PULL_EXISTS]>>
    qunabbrev_tac`ls`>>
    qpat_abbrev_tac `ls = [(t'',t''')]`>>
    `check_t (num_tvs tenvE) {} (t_walkstar s''' t'') ∧
     t_walkstar s''' t'' = t_walkstar s'''' t'''` by
       (CONJ_ASM1_TAC>>
       imp_res_tac infer_e_check_t>>
       rfs[t_compat_def]>>
       fs[]>>imp_res_tac sub_completion_completes>>
       match_mp_tac (GEN_ALL convert_bi_remove)>>
       ntac 2 (qexists_tac `num_tvs tenvE`)>>
       fs[t_compat_def])>>
    `t_walkstar s'''' t'' = t_walkstar s'''' t'''` by
       metis_tac[t_compat_def,t_walkstar_no_vars]>>
    pure_add_constraints_ignore_tac `s''''`
    >-
      fs[t_compat_def]>>
   pure_add_constraints_combine_tac [`st''''`,`constraints''''`,`s''''`]>>
   `t_wfs s2'` by metis_tac[pure_add_constraints_wfs]>>
   imp_res_tac infer_e_wfs>>rfs[]>>fs[]>>
   fs[pure_add_constraints_append]>>
   CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
   Q.EXISTS_TAC`<|next_uvar:=st''''.next_uvar;subst:=s2''';next_id:=st''''.next_id|>`>>
   Q.LIST_EXISTS_TAC [`si'`,`constraints''''`]>>
   fs[]>>
   Q.SPECL_THEN [`num_tvs tenvE`,`si'`,`s''''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
   rfs[]>>rw[]
   >-
     metis_tac[pure_add_constraints_success]
   >-
     metis_tac[t_compat_trans]
   >>
   AP_TERM_TAC>>
   metis_tac[t_walkstar_no_vars,t_compat_def])
  >- (*Mat*)
    (last_x_assum (qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    fs[UNCURRY,sub_completion_def]>>
    (*This proof is too complicated, there's probably a simpler way*)
    `check_freevars (num_tvs tenvE) [] t'` by
      (Cases_on`pes`>>fs[RES_FORALL]>>
      Cases_on`h`>>
      last_x_assum(qspec_then`q,r` assume_tac)>>
      fs[]>>
      qabbrev_tac `t1 = convert_t(t_walkstar s' t'')`>>
      Q.SPECL_THEN [`num_tvs tenvE`,`tenv`,`q`,`t1`,`bindings`] assume_tac
        (fst (CONJ_PAIR infer_p_complete))>>rfs[]>>
      pop_assum(qspecl_then [`loc`, `s'`,`ienv`,`st'`,`constraints'`] mp_tac)>>
      impl_keep_tac
      >-
        (fs[sub_completion_def,env_rel_complete_def,ienv_ok_def]>>
        metis_tac[infer_e_wfs])
      >>
      rw[]>>
      fs[sub_completion_def,env_rel_complete_def,ienv_ok_def]>>
      qabbrev_tac `ntenv = nsAppend (alist_to_ns (MAP (λ(n,t). (n,0,t)) new_bindings)) ienv.inf_v`>>
      first_x_assum(qspecl_then
        [`loc`, `s''`,`ienv with inf_v := ntenv`,`st''`,`constraints''`] mp_tac)>>
      impl_keep_tac>-
        (fs[Abbr`ntenv`]>>CONJ_TAC
        >-
          (fs[ienv_val_ok_def]>>
          match_mp_tac nsAll_nsAppend>>
          fs[nsAll_def,nsLookup_alist_to_ns_some,FORALL_PROD]>>rw[]
          >-
            (fs[ALOOKUP_MAP] >> imp_res_tac ALOOKUP_MEM>>
            imp_res_tac infer_p_check_t>>
            fs[EVERY_MEM]>>
            first_x_assum(qspec_then `(x',p_2)` assume_tac)>>
            rfs[])
          >>
            first_x_assum(qspecl_then[`x`,`p_1`,`p_2`] assume_tac)>>rfs[]>>
            `st.next_uvar ≤ st''.next_uvar` by
              (imp_res_tac infer_e_next_uvar_mono>>
              imp_res_tac infer_p_next_uvar_mono>>fs[])>>
            metis_tac[check_t_more4])>>
        CONJ_TAC>-
          metis_tac[infer_e_wfs,infer_p_wfs]>>
        ntac 4 strip_tac>>
        fs[simp_tenv_invC_def,lookup_var_bind_var_list,alist_to_ns_def,nsLookup_nsAppend_some]>>
       Cases_on`x`>>fs[nsLookup_def]
       >-
         (pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac
         >-
           (fs[ALOOKUP_MAP]>>
           Cases_on`ALOOKUP new_bindings n`
           >-
             (first_x_assum(qspecl_then [`Short n`,`tvs`,`t`] assume_tac)>>
             rfs[]>>fs[id_to_mods_def]>>rw[]>-metis_tac[]>>
             match_mp_tac (GEN_ALL tscheme_approx_weakening2)>>fs[]>>
             qexists_tac`s`>>
             imp_res_tac infer_e_next_uvar_mono>>
             imp_res_tac infer_p_next_uvar_mono>>
             fs[SUBSET_DEF,EQ_SYM_EQ]>>
             metis_tac[t_compat_trans])
           >>
           metis_tac[option_CLAUSES])
         >>
           first_x_assum(qspecl_then[`n`,`t`] assume_tac)>>rfs[]>>
           rw[]>-metis_tac[]>>
           fs[ALOOKUP_MAP]>>
           simp[tscheme_approx_def,LENGTH_NIL,infer_deBruijn_subst_id]>>
           metis_tac[t_walkstar_idempotent,t_compat_def])
       >>
       first_x_assum(qspecl_then [`Long m i`,`tvs`,`t`] assume_tac)>>rfs[]>>
       rw[]>- metis_tac[]
       >-
         (fs[id_to_mods_def]>>Cases_on`p1`>>fs[nsLookupMod_def])
       >>
         match_mp_tac (GEN_ALL tscheme_approx_weakening2)>>fs[]>>
         qexists_tac`s`>>
         imp_res_tac infer_e_next_uvar_mono>>
         imp_res_tac infer_p_next_uvar_mono>>
         fs[SUBSET_DEF,EQ_SYM_EQ]>>
         metis_tac[t_compat_trans])>>
      rw[]>>fs[]>>
      imp_res_tac infer_e_check_t>>
      imp_res_tac sub_completion_completes>>
      fs[t_compat_def,num_tvs_bind_var_list]>>rfs[]>>
      metis_tac[check_t_to_check_freevars])>>
   Q.SPECL_THEN [`t'`,`st'`,`s'`,`num_tvs tenvE`,`constraints'`] mp_tac (GEN_ALL extend_one_props)>>
   impl_tac >- metis_tac[infer_e_wfs,pure_add_constraints_wfs] >>
   qpat_abbrev_tac `s'' = s'|++A`>>
   Q.ABBREV_TAC `constraints'' = constraints'++[Infer_Tuvar st'.next_uvar,unconvert_t t']`>>
   rfs[LET_THM]>>
   imp_res_tac pure_add_constraints_success>>
   rw[]>>
   qpat_abbrev_tac `st'' = st' with next_uvar := A`>>
   `sub_completion (num_tvs tenvE) st''.next_uvar st''.subst constraints'' s''` by fs[sub_completion_def,Abbr`st''`]>>
    assume_tac (GEN_ALL infer_pes_complete)>>
    pop_assum (qspecl_then
      [`st.next_uvar`,`tenvE`,`tenv`,`Infer_Tuvar
      st'.next_uvar`,`t'`,`t''`,`convert_t(t_walkstar s' t'')`,`loc`,`ienv`,`pes`,`st''`,`constraints''`,`s''`] mp_tac)>>
    impl_tac
    >- (fs[Abbr`st''`,sub_completion_def]>>
       imp_res_tac infer_e_next_uvar_mono>>fs[]>>
       CONJ_ASM1_TAC>-metis_tac[infer_e_wfs]>>
       fs[]>>rw[]
       >-
         (fs[env_rel_complete_def]>>ntac 4 strip_tac>>
         res_tac>>fs[]>>rw[]
         >-
           metis_tac[]
         >>
         match_mp_tac tscheme_approx_weakening2>>fs[SUBSET_DEF]>>
         metis_tac[t_compat_trans,SUBMAP_t_compat])
       >- (`count (st'.next_uvar) ⊆ count(st'.next_uvar+1)` by
             (fs[SUBSET_DEF,count_def]>>DECIDE_TAC)>>
           metis_tac[SUBSET_TRANS])
       >- (imp_res_tac infer_e_check_t>>
          rfs[ienv_ok_def]>>
          imp_res_tac sub_completion_completes>>
          metis_tac[check_t_empty_unconvert_convert_id,submap_t_walkstar_replace]))
    >- (rw[]>>
        HINT_EXISTS_TAC>>fs[sub_completion_def]>>
        Q.LIST_EXISTS_TAC [`s'''`,`constraints'''`]>>fs[]>>
        CONJ_TAC>-metis_tac[t_compat_trans,SUBMAP_t_compat]>>
        fs[t_compat_def]>>
        pop_assum(qspec_then `Infer_Tuvar st'.next_uvar` assume_tac)>>rfs[]>>
        metis_tac[t_walkstar_no_vars,check_freevars_empty_convert_unconvert_id,check_freevars_to_check_t]))
  >- (*Let*)
    (last_x_assum(qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    Cases_on `n`>>fs[nsOptBind_def]
    >-
      (first_x_assum(qspecl_then [`loc`, `s'`,`ienv`,`st'`,`constraints'`] mp_tac)>>
      rfs[ienv_ok_def,opt_bind_name_def]>>
      impl_keep_tac>-
        (imp_res_tac infer_e_next_uvar_mono>> reverse(rw[])
        >-
          (match_mp_tac env_rel_complete_t_compat>>fs[SUBSET_DEF,t_compat_def])
        >>
          metis_tac[ienv_val_ok_more,infer_e_wfs])
      >>
      rw[]>>
      metis_tac[t_compat_trans])
    >>
      qmatch_goalsub_abbrev_tac`infer_e _ A _ _`>>
      first_x_assum(qspecl_then[`loc`, `s'`,`A`,`st'`,`constraints'`] mp_tac)>>
      impl_keep_tac>>fs[opt_bind_name_def,num_tvs_def,Abbr`A`]
      >-
        (imp_res_tac infer_e_check_t>>rfs[ienv_ok_def]>>
        imp_res_tac infer_e_next_uvar_mono>>
        fs[ienv_val_ok_def,nsAll_def,FORALL_PROD]>>rw[]
        >-
          (Cases_on`x'`>>fs[nsLookup_nsBind]>>
          Cases_on`Short n = Short x`>>fs[nsLookup_nsBind]>>
          rveq>>fs[]>>
          metis_tac[check_t_more4])
        >-
          metis_tac[infer_e_wfs]
        >-
          (fs[env_rel_complete_def,lookup_var_def,lookup_varE_def]>>
          ntac 3 strip_tac>>
          first_x_assum(qspecl_then[`x'`,`tvs`,`t`] mp_tac)>>fs[]>>
          FULL_CASE_TAC>>fs[]
          >-
            (fs[tveLookup_def]>>IF_CASES_TAC
            >-
            (fs[deBruijn_inc0]>>
            assume_tac (GEN_ALL check_t_less)>>
            pop_assum (Q.SPECL_THEN [`count st'.next_uvar`,`s'`,`num_tvs tenvE`]assume_tac)>>
            fs[sub_completion_def,t_compat_def]>>
            res_tac>>
            `check_t (num_tvs tenvE) {} (t_walkstar s' t'')` by
              metis_tac[COMPL_INTER]>>
            rw[]
            >-
              metis_tac[check_t_to_check_freevars]>>
            fs[tscheme_approx_def,LENGTH_NIL,infer_deBruijn_subst_id]>>
            metis_tac[check_t_empty_unconvert_convert_id,t_walkstar_idempotent])
            >>
            FULL_CASE_TAC>>rw[]>>fs[]>>
            match_mp_tac tscheme_approx_weakening2>>fs[SUBSET_DEF])
          >>
            rw[]>>fs[]>>
            match_mp_tac tscheme_approx_weakening2>>fs[SUBSET_DEF]))
      >>
        rw[]>>simp[]>>
        ntac 2 HINT_EXISTS_TAC>>fs[]>>metis_tac[t_compat_trans])
  >-
    (*Letrec*)
    (imp_res_tac type_funs_MAP_FST>>
    imp_res_tac type_funs_distinct>>
    `MAP (λx,y,z. x) funs = MAP FST funs` by
      fs[MAP_EQ_f,FORALL_PROD]>>
    fs[bind_var_list_def]>>
    qpat_abbrev_tac `new_tenv = nsAppend A ienv.inf_v`>>
    fs[sub_completion_def] >>
    qabbrev_tac `fun_tys = MAP SND env` >>
    Q.SPECL_THEN [`st`,`constraints`,`s`,`fun_tys`,`num_tvs tenvE`]
      mp_tac extend_multi_props>>
    impl_keep_tac
    >-
      (fs[]>>rw[]
      >- metis_tac[pure_add_constraints_wfs]
      >>
        imp_res_tac type_funs_lookup>>
        imp_res_tac type_funs_Tfn>>
        fs[num_tvs_bind_var_list,EVERY_MEM]>>
        rw[Abbr`fun_tys`,MEM_MAP]>>
        Cases_on`y`>>
        `MEM q (MAP FST env)` by
          (fs[MEM_MAP]>>
          Q.EXISTS_TAC`q,r`>>fs[])>>
        `MEM q (MAP FST funs)` by fs[]>>
        fs[MEM_MAP]>>
        PairCases_on`y'`>>
        first_x_assum(qspecl_then[`y'1`,`y'0`,`y'2`] assume_tac)>>rfs[]>>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM>>
        metis_tac[])
    >>
    LET_ELIM_TAC>>
    qpat_abbrev_tac `st' = st with next_uvar:=A`>>
    last_x_assum(qspecl_then [`loc`, `s'`,`ienv with inf_v :=new_tenv`,`st'`
                             ,`constraints++new_constraints`] mp_tac)>>
    impl_keep_tac>-
      (fs[Abbr`st'`,num_tvs_bind_var_list]>>
      `LENGTH env = LENGTH funs` by metis_tac[LENGTH_MAP]>>
      rw[Abbr`fun_tys`]
      >-
        (fs[ienv_ok_def,ienv_val_ok_def,Abbr`new_tenv`]>>
        match_mp_tac nsAll_nsAppend>>reverse (rw[])
        >-
          (fs[nsAll_def,FORALL_PROD]>>
          metis_tac[check_t_more3,ADD_SYM])
        >>
        fs[nsAll_def,nsLookup_alist_to_ns_some,MAP2_MAP,LENGTH_COUNT_LIST]>>
        rw[]>>
        Cases_on`v`>>
        imp_res_tac ALOOKUP_MEM>>fs[MEM_MAP]>>
        PairCases_on`y`>>fs[MEM_ZIP,LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST,check_t_def])
      >-
        (fs[SUBSET_DEF]>>
        rw[]>>
        last_x_assum(qspec_then`x` mp_tac)>>fs[])
      >>
        fs[env_rel_complete_def]>>ntac 4 strip_tac>>
        fs[Abbr`new_tenv`,lookup_var_bind_var_list,alist_to_ns_def,nsLookup_nsAppend_some]>>
       Cases_on`x`>>fs[nsLookup_def]
       >-
         (pop_assum mp_tac>>TOP_CASE_TAC
         >-
           (strip_tac>>
           qmatch_goalsub_abbrev_tac `ALOOKUP ls n = _`>>
           `ALOOKUP ls n = NONE` by
             (fs[Abbr`ls`,MAP2_MAP,LENGTH_COUNT_LIST,ALOOKUP_NONE,MEM_MAP,FORALL_PROD,MEM_ZIP]>>rw[]>>
             CCONTR_TAC>>fs[]>>
             `MEM n (MAP FST funs)` by
               (fs[MEM_MAP,MEM_EL]>>
               metis_tac[FST])>>
             metis_tac[FST,PAIR,MEM_MAP])>>
           first_x_assum(qspecl_then [`Short n`,`tvs`,`t'`] assume_tac)>>
           rfs[id_to_mods_def]>>rw[]
           >-
             metis_tac[]
           >>
             match_mp_tac (GEN_ALL tscheme_approx_weakening2)>>fs[]>>
             HINT_EXISTS_TAC>>fs[SUBSET_DEF]>>
             metis_tac[SUBMAP_t_compat])
         >>
           imp_res_tac ALOOKUP_MEM>>rw[]
           >-
             (fs[EVERY_MAP,EVERY_MEM,FORALL_PROD]>>
             metis_tac[])
           >>
             fs[MEM_EL]>>
             qmatch_goalsub_abbrev_tac `ALOOKUP ls n = _`>>
             `ALOOKUP ls n = SOME(0,Infer_Tuvar(n'+st.next_uvar))` by
               (`MAP FST ls = MAP FST funs` by
                   (fs[Abbr`ls`,MAP2_MAP,LENGTH_COUNT_LIST]>>
                   match_mp_tac LIST_EQ>>
                   fs[LENGTH_ZIP,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP]>>rw[]>>
                   pairarg_tac>>fs[]>>
                   `FST (EL x env) = FST (EL x funs)` by
                     fs[LIST_EQ_REWRITE,EL_MAP]>>
                   fs[])>>
               match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
               rw[]
               >-
                 metis_tac[]
               >>
                 fs[Abbr`ls`,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,EXISTS_PROD]>>
                 fs[MEM_ZIP,LENGTH_COUNT_LIST]>>
                 `FST (EL n' funs) = n` by
                   (fs[LIST_EQ_REWRITE,EL_MAP]>>
                   metis_tac[FST])>>
                 Cases_on`EL n' funs`>>Cases_on`r`>>fs[]>>
                 qexists_tac`q'`>>qexists_tac`r'`>>qexists_tac`n'`>>
                 fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST])>>
             fs[tscheme_approx_def,LENGTH_NIL,infer_deBruijn_subst_id,Abbr`targs`,EL_MAP]>>
             `t' = SND (EL n' env)` by metis_tac[SND]>>
             fs[]>>match_mp_tac t_walkstar_no_vars>>
             fs[EVERY_EL,EL_MAP]>>
             metis_tac[check_freevars_to_check_t])
       >>
         first_x_assum(qspecl_then [`Long m i`,`tvs`,`t'`] assume_tac)>>
         rfs[]>>
         rw[]>- metis_tac[]
         >-
           (fs[id_to_mods_def]>>Cases_on`p1`>>fs[nsLookupMod_def])
         >>
           match_mp_tac (GEN_ALL tscheme_approx_weakening2)>>fs[]>>
           HINT_EXISTS_TAC>>fs[SUBSET_DEF]>>
           metis_tac[SUBMAP_t_compat])
    >>
    fs[ienv_ok_def]>>
    qunabbrev_tac `fun_tys`>>
    rw[]>>
    fs[PULL_EXISTS]>>
    qpat_abbrev_tac `ls=ZIP(MAP (λn.Infer_Tuvar(n+st.next_uvar))A,env')`>>
    imp_res_tac infer_funs_length>>
    fs[LENGTH_COUNT_LIST]>>
    pure_add_constraints_ignore_tac `s''`>-
      (fs[t_compat_def,EVERY_MEM,LENGTH_COUNT_LIST,MEM_ZIP]>>rw[]>>
      fs[LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST]>>
      `LENGTH funs = LENGTH env` by
        (qpat_x_assum `MAP FST funs = B` (assume_tac o Q.AP_TERM`LENGTH`)>>
        fs[LENGTH_MAP])>>
     imp_res_tac infer_e_check_t>>
     first_x_assum(qspec_then `Infer_Tuvar (n+st.next_uvar)` (SUBST_ALL_TAC o SYM))>>
      last_x_assum(qspec_then `n` assume_tac)>>
      fs[]>>rfs[]>>
      qunabbrev_tac`targs`>>
      simp[EL_MAP,LENGTH_MAP]>>
      fs[EVERY_EL]>>
      first_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
      fs[num_tvs_bind_var_list]>>
      imp_res_tac sub_completion_completes>>
      imp_res_tac check_t_empty_unconvert_convert_id>>
      simp[]>>
      simp[t_walkstar_idempotent])>>
    pure_add_constraints_combine_tac [`st''`,`constraints''`,`s''`]>>
    pop_assum mp_tac >>impl_keep_tac>-
      metis_tac[infer_e_wfs]>>
    rw[]>>
    Q.SPECL_THEN [`num_tvs tenvE`,`si`,`s''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
    rfs[num_tvs_bind_var_list]>>
    fs[pure_add_constraints_append]>>
    CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
    qabbrev_tac`nst = <|next_uvar:=st''.next_uvar;subst:=s2''';next_id:=st''.next_id|>`>>
    qexists_tac`nst`>>
    first_x_assum(qspecl_then [`loc`, `si`,`ienv with inf_v := new_tenv`
                              ,`nst`,`constraints''`] mp_tac)>>
    impl_tac>-
      (imp_res_tac infer_e_next_uvar_mono>>
      fs[Abbr`st'`,Abbr`nst`]>>rw[]
      >-
        (match_mp_tac (GEN_ALL (CONJUNCT1 ienv_val_ok_more))>>
        HINT_EXISTS_TAC>>
        fs[SUBSET_DEF,EQ_SYM_EQ])
      >-
        metis_tac[pure_add_constraints_success]
      >-
        metis_tac[pure_add_constraints_success]
      >-
        (fs[env_rel_complete_def]>>rw[]>-metis_tac[]>>
        first_x_assum drule>>rw[]>>
        simp[]>>
        match_mp_tac (GEN_ALL tscheme_approx_weakening2)>>
        HINT_EXISTS_TAC>>fs[EQ_SYM_EQ,SUBSET_DEF]>>
        metis_tac[t_compat_trans]))>>
    rw[]>>
    Q.LIST_EXISTS_TAC [`constraints'''`,`s'''`,`st'''`,`t'`]>>
    fs[Abbr`nst`]>>
    metis_tac[t_compat_trans,SUBMAP_t_compat])
  >- (* Tannot *)
    (
    `ienv.inf_t = tenv.t` by fs [env_rel_complete_def] >>
    simp [type_name_check_subst_comp_thm] >>
    first_x_assum(qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    qmatch_goalsub_abbrev_tac`pure_add_constraints _ ls _`>>
    drule (CONJUNCT1 infer_e_wfs) >>
    rw [] >>
    `pure_add_constraints s' ls s'` by
      (match_mp_tac pure_add_constraints_ignore>>
      fs[Abbr`ls`]>>
      CONJ_ASM1_TAC
      >-
        metis_tac[sub_completion_wfs]
      >>
      fs[sub_completion_def,ienv_ok_def,env_rel_complete_def]>>
      imp_res_tac infer_e_check_t>>
      imp_res_tac(CONJUNCT1 check_t_less)>>
      rfs[]>>
      imp_res_tac check_t_to_check_freevars>>
      metis_tac[infer_type_subst_nil,check_t_empty_unconvert_convert_id,t_walkstar_idempotent])>>
    `pure_add_constraints st'.subst (constraints'++ls) s'` by
      metis_tac[pure_add_constraints_append,sub_completion_def]>>
    imp_res_tac pure_add_constraints_swap>>
    fs[pure_add_constraints_append,Abbr`ls`,pure_add_constraints_def,sub_completion_def]>>
    map_every qexists_tac [`<| subst := s2''; next_uvar := st'.next_uvar; next_id :=st'.next_id |>`, `si'`,`constraints'`]>>fs[]>>
    drule (GEN_ALL t_compat_bi_ground)>>
    disch_then(qspec_then`si'` assume_tac)>>rfs[]>>
    fs[simp_tenv_invC_def,env_rel_complete_def]>>
    metis_tac[t_compat_trans,t_unify_wfs,pure_add_constraints_success])
  >- metis_tac []
  >-
    (ntac 2 HINT_EXISTS_TAC>>fs[]>>metis_tac[sub_completion_wfs,t_compat_refl])
  >-
    (last_x_assum(qspecl_then [`loc`, `s`,`ienv`,`st`,`constraints`] assume_tac)>>
    rfs[ienv_ok_def]>>
    last_x_assum(qspecl_then [`loc`, `s'`,`ienv`,`st'`,`constraints'`] mp_tac)>>
    impl_tac>>fs[]
    >-
      (imp_res_tac infer_e_next_uvar_mono >> reverse (rw[])
      >-
        (match_mp_tac env_rel_complete_t_compat>>fs[t_compat_def,SUBSET_DEF])
      >>
        metis_tac[infer_e_wfs,ienv_val_ok_more])
    >>
    rw[]>>
    fs[PULL_EXISTS]>>
    ntac 2 HINT_EXISTS_TAC>>fs[]>>
    CONJ_TAC>- metis_tac[t_compat_trans]>>
    imp_res_tac infer_e_check_t>>
    fs[sub_completion_def]>>
    rfs[]>>
    AP_TERM_TAC>>
    imp_res_tac sub_completion_completes>>
    fs[t_compat_def]>>metis_tac[t_walkstar_no_vars])
  >-
    (ntac 2 HINT_EXISTS_TAC >>fs[]>>metis_tac[sub_completion_wfs,t_compat_refl])
  >- (
    fs[check_freevars_def]>>
    fs[sub_completion_def]>>
    imp_res_tac pure_add_constraints_success>>
    Q.SPECL_THEN [`t1`,`st`,`s`,`num_tvs tenvE`,`constraints`] mp_tac (GEN_ALL extend_one_props)>>
    impl_tac>>
    fs[LET_THM]>>
    qpat_abbrev_tac `constraints' = constraints ++A`>>
    qpat_abbrev_tac `s' = s|++B`>>
    strip_tac>>
    qmatch_goalsub_abbrev_tac`infer_e _ A _ B`>>
    last_x_assum(qspecl_then[`loc`, `s'`,`A`,`B`,`constraints'`] mp_tac)>>
    impl_keep_tac>>fs[num_tvs_def,Abbr`A`,Abbr`B`]
    >-
      (rw[]
      >-
        (fs[ienv_ok_def,ienv_val_ok_def,nsAll_def,FORALL_PROD]>>
        Cases>>fs[nsLookup_nsBind]
        >-
          (Cases_on`Short n = Short n'`>>fs[nsLookup_nsBind,check_t_def]>>
          metis_tac[check_t_more3])
        >>
          metis_tac[check_t_more3])
      >-
        (fs[count_def,SUBSET_DEF]>>rw[]>>
        `x < st.next_uvar` by metis_tac[]>>
        DECIDE_TAC)
      >>
        fs[env_rel_complete_def,lookup_var_def,lookup_varE_def]>>
        ntac 3 strip_tac>>
        first_x_assum(qspecl_then[`x`,`tvs`,`t'`] mp_tac)>>fs[]>>
        FULL_CASE_TAC>>fs[]
        >-
          (fs[tveLookup_def]>>IF_CASES_TAC
          >-
          (fs[deBruijn_inc0]>>rw[]>-
            metis_tac[check_t_to_check_freevars]>>
          fs[tscheme_approx_def,LENGTH_NIL,infer_deBruijn_subst_id]>>
          `st.next_uvar ∈ FDOM s'` by fs[]>>
          metis_tac[t_walkstar_no_vars])
          >>
          FULL_CASE_TAC>>fs[]>>
          rw[]>>fs[]>>
          match_mp_tac tscheme_approx_weakening>>
          first_assum (match_exists_tac o concl)>>fs[])
        >>
          rw[]>>fs[]>>
          match_mp_tac tscheme_approx_weakening>>
          first_assum (match_exists_tac o concl)>>fs[])>>
    rw[]>>
    fs[PULL_EXISTS]>>
    first_x_assum(qspecl_then[`loc`, `s''`,`ienv with inf_v:= ienv.inf_v`,`st''`,`constraints''`] mp_tac)>>
    impl_keep_tac>> fs[]
    >-
      (imp_res_tac infer_e_next_uvar_mono>>fs[]>>
      rw[]
      >- (`st.next_uvar ≤ st''.next_uvar` by fs[]>>
         metis_tac[ienv_ok_more])
      >- metis_tac[infer_e_wfs,infer_st_rewrs]
      >>
        match_mp_tac env_rel_complete_t_compat>>fs[SUBSET_DEF]>>
        metis_tac[SUBMAP_t_compat,t_compat_trans,t_compat_def])
    >>
    rw[]>>
    `ienv with inf_v := ienv.inf_v = ienv` by fs[]>>
    fs[]>>
    ntac 2 HINT_EXISTS_TAC>>fs[]>>
    CONJ_ASM1_TAC>-metis_tac[SUBMAP_t_compat,t_compat_trans]>>
    fs[t_compat_def]>>
    simp[Once t_walkstar_eqn,convert_t_def,SimpRHS,Once t_walk_eqn]>>
    CONJ_TAC
    >-
      (ntac 2 (last_x_assum(qspec_then `st.next_uvar` assume_tac))>>
      rfs[]>>
      metis_tac[t_walkstar_no_vars,check_freevars_empty_convert_unconvert_id])
    >>
      fs[ienv_ok_def]>>
      imp_res_tac infer_e_check_t>>
      rfs[]>>
      imp_res_tac sub_completion_completes>>
      AP_TERM_TAC>>metis_tac[t_walkstar_no_vars])
QED
