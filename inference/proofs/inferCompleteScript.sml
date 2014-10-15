open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;
open miscLib

val _ = new_theory "inferComplete";

(* Move to unification theory *)

val unify_fresh_uvar = Q.store_thm ("unify_fresh_uvar",
`!s uv t.
  t_wfs s ∧
  uv ∉ FDOM s
  ⇒
  (t_walk s t ≠ Infer_Tuvar uv ⇒ t_unify s (Infer_Tuvar uv) t = SOME (s |+ (uv, t_walk s t))) ∧
  (t_walk s t = Infer_Tuvar uv ⇒ t_unify s (Infer_Tuvar uv) t = SOME s)`,
 rw [t_unify_eqn, t_walk_eqn] >>
 `t_vwalk s uv = Infer_Tuvar uv` by rw [Once t_vwalk_eqn, FLOOKUP_DEF] >>
 rw [] >>
 Cases_on `t_walk s t` >>
 rw [t_ext_s_check_eqn, oc_tvar_db] >>
 cheat);

(* End unification stuff *)

(*Some of these might need to go into a props script*)

(*Useful lemmas about pure add constraints, some of these imply the others*)
val pure_add_constraints_success = prove(
``
!s constraints s'.
t_wfs s ∧ 
pure_add_constraints s constraints s'
⇒
s SUBMAP s' ∧
FDOM s ⊆ FDOM s' ∧ 
t_compat s s' ∧ 
t_wfs s'``,
  ho_match_mp_tac pure_add_constraints_ind>>
  fs[pure_add_constraints_def,t_compat_refl]>>
  ntac 7 strip_tac>>
  imp_res_tac t_unify_unifier>>
  res_tac>>fs[]>>CONJ_ASM1_TAC>>
  metis_tac[SUBMAP_DEF,SUBSET_DEF,SUBMAP_t_compat,SUBMAP_TRANS])

(*t_compat is preserved over certain types of pure_add_constraints*)
val t_compat_pure_add_constraints_1 = prove(
``!ls s sx. 
  t_compat s sx ∧ EVERY (\x,y. t_walkstar sx x = t_walkstar sx y) ls
  ⇒ 
  ?si. pure_add_constraints s ls si ∧ t_compat si sx``,
  Induct>>fs[pure_add_constraints_def]>>rw[]>>
  Cases_on`h`>>fs[]>>
  simp[pure_add_constraints_def]>>
  imp_res_tac t_compat_eqs_t_unify>>
  fs[])

(*If pure add constraints succeeds then the constraints all unify*)
val t_compat_pure_add_constraints_2 = prove(
``!ls s sx.
  t_wfs s ∧ 
  pure_add_constraints s ls sx
  ⇒ 
  EVERY (\x,y. t_walkstar sx x = t_walkstar sx y) ls``,
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
    metis_tac[t_unify_wfs])

(*behaves like a function if the first 2 arguments are equal*)
val pure_add_constraints_functional = prove(
`` !constraints s s' s''.
   t_wfs s ∧ 
   pure_add_constraints s constraints s' ∧
   pure_add_constraints s constraints s'' ⇒ s' = s''``,
   Induct>>
   rw[]>>
   fs[pure_add_constraints_def]>>
   Cases_on`h`>>
   fs[pure_add_constraints_def]>>
   fs[t_unify_eqn]>>
   imp_res_tac t_unify_wfs>>
   metis_tac[])

(*1 direction is sufficient to imply the other*)
val pure_add_constraints_swap_lemma = prove(
``t_wfs s ∧ 
  pure_add_constraints s (a++b) sx 
  ⇒
  ?si. pure_add_constraints s (b++a) si ∧
       t_compat si sx ``,
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
  HINT_EXISTS_TAC>>fs[])

val pure_add_constraints_swap = prove(
``t_wfs s ∧ 
  pure_add_constraints s (a++b) sx
  ⇒ 
  ?si. pure_add_constraints s (b++a) si ∧ 
       t_compat si sx ∧ 
       t_compat sx si``,
  rw[]>>
  assume_tac pure_add_constraints_swap_lemma>>rfs[]>>
  HINT_EXISTS_TAC>>fs[]>>
  imp_res_tac pure_add_constraints_swap_lemma>>
  imp_res_tac pure_add_constraints_functional>>
  fs[t_compat_trans])

val pure_add_constraints_swap = GEN_ALL pure_add_constraints_swap

(*End pure_add_constraints stuff*)

val unconvert_t_def = tDefine "unconvert_t" `
(unconvert_t (Tvar_db n) = Infer_Tvar_db n) ∧
(unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc)`
(wf_rel_tac `measure t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [t_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val tenv_inv_def = Define `
tenv_inv s tenv tenvE =
  (!x tvs t.
    lookup_tenv x 0 tenvE = SOME (tvs, t)
    ⇒
    (*tvs >0 ⇒ check_freevars (num_tvs tenvE) [] t ∧ *)
    (if tvs > 0 then check_freevars tvs [] t
                else ?n.check_freevars n [] t) ∧
    ?t'.
    unconvert_t t = t_walkstar s t' ∧ 
    (tvs > 0 ⇒ t_walkstar s t' = t') ∧
    (*
    (!targs. LENGTH targs ≤ tvs
    ⇒ 
    infer_deBruijn_subst targs (unconvert_t t) = 
    infer_deBruijn_subst targs (t_walkstar s t')) ∧ *)

    ALOOKUP tenv x = SOME (tvs,t'))`;

val extend_t_vR_WF = prove
(``(check_t lim {} (n) ∧
   WF (t_vR s) )⇒
   WF (t_vR (s |+ (uvar,n)))``,
  fs[WF_DEF]>>rw[]>>
  first_x_assum(qspec_then `B` assume_tac)>>fs[]>>
  Cases_on `?w. B w`>> fs[]>>
  Q.EXISTS_TAC `min` >>
  fs[t_vR_eqn,FLOOKUP_UPDATE]>>
  IF_CASES_TAC>>rw[]>>
  imp_res_tac check_t_t_vars>>
  fs[FLOOKUP_DEF])

val not_t_oc = prove(
``(!t s v lim. t_wfs s ∧ check_t lim {} t ⇒ ¬ t_oc s t v) ∧
  (!ts s t v lim. t_wfs s ∧ EVERY (check_t lim {}) ts ⇒ ~ EXISTS (\t. t_oc s t v) ts)``,
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def]>>
  TRY (res_tac>>metis_tac[])>>
  SPOSE_NOT_THEN assume_tac>>
  Q.ISPEC_THEN `s` assume_tac t_oc_eqn>>
  rfs[]>> res_tac>>
  fs[t_walk_eqn]>>
  fs[EVERY_MEM,EXISTS_MEM]>>
  res_tac)

val FDOM_extend = prove (
`` FDOM s = count next_uvar ⇒
   FDOM (s |+ (next_uvar, n)) = count (SUC next_uvar)``,
   fs[FDOM_FUPDATE,count_def,INSERT_DEF,SET_EQ_SUBSET,SUBSET_DEF]>>
   rw[]>- DECIDE_TAC>-
   (res_tac>>DECIDE_TAC)>>
   Cases_on`x=next_uvar`>>fs[]>>
   `x<next_uvar` by DECIDE_TAC>>fs[])

val check_freevars_empty_convert_unconvert_id = prove(
``!t. check_freevars n [] t ⇒ 
  convert_t (unconvert_t t) = t``,
  ho_match_mp_tac (fetch "-" "unconvert_t_ind")>>
  rw[]>>fs[unconvert_t_def,convert_t_def,check_freevars_def]>>
  fs[MAP_MAP_o,MAP_EQ_ID,EVERY_MEM])

val check_t_empty_unconvert_convert_id = prove(
``!t. check_t n {} t ⇒
  unconvert_t (convert_t t) = t``,
  ho_match_mp_tac convert_t_ind>>rw[]>>
  fs[unconvert_t_def,convert_t_def,check_t_def]>>
  fs[MAP_MAP_o,MAP_EQ_ID,EVERY_MEM])

val check_freevars_to_check_t = prove(
``!t z. check_freevars n [] t ⇒
  check_t n {} (unconvert_t t)``,
  ho_match_mp_tac (fetch "-" "unconvert_t_ind")>>
  rw[]>>
  fs[unconvert_t_def,check_freevars_def,check_t_def]>>
  fs[EVERY_MAP,EVERY_MEM])

val pure_add_constraints_exists = Q.prove (
`!s ts next_uvar lim.
  t_wfs s ∧
  FDOM s = count next_uvar ∧
  EVERY (check_freevars lim []) ts
  ⇒
  let tys = MAP ( λn. (next_uvar+n)) (COUNT_LIST (LENGTH ts)) in
  let targs = MAP unconvert_t ts in
  let constraints = ZIP ((MAP Infer_Tuvar tys),targs) in
  let extension = ZIP (tys,targs) in
  pure_add_constraints s constraints (s|++extension)`,
  induct_on`ts`>>
  rw[] >>unabbrev_all_tac>>
  rw [COUNT_LIST_def, pure_add_constraints_def]>-rw[FUPDATE_LIST]>>
  fs[LET_THM,MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = (SUC x) + y``] >>
  fs[t_unify_eqn]>>
  fs[t_walk_eqn,Once t_vwalk_eqn] >>
  `FLOOKUP s next_uvar = NONE ` by 
    (fs[FLOOKUP_DEF,count_def,SUBSET_DEF]>>
    first_x_assum (qspec_then `next_uvar` mp_tac)>>DECIDE_TAC)>>
  fs[t_ext_s_check_eqn]>>
  imp_res_tac check_freevars_to_check_t>>
  Cases_on`unconvert_t h`>>
  fs[t_walk_eqn]>>
  imp_res_tac not_t_oc
  >-
    (`t_wfs (s |+ (next_uvar,Infer_Tvar_db n))` by
      metis_tac[t_wfs_eqn,extend_t_vR_WF]>>
      imp_res_tac FDOM_extend>>
      simp[]>>
      pop_assum (qspec_then `Infer_Tvar_db n` assume_tac)>>
      res_tac>>
      fs[FUPDATE_LIST_THM,DECIDE ``SUC x + n = n + SUC x``])
  >-
    (`t_wfs (s |+ (next_uvar,Infer_Tapp l t))` by metis_tac[t_wfs_eqn,extend_t_vR_WF]>>
    imp_res_tac FDOM_extend>>simp[]>>
    pop_assum(qspec_then `Infer_Tapp l t` assume_tac)>>
    res_tac>>
    fs[FUPDATE_LIST_THM,DECIDE ``SUC x + n = n + SUC x``])
  >-
    fs[check_t_def])

(*Can't find a version of this in the right direction*)
val check_t_t_walkstar = prove
(``t_wfs s ⇒
  !tvs (uvars:num ->bool) t. check_t tvs {} (t_walkstar s t) ⇒ check_t tvs (FDOM s) t``,
  strip_tac>>ho_match_mp_tac check_t_ind>>
  rw[]
  >-
    (Cases_on`tvs' ∈ FDOM s`>>fs[check_t_def]>>
    qpat_assum `check_t A B C` mp_tac>>
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
    metis_tac[MEM_MAP])

(*Ignore increment on deBrujin vars*)
val t_walkstar_ignore_inc = prove(
``t_wfs s ⇒ 
(!t.(!uv. uv ∈ FDOM s ⇒ check_t 0 {} (t_walkstar s (Infer_Tuvar uv)))
⇒
t_walkstar (infer_deBruijn_inc tvs o_f s) t = t_walkstar s t) ∧
(!ts. (!t.(!uv. uv ∈ FDOM s ⇒ check_t 0 {} (t_walkstar s (Infer_Tuvar uv)))
⇒
EVERY (\t. t_walkstar (infer_deBruijn_inc tvs o_f s) t = t_walkstar s t) ts))``, 
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
  fs[infer_deBruijn_inc_def])

(*Adding a list of keys that did not already exist is safe*)
val SUBMAP_FUPDATE_LIST_NON_EXIST = prove(
``set (MAP FST ls) ∩ (FDOM s) = {} 
  ⇒ 
  s SUBMAP (s|++ls)``,
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
  metis_tac[SUBMAP_TRANS])

val t_vwalk_o_f_id = prove(
``t_wfs s ⇒
  !t. t_vwalk (infer_deBruijn_inc 0 o_f s) t = t_vwalk s t``,
  strip_tac>>
  ho_match_mp_tac (Q.INST[`s`|->`s`]t_vwalk_ind)>> 
  rw[]>>
  fs[Once t_vwalk_eqn]>>
  imp_res_tac inc_wfs>>
  simp[Once t_vwalk_eqn]>>
  fs[FLOOKUP_o_f]>>
  BasicProvers.EVERY_CASE_TAC>>
  fs[FLOOKUP_o_f,infer_deBruijn_inc0]>>
  metis_tac[])

val t_walkstar_o_f_id = prove(
``t_wfs s ⇒ 
  !t. t_walkstar ((infer_deBruijn_inc 0) o_f s) t  = t_walkstar s t``,
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
  BasicProvers.EVERY_CASE_TAC>>
  fs[MAP_EQ_f]>>rw[]>>res_tac>>
  fs[t_walkstar_eqn])

val deBruijn_subst_id = prove(
``(!t. deBruijn_subst 0 [] t = t) ∧
  (!ts. MAP (deBruijn_subst 0 []) ts = ts)``,
  Induct>>rw[]>>fs[deBruijn_subst_def,MAP_EQ_ID])

val infer_deBruijn_subst_id = prove(
``(!t. infer_deBruijn_subst [] t = t) ∧ 
  (!ts. MAP (infer_deBruijn_subst []) ts = ts)``,
  Induct>>rw[]>>fs[infer_deBruijn_subst_def,MAP_EQ_ID])

val tenv_inv_submap = prove(
``s SUBMAP s' ∧
  t_wfs s' ∧ 
  tenv_inv s tenv tenvE ⇒ 
  tenv_inv s' tenv tenvE``,
  rw[tenv_inv_def]
  >-
    metis_tac[] 
  >>
    res_tac>>
    `t_walkstar s t' = t_walkstar s' t'` by
      (imp_res_tac t_walkstar_SUBMAP>>
      pop_assum(qspec_then`t'` SUBST1_TAC)>>
      Cases_on`tvs`>>
      metis_tac[check_freevars_to_check_t,t_walkstar_no_vars])>>
    fs[])

val tenv_inv_t_compat = prove(
``t_compat s s' ∧
  t_wfs s' ∧ 
  tenv_inv s tenv tenvE ⇒ 
  tenv_inv s' tenv tenvE``,
  rw[tenv_inv_def]
  >-
    metis_tac[]
  >>
    res_tac>>
    fs[t_compat_def]>>
    first_x_assum(qspec_then `t'` (SUBST_ALL_TAC o SYM))>>
    Cases_on`tvs>0`>>
    metis_tac[check_freevars_to_check_t,t_walkstar_no_vars])

val NOT_SOME_NONE = prove(
``(!x. A ≠ SOME x) ⇒ A = NONE``,
metis_tac[optionTheory.option_nchotomy])

val t_walk_submap_walkstar = prove(
``
!s s'. s SUBMAP s' ∧ t_wfs s ∧ t_wfs s'
⇒  
(!h. t_walk s (t_walkstar s' h) = t_walkstar s' h) ∧
(!hs. MAP ((t_walk s) o t_walkstar s') hs = MAP (t_walkstar s') hs)``,
  ntac 3 strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>rw[]>>
  fs[t_walkstar_eqn,t_walk_eqn,MAP_MAP_o]>>
  Cases_on`t_vwalk s' n`>>fs[t_walk_eqn]>>
  imp_res_tac t_vwalk_to_var>>
  fs[Once t_vwalk_eqn]>>
  `n' ∉ FDOM s` by 
    metis_tac[SUBMAP_DEF]>>
  imp_res_tac flookup_thm>>
  fs[])

val t_unify_to_pure_add_constraints = prove(
``
!s s' h t constraints s''.
pure_add_constraints s (constraints ++ [h,t]) s'' ⇒ 
(?s'. pure_add_constraints s constraints s' ∧
t_unify s' h t = SOME s'')``,
  rw[pure_add_constraints_append]>>
  Q.EXISTS_TAC`s2`>>fs[]>>
  fs[pure_add_constraints_def])

val add_constraint_success = prove(
``
  !t1 t2 st st' x.
  add_constraint t1 t2 st = (Success x, st') ⇔
  x = () ∧
  pure_add_constraints st.subst [t1,t2] st'.subst ∧ 
  st'.next_uvar = st.next_uvar``,
  rw[add_constraint_success,pure_add_constraints_def,EQ_IMP_THM]>>
  rw[infer_st_rewrs,infer_st_component_equality])

val pure_add_constraints_combine = prove(
``
(?st'. (pure_add_constraints st.subst ls st'.subst ∧ st'.next_uvar = x) ∧
(pure_add_constraints st'.subst ls' st''.subst ∧ y = st'.next_uvar))
⇔
pure_add_constraints st.subst (ls++ls') st''.subst ∧ y = x``,

fs[pure_add_constraints_def,EQ_IMP_THM]>>rw[]
>-
  metis_tac[pure_add_constraints_append]
>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<| subst:= s2 ; next_uvar := x|>`>>fs[])

val t_unify_ignore = prove(
``(!s t t'.
  t_wfs s ⇒
  t_walkstar s t = t_walkstar s t' ⇒ 
  t_unify s t t' = SOME s) ∧
  (!s ts ts'.
  t_wfs s ⇒ 
  MAP (t_walkstar s) ts = MAP (t_walkstar s) ts' ⇒ 
  ts_unify s ts ts' = SOME s)``, 
  ho_match_mp_tac t_unify_strongind>>rw[]>>
  fs[t_unify_eqn]>-
  (BasicProvers.FULL_CASE_TAC>>
  imp_res_tac t_walk_submap_walkstar>>fs[]>>
  qpat_assum `t_walkstar s t = X` mp_tac>>
  fs[t_walkstar_eqn]>>every_case_tac>>fs[]>>
  metis_tac[])>>
  Cases_on`ts`>>Cases_on`ts'`>>
  fs[ts_unify_def])

val pure_add_constraints_ignore = prove(
``!s ls. t_wfs s ∧ EVERY (λx,y. t_walkstar s x = t_walkstar s y) ls 
  ⇒ pure_add_constraints s ls s``,
  strip_tac>>Induct>>
  fs[pure_add_constraints_def]>>
  rw[]>>
  Cases_on`h` >>rw[pure_add_constraints_def]>>
  fs[]>>imp_res_tac t_unify_ignore>>
  metis_tac[])

(*t_compat preserves all grounded (no unification variable after walk) terms*)
val t_compat_ground = prove(
``t_compat a b 
  ⇒ 
  ∀uv. uv ∈ FDOM a ∧
       check_t tvs {} (t_walkstar a (Infer_Tuvar uv))
       ⇒ uv ∈ FDOM b ∧ 
         check_t tvs {} (t_walkstar b (Infer_Tuvar uv))``,
  rw[t_compat_def]>>
  first_x_assum (qspec_then `Infer_Tuvar uv` assume_tac)>>
  imp_res_tac t_walkstar_no_vars>>
  fs[check_t_def]>>
  metis_tac[t_walkstar_tuvar_props])

val t_walkstar_tuvar_props2 = prove(
``t_wfs s ∧ t_walkstar s x = Infer_Tuvar uv  
  ⇒ 
  ?k. x = Infer_Tuvar k ∧ 
      (k = uv ⇒ k ∉ FDOM s) ∧
      (k ≠ uv ⇒ k ∈ FDOM s)``,
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
  fs[])

(*Remove every uvar in the FDOM if we walkstar using a completed map*)
val check_t_less = prove(
``
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
  EVERY (check_t n (uvars ∩ (COMPL (FDOM s)))) (MAP (t_walkstar s) ts))``,
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
    fs[check_t_def])

(*Double sided t_compat thm*)
val t_compat_bi_ground = prove(
``(!uv. uv ∈ FDOM a ⇒ check_t n {} (t_walkstar a (Infer_Tuvar uv))) ∧
  t_compat a b ∧ 
  t_compat b a
  ⇒
  (!uv. uv ∈ FDOM b ⇒ check_t n {} (t_walkstar b (Infer_Tuvar uv))) ∧ 
  FDOM a = FDOM b ∧ 
  ((!t. t_walkstar a t= t_walkstar b t) ∧
  (!ts. MAP (t_walkstar a) ts = MAP (t_walkstar b) ts))``, 
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
      metis_tac[t_walkstar_tuvar_props])

(*Free properties when extending the completed map with uvar->ground var*)
val extend_one_props = prove(
``
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
  ∀uv. uv ∈ FDOM s' ⇒ check_t n {} (t_walkstar s' (Infer_Tuvar uv))``,
  strip_tac>>
  fs[LET_THM]>>
  imp_res_tac check_freevars_to_check_t>>
  Q.ABBREV_TAC `constraints' = constraints++[Infer_Tuvar st.next_uvar,unconvert_t t]`>>
  Q.SPECL_THEN [`s`,`[t]`,`st.next_uvar`,`n`] mp_tac pure_add_constraints_exists>>
  discharge_hyps >-
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
       metis_tac[pure_add_constraints_success,t_walkstar_no_vars])

(*This occurs when looking up a list updated fmap*)
val ALOOKUP_lemma = GEN_ALL (prove(
``
  n<LENGTH ls ⇒ 
  ALOOKUP (REVERSE (ZIP ((MAP (\n. offset + n) (COUNT_LIST (LENGTH ls))),ls))) (offset+n)
  = SOME (EL n ls)``,
  rw[]>>
  qmatch_abbrev_tac `ALOOKUP (REVERSE L) k = SOME Y`>>
  Q.ISPECL_THEN [`L`,`k`] mp_tac alookup_distinct_reverse>>
  discharge_hyps_keep>-
    (rw[Abbr`L`,MAP_ZIP,LENGTH_COUNT_LIST]>>
    match_mp_tac ALL_DISTINCT_MAP_INJ>>
    fs[all_distinct_count_list])>>
  rw[]>>
  unabbrev_all_tac>>
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>fs[]>>
  fs[MEM_ZIP,LENGTH_COUNT_LIST]>>HINT_EXISTS_TAC>>
  fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]))

val submap_t_walkstar_replace = prove(
``t_wfs s' ∧
  s SUBMAP s' ∧ 
  check_t n {} (t_walkstar s h)
  ⇒
  t_walkstar s h = t_walkstar s' h``,
  rw[]>>
  imp_res_tac t_walkstar_SUBMAP>>
  metis_tac[t_walkstar_no_vars])

(*Generalize extend_one_props
  ts is a list of types given by the type system
*)
val extend_multi_props = prove(
``!st constraints s ts n.  
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
  ∀uv. uv ∈ FDOM s' ⇒ check_t n {} (t_walkstar s' (Infer_Tuvar uv))``,
  rpt strip_tac>>
  fs[LET_THM]>>CONJ_ASM1_TAC>-
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
    (fs[FDOM_FUPDATE_LIST,count_def,EXTENSION]>>rw[]>>
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
    (rw[]>>
    fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
    qpat_abbrev_tac `s' = s|++A`>>
    `FLOOKUP s' (st.next_uvar+n') = SOME (EL n' (MAP unconvert_t ts))` by
      (fs[Abbr`s'`,flookup_update_list_some]>>
      DISJ1_TAC>>
      Q.ISPECL_THEN [`st.next_uvar`,`n'`,`MAP unconvert_t ts`] mp_tac ALOOKUP_lemma>>
      discharge_hyps_keep>- metis_tac[LENGTH_MAP]>>
      rw[])>>
    simp[]>>
    `check_t n {} (EL n' (MAP unconvert_t ts))` by
      metis_tac[check_freevars_to_check_t,EL_MAP,EVERY_MEM,MEM_EL]>>
    BasicProvers.EVERY_CASE_TAC>>fs[check_t_def]>>
    fs[MAP_EQ_ID]>>rw[]>>metis_tac[EVERY_MEM,t_walkstar_no_vars])>>
  rw[]>>Cases_on`uv ∈ FDOM s`
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
        discharge_hyps>- DECIDE_TAC>>
        metis_tac[check_freevars_to_check_t])
   
(*Useful tactics, mainly for constrain_op*)
 
val unconversion_tac =
  rpt (qpat_assum `convert_t A = B` (assume_tac o (Q.AP_TERM `unconvert_t`)))>>
  imp_res_tac check_t_empty_unconvert_convert_id>>
  fs[unconvert_t_def];

fun pure_add_constraints_combine_tac st constraints s = 
  `pure_add_constraints ^(st).subst (^(constraints) ++ ls) ^(s)` by
    (fs[pure_add_constraints_append]>>
    Q.EXISTS_TAC`^(s)`>>fs[])>>
    Q.SPECL_THEN [`^(s)`,`^(st).subst`,`ls`,`^(constraints)`] assume_tac 
      pure_add_constraints_swap>>
    rfs[];
    
fun pure_add_constraints_rest_tac constraints s = 
  Q.EXISTS_TAC`si`>>
  Q.EXISTS_TAC`^(constraints)`>>
  Q.SPECL_THEN [`n`,`si`,`^(s)`] assume_tac (GEN_ALL t_compat_bi_ground)>>
  rfs[]>>
  rw[]
  >-
    metis_tac[pure_add_constraints_success]
  >>
    TRY(`t_wfs si` by metis_tac[pure_add_constraints_wfs]>>
    fs[pure_add_constraints_wfs,convert_t_def,t_walkstar_eqn,t_walk_eqn]>>NO_TAC);

fun pure_add_constraints_ignore_tac s =
    `pure_add_constraints ^(s) ls ^(s)` by
      (match_mp_tac pure_add_constraints_ignore >>
      fs[Abbr`ls`,t_walkstar_eqn,t_walk_eqn])

val pure_add_constraints_ignore_tac = Q_TAC pure_add_constraints_ignore_tac

(*For grounded ones*)
val pac_tac = 
  pure_add_constraints_ignore_tac `s`>>
  pure_add_constraints_combine_tac ``st`` ``constraints`` ``s``>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st.next_uvar |>` >>fs[]>>
  pure_add_constraints_rest_tac ``constraints`` ``s``;

fun extend_uvar_tac t= 
  `check_freevars n [] ^(t)` by
  (imp_res_tac check_t_to_check_freevars>>
  rfs[check_freevars_def])>>
  Q.SPECL_THEN [`^(t)`,`st`,`s`,`n`,`constraints`] mp_tac (GEN_ALL extend_one_props)>>
  discharge_hyps>- fs[]>>
  qpat_abbrev_tac `s' = s|++A`>>
  Q.ABBREV_TAC `constraints' = constraints++[Infer_Tuvar st.next_uvar,unconvert_t ^(t)]`>>
  rfs[LET_THM]>>
  imp_res_tac pure_add_constraints_success>>
  unconversion_tac>>
  rw[];

val replace_uvar_tac = 
  rpt (qpat_assum `t_walkstar s A = B` (fn th =>     
  (((Q.SUBGOAL_THEN `t_walkstar s' h = ^(th|>concl|>rhs)` assume_tac))>-
  (metis_tac[check_t_def,submap_t_walkstar_replace,th]))) )
    
val rest_uvar_tac =
  pure_add_constraints_ignore_tac `s'`>>
  pure_add_constraints_combine_tac ``st`` ``constraints'`` ``s'``>>
  `t_compat s si` by metis_tac[t_compat_trans]>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st.next_uvar+1 |>` >>fs[]>>
  pure_add_constraints_rest_tac ``constraints'`` ``s'``>>
  TRY(metis_tac[check_freevars_empty_convert_unconvert_id]);

val constrain_op_complete = prove(
``
!n.
type_op op ts t ∧
sub_completion n st.next_uvar st.subst constraints s ∧
FDOM st.subst ⊆ count st.next_uvar ∧
FDOM s = count st.next_uvar ∧
t_wfs st.subst ∧
MAP (convert_t o (t_walkstar s)) ts' = ts ∧
EVERY (check_t n {}) (MAP (t_walkstar s) ts')
⇒
?t' st' s' constraints'.
constrain_op op ts' st = (Success t',st') ∧
sub_completion n st'.next_uvar st'.subst constraints' s' ∧
t_compat s s' ∧
FDOM st'.subst ⊆ count st'.next_uvar ∧
FDOM s' = count st'.next_uvar ∧
t = convert_t (t_walkstar s' t')``,
  strip_tac>>
  fs[sub_completion_def]>>
  rw[]>>
  rfs[]>>
  imp_res_tac pure_add_constraints_wfs>>
  fs[constrain_op_def,type_op_cases]>>
  BasicProvers.EVERY_CASE_TAC>>
  ntac 2 (fs[unconvert_t_def,MAP]>>rw[])>>
  fs[add_constraint_success,success_eqns,sub_completion_def]>>
  Q.SPECL_THEN [`st.subst`,`constraints`,`s`] mp_tac pure_add_constraints_success>>
  discharge_hyps>>rw[]
  >-
    (*int->int->int*)
    (unconversion_tac>>
    Q.EXISTS_TAC `Infer_Tapp [] TC_int`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp [] TC_int);(h',B)]`>>
    pac_tac)
  >- (*int->int->bool*)
    (unconversion_tac>>
     Q.EXISTS_TAC`Infer_Tapp [] TC_bool`>>
     fs[pure_add_constraints_combine]>>
     qpat_abbrev_tac `ls = [(h,Infer_Tapp [] TC_int);(h',B)]`>>
     pac_tac) 
  >- (*Opapp --> Example with fresh unification variable*)
    ((*First find the extension to s and prove every property of s is carried over*)
    extend_uvar_tac ``t``>>
    qpat_abbrev_tac`ls = [(h,Infer_Tapp B C)]`>>
    `t_walkstar s' h' = t_walkstar s h'` by
      metis_tac[submap_t_walkstar_replace]>>
    `t_walkstar s' h = t_walkstar s h` by
      metis_tac[submap_t_walkstar_replace]>>
    rest_uvar_tac)
  >-
    (unconversion_tac>>
    qpat_abbrev_tac `ls = [(h,h')]`>> 
    pac_tac)
  >-
    (unconversion_tac>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    pac_tac)
  >-
    (Q.EXISTS_TAC`s`>>Q.EXISTS_TAC`constraints`>>
    fs[t_compat_refl]>>
    fs[convert_t_def,Once t_walkstar_eqn,Once t_walk_eqn,SimpRHS])
  >-
    (extend_uvar_tac ``t``>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    replace_uvar_tac>>
    rest_uvar_tac)
  >-
    (unconversion_tac>>
    Q.EXISTS_TAC`Infer_Tapp [] TC_word8array`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp [] TC_int);(h',B)]`>>
    pac_tac)
  >-
    (unconversion_tac>>
    Q.EXISTS_TAC`Infer_Tapp [] TC_word8`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp [] A);(h',B)]`>>
    pac_tac)
  >-
    (unconversion_tac>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp [] A)]`>>
    pac_tac)
  >-
    (unconversion_tac>>
    Q.EXISTS_TAC`Infer_Tapp [] TC_unit`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp [] A);B;C]`>>
    pac_tac)
  >-
    (unconversion_tac >>
     qpat_abbrev_tac `ls = [(h,Infer_Tapp [] A)]`>>
     simp[Tchar_def] >>
     pac_tac)
  >-
    (unconversion_tac >>
     fs[Tchar_def] >>
     qpat_abbrev_tac `ls = [(h,Infer_Tapp X A)]`>>
     pure_add_constraints_ignore_tac `s`>-simp[unconvert_t_def]>>
     pure_add_constraints_combine_tac ``st`` ``constraints`` ``s``>>
     fs[pure_add_constraints_append]>>
     Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st.next_uvar |>` >>fs[]>>
     pure_add_constraints_rest_tac ``constraints`` ``s``)
  >-
    (extend_uvar_tac ``t2``>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    replace_uvar_tac>>
    rest_uvar_tac>>
    `t_wfs si` by metis_tac[pure_add_constraints_wfs]>>
    fs[convert_t_def,t_walkstar_eqn,t_walk_eqn]>>
    metis_tac[check_freevars_empty_convert_unconvert_id])
  >-
    (Q.EXISTS_TAC `Infer_Tuvar st.next_uvar`>>
    fs[pure_add_constraints_combine]>>
    extend_uvar_tac ``t``>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B);C]`>>
    replace_uvar_tac>>
    (*Doesn't work because we don't know check_t of RHS in the tactic*)
    `t_walkstar s' h' = Infer_Tapp [] TC_int` by
      metis_tac[submap_t_walkstar_replace]>>
    rest_uvar_tac)
  >-
    (extend_uvar_tac ``t1``>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    replace_uvar_tac>>
    rest_uvar_tac)
  >-
    (unconversion_tac>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp [] A)]`>>
    pac_tac)
  >-
    (Q.EXISTS_TAC `Infer_Tuvar st.next_uvar`>>
    fs[pure_add_constraints_combine]>>
    extend_uvar_tac ``t``>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B);C]`>>
    replace_uvar_tac>>
    `t_walkstar s' h' = Infer_Tapp [] TC_int` by
      metis_tac[submap_t_walkstar_replace]>>
    rest_uvar_tac)
  >-
    (extend_uvar_tac ``t1``>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp A B)]`>>
    replace_uvar_tac>>
    rest_uvar_tac)
  >-
    (unconversion_tac>>
    Q.EXISTS_TAC`Infer_Tapp [] TC_unit`>>
    fs[pure_add_constraints_combine]>>
    qpat_abbrev_tac `ls = [(h,Infer_Tapp [h''] A);(h',B)]`>>
    pac_tac)
  )

val simp_tenv_inv_def = Define`
  simp_tenv_inv s tvs tenv tenvE ⇔ 
  (!n t. ALOOKUP tenvE n = SOME t 
  ⇒
  check_freevars tvs [] t ∧ 
  ?t'. ALOOKUP tenv n = SOME t' ∧ 
       unconvert_t t = t_walkstar s t') ∧ 
  !n t'. ALOOKUP tenv n = SOME t' ⇒ 
  ?t. ALOOKUP tenvE n = SOME t`

val simp_tenv_inv_empty = prove(
``simp_tenv_inv s n [] []``,
  rw[simp_tenv_inv_def])

val simp_tenv_inv_more = prove(
``simp_tenv_inv s tvs tenv tenvE ∧ 
  t_compat s s' ⇒ 
  simp_tenv_inv s' tvs tenv tenvE``,
  rw[simp_tenv_inv_def]>>
  res_tac>>
  fs[t_compat_def]>>
  metis_tac[check_freevars_to_check_t,t_walkstar_no_vars])

val simp_tenv_inv_append = prove(
``simp_tenv_inv s'' tvs tenv tenvE ∧
  simp_tenv_inv s'' tvs tenv' tenvE'
  ⇒ 
  simp_tenv_inv s'' tvs (tenv'++tenv) (tenvE' ++ tenvE)``,
  rw[simp_tenv_inv_def]>>
  fs[ALOOKUP_APPEND]>>
  BasicProvers.EVERY_CASE_TAC>>res_tac>>fs[]>>metis_tac[])

(*convert on both sides of eqn*)
val convert_bi_remove = prove(
``convert_t A = convert_t B ∧ 
  check_t n {} A ∧
  check_t m {} B
  ⇒ 
  A = B``,
  rw[]>>
  last_x_assum (assume_tac o (Q.AP_TERM `unconvert_t`))>>
  metis_tac[check_t_empty_unconvert_convert_id])

(*Substituting every tvs away with something that has no tvs leaves none left*)
val infer_type_subst_check_t_less = prove(
``
  LENGTH ls = LENGTH tvs ∧
  EVERY (check_t n {}) ls ⇒  
  (!t.
  check_freevars n tvs t 
  ⇒ 
  check_t n {} (infer_type_subst (ZIP (tvs,ls)) t)) ∧
  (!ts.
  EVERY (check_freevars n tvs) ts
  ⇒ 
  EVERY (check_t n {}) (MAP (infer_type_subst (ZIP(tvs,ls))) ts))``,
  strip_tac>>
  Induct>>rw[]
  >-
    (fs[check_freevars_def,infer_type_subst_def]>>
    `?x. ALOOKUP (ZIP(tvs,ls)) s = SOME x` by
      (SPOSE_NOT_THEN assume_tac>>
      imp_res_tac NOT_SOME_NONE>>
      fs[ALOOKUP_NONE]>>
      metis_tac[MAP_ZIP])>>
    imp_res_tac ALOOKUP_MEM>>
    Q.ISPECL_THEN [`tvs`,`ls`,`s,x`] assume_tac MEM_ZIP>> rfs[]>>
    metis_tac[EVERY_EL])
  >>
    fs[infer_type_subst_def,check_t_def,check_freevars_def]>>
    fs[EVERY_MAP]>>metis_tac[])

val infer_p_complete = prove(
``
  (!tvs tenvC p t tenvE.
  type_p tvs tenvC p t tenvE
  ⇒
  !s st constraints.
  tenvC_ok tenvC ∧ 
  t_wfs st.subst ∧
  sub_completion tvs st.next_uvar st.subst constraints s ∧
  FDOM st.subst ⊆ count st.next_uvar ∧ 
  FDOM s = count st.next_uvar 
  ⇒
  ?t' tenv st' s' constraints'.
    infer_p tenvC p st  = (Success (t',tenv),st') ∧ 
    sub_completion tvs st'.next_uvar st'.subst constraints' s' ∧ 
    FDOM st'.subst ⊆ count st'.next_uvar ∧ 
    FDOM s' = count st'.next_uvar ∧
    t_compat s s' ∧
    simp_tenv_inv s' tvs tenv tenvE ∧ 
    t = convert_t (t_walkstar s' t')) ∧ 
  (!tvs tenvC ps ts tenvE.
  type_ps tvs tenvC ps ts tenvE
  ⇒ 
  !s st constraints.
  tenvC_ok tenvC ∧ 
  t_wfs st.subst ∧ 
  sub_completion tvs st.next_uvar st.subst constraints s ∧ 
  FDOM st.subst ⊆ count st.next_uvar ∧ 
  FDOM s = count st.next_uvar
  ⇒ 
  ?ts' tenv st' s' constraints'.
    infer_ps tenvC ps st = (Success (ts',tenv),st') ∧ 
    sub_completion tvs st'.next_uvar st'.subst constraints' s' ∧ 
    FDOM st'.subst ⊆ count st'.next_uvar ∧ 
    FDOM s' = count st'.next_uvar ∧
    t_compat s s' ∧ 
    simp_tenv_inv s' tvs tenv tenvE ∧ 
    ts = MAP (convert_t o t_walkstar s') ts')``,
  ho_match_mp_tac type_p_strongind>>
  rw[UNCURRY,success_eqns,infer_p_def]
  >-
    (Q.SPECL_THEN [`t`,`st`,`s`,`tvs`,`constraints`]
      mp_tac (GEN_ALL extend_one_props)>>
    `t_wfs s` by metis_tac[sub_completion_wfs]>>
    discharge_hyps >> fs[LET_THM,sub_completion_def]>>
    qpat_abbrev_tac `s' = s|++A`>>
    qpat_abbrev_tac `constraints' = constraints ++ B`>> rw[]>>
    ntac 2 HINT_EXISTS_TAC>>rw[]
    >-
      (fs[SUBSET_DEF,count_def]>>rw[]>>res_tac>>DECIDE_TAC)
    >-
      metis_tac[SUBMAP_t_compat]
    >>
      fs[simp_tenv_inv_def]>>
      metis_tac[check_freevars_empty_convert_unconvert_id])
  >>TRY(ntac 2 HINT_EXISTS_TAC >>
    imp_res_tac sub_completion_wfs>>
    fs[t_walkstar_eqn,convert_t_def,t_walk_eqn,Tchar_def]>>
    metis_tac[t_compat_refl,simp_tenv_inv_empty])
  >-(
    first_x_assum(qspecl_then [`s`,`st`,`constraints`] assume_tac)>>rfs[]>>
    imp_res_tac tenvC_ok_lookup>>
    Q.SPECL_THEN [`st'`,`constraints'`,`s'`,`ts'`,`tvs`] mp_tac extend_multi_props>>
    discharge_hyps_keep >-
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
      discharge_hyps_keep
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
      discharge_hyps_keep>-
        (imp_res_tac infer_p_check_t>>
        fs[EVERY_EL]>>
        pop_assum(qspec_then `n` mp_tac)>>discharge_hyps>-metis_tac[]>>
        assume_tac (GEN_ALL check_t_less)>>
        pop_assum(qspecl_then [`count st'.next_uvar`,`s'`,`tvs`] assume_tac)>>
        rw[]>>
        first_x_assum(qspec_then `EL n ts''` mp_tac)>>
        discharge_hyps>>fs[])>>
      strip_tac>>
      pop_assum (qspec_then `tvs` mp_tac)>>discharge_hyps
      >-
        (assume_tac (GEN_ALL infer_type_subst_check_t_less)>>
        pop_assum(qspecl_then [`tvs'`,`tvs`,`unconv_ts'`] mp_tac)>>
        discharge_hyps>-
          (fs[EVERY_MEM,Abbr`unconv_ts'`]>>rw[MEM_MAP]>>res_tac>>
          fs[check_freevars_to_check_t])>>
        rw[]>>
        first_x_assum(qspec_then `EL n ts` mp_tac)>>
        discharge_hyps>-
          (imp_res_tac check_freevars_add>>
          pop_assum (qspec_then `tvs` assume_tac)>>rfs[])>>
        rw[])>>
      rw[]>>
      imp_res_tac submap_t_walkstar_replace>>
      ntac 7 (pop_assum kall_tac)>>
      pop_assum (SUBST1_TAC o SYM)>>
      qpat_assum `C = t_walkstar A B` (SUBST1_TAC o SYM)>>
      Q.SPECL_THEN [`EL n ts`,`tvs'`,`s''`,`st'.next_uvar`] mp_tac
         (fst (CONJ_PAIR subst_infer_subst_swap))>>
      discharge_hyps>-metis_tac[pure_add_constraints_success]>>
      rw[]>>fs[]>>
      AP_THM_TAC>>
      ntac 3 AP_TERM_TAC>>
      match_mp_tac LIST_EQ>> CONJ_ASM1_TAC
      >>
        fs[LENGTH_MAP,LENGTH_COUNT_LIST]
      >>
        rw[Abbr`s''`]>>
        simp[LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST])>>
    pure_add_constraints_combine_tac ``st'`` ``constraints''`` ``s''``>>
    imp_res_tac infer_p_wfs>>fs[pure_add_constraints_append]>>
    Q.EXISTS_TAC `<|subst:=s2';next_uvar:=st'.next_uvar+LENGTH tvs'|>`>>fs[]>>
    Q.LIST_EXISTS_TAC [`si`,`constraints''`]>>fs[]>>
    Q.SPECL_THEN [`tvs`,`si`,`s''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
    rfs[]>>
    rw[simp_tenv_inv_def]
    >-
      metis_tac[pure_add_constraints_success]
    >-
      metis_tac[t_compat_trans,SUBMAP_t_compat]
    >-
      metis_tac[simp_tenv_inv_def]
    >-
      (fs[simp_tenv_inv_def]>>res_tac>>
      imp_res_tac check_freevars_to_check_t>>
      `t_walkstar s' t' = t_walkstar s'' t'` by 
        (match_mp_tac (GEN_ALL submap_t_walkstar_replace)>>
        metis_tac[check_freevars_to_check_t])>>
      fs[t_compat_def])
    >-
      metis_tac[simp_tenv_inv_def]
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
        pop_assum kall_tac>>
        pop_assum (SUBST1_TAC o SYM)>>
        rpt AP_TERM_TAC>>
        DECIDE_TAC)
  >-
    (first_x_assum(qspecl_then [`s`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    ntac 2 HINT_EXISTS_TAC>>fs[]>>
    imp_res_tac infer_p_wfs>>
    imp_res_tac sub_completion_wfs>>
    fs[Once t_walkstar_eqn,Once t_walk_eqn,convert_t_def,MAP_MAP_o]>>
    fs[MAP_EQ_f])
  >-
    (first_x_assum(qspecl_then [`s`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    ntac 2 HINT_EXISTS_TAC>>fs[]>>
    imp_res_tac infer_p_wfs>>
    imp_res_tac sub_completion_wfs>>
    fs[Once t_walkstar_eqn,Once t_walk_eqn,SimpRHS,convert_t_def])
  >>
    (last_x_assum(qspecl_then [`s`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    first_x_assum(qspecl_then [`s'`,`st'`,`constraints'`] mp_tac)>>
    discharge_hyps>>fs[]
    >- metis_tac[infer_p_wfs]
    >>
    rw[]>>fs[]>>
    ntac 2 HINT_EXISTS_TAC>>fs[]>>
    rw[]
    >- metis_tac[t_compat_trans]
    >- metis_tac[simp_tenv_inv_more,simp_tenv_inv_append]
    >>
       imp_res_tac infer_p_check_t>>
       assume_tac (GEN_ALL check_t_less)>>
       fs[sub_completion_def]>>
       pop_assum (qspecl_then [`count st'.next_uvar`,`s'`,`tvs`] assume_tac)>>
       rfs[]>>
       first_x_assum(qspec_then `t'` mp_tac)>>
       discharge_hyps>-
         metis_tac[t_compat_def]>>
       rw[]>>AP_TERM_TAC>>
       fs[t_compat_def]>>
       metis_tac[t_walkstar_no_vars]))

(*Specialize check_t_less a bit since we use this form a lot*)
val sub_completion_completes = prove(
``t_wfs s ∧ 
  check_t 0 (count n) t ∧ 
  FDOM s = count n ∧ 
  (!uv. uv < n ⇒
    check_t (num_tvs tenvE) {} (t_walkstar s (Infer_Tuvar uv)))
  ⇒
  check_t (num_tvs tenvE) {} (t_walkstar s t)``,
  assume_tac (GEN_ALL (fst(CONJ_PAIR check_t_less)))>>
  rw[]>>
  first_x_assum(qspecl_then[`count n`,`s`,`num_tvs tenvE`,`t`] mp_tac)>>
  discharge_hyps>>fs[])

val lookup_tenv_bind_var_list = prove(
``!tenv. 
  lookup_tenv x 0 (bind_var_list 0 tenv tenvE) =
  case ALOOKUP tenv x of 
    SOME t => SOME (0,t)
  | NONE => lookup_tenv x 0 tenvE``,
  Induct>>rw[bind_var_list_def]>>
  Cases_on`h`>>rw[bind_var_list_def,lookup_tenv_def,bind_tenv_def,deBruijn_inc0])

(*This should be general enough to prove both Mat and Handle cases*)
val infer_pes_complete = prove(
``!pes st' constraints' s'. 
  pes ≠ [] ∧
  tenvC_ok tenvC ∧ 
  t_wfs st'.subst ∧
  check_menv menv ∧
  check_env (count uvar) tenv ∧ 
  uvar ≤ st'.next_uvar ∧
  tenv_inv s' tenv tenvE ∧ 
  (∀x::set pes.
    ∃tenv'.
      ALL_DISTINCT (pat_bindings (FST x) []) ∧
      type_p (num_tvs tenvE) tenvC (FST x) t1 tenv' ∧
      type_e (convert_menv menv) tenvC (bind_var_list 0 tenv' tenvE)
        (SND x) t2 ∧
      ∀s'' menv' tenv'' st'' constraints''.
        check_menv menv' ∧ check_env (count st''.next_uvar) tenv'' ∧
        convert_menv menv = convert_menv menv' ∧ t_wfs st''.subst ∧
        sub_completion (num_tvs (bind_var_list 0 tenv' tenvE))
          st''.next_uvar st''.subst constraints'' s'' ∧
        FDOM st''.subst ⊆ count st''.next_uvar ∧
        FDOM s'' = count st''.next_uvar ∧
        tenv_inv s'' tenv'' (bind_var_list 0 tenv' tenvE) ⇒
        ∃t'' st''' s''' constraints'''.
          infer_e menv' tenvC tenv'' (SND x) st'' =
          (Success t'',st''') ∧
          sub_completion (num_tvs (bind_var_list 0 tenv' tenvE))
            st'''.next_uvar st'''.subst constraints''' s''' ∧
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
  infer_pes menv tenvC tenv pes t1' t2' st' = (Success (), st'') ∧ 
  sub_completion (num_tvs tenvE) st''.next_uvar st''.subst constraints'' s'' ∧ 
  FDOM st''.subst ⊆ count st''.next_uvar ∧ 
  FDOM s'' = count st''.next_uvar ∧
  t_compat s' s''``,
  Induct>- rw[]>>
  rpt GEN_TAC>>
  strip_tac>>
  Cases_on`h`>>
  simp[add_constraint_success,infer_e_def,success_eqns,UNCURRY]>>
  fs[RES_FORALL]>>
  first_x_assum(qspec_then `q,r` assume_tac)>>rfs[]>>
  Q.SPECL_THEN [`num_tvs tenvE`,`tenvC`,`q`,`t1`,`tenv'`] assume_tac 
    (fst (CONJ_PAIR infer_p_complete))>>rfs[]>>
  pop_assum(qspecl_then [`s'`,`st'`,`constraints'`] assume_tac)>>rfs[]>>
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
  pure_add_constraints_combine_tac ``st''`` ``constraints''`` ``s''``>>
  `t_wfs st''.subst` by metis_tac[infer_p_wfs]>>fs[]>>
  Q.SPECL_THEN [`num_tvs tenvE`,`si`,`s''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
  rfs[]>>
  fs[pure_add_constraints_append]>>
  fs[Once PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
  Q.ABBREV_TAC `nst = <|next_uvar:=st''.next_uvar;subst:=s2'|>`>>
  qexists_tac `nst`>>fs[]>>
  qpat_abbrev_tac `ntenv = MAP bla tenv'' ++ tenv`>>
  first_x_assum(qspecl_then [`si`,`menv`,`ntenv`,`nst`,`constraints''`] mp_tac)>>
  discharge_hyps_keep>-
    (fs[Abbr`nst`]>>rw[]
     >-
       (fs[Abbr`ntenv`,check_env_merge]>>
       CONJ_TAC>-
        (fs[check_env_def,EVERY_MAP]>>
        imp_res_tac infer_p_check_t>>
        fs[EVERY_MEM]>>rw[]>>
        first_x_assum(qspec_then `x` assume_tac)>>rfs[]>>
        PairCases_on`x`>>fs[])
      >>
        `st'.next_uvar ≤ st''.next_uvar` by metis_tac[infer_p_next_uvar_mono]>>
        metis_tac[check_env_more])
    >-
      metis_tac[pure_add_constraints_wfs]
    >-
      fs[num_tvs_bind_var_list]
    >-
      metis_tac[pure_add_constraints_success]
    >>
      `t_compat s' si` by metis_tac[t_compat_trans]>>
      `t_wfs si` by metis_tac[pure_add_constraints_wfs]>>
      imp_res_tac tenv_inv_t_compat>>
      ntac 10 (pop_assum kall_tac)>>
      fs[tenv_inv_def,simp_tenv_inv_def]>>
      rw[]>>fs[lookup_tenv_bind_var_list]
      >-
        (BasicProvers.FULL_CASE_TAC>>fs[]>>
        metis_tac[])
      >-
        (BasicProvers.FULL_CASE_TAC>>fs[Abbr`ntenv`]>>
        fs[ALOOKUP_APPEND,ALOOKUP_MAP]>>
        Cases_on`ALOOKUP tenv'' x`>-
          (fs[]>>metis_tac[])>>
        first_x_assum(qspecl_then [`x`,`x'`] assume_tac)>>rfs[])
      >-
        (BasicProvers.FULL_CASE_TAC>>fs[]>>
        metis_tac[])
      >>
        BasicProvers.FULL_CASE_TAC>>fs[Abbr`ntenv`]
        >-
        (fs[ALOOKUP_APPEND,ALOOKUP_MAP]>>
        Cases_on`ALOOKUP tenv'' x`>-
          (fs[]>>metis_tac[])>>
        first_x_assum(qspecl_then [`x`,`x'`] assume_tac)>>rfs[])
        >>
        first_x_assum(qspecl_then [`x`,`t`] assume_tac)>>rfs[]>>
        qexists_tac`t''`>>
        fs[ALOOKUP_APPEND,ALOOKUP_MAP])
  >>
  rw[]>> 
  `t_wfs st''''.subst` by metis_tac[infer_e_wfs]>>
  fs[Abbr`nst`]>>
  qunabbrev_tac`ls`>>
  qpat_abbrev_tac `ls = ([t2',t''])`>>
  imp_res_tac infer_e_check_t>>
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
  pure_add_constraints_combine_tac ``st''''`` 
    ``constraints''''`` ``s''''``>>
  Q.SPECL_THEN [`num_tvs tenvE`,`si'`,`s''''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
  rfs[]>>
  fs[pure_add_constraints_append]>>
  fs[Once PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
  Q.ABBREV_TAC `nst = <|next_uvar:=st''''.next_uvar;subst:=s2'''|>`>>
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
    discharge_hyps>-
      (fs[Abbr`nst`,pure_add_constraints_success]>>rw[]
      >-
        metis_tac[pure_add_constraints_wfs]
      >-
        (imp_res_tac infer_p_next_uvar_mono>>
        imp_res_tac infer_e_next_uvar_mono>>
        fs[]>>DECIDE_TAC)
      >-
        (`t_compat s' si'` by metis_tac[t_compat_trans]>>
        `t_wfs si'` by metis_tac[pure_add_constraints_wfs]>>
        imp_res_tac tenv_inv_t_compat)
      >-
        metis_tac[pure_add_constraints_success]
      >>
      rfs[]>>
      `t_compat s' si'` by metis_tac[t_compat_trans]>>
      fs[t_compat_def]>>
      metis_tac[t_walkstar_no_vars,check_t_empty_unconvert_convert_id])>>
    rw[]>>
    fs[Abbr`nst`]>>
    ntac 2 HINT_EXISTS_TAC>> fs[]>>
    metis_tac[t_compat_trans])

val infer_e_complete = Q.prove (
`
 (!tenvM tenvC tenvE e t. 
   type_e tenvM tenvC tenvE e t
   ⇒
   !s menv tenv st constraints.
     (*These two might be a consequence of the others*)
     check_menv menv ∧ 
     check_env (count st.next_uvar) tenv ∧
     tenvC_ok tenvC ∧  
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion (num_tvs tenvE) st.next_uvar st.subst constraints s ∧
     (*I think these conditions are reasonable... the second one maybe not*)
     FDOM st.subst ⊆ count st.next_uvar ∧ 
     (*This forces "constraints" to only constrain the necessary unification variables*)
     FDOM s = count st.next_uvar ∧
     tenv_inv s tenv tenvE
     ⇒
     ?t' st' s' constraints'.
       infer_e menv tenvC tenv e st = (Success t', st') ∧
       sub_completion (num_tvs tenvE) st'.next_uvar st'.subst constraints' s' ∧
       FDOM st'.subst ⊆  count st'.next_uvar ∧ 
       FDOM s' = count st'.next_uvar ∧
       t_compat s s' ∧   
       t = convert_t (t_walkstar s' t')) ∧
 (!tenvM tenvC tenvE es ts. 
   type_es tenvM tenvC tenvE es ts
   ⇒
   !s menv tenv st constraints.
     check_menv menv ∧ 
     check_env (count st.next_uvar) tenv ∧ 
     tenvC_ok tenvC ∧ 
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion (num_tvs tenvE) st.next_uvar st.subst constraints s ∧
     FDOM st.subst ⊆ count st.next_uvar ∧ 
     FDOM s = count st.next_uvar ∧ 
     tenv_inv s tenv tenvE
     ⇒
     ?ts' st' s' constraints'.
       infer_es menv tenvC tenv es st = (Success ts', st') ∧
       sub_completion (num_tvs tenvE) st'.next_uvar st'.subst constraints' s' ∧
       FDOM st'.subst ⊆ count st'.next_uvar ∧ 
       FDOM s' = count st'.next_uvar ∧ 
       t_compat s s' ∧ 
       ts = MAP (convert_t o t_walkstar s') ts') ∧
 (!tenvM tenvC tenvE funs env. 
   type_funs tenvM tenvC tenvE funs env
   ⇒
   !s menv tenv st constraints.
     check_menv menv ∧ 
     check_env (count st.next_uvar) tenv ∧ 
     tenvC_ok tenvC ∧ 
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion (num_tvs tenvE) st.next_uvar st.subst constraints s ∧
     FDOM st.subst ⊆ count st.next_uvar ∧ 
     FDOM s = count st.next_uvar ∧ 
     tenv_inv s tenv tenvE
     ⇒
     ?env' st' s' constraints'.
       infer_funs menv tenvC tenv funs st = (Success env', st') ∧
       sub_completion (num_tvs tenvE) st'.next_uvar st'.subst constraints' s' ∧
       FDOM st'.subst ⊆ count st'.next_uvar ∧ 
       FDOM s' = count st'.next_uvar ∧
       t_compat s s' ∧  
       MAP SND env = MAP (convert_t o t_walkstar s') env')`,
 ho_match_mp_tac type_e_strongind >>
 rw [add_constraint_success,success_eqns,infer_e_def]
 (*Easy cases*)
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [t_compat_refl])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [t_compat_refl])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def, Tchar_def] >>
     metis_tac [t_compat_refl])
 >- (qexists_tac `s'` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [t_compat_refl])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [t_compat_refl])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [t_compat_refl])
 >-
   (*Raise*)
   (imp_res_tac check_freevars_to_check_t>>
   first_x_assum(qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>
   rfs[]>>
   `t_wfs st'.subst ∧ t_wfs s'` by 
     (CONJ_ASM1_TAC>> metis_tac[infer_e_wfs,sub_completion_wfs])>>
   Q.SPECL_THEN [`t`,`st'`,`s'`,`num_tvs tenvE`,`constraints'`]
     mp_tac (GEN_ALL extend_one_props)>>
   discharge_hyps >> fs[LET_THM,sub_completion_def]>>
   qpat_abbrev_tac `fin_s = s'|++A`>>
   qpat_abbrev_tac `fin_c = constraints' ++ B`>> rw[]>>
   Q.EXISTS_TAC `Infer_Tuvar st'.next_uvar`>>fs[]>>
   imp_res_tac infer_e_check_t>>
   assume_tac (GEN_ALL check_t_less)>>
   first_x_assum(qspecl_then [`count st'.next_uvar`,`s'`,`num_tvs tenvE`] assume_tac)>>
   fs[]>>
   first_x_assum(qspec_then `t'` mp_tac)>>
   discharge_hyps>>fs[]>> strip_tac>>
   `t_walkstar fin_s t' = Infer_Tapp [] TC_exn` by 
     (qpat_assum `A = convert_t B` (assume_tac o SYM o (Q.AP_TERM`unconvert_t`))>>
     fs[unconvert_t_def]>>
     metis_tac[pure_add_constraints_success,submap_t_walkstar_replace
              ,check_t_empty_unconvert_convert_id])>>
   qpat_abbrev_tac `ls = [(t',Infer_Tapp A B)]`>>
   pure_add_constraints_ignore_tac `fin_s`>>
   pure_add_constraints_combine_tac ``st'`` ``fin_c`` ``fin_s``>>
   fs[pure_add_constraints_append]>>
   fs[PULL_EXISTS]>>
   Q.LIST_EXISTS_TAC [`si`,`fin_c`,`<|subst:=s2' ; next_uvar := st'.next_uvar |>`]>>
   Q.SPECL_THEN [`num_tvs tenvE`,`si`,`fin_s`] assume_tac (GEN_ALL t_compat_bi_ground)>>
   rfs[]>>
   metis_tac[pure_add_constraints_success,t_compat_trans
            ,check_freevars_empty_convert_unconvert_id])
 >- (*Handler*)
   (
   last_x_assum (qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>rfs[]>>
   fs[UNCURRY]>>
   imp_res_tac infer_e_wfs>>
   fs[sub_completion_def]>>
   imp_res_tac infer_e_check_t>>
   rfs[]>>
   imp_res_tac pure_add_constraints_wfs>>
   `check_t (num_tvs tenvE) {} (t_walkstar s' t')` by
     metis_tac[sub_completion_completes]>>
   assume_tac (GEN_ALL infer_pes_complete)>>
   pop_assum(qspecl_then 
     [`st.next_uvar`,`tenvE`,`tenvC`,`tenv`,`t'`
     ,`t`,`Infer_Tapp [] TC_exn`,`Tapp [] TC_exn`
     ,`menv`,`pes`,`st'`,`constraints'`,`s'`] mp_tac)>>
   discharge_hyps_keep >-
     (fs[sub_completion_def]>>rw[]
     >-
       metis_tac[infer_e_next_uvar_mono]
     >-
       metis_tac[tenv_inv_t_compat]
     >-
       fs[t_walkstar_eqn,unconvert_t_def,t_walk_eqn]
     >>
       metis_tac[sub_completion_completes,check_t_empty_unconvert_convert_id])>>
   rw[]>>
   ntac 3 HINT_EXISTS_TAC>>fs[sub_completion_def]>>
   CONJ_TAC>-metis_tac[t_compat_trans]>>
   AP_TERM_TAC>>
   fs[t_compat_def]>>
   metis_tac[t_walkstar_no_vars])
   (*pop_assum kall_tac
     qid_spec_tac
    Q.ID_SPEC_TAC
    *) 
 >- (*Con*)
   (first_x_assum(qspecl_then[`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>> rfs[sub_completion_def]>>
   qspecl_then [`st'`,`constraints'`,`s'`,`ts'`,`num_tvs tenvE`] 
     mp_tac extend_multi_props>>
   discharge_hyps_keep>-
     (fs[]>>metis_tac[infer_e_wfs,pure_add_constraints_wfs])>>
   imp_res_tac tenvC_ok_lookup>>
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
      discharge_hyps_keep
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
      discharge_hyps_keep>-
        (
        imp_res_tac infer_e_check_t>>
        fs[EVERY_EL]>>
        first_x_assum(qspec_then `n` mp_tac)>>discharge_hyps>-metis_tac[]>>
        assume_tac (GEN_ALL check_t_less)>>
        pop_assum(qspecl_then [`count st'.next_uvar`,`s'`
                              ,`num_tvs tenvE`] assume_tac)>>
        rw[]>>
        first_x_assum(qspec_then `EL n ts''` mp_tac)>>
        discharge_hyps>>fs[])>>
      strip_tac>>
      pop_assum (qspec_then `num_tvs tenvE` mp_tac)>>discharge_hyps
      >-
        (assume_tac (GEN_ALL infer_type_subst_check_t_less)>>
        pop_assum(qspecl_then [`tvs`,`num_tvs tenvE `
                              ,`unconv_ts'`] mp_tac)>>
        discharge_hyps>-
          (fs[EVERY_MEM,Abbr`unconv_ts'`]>>rw[MEM_MAP]>>res_tac>>
          fs[check_freevars_to_check_t])>>
        rw[]>>
        first_x_assum(qspec_then `EL n ts` mp_tac)>>
        discharge_hyps>-
          (imp_res_tac check_freevars_add>>
          pop_assum (qspec_then `num_tvs tenvE` assume_tac)>>rfs[])>>
        rw[])>>
      rw[]>>
      imp_res_tac submap_t_walkstar_replace>>
      ntac 7 (pop_assum kall_tac)>>
      pop_assum (SUBST1_TAC o SYM)>>
      qpat_assum `C = t_walkstar A B` (SUBST1_TAC o SYM)>>
      Q.SPECL_THEN [`EL n ts`,`tvs`,`s''`,`st'.next_uvar`] mp_tac
         (fst (CONJ_PAIR subst_infer_subst_swap))>>
      discharge_hyps>-metis_tac[pure_add_constraints_success]>>
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
   pure_add_constraints_combine_tac ``st'`` ``constraints''`` ``s''``>>
   imp_res_tac infer_e_wfs>>fs[pure_add_constraints_append]>>
   Q.EXISTS_TAC `<|subst:=s2';next_uvar:=st'.next_uvar+LENGTH ts'|>`>>fs[]>>
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
    (first_x_assum(qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    ntac 2 HINT_EXISTS_TAC>>
    fs[t_compat_def]>>
    simp[SimpRHS,Once t_walkstar_eqn,t_walk_eqn,convert_t_def,MAP_MAP_o]>>
    fs[MAP_EQ_f])
 >- (*Var*)
    (Cases_on `n` >>
     rw [success_eqns, infer_e_def] >>
     fs [t_lookup_var_id_def, tenv_inv_def]
     >- (*Short*)
        (res_tac >>
         rw [success_eqns] >>
         rw [Once SWAP_EXISTS_THM] >>
         fs[sub_completion_def]>>
         Q.SPECL_THEN [`st`,`constraints`,`s`,`targs`,`num_tvs tenvE`]
           mp_tac extend_multi_props>>
         discharge_hyps>-
           (fs[]>>metis_tac[pure_add_constraints_wfs])
         >>
         BasicProvers.LET_ELIM_TAC>>
         Q.EXISTS_TAC`constraints++new_constraints`>>
         HINT_EXISTS_TAC>>
         rw[]
         >-
           (fs[SUBSET_DEF,count_def]>>rw[]>>res_tac>>DECIDE_TAC)
         >-
           metis_tac[SUBMAP_t_compat]
         (*deBruijn_subst*)
         >>
         reverse (Cases_on`LENGTH targs >0`)
         >-
         (unabbrev_all_tac>>
         `LENGTH targs = 0` by DECIDE_TAC>>
         fs[LENGTH_NIL,deBruijn_subst_id,COUNT_LIST_def
           ,infer_deBruijn_subst_id,FUPDATE_LIST]>>
         qpat_assum `unconvert_t t = bla`
           (assume_tac o Q.AP_TERM `convert_t`)>>
         metis_tac[check_freevars_empty_convert_unconvert_id])
         >>
         fs[]>>
         imp_res_tac check_freevars_to_check_t>>
         assume_tac (db_subst_infer_subst_swap|>CONJ_PAIR|>fst)>>
         pop_assum (qspecl_then [`t'`,`s'`,`LENGTH targs`
          ,`st.next_uvar`,`num_tvs tenvE`] assume_tac)>>
         `check_t (LENGTH targs) (FDOM s') t'` by
          (imp_res_tac check_t_t_walkstar>>
           `FDOM s ⊆ FDOM s'` by 
             fs[SUBSET_DEF,SUBMAP_DEF]>>
           imp_res_tac check_t_more5>>
           metis_tac[EMPTY_SUBSET])>> 
         rfs[check_t_more]>>
         fs[MAP_MAP_o]>>
         `(MAP (convert_t o t_walkstar s' o 
          (λn. Infer_Tuvar (st.next_uvar + n))) 
          (COUNT_LIST (LENGTH targs))) = targs` by
         (qunabbrev_tac `targs'`>>
         match_mp_tac LIST_EQ>>
         fs[LENGTH_COUNT_LIST]>>rw[]>>
         fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
         fs[EVERY_EL]>>
         metis_tac[check_freevars_empty_convert_unconvert_id])>>
       fs[]>>
       imp_res_tac inc_wfs>>
       AP_TERM_TAC>>
       metis_tac[t_walkstar_no_vars,check_freevars_empty_convert_unconvert_id])
    >>
    (fs[convert_menv_def,FLOOKUP_o_f]>>
    BasicProvers.FULL_CASE_TAC>>
    `(λ x:tvarN,(tvs:num,t). (x,tvs,convert_t t)) =
     (λ x,y. (x, (λtvs,t. tvs,convert_t t) y ))` by fs[LAMBDA_PROD]>>
    fs[ALOOKUP_MAP]>>
    fs[UNCURRY,success_eqns,check_menv_def]>>
    fs[sub_completion_def]>>
    Q.SPECL_THEN [`st`,`constraints`,`s`,`targs`,`num_tvs tenvE`]
      mp_tac extend_multi_props>>
    discharge_hyps>-
      (fs[]>>metis_tac[pure_add_constraints_wfs])>>
    BasicProvers.LET_ELIM_TAC>>
    ntac 2 HINT_EXISTS_TAC>>rw[]
    >-
      (fs[SUBSET_DEF,count_def]>>rw[]>>res_tac>>DECIDE_TAC)
    >-
       metis_tac[SUBMAP_t_compat]
    (*deBruijn_subst*)
    >>
      assume_tac (db_subst_infer_subst_swap|>CONJ_PAIR|>fst)>>
      imp_res_tac FEVERY_FLOOKUP>> fs[EVERY_MEM]>>
      imp_res_tac ALOOKUP_MEM>>
      first_x_assum(qspec_then `a,y` assume_tac)>>
      Cases_on`y`>>rfs[]>>
      first_x_assum (qspecl_then [`r`,`s''`,`LENGTH targs`
        ,`st.next_uvar`,`num_tvs tenvE`] mp_tac)>>
      discharge_hyps 
      >- (rw[]>>metis_tac[check_t_more])
      >>
      rw[]>>
      imp_res_tac inc_wfs>>
      qpat_abbrev_tac `ls = MAP (convert_t o t_walkstar s'') A`>>
      `targs = ls` by 
        (match_mp_tac LIST_EQ>>
        fs[Abbr`ls`]>>CONJ_ASM1_TAC>-
          metis_tac[LENGTH_COUNT_LIST]
        >>
        fs[EL_MAP,MAP_MAP_o,LENGTH_COUNT_LIST]>>
        rw[]>>
        fs[EL_COUNT_LIST,Abbr`targs'`,EL_MAP]>>
        fs[EVERY_EL,MEM_EL]>>
        metis_tac[check_freevars_empty_convert_unconvert_id])>>
      fs[]>>
      AP_TERM_TAC>>
      metis_tac[t_walkstar_no_vars])
    )
 >-
   (*Fun*)
   (
   imp_res_tac check_freevars_to_check_t>>
   fs[sub_completion_def]>>
   imp_res_tac pure_add_constraints_success>>
   Q.SPECL_THEN [`t1`,`st`,`s`,`num_tvs tenvE`,`constraints`]
     mp_tac (GEN_ALL extend_one_props)>>
   discharge_hyps>>
   fs[LET_THM]>>
   qpat_abbrev_tac `constraints' = constraints ++A`>>
   qpat_abbrev_tac `s' = s|++B`>>
   strip_tac>>
   first_x_assum(qspecl_then[`s'`,`menv`,
     `(n,0,Infer_Tuvar st.next_uvar)::tenv`,
     `st with next_uvar:= st.next_uvar+1`,`constraints'`] mp_tac)>>
   discharge_hyps>>fs[bind_tenv_def,num_tvs_def]
   >-
     (rpt strip_tac
     >-
       (imp_res_tac check_env_more>>
       pop_assum(qspec_then `st.next_uvar +1` mp_tac)>>
       discharge_hyps>-DECIDE_TAC>>
       fs[check_env_def,check_t_def])
     >-
       (fs[SUBSET_DEF]>>rw[]>>res_tac>>DECIDE_TAC)
     >>
       (fs[tenv_inv_def,lookup_tenv_def]>>rpt strip_tac>>
       Cases_on`n=x`>>fs[deBruijn_inc0]
       >-
         (HINT_EXISTS_TAC>>fs[])
       >- res_tac
       >-
         (res_tac>>
         Q.EXISTS_TAC `t''`>>
         Cases_on`tvs>0`>>
         fs[] >>imp_res_tac check_freevars_to_check_t>>
         metis_tac[submap_t_walkstar_replace])))
   >>
   (strip_tac>>rw[success_eqns]>>
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
    metis_tac[check_freevars_empty_convert_unconvert_id,t_walkstar_no_vars]))
 >-
   (*App*)
   (first_x_assum(qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>rfs[]>>
   `MAP (convert_t o (t_walkstar s')) ts' = ts ∧ 
    EVERY (check_t (num_tvs tenvE) {}) (MAP (t_walkstar s') ts')` by
     (imp_res_tac infer_e_check_t>>
     CONJ_ASM2_TAC>>
     fs[MAP,MAP_MAP_o,MAP_EQ_f,EVERY_MEM,MEM_MAP]>>rw[]
     >>
     assume_tac (GEN_ALL check_t_less)>>
     first_x_assum(qspecl_then [`count st'.next_uvar`,`s'`,`num_tvs tenvE`] assume_tac)>>
     rfs[sub_completion_def]>>
     res_tac>>
     first_x_assum(qspec_then `y` assume_tac)>>
     `t_wfs s'` by metis_tac[infer_e_wfs,pure_add_constraints_wfs]>>fs[]>>rfs[])>>
   Q.SPECL_THEN [`ts'`,`ts`,`t`,`st'`,`s'`,`op`,`constraints'`,`num_tvs tenvE`] mp_tac
     (GEN_ALL constrain_op_complete)>>
   discharge_hyps_keep>- (fs[]>>metis_tac[infer_e_wfs])>>
   fs[]>>metis_tac[t_compat_trans])
 >- (*Log*)
   (last_x_assum(qspecl_then
     [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>rfs[]>>
   first_x_assum(qspecl_then
     [`s'`,`menv`,`tenv`,`st'`,`constraints'`] mp_tac)>>
   discharge_hyps_keep
   >-
     (rw[]>>
     metis_tac[infer_e_next_uvar_mono,check_env_more,infer_e_wfs
              ,tenv_inv_t_compat,sub_completion_wfs])
   >>
   rw[]>>simp[]>>
   qexists_tac `Infer_Tapp [] TC_bool`>>
   fs[pure_add_constraints_combine]>>
   qpat_abbrev_tac `ls = [(t,Infer_Tapp [] TC_bool);(t'',B)]`>>
   Q.SPECL_THEN [`s''`,`ls`] mp_tac pure_add_constraints_ignore>>
   discharge_hyps_keep
   >-
     (fs[Abbr`ls`,sub_completion_def,t_compat_def]>>
     imp_res_tac infer_e_check_t>>CONJ_TAC
     >-
       (qpat_assum `Tapp [] TC_bool =A` (SUBST_ALL_TAC o SYM)>>
       qpat_assum`convert_t A =B` (assume_tac o (Q.AP_TERM `unconvert_t`))>>
       first_x_assum(qspec_then `t'` (SUBST1_TAC o SYM))>>
       fs[]>>rfs[]>>
       imp_res_tac sub_completion_completes>>
       imp_res_tac check_t_empty_unconvert_convert_id>>
       fs[unconvert_t_def])
     >>
       simp[Once t_walkstar_eqn,Once t_walk_eqn,SimpRHS]>>
       imp_res_tac sub_completion_completes>>
       qpat_assum `Tapp [] TC_bool = A` 
         (assume_tac o (Q.AP_TERM `unconvert_t`))>>
       imp_res_tac check_t_empty_unconvert_convert_id>>
       fs[unconvert_t_def]>>metis_tac[])>>
  rw[]>>
  fs[sub_completion_def]>>
  pure_add_constraints_combine_tac ``st''`` ``constraints''`` ``s''``>>
  imp_res_tac infer_e_wfs>>
  fs[pure_add_constraints_append]>>
  Q.EXISTS_TAC `<|subst:=s2' ; next_uvar := st''.next_uvar |>` >>fs[]>>
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
   (last_x_assum (qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>
   rfs[]>>
   qpat_abbrev_tac `ls = [t',Infer_Tapp [] B]`>>
   pure_add_constraints_ignore_tac `s'`>-
     (fs[t_compat_def,sub_completion_def]>>
     imp_res_tac infer_e_check_t>>
     rfs[]>>
     imp_res_tac sub_completion_completes>>
     qpat_assum `A = convert_t B` 
       (assume_tac o (Q.AP_TERM `unconvert_t`))>>
     fs[unconvert_t_def]>>
     metis_tac[t_walkstar_no_vars,check_t_empty_unconvert_convert_id])>>
   fs[sub_completion_def]>>
   pure_add_constraints_combine_tac ``st'`` ``constraints'`` ``s'``>>
   imp_res_tac infer_e_wfs>>fs[]>>
   fs[pure_add_constraints_append]>>
   Q.SPECL_THEN [`num_tvs tenvE`,`si`,`s'`] assume_tac (GEN_ALL t_compat_bi_ground)>>
   rfs[Once PULL_EXISTS]>>
   CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
   qabbrev_tac `nst = <|next_uvar:=st'.next_uvar;subst:=s2'|>`>>
   qexists_tac `nst`>>
   last_x_assum(qspecl_then [`si`,`menv`,`tenv`,`nst`,`constraints'`]
     mp_tac)>>
   discharge_hyps_keep>>fs[Abbr`nst`]
   >-
    (rw[]>>fs[]>>
     metis_tac[check_env_more,infer_e_next_uvar_mono
              ,pure_add_constraints_success
              ,tenv_inv_t_compat,t_compat_trans,t_compat_def])
   >>
   rw[]>>fs[PULL_EXISTS]>>
   last_x_assum(qspecl_then [`s'''`,`menv`,`tenv`,`st'''`
                            ,`constraints'''`] mp_tac)>>
   discharge_hyps_keep
   >-
     (`st.next_uvar ≤ st'''.next_uvar` by
       (imp_res_tac infer_e_next_uvar_mono>>fs[]>>DECIDE_TAC)>>
     imp_res_tac infer_e_wfs>>fs[]>>
     metis_tac[check_env_more ,infer_e_next_uvar_mono
              ,pure_add_constraints_success,infer_e_wfs
              ,tenv_inv_t_compat,t_compat_trans,t_compat_def])
   >>
   rw[PULL_EXISTS]>>
   qunabbrev_tac`ls`>>
   qpat_abbrev_tac `ls = [(t'',t''')]`>>
   `check_t (num_tvs tenvE) {} (t_walkstar s''' t'') ∧ 
    t_walkstar s''' t'' = t_walkstar s'''' t'''` by 
      (
      CONJ_ASM1_TAC>>
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
  pure_add_constraints_combine_tac ``st''''`` ``constraints''''`` 
    ``s''''``>>
  `t_wfs s2'` by metis_tac[pure_add_constraints_wfs]>>
  imp_res_tac infer_e_wfs>>rfs[]>>fs[]>>
  fs[pure_add_constraints_append]>>
  CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
  Q.EXISTS_TAC`<|next_uvar:=st''''.next_uvar;subst:=s2'''|>`>>
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
   (last_x_assum (qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>
   rfs[]>>
   fs[UNCURRY]>>
   fs[sub_completion_def]>>
   `check_freevars (num_tvs tenvE) [] t'` by 
     (Cases_on`pes`>>fs[RES_FORALL]>>
     Cases_on`h`>>
     last_x_assum(qspec_then`q,r` assume_tac)>>
     fs[]>>
     qabbrev_tac `t1 = convert_t(t_walkstar s' t'')`>>
     Q.SPECL_THEN [`num_tvs tenvE`,`tenvC`,`q`,`t1`,`tenv'`] assume_tac 
       (fst (CONJ_PAIR infer_p_complete))>>rfs[]>>
     pop_assum(qspecl_then [`s'`,`st'`,`constraints'`] mp_tac)>>
     discharge_hyps_keep
     >-
       (fs[sub_completion_def]>>metis_tac[infer_e_wfs])
     >>
     rw[]>>
     fs[sub_completion_def]>>
     qabbrev_tac `ntenv = MAP (λ(n,t). (n,0,t)) tenv'' ++ tenv`>>
     first_x_assum(qspecl_then 
       [`s''`,`menv`,`ntenv`,`st''`,`constraints''`] mp_tac)>>
     discharge_hyps_keep>-
       (rw[]
       >-
       (fs[Abbr`ntenv`,check_env_merge]>>
       CONJ_TAC>-
        (fs[check_env_def,EVERY_MAP]>>
        imp_res_tac infer_p_check_t>>
        fs[EVERY_MEM]>>rw[]>>
        first_x_assum(qspec_then `x` assume_tac)>>rfs[]>>
        PairCases_on`x`>>fs[])
        >>
        `st.next_uvar ≤ st'.next_uvar ∧ 
         st'.next_uvar ≤ st''.next_uvar ` by 
          metis_tac[infer_e_next_uvar_mono,infer_p_next_uvar_mono]>>
        metis_tac[check_env_more])
      >-
        metis_tac[infer_p_wfs,infer_e_wfs]
      >-
        fs[num_tvs_bind_var_list]
      >>
        `t_compat s s''` by metis_tac[t_compat_trans]>>
        `t_wfs s''` by metis_tac[infer_p_wfs,pure_add_constraints_wfs]>>
        imp_res_tac tenv_inv_t_compat>>
        ntac 9 (pop_assum kall_tac)>>
        fs[tenv_inv_def,simp_tenv_inv_def]>>
        rw[]>>fs[lookup_tenv_bind_var_list]
        >-
          (BasicProvers.FULL_CASE_TAC>>fs[]>>
          metis_tac[])
        >-
          (BasicProvers.FULL_CASE_TAC>>fs[Abbr`ntenv`]>>
          fs[ALOOKUP_APPEND,ALOOKUP_MAP]>>
          Cases_on`ALOOKUP tenv'' x`>-
            (fs[]>>metis_tac[])>>
          first_x_assum(qspecl_then [`x`,`x'`] assume_tac)>>rfs[])
        >-
          (BasicProvers.FULL_CASE_TAC>>fs[]>>
          metis_tac[])
        >>
          BasicProvers.FULL_CASE_TAC>>fs[Abbr`ntenv`]
        >-
        (fs[ALOOKUP_APPEND,ALOOKUP_MAP]>>
        Cases_on`ALOOKUP tenv'' x`>-
          (fs[]>>metis_tac[])>>
        first_x_assum(qspecl_then [`x`,`x'`] assume_tac)>>rfs[])
        >>
        first_x_assum(qspecl_then [`x`,`t`] assume_tac)>>rfs[]>>
        qexists_tac`t''''`>>
        fs[ALOOKUP_APPEND,ALOOKUP_MAP])
     >>
     rw[]>>fs[]>>
     imp_res_tac infer_e_check_t>>
     imp_res_tac sub_completion_completes>>
     fs[t_compat_def,num_tvs_bind_var_list]>>rfs[]>>
     metis_tac[check_t_to_check_freevars])>>
   Q.SPECL_THEN [`t'`,`st'`,`s'`,`num_tvs tenvE`,`constraints'`] mp_tac (GEN_ALL extend_one_props)>>
  discharge_hyps>- 
    metis_tac[infer_e_wfs,pure_add_constraints_wfs]>>
  qpat_abbrev_tac `s'' = s'|++A`>>
  Q.ABBREV_TAC `constraints'' = constraints'++[Infer_Tuvar st'.next_uvar,unconvert_t t']`>>
  rfs[LET_THM]>>
  imp_res_tac pure_add_constraints_success>>
  rw[]>>
  qpat_abbrev_tac `st'' = st' with next_uvar := A`>>
  `sub_completion (num_tvs tenvE) st''.next_uvar st''.subst constraints'' s''` by fs[sub_completion_def,Abbr`st''`]>>
   assume_tac (GEN_ALL infer_pes_complete)>>
   pop_assum (qspecl_then
     [`st.next_uvar`,`tenvE`,`tenvC`,`tenv`,`Infer_Tuvar st'.next_uvar`
     ,`t'`,`t''`,`convert_t (t_walkstar s' t'')`
     ,`menv`,`pes`,`st''`,`constraints''`,`s''`] mp_tac)>>
   discharge_hyps>-
     (fs[Abbr`st''`,sub_completion_def]>>
     CONJ_ASM1_TAC>-metis_tac[infer_e_wfs]>>
     fs[]>>rw[]
     >-
       (imp_res_tac infer_e_next_uvar_mono>>
       DECIDE_TAC)
     >-
       metis_tac[tenv_inv_t_compat,SUBMAP_t_compat]
     >-
       (`count (st'.next_uvar) ⊆ count(st'.next_uvar+1)` by
         (fs[SUBSET_DEF,count_def]>>DECIDE_TAC)>>
       metis_tac[SUBSET_TRANS])
     >>
       imp_res_tac infer_e_check_t>>
       imp_res_tac sub_completion_completes>>
       metis_tac[check_t_empty_unconvert_convert_id,submap_t_walkstar_replace])>> 
  rw[]>>
  HINT_EXISTS_TAC>>fs[sub_completion_def]>>
  Q.LIST_EXISTS_TAC [`s'''`,`constraints'''`]>>fs[]>>
  CONJ_TAC>-metis_tac[t_compat_trans,SUBMAP_t_compat]>>
  fs[t_compat_def]>>
  pop_assum(qspec_then `Infer_Tuvar st'.next_uvar` assume_tac)>>rfs[]>>
  metis_tac[t_walkstar_no_vars,check_freevars_empty_convert_unconvert_id,check_freevars_to_check_t])
 >- (*Let*)
   (last_x_assum(qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>
   rfs[]>>
   Cases_on `n`>>fs[opt_bind_def]
   >-
     (first_x_assum(qspecl_then [`s'`,`menv`,`tenv`,`st'`,`constraints'`] assume_tac)>>
     rfs[opt_bind_tenv_def]>>
     `t_wfs st'.subst` by 
       imp_res_tac infer_e_wfs>>
     imp_res_tac sub_completion_wfs>>
     imp_res_tac tenv_inv_t_compat>>fs[]>>
     `st.next_uvar ≤ st'.next_uvar` by metis_tac[infer_e_next_uvar_mono]>>
     imp_res_tac check_env_more>>fs[]>>
     ntac 2 HINT_EXISTS_TAC>>
     fs[]>>metis_tac[t_compat_trans])
   >>
    `t_wfs st'.subst` by metis_tac[infer_e_wfs]>>
    `t_wfs s'` by metis_tac[sub_completion_wfs]>>
    first_x_assum(qspecl_then[`s'`,`menv`,
      `(x,0,t'')::tenv`,
      `st'`,`constraints'`] mp_tac)>>
    discharge_hyps>>fs[opt_bind_tenv_def,num_tvs_def]
    >-
      (rpt strip_tac
      >-
        (imp_res_tac infer_e_check_t>>
         imp_res_tac infer_e_next_uvar_mono>>
         fs[check_env_def]>>
         fs[EVERY_MEM,FORALL_PROD]>>rw[]>>
         res_tac>>
         `count st.next_uvar ⊆ count st'.next_uvar` by
           (fs[count_def,SUBSET_DEF]>>rw[]>> DECIDE_TAC)>>
         metis_tac[check_t_more5,count_def])
      >>
         fs[tenv_inv_def,lookup_tenv_def]>>
         ntac 4 strip_tac>>
         Cases_on`x=x'`>>fs[deBruijn_inc0]
         >-
           (imp_res_tac infer_e_check_t>>
           assume_tac (GEN_ALL check_t_less)>>
           pop_assum (Q.SPECL_THEN [`count st'.next_uvar`,`s'`,`num_tvs tenvE`]assume_tac)>>
           fs[sub_completion_def]>>
           res_tac>>
           `check_t (num_tvs tenvE) {} (t_walkstar s' t'')` by 
             metis_tac[COMPL_INTER]>>
           CONJ_TAC 
           >-
             metis_tac[check_t_to_check_freevars]
           >>
             qpat_assum `convert_t A = B` (assume_tac o Q.AP_TERM `unconvert_t`)>>
             metis_tac[check_t_empty_unconvert_convert_id])
         >>
         (res_tac>>
         Cases_on`tvs>0`>>fs[]>>
         TRY (CONJ_TAC>-(HINT_EXISTS_TAC>>fs[]))>>
         imp_res_tac check_freevars_to_check_t
         >-
           (fs[EQ_SYM_EQ]>>
           metis_tac[t_walkstar_no_vars])
         >>
           fs[t_compat_def]>>
           first_x_assum(qspec_then `t''''` (SUBST_ALL_TAC o SYM))>>
           metis_tac[t_walkstar_no_vars]))
     >>
       rw[]>>simp[]>>
       ntac 2 HINT_EXISTS_TAC>>fs[]>>metis_tac[t_compat_trans])
 >-
   (*Letrec
   use type_funs_lookup and type_funs_Tfn to get an inversion and extend the sub_completed map with LENGTH n funs
   not sure about order yet..
   *)
   (imp_res_tac type_funs_MAP_FST>>
   imp_res_tac type_funs_distinct>>
   `MAP (λx,y,z. x) funs = MAP FST funs` by
     fs[MAP_EQ_f,FORALL_PROD]>>
   fs[bind_var_list_def]>>
   qpat_abbrev_tac `new_tenv = A ++ tenv`>>
   fs[sub_completion_def] >>
   (*
   qabbrev_tac `fun_tys = MAP (THE o (ALOOKUP env) o FST) funs`>>*)
   qabbrev_tac `fun_tys = MAP SND env` >>
   Q.SPECL_THEN [`st`,`constraints`,`s`,`fun_tys`,`num_tvs tenvE`] 
     mp_tac extend_multi_props>>
   discharge_hyps_keep
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
   BasicProvers.LET_ELIM_TAC>>
   qpat_abbrev_tac `st' = st with next_uvar:=A`>>
   last_x_assum(qspecl_then [`s'`,`menv`,`new_tenv`,`st'`
                            ,`constraints++new_constraints`] mp_tac)>>
   discharge_hyps_keep>-
     (fs[Abbr`st'`,num_tvs_bind_var_list]>>
     `LENGTH env = LENGTH funs` by metis_tac[LENGTH_MAP]>>
     rw[Abbr`fun_tys`]
     >-
       (fs[Abbr`new_tenv`]>>
       simp[check_env_merge]>>CONJ_TAC
       >-
         (fs[check_env_def]>>
         qpat_abbrev_tac `ls = MAP (λn.Infer_Tuvar(n+st.next_uvar))A` >>
         `LENGTH funs = LENGTH ls` by 
           metis_tac[LENGTH_MAP,LENGTH_COUNT_LIST]>>
         simp[EL_MAP,EL_ZIP,MAP2_MAP,EVERY_EL]>>
         rw[Abbr`ls`]>>
         fs[EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST]>>
         qpat_abbrev_tac `x= EL n funs`>>
         PairCases_on`x`>>fs[check_t_def,EL_COUNT_LIST])
       >>
         imp_res_tac check_env_more>>
         pop_assum(qspec_then `LENGTH funs + st.next_uvar` mp_tac)>>
         discharge_hyps>-DECIDE_TAC>>fs[])
     >-
       (fs[SUBSET_DEF]>>rw[]>>res_tac>>DECIDE_TAC)
     >>
       `t_compat s s'` by metis_tac[SUBMAP_t_compat]>>
       imp_res_tac tenv_inv_t_compat>>
       ntac 5 (pop_assum kall_tac)>>
       fs[tenv_inv_def,Abbr`new_tenv`]>>
       qpat_abbrev_tac `ls = MAP2 (λ(f,x,e) uvar. (f,0:num,uvar)) funs
                            (MAP (λn. Infer_Tuvar (st.next_uvar + n))
                            (COUNT_LIST (LENGTH funs)))`>>
       `LENGTH ls = LENGTH funs` by
         fs[Abbr`ls`,LENGTH_MAP2,LENGTH_COUNT_LIST]>>
       `!n. n < LENGTH ls ⇒
        EL n ls =  
        (λ(f,x,e). (f,0,Infer_Tuvar (st.next_uvar+n))) (EL n funs)` by
          (rw[Abbr`ls`]>>
          fs[MAP2_MAP,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP]>>
          qabbrev_tac `v = EL n funs`>>PairCases_on`v`>>
          fs[EL_COUNT_LIST])>>
       `!k. ALOOKUP env k = NONE ⇒  ALOOKUP ls k = NONE` by
         (rw[]>>
         SPOSE_NOT_THEN assume_tac>>
         `?v. ALOOKUP ls k  = SOME v` by
           metis_tac[NOT_SOME_NONE]>>
         imp_res_tac ALOOKUP_MEM>>
         fs[MEM_EL]>>
         fs[ALOOKUP_NONE]>>
         first_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
         Cases_on`EL n funs`>>Cases_on`r`>>fs[]>>
         `MEM q (MAP FST funs)` by 
           (fs[MEM_MAP,MEM_EL,EXISTS_PROD]>>
           metis_tac[])>>
         metis_tac[])>>
       rw[]>>fs[lookup_tenv_bind_var_list]
        >-
          (BasicProvers.FULL_CASE_TAC>>fs[]>>
          metis_tac[])
        >-
          (BasicProvers.FULL_CASE_TAC>>
          fs[ALOOKUP_APPEND,ALOOKUP_MAP]>>
          metis_tac[])
        >-
          (BasicProvers.FULL_CASE_TAC>>fs[]>>
          metis_tac[type_funs_Tfn])
        >>
        BasicProvers.FULL_CASE_TAC>>fs[ALOOKUP_APPEND]
        >-
          metis_tac[]
        >>
          imp_res_tac ALOOKUP_MEM>>
          `MEM x (MAP FST env)` by 
            (fs[EXISTS_PROD,MEM_MAP]>>metis_tac[])>>
          qpat_assum `A = MAP FST env` (SUBST_ALL_TAC o SYM)>>
          fs[MEM_MAP,MEM_EL]>>
          first_x_assum(qspec_then `n'` assume_tac)>>rfs[]>>
          Cases_on`EL n' funs`>>Cases_on`r`>>fs[]>>
          `n' < LENGTH ls` by fs[]>>
          imp_res_tac EL_MEM>>rfs[]>>
          imp_res_tac ALOOKUP_ALL_DISTINCT_MEM>>
          pop_assum mp_tac>>discharge_hyps>>
          `MAP FST ls = MAP FST funs` by
          (rw[Abbr`ls`,MAP2_MAP,LENGTH_COUNT_LIST,MAP_ZIP]>>
          match_mp_tac LIST_EQ>>CONJ_ASM1_TAC
          >-
            fs[LENGTH_ZIP,LENGTH_COUNT_LIST]
          >>
          rw[]>>fs[EL_MAP,EL_ZIP,LENGTH_COUNT_LIST]>>
          Cases_on`EL x funs`>>Cases_on`r`>>fs[])>>
          fs[]>>
          rw[Abbr`targs`]>>
          fs[EL_MAP]>>
          `n = n'` by 
            (`q = EL n (MAP FST env)` by 
              (fs[EL_MAP]>>
              qpat_assum`A = EL n env` (SUBST1_TAC o SYM)>>
              fs[])>>
            imp_res_tac type_funs_MAP_FST >>
            pop_assum (SUBST_ALL_TAC o SYM)>>
            `q = EL n' (MAP FST funs)` by
              (FULL_SIMP_TAC arith_ss [EL_MAP])>>
            fs[]>>
            Q.ISPEC_THEN `MAP FST funs`assume_tac EL_ALL_DISTINCT_EL_EQ>>
            pop_assum (assume_tac o (fst o EQ_IMP_RULE)) >>rfs[]>>
            metis_tac[])>>
         fs[]>>
         qpat_assum `A = EL n' env` (SUBST1_TAC o SYM)>>
         fs[])>>
   qunabbrev_tac `fun_tys`>>
   rw[]>>
   fs[PULL_EXISTS]>>
   qpat_abbrev_tac `ls=ZIP(MAP (λn.Infer_Tuvar(st.next_uvar+n))A,env')`>>
   imp_res_tac infer_funs_length>>
   fs[LENGTH_COUNT_LIST]>>
   pure_add_constraints_ignore_tac `s''`>-
     (fs[t_compat_def,EVERY_MEM,LENGTH_COUNT_LIST,MEM_ZIP]>>rw[]>>
     fs[LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST]>>
     `LENGTH funs = LENGTH env` by
       (qpat_assum `MAP FST funs = B` (assume_tac o Q.AP_TERM`LENGTH`)>>
       fs[LENGTH_MAP])>>
    imp_res_tac infer_e_check_t>>
    first_x_assum(qspec_then `Infer_Tuvar (st.next_uvar+n)` (SUBST_ALL_TAC o SYM))>>
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
     metis_tac[t_walkstar_no_vars])>>
   pure_add_constraints_combine_tac ``st''`` ``constraints''`` ``s''``>>
   pop_assum mp_tac >>discharge_hyps_keep>- 
     metis_tac[infer_e_wfs]>> 
   rw[]>>
   Q.SPECL_THEN [`num_tvs tenvE`,`si`,`s''`] assume_tac (GEN_ALL t_compat_bi_ground)>>
   rfs[num_tvs_bind_var_list]>>
   fs[pure_add_constraints_append]>>
   CONV_TAC (RESORT_EXISTS_CONV List.rev)>>
   qabbrev_tac`nst = <|next_uvar:=st''.next_uvar;subst:=s2'''|>`>>
   qexists_tac`nst`>>
   first_x_assum(qspecl_then [`si`,`menv`,`new_tenv`
                             ,`nst`,`constraints''`] mp_tac)>>
   discharge_hyps>-
     (imp_res_tac infer_e_next_uvar_mono>>
     fs[Abbr`st'`,Abbr`nst`]>>
     metis_tac[check_env_more,pure_add_constraints_wfs
              ,pure_add_constraints_success
              ,tenv_inv_t_compat,t_compat_def,t_compat_trans])>>
   rw[]>>
   Q.LIST_EXISTS_TAC [`constraints'''`,`s'''`,`st'''`,`t'`]>>
   fs[Abbr`nst`]>>
   metis_tac[t_compat_trans,SUBMAP_t_compat])
 >- 
   (ntac 2 HINT_EXISTS_TAC>>fs[]>>metis_tac[sub_completion_wfs,t_compat_refl])
 >-
   (last_x_assum(qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>
   rfs[]>>
   last_x_assum(qspecl_then [`s'`,`menv`,`tenv`,`st'`,`constraints'`] mp_tac)>>
   discharge_hyps>>fs[]
   >- metis_tac[t_compat_def,tenv_inv_t_compat,infer_e_wfs,check_env_more,infer_e_next_uvar_mono]>>
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
 >>
  (*similar to Fun*)
   fs[check_freevars_def]>>
   fs[sub_completion_def]>>
   imp_res_tac pure_add_constraints_success>>
   Q.SPECL_THEN [`t1`,`st`,`s`,`num_tvs tenvE`,`constraints`]
     mp_tac (GEN_ALL extend_one_props)>>
   discharge_hyps>>
   fs[LET_THM]>>
   qpat_abbrev_tac `constraints' = constraints ++A`>>
   qpat_abbrev_tac `s' = s|++B`>>
   strip_tac>>
   last_x_assum(qspecl_then[`s'`,`menv`,
     `(n,0,Infer_Tuvar st.next_uvar)::tenv`,
     `st with next_uvar:= st.next_uvar+1`,`constraints'`] mp_tac)>>
   discharge_hyps_keep>>fs[bind_tenv_def,num_tvs_def]
   >-
     (rw[]
     >-
       (imp_res_tac check_env_more>>
       fs[check_env_def,check_t_def])
     >-
       (fs[count_def,SUBSET_DEF]>>rw[]>>
       `x < st.next_uvar` by metis_tac[]>>
       DECIDE_TAC)
     >>
      (fs[tenv_inv_def,lookup_tenv_def]>>rpt strip_tac>>
       Cases_on`n=x`>>fs[deBruijn_inc0]
       >-
         metis_tac[]
       >- res_tac
       >>
         first_x_assum(qspecl_then [`x`,`tvs`,`t'`] assume_tac)>>rfs[]>>
         Cases_on`tvs>0`>>
         fs[] >>imp_res_tac check_freevars_to_check_t>>
         metis_tac[submap_t_walkstar_replace]))>>   
   rw[]>>
   fs[PULL_EXISTS]>>
   first_x_assum(qspecl_then[`s''`,`menv`,
     `tenv`,`st''`,`constraints''`] mp_tac)>>
   discharge_hyps_keep>> fs[]
   >-
     (rw[]
     >-
       (`st.next_uvar ≤ st''.next_uvar` by 
         (imp_res_tac infer_e_next_uvar_mono>>
         fs[]>>DECIDE_TAC)>>
       metis_tac[check_env_more])
     >-
       metis_tac[infer_e_wfs,infer_st_rewrs]
     >>
       metis_tac[SUBMAP_t_compat,t_compat_trans
                ,t_compat_def,tenv_inv_t_compat])
   >>
   rw[]>>
   ntac 4 HINT_EXISTS_TAC>>fs[]>>
   CONJ_ASM1_TAC>-metis_tac[SUBMAP_t_compat,t_compat_trans]>>
   fs[t_compat_def]>>
   simp[Once t_walkstar_eqn,convert_t_def,SimpRHS,Once t_walk_eqn]>>
   CONJ_TAC
   >-
     (ntac 2 (last_x_assum(qspec_then `st.next_uvar` assume_tac))>>
     rfs[]>>
     metis_tac[t_walkstar_no_vars,check_freevars_empty_convert_unconvert_id])
   >>
     imp_res_tac infer_e_check_t>>
     rfs[]>>
     imp_res_tac sub_completion_completes>>
     AP_TERM_TAC>>metis_tac[t_walkstar_no_vars])
     
val _ = export_theory ();
