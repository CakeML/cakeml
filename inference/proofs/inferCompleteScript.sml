open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;

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

val t_walkstar_tuvar_props = prove(
``t_wfs s 
  ⇒
  (uv ∉ FDOM s ⇔  t_walkstar s (Infer_Tuvar uv) = Infer_Tuvar uv)``,
  rw[EQ_IMP_THM]
  >-
    (fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
    imp_res_tac flookup_thm>>fs[])
  >>
    imp_res_tac t_walkstar_vars_notin>>
    pop_assum (Q.SPECL_THEN [`uv`,`Infer_Tuvar uv`] mp_tac)>>
    fs[t_vars_eqn])


(*COMPAT for t_unification
  Note that the order is swapped: 
  t_compat s s' is s << s'
*)
val t_compat_def = Define`
  t_compat s s' ⇔
  t_wfs s ∧ t_wfs s' ∧
  !t. t_walkstar s' (t_walkstar s t) = t_walkstar s' t`

val t_compat_refl = prove(
``t_wfs s ⇒ t_compat s s``,
  rw[t_compat_def]>>fs[t_walkstar_SUBMAP])

val t_compat_trans = prove(
``t_compat a b ∧ t_compat b c ⇒ t_compat a c``,
  rw[t_compat_def]>>metis_tac[])

val SUBMAP_t_compat = prove(
``t_wfs s' ∧ s SUBMAP s' ⇒ t_compat s s'``,
  rw[t_compat_def]
  >-
    metis_tac[t_wfs_SUBMAP]>>
  fs[t_walkstar_SUBMAP])

(*t_compat is preserved under certain types of unification
  Proof basically from HOL*)
val t_compat_eqs_t_unify = prove(
``!s t1 t2 sx.
    t_compat s sx ∧ (t_walkstar sx t1 = t_walkstar sx t2)
    ⇒ 
    ?si. (t_unify s t1 t2 = SOME si) ∧ t_compat si sx``,
  rw[t_compat_def]>>
  Q.ISPECL_THEN [`t2`,`t1`,`sx`,`s`] assume_tac (GEN_ALL eqs_t_unify)>>
  rfs[]>>
  CONJ_ASM1_TAC>-metis_tac[t_unify_wfs]>>
  rw[]>>
  Q.ISPECL_THEN [`s`,`t1`,`t2`,`sx'`,`sx`] assume_tac t_unify_mgu>>
  rfs[])


(* End unification stuff *)


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

(*TODO: This may be too specific to the Var case, it provides a witness to 
  pure_add_constraints where we unify with unbound unification vars with tyvars*)
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

(*
val new_uvars_sub_completion_exists = Q.prove (
`!s constraints s' ts next_uvar.
  t_wfs s ∧
  EVERY (check_t 0 (count next_uvar)) ts ∧
  check_s 0 (count next_uvar) s ∧
  sub_completion 0 next_uvar s constraints s'
  ⇒
  ∃s''.
    sub_completion 0 (next_uvar + LENGTH ts) s
      (constraints++ZIP
         (MAP (λn. Infer_Tuvar (next_uvar + n))
            (COUNT_LIST (LENGTH ts)),ts)) s''`,

 rw [sub_completion_def, pure_add_constraints_append] >>
 rw [PULL_EXISTS] >>
 rw [Once SWAP_EXISTS_THM] >>
 qexists_tac `s'` >>
 rw []


 induct_on `constraints` >>
 rw [] >>
 >- (


 fs [sub_completion_def] >>
 PairCases_on `h` >>
 fs [pure_add_constraints_def] >>
 FIRST_X_ASSUM match_mp_tac >>
 qexists_tac `s'` >>
 rw [] >>
 metis_tac [{{{{{{{{{{{, t_unify_check_s]);

 rw [ZIP_COUNT_LIST, LENGTH_COUNT_LIST]

*)

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


(*For cases where the substitution is exactly known
we can always partially constrain the pre-map in some way
val pure_add_constraints_sublist_exists = prove(
``
!s constraints s' ts ts'.
t_wfs s ∧
pure_add_constraints s constraints s' ∧
MAP (t_walkstar s') ts = ts'
⇒
?s''.
pure_add_constraints s (ZIP(ts,ts')) s''``, 
  cheat)
*)


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
  t' = t_walkstar s t ⇒ 
  t_unify s t t' = SOME s) ∧
  (!s ts ts'.
  t_wfs s ⇒ 
  ts' = MAP (t_walkstar s) ts ⇒ 
  ts_unify s ts ts' = SOME s)``, 
  ho_match_mp_tac t_unify_strongind>>rw[]>>
  fs[t_unify_eqn]>-
  (BasicProvers.FULL_CASE_TAC>>
  imp_res_tac t_walk_submap_walkstar>>fs[]>>
  qpat_assum `t_walkstar s t = X` mp_tac>>
  fs[t_walkstar_eqn]>>every_case_tac>>fs[]>>
  metis_tac[])>>
  Cases_on`ts`>>fs[ts_unify_def])

val pure_add_constraints_ignore = prove(
``!s ls. t_wfs s ⇒ 
  pure_add_constraints s (ZIP (ls,MAP (t_walkstar s) ls)) s``,
  strip_tac>>Induct>>
  fs[pure_add_constraints_def]>>
  rw[]>>
  fs[t_unify_eqn,t_walk_submap_walkstar]>>
  Cases_on`t_walk s h`>>
  fs[t_walkstar_eqn]>>
  imp_res_tac t_unify_ignore>>
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

(*Double sided t_compat thm*)
val t_compat_bi_ground = prove(
``(!uv. uv ∈ FDOM a ⇒ check_t n {} (t_walkstar a (Infer_Tuvar uv))) ∧
  t_compat a b ∧ 
  t_compat b a
  ⇒
  FDOM a = FDOM b ∧ 
  (!uv. uv ∈ FDOM b ⇒ check_t n {} (t_walkstar b (Infer_Tuvar uv)))``,
  strip_tac>>
  CONJ_ASM2_TAC
  >-
    (fs[EXTENSION]>>
    rw[EQ_IMP_THM]>>
    imp_res_tac t_compat_ground>>
    res_tac>> metis_tac[])
  >>
    fs[t_compat_def]>>
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
    (*Q.SPECL_THEN [`st.subst`,`constraints`,`s`,`ts'`,`MAP unconvert_t ts`] assume_tac
      pure_add_constraints_sublist_exists>>*)
  rfs[]>>
  imp_res_tac pure_add_constraints_wfs>>
  fs[constrain_op_def,type_op_cases]>>
  BasicProvers.EVERY_CASE_TAC>>
  ntac 2 (fs[unconvert_t_def,MAP]>>rw[])>>
  fs[add_constraint_success,success_eqns,sub_completion_def]
 >-
    (*int->int->int*)
    (
     ntac 2 (qpat_assum `convert_t A = B` (assume_tac o (Q.AP_TERM `unconvert_t`)))>>
     imp_res_tac check_t_empty_unconvert_convert_id>>
     fs[unconvert_t_def]>>
     Q.EXISTS_TAC `Infer_Tapp [] TC_int`>>
     imp_res_tac pure_add_constraints_success>>
     fs[pure_add_constraints_combine]>>
     qpat_abbrev_tac `ls = [(h,Infer_Tapp [] TC_int);(h',B)]`>>
     imp_res_tac t_compat_pure_add_constraints_1>>
     pop_assum(qspec_then `ls` mp_tac)>> miscLib.discharge_hyps
     >-
       (unabbrev_all_tac>>fs[t_walkstar_eqn,t_walk_eqn])
     >>
    rw[]>>
    Q.EXISTS_TAC `<|subst:=si ; next_uvar := st.next_uvar |>` >>fs[]>>
    fs[pure_add_constraints_combine]>>
    imp_res_tac pure_add_constraints_success>>
    imp_res_tac t_compat_eqs_t_unify>>
    first_x_assum(qspecl_then [`h`,`Infer_Tapp [] TC_int`] mp_tac)>>
    miscLib.discharge_hyps>-
    (fs[SimpLHS,t_walkstar_eqn,t_walk_eqn]>>metis_tac[])>>
    rw[]>>
    assume_tac (Q.SPEC `s` pure_add_constraints_ignore)>>
    `pure_add_constraints st.subst (constraints++ls) s` by
      (fs[pure_add_constraints_append]>>
      Q.EXISTS_TAC`s`>>
      fs[Abbr`ls`]>>
      first_x_assum(qspec_then `[h;h']` assume_tac)>>
      fs[]>>metis_tac[])>>
    Q.SPECL_THEN [`s`,`st.subst`,`ls`,`constraints`] assume_tac pure_add_constraints_swap>>
    rfs[]>>
    Q.EXISTS_TAC`si''`>>
    Q.EXISTS_TAC`constraints`>>
    Q.SPECL_THEN [`n`,`si''`,`s`] assume_tac (GEN_ALL t_compat_bi_ground)>>
    rfs[]>>
    fs[pure_add_constraints_append]>>
    `si = s2'` by metis_tac[pure_add_constraints_functional]>>
    rw[]
    >-
      metis_tac[pure_add_constraints_success]
    >>
      `t_wfs si''` by metis_tac[pure_add_constraints_wfs]>>
      fs[pure_add_constraints_wfs,convert_t_def,t_walkstar_eqn,t_walk_eqn]
    )
  >- (*int->int->bool*)
    cheat
  >- (*Opapp --> Example with fresh unification variable*)
    (qpat_abbrev_tac `ls = [(h,Infer_Tapp B C)]`>>
    Q.ABBREV_TAC `constraints' = constraints++
                 [Infer_Tuvar st.next_uvar,unconvert_t t]`>>
    Q.SPECL_THEN [`s`,`[t]`,`st.next_uvar`,`n`] 
      mp_tac pure_add_constraints_exists>>
    miscLib.discharge_hyps>-
      (fs[check_t_def]>>
      imp_res_tac check_t_to_check_freevars>>
      rfs[check_freevars_def])>>
    fs[LET_THM,EVAL``COUNT_LIST 1``]>>
    qpat_abbrev_tac `s' = s|++ A`>>strip_tac>>
    `pure_add_constraints st.subst constraints' s'` by
      metis_tac[pure_add_constraints_append]>>
    imp_res_tac pure_add_constraints_success>>
    Q.SPECL_THEN [`ls`,`st.subst`,`s'`] mp_tac t_compat_pure_add_constraints_1>>
    (*should factor this bit out.. probably common across all*)
    qpat_assum `convert_t A = B` (assume_tac o (Q.AP_TERM `unconvert_t`))>>
    imp_res_tac check_t_empty_unconvert_convert_id>>
    fs[unconvert_t_def]>>
    miscLib.discharge_hyps
    >-
      (fs[Abbr`ls`]>>cheat) (*true using s SUBMAP s' and t_walkstar s h = ... *)
    >>
      rw[]>>
      Q.EXISTS_TAC`<|subst:=si ; next_uvar:= st.next_uvar+1|>`>>fs[]>>
      assume_tac (Q.SPEC `s'` pure_add_constraints_ignore)>>
      `pure_add_constraints st.subst (constraints'++ls) s'` by
        (fs[pure_add_constraints_append]>>
        Q.EXISTS_TAC`s'`>>fs[]>>
        fs[Abbr`ls`]>>
        cheat)>> (*Probably looks the same as the cheat above because s' is complete*)
      Q.SPECL_THEN [`s'`,`st.subst`,`ls`,`constraints'`] mp_tac pure_add_constraints_swap>>
      rw[]>>
      Q.EXISTS_TAC`si'`>>
      Q.EXISTS_TAC`constraints'`>>
      Q.SPECL_THEN [`n`,`si'`,`s'`] mp_tac (GEN_ALL t_compat_bi_ground)>>
      miscLib.discharge_hyps_keep>>
        (fs[]>>cheat)>> (*true by construction of s'*)
      strip_tac>>
      rfs[]>>
     cheat)
  >> 
    cheat)

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

val infer_e_complete = Q.prove (
`(!tenvM tenvC tenvE e t. 
   type_e tenvM tenvC tenvE e t
   ⇒
   !s menv tenv st constraints.
     (*These two might be a consequence of the others*)
     check_menv menv ∧ 
     check_env (count st.next_uvar) tenv ∧ 
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion (num_tvs tenvE) st.next_uvar st.subst constraints s ∧
     (*I think these conditions are reasonable... the second one maybe not*)
     FDOM st.subst ⊆ count st.next_uvar ∧ 
     (*This constrains constraints to only constrain the necessary unification variables*)
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
       t_walkstar_sub_eq s s' ∧  
       MAP SND env = MAP (convert_t o t_walkstar s') env')`,
 ho_match_mp_tac type_e_strongind >>
 rw [success_eqns,infer_e_def]
 (*Easy cases*)
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [t_compat_refl])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
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
    (*first_x_assum(qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    `t_wfs st'.subst /\ t_wfs s'` by metis_tac[infer_e_wfs,sub_completion_wfs]>>
     miscLib.specl_args_of_then ``t_unify`` (Q.GENL [`t2`,`t1`,`s`] (SPEC_ALL t_unify_eqn)) assume_tac>>rfs[t_walk_eqn]>>
    fs[t_walkstar_eqn]>>
    Cases_on`t'`>>
   infer_e_check_t
    fs[convert_t_def,t_walk_eqn]>-
      (fs[ts_unify_def]>>
      Q.ABBREV_TAC`unc_t = unconvert_t t`>>
      Cases_on`t`>>fs[check_freevars_def]>>cheat)>>
      (*put in substitutions = unconvert_t t on st'.next_uvar*)
    fs[Once t_vwalk_eqn]
    Cases_on`t_vwalk st'.subst n`>>
    qpat_assum `Tapp [] TC_exn = Y` (assume_tac o Q.AP_TERM `unconvert_t`)>>
    fs[unconvert_t_def]
    check_freevars_empty_convert_unconvert_id
      fs[]
    fs[Once t_vwalk_eqn]
    fs[t_ext_s_check_eqn
      fs[sub_completion_def] 

    imp_res_tac t_walkstar_eqn>>
    last_x_assum(qspec_then `t'` SUBST_ALL_TAC)>>
   fs[t_walk_eqn]

   `t_walkstar st'.subst t' = Infer_Tapp [] TC_exn` by cheat 


    inferSoundTheory.infer_e_sound
    reverse(Cases_on`t_walkstar s' t'`) >>
    fs[convert_t_def] >- (
      fs[sub_completion_def] >>
      `t_walkstar s' t' = t_walkstar s' (Infer_Tuvar n)` by cheat >> soundness
      `t_unify st'.subst t' (Infer_Tapp [] TC_exn) =
       t_unify st'.subst (t_walkstar s' t') (Infer_Tapp [] TC_exn)` by cheat >>
      `t_unify st'.subst (Infer_Tapp [] TC_exn) (Infer_Tapp [] TC_exn) = SOME st'.subst` by cheat
      simp[] >>
      set the constraints to bind st'.next_uvar to t, figure out what the resulting sub_completion should be
      simp[t_walkstar_eqn]
      simp[t_unify_eqn]
      print_apropos``unify s x x = SOME s`` make unify_same into t_unify_same
      `
      print_find"walkstar_idem"
      print_find"t_walkstar_eqn"
      fs[check_t_def]

    imp_res_tac sub_completion_wfs
    rw[t_unify_eqn]
    
    def, encode_infer_t_def, decode_infer_t_def]
    *) cheat
 >- (*Handler*)
    cheat
 >- (*Con*)
    cheat
 >- (*Con*)
    cheat

 >- (*Var*)
    (Cases_on `n` >>
     rw [success_eqns, infer_e_def] >>
     fs [t_lookup_var_id_def, tenv_inv_def]
     >- (*Short*)
        (res_tac >>
         rw [success_eqns] >>
         rw [Once SWAP_EXISTS_THM] >>
	       qexists_tac `constraints++(ZIP 
	       (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST (LENGTH targs))
         ,MAP unconvert_t targs))`>>
         `t_wfs s` by metis_tac[sub_completion_wfs]>>
	       fs[sub_completion_def,pure_add_constraints_append]>>
         fs[PULL_EXISTS,Once SWAP_EXISTS_THM]>>
         imp_res_tac check_freevars_to_check_t>>
         HINT_EXISTS_TAC>>fs[]>>
         assume_tac pure_add_constraints_exists>>
         pop_assum(qspecl_then [`s`,`targs`,`st.next_uvar`,`num_tvs tenvE`] assume_tac)>>
         rfs[LET_THM,MAP_MAP_o,combinTheory.o_DEF]>>
         HINT_EXISTS_TAC>>fs[]>>
         imp_res_tac pure_add_constraints_wfs>>
         qpat_abbrev_tac `s' = s|++ ls`>>
         `s SUBMAP s'` by 
           (unabbrev_all_tac>>
           match_mp_tac SUBMAP_FUPDATE_LIST_NON_EXIST>>
           fs[MAP_ZIP,LENGTH_COUNT_LIST]>>
           fs[INTER_DEF,MEM_MAP,MEM_COUNT_LIST,EXTENSION]>>
           rw[] >>DECIDE_TAC)>>
         CONJ_ASM1_TAC>-
         (rw[]>-
         (unabbrev_all_tac>>
         fs[FDOM_FUPDATE_LIST,SUBSET_DEF,MAP_ZIP,LENGTH_COUNT_LIST]>>
         fs[MEM_MAP,MEM_COUNT_LIST]>>rw[]>>
         Cases_on`x<st.next_uvar`>>fs[]>>
         imp_res_tac arithmeticTheory.LESS_ADD>>
         Q.EXISTS_TAC `LENGTH targs - p`>>
         DECIDE_TAC)>-
         (imp_res_tac t_walkstar_SUBMAP>>
         first_x_assum (qspec_then `(Infer_Tuvar uv)` assume_tac)>>
         fs[]>>
         Cases_on`uv < st.next_uvar`
         >-
           (res_tac>>
           imp_res_tac t_walkstar_no_vars>>fs[]) >>
	      `uv ∉ FDOM s ∧ FLOOKUP s uv = NONE` by fs[flookup_thm]>>
         fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
         fs[Once t_vwalk_eqn]>>
         BasicProvers.FULL_CASE_TAC>-
           fs[flookup_thm]>>
         `t_walkstar s' x = x ∧ check_t (num_tvs tenvE) {} x` by 
           (
           CONJ_ASM2_TAC
           >-
             metis_tac[t_walkstar_no_vars]
           >>
           fs[Abbr`s'`,flookup_fupdate_list]>>
           pop_assum mp_tac>>
           BasicProvers.FULL_CASE_TAC>>
           imp_res_tac ALOOKUP_MEM>>
           fs[MEM_REVERSE]>>
           fs[LENGTH_COUNT_LIST,MEM_ZIP,EL_MAP]>>
           fs[EVERY_MEM,MEM_EL]>>res_tac>>
           strip_tac>>
           metis_tac[check_freevars_empty_convert_unconvert_id
                    ,check_freevars_to_check_t])>>
        Cases_on`x`>> fs[check_t_def]>>
        fs[EVERY_MEM,MEM_MAP]>>rw[]>>
        first_x_assum (qspec_then `y` mp_tac)>>
        metis_tac[t_walkstar_no_vars]))>>
       rw[]>-
       (fs[SUBSET_DEF,count_def]>>rw[]>>res_tac>>DECIDE_TAC)>-
       (unabbrev_all_tac>>
       fs[FDOM_FUPDATE_LIST,MAP_ZIP,LENGTH_COUNT_LIST,SUBSET_DEF,SET_EQ_SUBSET,MEM_MAP]>>
       rw[]>>res_tac
       >-
         DECIDE_TAC
       >-
         fs[MEM_COUNT_LIST]
       >>
         Cases_on`x ∈ FDOM s`>>fs[]>>
         `x>= st.next_uvar` by 
           (SPOSE_NOT_THEN assume_tac>>
           `x < st.next_uvar` by DECIDE_TAC>>res_tac)>>
         imp_res_tac arithmeticTheory.LESS_ADD>>
         Q.EXISTS_TAC `LENGTH targs - p`>>
         fs[MEM_COUNT_LIST]>>
         DECIDE_TAC)
	     >- fs[SUBMAP_t_compat]
      (*deBruijn_subst*)
       >>
       reverse (Cases_on`LENGTH targs >0`)
       >-
       (`LENGTH targs = 0` by DECIDE_TAC>>
       fs[LENGTH_NIL,deBruijn_subst_id,COUNT_LIST_def,infer_deBruijn_subst_id]>>
       `t_walkstar s' t' = t_walkstar s t'` by
         (imp_res_tac t_walkstar_SUBMAP>>
         first_x_assum(qspec_then `t'` mp_tac)>>
         imp_res_tac check_freevars_to_check_t>>
         rw[]>>metis_tac[t_walkstar_no_vars])>> 
        pop_assum SUBST_ALL_TAC>>
        qpat_assum `unconvert_t t = bla` (assume_tac o Q.AP_TERM `convert_t`)>>
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
           fs[Abbr`s'`,FDOM_FUPDATE_LIST]>> 
         imp_res_tac check_t_more5>>
         metis_tac[EMPTY_SUBSET])>> 
       rfs[check_t_more]>>
       fs[MAP_MAP_o]>>
             `(MAP (convert_t o t_walkstar s' o (λn. Infer_Tuvar (st.next_uvar + n)))
                   (COUNT_LIST (LENGTH targs))) = targs` by
       (
       match_mp_tac LIST_EQ>>
       fs[LENGTH_COUNT_LIST]>>rw[]>>
       fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
       qpat_abbrev_tac `tar = EL x targs`>>
       fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
       `FLOOKUP s' (st.next_uvar +x) = SOME (unconvert_t tar)` by
       (
         fs[Abbr`s'`,flookup_update_list_some]>>DISJ1_TAC>>
               qmatch_abbrev_tac `ALOOKUP (REVERSE L) k = SOME Y`>>
         Q.ISPECL_THEN [`L`,`k`] mp_tac alookup_distinct_reverse>>
         `ALL_DISTINCT (MAP FST L)` by
         (rw[Abbr`L`,MAP_ZIP,LENGTH_COUNT_LIST]>>
          match_mp_tac ALL_DISTINCT_MAP_INJ>>
          fs[all_distinct_count_list])>>
         rw[]>>
         unabbrev_all_tac>>
         match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>fs[]>>
         fs[MEM_ZIP,LENGTH_COUNT_LIST]>>HINT_EXISTS_TAC>>
         fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST])>>
       fs[]>>
       fs[EVERY_EL]>>last_x_assum(qspec_then `x` assume_tac)>>
       rfs[]>>
       imp_res_tac check_freevars_to_check_t>>
       imp_res_tac check_freevars_empty_convert_unconvert_id>>
       Cases_on`unconvert_t tar`
       >-
         (fs[]>>metis_tac[])
       >-
         (fs[check_t_def]>>
         `MAP (t_walkstar s') l = l` by
           (fs[MAP_EQ_ID,EVERY_MEM]>>rw[]>>
           metis_tac[t_walkstar_no_vars])>>fs[])
       >>
         fs[check_t_def])>>
     fs[]>>
     imp_res_tac inc_wfs>>
     AP_TERM_TAC>>
     metis_tac[t_walkstar_no_vars,check_freevars_empty_convert_unconvert_id])
    >-
    (*Long*)
    cheat)
 >-
   (*Fun*)
   (fs[bind_tenv_def,num_tvs_def,tenv_inv_def]>>
   Q.ABBREV_TAC `constraints' = constraints++
                 [Infer_Tuvar st.next_uvar,unconvert_t t1]`>>
   imp_res_tac pure_add_constraints_exists>>
   pop_assum (qspecl_then [`[t1]`,`num_tvs tenvE`] mp_tac)>>
   miscLib.discharge_hyps>>fs[]>>
   miscLib.discharge_hyps_keep>-
   metis_tac[sub_completion_wfs]>>
   fs[LET_THM,EVAL``COUNT_LIST 1``]>>
   qpat_abbrev_tac `s' = s|++ls`>>
   first_x_assum(qspecl_then[`s'`,`menv`,
     `(n,0,Infer_Tuvar st.next_uvar)::tenv`,
     `st with next_uvar:= st.next_uvar+1`,`constraints'`] mp_tac)>>
   imp_res_tac check_freevars_to_check_t>>
   `t_wfs s'` by 
     metis_tac[Abbr`s'`,t_wfs_eqn,extend_t_vR_WF,FUPDATE_EQ_FUPDATE_LIST]>>
   `s SUBMAP s'` by
     (unabbrev_all_tac>>
     match_mp_tac SUBMAP_FUPDATE_LIST_NON_EXIST>>
     fs[MAP_ZIP,LENGTH_COUNT_LIST]>>
     fs[INTER_DEF,MEM_MAP,MEM_COUNT_LIST,EXTENSION]>>
     rw[] >>DECIDE_TAC)>>
   miscLib.discharge_hyps>>fs[]
   >-
     (rpt strip_tac
     >-
       (imp_res_tac check_env_more>>
       pop_assum(qspec_then `st.next_uvar +1` mp_tac)>>
       miscLib.discharge_hyps>-DECIDE_TAC>>
       fs[check_env_def,check_t_def])
     >-
       (fs[sub_completion_def]>>
       unabbrev_all_tac>>
       rpt strip_tac
       >-
         (fs[pure_add_constraints_append]>>HINT_EXISTS_TAC>>fs[]>>
         assume_tac pure_add_constraints_exists>>
         pop_assum(qspecl_then [`s`,`[t1]`,`st.next_uvar`,`num_tvs tenvE`] mp_tac)>>
         miscLib.discharge_hyps>>
         fs[LET_THM,EVAL ``COUNT_LIST 1``])
       >-
         (fs[FDOM_FUPDATE_LIST,SUBSET_DEF]>>DECIDE_TAC)
       >-
         cheat) (*Because it extends s*)
     >-
       (fs[SUBSET_DEF]>>rw[]>>res_tac>>DECIDE_TAC)
     >-
       (unabbrev_all_tac>>
       fs[FDOM_FUPDATE_LIST,EXTENSION]>>DECIDE_TAC)
     >-
       (fs[tenv_inv_def,lookup_tenv_def]>>rpt strip_tac>>
       Cases_on`n=x`>>fs[deBruijn_inc0]
       >-
         (HINT_EXISTS_TAC>>fs[])
       >- res_tac)
     >-
       (fs[tenv_inv_def,lookup_tenv_def]>>rpt strip_tac>>
       Cases_on`n=x`>>fs[deBruijn_inc0]
       >-
       (fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
       unabbrev_all_tac>>
       fs[flookup_fupdate_list]>>
       Cases_on`unconvert_t t'`
       >-
         fs[]
       >-
         (fs[MAP_EQ_ID,check_t_def,EVERY_MEM]>>rw[]>>
         res_tac>>metis_tac[t_walkstar_no_vars])
       >- fs[check_t_def])
       >>
       res_tac>>
       Q.EXISTS_TAC `t''`>>
       `t_walkstar s t'' = t_walkstar s' t''` by 
         (imp_res_tac t_walkstar_SUBMAP>>
         first_x_assum(qspec_then `t''` SUBST1_TAC)>>
         Cases_on`tvs>0`>>
         metis_tac[check_freevars_to_check_t,t_walkstar_no_vars])>>
         fs[])) 
   >>
   (strip_tac>>rw[success_eqns]>>
   HINT_EXISTS_TAC>>HINT_EXISTS_TAC>>
   fs[]>> CONJ_TAC
   >-
     (`t_compat s s'` by fs[SUBMAP_t_compat]>>
     metis_tac[t_compat_trans])
   >>
     `t_wfs s''` by
       (`t_wfs st''.subst` by  
         (imp_res_tac infer_e_wfs>> rfs[])>>
       metis_tac[sub_completion_wfs])>>
     simp[Once t_walkstar_eqn,Once t_walk_eqn,SimpRHS]>>
     simp[convert_t_def]>>
     fs[t_compat_def]>>
     `t_walkstar s' (Infer_Tuvar st.next_uvar) = unconvert_t t1` by
       (simp[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
       unabbrev_all_tac>>
       simp[flookup_fupdate_list]>>
       Cases_on`unconvert_t t1`
       >-
         simp[]
       >-
         (fs[MAP_EQ_ID,check_t_def,EVERY_MEM]>>rw[]>>
         res_tac>>metis_tac[t_walkstar_no_vars])
       >- fs[check_t_def])>>
    first_x_assum(qspec_then `Infer_Tuvar st.next_uvar` assume_tac)>>rfs[]>>
    metis_tac[check_freevars_empty_convert_unconvert_id,t_walkstar_no_vars]))
 >-
   (*App*)
   first_x_assum(qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>rfs[]>>
 
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
     `t_wfs s'` by metis_tac[infer_e_wfs,pure_add_constraints_wfs]>>fs[]>>rfs[])


     res_tac>>
     Q.SPEC_THEN `e` assume_tac (Q.INST[`n`|->`num_tvs tenvE`] 
       (fst(CONJ_PAIR check_t_less)))>>
     fs[sub_completion_def]
     

   Q.EXISTS_TAC `t''`>>Q.EXISTS_TAC`st''`>>
   `constrain_op op ts' st' = (Success t'',st'')` by cheat >>
   fs[
   simp[PULL_EXISTS]
   
   fs[type_op_def]
 >- (*Log*)
   cheat
 >- (*If *)
   cheat
 >- (*Mat*)
   cheat
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
     imp_res_tac tenv_inv_submap>>fs[]>>
     ntac 2 HINT_EXISTS_TAC>>
     fs[]>>metis_tac[SUBMAP_TRANS])
   >>
     cheat) (*Rest of this should be about the same as Fun*)
 >-
   (*Letrec*)
   (imp_res_tac type_funs_distinct>>
   `MAP (\x,y,z. x) funs = MAP FST funs` by
     fs[MAP_EQ_f,FORALL_PROD]>>
   fs[bind_var_list_def]>>
   qpat_abbrev_tac `new_tenv = A ++ tenv`>>
   (*last_x_assum (qspecl_then [`s',`menv`,`st with next_uvar:=st.next_uvar + LENGTH funs`,*)
   cheat)  
 >> cheat)
 
 (*(`tenv_inv (bind n (0,Infer_Tuvar st.next_uvar) tenv) (bind_tenv n 0 t1 tenvE)`
              by (rw [bind_def, tenv_inv_def, bind_tenv_def] >>
                  cheat) >>
     `convert_menv menv = convert_menv menv` by cheat

     res_tac >>
     fs []
     rw []

     *)


val _ = export_theory ();
