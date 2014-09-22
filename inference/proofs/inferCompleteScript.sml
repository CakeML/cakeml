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

(* End unification stuff *)

val unconvert_t_def = tDefine "unconvert_t" `
(unconvert_t (Tvar_db n) = Infer_Tvar_db n) ∧
(unconvert_t (Tapp ts tc) = Infer_Tapp (MAP unconvert_t ts) tc)`
(wf_rel_tac `measure t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [t_size_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val tenv_inv_def = Define `
tenv_inv s env tenv =
  (!x tvs t.
    lookup_tenv x 0 tenv = SOME (tvs, t)
    ⇒
    check_freevars tvs [] t ∧
    ?t'. unconvert_t t = t_walkstar s t' ∧ ALOOKUP env x = SOME (tvs,t'))`;


val t_walk_vwalk_id = prove
(``t_wfs s ⇒ 
  !n. t_walk s (t_vwalk s n) = t_vwalk s n``,
  strip_tac>>
  ho_match_mp_tac (Q.INST[`s`|->`s`]t_vwalk_ind)>>
  rw[]>>
  Cases_on`FLOOKUP s n`>>fs[t_walk_eqn,Once t_vwalk_eqn]>>
  simp[EQ_SYM_EQ]>>
  fs[Once t_vwalk_eqn]>>
  Cases_on`x`
  >-
    fs[t_walk_eqn,Once t_vwalk_eqn]
  >-
    fs[t_walk_eqn,Once t_vwalk_eqn]
  >>
    fs[])
  
val t_walk_walk_id = prove(
``t_wfs s ⇒ 
  t_walk s (t_walk s h) = t_walk s h``,
  Cases_on`h`>>
  fs[t_walk_eqn,t_walk_vwalk_id])

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
``!t. check_freevars n [] t ==>
  convert_t (unconvert_t t) = t``,
  ho_match_mp_tac (fetch "-" "unconvert_t_ind")>>
  rw[]>>fs[unconvert_t_def,convert_t_def,check_freevars_def]>>
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


val infer_e_complete = Q.prove (

`(!tenvM tenvC tenvE e t. 
   type_e tenvM tenvC tenvE e t
   ⇒
   !s menv tenv st constraints.
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion 0 st.next_uvar st.subst constraints s ∧
     (*I think these conditions are reasonable... the second one might not*)
     FDOM st.subst ⊆ count st.next_uvar ∧ 
     FDOM s = count st.next_uvar ∧
     tenv_inv s tenv tenvE
     ⇒
     ?t' st' s' constraints'.
       infer_e menv tenvC tenv e st = (Success t', st') ∧
       sub_completion 0 st'.next_uvar st'.subst constraints' s' ∧
       FDOM st'.subst ⊆  count st'.next_uvar ∧ 
       FDOM s' = count st'.next_uvar ∧ 
       t = convert_t (t_walkstar s' t')) ∧
 (!tenvM tenvC tenvE es ts. 
   type_es tenvM tenvC tenvE es ts
   ⇒
   !s menv tenv st constraints.
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion 0 st.next_uvar st.subst constraints s ∧
     tenv_inv s tenv tenvE
     ⇒
     ?ts' st' s' constraints'.
       infer_es menv tenvC tenv es st = (Success ts', st') ∧
       sub_completion 0 st'.next_uvar st'.subst constraints' s' ∧
       ts = MAP (convert_t o t_walkstar s') ts') ∧
 (!tenvM tenvC tenvE funs env. 
   type_funs tenvM tenvC tenvE funs env
   ⇒
   !s menv tenv st constraints.
     tenvM = convert_menv menv ∧
     t_wfs st.subst ∧
     sub_completion 0 st.next_uvar st.subst constraints s ∧
     tenv_inv s tenv tenvE
     ⇒
     ?env' st' s' constraints'.
       infer_funs menv tenvC tenv funs st = (Success env', st') ∧
       sub_completion 0 st'.next_uvar st'.subst constraints' s' ∧
       MAP SND env = MAP (convert_t o t_walkstar s') env')`,
 ho_match_mp_tac type_e_strongind >>
 rw [success_eqns,infer_e_def]
 (*Easy cases*)
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- (qexists_tac `s'` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >- (qexists_tac `s` >>
     imp_res_tac sub_completion_wfs >>
     rw [t_walkstar_eqn1, convert_t_def] >>
     metis_tac [])
 >-
 (*Raise*) 
    (*first_x_assum(qspecl_then [`s`,`menv`,`tenv`,`st`,`constraints`] assume_tac)>>
    rfs[]>>
    `t_wfs st'.subst /\ t_wfs s'` by metis_tac[infer_e_wfs,sub_completion_wfs]>>
     miscLib.specl_args_of_then ``t_unify`` (Q.GENL [`t2`,`t1`,`s`] (SPEC_ALL t_unify_eqn)) assume_tac>>rfs[t_walk_eqn]>>
    fs[t_walkstar_eqn]>>
    Cases_on`t'`>>
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
           ,MAP unconvert_t targs))` >>
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
	 (
	 rw[]>-
	 (unabbrev_all_tac>>
	 fs[FDOM_FUPDATE_LIST,SUBSET_DEF,MAP_ZIP,LENGTH_COUNT_LIST]>>
	 fs[MEM_MAP,MEM_COUNT_LIST]>>rw[]>>
	 Cases_on`x<st.next_uvar`>>fs[]>>
	 imp_res_tac arithmeticTheory.LESS_ADD>>
	 Q.EXISTS_TAC `LENGTH targs - p`>>
	 DECIDE_TAC)>-
         (
	 imp_res_tac t_walkstar_SUBMAP>>
	 first_x_assum (qspec_then `(Infer_Tuvar uv)` assume_tac)>>
	 fs[]>>
	 Cases_on`uv < st.next_uvar`
	 >-
	   (res_tac>>
	   imp_res_tac t_walkstar_no_vars>>fs[])
	 >>
	   `uv ∉ FDOM s ∧ FLOOKUP s uv = NONE` by fs[flookup_thm]>>
	   fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
	   fs[Once t_vwalk_eqn]>>
	   BasicProvers.FULL_CASE_TAC>-
	     fs[flookup_thm]>>
	   fs[Abbr`s'`,flookup_fupdate_list]>>
	   pop_assum mp_tac>>
	   BasicProvers.FULL_CASE_TAC>>
	   imp_res_tac ALOOKUP_MEM>>
	   fs[MEM_REVERSE]>>
	   fs[LENGTH_COUNT_LIST,MEM_ZIP,EL_MAP]>>
	   fs[EVERY_MEM,MEM_EL]>>res_tac>>
	   strip_tac>>
	   `convert_t x = EL n targs` by
	     metis_tac[check_freevars_empty_convert_unconvert_id] >>
           (*Problem here!*)cheat
	 ))>>
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
	   DECIDE_TAC)>>
	(*deBruijn_subst*)
         imp_res_tac check_freevars_to_check_t>>
	 fs[]>>
	 `check_t (LENGTH targs) (FDOM s') t'` by 
	   (imp_res_tac check_t_t_walkstar>>
	   `FDOM s ⊆ FDOM s'` by 
	     fs[Abbr`s'`,FDOM_FUPDATE_LIST]>> 
	   imp_res_tac check_t_more5)>>
	 assume_tac (db_subst_infer_subst_swap|>CONJ_PAIR|>fst)>>
	 pop_assum (qspecl_then [`t'`,`s'`,`LENGTH targs`,`st.next_uvar`,`0`] assume_tac)>>
	 rfs[]>>
	 fs[MAP_MAP_o]>>
         `(MAP (convert_t o t_walkstar s' o (λn. Infer_Tuvar (st.next_uvar + n)))
               (COUNT_LIST (LENGTH targs))) = targs` by cheat>>
	 fs[t_walkstar_ignore_inc]>>
	 AP_TERM_TAC>>
	 `t_walkstar s' t' = t_walkstar s t'` by 
	   (imp_res_tac t_walkstar_SUBMAP>>
	   first_x_assum (qspec_then `t'` assume_tac)>>
	   imp_res_tac t_walkstar_no_vars)>>
	 metis_tac[check_freevars_empty_convert_unconvert_id])
    >-
    (*Long*)
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
