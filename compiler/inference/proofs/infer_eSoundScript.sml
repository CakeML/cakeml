(*
  Prove soundness of the type inferencer for the expression-level.
*)
Theory infer_eSound
Ancestors
  typeSystem ast semanticPrimitives infer unify infer_t
  inferProps envRel typeSysProps namespaceProps
  typeSoundInvariants[qualified]
Libs
  preamble

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

(* ---------- sub_completion ---------- *)

Theorem sub_completion_unify[local]:
  !st t1 t2 s1 n ts s2 n.
  (t_unify st.subst t1 t2 = SOME s1) ∧
  sub_completion n (st.next_uvar + 1) s1 ts s2
  ⇒
  sub_completion n st.next_uvar st.subst ((t1,t2)::ts) s2
Proof
  rw [sub_completion_def, pure_add_constraints_def] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF, count_add1]
QED

Theorem sub_completion_unify2:
 !t1 t2 s1 ts s2 n s3 next_uvar.
  (t_unify s1 t1 t2 = SOME s2) ∧
  sub_completion n next_uvar s2 ts s3
  ⇒
  sub_completion n next_uvar s1 ((t1,t2)::ts) s3
Proof
rw [sub_completion_def, pure_add_constraints_def]
QED

Theorem sub_completion_infer[local]:
  !l ienv e st1 t st2 n ts2 s.
  infer_e l ienv e st1 = (Success t, st2) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s
Proof
  rw [sub_completion_def, pure_add_constraints_append] >>
imp_res_tac infer_e_constraints >>
imp_res_tac infer_e_next_uvar_mono >>
qexists_tac `ts` >>
rw [] >|
[qexists_tac `st2.subst` >>
     rw [],
 full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF]]
QED

Theorem sub_completion_add_constraints:
 !s1 ts1 s2 n next_uvar s3 ts2.
  pure_add_constraints s1 ts1 s2 ∧
  sub_completion n next_uvar s2 ts2 s3
  ⇒
  sub_completion n next_uvar s1 (ts1++ts2) s3
Proof
induct_on `ts1` >>
rw [pure_add_constraints_def] >>
Cases_on `h` >>
fs [pure_add_constraints_def] >>
res_tac >>
fs [sub_completion_def] >>
rw [] >>
fs [pure_add_constraints_def, pure_add_constraints_append] >>
metis_tac []
QED

Theorem sub_completion_more_vars[local]:
  !m n1 n2 s1 ts s2.
  sub_completion m (n1 + n2) s1 ts s2 ⇒ sub_completion m n1 s1 ts s2
Proof
  rw [sub_completion_def] >>
rw [] >>
full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF]
QED

Theorem sub_completion_infer_es[local]:
  !l cenv es st1 t st2 n ts2 s.
  infer_es l cenv es st1 = (Success t, st2) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s
Proof
  induct_on `es` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
res_tac >>
imp_res_tac sub_completion_infer >>
metis_tac [APPEND_ASSOC]
QED

Theorem sub_completion_infer_p:
  (!l cenv p st t env st' tvs extra_constraints s.
    infer_p l cenv p st = (Success (t,env), st') ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    ?ts. sub_completion tvs st.next_uvar st.subst (ts++extra_constraints) s) ∧
  (!l cenv ps st ts env st' tvs extra_constraints s.
    infer_ps l cenv ps st = (Success (ts,env), st') ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    ?ts. sub_completion tvs st.next_uvar st.subst (ts++extra_constraints) s)
Proof
  ho_match_mp_tac infer_p_ind >>
  rw [infer_p_def, success_eqns, remove_pair_lem] >>
  fs []
  >- metis_tac [APPEND, sub_completion_more_vars]
  >- metis_tac [APPEND, sub_completion_more_vars]
  >- metis_tac [APPEND, sub_completion_more_vars]
  >- metis_tac [APPEND, sub_completion_more_vars]
  >- metis_tac [APPEND, sub_completion_more_vars]
  >- metis_tac [APPEND, sub_completion_more_vars]
  >- metis_tac [APPEND, sub_completion_more_vars]
  >- (PairCases_on `v'` >>
      fs [] >>
      metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars])
  >- (imp_res_tac sub_completion_add_constraints >>
      PairCases_on `v''` >>
      fs [] >>
      metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars,ADD_COMM])
  >- (PairCases_on `v'` >>
      fs [] >>
      metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars])
  >- (PairCases_on `v'` >>
      fs [] >>
      metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars])
  >- (
    imp_res_tac type_name_check_subst_state >>
    fs [] >>
    imp_res_tac sub_completion_unify2 >>
    metis_tac [APPEND_ASSOC, APPEND, sub_completion_more_vars])
  >- metis_tac [APPEND, sub_completion_more_vars]
  >- (PairCases_on `v'` >>
      PairCases_on `v''` >>
      fs [] >>
      metis_tac [APPEND_ASSOC])
QED

Theorem sub_completion_infer_pes[local]:
  !l ienv pes t1 t2 st1 t st2 n ts2 s.
  infer_pes l ienv pes t1 t2 st1 = (Success (), st2) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s
Proof
  induct_on `pes` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
PairCases_on `v'` >>
fs [infer_e_def, success_eqns] >>
rw [] >>
res_tac >>
fs [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer >>
fs [] >>
imp_res_tac sub_completion_unify2 >>
imp_res_tac sub_completion_infer_p >>
fs [] >>
metis_tac [APPEND, APPEND_ASSOC]
QED

Theorem sub_completion_infer_funs[local]:
  !l ienv funs st1 t st2 n ts2 s.
  infer_funs l ienv funs st1 = (Success t, st2) ∧
  sub_completion n st2.next_uvar st2.subst ts2 s
  ⇒
  ?ts1. sub_completion n st1.next_uvar st1.subst (ts1 ++ ts2) s
Proof
  induct_on `funs` >>
rw [infer_e_def, success_eqns] >-
metis_tac [APPEND] >>
PairCases_on `h` >>
fs [infer_e_def, success_eqns] >>
res_tac >>
imp_res_tac sub_completion_infer >>
fs [] >>
metis_tac [sub_completion_more_vars, APPEND_ASSOC]
QED

Theorem sub_completion_apply:
 !n uvars s1 ts s2 t1 t2.
  t_wfs s1 ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2) ∧
  sub_completion n uvars s1 ts s2
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)
Proof
rw [sub_completion_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum mp_tac >>
pop_assum mp_tac >>
pop_assum mp_tac >>
Q.SPEC_TAC (`s1`, `s1`) >>
induct_on `ts` >>
rw [pure_add_constraints_def] >-
metis_tac [] >>
cases_on `h` >>
fs [pure_add_constraints_def] >>
fs [] >>
metis_tac [t_unify_apply2, t_unify_wfs]
QED

Theorem sub_completion_apply_list[local]:
  !n uvars s1 ts s2 ts1 ts2.
  t_wfs s1 ∧
  (MAP (t_walkstar s1) ts1 = MAP (t_walkstar s1) ts2) ∧
  sub_completion n uvars s1 ts s2
  ⇒
  (MAP (t_walkstar s2) ts1 = MAP (t_walkstar s2) ts2)
Proof
  induct_on `ts1` >>
rw [] >>
cases_on `ts2` >>
fs [] >>
metis_tac [sub_completion_apply]
QED

Theorem sub_completion_check[local]:
  !tvs m s uvar s' extra_constraints.
sub_completion m (uvar + tvs) s' extra_constraints s
⇒
EVERY (λn. check_freevars m [] (convert_t (t_walkstar s (Infer_Tuvar (uvar + n))))) (COUNT_LIST tvs)
Proof
  induct_on `tvs` >>
rw [sub_completion_def, COUNT_LIST_SNOC, EVERY_SNOC] >>
fs [sub_completion_def] >|
[qpat_x_assum `!m' s. P m' s` match_mp_tac >>
     rw [] >>
     qexists_tac `s'` >>
     qexists_tac `extra_constraints` >>
     rw [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF],
 fs [SUBSET_DEF] >>
     `uvar+tvs < uvar + SUC tvs`
            by full_simp_tac (srw_ss()++ARITH_ss) [SUBSET_DEF] >>
     metis_tac [check_t_to_check_freevars,ADD_COMM]]
QED

(* ---------- Soundness ---------- *)

Theorem infer_p_sound:
  (!l ienv p st t tenv env st' tvs extra_constraints s.
    infer_p l ienv p st = (Success (t,env), st') ∧
    t_wfs st.subst ∧
    tenv_ctor_ok tenv.c ∧
    ienv.inf_c = tenv.c ∧
    ienv.inf_t = tenv.t ∧
    tenv_abbrev_ok tenv.t ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_p tvs tenv p (convert_t (t_walkstar s t)) (convert_env s env)) ∧
  (!l ienv ps st ts tenv env st' tvs extra_constraints s.
    infer_ps l ienv ps st = (Success (ts,env), st') ∧
    t_wfs st.subst ∧
    tenv_ctor_ok tenv.c ∧
    ienv.inf_c = tenv.c ∧
    ienv.inf_t = tenv.t ∧
    tenv_abbrev_ok tenv.t ∧
    sub_completion tvs st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_ps tvs tenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env))
Proof
  ho_match_mp_tac infer_p_ind >>
  rw [infer_p_def, success_eqns, remove_pair_lem] >>
  rw [Once type_p_cases, convert_env_def] >>
  imp_res_tac sub_completion_wfs >>
  fs [] >>
  rw [t_walkstar_eqn1, convert_t_def, Tint_def, Tstring_def, Tchar_def] >>
  imp_res_tac type_name_check_subst_thm >>
  imp_res_tac type_name_check_subst_state>>
  fs []
  >- (match_mp_tac check_t_to_check_freevars >>
      rw [] >>
      fs [sub_completion_def] >>
      qpat_x_assum `!uv. uv ∈ FDOM s ⇒ P uv` match_mp_tac >>
      fs [count_def, SUBSET_DEF])
  >- (match_mp_tac check_t_to_check_freevars >>
      rw [] >>
      fs [sub_completion_def] >>
      qpat_x_assum `!uv. uv ∈ FDOM s ⇒ P uv` match_mp_tac >>
      fs [count_def, SUBSET_DEF])
  >- (`?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
      `t_wfs s` by metis_tac [infer_p_wfs] >>
      rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
      fs [convert_env_def] >>
      metis_tac [MAP_MAP_o])
  >- (`?ts env. v'' = (ts,env)` by (PairCases_on `v''` >> metis_tac []) >>
      `?tvs ts tn. v' = (tvs,ts,tn)` by (PairCases_on `v'` >> metis_tac []) >>
      rw [] >>
      `type_ps tvs tenv ps (MAP (convert_t o t_walkstar s) ts) (convert_env s env)`
                by metis_tac [sub_completion_add_constraints, sub_completion_more_vars,ADD_COMM] >>
      rw [] >>
      `t_wfs s` by metis_tac [sub_completion_wfs, infer_p_wfs, pure_add_constraints_wfs] >>
      rw [convert_t_def, t_walkstar_eqn1, MAP_MAP_o, combinTheory.o_DEF,
          EVERY_MAP, LENGTH_COUNT_LIST] >>
      fs [] >- (
        qpat_x_assum`_ + _ = (_:num)`(assume_tac o ONCE_REWRITE_RULE[ADD_COMM] o SYM)
        \\ fsrw_tac[][]
        \\ drule sub_completion_check
        \\ simp[] ) >>
      `t_wfs st'''.subst` by metis_tac [infer_p_wfs] >>
      imp_res_tac pure_add_constraints_apply >>
      pop_assum (fn _ => all_tac) >>
      pop_assum (fn _ => all_tac) >>
      pop_assum mp_tac >>
      rw [MAP_ZIP] >>
      `t_wfs st'.subst` by metis_tac [pure_add_constraints_wfs] >>
      imp_res_tac sub_completion_apply_list >>
      NTAC 6 (pop_assum (fn _ => all_tac)) >>
      pop_assum mp_tac >>
      rw [ONCE_REWRITE_RULE[ADD_COMM](CONJUNCT2 subst_infer_subst_swap)] >>
      `EVERY (check_freevars 0 tvs') ts'` by metis_tac [tenv_ctor_ok_lookup] >>
      rw [] >>
      fs [convert_env_def] >>
      metis_tac [convert_t_subst, LENGTH_COUNT_LIST, LENGTH_MAP,
                 MAP_MAP_o, combinTheory.o_DEF])
  >- (`?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
      `t_wfs s` by metis_tac [infer_p_wfs] >>
      rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
      fs [convert_env_def] >>
      metis_tac [])
  >- (`?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
      `t_wfs s` by metis_tac [infer_p_wfs] >>
      rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
      fs [convert_env_def] >>
      metis_tac [])
  >- (drule (hd (CONJUNCTS infer_p_wfs)) >>
      disch_then drule >>
      rw [] >>
      drule t_unify_apply >>
      disch_then drule >>
      rw [] >>
      drule t_unify_wfs >>
      disch_then drule >>
      rw [] >>
      drule sub_completion_apply >>
      rpt (disch_then drule) >>
      rw [] >>
      drule check_freevars_type_name_subst >>
      rpt (disch_then drule) >>
      disch_then(qspec_then`0n` assume_tac)>>
      rw [] >>
      drule (hd (CONJUNCTS infer_type_subst_nil)) >>
      rw [] >> fs [] >>
      `check_t 0 {} (infer_type_subst [] (type_name_subst tenv.t t))`
        by metis_tac [infer_type_subst_empty_check] >>
      metis_tac [t_walkstar_no_vars, check_freevars_empty_convert_unconvert_id])
  >- (`type_name_subst tenv.t t = convert_t (t_walkstar s t')`
         by (* This is the previous goal *)
            (drule (hd (CONJUNCTS infer_p_wfs)) >>
             disch_then drule >>
             rw [] >>
             drule t_unify_apply >>
             disch_then drule >>
             rw [] >>
             drule t_unify_wfs >>
             disch_then drule >>
             rw [] >>
             drule sub_completion_apply >>
             rpt (disch_then drule) >>
             rw [] >>
             drule check_freevars_type_name_subst >>
             rpt (disch_then drule) >>
             disch_then(qspec_then`0n` assume_tac)>>
             rw [] >>
             drule (hd (CONJUNCTS infer_type_subst_nil)) >>
             rw [] >> fs [] >>
             `check_t 0 {} (infer_type_subst [] (type_name_subst tenv.t t))`
               by metis_tac [infer_type_subst_empty_check] >>
             metis_tac [t_walkstar_no_vars, check_freevars_empty_convert_unconvert_id]) >>
      rw [GSYM convert_env_def] >>
      first_x_assum irule >> rw [] >>
      imp_res_tac sub_completion_unify2 >>
      metis_tac [APPEND_ASSOC, APPEND, sub_completion_add_constraints])
  >- (`?t env. v' = (t,env)` by (PairCases_on `v'` >> metis_tac []) >>
      `?ts' env'. v'' = (ts',env')` by (PairCases_on `v''` >> metis_tac []) >>
      rw [] >>
      `t_wfs st''.subst` by metis_tac [infer_p_wfs] >>
      `?ts. sub_completion tvs st''.next_uvar st''.subst ts s` by metis_tac [sub_completion_infer_p] >>
      fs [convert_env_def] >>
      metis_tac [])
QED

Theorem letrec_lemma[local]:
  !funs funs_ts s st.
  (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)) =
   MAP (\t. convert_t (t_walkstar s t)) funs_ts)
  ⇒
  (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs))) =
   MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts)
Proof
  induct_on `funs` >>
srw_tac[] [] >>
cases_on `funs_ts` >>
fsrw_tac[] [COUNT_LIST_def] >>
srw_tac[] [] >|
[PairCases_on `h` >>
     rw [],
 qpat_x_assum `!x. P x` match_mp_tac >>
     qexists_tac `st with next_uvar := st.next_uvar + 1` >>
     fsrw_tac[] [MAP_MAP_o, combinTheory.o_DEF, DECIDE ``x + SUC y = x + 1 + y``]]
QED

Theorem map_zip_lem[local]:
  !funs ts.
  (LENGTH funs = LENGTH ts)
  ⇒
  (MAP (λx. FST ((λ((x',y,z),t). (x',convert_t (t_walkstar s t))) x)) (ZIP (funs,ts))
   =
   MAP FST funs)
Proof
  induct_on `funs` >>
rw [] >>
cases_on `ts` >>
fs [] >>
PairCases_on `h` >>
rw []
QED

Theorem word_tc_cases:
    (word_tc wz = Tword8_num ⇔ wz = W8) ∧
  (word_tc wz = Tword64_num ⇔ wz = W64)
Proof
  Cases_on`wz`>>rw[word_tc_def,Tword8_num_def,Tword64_num_def]
QED

val binop_tac =
 imp_res_tac infer_e_wfs >>
 imp_res_tac t_unify_wfs >>
 fsrw_tac[] [] >>
 imp_res_tac sub_completion_unify2 >>
 imp_res_tac sub_completion_infer >>
 fsrw_tac[] [] >>
 res_tac >>
 fsrw_tac[] [] >>
 imp_res_tac t_unify_apply >>
 imp_res_tac sub_completion_apply >>
 imp_res_tac t_unify_wfs >>
 imp_res_tac sub_completion_wfs >>
 fsrw_tac[] [t_walkstar_eqn, t_walk_eqn, convert_t_def, deBruijn_inc_def, check_t_def] >>
 srw_tac[] [type_op_cases, Tint_def, Tstring_def, Tref_def, Tfn_def, Texn_def, Tchar_def,word_tc_cases] >>
 metis_tac [MAP, infer_e_next_uvar_mono, check_env_more, word_size_nchotomy];

Theorem constrain_op_sub_completion[local]:
 sub_completion (num_tvs tenv) st.next_uvar st.subst extra_constraints s ∧
 constrain_op l op ts st' = (Success t,st)
 ⇒
 ∃c. sub_completion (num_tvs tenv) st'.next_uvar st'.subst c s
Proof
 rw [] >>
 fs [constrain_op_success] >>
 every_case_tac >>
 fs [success_eqns] >>
 TRY pairarg_tac >>
 gvs [CaseEq"bool", success_eqns] >>
 rw [] >>
 fs [infer_st_rewrs, success_eqns] >>
 PROVE_TAC [sub_completion_unify2, sub_completion_unify,
            sub_completion_add_constraints]
QED

Theorem constrain_op_sound[local]:
 t_wfs st.subst ∧
 sub_completion (num_tvs tenv) st'.next_uvar st'.subst c s ∧
 constrain_op l op ts st = (Success t,st')
 ⇒
 type_op op (MAP (convert_t o t_walkstar s) ts) (convert_t (t_walkstar s t))
Proof
  fs[constrain_op_success] >>
  rw [] >>
  fs [fresh_uvar_def,infer_st_rewrs,Tchar_def,Tword64_def] >> rw[] >>
  TRY pairarg_tac >>
  fs [success_eqns] >~
  [‘Test t1 t2’] >-
   (Cases_on ‘t1’ \\ Cases_on ‘t2’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ binop_tac)
  >~ [‘FromTo p1 p2’] >- (
    Cases_on ‘p1’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ Cases_on ‘p2’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ gvs[supported_conversion_def]
    \\ binop_tac )
  >~ [‘Arith a p’] >- (
    gvs[CaseEq"option",CaseEq"bool",failwith_def,
        st_ex_bind_def,st_ex_return_def,CaseEq"exc",CaseEq"prod"]
    \\ Cases_on`a` \\ Cases_on ‘p’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ gvs[supported_arith_def,LENGTH_EQ_NUM_compute, REPLICATE_compute,
           add_constraints_def, st_ex_bind_def,CaseEq"prod",CaseEq"exc",
           st_ex_return_def,add_constraint_def,CaseEq"option"]
    \\ binop_tac )
  \\ binop_tac
QED

Theorem infer_deBruijn_subst_walkstar:
   !ts t s.
    t_wfs s ⇒
    t_walkstar s (infer_deBruijn_subst (MAP (t_walkstar s) ts) t)
    =
    t_walkstar s (infer_deBruijn_subst ts t)
Proof
  gen_tac \\ ho_match_mp_tac infer_t_ind
  >> rw [infer_deBruijn_subst_alt, EL_MAP]
  >- metis_tac [SUBMAP_REFL, t_walkstar_idempotent]
  >> rw [t_walkstar_eqn1, MAP_EQ_EVERY2, LIST_REL_EL_EQN]
  >> `MEM (EL n l) l` by (rw [MEM_EL] >> metis_tac [])
  >> first_x_assum drule
  >> disch_then drule
  >> simp [EL_MAP]
QED

val log_tac =
 ( (* Log *)
   imp_res_tac t_unify_wfs
   >> imp_res_tac infer_e_wfs
   >> imp_res_tac sub_completion_wfs
   >> `t_wfs s` by metis_tac []
   >> rw [t_walkstar_eqn1, convert_t_def]
   >> NO_TAC)
 ORELSE
 ( (* Log *)
   imp_res_tac (CONJUNCT1 infer_e_wfs)
   >> fs []
   >> imp_res_tac t_unify_wfs
   >> fs []
   >> first_x_assum drule
   >> first_x_assum drule
   >> rename1 `infer_e _ _ e _ = (Success t1, st1)`
   >> rename1 `infer_e _ _ e1 st1 = (Success t2, st2)`
   >> `ienv_ok (count st1.next_uvar) ienv` by metis_tac [ienv_ok_more, infer_e_next_uvar_mono]
   >> simp []
   >> disch_then drule
   >> strip_tac
   >> disch_then drule
   >> strip_tac
   >> rename1 `t_unify s1 _ _ = SOME s2`
   >> `t_walkstar s1 t1 = t_walkstar s1 (Infer_Tapp [] Tbool_num)`
     by (irule t_unify_apply >> metis_tac [])
   >> `t_walkstar s2 t2 = t_walkstar s2 (Infer_Tapp [] Tbool_num)`
     by (irule t_unify_apply >> metis_tac [])
   >> fs []
   >> drule sub_completion_unify2
   >> disch_then drule
   >> strip_tac
   >> qpat_x_assum `t_unify _ _ _ = _` mp_tac
   >> drule sub_completion_unify2
   >> disch_then drule
   >> rw []
   >> imp_res_tac sub_completion_infer
   >> first_x_assum drule
   >> first_x_assum drule
   >> imp_res_tac sub_completion_apply
   >> `t_wfs s` by metis_tac [sub_completion_wfs]
   >> simp [t_walkstar_eqn1, convert_t_def]);

Theorem infer_e_sound:
 (!l ienv e st st' tenv tenvE t extra_constraints s.
    infer_e l ienv e st = (Success t, st') ∧
    ienv_ok (count st.next_uvar) ienv ∧
    env_rel_sound s ienv tenv tenvE ∧
    t_wfs st.subst ∧
    sub_completion (num_tvs tenvE) st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_e tenv tenvE e (convert_t (t_walkstar s t))) ∧
 (!l ienv es st st' tenv tenvE ts extra_constraints s.
    infer_es l ienv es st = (Success ts, st') ∧
    ienv_ok (count st.next_uvar) ienv ∧
    env_rel_sound s ienv tenv tenvE ∧
    t_wfs st.subst ∧
    sub_completion (num_tvs tenvE) st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_es tenv tenvE es (MAP (convert_t o t_walkstar s) ts)) ∧
 (!l ienv pes t1 t2 st st' tenv tenvE extra_constraints s.
    infer_pes l ienv pes t1 t2 st = (Success (), st') ∧
    ienv_ok (count st.next_uvar) ienv ∧
    env_rel_sound s ienv tenv tenvE ∧
    t_wfs st.subst ∧
    sub_completion (num_tvs tenvE) st'.next_uvar st'.subst extra_constraints s
    ⇒
    type_pes (num_tvs tenvE) 0 tenv tenvE pes (convert_t (t_walkstar s t1)) (convert_t (t_walkstar s t2))) ∧
 (!l ienv funs st st' tenv tenvE extra_constraints s ts.
    infer_funs l ienv funs st = (Success ts, st') ∧
    ienv_ok (count st.next_uvar) ienv ∧
    env_rel_sound s ienv tenv tenvE ∧
    t_wfs st.subst ∧
    sub_completion (num_tvs tenvE) st'.next_uvar st'.subst extra_constraints s ∧
    ALL_DISTINCT (MAP FST funs)
    ⇒
    type_funs tenv tenvE funs (MAP2 (\(x,y,z) t. (x, (convert_t o t_walkstar s) t)) funs ts))
Proof
  ho_match_mp_tac infer_e_ind >>
  rw [infer_e_def, success_eqns, remove_pair_lem] >>
  rw [check_t_def] >>
  fs [check_t_def] >>
  ONCE_REWRITE_TAC [type_e_cases] >>
  rw [Tint_def, Tchar_def] >>
  imp_res_tac type_name_check_subst_state >>
  imp_res_tac type_name_check_subst_thm >>
  fs []
  >-
  (* Raise *)
     (fs [sub_completion_def, flookup_thm, count_add1, SUBSET_DEF] >>
     `st''.next_uvar < st''.next_uvar + 1` by decide_tac >>
     metis_tac [IN_INSERT, check_convert_freevars, prim_recTheory.LESS_REFL])
  >-
 (* Raise *)
     (imp_res_tac sub_completion_unify >>
     `type_e tenv tenvE e (convert_t (t_walkstar s t2))` by metis_tac [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_apply >>
     imp_res_tac sub_completion_apply >>
     imp_res_tac t_unify_wfs >>
     fs [] >>
     rw [] >>
     imp_res_tac sub_completion_wfs >>
     fs [t_walkstar_eqn1, convert_t_def, Texn_def])
  >- (
    Cases_on `pes` >>
    fs [failwith_def, success_eqns] >>
    first_x_assum match_mp_tac >>
    rw [] >>
    `?ts. sub_completion (num_tvs tenvE) st''.next_uvar st''.subst  ts s`
              by (imp_res_tac sub_completion_infer_pes >>
                  fs [] >>
                  metis_tac [sub_completion_more_vars]) >>
     metis_tac [])
  >-
     (
     Cases_on `pes = []` >>
     fs [failwith_def, success_eqns] >>
     `?ts. sub_completion (num_tvs tenvE) st''.next_uvar st''.subst  ts s`
              by (imp_res_tac sub_completion_infer_pes >>
                  fs [] >>
                  metis_tac [sub_completion_more_vars]) >>
     rw [RES_FORALL] >>
     `?p e. x = (p,e)` by (PairCases_on `x` >> metis_tac []) >>
     rw [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     `st.next_uvar ≤ st''.next_uvar` by metis_tac [infer_e_next_uvar_mono] >>
     `type_pes (num_tvs tenvE) 0 tenv tenvE pes (convert_t (t_walkstar s (Infer_Tapp [] Texn_num))) (convert_t (t_walkstar s t))` by metis_tac [ienv_ok_more] >>
     fs [type_pes_def, RES_FORALL] >>
     pop_assum (mp_tac o Q.SPEC `(p,e')`) >>
     rw [Texn_def] >>
     imp_res_tac sub_completion_wfs >>
     fs [t_walkstar_eqn1, convert_t_def, Texn_def] >>
     metis_tac [])
  >-
 (* Lit int *)
     binop_tac
  >-
 (* Lit char *)
     binop_tac
  >-
 (* Lit string *)
     binop_tac
 (* Lit word8 *)
 >- binop_tac
 (* Lit word64 *)
 >- binop_tac
 (* Lit float64 *)
 >- binop_tac
 >- ( (* Var *)
   drule env_rel_sound_lookup_some
   >> disch_then drule
   >> rw []
   >> rename1 `nsLookup _ _ = SOME v`
   >> `?tvs t. v = (tvs, t)` by metis_tac [pair_CASES]
   >> `t_wfs s` by metis_tac [sub_completion_wfs]
   >> drule tscheme_approx_thm
   >> var_eq_tac
   >> disch_then drule
   >> disch_then
     (qspec_then `MAP (t_walkstar s) (MAP (λn. Infer_Tuvar (st.next_uvar + n)) (COUNT_LIST tvs))` mp_tac)
   >> simp [LENGTH_COUNT_LIST, EVERY_MAP, every_count_list, check_t_def]
   >> impl_keep_tac
   >- fs [sub_completion_def, SUBSET_DEF]
   >> rw []
   >> rw []
   >> qexists_tac `MAP (convert_t o t_walkstar s) subst'`
   >> simp [EVERY_MAP]
   >> conj_tac
   >- (
     rfs [infer_deBruijn_subst_walkstar]
     >> metis_tac [db_subst_infer_subst_swap3])
   >- (
     fs [EVERY_MEM, sub_completion_def]
     >> rw []
     >> irule check_t_to_check_freevars
     >> irule (CONJUNCT1 check_t_walkstar)
     >> rw []
     >> metis_tac [pure_add_constraints_wfs]))
 >-
 (* Tup *)
     (`?ts env. v' = (ts,env)` by (PairCases_on `v'` >> metis_tac []) >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs, pure_add_constraints_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tref_def] >>
     metis_tac [MAP_MAP_o])
 >- ( (* Con *)
     rename1 `nsLookup _ _ = SOME v` >>
     `?tvs ts t. v = (tvs, ts, t)` by metis_tac [pair_CASES] >>
     rw [] >>
     fs [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs, infer_e_wfs, pure_add_constraints_wfs] >>
     rw [convert_t_def, t_walkstar_eqn1, MAP_MAP_o, combinTheory.o_DEF,
         EVERY_MAP, LENGTH_COUNT_LIST] >>
     drule sub_completion_add_constraints
     >> disch_then drule
     >> rw []
     >> drule sub_completion_infer_es
     >> qpat_x_assum `LENGTH tvs + st'''.next_uvar = st'.next_uvar`
       (assume_tac o GSYM o SIMP_RULE (bool_ss) [Once ADD_COMM])
     >> full_simp_tac bool_ss []
     >> drule sub_completion_more_vars
     >> strip_tac
     >> disch_then drule
     >> rw []
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> rw []
     >> fs [env_rel_sound_def]
     >> `t_wfs st'''.subst` by metis_tac [infer_e_wfs] >>
     simp [every_count_list] >>
     drule pure_add_constraints_apply >>
     disch_then drule >>
     simp [MAP_ZIP] >>
     strip_tac >>
     `t_wfs st'.subst` by metis_tac [pure_add_constraints_wfs] >>
     drule sub_completion_apply_list >>
     rpt (disch_then drule) >>
     simp_tac (bool_ss) [Once ADD_COMM] >>
     qpat_x_assum `t_wfs s` assume_tac >>
     drule (CONJUNCT2 subst_infer_subst_swap) >>
     strip_tac >>
     ASM_REWRITE_TAC [] >>
     strip_tac >>
     drule (METIS_PROVE [] ``!x y. x = y ⇒ MAP convert_t x = MAP convert_t y``) >>
     pop_assum kall_tac >>
     `EVERY (check_freevars 0 tvs) ts`
       by (
         fs [ienv_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def]
         >> drule nsLookup_nsAll
         >> disch_then drule
         >> rw []) >>
     simp [convert_t_subst, LENGTH_COUNT_LIST] >>
     strip_tac >>
     fs [MAP_MAP_o, combinTheory.o_DEF] >>
     rw [] >>
     mp_tac sub_completion_check >>
     simp [EVERY_MEM, PULL_FORALL] >>
     disch_then irule >>
     simp [MEM_COUNT_LIST] >>
     metis_tac [])
 >- ( (* Fun *)
   `t_wfs s ∧ t_wfs st'.subst` by metis_tac [infer_st_rewrs,sub_completion_wfs, infer_e_wfs]
   >> rw [t_walkstar_eqn1, convert_t_def, Tfn_def]
   >> imp_res_tac infer_e_next_uvar_mono
   >> fs []
   >> `st.next_uvar < st'.next_uvar` by decide_tac
   >- (
     fs [sub_completion_def, SUBSET_DEF] >>
     metis_tac [check_t_to_check_freevars])
   >- (
     first_x_assum drule
     >> disch_then irule
     >> simp []
     >> conj_tac >- (
       fs [ienv_ok_def, ienv_val_ok_def]
       >> irule nsAll_nsBind
       >> simp [check_t_def]
       >> irule nsAll_mono
       >> HINT_EXISTS_TAC
       >> rw []
       >> pairarg_tac
       >> fs []
       >> metis_tac [check_t_more3])
     >> conj_tac >- (
       irule env_rel_sound_extend0
       >> fs [sub_completion_def, check_t_def, SUBSET_DEF])
     >- metis_tac []))
 >-
 (* App *)
     (`?c. sub_completion (num_tvs tenvE) st''.next_uvar st''.subst c s`
           by metis_tac [constrain_op_sub_completion] >>
     res_tac >>
     simp [GSYM PULL_EXISTS, CONJ_ASSOC] >>
     rw []
     >- metis_tac [constrain_op_sound, infer_e_wfs] >>
     irule check_t_to_check_freevars >>
     irule (CONJUNCT1 check_t_walkstar) >>
     simp []
     >> conj_tac >- fs [sub_completion_def]
     >> conj_tac >- metis_tac [sub_completion_wfs, infer_e_wfs] >>
     imp_res_tac constrain_op_check_t >>
     drule (CONJUNCT1 (CONJUNCT2 infer_e_check_t)) >>
     simp [] >>
     fs [ienv_ok_def] >>
     rw [] >>
     fs [] >>
     irule (CONJUNCT1 check_t_more5) >>
     qexists_tac `count st'.next_uvar` >>
     fs [sub_completion_def] >>
     metis_tac [check_t_more2, DECIDE ``!x. x + 0 = x:num``])
 >- log_tac
 >- log_tac
 >- log_tac
 >- (* If *)
     (imp_res_tac sub_completion_unify2 >>
     imp_res_tac sub_completion_infer >>
     imp_res_tac sub_completion_infer >>
     fs [] >>
     imp_res_tac sub_completion_unify2 >>
     `type_e tenv tenvE e (convert_t (t_walkstar s t1))`
             by metis_tac [] >>
     `t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     imp_res_tac t_unify_apply >>
     `t_wfs s'`  by metis_tac [t_unify_wfs] >>
     imp_res_tac sub_completion_apply >>
     `t_wfs s` by metis_tac [sub_completion_wfs] >>
     fs [t_walkstar_eqn, t_walk_eqn, convert_t_def])
 >-
 (* If *)
     (`t_wfs (st'' with subst := s').subst`
                by (rw [] >>
                    metis_tac [t_unify_wfs, infer_e_wfs]) >>
     `st.next_uvar ≤ (st'' with subst := s').next_uvar`
                by (imp_res_tac infer_e_next_uvar_mono >>
                    fs [] >>
                    decide_tac) >>
     `?ts. sub_completion (num_tvs tenvE) st'''''.next_uvar st'''''.subst ts s`
               by metis_tac [sub_completion_unify2] >>
     imp_res_tac sub_completion_infer >>
     metis_tac [ienv_ok_more])
  >-
 (* If *)
    (`t_wfs (st'' with subst := s').subst`
                by (rw [] >>
                    metis_tac [t_unify_wfs, infer_e_wfs]) >>
     `t_wfs st''''.subst ∧ t_wfs st'''''.subst ∧ t_wfs st''.subst` by metis_tac [infer_e_wfs] >>
     `st.next_uvar ≤ st''''.next_uvar`
                by (imp_res_tac infer_e_next_uvar_mono >>
                    fs [] >>
                    decide_tac) >>
     `?ts. sub_completion (num_tvs tenvE) st'''''.next_uvar st'''''.subst ts s`
               by metis_tac [sub_completion_unify2] >>
     `type_e tenv tenvE e'' (convert_t (t_walkstar s t3))`
       by (
         first_x_assum irule >>
         simp [] >>
         qpat_x_assum `t_wfs st''''.subst` assume_tac >>
         goal_assum drule >>
         simp [] >>
         metis_tac [infer_e_next_uvar_mono, ienv_ok_more]) >>
     imp_res_tac t_unify_apply >>
     `t_wfs s''` by metis_tac [t_unify_wfs] >>
     imp_res_tac sub_completion_apply >>
     metis_tac [ienv_ok_more])
  >- ( (* Match *)
     Cases_on `pes = []` >>
     fs [failwith_def, success_eqns] >>
     `?ts. sub_completion (num_tvs tenvE) st''.next_uvar st''.subst  ts s`
              by (imp_res_tac sub_completion_infer_pes >>
                  fs [] >>
                  metis_tac [sub_completion_more_vars]) >>
     `type_e tenv tenvE e (convert_t (t_walkstar s t1))` by metis_tac [] >>
     qexists_tac `convert_t (t_walkstar s t1)` >>
     rw [RES_FORALL] >>
     `?p e. x = (p,e)` by (PairCases_on `x` >> metis_tac []) >>
     rw [] >>
     `t_wfs (st'' with next_uvar := st''.next_uvar + 1).subst`
              by (rw [] >>
                  metis_tac [infer_e_wfs]) >>
     `st.next_uvar ≤ (st'' with next_uvar := st''.next_uvar + 1).next_uvar`
              by (rw [] >>
                  imp_res_tac infer_e_next_uvar_mono >>
                  fs [] >>
                  decide_tac) >>
     `ienv_ok (count (st'' with next_uvar := st''.next_uvar + 1).next_uvar) ienv`
       by metis_tac [ienv_ok_more] >>
     `type_pes (num_tvs tenvE) 0 tenv tenvE pes (convert_t (t_walkstar s t1)) (convert_t (t_walkstar s (Infer_Tuvar st''.next_uvar)))`
              by metis_tac [] >>
     fs [type_pes_def, RES_FORALL] >>
     pop_assum (mp_tac o Q.SPEC `(p,e')`) >>
     rw [])
 >- ( (* Let *)
   imp_res_tac (CONJUNCT1 infer_e_wfs)
   >> fs []
   >> first_x_assum drule
   >> simp []
   >> disch_then drule
   >> rw []
   >> drule sub_completion_infer
   >> disch_then drule
   >> rw []
   >> first_x_assum drule
   >> rw []
   >> `check_t 0 (count st''.next_uvar) t1` by metis_tac [ienv_ok_def, infer_e_check_t]
   >> goal_assum drule
   >> first_x_assum drule
   >> disch_then irule
   >> simp []
   >> conj_tac >- (
     fs [ienv_ok_def, ienv_val_ok_def]
     >> irule nsAll_nsOptBind
     >> simp []
     >> conj_tac >- metis_tac [option_nchotomy]
     >> irule nsAll_mono
     >> HINT_EXISTS_TAC
     >> rw []
     >> pairarg_tac
     >> fs []
     >> metis_tac [check_t_more4, infer_e_next_uvar_mono])
   >> conj_tac >- (
     Cases_on `x`
     >> fs [namespaceTheory.nsOptBind_def, opt_bind_name_def]
     >> irule env_rel_sound_extend0
     >> fs [check_t_def, SUBSET_DEF]
     >> conj_tac >- fs [sub_completion_def]
     >> conj_tac >- metis_tac [sub_completion_wfs]
     >> fs [sub_completion_def]
     >> metis_tac [check_t_more5, check_t_more2, DECIDE ``x+0n = x``])
   >- (
     Cases_on `x`
     >> simp [opt_bind_name_def]
     >> metis_tac []))
 >- ( (* Letrec *)
   qmatch_assum_abbrev_tac
       `infer_funs _ (_ with inf_v := nsAppend bindings _) _ _ = (Success funs_ts, st1)`
   >> rename1 `pure_add_constraints st1.subst _ st2.subst`
   >> rename1 `infer_e _ _ _ _ = (Success t, st3)`
   >> drule (List.nth (CONJUNCTS infer_e_wfs, 3))
   >> rw []
   >> `t_wfs st2.subst ∧ t_wfs st3.subst ∧ t_wfs s`
     by metis_tac [infer_e_wfs, pure_add_constraints_wfs, sub_completion_wfs]
   >> Q.ABBREV_TAC `tenv' = MAP2 (λ(f,x,e) t. (f,t)) funs (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (st.next_uvar + n)))) (COUNT_LIST (LENGTH funs)))`
   >> `?constraints1. sub_completion (num_tvs tenvE) st2.next_uvar st2.subst constraints1 s`
                 by metis_tac [sub_completion_infer] >>
     `?constraints2. sub_completion (num_tvs tenvE) st1.next_uvar st1.subst constraints2 s`
                 by metis_tac [sub_completion_add_constraints] >>
     `env_rel_sound s (ienv with inf_v := nsAppend bindings ienv.inf_v) tenv (bind_var_list 0 tenv' tenvE)`
                 by (UNABBREV_ALL_TAC >>
                     simp_tac bool_ss [Once ADD_COMM] >>
                     match_mp_tac env_rel_e_sound_letrec_merge0 >>fs[]>>
                     imp_res_tac infer_e_wfs>>
                     fs[]>>
                     rw [] >>
                     rfs[sub_completion_def, SUBSET_DEF]>>
                     rw [] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     fs []) >>
     `ienv_ok (count (LENGTH funs + st.next_uvar))
       (ienv with inf_v := nsAppend bindings ienv.inf_v)`
                 by (fs [ienv_ok_def, ienv_val_ok_def] >>
                     irule nsAll_nsAppend >>
                     simp []
                     >> conj_tac >- rw [check_env_letrec_lem, Abbr `bindings`]
                     >> metis_tac [check_env_more, DECIDE ``x ≤ y+x:num``])
   >> first_x_assum drule
   >> asm_simp_tac (srw_ss()) []
   >> disch_then drule
   >> simp [num_tvs_bind_var_list]
   >> disch_then (qspec_then `constraints2` mp_tac)
   >> impl_keep_tac
   >- (
     irule sub_completion_more_vars
     >> `?x. st2.next_uvar + x = st1.next_uvar`
       suffices_by metis_tac []
     >> intLib.ARITH_TAC)
   >> `st.next_uvar + LENGTH funs ≤ st2.next_uvar`
                 by (fs [] >>
                     imp_res_tac infer_e_next_uvar_mono >>
                     fs [] >>
                     metis_tac [])
   >> fs []
   >> `type_e tenv (bind_var_list 0 tenv' tenvE) e (convert_t (t_walkstar s t))`
             by (first_x_assum match_mp_tac >>
                 rw [] >>
                 metis_tac [ienv_ok_more])
   >> rw []
   >> qexists_tac `tenv'`
   >> rw [bind_tvar_def]
   >> `tenv' = MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s t))) funs funs_ts`
                 by (Q.UNABBREV_TAC `tenv'` >>
                     simp_tac bool_ss [Once ADD_COMM] >>
                     match_mp_tac letrec_lemma >>
                     imp_res_tac pure_add_constraints_apply >>
                     `LENGTH funs = LENGTH funs_ts` by metis_tac [LENGTH_COUNT_LIST] >>
                     fs [GSYM MAP_MAP_o, MAP_ZIP, LENGTH_COUNT_LIST, LENGTH_MAP] >>
                     metis_tac [MAP_MAP_o, combinTheory.o_DEF, sub_completion_apply_list])
   >> rw [])
 >- (* Tannot*)
    (drule (hd (CONJUNCTS infer_e_wfs)) >>
     disch_then drule >>
     rw [] >>
     drule t_unify_apply >>
     disch_then drule >>
     rw [] >>
     drule t_unify_wfs >>
     disch_then drule >>
     imp_res_tac sub_completion_wfs >>
     rw [] >>
     drule sub_completion_apply >>
     rpt (disch_then drule) >>
     rw [] >>
     fs [ienv_ok_def] >>
     drule check_freevars_type_name_subst >>
     rpt (disch_then drule) >>
     disch_then (qspec_then `0` mp_tac)>>
     rw [] >>
     `check_t 0 {} (infer_type_subst [] (type_name_subst ienv.inf_t t))`
       by metis_tac [infer_type_subst_empty_check] >>
     qpat_x_assum `t_wfs s` assume_tac >>
     imp_res_tac t_walkstar_no_vars >>
     simp [] >>
     drule (hd (CONJUNCTS infer_type_subst_nil)) >>
     rw [] >>
     fs [env_rel_sound_def] >>
     irule check_freevars_empty_convert_unconvert_id >>
     metis_tac [check_freevars_empty_convert_unconvert_id])
 >- (* Tannot *)
    (fs [env_rel_sound_def] >>
     metis_tac [])
 >- (* Tannot*)
    (`convert_t (t_walkstar s t') = type_name_subst tenv.t t`
       by (* This is the previous goal *)
       (drule (hd (CONJUNCTS infer_e_wfs)) >>
        disch_then drule >>
        rw [] >>
        drule t_unify_apply >>
        disch_then drule >>
        rw [] >>
        drule t_unify_wfs >>
        disch_then drule >>
        imp_res_tac sub_completion_wfs >>
        rw [] >>
        drule sub_completion_apply >>
        rpt (disch_then drule) >>
        rw [] >>
        fs [ienv_ok_def] >>
        drule check_freevars_type_name_subst >>
        rpt (disch_then drule) >>
        disch_then(qspec_then`0` mp_tac)>>
        rw [] >>
        `check_t 0 {} (infer_type_subst [] (type_name_subst ienv.inf_t t))`
          by metis_tac [infer_type_subst_empty_check] >>
        qpat_x_assum `t_wfs s` assume_tac >>
        imp_res_tac t_walkstar_no_vars >>
        simp [] >>
        drule (hd (CONJUNCTS infer_type_subst_nil)) >>
        rw [] >>
        fs [env_rel_sound_def] >>
        irule check_freevars_empty_convert_unconvert_id >>
        metis_tac [check_freevars_empty_convert_unconvert_id]) >>
     pop_assum (assume_tac o GSYM) >>
     rw [] >>
     first_x_assum irule >> rw [] >>
     imp_res_tac sub_completion_unify2 >>
     metis_tac [APPEND_ASSOC, APPEND, sub_completion_add_constraints])
 >- metis_tac [sub_completion_infer_es]
 >- metis_tac [sub_completion_infer_es]
 >- metis_tac [infer_e_wfs, infer_e_next_uvar_mono, ienv_ok_more]
 >- rw [type_pes_def, RES_FORALL]
 >- (
     `?t env'. v' = (t,env')` by (PairCases_on `v'` >> metis_tac []) >>
     rw [] >>
     `∃ts. sub_completion (num_tvs tenvE) (st'''' with subst:= s'').next_uvar (st'''' with subst:= s'').subst ts s`
                   by metis_tac [sub_completion_infer_pes] >>
     fs [] >>
     `∃ts. sub_completion (num_tvs tenvE) st''''.next_uvar st''''.subst ts s`
              by metis_tac [sub_completion_unify2] >>
     `∃ts. sub_completion (num_tvs tenvE) (st'' with subst := s').next_uvar (st'' with subst := s').subst ts s`
              by metis_tac [sub_completion_infer] >>
     fs [] >>
     `∃ts. sub_completion (num_tvs tenvE) st''.next_uvar st''.subst ts s`
              by metis_tac [sub_completion_unify2] >>
     `type_p (num_tvs tenvE) tenv p (convert_t (t_walkstar s t)) (convert_env s env')`
              by metis_tac [infer_p_sound, ienv_ok_def, env_rel_sound_def] >>
     `t_wfs (st'' with subst := s').subst`
           by (rw [] >>
               metis_tac [infer_p_wfs, t_unify_wfs]) >>
     imp_res_tac infer_p_check_t >>
     `ienv_ok (count (st'' with subst:=s').next_uvar) (ienv with inf_v := nsAppend (alist_to_ns (MAP (λ(n,t). (n,0,t)) (SND (t,env')))) ienv.inf_v)`
           by (
             fs [ienv_ok_def, ienv_val_ok_def]
             >> irule nsAll_nsAppend
             >> simp []
             >> conj_tac >- (
               irule nsAll_alist_to_ns
               >> simp [EVERY_MAP, EVERY_MEM]
               >> rw []
               >> pairarg_tac
               >> fs []
               >> pairarg_tac
               >> fs []
               >> pairarg_tac
               >> fs []
               >> rw []
               >> fs [EVERY_MEM]
               >> first_x_assum drule
               >> simp [])
             >- (
               irule nsAll_mono
               >> HINT_EXISTS_TAC
               >> drule (CONJUNCT1 infer_p_next_uvar_mono)
               >> rw []
               >> pairarg_tac
               >> fs []
               >> metis_tac [check_t_more4])) >>
     `env_rel_sound s
       (ienv with inf_v := nsAppend (alist_to_ns (MAP (λ(n,t). (n,0,t)) env')) ienv.inf_v)
       tenv
       (bind_var_list 0 (convert_env s env') tenvE)`
              by (
                irule env_rel_sound_merge0
                >> simp []
                >> imp_res_tac sub_completion_wfs
                >> fs [sub_completion_def]
                >> fs [EVERY_MEM]
                >> rw []
                >> pairarg_tac
                >> fs []
                >> `(λ(x,t). check_t 0 (count st''.next_uvar) t) e'` by metis_tac []
                >> rw []
                >> fs []
                >> metis_tac [check_t_more5]) >>
     `type_e tenv (bind_var_list 0 (convert_env s env') tenvE) e (convert_t (t_walkstar s t2'))`
               by (
                 first_x_assum match_mp_tac >>
                 rw [] >>
                 metis_tac [SND, num_tvs_bind_var_list]) >>
     rw [type_pes_cons] >|
     [imp_res_tac infer_p_bindings >>
          metis_tac [APPEND_NIL],
      qexists_tac `(convert_env s env')` >>
           rw [] >>
           imp_res_tac infer_p_wfs >>
           imp_res_tac infer_e_wfs >>
           imp_res_tac t_unify_apply >>
           metis_tac [t_unify_wfs, sub_completion_apply],
      `t_wfs (st'''' with subst := s'').subst`
           by (rw [] >>
               metis_tac [t_unify_wfs, infer_e_wfs]) >>
          `(st.next_uvar ≤ (st'''' with subst := s'').next_uvar)`
                  by (fs [] >>
                      imp_res_tac infer_p_next_uvar_mono >>
                      imp_res_tac infer_e_next_uvar_mono >>
                      fs [] >>
                      decide_tac) >>
          `ienv_ok (count (st'''' with subst := s'').next_uvar) ienv` by metis_tac [ienv_ok_more] >>
          metis_tac []])
 >- (
 `t_wfs st'''.subst ∧ t_wfs (st with next_uvar := st.next_uvar + 1).subst` by metis_tac [infer_e_wfs, infer_st_rewrs] >>
     imp_res_tac sub_completion_infer_funs >>
     `env_rel_sound s
         (ienv with inf_v := nsBind x (0,Infer_Tuvar st.next_uvar) ienv.inf_v)
         tenv
         (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenvE)`
              by (match_mp_tac env_rel_sound_extend0 >>
                  fs[]>>
                  rw []
                  >- metis_tac[sub_completion_wfs]
                  >> fs [sub_completion_def, check_t_def, SUBSET_DEF]
                  >> imp_res_tac infer_e_next_uvar_mono
                  >> fs [])>>
     `num_tvs (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenvE) = num_tvs tenvE`
              by fs [num_tvs_def] >>
     `ienv_ok (count (st with next_uvar := st.next_uvar + 1).next_uvar) ienv ∧
      check_t 0 (count (st with next_uvar := st.next_uvar + 1).next_uvar) (Infer_Tuvar st.next_uvar)`
                by (rw [check_t_def] >>
                    metis_tac [ienv_ok_more, DECIDE ``x ≤ x + 1:num``]) >>
     `type_e tenv (Bind_name x 0 (convert_t (t_walkstar s (Infer_Tuvar st.next_uvar))) tenvE) e (convert_t (t_walkstar s t))`
                 by (first_x_assum match_mp_tac
                     >> rw []
                     >> goal_assum drule
                     >> fs []
                     >> HINT_EXISTS_TAC
                     >> rw []
                     >> fs [ienv_ok_def, ienv_val_ok_def]
                     >> irule nsAll_nsBind
                     >> rw []) >>
     `ienv_ok (count st'''.next_uvar) ienv`
                 by (metis_tac [ienv_ok_more, infer_e_next_uvar_mono]) >>
     `type_funs tenv tenvE funs (MAP2 (\(x,y,z) t. (x, convert_t (t_walkstar s t))) funs ts')`
               by metis_tac [] >>
     `t_wfs s` by metis_tac [sub_completion_wfs] >>
     rw [t_walkstar_eqn1, convert_t_def, Tfn_def] >|
     [rw [check_freevars_def] >>
          match_mp_tac check_t_to_check_freevars >>
          rw [] >>
          fs [sub_completion_def] >|
          [`st.next_uvar < st'''.next_uvar`
                    by (imp_res_tac infer_e_next_uvar_mono >>
                        fs [] >>
                        decide_tac) >>
               `st.next_uvar ∈ FDOM s`
                    by fs [count_def, SUBSET_DEF] >>
               metis_tac [],
           match_mp_tac (hd (CONJUNCTS check_t_walkstar)) >>
               rw [] >>
               `check_t 0 (count (st'''.next_uvar)) t`
                         by (imp_res_tac infer_e_check_t >>
                             fs []
                             >> first_x_assum irule
                             >> fs [ienv_ok_def, ienv_val_ok_def]
                             >> irule nsAll_nsBind
                             >> simp []) >>
               metis_tac [check_t_more2, DECIDE ``x+0n = x``, check_t_more5]],
      imp_res_tac infer_funs_length >>
          rw [ALOOKUP_FAILS, MAP2_MAP, MEM_MAP, MEM_ZIP] >>
          PairCases_on `y` >>
          fs [MEM_MAP, MEM_EL] >>
          metis_tac [FST]])
QED
