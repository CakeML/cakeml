open preamble;
open alistTheory optionTheory rich_listTheory;
open miscTheory;
open astTheory;
open semanticPrimitivesTheory;
open libTheory;
open libPropsTheory;
open conLangTheory;
open decLangTheory;
open exhLangTheory;
open evalPropsTheory;
open compilerTerminationTheory;

val _ = new_theory "exhLangProof";

val v_to_exh_def = tDefine "v_to_exh" `
(v_to_exh exh (Litv_i2 l) =
  Litv_exh l) ∧
(v_to_exh exh (Conv_i2 t vs) =
  Conv_exh (FST t) (vs_to_exh exh vs)) ∧
(v_to_exh exh (Closure_i2 env x e) =
  Closure_exh (env_to_exh exh env) x (exp_to_exh exh e)) ∧
(v_to_exh exh (Recclosure_i2 env funs x) =
  Recclosure_exh (env_to_exh exh env) (funs_to_exh exh funs) x) ∧
(v_to_exh exh (Loc_i2 l) =
  Loc_exh l) ∧
(vs_to_exh exh [] = []) ∧
(vs_to_exh exh (v::vs) = v_to_exh exh v :: vs_to_exh exh vs) ∧
(env_to_exh exh [] = []) ∧
(env_to_exh exh ((x,v)::env) = (x,v_to_exh exh v) :: env_to_exh exh env)`
cheat;

val store_to_exh_def = Define `
store_to_exh exh (s,genv) =
  ((FST s, MAP (v_to_exh exh) (SND s)), MAP (OPTION_MAP (v_to_exh exh)) genv)`;

val result_to_exh_def = Define `
(result_to_exh r exh (s,res) =
  (store_to_exh exh s,
   case res of
     | Rval v => Rval (r exh v)
     | Rerr (Rraise v) => Rerr (Rraise (v_to_exh exh v))
     | Rerr Rtimeout_error => Rerr Rtimeout_error
     | Rerr Rtype_error => Rerr Rtype_error))`;

val exists_match_def = Define `
exists_match exh s ps v ⇔
  !env. ?p. MEM p ps ∧ pmatch_i2 exh s p v env ≠ No_match`;

val exh_to_exists_match = Q.prove (
`!exh ps. exhaustive_match exh ps ⇒ !s v. exists_match exh s ps v`,
 rw [exhaustive_match_def, exists_match_def] >>
 every_case_tac >>
 fs [get_tags_def, pmatch_i2_def]
 >- (cases_on `v` >>
     rw [pmatch_i2_def] >>
     cases_on `l` >>
     fs [lit_same_type_def])
 >- (cases_on `v` >>
     rw [pmatch_i2_def] >>
     PairCases_on `p` >>
     Cases_on `p1` >>
     fs [pmatch_i2_def] >>
     cheat)
 >- (cases_on `v` >>
     rw [pmatch_i2_def] >>
     PairCases_on `p` >>
     Cases_on `p1` >>
     fs [pmatch_i2_def] >>
     Cases_on `x` >>
     fs [pmatch_i2_def])
 >- (cases_on `v` >>
     rw [pmatch_i2_def] >>
     every_case_tac)
 >- (every_case_tac >>
     fs [] >>
     cheat));

val exp_to_exh_correct = Q.store_thm ("exp_to_exh_correct",
`(!ck env s e r.
  evaluate_i3 ck env s e r
  ⇒
  !exh env'.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ⇒
    evaluate_exh ck (env_to_exh exh env') (store_to_exh exh s) (exp_to_exh exh e) (result_to_exh v_to_exh exh r)) ∧
 (!ck env s es r.
  evaluate_list_i3 ck env s es r
  ⇒
  !exh env'.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ⇒
    evaluate_list_exh ck (env_to_exh exh env') (store_to_exh exh s) (exps_to_exh exh es) (result_to_exh vs_to_exh exh r)) ∧
 (!ck env s v pes err_v r.
  evaluate_match_i3 ck env s v pes err_v r
  ⇒
  !exh env' pes' is_handle.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ∧
    (pes' = add_default is_handle F pes ∨
     exists_match exh (SND (FST s)) (MAP FST pes) v ∧ pes' = add_default is_handle T pes)
     ⇒
    evaluate_match_exh ck (env_to_exh exh env') (store_to_exh exh s) (v_to_exh exh v)
                          (pat_exp_to_exh exh pes')
                          (result_to_exh v_to_exh exh r))`,
 ho_match_mp_tac evaluate_i3_ind >>
 rw [exp_to_exh_def, v_to_exh_def, result_to_exh_def] >>
 ONCE_REWRITE_TAC [evaluate_exh_cases] >>
 fs [v_to_exh_def, result_to_exh_def, store_to_exh_def] >>
 TRY (Cases_on `err`) >>
 fs [] >>
 rw []
 >- (cases_on `exhaustive_match exh (MAP FST pes)` >>
     fs [] >>
     metis_tac [pair_CASES, exh_to_exists_match])
 >- (induct_on `env` >>
     rw [] >>
     PairCases_on `h` >>
     fs [v_to_exh_def] >>
     rw [] >>
     fs [])
 >- (`n < LENGTH genv` by decide_tac >>
     rw [EL_MAP])
 >- (fs [do_uapp_exh_def, do_uapp_i3_def] >>
     every_case_tac >>
     fs [v_to_exh_def] >>
     rw []
     >- (MAP_EVERY qexists_tac [`Loc_exh n`, `MAP (v_to_exh exh) s2`] >>
         rw [] >>
         fs [store_lookup_def, EL_MAP])
     >- (fs [LET_THM, store_alloc_def] >>
         rw [v_to_exh_def])
     >- (MAP_EVERY qexists_tac [`v_to_exh exh v`, `MAP (v_to_exh exh) s2`, `MAP (OPTION_MAP (v_to_exh exh)) genv2`] >>
         rw [LUPDATE_MAP, EL_MAP, v_to_exh_def]))
 >- (fs [do_app_exh_def, do_app_i2_def] >>
     every_case_tac >>
     fs [v_to_exh_def] >>
     rw [] >>
     cheat)
 >- cheat
 >- cheat
 >- metis_tac []
 >- metis_tac []
 >- (fs [do_if_i2_def, do_if_exh_def] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     cheat)
 >- (res_tac >>
     fs [] >>
     cases_on `exhaustive_match exh (MAP FST pes)` >>
     fs []  >>
     metis_tac [exh_to_exists_match])
 >- cheat
 >- cheat
 >- (induct_on `n` >>
     rw [GENLIST])
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (rw [add_default_def, exp_to_exh_def, pat_bindings_exh_def, pat_to_exh_def, pmatch_exh_def] >>
     ONCE_REWRITE_TAC [evaluate_exh_cases] >>
     rw [] >>
     (* This case is probably false *)
     cheat)
 >- fs [exists_match_def]
 >- cheat
 >- (rw [add_default_def, exp_to_exh_def] >>
     cheat)
 >- cheat
 >- cheat);

val _ = export_theory ();
