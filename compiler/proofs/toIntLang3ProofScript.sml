open preamble;
open alistTheory optionTheory rich_listTheory;
open miscTheory;
open astTheory;
open semanticPrimitivesTheory;
open libTheory;
open libPropsTheory;
open intLang2Theory;
open intLang3Theory;
open evalPropsTheory;

val _ = new_theory "toIntLang3Proof";

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

(*
val (pat_to_i2_def, pat_to_i2_ind) =
  tprove_no_defn ((pat_to_i2_def, pat_to_i2_ind),
  wf_rel_tac `inv_image $< (\(x,p). pat_size p)` >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  induct_on `ps` >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "pat_to_i2" pat_to_i2_def pat_to_i2_ind;
*)

val exp_to_i3_correct = Q.prove (
`(∀b env s e res. 
   evaluate_i2 b env s e res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' genv env' r.
     (res = (s',r)) ∧
     (env = (genv,env'))
     ⇒
     evaluate_i3 b env' (s,genv) e ((s',genv),r)) ∧
 (∀b env s es res.
   evaluate_list_i2 b env s es res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' genv env' r.
     (res = (s',r)) ∧
     (env = (genv,env'))
     ⇒
     evaluate_list_i3 b env' (s,genv) es ((s',genv),r)) ∧
 (∀b env s v pes err_v res. 
   evaluate_match_i2 b env s v pes err_v res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' genv env' r.
     (res = (s',r)) ∧
     (env = (genv,env'))
     ⇒
     evaluate_match_i3 b env' (s,genv) v pes err_v ((s',genv),r))`,
 ho_match_mp_tac evaluate_i2_ind >>
 rw [] >>
 rw [Once evaluate_i3_cases] >>
 fs [all_env_i2_to_genv_def, all_env_i2_to_env_def]
 >- metis_tac []
 >- (* Uapp *)
    (fs [do_uapp_i2_def, do_uapp_i3_def] >>
     every_case_tac >>
     fs [LET_THM]
     >- (Q.LIST_EXISTS_TAC [`Loc_i2 n`,`s2`] >>
         rw [])
     >- (Q.LIST_EXISTS_TAC [`v`, `s2`, `genv`] >>
         rw [] >>
         cases_on `store_alloc v s2` >>
         fs []))
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []);

 (*
val eval_i3_genv_weakening = Q.prove (
`(∀b env s e res. 
   evaluate_i3 b env s e res ⇒ 
   !s' s'' genv env' r genv''.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r))
     ⇒
     evaluate_i3 b env (s',genv++genv'') e ((s'',genv'++genv''),r)) ∧
 (∀b env s es res.
   evaluate_list_i3 b env s es res ⇒ 
   !s' s'' genv genv' genv'' env' r.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r))
     ⇒
     evaluate_list_i3 b env (s',genv++genv'') es ((s'',genv'++genv''),r) )∧
 (∀b env s v pes err_v res. 
   evaluate_match_i3 b env s v pes err_v res ⇒ 
   !s' s'' genv genv' genv'' env' r.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r))
     ⇒
     evaluate_match_i3 b env (s',genv++genv'') v pes err_v ((s'',genv'++genv''),r))`,

 ho_match_mp_tac evaluate_i3_ind >>
 rw [] >>
 srw_tac [ARITH_ss] [Once evaluate_i3_cases] >>
 >- cheat
 >- srw_tac [ARITH_ss] [EL_APPEND1]
 >- srw_tac [ARITH_ss] [EL_APPEND1]
 >- (CCONTR_TAC >>
     fs [arithmeticTheory.NOT_GREATER]
     >- decide_tac 
     >- cheat)
 >- metis_tac []
 >- (fs [do_uapp_i3_def] >>
     every_case_tac >>
     fs [LET_THM]
     >- (Q.LIST_EXISTS_TAC [`Loc_i2 n`,`s2`] >>
         rw [])
     >- (Q.LIST_EXISTS_TAC [`v`, `s2`] >>
         rw [] >>
         cases_on `store_alloc v s2` >>
         fs []))
 >- (rw [] >>
     Q.LIST_EXISTS_TAC [`v`, `s2`, `genv++genv''`] >>
     rw []
     >- metis_tac []




val (result_to_i3_rules, result_to_i3_ind, result_to_i3_cases) = Hol_reln `
(∀v. result_to_i3 NONE (Rval v)) ∧
(∀err. result_to_i3 (SOME err) (Rerr err))`;

val eval_i3_extend_genv = Q.prove (
`!b env s genv n s' genv' v.
  evaluate_i3 b env (s,genv) (Extend_global_i2 n) (s',r)
  ⇔
  r = Rval (Litv_i2 Unit) ∧
  s' = (s,genv ++ GENLIST (\x. NONE) n)`,
 rw [Once evaluate_i3_cases] >>
 metis_tac []);

val eval_i3_con =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Con_i2 tag es) (s',r)``;

val eval_i3_mat =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Mat_i2 e pes) (s',r)``;

val decs_to_i3_correct = Q.prove (
`!genv s ds r next.
  evaluate_decs_i2 genv s ds r ∧
  SND (SND r) ≠ SOME Rtype_error
  ⇒
  ?r_i3.
    evaluate_list_i3 F [] ((0,s),genv ++ GENLIST (\x. NONE) (num_defs ds)) (decs_to_i3 next ds) r_i3`

 induct_on `ds` >>
 rw [decs_to_i3_def]
 >- rw [Once evaluate_i3_cases] >>
 Cases_on `h` >>
 qpat_assum `evaluate_decs_i2 x0 x1 x2 x3` (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_decs_i2_cases]) >>
 rw [num_defs_def, LET_THM] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [] >>
 fs [evaluate_dec_i2_cases] >>
 rw [] >>
 imp_res_tac exp_to_i3_correct >>
 fs [emp_def] >>
 pop_assum mp_tac >>
 rw [eval_i3_mat]

 metis_tac []

val prompt_to_i3_correct =
`!genv s p new_env s' r next next' es.
  evaluate_prompt_i2 genv s p (s',new_env,r) ∧
  ((next',es) = prompt_to_i3 next p)
  ⇒
  ?r_i3.
    result_to_i3 r r_i3 ∧
    evaluate_list_i3 F [] ((0,s),genv) es (((0,s'),genv++MAP SOME new_env),r_i3)`,

 rw [evaluate_prompt_i2_cases, prompt_to_i3_def] >>
 fs [LET_THM] >>
 rw [result_to_i3_cases] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [eval_i3_extend_genv] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [eval_i3_con]
 *)

val _ = export_theory ();
