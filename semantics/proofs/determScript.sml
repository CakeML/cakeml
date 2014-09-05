(* Determinism for the big-step semantics *)

open preamble semanticPrimitivesTheory bigStepTheory replTheory;

val _ = new_theory "determ";

(* ------------------------- Big step determinacy ----------------------- *)

val big_exp_determ = Q.store_thm ("big_exp_determ",
`(∀ck env s e r1.
   evaluate ck env s e r1 ⇒
   ∀r2. evaluate ck env s e r2 ⇒
   (r1 = r2)) ∧
 (∀ck env s es r1.
   evaluate_list ck env s es r1 ⇒
   ∀r2. evaluate_list ck env s es r2 ⇒
   (r1 = r2)) ∧
 (∀ck env s v pes err_v r1.
   evaluate_match ck env s v pes err_v r1 ⇒
   ∀r2. evaluate_match ck env s v pes err_v r2 ⇒
   (r1 = r2))`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw [] >>
res_tac >>
fs [] >>
rw [] >> 
metis_tac []);

val dec_determ = Q.store_thm ("dec_determ",
`!ck mn s env d r1.
  evaluate_dec ck mn env s d r1 ⇒
  !r2.
    evaluate_dec ck mn env s d r2
    ⇒
    (r1 = r2)`,
rw [evaluate_dec_cases] >>
metis_tac [big_exp_determ, result_11, result_distinct,PAIR_EQ,NOT_EXISTS,NOT_EVERY, match_result_11, match_result_distinct, optionTheory.SOME_11]);

val decs_determ = Q.store_thm ("decs_determ",
`!ck mn env s ds r1.
  evaluate_decs ck mn env s ds r1 ⇒
  !r2.
    evaluate_decs ck mn env s ds r2
    ⇒
    (r1 = r2)`,
HO_MATCH_MP_TAC evaluate_decs_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_decs_cases]) >>
fs [] >>
rw [] >>
metis_tac [dec_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11]);

val top_determ = Q.store_thm ("top_determ",
`!ck env s top r1.
  evaluate_top ck env s top r1 ⇒
  !r2.
    evaluate_top ck env s top r2
    ⇒
    (r1 = r2)`,
rw [evaluate_top_cases] >>
metis_tac [dec_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11,
           decs_determ]);

val prog_determ = Q.store_thm ("prog_determ",
`!ck env s ds r1.
  evaluate_prog ck env s ds r1 ⇒
  !r2.
    evaluate_prog ck env s ds r2
    ⇒
    (r1 = r2)`,
HO_MATCH_MP_TAC evaluate_prog_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_prog_cases]) >>
fs [] >>
rw [] >>
metis_tac [top_determ, result_11, result_distinct,PAIR_EQ,
           match_result_11, match_result_distinct, optionTheory.SOME_11]);

val whole_prog_determ = Q.store_thm ("whole_prog_determ",
`!ck env s ds r1.
  evaluate_whole_prog ck env s ds r1 ⇒
  !r2.
    evaluate_whole_prog ck env s ds r2
    ⇒
    (r1 = r2)`,
 rw [] >>
 PairCases_on `r1` >>
 PairCases_on `r2` >>
 fs [evaluate_whole_prog_def] >>
 every_case_tac >>
 fs [] >>
 imp_res_tac prog_determ >>
 rw []);

val _ = export_theory ();
