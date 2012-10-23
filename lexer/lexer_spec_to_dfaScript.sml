open preamble;
open dfaTheory regexpTheory lexer_runtimeTheory;

val _ = new_theory "lexer_spec_to_dfa"

val is_error_state_def = Define `
is_error_state lex_spec =
  EVERY (λ(regexp,action). is_regexp_empty regexp) lex_spec`;

val lex_spec_to_dfa_def = Define `
lex_spec_to_dfa lex_spec = 
  ((\(state,c). 
    let state' = MAP (\(regexp,action). (deriv c regexp, action)) state in
      if is_error_state state' then
        NONE
      else
        SOME state'),
   lex_spec,
   (\state.
     case FILTER (\(regexp,action). nullable regexp) state of
       | (regexp,action)::_ => SOME action
       | _ => NONE))`;

val lex_spec_action_lem = Q.prove (
`n < LENGTH start_st ∧
 (FST (lex_spec_to_dfa lex_spec) (start_st,c) = SOME start_st') 
 ⇒
 (SND (EL n start_st) = SND (EL n start_st'))`,
rw [LET_THM, lex_spec_to_dfa_def] >>
rw [EL_MAP] >>
cases_on `EL n start_st` >>
rw []);

val lex_spec_trans_lem = Q.prove (
`n < LENGTH start_st' ∧
 n < LENGTH start_st ∧
 (FST (lex_spec_to_dfa lex_spec) (start_st,c) = SOME start_st') ∧
 regexp_matches (FST (EL n start_st')) (MAP FST p)
 ⇒
 regexp_matches (FST (EL n start_st)) (STRING c (MAP FST p))`,
rw [LET_THM, lex_spec_to_dfa_def] >>
POP_ASSUM MP_TAC >>
rw [EL_MAP] >>
cases_on `EL n start_st` >>
fs [regexp_matches_deriv, deriv_matches_def]);

val lex_spec_trans_lem2 = Q.prove (
`n' < n ∧
 n' < LENGTH start_st' ∧
 n' < LENGTH start_st ∧
 (FST (lex_spec_to_dfa lex_spec) (start_st,c) = SOME start_st') ∧
 ¬regexp_matches (FST (EL n' start_st')) (MAP FST p)
 ⇒
 ¬regexp_matches (FST (EL n' start_st)) (STRING c (MAP FST p))`,
rw [LET_THM, lex_spec_to_dfa_def] >>
POP_ASSUM MP_TAC >>
rw [EL_MAP] >>
cases_on `EL n' start_st` >>
fs [regexp_matches_deriv, deriv_matches_def]);

val path_to_spec = Q.prove (
`!trans start_st end_st p.
  dfa_path trans start_st end_st p 
  ⇒
  !t.
    (trans = FST (lex_spec_to_dfa lex_spec)) ∧
    (SND (SND (lex_spec_to_dfa lex_spec)) end_st = SOME t)
    ⇒
    ∃n.
      n < LENGTH start_st ∧ (SND (EL n start_st) = t) ∧
      regexp_matches (FST (EL n start_st)) (MAP FST p) ∧
      (∀n'. n' < n ⇒ ¬regexp_matches (FST (EL n' start_st)) (MAP FST p))`,
ho_match_mp_tac dfa_path_ind >>
rw [LET_THM,dfa_path_def] >|
[fs [lex_spec_to_dfa_def] >>
     cases_on `FILTER (λ(regexp,action). nullable regexp) end_st` >>
     fs [] >>
     PairCases_on `h`  >>
     fs [] >>
     rw [] >>
     Induct_on `end_st` >>
     rw [] >>
     fs [] >|
     [qexists_tac `0` >>
          rw [] >>
          metis_tac [nullable_thm],
      qexists_tac `SUC n` >>
          fs [] >>
          rw [] >>
          cases_on `n'` >>
          fs [] >>
          PairCases_on `h` >>
          fs [] >>
          metis_tac [nullable_thm]],
 cases_on `FST (lex_spec_to_dfa lex_spec) (start_st,c)` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     `n < LENGTH start_st` 
              by (fs [LET_THM,lex_spec_to_dfa_def] >>
                  metis_tac [LENGTH_MAP]) >>
     qexists_tac `n` >>
     rw [] >>
     metis_tac [arithmeticTheory.LESS_TRANS, lex_spec_action_lem, lex_spec_trans_lem, lex_spec_trans_lem2]]);

val spec_to_path = Q.prove (
`∀n lex_spec l.
  n < LENGTH lex_spec ∧
  regexp_matches (FST (EL n lex_spec)) l ∧
  (∀n'. n' < n ⇒ ¬regexp_matches (FST (EL n' lex_spec)) l)
  ⇒
  ∃p s.
    (l = MAP FST p) ∧
    dfa_path (FST (lex_spec_to_dfa lex_spec)) (FST (SND (lex_spec_to_dfa lex_spec))) s p ∧
    (SND (SND (lex_spec_to_dfa lex_spec)) s = SOME (SND (EL n lex_spec)))`,
induct_on `l` >>
rw [] >|
[qexists_tac `lex_spec` >>
     rw [dfa_path_def, lex_spec_to_dfa_def, nullable_thm] >>
     REPEAT (pop_assum mp_tac) >>
     Q.SPEC_TAC (`lex_spec`, `lex_spec`) >>
     induct_on `n` >>
     rw [] >>
     cases_on `lex_spec` >>
     fs [] >>
     PairCases_on `h` >>
     fs [] >>
     rw [] >-
     metis_tac [DECIDE ``0 < SUC n``, EL, FST, HD, TL] >>
     res_tac >>
     pop_assum match_mp_tac >>
     rw [] >>
     `SUC n' < SUC n` by decide_tac >>
     metis_tac [EL, FST, HD, TL],
 `∀n'. n' < n ⇒
         ¬deriv_matches (FST (EL n' (MAP (λ(regexp,action). (deriv h regexp,action)) lex_spec))) l`
               by (rw [] >>
                   `n' < LENGTH lex_spec` by decide_tac >>
                   rw [EL_MAP, LENGTH_MAP] >>
                   fs [deriv_matches_def, regexp_matches_deriv] >>
                   cases_on  `EL n' lex_spec` >>
                   rw [] >>
                   metis_tac [FST]) >>
     qpat_assum `!n lex_spec. P n lex_spec` 
            (MP_TAC o Q.SPECL [`n`, `THE ((FST (lex_spec_to_dfa lex_spec)) (lex_spec,h))`]) >>
     rw [lex_spec_to_dfa_def, EL_MAP, LET_THM] >>
     cases_on `EL n lex_spec` >>
     fs [regexp_matches_deriv, deriv_matches_def] >|
     [fs [is_error_state_def, EVERY_MAP] >>
          fs [EVERY_EL] >>
          res_tac >>
          cases_on `EL n lex_spec` >>
          fs [] >>
          rw [] >>
          metis_tac [regexp_matches_deriv, regexp_empty_thm],
      res_tac >>
          rw [] >>
          cases_on `FILTER (λ(regexp,action). nullable regexp) s` >>
          fs [] >>
          PairCases_on `h'` >>
          fs [] >>
          rw [] >>
          qexists_tac `(h,MAP (λ(regexp,action). (deriv h regexp,action)) lex_spec)::p` >>
          qexists_tac `s` >>
          rw [dfa_path_def]]]);

val lex_spec_to_dfa_correct = Q.store_thm ("lex_spec_to_dfa_correct",
`!lex_spec.
  dfa_correct lex_spec 
      (FST (lex_spec_to_dfa lex_spec))
      (SND (SND (lex_spec_to_dfa lex_spec)))
      (FST (SND (lex_spec_to_dfa lex_spec)))`,
rw [dfa_correct_def] >>
eq_tac >>
rw [] >|
[imp_res_tac path_to_spec >>
     fs [lex_spec_to_dfa_def],
 imp_res_tac spec_to_path >>
     fs [lex_spec_to_dfa_def] >>
     metis_tac []]);

val _ = export_theory ();
