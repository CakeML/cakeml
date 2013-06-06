open preamble;
open BigStepTheory;

val _ = new_theory "bigClock";

val big_unclocked_unchanged = Q.prove (
`(∀ck (menv : envM) (cenv : envC) s env e r1.
   evaluate ck menv cenv s env e r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1))) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r1.
   evaluate_list ck menv cenv s env es r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1))) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r1.
   evaluate_match ck menv cenv s env v pes r1 ⇒
     (ck = F)
     ⇒
     (SND r1 ≠ Rerr Rtimeout_error) ∧
     (FST s = FST (FST r1)))`,
ho_match_mp_tac evaluate_ind >>
rw []);

val big_unclocked_ignore = Q.prove (
`(∀ck (menv : envM) (cenv : envC) s env e r1.
   evaluate ck menv cenv s env e r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (ck = F) ∧
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r))
       ⇒
       evaluate ck menv cenv (count2,st) env e ((count2, st'), r)) ∧
 (∀ck (menv : envM) (cenv : envC) s env es r1.
   evaluate_list ck menv cenv s env es r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (ck = F) ∧
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r))
       ⇒
       evaluate_list ck menv cenv (count2,st) env es ((count2, st'), r)) ∧
 (∀ck (menv : envM) (cenv : envC) s env v pes r1.
   evaluate_match ck menv cenv s env v pes r1 ⇒
     !count1 count1' count2 count2' st st' r.
       (ck = F) ∧
       (s = (count1,st)) ∧
       (r1 = ((count1', st'), r))
       ⇒
       evaluate_match ck menv cenv (count2,st) env v pes ((count2, st'), r))`,
ho_match_mp_tac evaluate_ind >>
rw [] >>
rw [Once evaluate_cases]>>
TRY (PairCases_on `s'`) >>
fs [] >>
rw [] >>
metis_tac []);

val big_unclocked = Q.store_thm ("big_unclocked",
`!(menv : envM) (cenv : envC) count s env e count' s' r env.
  (evaluate F menv cenv (count, s) env e ((count',s'), r)
   ⇒
   (r ≠ Rerr Rtimeout_error) ∧
   (count = count')) ∧
  (evaluate F menv cenv (count, s) env e ((count,s'), r)
   =
   evaluate F menv cenv (count', s) env e ((count',s'), r))`,
rw [] >>
metis_tac [big_unclocked_ignore, big_unclocked_unchanged, FST, SND]);

val _ = export_theory ();
