open preamble;
open clos_relationTheory clos_relationPropsTheory closPropsTheory clos_mtiTheory;

val _ = new_theory "clos_mtiProof";

val collect_args_correct = Q.prove (
`!num_args e num_args' e' e''.
  collect_args num_args e = (num_args', e') ∧
  exp_rel (:'ffi) [e'] [e'']
  ⇒
  exp_rel (:'ffi) [Fn NONE NONE num_args e] [Fn NONE NONE num_args' e'']`,
 ho_match_mp_tac collect_args_ind >>
 rw [collect_args_def]
 >- (
   (* Either make fn_add_arg more general, or add a syntactic check *)
   `num_args ≠ 0 ∧ num_args' ≠ 0` by cheat >> 
   metis_tac [fn_add_arg, exp_rel_trans, exp_rel_refl])
 >- cheat >> (* Haven't verified this. Might not want to do the transformation anyway *)
 metis_tac [compat]);

val intro_multi_correct = Q.store_thm ("intro_multi_correct",
`!es. exp_rel (:'ffi) es (intro_multi es)`,
 ho_match_mp_tac intro_multi_ind >>
 rw [intro_multi_def, compat_nil, compat_var]
 >- metis_tac [compat_cons, intro_multi_sing, HD]
 >- metis_tac [compat_if, intro_multi_sing, HD]
 >- metis_tac [compat_let, intro_multi_sing, HD]
 >- metis_tac [compat_raise, intro_multi_sing, HD]
 >- metis_tac [compat_handle, intro_multi_sing, HD]
 >- metis_tac [compat_tick, intro_multi_sing, HD]
 >- metis_tac [compat_call, intro_multi_sing, HD]
 >- cheat
 >- metis_tac [compat_app, intro_multi_sing, HD]
 >- metis_tac [collect_args_correct, intro_multi_sing, HD]
 >- metis_tac [compat_fn, intro_multi_sing, HD]
 >- metis_tac [compat_fn, intro_multi_sing, HD]
 >- cheat
 >- metis_tac [compat_op, intro_multi_sing, HD]);

 (*

 >- (
   Cases_on `e1` >>
   fs []
   >- (fs [intro_multi_def] >> metis_tac [compat_app])
   >- (fs [intro_multi_def] >> metis_tac [compat_app])
   >- (fs [intro_multi_def] >> metis_tac [compat_app])
   >- (fs [intro_multi_def] >> metis_tac [compat_app])
   >- (fs [intro_multi_def] >> metis_tac [compat_app])
   >- (fs [intro_multi_def] >> metis_tac [compat_app])
   >- (fs [intro_multi_def] >> metis_tac [compat_app])
   >- (
     reverse (Cases_on `o'`)
     >- (fs [intro_multi_def] >- metis_tac [compat_app]) >>
     Cases_on `HD (intro_multi [App NONE e l])` >>
     fs []
     >- (Cases_on `e` >> fs [intro_multi_def])
     *)

val _ = export_theory();

