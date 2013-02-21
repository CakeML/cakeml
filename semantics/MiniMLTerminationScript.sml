open preamble intSimps;
open MiniMLTheory;

val _ = new_theory "MiniMLTermination";

(* ------------------ Termination proofs for MiniMLTheory ----------------- *)

val tac = Induct >- rw[exp_size_def,pat_size_def,v_size_def] >> srw_tac [ARITH_ss][exp_size_def,pat_size_def,v_size_def]
fun tm t1 t2 =  ``∀ls f. ^t1 f ls = SUM (MAP (^t2 f) ls) + LENGTH ls``
fun size_thm name t1 t2 = store_thm(name,tm t1 t2,tac)
val exp1_size_thm = size_thm "exp1_size_thm" ``exp1_size`` ``exp2_size``
val exp5_size_thm = size_thm "exp5_size_thm" ``exp5_size`` ``exp7_size``
val exp8_size_thm = size_thm "exp8_size_thm" ``exp8_size`` ``exp_size``
val pat1_size_thm = size_thm "pat1_size_thm" ``pat1_size`` ``pat_size``
val v1_size_thm = size_thm "v1_size_thm" ``v1_size`` ``v2_size``
val v4_size_thm = size_thm "v4_size_thm" ``v4_size`` ``v_size``

val SUM_MAP_exp2_size_thm = store_thm(
"SUM_MAP_exp2_size_thm",
``∀defs f. SUM (MAP (exp2_size f) defs) = SUM (MAP (list_size char_size) (MAP FST defs)) +
                                          SUM (MAP (exp3_size f) (MAP SND defs)) +
                                          LENGTH defs``,
Induct >- rw[exp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp3_size_thm = store_thm(
"SUM_MAP_exp3_size_thm",
``∀ls f. SUM (MAP (exp3_size f) ls) = SUM (MAP (option_size f) (MAP FST ls)) +
                                      SUM (MAP (exp4_size f) (MAP SND ls)) +
                                      LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp4_size_thm = store_thm(
"SUM_MAP_exp4_size_thm",
``∀ls f. SUM (MAP (exp4_size f) ls) = SUM (MAP (list_size char_size) (MAP FST ls)) +
                                      SUM (MAP (exp6_size f) (MAP SND ls)) +
                                      LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp6_size_thm = store_thm(
"SUM_MAP_exp6_size_thm",
``∀ls f. SUM (MAP (exp6_size f) ls) = SUM (MAP (option_size f) (MAP FST ls)) +
                                      SUM (MAP (exp_size f) (MAP SND ls)) +
                                      LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp7_size_thm = store_thm(
"SUM_MAP_exp7_size_thm",
``∀ls f. SUM (MAP (exp7_size f) ls) = SUM (MAP (pat_size f) (MAP FST ls)) +
                                      SUM (MAP (exp_size f) (MAP SND ls)) +
                                      LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_v2_size_thm = store_thm(
"SUM_MAP_v2_size_thm",
``∀env f. SUM (MAP (v2_size f) env) = SUM (MAP (list_size char_size) (MAP FST env)) +
                                      SUM (MAP (v3_size f) (MAP SND env)) +
                                      LENGTH env``,
Induct >- rw[v_size_def] >>
Cases >> srw_tac[ARITH_ss][v_size_def])

val SUM_MAP_v3_size_thm = store_thm(
"SUM_MAP_v3_size_thm",
``∀env f. SUM (MAP (v3_size f) env) = SUM (MAP (v_size f) (MAP FST env)) +
                                      SUM (MAP (option_size (pair_size (λx. x) f)) (MAP SND env)) +
                                      LENGTH env``,
Induct >- rw[v_size_def] >>
Cases >> srw_tac[ARITH_ss][v_size_def])

val exp_size_positive = store_thm(
"exp_size_positive",
``∀e f. 0 < exp_size f e``,
Induct >> srw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["exp_size_positive"];

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end

val (lookup_def, lookup_ind) =
  tprove_no_defn ((lookup_def, lookup_ind),
  WF_REL_TAC `measure (λ(x,y). LENGTH y)` >>
  rw []);
val _ = register "lookup" lookup_def lookup_ind;
val _ = export_rewrites["lookup_def"];

val (pmatch_def, pmatch_ind) =
  tprove_no_defn ((pmatch_def, pmatch_ind),
  wf_rel_tac
  `inv_image $< (λx. case x of INL (tvs,s,a,p,b,c) => pat_size (\x.0) p 
                             | INR (tvs,s,a,ps,b,c) => pat1_size (\x.0) ps)`);
val _ = register "pmatch" pmatch_def pmatch_ind;

val (pmatch'_def, pmatch'_ind) =
  tprove_no_defn ((pmatch'_def, pmatch'_ind),
  wf_rel_tac
  `inv_image $< (λx. case x of INL (tvs,s,p,b,c) => pat_size (\x.0) p 
                             | INR (tvs,s,ps,b,c) => pat1_size (\x.0) ps)`);
val _ = register "pmatch'" pmatch'_def pmatch'_ind;

val (find_recfun_def, find_recfun_ind) =
  tprove_no_defn ((find_recfun_def, find_recfun_ind),
  WF_REL_TAC `measure (λ(x,y). LENGTH y)` >>
  rw []);
val _ = register "find_recfun" find_recfun_def find_recfun_ind;

val (type_subst_def, type_subst_ind) =
  tprove_no_defn ((type_subst_def, type_subst_ind),
  WF_REL_TAC `measure (λ(x,y). t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "type_subst" type_subst_def type_subst_ind;

val (deBruijn_subst_def, deBruijn_subst_ind) =
  tprove_no_defn ((deBruijn_subst_def, deBruijn_subst_ind),
  WF_REL_TAC `measure (λ(_,x,y). t_size y)` >>
  rw [] >>
  induct_on `ts'` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "deBruijn_subst" deBruijn_subst_def deBruijn_subst_ind;

val (check_freevars_def,check_freevars_ind) =
  tprove_no_defn ((check_freevars_def,check_freevars_ind),
wf_rel_tac `measure (t_size o SND o SND)` >>
srw_tac [ARITH_ss] [t_size_def] >>
induct_on `ts` >>
srw_tac [ARITH_ss] [t_size_def] >>
res_tac >>
decide_tac);
val _ = register "check_freevars" check_freevars_def check_freevars_ind;

val (deBruijn_inc_def,deBruijn_inc_ind) =
  tprove_no_defn ((deBruijn_inc_def,deBruijn_inc_ind),
wf_rel_tac `measure (t_size o SND o SND)` >>
srw_tac [ARITH_ss] [t_size_def] >>
induct_on `ts` >>
srw_tac [ARITH_ss] [t_size_def] >>
res_tac >>
decide_tac);
val _ = register "deBruijn_inc" deBruijn_inc_def deBruijn_inc_ind;

val (bind_var_list2_def,bind_var_list2_ind) =
  tprove_no_defn ((bind_var_list2_def,bind_var_list2_ind),
wf_rel_tac `measure (LENGTH o FST)` >>
srw_tac [] []);
val _ = register "bind_var_list2" bind_var_list2_def bind_var_list2_ind;


val (bind_var_list_def,bind_var_list_ind) =
  tprove_no_defn ((bind_var_list_def,bind_var_list_ind),
wf_rel_tac `measure (LENGTH o FST o SND)` >>
srw_tac [] []);
val _ = register "bind_var_list" bind_var_list_def bind_var_list_ind;

val (is_value_def,is_value_ind) =
  tprove_no_defn ((is_value_def,is_value_ind),
wf_rel_tac `measure (exp_size (\x.0))` >>
srw_tac [] [] >>
induct_on `es` >>
srw_tac [] [exp_size_def] >>
res_tac >>
decide_tac);
val _ = register "is_value" is_value_def is_value_ind;

val (deBruijn_subst_p_def,deBruijn_subst_p_ind) =
  tprove_no_defn ((deBruijn_subst_p_def,deBruijn_subst_p_ind),
wf_rel_tac `measure (pat_size (\x.0) o SND o SND)` >>
srw_tac [] [] >>
induct_on `ps` >>
srw_tac [] [pat_size_def] >>
res_tac >>
decide_tac);
val _ = register "deBruijn_subst_p" deBruijn_subst_p_def deBruijn_subst_p_ind;

val (deBruijn_subst_e_def,deBruijn_subst_e_ind) =
  tprove_no_defn ((deBruijn_subst_e_def,deBruijn_subst_e_ind),
wf_rel_tac `measure (exp_size (\x.0) o SND o SND)` >>
srw_tac [] [] >|
[decide_tac,
 decide_tac,
 decide_tac,
 decide_tac,
 induct_on `funs` >>
     srw_tac [] [exp_size_def] >>
     srw_tac [] [exp_size_def] >>
     res_tac >>
     decide_tac,
 induct_on `pes` >>
     srw_tac [] [exp_size_def] >>
     srw_tac [] [exp_size_def] >>
     res_tac >>
     decide_tac,
 decide_tac,
 decide_tac,
 decide_tac,
 decide_tac,
 decide_tac,
 decide_tac,
 induct_on `es` >>
     srw_tac [] [exp_size_def] >>
     res_tac >>
     decide_tac,
 decide_tac,
 decide_tac,
 decide_tac,
 decide_tac]);
val _ = register "deBruijn_subst_e" deBruijn_subst_e_def deBruijn_subst_e_ind;

val (deBruijn_subst_v_def,deBruijn_subst_v_ind) =
  tprove_no_defn ((deBruijn_subst_v_def,deBruijn_subst_v_ind),
wf_rel_tac `measure (v_size (\x.0) o SND)` >>
srw_tac [] [] >>
induct_on `vs` >>
srw_tac [] [v_size_def] >>
res_tac >>
decide_tac);
val _ = register "deBruijn_subst_v" deBruijn_subst_v_def deBruijn_subst_v_ind;

val _ = export_theory ();
