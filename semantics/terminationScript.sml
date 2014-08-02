open preamble intSimps;
open libTheory astTheory semanticPrimitivesTheory typeSystemTheory;

val _ = new_theory "termination";

val pats_size_def = Define `pats_size = pat1_size`;

val exps_size_def = Define `exps_size = exp6_size`;
val pes_size_def = Define `pes_size = exp3_size`;
val funs_size_def = Define `funs_size = exp1_size`;

val vs_size_def = Define `vs_size = v7_size`;
val envE_size_def = Define `envE_size = v5_size`;
val envM_size_def = Define `envM_size = v3_size`;

val size_abbrevs = save_thm ("size_abbrevs",
LIST_CONJ [pats_size_def, 
           exps_size_def, pes_size_def, funs_size_def, 
           vs_size_def, envE_size_def, envM_size_def]);

val _ = export_rewrites["size_abbrevs"];

val tac = Induct >- rw[exp_size_def,pat_size_def,v_size_def,size_abbrevs] >>
  full_simp_tac (srw_ss()++ARITH_ss)[exp_size_def,pat_size_def,v_size_def, size_abbrevs];
fun tm t1 t2 =  ``∀ls. ^t1 ls = SUM (MAP ^t2 ls) + LENGTH ls``;
fun size_thm name t1 t2 = store_thm(name,tm t1 t2,tac);

val exps_size_thm = size_thm "exps_size_thm" ``exps_size`` ``exp_size``;
val pes_size_thm = size_thm "pes_size_thm" ``pes_size`` ``exp5_size``;
val funs_size_thm = size_thm "funs_size_thm" ``funs_size`` ``exp2_size``;
val pats_size_thm = size_thm "pats_size_thm" ``pats_size`` ``pat_size``;
val vs_size_thm = size_thm "vs_size_thm" ``vs_size`` ``v_size``;
val envE_size_thm = size_thm "envE_size_thm" ``envE_size`` ``v6_size``;
val envM_size_thm = size_thm "envM_size_thm" ``envM_size`` ``v4_size``;

val SUM_MAP_exp2_size_thm = store_thm(
"SUM_MAP_exp2_size_thm",
``∀defs. SUM (MAP exp2_size defs) = SUM (MAP (list_size char_size) (MAP FST defs)) +
                                          SUM (MAP exp4_size (MAP SND defs)) +
                                          LENGTH defs``,
Induct >- rw[exp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp4_size_thm = store_thm(
"SUM_MAP_exp4_size_thm",
``∀ls. SUM (MAP exp4_size ls) = SUM (MAP (list_size char_size) (MAP FST ls)) +
                                      SUM (MAP exp_size (MAP SND ls)) +
                                      LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp5_size_thm = store_thm(
"SUM_MAP_exp5_size_thm",
``∀ls. SUM (MAP exp5_size ls) = SUM (MAP pat_size (MAP FST ls)) +
                                SUM (MAP exp_size (MAP SND ls)) +
                                LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def])

(*
val SUM_MAP_v2_size_thm = store_thm(
"SUM_MAP_v2_size_thm",
``∀env. SUM (MAP v2_size env) = SUM (MAP (list_size char_size) (MAP FST env)) +
                                SUM (MAP v_size (MAP SND env)) +
                                LENGTH env``,
Induct >- rw[v_size_def] >>
Cases >> srw_tac[ARITH_ss][v_size_def])
*)

(*
val SUM_MAP_v3_size_thm = store_thm(
"SUM_MAP_v3_size_thm",
``∀env f. SUM (MAP (v3_size f) env) = SUM (MAP (v_size f) (MAP FST env)) +
                                      SUM (MAP (option_size (pair_size (λx. x) f)) (MAP SND env)) +
                                      LENGTH env``,
Induct >- rw[v_size_def] >>
Cases >> srw_tac[ARITH_ss][v_size_def])
*)

val exp_size_positive = store_thm(
"exp_size_positive",
``∀e. 0 < exp_size e``,
Induct >> srw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["exp_size_positive"];

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val _ = export_rewrites["lib.lookup_def"];

val (pmatch_def, pmatch_ind) =
  tprove_no_defn ((pmatch_def, pmatch_ind),
  wf_rel_tac
  `inv_image $< (λx. case x of INL (s,a,p,b,c) => pat_size  p
                             | INR (s,a,ps,b,c) => pats_size ps)` >>
  srw_tac [ARITH_ss] [size_abbrevs, pat_size_def]);
val _ = register "pmatch" pmatch_def pmatch_ind;

val (contains_closure_def, contains_closure_ind) =
  tprove_no_defn ((contains_closure_def, contains_closure_ind),
  wf_rel_tac `measure v_size` >> conj_tac
  THEN Induct_on `vs` THEN rw [v_size_def] THEN1 decide_tac
  THEN RES_TAC THEN TRY (POP_ASSUM (ASSUME_TAC o Q.SPEC `cn`)) THEN decide_tac);
val _ = register "contains_closure" contains_closure_def contains_closure_ind;

val (type_subst_def, type_subst_ind) =
  tprove_no_defn ((type_subst_def, type_subst_ind),
  WF_REL_TAC `measure (λ(x,y). t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "type_subst" type_subst_def type_subst_ind;

val (type_name_subst_def, type_name_subst_ind) =
  tprove_no_defn ((type_name_subst_def, type_name_subst_ind),
  WF_REL_TAC `measure (λ(x,y). t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "type_name_subst" type_name_subst_def type_name_subst_ind;

val (check_type_names_def, check_type_names_ind) =
  tprove_no_defn ((check_type_names_def, check_type_names_ind),
  WF_REL_TAC `measure (λ(x,y). t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "check_type_names" check_type_names_def check_type_names_ind;

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

val (is_value_def,is_value_ind) =
  tprove_no_defn ((is_value_def,is_value_ind),
wf_rel_tac `measure (exp_size)` >>
srw_tac [] [] >>
induct_on `es` >>
srw_tac [] [exp_size_def] >>
res_tac >>
decide_tac);
val _ = register "is_value" is_value_def is_value_ind;

val (do_eq_def,do_eq_ind) =
  tprove_no_defn ((do_eq_def,do_eq_ind),
wf_rel_tac `inv_image $< (λx. case x of INL (v1,v2) => v_size v1
                                      | INR (vs1,vs2) => vs_size vs1)` >>
srw_tac [ARITH_ss] [size_abbrevs, v_size_def]);
val _ = register "do_eq" do_eq_def do_eq_ind;

val (v_to_list_def,v_to_list_ind) =
  tprove_no_defn ((v_to_list_def,v_to_list_ind),
wf_rel_tac `measure v_size`);
val _ = register "v_to_list" v_to_list_def v_to_list_ind;

val check_ctor_foldr_flat_map = Q.prove (
`!c. (FOLDR
         (λ(tvs,tn,condefs) x2.
            FOLDR (λ(n,ts) x2. n::x2) x2 condefs) [] c)
    =
    FLAT (MAP (\(tvs,tn,condefs). (MAP (λ(n,ts). n)) condefs) c)`,
induct_on `c` >>
rw [LET_THM] >>
PairCases_on `h` >>
fs [LET_THM] >>
pop_assum (fn _ => all_tac) >>
induct_on `h2` >>
rw [] >>
PairCases_on `h` >>
rw []);

val check_dup_ctors_thm = Q.store_thm ("check_dup_ctors_thm",
`!tds.
  check_dup_ctors tds =
    ALL_DISTINCT (FLAT (MAP (\(tvs,tn,condefs). (MAP (λ(n,ts). n)) condefs) tds))`,
metis_tac [check_dup_ctors_def,check_ctor_foldr_flat_map]);

val _ = export_theory ();
