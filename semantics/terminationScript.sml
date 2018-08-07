open preamble intSimps;
open libTheory astTheory open namespaceTheory semanticPrimitivesTheory typeSystemTheory;
open evaluateTheory;

val _ = new_theory "termination";

val pats_size_def = Define `pats_size = pat1_size`;

val exps_size_def = Define `exps_size = exp6_size`;
val pes_size_def = Define `pes_size = exp3_size`;
val funs_size_def = Define `funs_size = exp1_size`;

val vs_size_def = Define `vs_size = v7_size`;
val envE_size_def = Define `envE_size = v2_size`;
val envM_size_def = Define `envM_size = v4_size`;

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
(* val vs_size_thm = size_thm "vs_size_thm" ``vs_size`` ``v_size``; *)
(* val envE_size_thm = size_thm "envE_size_thm" ``envE_size`` ``v3_size``; *)
(* val envM_size_thm = size_thm "envM_size_thm" ``envM_size`` ``v5_size``; *)

val SUM_MAP_exp2_size_thm = Q.store_thm(
"SUM_MAP_exp2_size_thm",
`∀defs. SUM (MAP exp2_size defs) = SUM (MAP (list_size char_size) (MAP FST defs)) +
                                          SUM (MAP exp4_size (MAP SND defs)) +
                                          LENGTH defs`,
Induct >- rw[exp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac[ARITH_ss][exp_size_def])

val SUM_MAP_exp4_size_thm = Q.store_thm(
"SUM_MAP_exp4_size_thm",
`∀ls. SUM (MAP exp4_size ls) = SUM (MAP (list_size char_size) (MAP FST ls)) +
                                      SUM (MAP exp_size (MAP SND ls)) +
                                      LENGTH ls`,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def]);

val SUM_MAP_exp5_size_thm = Q.store_thm(
"SUM_MAP_exp5_size_thm",
`∀ls. SUM (MAP exp5_size ls) = SUM (MAP pat_size (MAP FST ls)) +
                                SUM (MAP exp_size (MAP SND ls)) +
                                LENGTH ls`,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def]);

(*
val SUM_MAP_v2_size_thm = Q.store_thm(
"SUM_MAP_v2_size_thm",
`∀env. SUM (MAP v2_size env) = SUM (MAP (list_size char_size) (MAP FST env)) +
                                SUM (MAP v_size (MAP SND env)) +
                                LENGTH env`,
Induct >- rw[v_size_def] >>
Cases >> srw_tac[ARITH_ss][v_size_def])
*)

(*
val SUM_MAP_v3_size_thm = Q.store_thm(
"SUM_MAP_v3_size_thm",
`∀env f. SUM (MAP (v3_size f) env) = SUM (MAP (v_size f) (MAP FST env)) +
                                      SUM (MAP (option_size (pair_size (λx. x) f)) (MAP SND env)) +
                                      LENGTH env`,
Induct >- rw[v_size_def] >>
Cases >> srw_tac[ARITH_ss][v_size_def])
*)

val exp_size_positive = Q.store_thm(
"exp_size_positive",
`∀e. 0 < exp_size e`,
Induct >> srw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["exp_size_positive"];

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val (nsMap_def, nsMap_ind) =
  tprove_no_defn ((nsMap_def, nsMap_ind),
  wf_rel_tac `measure (\(_, env). namespace_size (\x. 1) (\x. 1) (\x. 1) env)`
  >> Induct_on `m`
  >> rw [namespace_size_def]
  >> rw [namespace_size_def]
  >> first_x_assum drule
  >> disch_then (qspec_then `v` assume_tac)
  >> decide_tac);
val _ = register "nsMap" nsMap_def nsMap_ind;

val (pmatch_def, pmatch_ind) =
  tprove_no_defn ((pmatch_def, pmatch_ind),
  wf_rel_tac
  `inv_image $< (λx. case x of INL (s,a,p,b,c) => pat_size  p
                             | INR (s,a,ps,b,c) => pats_size ps)` >>
  srw_tac [ARITH_ss] [size_abbrevs, pat_size_def]);
val _ = register "pmatch" pmatch_def pmatch_ind;

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
  WF_REL_TAC `measure (λ(x,y). ast_t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [ast_t_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "type_name_subst" type_name_subst_def type_name_subst_ind;

val (check_type_names_def, check_type_names_ind) =
  tprove_no_defn ((check_type_names_def, check_type_names_ind),
  WF_REL_TAC `measure (λ(x,y). ast_t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [ast_t_size_def] >>
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

val (check_freevars_ast_def,check_freevars_ast_ind) =
  tprove_no_defn ((check_freevars_ast_def,check_freevars_ast_ind),
wf_rel_tac `measure (ast_t_size o SND)` >>
srw_tac [ARITH_ss] [ast_t_size_def] >>
induct_on `ts` >>
srw_tac [ARITH_ss] [ast_t_size_def] >>
res_tac >>
decide_tac);
val _ = register "check_freevars_ast" check_freevars_ast_def check_freevars_ast_ind;

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
simp[] >>
srw_tac [][] >>
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

val (v_to_char_list_def,v_to_char_list_ind) =
  tprove_no_defn ((v_to_char_list_def,v_to_char_list_ind),
wf_rel_tac `measure v_size`);
val _ = register "v_to_char_list" v_to_char_list_def v_to_char_list_ind;

val (vs_to_string_def,vs_to_string_ind) =
  tprove_no_defn ((vs_to_string_def,vs_to_string_ind),
wf_rel_tac `measure LENGTH` \\ rw[]);
val _ = register "vs_to_string" vs_to_string_def vs_to_string_ind;

val check_dup_ctors_thm = Q.store_thm ("check_dup_ctors_thm",
  `check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)`,
  rw [check_dup_ctors_def] >>
  induct_on `condefs` >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  eq_tac >>
  rw [] >>
  induct_on `condefs` >>
  rw [] >>
  pairarg_tac >>
  fs []);

(*
val do_log_thm = Q.store_thm("do_log_thm",
  `do_log l v e =
    if l = And ∧ v = Conv(SOME("true",TypeId(Short"bool")))[] then SOME (Exp e) else
    if l = Or ∧ v = Conv(SOME("false",TypeId(Short"bool")))[] then SOME (Exp e) else
    if v = Conv(SOME("true",TypeId(Short"bool")))[] then SOME (Val v) else
    if v = Conv(SOME("false",TypeId(Short"bool")))[] then SOME (Val v) else
    NONE`,
  rw[semanticPrimitivesTheory.do_log_def] >>
    every_case_tac >> rw[])
    *)

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (s1,res) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val (evaluate_def,evaluate_ind) =
  tprove_no_defn ((evaluate_def,evaluate_ind),
  wf_rel_tac`inv_image ($< LEX $<)
    (λx. case x of
         | INL(s,_,es) => (s.clock,exps_size es)
         | INR(s,_,_,pes,_) => (s.clock,pes_size pes))` >>
  rw[size_abbrevs,exp_size_def,
  dec_clock_def,LESS_OR_EQ,
  do_if_def,do_log_def] >>
  imp_res_tac fix_clock_IMP >>
  simp[SIMP_RULE(srw_ss())[]exps_size_thm,MAP_REVERSE,SUM_REVERSE]);

val evaluate_clock = Q.store_thm("evaluate_clock",
  `(∀(s1:'ffi state) env e r s2. evaluate s1 env e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
   (∀(s1:'ffi state) env v p v' r s2. evaluate_match s1 env v p v' = (s2,r) ⇒ s2.clock ≤ s1.clock)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[] >> rw[] >> rfs[] >>
  fs[dec_clock_def,fix_clock_def] >> simp[] >>
  imp_res_tac fix_clock_IMP >> fs[]);

val fix_clock_evaluate = Q.store_thm("fix_clock_evaluate",
  `fix_clock s1 (evaluate s1 env e) = evaluate s1 env e`,
  Cases_on `evaluate s1 env e` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,state_component_equality]);

val evaluate_def = save_thm("evaluate_def",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def |> INST_TYPE[alpha|->``:'ffi``] (* TODO: this is only broken because Lem sucks *));

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind |> INST_TYPE[alpha|->``:'ffi``] (* TODO: this is only broken because Lem sucks *));

val _ = register "evaluate" evaluate_def evaluate_ind

val _ = export_rewrites["evaluate.list_result_def"];

val (evaluate_decs_def,evaluate_decs_ind) =
  tprove_no_defn ((evaluate_decs_def,evaluate_decs_ind),
  wf_rel_tac `measure (list_size dec_size o SND o SND)` >>
  rw [] >>
  induct_on `ds` >>
  rw [list_size_def, dec_size_def]);

val _ = register "evaluate_decs" evaluate_decs_def evaluate_decs_ind

val _ = export_theory ();
