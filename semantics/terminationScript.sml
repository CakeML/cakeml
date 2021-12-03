(*
  Termination proofs for functions defined in .lem files whose termination is
  not proved automatically.
*)
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

Theorem v1_size:
  !xs. v1_size xs = SUM (MAP v_size xs) + LENGTH xs
Proof
  Induct \\ simp [v_size_def]
QED

Theorem SUM_MAP_exp2_size_thm:
 ∀defs. SUM (MAP exp2_size defs) = SUM (MAP (list_size char_size) (MAP FST defs)) +
                                          SUM (MAP exp4_size (MAP SND defs)) +
                                          LENGTH defs
Proof
Induct >- rw[exp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac[ARITH_ss][exp_size_def]
QED

Theorem SUM_MAP_exp4_size_thm:
 ∀ls. SUM (MAP exp4_size ls) = SUM (MAP (list_size char_size) (MAP FST ls)) +
                                      SUM (MAP exp_size (MAP SND ls)) +
                                      LENGTH ls
Proof
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def]
QED

Theorem SUM_MAP_exp5_size_thm:
 ∀ls. SUM (MAP exp5_size ls) = SUM (MAP pat_size (MAP FST ls)) +
                                SUM (MAP exp_size (MAP SND ls)) +
                                LENGTH ls
Proof
Induct >- rw[exp_size_def] >>
Cases >> srw_tac[ARITH_ss][exp_size_def]
QED

Theorem exp_size_positive:
 ∀e. 0 < exp_size e
Proof
Induct >> srw_tac[ARITH_ss][exp_size_def]
QED
val _ = export_rewrites["exp_size_positive"];

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val _ = register "nsMap" nsMap_def nsMap_ind;

val _ = register "pmatch" pmatch_def pmatch_ind;

val _ = register "type_subst" type_subst_def type_subst_ind;

val _ = register "type_name_subst" type_name_subst_def type_name_subst_ind;

val _ = register "check_type_names" check_type_names_def check_type_names_ind;

val _ = register "deBruijn_subst" deBruijn_subst_def deBruijn_subst_ind;

val _ = register "check_freevars" check_freevars_def check_freevars_ind;

val _ = register "check_freevars_ast" check_freevars_ast_def check_freevars_ast_ind;

val _ = register "deBruijn_inc" deBruijn_inc_def deBruijn_inc_ind;

val _ = register "is_value" is_value_def is_value_ind;

val _ = register "do_eq" do_eq_def do_eq_ind;

val _ = register "v_to_list" v_to_list_def v_to_list_ind;

val _ = register "maybe_all_list" maybe_all_list_def maybe_all_list_ind;

val _ = register "v_to_char_list" v_to_char_list_def v_to_char_list_ind;

val _ = register "vs_to_string" vs_to_string_def vs_to_string_ind;

Theorem check_dup_ctors_thm:
   check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)
Proof
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
  fs []
QED

(* tidy up evalute_def and evaluate_ind *)

Theorem evaluate_clock = evaluateTheory.evaluate_clock

Theorem fix_clock_do_eval_res = evaluateTheory.fix_clock_do_eval_res

Theorem fix_clock_evaluate = evaluateTheory.fix_clock_evaluate

(* store evaluate_def and evaluate_ind in full and in parts *)

Theorem full_evaluate_def = evaluateTheory.full_evaluate_def
Theorem full_evaluate_ind = evaluateTheory.full_evaluate_ind

Theorem evaluate_ind = evaluateTheory.evaluate_ind
Theorem evaluate_match_ind = evaluateTheory.evaluate_match_ind
Theorem evaluate_decs_ind = evaluateTheory.evaluate_decs_ind

Theorem evaluate_def = evaluateTheory.evaluate_def
Theorem evaluate_match_def = evaluateTheory.evaluate_match_def
Theorem evaluate_decs_def = evaluateTheory.evaluate_decs_def

val _ = export_rewrites["evaluate.list_result_def"];

Theorem dec1_size_eq:
   dec1_size xs = list_size dec_size xs
Proof
  Induct_on `xs` \\ fs [dec_size_def, list_size_def]
QED

val _ = register "enc_ast_t" enc_ast_t_def enc_ast_t_ind;

val _ = register "enc_pat" enc_pat_def enc_pat_ind;

val _ = register "enc_exp" enc_exp_def enc_exp_ind;

val _ = register "enc_dec" enc_dec_def enc_dec_ind;

val _ = register "concrete_v" concrete_v_def concrete_v_ind;

val _ = export_theory ();
