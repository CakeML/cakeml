open preamble intSimps;
open astTheory print_astTheory;

val _ = new_theory "print_astTermination";

(* ----------------- Termination proofs for Print_astTheory --------------- *)

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end

val (spaces_def, spaces_ind) =
  tprove_no_defn ((spaces_def, spaces_ind),
  wf_rel_tac `measure (\(x,y).x)` >>
  srw_tac [ARITH_ss] []);
val _ = register "spaces" spaces_def spaces_ind;

val (join_trees_def, join_trees_ind) =
  tprove_no_defn ((join_trees_def, join_trees_ind),
  wf_rel_tac `measure (\(_,x).LENGTH x)` >>
  srw_tac [ARITH_ss] []);
val _ = register "join_trees" join_trees_def join_trees_ind;

val pat_size_lemma = prove(
  ``!xs a. MEM a xs ==> pat_size a < pat1_size xs``,
  Induct >> srw_tac [] [pat_size_def] >> res_tac >> decide_tac);

val (pat_to_tok_tree_def, pat_to_tok_tree_ind) =
  tprove_no_defn ((pat_to_tok_tree_def, pat_to_tok_tree_ind),
  wf_rel_tac `measure pat_size` >>
  rw [] >>
  imp_res_tac pat_size_lemma >>
  decide_tac);
val _ = register "pat_to_tok_tree" pat_to_tok_tree_def pat_to_tok_tree_ind;

val exp_size_lemma = prove(
  ``!xs a. MEM a xs ==> exp_size a < exp6_size xs``,
  Induct >> srw_tac [] [exp_size_def] >> res_tac >> decide_tac);

val (exp_to_tok_tree_def, exp_to_tok_tree_ind) =
  tprove_no_defn ((exp_to_tok_tree_def, exp_to_tok_tree_ind),
  wf_rel_tac `measure (\x. case x of INL (_,e) => exp_size e
                                   | INR (INL (_,_,p,e)) => exp_size e + 1
                                   | INR (INR (_,_,e)) => exp_size e + 1)` >>
  rw [] >>
  srw_tac[ARITH_ss][] >>
  TRY (induct_on `funs`) >>
  TRY (induct_on `pes`) >>
  TRY (induct_on `es`) >>
  TRY (induct_on `v37`) >>
  rw [exp_size_def] >>
  fs [exp_size_def] >>
  rw [exp_size_def] >>
  imp_res_tac exp_size_lemma >>
  decide_tac);

val _ = register "exp_to_tok_tree" exp_to_tok_tree_def exp_to_tok_tree_ind;

val (type_to_tok_tree_def, type_to_tok_tree_ind) =
  tprove_no_defn ((type_to_tok_tree_def, type_to_tok_tree_ind),
  wf_rel_tac `measure t_size` >>
  srw_tac [ARITH_ss] [] >>
  srw_tac [ARITH_ss] [] >>
  TRY (qpat_assum `ts ≠ []` (fn _ => all_tac)) >>
  TRY (induct_on `v16`) >>
  TRY (induct_on `ts`) >>
  rw [] >>
  fs [t_size_def] >>
  res_tac >>
  decide_tac);

val _ = register "type_to_tok_tree" type_to_tok_tree_def type_to_tok_tree_ind;

val tok_to_string_def =
  save_thm ("tok_to_string_def",SIMP_RULE (srw_ss()) [] tok_to_string_def);

val _ =
  computeLib.add_persistent_funs [("tok_to_string_def")];

val _ = export_theory ();
