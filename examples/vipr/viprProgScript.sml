(*
  Produces a verified CakeML program that checks VIPR proofs
*)
open preamble basis basisProgTheory cfLib basisFunctionsLib
     vipr_checkerTheory milpTheory;

val _ = new_theory "viprProg"

val _ = translation_extends "basisProg";

(* ----------------------------------------------------------------- *
    translation of definitions from background theories
 * ----------------------------------------------------------------- *)

val r = translate sptreeTheory.insert_def;
val r = translate sptreeTheory.lookup_def;
val r = translate sptreeTheory.lrnext_def;
val r = translate sptreeTheory.foldi_def;
val r = translate sptreeTheory.toAList_def;
val r = translate sptreeTheory.mk_BS_def;
val r = translate sptreeTheory.mk_BN_def;
val r = translate sptree_unionWithTheory.unionWith_def;
val r = translate sptreeTheory.map_def;

(* ----------------------------------------------------------------- *
    translation of definitions from milp
 * ----------------------------------------------------------------- *)

val r = translate check_dom_def;
val r = translate mk_sol_def;
val r = translate do_op_def;
val r = translate rSUM_def;
val r = translate eval_real_term_def;
val r = translate eval_lhs_eq;
val r = translate satisfies_lc_def;
val r = translate check_lcs_def;
val r = translate check_sol_def;
val r = translate absurdity_def;
val r = translate dominates_def;
val r = translate check_last_def;
val r = translate get_obj_def;
val r = translate le_inf_def;
val r = translate inf_le_def;
val r = translate check_rtp_bound_def;
val r = translate build_fml_def;
val r = translate (nub_def |> REWRITE_RULE [MEMBER_INTRO]);

val r = translate id_not_in_def;
val r = translate lookup_all_lhs_def;
val r = translate slop_def;
val r = translate compat_def;
val r = translate add_r_def;
val r = translate cmul_def;
val r = translate add_def;

val r = translate op_str_def;
val r = translate print_coeff_var_def;
val r = translate spt_center_def;
val r = translate spt_right_def;
val r = translate spt_left_def;
val r = translate spts_to_alist_add_pause_def;
val r = translate spts_to_alist_aux_def;
val r = translate spts_to_alist_def;
val r = translate toSortedAList_def;
val r = translate print_lc_def;
val r = translate lin_comb_def;
val r = translate do_lin_def;
val r = translate int_valued_def;
val r = translate round_lc_def;
val r = translate lookup_2_def;
val r = translate resolvable_aux_def;
val r = translate resolvable_def;
val r = translate delete_mem_def;
val r = translate assum_err_def;
val r = translate resolv_dom_err_def;
val r = translate (unsplit_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate check_vipr_def;

(* ----------------------------------------------------------------- *
    translation of definitions from vipr_checker
 * ----------------------------------------------------------------- *)

val r = translate empty_conf_def;
val r = translate (is_white_space_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate tokens_spaces_def;
val r = translate read_n_strings_def;
val r = translate read_n_nums_def;
val r = translate (str_to_real_def |> SIMP_RULE std_ss [MEM]);
val r = translate read_num_def;
val r = translate read_lin_def;
val r = translate read_lin_term_simple_def;
val r = translate read_lin_term_def;
val r = translate read_linop_def;
val r = translate read_real_def;
val r = translate read_lc_def;
val r = translate read_n_constraints_def;
val r = translate read_n_solutions_def;
val r = translate read_bound_def;
val r = translate read_goal_def;
val r = translate read_sol_def;
val r = translate read_rtp_def;
val r = translate read_con_def;
val r = translate (read_obj_def |> SIMP_RULE std_ss [MEM]);
val r = translate read_int_def;
val r = translate read_problem_def;
val r = translate read_end_def;
val r = translate read_vipr_lin_aux_def;
val r = translate read_vipr_lin_def;
val r = translate read_vipr_def;
val r = translate read_der_line_def;

val init_state_v_thm = translate init_state_def;
val checker_step_v_thm = translate checker_step_def;
val print_outcome_v_thm = translate print_outcome_def;

(* ---- *)

Definition usage_message_def:
  usage_message = concat [strlit "Usage:\n";
                          strlit "to read from stdin:   cake_vipr\n";
                          strlit "to read from a file:  cake_vipr FILE\n"]
End

val r = translate (usage_message_def |> CONV_RULE (RAND_CONV EVAL));
val r = translate oHD_def;

val _ = (append_prog o process_topdecs) `
  fun main u =
    let
      val cl = CommandLine.arguments ()
      val r = TextIO.foldLines #"\n" checker_step init_state (ohd cl)
    in print (print_outcome (Option.valOf r)) end
    handle e => TextIO.output TextIO.stdErr usage_message`;

val main_v_def = fetch "-" "main_v_def";

Theorem lines_of_gen_lines_of:
  lines_of_gen #"\n" xs =
  lines_of xs
Proof
  rw[lines_of_def,lines_of_gen_def,splitlines_at_def,splitlines_def,str_def]
QED

Theorem main_spec_stdin:
   hasFreeFD fs ∧ stdin_content fs = SOME text ∧ LENGTH cl < 2
   ⇒
   app (p:'ffi ffi_proj) main_v
     [Conv NONE []]
     (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
                STDIO (add_stdout (fastForwardFD fs 0) $
                         run_vipr (lines_of (implode text))) *
                COMMANDLINE cl)
Proof
  strip_tac
  \\ xcf_with_def main_v_def
  \\ reverse $ xhandle ‘(POSTv uv. &UNIT_TYPE () uv *
                STDIO (add_stdout (fastForwardFD fs 0) $
                         run_vipr (lines_of (implode text))) *
                COMMANDLINE cl)’
  >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)
  \\ fs[wfcl_def]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ assume_tac checker_step_v_thm
  \\ assume_tac init_state_v_thm
  \\ drule_at Any foldLines_NONE
  \\ disch_then $ drule_at $ Pos last
  \\ disch_then $ drule_at $ Any
  \\ rename [‘OPTION_TYPE STRING_TYPE (oHD (TL cl)) vvv’]
  \\ ‘OPTION_TYPE FILENAME NONE vvv’ by
    (Cases_on ‘cl’ \\ fs [] \\ Cases_on ‘t’ \\ fs [std_preludeTheory.OPTION_TYPE_def])
  \\ disch_then $ qspec_then ‘p’ mp_tac
  \\ disch_then $ drule_at $ Any
  \\ strip_tac
  \\ xlet ‘(POSTv retv.
             STDIO (fastForwardFD fs 0) * COMMANDLINE cl *
             &OPTION_TYPE VIPR_CHECKER_READER_STATE_TYPE
               (SOME
                  (foldl checker_step init_state (lines_of (implode text))))
               retv)’
  >- (
    xapp \\ xsimpl \\
    simp[lines_of_gen_lines_of]
  )
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ xsimpl
  \\ pop_assum $ irule_at $ Pos hd
  \\ fs [GSYM run_vipr_def]
  \\ qexists_tac ‘fastForwardFD fs 0’
  \\ xsimpl
QED

Definition filename_ok_def:
  filename_ok name ⇔
    ¬MEM #"\^@" (explode name) ∧ strlen name < 256 * 256
End

Theorem main_spec_file:
   hasFreeFD fs ∧ file_content fs (EL 1 cl) = SOME text ∧ 1 < LENGTH cl ∧
   filename_ok (EL 1 cl)
   ⇒
   app (p:'ffi ffi_proj) main_v
     [Conv NONE []]
     (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
                STDIO (add_stdout fs $
                         run_vipr (lines_of (implode text))) *
                COMMANDLINE cl)
Proof
  strip_tac
  \\ xcf_with_def main_v_def
  \\ reverse $ xhandle ‘(POSTv uv. &UNIT_TYPE () uv *
                STDIO (add_stdout fs $
                         run_vipr (lines_of (implode text))) *
                COMMANDLINE cl)’
  >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)
  \\ fs[wfcl_def]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ assume_tac checker_step_v_thm
  \\ assume_tac init_state_v_thm
  \\ drule_at Any foldLines_SOME
  \\ disch_then (drule_at Any)
  \\ fs []
  \\ disch_then $ drule_at $ Pos last \\ fs []
  \\ rename [‘OPTION_TYPE STRING_TYPE (oHD (TL cl)) vvv’]
  \\ ‘OPTION_TYPE FILENAME (SOME (EL 1 cl)) vvv’ by
    (Cases_on ‘cl’ \\ fs [] \\ Cases_on ‘t’ \\ fs [std_preludeTheory.OPTION_TYPE_def]
     \\ fs [FILENAME_def,filename_ok_def])
  \\ disch_then (drule_at Any)
  \\ disch_then $ qspec_then ‘p’ mp_tac
  \\ strip_tac
  \\ xlet ‘(POSTv retv.
             STDIO fs * COMMANDLINE cl *
             &OPTION_TYPE VIPR_CHECKER_READER_STATE_TYPE
               (SOME
                  (foldl checker_step init_state (lines_of (implode text))))
               retv)’
  >- (
    xapp \\ xsimpl \\
    simp[lines_of_gen_lines_of]
  )
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ xsimpl
  \\ pop_assum $ irule_at $ Pos hd
  \\ fs [GSYM run_vipr_def]
  \\ qexists_tac ‘fs’
  \\ xsimpl
QED

Theorem vipr_stdin_whole_prog_spec:
   hasFreeFD fs ∧ stdin_content fs = SOME text ∧ LENGTH cl < 2 ⇒
   whole_prog_spec main_v cl fs NONE ((=) $ add_stdout (fastForwardFD fs 0) $
                                              run_vipr (lines_of (implode text)))
Proof
  rw[whole_prog_spec_def]
  \\ irule_at Any app_wgframe
  \\ irule_at Any main_spec_stdin
  \\ fs []
  \\ rpt $ first_assum $ irule_at Any
  \\ xsimpl
  \\ qexists_tac ‘(add_stdout (fastForwardFD fs 0)
               (run_vipr (lines_of (implode text))))’
  \\ gvs [] \\ xsimpl
  \\ gvs [GSYM add_stdo_with_numchars,with_same_numchars]
  \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ gvs [IO_fs_component_equality]
QED

Theorem vipr_file_whole_prog_spec:
   hasFreeFD fs ∧ file_content fs (EL 1 cl) = SOME text ∧ 1 < LENGTH cl ∧
   filename_ok (EL 1 cl) ⇒
   whole_prog_spec main_v cl fs NONE ((=) $ add_stdout fs $
                                              run_vipr (lines_of (implode text)))
Proof
  rw[whole_prog_spec_def]
  \\ irule_at Any app_wgframe
  \\ irule_at Any main_spec_file
  \\ fs []
  \\ rpt $ first_assum $ irule_at Any
  \\ xsimpl
  \\ qexists_tac ‘(add_stdout fs
               (run_vipr (lines_of (implode text))))’
  \\ gvs [] \\ xsimpl
  \\ gvs [GSYM add_stdo_with_numchars,with_same_numchars]
QED

val (stdin_thm,prog_tm) = whole_prog_thm
                            (get_ml_prog_state())
                            "main"
                            (UNDISCH vipr_stdin_whole_prog_spec);

val (file_thm,prog_tm) = whole_prog_thm
                            (get_ml_prog_state())
                            "main"
                            (UNDISCH vipr_file_whole_prog_spec);

Definition vipr_prog_def:
  vipr_prog = ^prog_tm
End

Triviality clean_up:
  (b' ⇒ c) ⇒ ∀b. (b ⇒ b') ⇒ b ⇒ c
Proof
  fs []
QED

Theorem vipr_stdin_semantics =
  stdin_thm
  |> REWRITE_RULE[GSYM vipr_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO]
  |> MATCH_MP clean_up
  |> Q.SPEC ‘stdin_content fs = SOME text ∧ LENGTH cl < 2 ∧ wfcl cl ∧
             wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs’
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (srw_ss()) []))
  |> (fn th => MATCH_MP th TRUTH);

Theorem vipr_file_semantics =
  file_thm
  |> REWRITE_RULE[GSYM vipr_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO]
  |> MATCH_MP clean_up
  |> Q.SPEC ‘hasFreeFD fs ∧ file_content fs (EL 1 cl) = SOME text ∧ 1 < LENGTH cl ∧
             filename_ok (EL 1 cl) ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs’
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (srw_ss()) []))
  |> (fn th => MATCH_MP th TRUTH);

val _ = export_theory();
